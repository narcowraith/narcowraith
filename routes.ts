import type { Express, Request, Response, NextFunction } from "express";
import { createServer, type Server } from "http";
import session from "express-session";
import connectPgSimple from "connect-pg-simple";
import crypto from "crypto";
import { storage } from "./storage";
import {
  generateRegistrationOptionsForUser,
  verifyRegistration,
  generateAuthenticationOptionsForUser,
  verifyAuthentication,
} from "./webauthn";
import { encryptData, decryptData, generateEncryptedFileName } from "./encryption";
import type { RegistrationResponseJSON, AuthenticationResponseJSON } from "@simplewebauthn/types";
import { securityMonitor } from "./security-monitor";
import { setupHoneypots } from "./honeypot";
import multer from "multer";
import { Readable } from "stream";

// Re-aliasing isAuthenticated as requireAuth to match the original code's usage
const isAuthenticated = requireAuth;

declare module "express-session" {
  interface SessionData {
    userId?: string;
    username?: string;
    challenge?: string;
    csrfToken?: string;
    pendingRegistration?: {
      userId: string;
      username: string;
    };
    pendingLogin?: {
      userId: string;
      username: string;
    };
  }
}

const MAX_ACCOUNTS_PER_IP = 3;
const MAX_FILE_SIZE = 50 * 1024 * 1024 * 1024; // 50GB
const MAX_STORAGE_PER_USER = 50 * 1024 * 1024 * 1024; // 50GB
const RATE_LIMIT_WINDOW = 60;
const RATE_LIMIT_MAX_AUTH = 10;
const RATE_LIMIT_MAX_UPLOAD = 30;

// Configure multer for memory storage with streaming
const upload = multer({
  storage: multer.memoryStorage(),
  limits: {
    fileSize: MAX_FILE_SIZE,
    files: 1,
  },
  fileFilter: (req, file, cb) => {
    if (!isValidFilename(file.originalname)) {
      cb(new Error("Invalid filename"));
      return;
    }
    cb(null, true);
  },
});

// Mullvad VPN - check by /24 CIDR ranges (Mullvad owns entire blocks)
let mullvadCIDRs: Set<string> = new Set();
let mullvadIPsLoaded = false;

function ipToCIDR24(ip: string): string {
  const parts = ip.split('.');
  if (parts.length !== 4) return '';
  return `${parts[0]}.${parts[1]}.${parts[2]}.0/24`;
}

async function loadMullvadIPs(): Promise<void> {
  try {
    console.log('[Mullvad] Fetching relay list from API...');
    const response = await fetch('https://api.mullvad.net/www/relays/all/', {
      signal: AbortSignal.timeout(10000)
    });

    if (!response.ok) {
      throw new Error(`HTTP ${response.status}`);
    }

    const relays = await response.json() as Array<{ ipv4_addr_in?: string; active?: boolean }>;

    for (const relay of relays) {
      if (relay.ipv4_addr_in && relay.active !== false) {
        // Store as /24 CIDR range since Mullvad owns entire blocks
        const cidr = ipToCIDR24(relay.ipv4_addr_in);
        if (cidr) mullvadCIDRs.add(cidr);
      }
    }

    mullvadIPsLoaded = true;
    console.log(`[Mullvad] Loaded ${mullvadCIDRs.size} /24 CIDR ranges`);
  } catch (error: any) {
    console.error('[Mullvad] Failed to fetch relay list:', error.message);
    mullvadIPsLoaded = false;
  }
}

// Load Mullvad IPs on module initialization
loadMullvadIPs();

// Refresh Mullvad IPs every hour
setInterval(() => {
  loadMullvadIPs();
}, 60 * 60 * 1000);

function isMullvadVPN(ip: string): boolean {
  // If we couldn't load the IP list, fail open (allow registration)
  if (!mullvadIPsLoaded || mullvadCIDRs.size === 0) {
    console.warn(`[Mullvad] IP list not loaded, allowing registration for IP: ${ip}`);
    return true;
  }

  // Check if IP's /24 range is in our Mullvad CIDR list
  const ipCIDR = ipToCIDR24(ip);
  const isMullvad = mullvadCIDRs.has(ipCIDR);
  console.log(`[Mullvad] Checking IP ${ip} (${ipCIDR}): ${isMullvad ? 'ALLOWED (Mullvad)' : 'BLOCKED (not Mullvad)'}`);
  return isMullvad;
}

const USERNAME_REGEX = /^[a-zA-Z0-9_-]{3,32}$/;
const DANGEROUS_PATTERNS = [
  /<script/i,
  /javascript:/i,
  /on\w+=/i,
  /data:/i,
  /vbscript:/i,
  /expression\(/i,
];

function sanitizeString(input: string): string {
  if (typeof input !== "string") return "";
  return input
    .replace(/[<>]/g, "")
    .replace(/&/g, "&amp;")
    .trim()
    .substring(0, 1000);
}

function isValidFilename(filename: string): boolean {
  if (!filename || typeof filename !== "string") return false;
  if (filename.length > 255) return false;
  if (filename.includes("..") || filename.includes("/") || filename.includes("\\")) return false;
  for (const pattern of DANGEROUS_PATTERNS) {
    if (pattern.test(filename)) return false;
  }
  return true;
}

function getClientIp(req: Request): string {
  const forwardedFor = req.headers["x-forwarded-for"];
  if (forwardedFor) {
    const ips = (Array.isArray(forwardedFor) ? forwardedFor[0] : forwardedFor).split(",");
    return ips[0].trim();
  }
  return req.socket.remoteAddress || req.ip || "unknown";
}

function generateCsrfToken(): string {
  return crypto.randomBytes(32).toString("hex");
}

async function requireAuth(req: Request, res: Response, next: NextFunction) {
  // CRITICAL: Strict session validation
  if (!req.session.userId || !req.session.username) {
    req.session.destroy((err) => {
      if (err) console.error("Session destruction error:", err);
    });
    res.clearCookie("__cartel_sid");
    return res.status(401).json({ error: "Authentication required" });
  }

  // Verify user still exists in database
  const user = await storage.getUser(req.session.userId);
  if (!user || user.username !== req.session.username) {
    await storage.createLog({
      userId: req.session.userId,
      action: "INVALID_SESSION_DETECTED",
      details: "Session user mismatch or deleted user",
      ipAddress: getClientIp(req),
      userAgent: req.get("user-agent"),
      type: "error",
    });

    req.session.destroy((err) => {
      if (err) console.error("Session destruction error:", err);
    });
    res.clearCookie("__cartel_sid");
    return res.status(401).json({ error: "Invalid session" });
  }

  next();
}

function verifyCsrf(req: Request, res: Response, next: NextFunction) {
  const tokenFromHeader = req.headers["x-csrf-token"] as string;
  const tokenFromSession = req.session.csrfToken;

  if (!tokenFromHeader || !tokenFromSession || tokenFromHeader !== tokenFromSession) {
    return res.status(403).json({ error: "Invalid CSRF token" });
  }
  next();
}

async function rateLimit(endpoint: string, max: number) {
  return async (req: Request, res: Response, next: NextFunction) => {
    const ip = getClientIp(req);
    const allowed = await storage.checkRateLimit(ip, endpoint, max, RATE_LIMIT_WINDOW);

    if (!allowed) {
      await securityMonitor.logSecurityEvent({
        type: 'THRESHOLD_EXCEEDED',
        severity: 'MEDIUM',
        ipAddress: ip,
        details: `Rate limit exceeded for ${endpoint}`,
      });

      await storage.createLog({
        action: "RATE_LIMIT_EXCEEDED",
        details: `Rate limit exceeded for ${endpoint} from ${ip}`,
        ipAddress: ip,
        userAgent: req.get("user-agent"),
        type: "warning",
      });
      return res.status(429).json({ error: "Too many requests. Please try again later." });
    }

    await storage.incrementRateLimit(ip, endpoint);
    next();
  };
}

export async function registerRoutes(
  httpServer: Server,
  app: Express
): Promise<Server> {
  // Trust proxy for nginx reverse proxy (required for secure cookies)
  app.set("trust proxy", 1);

  // Setup honeypot endpoints for attack detection
  setupHoneypots(app);

  app.use((req, res, next) => {
    res.setHeader("X-Content-Type-Options", "nosniff");
    res.setHeader("X-Frame-Options", "DENY");
    res.setHeader("X-XSS-Protection", "1; mode=block");
    res.setHeader("Referrer-Policy", "strict-origin-when-cross-origin");
    res.setHeader("Permissions-Policy", "geolocation=(), microphone=(), camera=()");
    res.setHeader(
      "Content-Security-Policy",
      "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; font-src 'self'; connect-src 'self'; frame-ancestors 'none'"
    );
    res.setHeader("Link", '</favicon.ico>; rel="icon"'); // Folder icon favicon
    next();
  });

  const PgSession = connectPgSimple(session);

  app.use(
    session({
      store: new PgSession({
        conString: process.env.DATABASE_URL,
        tableName: "user_sessions",
        createTableIfMissing: true,
        pruneSessionInterval: 60 * 15,
      }),
      secret: process.env.SESSION_SECRET || crypto.randomBytes(64).toString("hex"),
      name: "__cartel_sid",
      resave: false,
      saveUninitialized: false,
      cookie: {
        secure: process.env.NODE_ENV === "production",
        httpOnly: true,
        maxAge: 30 * 60 * 1000,
        sameSite: "strict", // CRITICAL: Changed from lax to strict for better CSRF protection
        path: "/",
      },
      rolling: true,
    })
  );

  app.use((req, res, next) => {
    // Initialize CSRF token for new sessions
    if (!req.session.csrfToken) {
      req.session.csrfToken = generateCsrfToken();
    }

    // CRITICAL: Detect session tampering
    if (req.session.userId) {
      // If userId exists, username MUST also exist
      if (!req.session.username) {
        console.error("Session tampering detected: userId without username");
        req.session.destroy((err) => {
          if (err) console.error("Session destruction error:", err);
        });
        res.clearCookie("__cartel_sid");
        return res.status(401).json({ error: "Invalid session" });
      }

      // pendingLogin/pendingRegistration should NEVER coexist with authenticated userId
      if (req.session.pendingLogin || req.session.pendingRegistration) {
        console.error("Session tampering detected: authenticated session with pending auth");
        req.session.destroy((err) => {
          if (err) console.error("Session destruction error:", err);
        });
        res.clearCookie("__cartel_sid");
        return res.status(401).json({ error: "Invalid session" });
      }
    }

    next();
  });

  app.get("/api/auth/session", (req, res) => {
    if (req.session.userId) {
      res.json({ 
        authenticated: true, 
        username: req.session.username,
        userId: req.session.userId,
        csrfToken: req.session.csrfToken,
      });
    } else {
      res.json({ 
        authenticated: false,
        csrfToken: req.session.csrfToken,
      });
    }
  });

  app.post("/api/auth/register/options", await rateLimit("auth", RATE_LIMIT_MAX_AUTH), async (req, res) => {
    try {
      const { username } = req.body;

      if (!username || typeof username !== "string") {
        return res.status(400).json({ error: "Username required" });
      }

      const sanitizedUsername = sanitizeString(username);
      if (!USERNAME_REGEX.test(sanitizedUsername)) {
        return res.status(400).json({ 
          error: "Invalid username. Use 3-32 alphanumeric characters, underscores, or hyphens only." 
        });
      }

      const clientIp = getClientIp(req);

      // CRITICAL: Silently reject non-Mullvad VPN connections
      if (!isMullvadVPN(clientIp)) {
        await storage.createLog({
          action: "REGISTRATION_BLOCKED_NON_VPN",
          details: `Registration blocked from non-Mullvad IP: ${clientIp}`,
          ipAddress: clientIp,
          userAgent: req.get("user-agent"),
          type: "warning",
        });

        // Return generic error without revealing VPN requirement
        await new Promise(resolve => setTimeout(resolve, 500 + Math.random() * 1000));
        return res.status(500).json({ error: "Registration service temporarily unavailable" });
      }

      const ipAccountCount = await storage.countUsersByIp(clientIp);

      if (ipAccountCount >= MAX_ACCOUNTS_PER_IP) {
        await storage.createLog({
          action: "REGISTRATION_BLOCKED",
          details: `IP ${clientIp} exceeded max accounts (${MAX_ACCOUNTS_PER_IP})`,
          ipAddress: clientIp,
          userAgent: req.get("user-agent"),
          type: "warning",
        });
        return res.status(403).json({ 
          error: `Maximum number of accounts (${MAX_ACCOUNTS_PER_IP}) reached for this network.` 
        });
      }

      const existingUser = await storage.getUserByUsername(sanitizedUsername);
      if (existingUser) {
        return res.status(400).json({ error: "Username already exists" });
      }

      const user = await storage.createUser({ 
        username: sanitizedUsername,
        registrationIp: clientIp,
      });

      await storage.createUserSettings({ userId: user.id });

      const options = await generateRegistrationOptionsForUser(user.id, sanitizedUsername);

      // Store pending registration data without authenticating the session
      req.session.pendingRegistration = {
        userId: user.id,
        username: sanitizedUsername,
      };
      req.session.challenge = options.challenge;

      // Explicitly save session before responding
      await new Promise<void>((resolve, reject) => {
        req.session.save((err) => {
          if (err) reject(err);
          else resolve();
        });
      });

      await storage.createLog({
        userId: user.id,
        action: "REGISTRATION_STARTED",
        details: `User ${sanitizedUsername} initiated device registration`,
        ipAddress: clientIp,
        userAgent: req.get("user-agent"),
        type: "info",
      });

      res.json(options);
    } catch (error: any) {
      console.error("Registration options error:", error?.message, error?.stack);
      res.status(500).json({ error: "Failed to generate registration options", details: error?.message });
    }
  });

  app.post("/api/auth/register/verify", await rateLimit("auth", RATE_LIMIT_MAX_AUTH), async (req, res) => {
    try {
      const { response } = req.body as { response: RegistrationResponseJSON };
      const pendingRegistration = req.session.pendingRegistration;
      const challenge = req.session.challenge;

      // CRITICAL: Ensure no authenticated session exists during verification
      if (req.session.userId) {
        console.error("Invalid state: authenticated session during registration verification");
        req.session.destroy((err) => {
          if (err) console.error("Session destruction error:", err);
        });
        res.clearCookie("__cartel_sid");
        return res.status(400).json({ error: "Invalid registration state" });
      }

      if (!pendingRegistration || !challenge) {
        return res.status(400).json({ error: "No registration in progress" });
      }

      const { userId, username } = pendingRegistration;
      const verification = await verifyRegistration(userId, response, challenge);

      if (verification.verified) {
        // Only now set the authenticated session
        req.session.userId = userId;
        req.session.username = username;
        req.session.csrfToken = generateCsrfToken();
        delete req.session.pendingRegistration;

        await storage.createLog({
          userId,
          action: "REGISTRATION_COMPLETE",
          details: "FIDO2 credential registered successfully",
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "success",
        });

        res.json({ 
          verified: true, 
          username: username,
          csrfToken: req.session.csrfToken,
        });
      } else {
        // CRITICAL: Destroy session completely on registration failure
        req.session.destroy((err) => {
          if (err) {
            console.error("Session destruction error:", err);
          }
          res.clearCookie("__cartel_sid");
          res.status(400).json({ error: "Verification failed" });
        });
      }
    } catch (error: any) {
      console.error("Registration verify error:", error);
      // CRITICAL: Destroy session completely on error
      req.session.destroy((err) => {
        if (err) {
          console.error("Session destruction error:", err);
        }
        res.clearCookie("__cartel_sid");
        res.status(500).json({ error: "Registration verification failed" });
      });
    }
  });

  app.post("/api/auth/login/options", await rateLimit("auth", RATE_LIMIT_MAX_AUTH), async (req, res) => {
    try {
      const { username } = req.body;

      if (!username || typeof username !== "string") {
        return res.status(400).json({ error: "Username required" });
      }

      const sanitizedUsername = sanitizeString(username);
      if (!USERNAME_REGEX.test(sanitizedUsername)) {
        return res.status(400).json({ error: "Invalid username format" });
      }

      const user = await storage.getUserByUsername(sanitizedUsername);
      if (!user) {
        await new Promise(resolve => setTimeout(resolve, 100 + Math.random() * 200));
        return res.status(404).json({ error: "User not found" });
      }

      console.log("Generating authentication options for user:", user.id);
      const options = await generateAuthenticationOptionsForUser(user.id);

      // Store pending login data without authenticating the session
      req.session.pendingLogin = {
        userId: user.id,
        username: sanitizedUsername,
      };
      req.session.challenge = options.challenge;

      res.json(options);
    } catch (error: any) {
      console.error("Login options error:", error?.message, error?.stack);
      res.status(500).json({ error: "Failed to generate authentication options", details: error?.message });
    }
  });

  app.post("/api/auth/login/verify", await rateLimit("auth", RATE_LIMIT_MAX_AUTH), async (req, res) => {
    try {
      const { response } = req.body as { response: AuthenticationResponseJSON };
      const pendingLogin = req.session.pendingLogin;
      const challenge = req.session.challenge;

      // CRITICAL: Ensure no authenticated session exists during verification
      if (req.session.userId) {
        console.error("Invalid state: authenticated session during login verification");
        req.session.destroy((err) => {
          if (err) console.error("Session destruction error:", err);
        });
        res.clearCookie("__cartel_sid");
        return res.status(400).json({ error: "Invalid authentication state" });
      }

      if (!pendingLogin || !challenge) {
        return res.status(400).json({ error: "No authentication in progress" });
      }

      const { userId, username } = pendingLogin;
      const verification = await verifyAuthentication(userId, response, challenge);

      if (verification.verified) {
        // Only now set the authenticated session
        req.session.userId = userId;
        req.session.username = username;
        req.session.csrfToken = generateCsrfToken();
        delete req.session.pendingLogin;

        await storage.createLog({
          userId,
          action: "LOGIN_SUCCESS",
          details: "FIDO2 authentication successful",
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "success",
        });

        res.json({ 
          verified: true, 
          username: username,
          csrfToken: req.session.csrfToken,
        });
      } else {
        // CRITICAL: Destroy session completely on auth failure
        await storage.createLog({
          userId,
          action: "LOGIN_FAILED",
          details: "FIDO2 authentication failed",
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "warning",
        });

        req.session.destroy((err) => {
          if (err) {
            console.error("Session destruction error:", err);
          }
          res.clearCookie("__cartel_sid");
          res.status(400).json({ error: "Authentication failed" });
        });
      }
    } catch (error: any) {
      console.error("Login verify error:", error);
      // Clear pending login on error and ensure no session data persists
      if (req.session.pendingLogin) {
        await storage.createLog({
          userId: req.session.pendingLogin.userId,
          action: "LOGIN_ERROR",
          details: `Authentication error: ${error.message}`,
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "error",
        });
      }
      // CRITICAL: Destroy session completely on error
      req.session.destroy((err) => {
        if (err) {
          console.error("Session destruction error:", err);
        }
        res.clearCookie("__cartel_sid");
        res.status(500).json({ error: "Authentication verification failed" });
      });
    }
  });

  app.post("/api/auth/logout", requireAuth, verifyCsrf, async (req, res) => {
    const userId = req.session.userId;

    await storage.createLog({
      userId: userId!,
      action: "LOGOUT",
      details: "User logged out",
      ipAddress: getClientIp(req),
      userAgent: req.get("user-agent"),
      type: "info",
    });

    req.session.destroy((err) => {
      if (err) {
        return res.status(500).json({ error: "Logout failed" });
      }
      res.clearCookie("__cartel_sid");
      res.json({ success: true });
    });
  });

  app.get("/api/files", requireAuth, async (req, res) => {
    try {
      const files = await storage.getFilesByUserId(req.session.userId!);

      const sanitizedFiles = files.map((file) => ({
        id: file.id,
        originalName: sanitizeString(file.originalName),
        encryptedName: file.encryptedName,
        mimeType: file.mimeType,
        size: file.size,
        createdAt: file.createdAt,
        updatedAt: file.updatedAt,
        expiresAt: file.expiresAt,
        autoDestructEnabled: file.autoDestructEnabled,
        extensionCount: file.extensionCount,
      }));

      res.json(sanitizedFiles);
    } catch (error: any) {
      console.error("Get files error:", error);
      res.status(500).json({ error: "Failed to retrieve files" });
    }
  });

  app.get("/api/storage", requireAuth, async (req, res) => {
    try {
      const totalUsed = await storage.getTotalStorageByUserId(req.session.userId!);
      res.json({ 
        used: totalUsed,
        total: MAX_STORAGE_PER_USER,
        percentage: Math.round((totalUsed / MAX_STORAGE_PER_USER) * 100),
      });
    } catch (error: any) {
      console.error("Get storage error:", error);
      res.status(500).json({ error: "Failed to retrieve storage info" });
    }
  });

  // New streaming multipart upload endpoint
  app.post("/api/files/upload-stream", requireAuth, verifyCsrf, await rateLimit("upload", RATE_LIMIT_MAX_UPLOAD), upload.single("file"), async (req, res) => {
    try {
      const userId = req.session.userId!;
      const file = req.file;

      if (!file) {
        return res.status(400).json({ error: "No file uploaded" });
      }

      console.log("Streaming upload received", {
        userId,
        fileName: file.originalname,
        size: file.size,
        mimeType: file.mimetype,
      });

      const currentStorage = await storage.getTotalStorageByUserId(userId);
      if (currentStorage + file.size > MAX_STORAGE_PER_USER) {
        return res.status(400).json({ 
          error: `Storage limit exceeded. Current: ${currentStorage}, Limit: ${MAX_STORAGE_PER_USER}` 
        });
      }

      const encrypted = encryptData(file.buffer, userId);
      const encryptedName = generateEncryptedFileName(file.originalname, userId);

      const newFile = await storage.createFile({
        userId,
        originalName: file.originalname,
        encryptedName,
        encryptedData: encrypted.data,
        iv: encrypted.iv,
        authTag: encrypted.authTag,
        salt: encrypted.salt,
        size: file.size,
        mimeType: file.mimetype || "application/octet-stream",
        autoDestructEnabled: true,
        expiresAt: new Date(Date.now() + 7 * 24 * 60 * 60 * 1000),
      });

      await storage.createLog({
        userId,
        action: "FILE_UPLOADED",
        details: `Uploaded: ${file.originalname} (${file.size} bytes)`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "success",
      });

      console.log("File uploaded successfully (streaming):", newFile.id);
      res.json({
        id: newFile.id,
        originalName: newFile.originalName,
        encryptedName: newFile.encryptedName,
        size: newFile.size,
        createdAt: newFile.createdAt,
      });
    } catch (error: any) {
      console.error("Streaming upload error:", error?.message, error?.stack);
      res.status(500).json({ error: "Failed to upload file", details: error?.message });
    }
  });

  // Legacy base64 upload endpoint (keep for backwards compatibility)
  app.post("/api/files/upload", requireAuth, verifyCsrf, await rateLimit("upload", RATE_LIMIT_MAX_UPLOAD), async (req, res) => {
    try {
      if (!req.body || typeof req.body !== 'object') {
        console.error("Invalid request body - body not parsed");
        return res.status(400).json({ error: "Invalid request body - ensure Content-Type is application/json" });
      }

      console.log("Upload request received", {
        userId: req.session.userId,
        contentType: req.headers['content-type'],
        hasFileName: !!req.body?.fileName,
        hasFileData: !!req.body?.fileData,
        fileDataLength: req.body?.fileData?.length
      });

      const { fileName, fileData, mimeType } = req.body;
      const userId = req.session.userId!;

      if (!fileName || !fileData) {
        console.error("Missing fileName or fileData", { fileName, hasFileData: !!fileData });
        return res.status(400).json({ error: "File name and data required" });
      }

      if (!isValidFilename(fileName)) {
        console.error("Invalid filename:", fileName);
        return res.status(400).json({ error: "Invalid file name" });
      }

      const fileBuffer = Buffer.from(fileData, "base64");
      console.log("File buffer created", { bufferLength: fileBuffer.length });

      if (fileBuffer.length > MAX_FILE_SIZE) {
        console.error("File too large:", fileBuffer.length);
        return res.status(400).json({ error: `File exceeds maximum size of ${MAX_FILE_SIZE / 1024 / 1024}MB` });
      }

      const currentStorage = await storage.getTotalStorageByUserId(userId);
      if (currentStorage + fileBuffer.length > MAX_STORAGE_PER_USER) {
        console.error("Storage limit exceeded:", { currentStorage, fileSize: fileBuffer.length });
        return res.status(400).json({ error: "Storage limit exceeded" });
      }

      const sanitizedMimeType = sanitizeString(mimeType || "application/octet-stream");
      console.log("Encrypting file...");
      const encrypted = encryptData(fileBuffer, userId);
      const encryptedName = generateEncryptedFileName();

      console.log("Creating file in database...");
      // Calculate expiry time (24 hours from now by default)
      const expiresAt = new Date(Date.now() + 24 * 60 * 60 * 1000);

      const file = await storage.createFile({
        userId,
        originalName: sanitizeString(fileName),
        encryptedName,
        mimeType: sanitizedMimeType,
        size: fileBuffer.length,
        encryptedData: encrypted.encryptedData,
        iv: encrypted.iv,
        authTag: encrypted.authTag,
        salt: encrypted.salt,
        expiresAt,
        autoDestructEnabled: true,
      });

      await storage.createLog({
        userId,
        action: "FILE_UPLOADED",
        details: `Encrypted and stored: ${sanitizeString(fileName)} (${fileBuffer.length} bytes)`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "success",
      });

      console.log("File uploaded successfully:", file.id);
      res.json({
        id: file.id,
        originalName: file.originalName,
        encryptedName: file.encryptedName,
        size: file.size,
        createdAt: file.createdAt,
      });
    } catch (error: any) {
      console.error("Upload error:", error?.message, error?.stack);
      res.status(500).json({ error: "Failed to upload file", details: error?.message });
    }
  });

  // Chunked upload storage - store chunks temporarily in memory
  const chunkedUploads = new Map<string, {
    chunks: Map<number, string>;
    totalChunks: number;
    fileName: string;
    mimeType: string;
    userId: string;
    createdAt: Date;
  }>();

  // Cleanup old incomplete uploads every 5 minutes
  setInterval(() => {
    const now = Date.now();
    const entries = Array.from(chunkedUploads.entries());
    for (const [uploadId, upload] of entries) {
      // Remove uploads older than 1 hour
      if (now - upload.createdAt.getTime() > 60 * 60 * 1000) {
        console.log(`[ChunkedUpload] Cleaning up stale upload: ${uploadId}`);
        chunkedUploads.delete(uploadId);
      }
    }
  }, 5 * 60 * 1000);

  // Initialize chunked upload
  app.post("/api/files/upload-init", requireAuth, verifyCsrf, await rateLimit("upload", RATE_LIMIT_MAX_UPLOAD), async (req, res) => {
    try {
      const userId = req.session.userId!;
      const { fileName, mimeType, totalChunks, totalSize } = req.body;

      if (!fileName || typeof fileName !== "string" || !isValidFilename(fileName)) {
        return res.status(400).json({ error: "Invalid filename" });
      }

      if (!totalChunks || typeof totalChunks !== "number" || totalChunks < 1) {
        return res.status(400).json({ error: "Invalid total chunks" });
      }

      if (!totalSize || typeof totalSize !== "number" || totalSize < 1) {
        return res.status(400).json({ error: "Invalid total size" });
      }

      if (totalSize > MAX_FILE_SIZE) {
        return res.status(413).json({ error: "File too large" });
      }

      // Check storage quota
      const currentStorage = await storage.getTotalStorageByUserId(userId);
      if (currentStorage + totalSize > MAX_STORAGE_PER_USER) {
        return res.status(413).json({ error: "Storage quota exceeded" });
      }

      const uploadId = crypto.randomBytes(32).toString("hex");

      chunkedUploads.set(uploadId, {
        chunks: new Map(),
        totalChunks,
        fileName: sanitizeString(fileName),
        mimeType: sanitizeString(mimeType || "application/octet-stream"),
        userId,
        createdAt: new Date(),
      });

      console.log(`[ChunkedUpload] Initialized upload ${uploadId.substring(0, 8)}... for ${fileName} (${totalChunks} chunks)`);

      res.json({ uploadId, message: "Upload initialized" });
    } catch (error: any) {
      console.error("Chunk init error:", error?.message);
      res.status(500).json({ error: "Failed to initialize upload" });
    }
  });

  // Upload a chunk
  app.post("/api/files/upload-chunk", requireAuth, verifyCsrf, upload.single("chunk"), async (req, res) => {
    try {
      const userId = req.session.userId!;
      const { uploadId, chunkNumber, totalChunks } = req.body;
      const chunk = req.file;

      if (!uploadId || typeof uploadId !== "string") {
        return res.status(400).json({ error: "Invalid upload ID" });
      }

      const uploadSession = chunkedUploads.get(uploadId);
      if (!uploadSession) {
        return res.status(404).json({ error: "Upload session not found or expired" });
      }

      if (uploadSession.userId !== userId) {
        return res.status(403).json({ error: "Unauthorized" });
      }

      const chunkNum = parseInt(chunkNumber, 10);
      if (isNaN(chunkNum) || chunkNum < 0 || chunkNum >= uploadSession.totalChunks) {
        return res.status(400).json({ error: "Invalid chunk number" });
      }

      if (!chunk || !chunk.buffer) {
        return res.status(400).json({ error: "No chunk data received" });
      }

      // Store chunk as base64
      uploadSession.chunks.set(chunkNum, chunk.buffer.toString("base64"));

      const receivedChunks = uploadSession.chunks.size;
      console.log(`[ChunkedUpload] Received chunk ${chunkNum + 1}/${uploadSession.totalChunks} for ${uploadId.substring(0, 8)}...`);

      res.json({
        success: true,
        chunkNumber: chunkNum,
        receivedChunks,
        totalChunks: uploadSession.totalChunks,
      });
    } catch (error: any) {
      console.error("Chunk upload error:", error?.message);
      res.status(500).json({ error: "Failed to upload chunk" });
    }
  });

  // Complete chunked upload - merge chunks and save
  app.post("/api/files/upload-complete", requireAuth, verifyCsrf, await rateLimit("upload", RATE_LIMIT_MAX_UPLOAD), async (req, res) => {
    try {
      const userId = req.session.userId!;
      const { uploadId } = req.body;

      if (!uploadId || typeof uploadId !== "string") {
        return res.status(400).json({ error: "Invalid upload ID" });
      }

      const uploadSession = chunkedUploads.get(uploadId);
      if (!uploadSession) {
        return res.status(404).json({ error: "Upload session not found or expired" });
      }

      if (uploadSession.userId !== userId) {
        return res.status(403).json({ error: "Unauthorized" });
      }

      // Verify all chunks received
      if (uploadSession.chunks.size !== uploadSession.totalChunks) {
        return res.status(400).json({
          error: "Missing chunks",
          received: uploadSession.chunks.size,
          expected: uploadSession.totalChunks,
        });
      }

      console.log(`[ChunkedUpload] Merging ${uploadSession.totalChunks} chunks for ${uploadId.substring(0, 8)}...`);

      // Merge all chunks in order
      const sortedChunks: string[] = [];
      for (let i = 0; i < uploadSession.totalChunks; i++) {
        const chunk = uploadSession.chunks.get(i);
        if (!chunk) {
          return res.status(400).json({ error: `Missing chunk ${i}` });
        }
        sortedChunks.push(chunk);
      }

      // Combine base64 chunks into buffer
      const combinedBuffer = Buffer.concat(
        sortedChunks.map(chunk => Buffer.from(chunk, "base64"))
      );

      // Encrypt the combined data
      const encrypted = encryptData(combinedBuffer, userId);
      const encryptedFileName = generateEncryptedFileName();

      // Calculate expiration (7 days default)
      const expiresAt = new Date();
      expiresAt.setDate(expiresAt.getDate() + 7);

      // Save to database
      const file = await storage.createFile({
        userId,
        originalName: uploadSession.fileName,
        encryptedName: encryptedFileName,
        mimeType: uploadSession.mimeType,
        size: combinedBuffer.length,
        encryptedData: encrypted.encryptedData,
        iv: encrypted.iv,
        authTag: encrypted.authTag,
        salt: encrypted.salt,
        expiresAt,
        autoDestructEnabled: true,
      });

      // Clean up upload session
      chunkedUploads.delete(uploadId);

      await storage.createLog({
        userId,
        action: "FILE_UPLOADED",
        details: `Chunked upload complete: ${uploadSession.fileName} (${combinedBuffer.length} bytes)`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "success",
      });

      console.log(`[ChunkedUpload] Completed upload ${uploadId.substring(0, 8)}... -> file ${file.id}`);

      res.json({
        id: file.id,
        originalName: file.originalName,
        encryptedName: file.encryptedName,
        size: file.size,
        createdAt: file.createdAt,
      });
    } catch (error: any) {
      console.error("Chunk complete error:", error?.message, error?.stack);
      res.status(500).json({ error: "Failed to complete upload", details: error?.message });
    }
  });

  // Cancel/abort chunked upload
  app.post("/api/files/upload-abort", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const { uploadId } = req.body;

      if (!uploadId || typeof uploadId !== "string") {
        return res.status(400).json({ error: "Invalid upload ID" });
      }

      const uploadSession = chunkedUploads.get(uploadId);
      if (uploadSession && uploadSession.userId === userId) {
        chunkedUploads.delete(uploadId);
        console.log(`[ChunkedUpload] Aborted upload ${uploadId.substring(0, 8)}...`);
      }

      res.json({ success: true });
    } catch (error: any) {
      console.error("Chunk abort error:", error?.message);
      res.status(500).json({ error: "Failed to abort upload" });
    }
  });

  app.get("/api/files/:id/download", requireAuth, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      const decrypted = decryptData(
        file.encryptedData,
        file.iv,
        file.authTag,
        file.salt,
        userId
      );

      await storage.createLog({
        userId,
        action: "FILE_DOWNLOADED",
        details: `Decrypted and downloaded: ${file.originalName}`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "success",
      });

      res.json({
        fileName: file.originalName,
        mimeType: file.mimeType,
        data: decrypted.toString("base64"),
      });
    } catch (error: any) {
      console.error("Download error:", error);
      res.status(500).json({ error: "Failed to download file" });
    }
  });

  app.get("/api/files/:id/view", requireAuth, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      const decrypted = decryptData(
        file.encryptedData,
        file.iv,
        file.authTag,
        file.salt,
        userId
      );

      await storage.createLog({
        userId,
        action: "FILE_VIEWED",
        details: `Viewed: ${file.originalName}`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "info",
      });

      res.json({
        fileName: file.originalName,
        mimeType: file.mimeType,
        size: file.size,
        data: decrypted.toString("base64"),
        createdAt: file.createdAt,
      });
    } catch (error: any) {
      console.error("View error:", error);
      res.status(500).json({ error: "Failed to view file" });
    }
  });

  // Get file TTL information
  app.get("/api/files/:id/ttl", requireAuth, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      const now = Date.now();
      const expiresAtMs = file.expiresAt.getTime();
      const remainingMs = Math.max(0, expiresAtMs - now);

      res.json({
        expiresAt: file.expiresAt,
        remainingSeconds: Math.floor(remainingMs / 1000),
        autoDestructEnabled: file.autoDestructEnabled,
        extensionCount: file.extensionCount,
        lastExtendedAt: file.lastExtendedAt,
      });
    } catch (error: any) {
      console.error("Get TTL error:", error);
      res.status(500).json({ error: "Failed to get file TTL" });
    }
  });

  // Extend file TTL by 24 hours
  app.post("/api/files/:id/extend", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      // Extend by 24 hours (86400 seconds)
      const extendedFile = await storage.extendFileTTL(fileId, userId, 24 * 60 * 60);

      if (!extendedFile) {
        return res.status(500).json({ error: "Failed to extend file TTL" });
      }

      await storage.createLog({
        userId,
        action: "FILE_TTL_EXTENDED",
        details: `Extended TTL for: ${file.originalName} (extension #${extendedFile.extensionCount})`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "info",
      });

      const now = Date.now();
      const remainingMs = Math.max(0, extendedFile.expiresAt.getTime() - now);

      res.json({
        success: true,
        expiresAt: extendedFile.expiresAt,
        remainingSeconds: Math.floor(remainingMs / 1000),
        extensionCount: extendedFile.extensionCount,
      });
    } catch (error: any) {
      console.error("Extend TTL error:", error);
      res.status(500).json({ error: "Failed to extend file TTL" });
    }
  });

  app.delete("/api/files/:id", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      const deleted = await storage.deleteFile(fileId, userId);

      if (deleted) {
        await storage.createLog({
          userId,
          action: "FILE_DELETED",
          details: `Permanently removed: ${file.originalName}`,
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "warning",
        });

        res.json({ success: true });
      } else {
        res.status(500).json({ error: "Failed to delete file" });
      }
    } catch (error: any) {
      console.error("Delete error:", error);
      res.status(500).json({ error: "Failed to delete file" });
    }
  });

  // Generate share link for a file
  app.post("/api/files/:id/share", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      // Generate a random 32-character password
      const sharePassword = crypto.randomBytes(16).toString("hex");

      // Create a hash of the password to store
      const passwordHash = crypto.createHash("sha256").update(sharePassword).digest("hex");

      // Update file with share password hash
      await storage.updateFileSharePassword(fileId, userId, passwordHash);

      await storage.createLog({
        userId,
        action: "FILE_SHARE_CREATED",
        details: `Share link created for: ${file.originalName}`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "info",
      });

      const shareUrl = `${req.protocol}://${req.get("host")}/share/${fileId}?password=${sharePassword}`;

      res.json({
        shareUrl,
        password: sharePassword,
        expiresAt: file.expiresAt,
      });
    } catch (error: any) {
      console.error("Share error:", error);
      res.status(500).json({ error: "Failed to create share link" });
    }
  });

  // Public endpoint to access shared files
  app.get("/share/:id", async (req, res) => {
    try {
      const fileId = req.params.id;
      const password = req.query.password as string;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).send("Invalid file ID");
      }

      if (!password || typeof password !== "string") {
        return res.status(401).send("Password required");
      }

      const file = await storage.getFileByIdWithoutUserCheck(fileId);

      if (!file || file.securelyDeleted) {
        return res.status(404).send("File not found or has been deleted");
      }

      // Check if file has expired
      if (file.expiresAt < new Date()) {
        return res.status(410).send("File has expired");
      }

      // Verify password
      if (!file.sharePasswordHash) {
        return res.status(403).send("File is not shared");
      }

      const passwordHash = crypto.createHash("sha256").update(password).digest("hex");
      if (passwordHash !== file.sharePasswordHash) {
        await storage.createLog({
          action: "SHARE_ACCESS_DENIED",
          details: `Invalid password attempt for shared file: ${file.id}`,
          ipAddress: getClientIp(req),
          userAgent: req.get("user-agent"),
          type: "warning",
        });
        return res.status(401).send("Invalid password");
      }

      // Decrypt and send file
      const decrypted = decryptData(
        file.encryptedData,
        file.iv,
        file.authTag,
        file.salt,
        file.userId
      );

      await storage.createLog({
        action: "SHARE_ACCESS_SUCCESS",
        details: `Shared file accessed: ${file.originalName}`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "info",
      });

      res.setHeader("Content-Type", file.mimeType || "application/octet-stream");
      res.setHeader("Content-Disposition", `attachment; filename="${file.originalName}"`);
      res.send(decrypted);
    } catch (error: any) {
      console.error("Share access error:", error);
      res.status(500).send("Failed to access shared file");
    }
  });

  // Revoke share link
  app.delete("/api/files/:id/share", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const fileId = req.params.id;

      if (!fileId || typeof fileId !== "string" || fileId.length > 100) {
        return res.status(400).json({ error: "Invalid file ID" });
      }

      const file = await storage.getFileById(fileId, userId);

      if (!file) {
        return res.status(404).json({ error: "File not found" });
      }

      await storage.updateFileSharePassword(fileId, userId, null);

      await storage.createLog({
        userId,
        action: "FILE_SHARE_REVOKED",
        details: `Share link revoked for: ${file.originalName}`,
        ipAddress: getClientIp(req),
        userAgent: req.get("user-agent"),
        type: "info",
      });

      res.json({ success: true });
    } catch (error: any) {
      console.error("Revoke share error:", error);
      res.status(500).json({ error: "Failed to revoke share link" });
    }
  });

  app.get("/api/logs", requireAuth, async (req, res) => {
    try {
      const limitStr = req.query.limit as string;
      const limit = Math.min(Math.max(parseInt(limitStr) || 100, 1), 500);
      const logs = await storage.getLogsByUserId(req.session.userId!, limit);
      res.json(logs);
    } catch (error: any) {
      console.error("Get logs error:", error);
      res.status(500).json({ error: "Failed to retrieve logs" });
    }
  });

  app.get("/api/settings", requireAuth, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const user = await storage.getUser(userId);

      if (!user) {
        return res.status(404).json({ error: "User not found" });
      }

      let settings = await storage.getUserSettings(userId);

      if (!settings) {
        settings = await storage.createUserSettings({
          userId,
          sessionTimeout: 1800,
          autoLock: true,
          twoFactorEnabled: false,
        });
      }

      res.json({
        ...settings,
        discordInvite: user.discordInvite,
        bitcoinAddress: user.bitcoinAddress,
      });
    } catch (error: any) {
      console.error("Get settings error:", error);
      res.status(500).json({ error: "Failed to retrieve settings" });
    }
  });

  app.put("/api/settings", requireAuth, verifyCsrf, async (req, res) => {
    try {
      const userId = req.session.userId!;
      const { sessionTimeout, autoLock, twoFactorEnabled, discordInvite, bitcoinAddress } = req.body;

      const settingsUpdates: any = {};
      if (sessionTimeout !== undefined && typeof sessionTimeout === "number" && sessionTimeout >= 300 && sessionTimeout <= 7200) {
        settingsUpdates.sessionTimeout = sessionTimeout;
      }
      if (autoLock !== undefined && typeof autoLock === "boolean") {
        settingsUpdates.autoLock = autoLock;
      }
      if (twoFactorEnabled !== undefined && typeof twoFactorEnabled === "boolean") {
        settingsUpdates.twoFactorEnabled = twoFactorEnabled;
      }

      const userUpdates: { discordInvite?: string; bitcoinAddress?: string } = {};
      if (discordInvite !== undefined && typeof discordInvite === "string") {
        userUpdates.discordInvite = discordInvite;
      }
      if (bitcoinAddress !== undefined && typeof bitcoinAddress === "string") {
        userUpdates.bitcoinAddress = bitcoinAddress;
      }

      if (Object.keys(settingsUpdates).length > 0) {
        await storage.updateUserSettings(userId, settingsUpdates);
      }

      if (Object.keys(userUpdates).length > 0) {
        await storage.updateUser(userId, userUpdates);
      }

      // Fetch the updated settings and user data to return
      const updatedSettings = await storage.getUserSettings(userId);
      const updatedUser = await storage.getUser(userId);

      res.json({
        ...(updatedSettings || {}),
        discordInvite: updatedUser?.discordInvite,
        bitcoinAddress: updatedUser?.bitcoinAddress,
      });
    } catch (error: any) {
      console.error("Update settings error:", error);
      res.status(500).json({ error: "Failed to update settings" });
    }
  });

  setInterval(async () => {
    try {
      await storage.cleanupExpiredRateLimits();
    } catch (error) {
      console.error("Rate limit cleanup error:", error);
    }
  }, 5 * 60 * 1000);

  return httpServer;
}
