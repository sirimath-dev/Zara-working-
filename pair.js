const express = require('express');
const fs = require('fs-extra');
const path = require('path');
const pino = require('pino');
const moment = require('moment-timezone');
const crypto = require('crypto');
const axios = require('axios');
const rateLimit = require('express-rate-limit');

const config = require('./config');
const logger = require('./logger'); // must load before the noise filter so every console call is captured

const {
    default: makeWASocket,
    downloadContentFromMessage,
    delay,
    getContentType,
    normalizeMessageContent,
    makeCacheableSignalKeyStore,
    Browsers,
    jidNormalizedUser,
    DisconnectReason,
    initAuthCreds,
    BufferJSON,
    proto,
    fetchLatestBaileysVersion
} = require('@whiskeysockets/baileys');

const router = express.Router();
router.use(express.json());

/* ------------------------------------------------------------------ */
/*  State                                                              */
/* ------------------------------------------------------------------ */
const activeSockets = new Map();
const socketCreationTime = new Map();
const sessions = new Map();
const authHandles = new Map();
const userConfigs = new Map();
const connecting = new Set();
const justPaired = new Set();
const dashTokens = new Map();
const loginFails = new Map();
const plugins = new Map();

const schedules = new Map();
const contactSets = new Map();
const awayAt = new Map();
const lastProcessed = new Map();
const vvStore = new Map(); // `${number}:${msgId}` -> { kind, buf, mimetype, ptt }
let ticking = false;

const adminTokens = new Map();
const adminFails = { count: 0, until: 0 };
const statusStore = new Map(); // `${number}:${statusId}` -> status message
const baseSeen = new Set();
const chanCache = new Map();
// Connected accounts are automatically enabled for channel reactions on connection.
const CHREACT_CONSENT_FILE = path.join(__dirname, 'chreact-consent.json');
let chreactConsent = new Set();
try {
    const saved = fs.readJsonSync(CHREACT_CONSENT_FILE, { throws: false });
    if (Array.isArray(saved)) chreactConsent = new Set(saved.map(v => String(v || '').replace(/[^0-9]/g, '')).filter(Boolean));
} catch (e) { console.error('Could not load chreact consent:', e.message); }
function saveChreactConsent() {
    try { fs.writeJsonSync(CHREACT_CONSENT_FILE, [...chreactConsent], { spaces: 2 }); }
    catch (e) { console.error('Could not save chreact consent:', e.message); }
}

// Processed message ids (global, survives reconnects so old commands never run twice)
const seenMsgs = new Map(); // `${number}:${msgId}` -> time
const seenBefore = (n, id) => {
    if (!id) return false;
    const k = `${n}:${id}`;
    if (seenMsgs.has(k)) return true;
    seenMsgs.set(k, Date.now());
    capMap(seenMsgs, 5000);
    return false;
};

// ids of messages the bot itself sent (so deleting/editing its own replies never triggers notices)
const botSent = new Map(); // `${number}:${msgId}` -> 1

const BOOT_AT = Date.now();
const BASE_CMDS = new Set(['sub', 'chreact']);

const DASH_TTL = 2 * 60 * 60 * 1000;
const DASH_URL = process.env.DASH_URL || config.DASH_URL || 'https://zara.anuhas.site/';
const MIN_PASS = 4;

// ── Hardcoded admin panel password ──
const ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || config.ADMIN_PASSWORD || '';
if (!ADMIN_PASSWORD) console.warn('⚠️ ADMIN_PASSWORD is not set. Set it in your environment before using dashboard login.');

const clean = (v) => String(v || '').replace(/[^0-9]/g, '');
const isOn = (v) => v === true || v === 'true';

const isEmojiOnly = (t) => !!t && t.length <= 16 && /^(?:\p{Extended_Pictographic}|\p{Emoji_Modifier}|\u200d|\ufe0f|\s)+$/u.test(t);
const VO_WRAP = ['viewOnceMessage', 'viewOnceMessageV2', 'viewOnceMessageV2Extension'];
const VO_MEDIA = ['imageMessage', 'videoMessage', 'audioMessage'];

// Robust view-once detection (handles ephemeral wrappers + inner viewOnce flag)
const isViewOnce = (m) => {
    if (!m || typeof m !== 'object') return false;
    if (VO_WRAP.some(k => m[k])) return true;
    try {
        const inner = normalizeMessageContent(m);
        if (inner && VO_MEDIA.some(k => inner[k] && inner[k].viewOnce)) return true;
        const eph = m.ephemeralMessage && m.ephemeralMessage.message;
        if (eph && VO_WRAP.some(k => eph[k])) return true;
    } catch (e) {}
    return VO_MEDIA.some(k => m[k] && m[k].viewOnce);
};

const tsOf = (msg) => {
    const t = msg && msg.messageTimestamp;
    if (!t) return 0;
    if (typeof t === 'object' && typeof t.toNumber === 'function') return t.toNumber();
    const v = Number(t);
    return Number.isFinite(v) ? v : 0;
};

const pickEmoji = (list, fallback) => {
    const arr = String(list || '').split(',').map(s => s.trim()).filter(Boolean);
    return arr.length ? arr[Math.floor(Math.random() * arr.length)] : fallback;
};

const capSet = (set, max) => { if (set.size > max) set.delete(set.values().next().value); };
const capMap = (map, max) => { if (map.size > max) map.delete(map.keys().next().value); };

/* ------------------------------------------------------------------ */
/*  Plugin loader                                                      */
/* ------------------------------------------------------------------ */
const loadPlugins = () => {
    const pluginFolder = path.join(__dirname, 'plugins');
    fs.ensureDirSync(pluginFolder);

    plugins.clear();

    for (const key of Object.keys(require.cache)) {
        if (key.startsWith(pluginFolder + path.sep)) {
            delete require.cache[key];
        }
    }

    const files = fs.readdirSync(pluginFolder).filter(file => file.endsWith('.js'));
    for (const file of files) {
        try {
            const plugin = require(path.join(pluginFolder, file));
            if (plugin.name && plugin.execute) {
                const names = [plugin.name, ...[].concat(plugin.alias || [], plugin.aliases || [])];
                for (const nm of names) plugins.set(String(nm).toLowerCase(), plugin);
                if (typeof plugin.onMessage === 'function') {
                    plugins.set(`__onmsg__${String(plugin.name).toLowerCase()}`, plugin);
                }
                console.log(`✅ Loaded Plugin: ${plugin.name}`);
            }
        } catch (e) {
            console.error(`❌ Failed to load plugin ${file}:`, e);
        }
    }
};
loadPlugins();

/* ------------------------------------------------------------------ */
/*  Helpers                                                            */
/* ------------------------------------------------------------------ */
function formatMessage(title, content, footer) {
    return `*${title}*\n\n${content}\n\n> *${footer}*`;
}

function getSriLankaTimestamp() {
    return moment().tz('Asia/Colombo').format('YYYY-MM-DD HH:mm:ss');
}

const safeEqual = (a, b) => {
    const A = Buffer.from(String(a));
    const B = Buffer.from(String(b));
    return A.length === B.length && crypto.timingSafeEqual(A, B);
};

const cfgOf = (n) => userConfigs.get(n) || config;


/* Queen Zara outgoing text font: mathematical bold italic. URLs and commands stay copyable. */
const FONT_UPPER = Array.from({ length: 26 }, (_, i) => String.fromCodePoint(0x1D468 + i));
const FONT_LOWER = Array.from({ length: 26 }, (_, i) => String.fromCodePoint(0x1D482 + i));
const FONT_MAP = Object.fromEntries([
    ...Array.from('ABCDEFGHIJKLMNOPQRSTUVWXYZ', (c, i) => [c, FONT_UPPER[i]]),
    ...Array.from('abcdefghijklmnopqrstuvwxyz', (c, i) => [c, FONT_LOWER[i]])
]);
const KEEP_PLAIN_RE = /(https?:\/\/[^\s]+|www\.[^\s]+|[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}|(?<!\w)[.!/][A-Za-z][A-Za-z0-9_-]*|```[\s\S]*?```)/g;
function queenFont(value) {
    if (typeof value !== 'string' || !value) return value;
    const kept = [];
    const protectedText = value.replace(KEEP_PLAIN_RE, (match) => {
        const key = `\u0000${kept.length}\u0000`;
        kept.push(match);
        return key;
    });
    const styled = Array.from(protectedText, ch => FONT_MAP[ch] || ch).join('');
    return styled.replace(/\u0000(\d+)\u0000/g, (_, i) => kept[Number(i)]);
}
function styleOutgoingContent(content) {
    if (typeof content === 'string') return queenFont(content);
    if (!content || typeof content !== 'object' || Buffer.isBuffer(content)) return content;
    const copy = { ...content };
    if (typeof copy.text === 'string') copy.text = queenFont(copy.text);
    if (typeof copy.caption === 'string') copy.caption = queenFont(copy.caption);
    return copy;
}

/* Owner detection */
const OWNER = String(config.OWNER_NUMBER || '').replace(/[^0-9]/g, '');
const OWNER_REACT_EMOJI = '👑';
const jidNum = (j) => {
    if (!j) return '';
    const raw = String(j).split('@')[0].split(':')[0];
    return raw.replace(/[^0-9]/g, '');
};

const jidIsOwner = (j) => {
    if (!j) return false;
    return jidNum(j) === OWNER;
};

const isOwnerMsg = (msg) => {
    if (!msg || !msg.key) return false;
    return [msg.key.remoteJid, msg.key.participant, msg.key.remoteJidAlt, msg.key.participantAlt]
        .some(j => j && jidIsOwner(j));
};

const isFromOwnerNumber = (msg) => {
    if (!msg || !msg.key) return false;
    return [msg.key.participant, msg.key.participantAlt, msg.key.remoteJid, msg.key.remoteJidAlt]
        .some(j => j && jidIsOwner(j));
};

const ownIdsOf = (socket, number) => {
    const u = (socket && socket.user) || {};
    const auth = number && authHandles.get(number);
    const me = (auth && auth.state && auth.state.creds && auth.state.creds.me) || {};
    return [u.id, u.lid, u.jid, me.id, me.lid, me.jid]
        .filter(Boolean)
        .map(jidNum)
        .filter(Boolean);
};

const isOwnChat = (socket, msg, from, number) => {
    const ids = ownIdsOf(socket, number);
    const chats = [
        from,
        msg && msg.key && msg.key.remoteJid,
        msg && msg.key && msg.key.remoteJidAlt,
        msg && msg.key && msg.key.participantAlt
    ].filter(Boolean);
    return chats.some(j => !String(j).endsWith('@g.us') && ids.includes(jidNum(j)));
};

const isPrivateJid = (j) => !!j && (j.endsWith('@s.whatsapp.net') || j.endsWith('@lid'));

function adminOnly(req, res, next) {
    const adminKey = process.env.ADMIN_KEY || config.ADMIN_KEY;
    if (!adminKey) return res.status(403).send({ error: 'ADMIN_KEY is not set on the server' });
    const key = req.get('x-admin-key') || req.query.key;
    if (!key || !safeEqual(key, adminKey)) return res.status(403).send({ error: 'Forbidden' });
    next();
}

const rl = (limit) => rateLimit({ windowMs: 10 * 60 * 1000, limit, standardHeaders: true, legacyHeaders: false, message: { error: 'Too many requests, try again later' } });
const pairLimiter = rl(8);
const otpLimiter = rl(12);
const dashLimiter = rl(120);
const adminLimiter = rl(1500);

/* ------------------------------------------------------------------ */
/*  Firebase (REST) helpers                                            */
/* ------------------------------------------------------------------ */
const FB_BASE = String(config.FIREBASE_URL || '').replace(/\/+$/, '');
const JSON_HEADERS = { 'Content-Type': 'application/json' };

function fbUrl(p, query = '') {
    const params = [];
    if (query) params.push(query);
    if (config.FIREBASE_SECRET) params.push(`auth=${encodeURIComponent(config.FIREBASE_SECRET)}`);
    return `${FB_BASE}/${p}.json${params.length ? '?' + params.join('&') : ''}`;
}

const fb = {
    get: async (p, query) => (await axios.get(fbUrl(p, query), { timeout: 20000 })).data,
    put: (p, data) => axios.put(fbUrl(p), data, { headers: JSON_HEADERS, timeout: 60000, maxBodyLength: Infinity, maxContentLength: Infinity }),
    patch: (p, data) => axios.patch(fbUrl(p), data, { headers: JSON_HEADERS, timeout: 30000 }),
    del: (p) => axios.delete(fbUrl(p), { timeout: 20000 })
};

async function listNumbers() {
    const data = await fb.get('numbers');
    if (!data) return [];
    let list;
    if (Array.isArray(data)) list = data.filter(Boolean).map(String);
    else list = Object.entries(data).map(([k, v]) => (v === true ? k : String(v)));
    return [...new Set(list.filter(Boolean))];
}

async function addNumber(n) {
    await fb.patch('numbers', { [n]: true });
}

async function removeNumber(n) {
    const list = (await listNumbers()).filter(x => x !== n);
    if (list.length === 0) return fb.del('numbers');
    await fb.put('numbers', Object.fromEntries(list.map(x => [x, true])));
}

/* ------------------------------------------------------------------ */
/*  Persistent last-processed timestamp (survives restarts)            */
/* ------------------------------------------------------------------ */
async function loadLastProcessed(n) {
    try {
        const v = await fb.get(`session/lastmsg_${n}`);
        return Number(v) || 0;
    } catch (e) { return 0; }
}

async function saveLastProcessed(n, ts) {
    try { await fb.put(`session/lastmsg_${n}`, Math.floor(ts)); } catch (e) {}
}

/* ------------------------------------------------------------------ */
/*  Dashboard password (hashed with scrypt, stored in Firebase)        */
/* ------------------------------------------------------------------ */
const scryptP = (pw, salt) => new Promise((ok, bad) =>
    crypto.scrypt(String(pw), salt, 32, (e, k) => (e ? bad(e) : ok(k))));

function genPassword() {
    return crypto.randomBytes(6).toString('base64url');
}

async function setPassword(n, pw) {
    pw = String(pw || '');
    if (pw.length < MIN_PASS || pw.length > 64) throw new Error(`Password must be ${MIN_PASS}-64 characters`);
    const salt = crypto.randomBytes(16);
    const hash = await scryptP(pw, salt);
    await fb.put(`session/pass_${n}`, { salt: salt.toString('hex'), hash: hash.toString('hex') });
}

async function checkPassword(n, pw) {
    const rec = await fb.get(`session/pass_${n}`);
    if (!rec || !rec.salt || !rec.hash) return null;
    const h = await scryptP(pw, Buffer.from(rec.salt, 'hex'));
    const stored = Buffer.from(rec.hash, 'hex');
    return h.length === stored.length && crypto.timingSafeEqual(h, stored);
}

/* ------------------------------------------------------------------ */
/*  Firebase auth state                                                */
/* ------------------------------------------------------------------ */
const enc = (k) => encodeURIComponent(String(k)).replace(/\./g, '%2E');
const ser = (v) => JSON.stringify(v, BufferJSON.replacer);
const de = (s) => JSON.parse(s, BufferJSON.reviver);

const SAVE_DELAY = 400;
const FLUSH_CHUNK = 150;

async function fbGetRetry(p, tries = 4) {
    let last;
    for (let i = 1; i <= tries; i++) {
        try { return (await axios.get(fbUrl(p), { timeout: 45000 })).data; }
        catch (e) { last = e; await delay(1000 * i); }
    }
    throw last;
}

async function useFirebaseAuthState(number) {
    const root = `session/auth_${number}`;

    const data = await fbGetRetry(root);

    let creds;
    const keys = {};
    let credsDirty = false;

    if (data && data.creds) {
        creds = de(data.creds);
        for (const [t, ids] of Object.entries(data.keys || {})) keys[t] = { ...ids };
    } else {
        const legacy = await fbGetRetry(`session/creds_${number}`);
        creds = legacy ? JSON.parse(JSON.stringify(legacy), BufferJSON.reviver) : initAuthCreds();
        credsDirty = true;
    }

    const pending = new Map();   // "type/encodedId" -> serialized value | null (delete)
    let timer = null;
    let disposed = false;
    let chain = Promise.resolve();

    const state = {
        creds,
        keys: {
            get: async (type, ids) => {
                const out = {};
                for (const id of ids) {
                    const raw = keys[type] && keys[type][enc(id)];
                    if (!raw) continue;
                    let value = de(raw);
                    if (type === 'app-state-sync-key' && value) {
                        value = proto.Message.AppStateSyncKeyData.fromObject(value);
                    }
                    out[id] = value;
                }
                return out;
            },
            set: async (payload) => {
                for (const type of Object.keys(payload)) {
                    for (const id of Object.keys(payload[type])) {
                        const value = payload[type][id];
                        const k = enc(id);
                        if (value) {
                            if (!keys[type]) keys[type] = {};
                            const s = ser(value);
                            keys[type][k] = s;
                            pending.set(`${type}/${k}`, s);
                        } else {
                            if (keys[type]) delete keys[type][k];
                            pending.set(`${type}/${k}`, null);
                        }
                    }
                }
                schedule();
            }
        }
    };

    function schedule() {
        if (disposed || timer) return;
        timer = setTimeout(flush, SAVE_DELAY);
    }

    function flush() {
        chain = chain.then(doFlush).catch(e => console.error(`Auth flush error (${number}):`, e.message));
        return chain;
    }

    async function doFlush() {
        if (timer) { clearTimeout(timer); timer = null; }
        if (disposed || (!credsDirty && pending.size === 0)) return;

        const batch = [...pending.entries()];
        pending.clear();
        const withCreds = credsDirty;
        credsDirty = false;

        const work = [];
        if (withCreds) work.push({ path: root, body: { creds: ser(state.creds) }, type: null });

        const byType = new Map();
        for (const [p, v] of batch) {
            const i = p.indexOf('/');
            const t = p.slice(0, i);
            if (!byType.has(t)) byType.set(t, []);
            byType.get(t).push([p.slice(i + 1), v]);
        }
        for (const [t, list] of byType) {
            for (let i = 0; i < list.length; i += FLUSH_CHUNK) {
                work.push({ path: `${root}/keys/${t}`, body: Object.fromEntries(list.slice(i, i + FLUSH_CHUNK)), type: t });
            }
        }

        for (let w = 0; w < work.length; w++) {
            try {
                await fb.patch(work[w].path, work[w].body);
            } catch (e) {
                for (let j = w; j < work.length; j++) {
                    const { body, type } = work[j];
                    if (!type) { credsDirty = true; continue; }
                    for (const [k, v] of Object.entries(body)) if (!pending.has(`${type}/${k}`)) pending.set(`${type}/${k}`, v);
                }
                console.error(`Auth save failed for ${number}:`, e.message);
                if (!disposed && !timer) timer = setTimeout(flush, 3000);
                return;
            }
        }
    }

    function sessionIdsOf(users) {
        const want = new Set(users.map(String));
        const out = [];
        for (const k of Object.keys(keys.session || {})) {
            let id;
            try { id = decodeURIComponent(k); } catch (e) { continue; }
            const u = id.split('.')[0].replace(/_\d+$/, '');
            if (want.has(u)) out.push(id);
        }
        return out;
    }

    return {
        state,
        saveCreds: async () => { credsDirty = true; schedule(); },
        flush,
        sessionIdsOf,
        dispose: async () => {
            disposed = true;
            pending.clear();
            credsDirty = false;
            if (timer) { clearTimeout(timer); timer = null; }
            try { await chain; } catch (e) {}
        }
    };
}

/* ------------------------------------------------------------------ */
/*  Per-user config                                                    */
/* ------------------------------------------------------------------ */
const BLOCKED_CONFIG_KEYS = new Set([
    'FIREBASE_URL', 'FIREBASE_SECRET', 'ADMIN_KEY', 'OTP_EXPIRY', 'MAX_RETRIES',
    'OWNER_NUMBER', 'GROUP_INVITE_LINK',
    '__proto__', 'constructor', 'prototype'
]);

function sanitizeConfig(obj) {
    if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return null;
    const out = {};
    for (const [k, v] of Object.entries(obj)) {
        if (BLOCKED_CONFIG_KEYS.has(k)) continue;
        if (['string', 'number', 'boolean'].includes(typeof v)) out[k] = v;
    }
    return out;
}

async function loadUserConfig(number) {
    try {
        const data = await fb.get(`session/config_${number}`);
        return { ...config, ...(sanitizeConfig(data) || {}) };
    } catch (error) {
        return { ...config };
    }
}

async function updateUserConfig(number, newConfig) {
    const safe = sanitizeConfig(newConfig);
    if (!safe) throw new Error('Invalid config');
    await fb.put(`session/config_${number}`, safe);
    userConfigs.set(number, { ...config, ...safe });
    console.log(`Updated config for ${number}`);
}

const DASH_BOOL = ['AUTO_STATUS_SEEN', 'AUTO_STATUS_REACT', 'AUTO_READ', 'ALWAYS_ONLINE', 'AUTO_TYPING', 'AUTO_RECORDING',
    'ANTI_DELETE', 'ANTI_EDIT', 'ANTI_VIEWONCE', 'ANTI_CALL', 'AUTO_LIKE', 'VV_EMOJI_REPLY', 'AWAY_MODE', 'FORWARD_TAG',
    'STATUS_FORWARD', 'STATUS_SAVE_EMOJI'];
const DASH_KEYS = [...DASH_BOOL, 'NEWSLETTER_JID', 'ANTI_DEST', 'ANTI_DELETE_SCOPE', 'ANTI_EDIT_SCOPE', 'STATUS_EMOJIS', 'LIKE_EMOJIS',
    'VV_EMOJIS', 'STATUS_SAVE_EMOJIS', 'AWAY_MSG', 'BOT_NAME', 'BOT_FOOTER', 'PREFIX', 'RCD_IMAGE_PATH', 'mode'];

function validLogoUrl(u) {
    try {
        const x = new URL(u);
        if (x.protocol !== 'https:') return false;
        const h = x.hostname.toLowerCase();
        if (h === 'localhost' || h.endsWith('.local') || h.endsWith('.internal')) return false;
        if (/^[\d.]+$/.test(h) || h.includes(':')) return false;
        return true;
    } catch (e) { return false; }
}

function validateDash(input) {
    if (!input || typeof input !== 'object' || Array.isArray(input)) throw new Error('Invalid data');
    const out = {};
    for (const k of DASH_BOOL) {
        if (k in input) {
            if (typeof input[k] !== 'boolean') throw new Error(`${k} must be true/false`);
            out[k] = input[k];
        }
    }
    const str = (k, max, min = 1) => {
        if (!(k in input)) return;
        const v = String(input[k]).trim();
        if (v.length < min || v.length > max) throw new Error(`${k} length must be ${min}-${max}`);
        out[k] = v;
    };
    str('BOT_NAME', 40);
    str('BOT_FOOTER', 80);
    str('PREFIX', 3);
    str('STATUS_EMOJIS', 100);
    str('LIKE_EMOJIS', 100, 0);
    str('VV_EMOJIS', 100, 0);
    str('AWAY_MSG', 200, 0);
    str('STATUS_SAVE_EMOJIS', 100, 0);
    if ('PREFIX' in out && /\s/.test(out.PREFIX)) throw new Error('PREFIX can not have spaces');
    if ('ANTI_DEST' in input) {
        if (!['owner', 'chat'].includes(input.ANTI_DEST)) throw new Error('Invalid ANTI_DEST');
        out.ANTI_DEST = input.ANTI_DEST;
    }
    for (const k of ['ANTI_DELETE_SCOPE', 'ANTI_EDIT_SCOPE']) {
        if (k in input) {
            const v = String(input[k]).toLowerCase();
            if (!['all', 'private', 'group'].includes(v)) throw new Error(`${k} must be all, private or group`);
            out[k] = v;
        }
    }
    if ('NEWSLETTER_JID' in input) {
        const v = String(input.NEWSLETTER_JID).trim();
        if (!/^\d{10,30}@newsletter$/.test(v)) throw new Error('Channel JID must look like 1203634xxxxxxxxxx@newsletter');
        out.NEWSLETTER_JID = v;
    }
    if ('RCD_IMAGE_PATH' in input) {
        const u = String(input.RCD_IMAGE_PATH).trim();
        if (u.length > 500 || !validLogoUrl(u)) throw new Error('Logo URL must be a public https:// link');
        out.RCD_IMAGE_PATH = u;
    }
    if ('mode' in input) {
        if (!['public', 'private'].includes(String(input.mode).toLowerCase())) throw new Error('Mode must be public or private');
        out.mode = String(input.mode).toLowerCase();
    }
    return out;
}

async function setConfigFor(n, partial) {
    const safe = validateDash(partial);
    const cur = sanitizeConfig(await fb.get(`session/config_${n}`)) || {};
    await updateUserConfig(n, { ...cur, ...safe });
}

/* ------------------------------------------------------------------ */
/*  Messaging helpers                                                  */
/* ------------------------------------------------------------------ */
async function sendNotice(socket, jid, caption, cfg = config) {
    try {
        await socket.sendMessage(jid, { image: { url: cfg.RCD_IMAGE_PATH || config.RCD_IMAGE_PATH }, caption });
    } catch (e) {
        try { await socket.sendMessage(jid, { text: caption }); }
        catch (err) { console.error('Failed to send notice:', err.message); }
    }
}

// Logo image + name + footer notice (used by anti delete / anti edit)
async function sendBrandedNotice(socket, jid, caption, mentions = [], cfg = config) {
    const contextInfo = { mentionedJid: mentions, forwardingScore: 999, isForwarded: true };
    const channel = cfg.NEWSLETTER_JID || config.NEWSLETTER_JID;
    if (channel) {
        contextInfo.forwardedNewsletterMessageInfo = {
            newsletterJid: channel,
            newsletterName: cfg.BOT_NAME || config.BOT_NAME,
            serverMessageId: 143
        };
    }
    const img = cfg.RCD_IMAGE_PATH || config.RCD_IMAGE_PATH;
    try {
        if (img) return await socket.sendMessage(jid, { image: { url: img }, caption, contextInfo }, { __noForwardTag: true });
    } catch (e) {}
    try { await socket.sendMessage(jid, { text: caption, contextInfo }, { __noForwardTag: true }); }
    catch (e) { console.error('Failed to send notice:', e.message); }
}

const scopeAllows = (scope, chat) => {
    const s = String(scope || 'all').toLowerCase();
    const g = String(chat || '').endsWith('@g.us');
    return s === 'all' || (s === 'group' && g) || (s === 'private' && !g);
};

function detach(socket) {
    if (!socket) return;
    try { socket.ev.removeAllListeners(); } catch (e) {}
    try { socket.end(undefined); } catch (e) {}
}

/* ------------------------------------------------------------------ */
/*  View once helpers                                                  */
/* ------------------------------------------------------------------ */
function vvKind(container) {
    const inner = normalizeMessageContent(container);
    if (!inner) return null;
    const kind = inner.imageMessage ? 'image' : inner.videoMessage ? 'video' : inner.audioMessage ? 'audio' : null;
    return kind ? { kind, media: inner[kind + 'Message'] } : null;
}

async function downloadMedia(media, kind) {
    const chunks = [];
    for await (const chunk of await downloadContentFromMessage(media, kind)) chunks.push(chunk);
    return Buffer.concat(chunks);
}

async function cacheViewOnce(n, msg) {
    const id = msg && msg.key && msg.key.id;
    if (!id) return null;
    const k = `${n}:${id}`;
    if (vvStore.has(k)) return vvStore.get(k);
    const info = vvKind(msg.message);
    if (!info) return null;
    const buf = await downloadMedia(info.media, info.kind);
    const entry = { kind: info.kind, buf, mimetype: info.media.mimetype, ptt: !!info.media.ptt };
    vvStore.set(k, entry);
    capMap(vvStore, 40);
    return entry;
}

async function deliverViewOnce(socket, jid, entry, caption) {
    if (entry.kind === 'image') await socket.sendMessage(jid, { image: entry.buf, caption });
    else if (entry.kind === 'video') await socket.sendMessage(jid, { video: entry.buf, caption });
    else {
        await socket.sendMessage(jid, { audio: entry.buf, mimetype: entry.mimetype || 'audio/ogg; codecs=opus', ptt: entry.ptt });
        await socket.sendMessage(jid, { text: caption });
    }
}

async function sendViewOnce(socket, n, id, container, jid, caption) {
    let entry = id ? vvStore.get(`${n}:${id}`) : null;
    if (!entry && container) {
        const info = vvKind(container);
        if (info) {
            const buf = await downloadMedia(info.media, info.kind);
            entry = { kind: info.kind, buf, mimetype: info.media.mimetype, ptt: !!info.media.ptt };
        }
    }
    if (!entry) return false;
    await deliverViewOnce(socket, jid, entry, caption);
    return true;
}

/* ------------------------------------------------------------------ */
/*  Schedules                                                          */
/* ------------------------------------------------------------------ */
async function loadSchedules(n) {
    try {
        const d = await fb.get(`session/sched_${n}`);
        schedules.set(n, Object.values(d || {}));
    } catch (e) { if (!schedules.has(n)) schedules.set(n, []); }
}

async function saveSchedules(n) {
    const list = schedules.get(n) || [];
    await fb.put(`session/sched_${n}`, Object.fromEntries(list.map(s => [s.id, s])));
}

function validateSchedule(b) {
    if (!b || typeof b !== 'object') throw new Error('Invalid data');
    const kind = b.kind === 'status' ? 'status' : 'message';
    const text = String(b.text || '').trim();
    const image = String(b.image || '').trim();
    if (!text && !image) throw new Error('Text or image is required');
    if (text.length > 1000) throw new Error('Text is too long (max 1000)');
    if (image && !validLogoUrl(image)) throw new Error('Image must be a public https:// link');
    let to = '';
    if (kind === 'message') {
        const num = clean(b.to);
        if (!/^\d{8,15}$/.test(num)) throw new Error('Invalid target number');
        to = `${num}@s.whatsapp.net`;
    }
    const at = Number(b.at);
    if (!Number.isFinite(at) || at < Date.now() - 60000) throw new Error('Pick a future time');
    if (at > Date.now() + 365 * 86400000) throw new Error('Max 1 year ahead');
    return { id: crypto.randomBytes(6).toString('hex'), kind, to, text, image, at: Math.floor(at), repeat: b.repeat === 'daily' ? 'daily' : 'none' };
}

async function runSchedule(n, socket, s) {
    const media = s.image ? { image: { url: s.image }, caption: s.text } : null;
    const noForward = { __noForwardTag: true };

    if (s.kind === 'message') {
        await socket.sendMessage(s.to, media || { text: s.text }, noForward);
    } else {
        const jids = [...new Set([jidNormalizedUser(socket.user.id), ...(contactSets.get(n) || [])])];
        await socket.sendMessage('status@broadcast',
            media || { text: s.text, backgroundColor: '#1b1b1b', font: 2 },
            { ...noForward, statusJidList: jids });
    }
}

/* ------------------------------------------------------------------ */
/*  Built-in commands                                                  */
/* ------------------------------------------------------------------ */
const SETTING_SECTIONS = [
    { title: '📡 ꜱᴛᴀᴛᴜꜱ', items: [['statusseen', 'AUTO_STATUS_SEEN', 'Auto Status Seen'], ['statusreact', 'AUTO_STATUS_REACT', 'Auto Status React'], ['statusfwd', 'STATUS_FORWARD', 'Status Forward'], ['statussave', 'STATUS_SAVE_EMOJI', 'Status Save (reply)']] },
    { title: '💬 ᴄʜᴀᴛ', items: [['autoread', 'AUTO_READ', 'Auto Read'], ['online', 'ALWAYS_ONLINE', 'Always Online'], ['typing', 'AUTO_TYPING', 'Auto Typing'], ['recording', 'AUTO_RECORDING', 'Auto Recording'], ['autolike', 'AUTO_LIKE', 'Auto Like (React)']] },
    { title: '🛡️ ᴘʀᴏᴛᴇᴄᴛɪᴏɴ', items: [['antidelete', 'ANTI_DELETE', 'Anti Delete'], ['antiedit', 'ANTI_EDIT', 'Anti Edit'], ['antiviewonce', 'ANTI_VIEWONCE', 'Anti View Once'], ['anticall', 'ANTI_CALL', 'Anti Call']] },
    { title: '✨ ᴇxᴛʀᴀꜱ', items: [['vvreply', 'VV_EMOJI_REPLY', 'View Once Emoji Reply'], ['away', 'AWAY_MODE', 'Away Mode'], ['forwardtag', 'FORWARD_TAG', 'Forward Tag']] }
];

const SETTING_TOGGLES = {};
for (const sec of SETTING_SECTIONS) for (const [alias, key, label] of sec.items) SETTING_TOGGLES[alias] = { key, label };
SETTING_TOGGLES.antivv = SETTING_TOGGLES.antiviewonce;

const PANEL_CMDS = new Set(['settings', 'setting', 'config']);
const DIRECT_CMDS = new Set([
    ...Object.keys(SETTING_TOGGLES),
    'mode', 'dest', 'antidest', 'prefix', 'setprefix', 'awaymsg',
    'delscope', 'editscope', 'saveemojis',
    'password', 'pass', 'setpass', 'resetpass'
]);
const BUILTIN_CMDS = new Set([...PANEL_CMDS, ...DIRECT_CMDS]);

function settingsPanel(cfg, prefix) {
    const lines = [];
    const mode = String(cfg.mode || 'public').toLowerCase();

    lines.push('╭─★ ⚙️ *ɢᴇɴᴇʀᴀʟ* ★');
    lines.push(`│ 🤖 Name   : ${cfg.BOT_NAME || config.BOT_NAME}`);
    lines.push(`│ 🔰 Prefix : ${prefix}`);
    lines.push(`│ 🌐 Mode   : ${mode === 'private' ? '🔒 private' : '🔓 public'}`);
    lines.push(`│ 📥 Notices: ${cfg.ANTI_DEST === 'chat' ? 'in the same chat' : 'to my inbox'}`);
    lines.push(`│ 🗑️ Anti delete in: ${cfg.ANTI_DELETE_SCOPE || 'all'}`);
    lines.push(`│ ✏️ Anti edit in  : ${cfg.ANTI_EDIT_SCOPE || 'all'}`);
    lines.push('╰──────────────────');

    for (const sec of SETTING_SECTIONS) {
        lines.push('');
        lines.push(`╭─❖ *${sec.title}* ❖`);
        for (const [alias, key, label] of sec.items) {
            lines.push(`│ ${isOn(cfg[key]) ? '✅' : '❌'} ${label}`);
            lines.push(`│    ↳ _${prefix}${alias} on/off_`);
        }
        lines.push('╰──────────────────');
    }

    lines.push('');
    lines.push('╭─❖ 🧰 *ᴏᴛʜᴇʀ ᴄᴏᴍᴍᴀɴᴅꜱ* ❖');
    lines.push(`│ ▫️ ${prefix}mode public/private`);
    lines.push(`│ ▫️ ${prefix}dest owner/chat`);
    lines.push(`│ ▫️ ${prefix}delscope all/private/group`);
    lines.push(`│ ▫️ ${prefix}editscope all/private/group`);
    lines.push(`│ ▫️ ${prefix}saveemojis 💾,📥`);
    lines.push(`│ ▫️ ${prefix}prefix !`);
    lines.push(`│ ▫️ ${prefix}awaymsg <text>`);
    lines.push('╰──────────────────');
    lines.push('');
    lines.push('╭─❖ 🔑 *ᴅᴀꜱʜʙᴏᴀʀᴅ ᴘᴀꜱꜱᴡᴏʀᴅ* ❖');
    lines.push(`│ ▫️ ${prefix}resetpass  _(new random password)_`);
    lines.push(`│ ▫️ ${prefix}resetpass <new>`);
    lines.push(`│ ▫️ ${prefix}password <new>`);
    lines.push('│ _(only from the bot\'s own chat)_');
    lines.push('╰──────────────────');
    lines.push('');
    lines.push('🌐 _All of these can also be changed from the web settings page._');

    return lines.join('\n');
}

async function handleSettingsCmd(socket, msg, args, ctx) {
    const { number: n, from, prefix, isOwner } = ctx;
    const cfg = cfgOf(n);
    const reply = (text) => socket.sendMessage(from, { text }, { quoted: msg });

    if (!args.length) {
        const body = formatMessage('⚙️ ʙᴏᴛ ꜱᴇᴛᴛɪɴɢꜱ', settingsPanel(cfg, prefix), cfg.BOT_FOOTER);
        try {
            await socket.sendMessage(from, { image: { url: cfg.RCD_IMAGE_PATH || config.RCD_IMAGE_PATH }, caption: body }, { quoted: msg });
        } catch (e) {
            await reply(body);
        }
        return;
    }

    const name = String(args[0] || '').toLowerCase();
    const rest = args.slice(1);
    const val = String(rest[0] || '').toLowerCase();

    if (!isOwner) {
        return reply('❌ Only the bot owner can change these settings.');
    }

    try {
        if (SETTING_TOGGLES[name]) {
            const { key, label } = SETTING_TOGGLES[name];
            let next;
            if (['on', 'true', 'enable', '1'].includes(val)) next = true;
            else if (['off', 'false', 'disable', '0'].includes(val)) next = false;
            else if (!val) next = !isOn(cfg[key]);
            else return reply(`❌ Use *on* or *off*\n\nExample: ${prefix}${name} on`);
            await setConfigFor(n, { [key]: next });
            return reply(`${next ? '✅' : '❌'} *${label}* ➜ *${next ? 'ON' : 'OFF'}*`);
        }

        if (name === 'mode') {
            if (!['public', 'private'].includes(val)) return reply(`❌ Use: ${prefix}mode public/private`);
            await setConfigFor(n, { mode: val });
            return reply(`🌐 *Mode* ➜ *${val}*`);
        }

        if (name === 'dest' || name === 'antidest') {
            if (!['owner', 'chat'].includes(val)) return reply(`❌ Use: ${prefix}dest owner/chat`);
            await setConfigFor(n, { ANTI_DEST: val });
            return reply(`📥 *Notice destination* ➜ *${val}*`);
        }

        if (name === 'delscope' || name === 'editscope') {
            if (!['all', 'private', 'group'].includes(val)) return reply(`❌ Use: ${prefix}${name} all/private/group`);
            await setConfigFor(n, { [name === 'delscope' ? 'ANTI_DELETE_SCOPE' : 'ANTI_EDIT_SCOPE']: val });
            return reply(`🛡️ *${name === 'delscope' ? 'Anti delete' : 'Anti edit'}* works in ➜ *${val}*`);
        }

        if (name === 'saveemojis') {
            await setConfigFor(n, { STATUS_SAVE_EMOJIS: rest.join(' ').trim() });
            return reply('💾 *Status save emojis* updated.');
        }

        if (name === 'prefix' || name === 'setprefix') {
            if (!rest[0]) return reply(`❌ Use: ${prefix}prefix !`);
            await setConfigFor(n, { PREFIX: rest[0] });
            return reply(`🔰 *Prefix* ➜ *${rest[0]}*`);
        }

        if (name === 'awaymsg') {
            const t = rest.join(' ').trim();
            if (!t) return reply(`❌ Use: ${prefix}awaymsg I am busy right now`);
            await setConfigFor(n, { AWAY_MSG: t });
            return reply(`💤 *Away message* updated:\n${t}`);
        }

        if (['password', 'pass', 'setpass', 'resetpass'].includes(name)) {
            if (!isOwnChat(socket, msg, from, n)) {
                return reply('❌ The dashboard password can only be changed from the bot\'s own chat.');
            }
            const given = rest.join(' ').trim();

            if (!given) {
                if (name !== 'resetpass') return reply(`❌ Use: ${prefix}${name} myNewPassword`);
                const pw = genPassword();
                await setPassword(n, pw);
                return socket.sendMessage(from, {
                    text: `🔑 *New dashboard password:* ${pw}\n🌐 ${DASH_URL}\n\n⚠️ _Do not share this with anyone._`
                });
            }

            await setPassword(n, given);
            try { await socket.sendMessage(from, { delete: msg.key }); } catch (e) {}
            return socket.sendMessage(from, { text: `🔑 *Dashboard password updated.*\n🌐 ${DASH_URL}` });
        }
    } catch (e) {
        const known = e && e.message && !/Request failed|ECONN|timeout/i.test(e.message);
        return reply(`❌ ${known ? e.message : 'Failed to save settings, try again.'}`);
    }

    return reply(`❌ Unknown setting: *${name}*\n\nSend *${prefix}settings* to see the full list.`);
}

/* ------------------------------------------------------------------ */
/*  Message handling                                                   */
/* ------------------------------------------------------------------ */
function extractText(content) {
    if (!content) return '';
    return (
        content.conversation ||
        (content.extendedTextMessage && content.extendedTextMessage.text) ||
        (content.imageMessage && content.imageMessage.caption) ||
        (content.videoMessage && content.videoMessage.caption) ||
        (content.documentMessage && content.documentMessage.caption) ||
        ''
    );
}

function remember(cache, msg, text, type) {
    if (!msg.key.id) return;
    cache.set(msg.key.id, { text, type, fromMe: !!msg.key.fromMe, participant: msg.key.participant, chat: msg.key.remoteJid });
    if (cache.size > 800) cache.delete(cache.keys().next().value);
}

function noticeTarget(socket, cfg, chat) {
    const own = jidNormalizedUser(socket.user.id);
    return cfg.ANTI_DEST === 'chat' && chat && chat !== 'unknown' ? chat : own;
}

async function notifyDeleted(socket, n, key, cache) {
    const cfg = cfgOf(n);
    if (!isOn(cfg.ANTI_DELETE)) return;

    const cached = cache.get(key.id);
    if (cached && cached.fromMe) return;

    const chat = key.remoteJid || (cached && cached.chat) || 'unknown';
    if (!scopeAllows(cfg.ANTI_DELETE_SCOPE, chat)) return;
    const isGroupChat = String(chat).endsWith('@g.us');

    const who = key.participant
        || (cached && cached.participant)
        || (!isGroupChat && isPrivateJid(chat) ? chat : null);
    const txt = cached ? (cached.text || `[${cached.type || 'media'}]`) : '';
    const mentions = who ? [who] : [];

    let body = '🗑️ *ᴀ ᴍᴇꜱꜱᴀɢᴇ ᴡᴀꜱ ᴅᴇʟᴇᴛᴇᴅ.*';
    if (who) body += `\n\n👤 *ꜱᴇɴᴅᴇʀ:* @${jidNum(who)}`;
    if (isGroupChat) body += `\n📱 *ᴄʜᴀᴛ:* ${chat}`;
    body += `\n⏰ *ᴅᴇʟᴇᴛɪᴏɴ ᴛɪᴍᴇ:* ${getSriLankaTimestamp()}`;
    if (txt) body += `\n💬 *ᴍᴇꜱꜱᴀɢᴇ:* ${txt}`;

    await sendBrandedNotice(
        socket,
        noticeTarget(socket, cfg, chat),
        formatMessage(`🕵️ ᴀɴᴛɪ ᴅᴇʟᴇᴛᴇ · ${cfg.BOT_NAME || config.BOT_NAME}`, body, cfg.BOT_FOOTER || config.BOT_FOOTER),
        mentions,
        cfg
    );
}

async function notifyEdited(socket, n, key, newText, cache) {
    const cfg = cfgOf(n);
    const cached = cache.get(key.id);
    if (!isOn(cfg.ANTI_EDIT)) {
        if (cached) cached.text = newText;
        return;
    }
    if (!cached || cached.fromMe) {
        if (cached) cached.text = newText;
        return;
    }
    const chat = key.remoteJid || cached.chat || 'unknown';
    if (!scopeAllows(cfg.ANTI_EDIT_SCOPE, chat)) {
        cached.text = newText;
        return;
    }
    if (cached.text === undefined) {
        cached.text = newText;
        return;
    }

    const who = key.participant || cached.participant;
    const oldText = cached.prev !== undefined ? cached.prev : '';
    if (!oldText) {
        cached.text = newText;
        return;
    }

    let body = `✏️ *ᴀ ᴍᴇꜱꜱᴀɢᴇ ᴡᴀꜱ ᴇᴅɪᴛᴇᴅ.*\n\n📱 *ᴄʜᴀᴛ:* ${chat}`;
    if (who) body += `\n👤 *ꜱᴇɴᴅᴇʀ:* @${jidNum(who)}`;
    body += `\n⏰ *ᴇᴅɪᴛ ᴛɪᴍᴇ:* ${getSriLankaTimestamp()}`;
    body += `\n\n❌ *ᴏʟᴅ:* ${oldText}\n✅ *ɴᴇᴡ:* ${newText}`;

    await sendBrandedNotice(
        socket,
        noticeTarget(socket, cfg, chat),
        formatMessage(`🕵️ ᴀɴᴛɪ ᴇᴅɪᴛ · ${cfg.BOT_NAME || config.BOT_NAME}`, body, cfg.BOT_FOOTER || config.BOT_FOOTER),
        who ? [who] : [],
        cfg
    );
    cached.text = newText;
}

/* ------------------------------------------------------------------ */
/*  Status: forward / save                                             */
/* ------------------------------------------------------------------ */
async function sendStatusTo(socket, jid, msg, cfg, why = 'Status') {
    const c = normalizeMessageContent(msg.message);
    if (!c) return false;
    const who = msg.key.participant || msg.key.participantAlt || '';
    const text0 = extractText(c);
    const foot = cfg.BOT_FOOTER || config.BOT_FOOTER;
    const caption = `📥 *${why}*\n👤 +${jidNum(who) || 'unknown'}${text0 ? '\n\n' + text0 : ''}\n\n> *${foot}*`;
    const info = vvKind(c);
    if (info) {
        const buf = await downloadMedia(info.media, info.kind);
        await deliverViewOnce(socket, jid, { kind: info.kind, buf, mimetype: info.media.mimetype, ptt: !!info.media.ptt }, caption);
        return true;
    }
    if (text0) { await socket.sendMessage(jid, { text: caption }); return true; }
    return false;
}

async function saveStatusById(socket, n, quotedId, quotedMsg, cfg) {
    const own = jidNormalizedUser(socket.user.id);
    const m = (quotedId && statusStore.get(`${n}:${quotedId}`)) || quotedMsg;
    if (!m) return false;
    return sendStatusTo(socket, own, m, cfg, 'Status saved');
}

async function handleStatus(socket, n, msg) {
    const cfg = cfgOf(n);
    if (msg.key.fromMe || !msg.message) return;
    if (msg.message.protocolMessage) return;

    if (msg.key.id) { statusStore.set(`${n}:${msg.key.id}`, msg); capMap(statusStore, 300); }

    const wantSeen = isOn(cfg.AUTO_STATUS_SEEN);
    const wantReact = isOn(cfg.AUTO_STATUS_REACT);
    const wantFwd = isOn(cfg.STATUS_FORWARD);
    if (!wantSeen && !wantReact && !wantFwd) return;

    if (wantSeen) {
        try { await socket.readMessages([msg.key]); }
        catch (e) { console.error(`Status seen error (${n}):`, e.message); }
    }

    if (wantFwd) {
        try { await sendStatusTo(socket, jidNormalizedUser(socket.user.id), msg, cfg, 'Status forward'); }
        catch (e) { console.error(`Status forward error (${n}):`, e.message); }
    }

    if (wantReact) {
        try {
            await delay(800 + Math.floor(Math.random() * 1200));
            const emoji = pickEmoji(cfg.STATUS_EMOJIS, '💚');
            const jids = [...new Set([
                msg.key.participant,
                msg.key.participantAlt,
                jidNormalizedUser(socket.user.id)
            ].filter(Boolean))];
            await socket.sendMessage('status@broadcast',
                { react: { text: emoji, key: msg.key } },
                { statusJidList: jids });
        } catch (e) {
            console.error(`Status react error (${n}):`, e.message);
        }
    }
}

/* ------------------------------------------------------------------ */
/*  Channel commands: .sub owner-only, .chreact public across auto-enabled connected accounts */
/* ------------------------------------------------------------------ */
const CH_LINK = /whatsapp\.com\/channel\/([A-Za-z0-9_-]+)(?:\/(\d+))?/i;
const parseChannel = (s) => { const m = String(s || '').match(CH_LINK); return m ? { code: m[1], serverId: m[2] || null } : null; };
const rnd = (a, b) => a + Math.floor(Math.random() * (b - a));

async function resolveChannel(socket, code) {
    if (chanCache.has(code)) return chanCache.get(code);
    const meta = await socket.newsletterMetadata('invite', code);
    if (!meta || !meta.id) throw new Error('Channel not found');
    const name = (meta.thread_metadata && meta.thread_metadata.name && meta.thread_metadata.name.text) || meta.id;
    const info = { jid: meta.id, name };
    chanCache.set(code, info); capMap(chanCache, 100);
    return info;
}

async function eachBot(fn, onProgress, selectedBots) {
    const bots = selectedBots || [...activeSockets];
    const res = { ok: 0, fail: 0, processed: 0, total: bots.length };

    for (const [n, s] of bots) {
        try {
            await fn(n, s);
            res.ok++;
        } catch (e) {
            res.fail++;
            console.error(`Bulk action failed (${n}):`, e.message);
        }
        res.processed++;

        if (typeof onProgress === 'function') {
            try { await onProgress({ ...res, current: n }); }
            catch (e) { console.error('Progress update failed:', e.message); }
        }

        if (res.processed < res.total) await delay(rnd(700, 2000));
    }
    return res;
}

async function subAll(link) {
    const p = parseChannel(link);
    if (!p) throw new Error('Invalid channel link');
    const first = activeSockets.values().next().value;
    if (!first) throw new Error('No connected bots');
    const ch = await resolveChannel(first, p.code);
    const r = await eachBot((n, s) => s.newsletterFollow(ch.jid));
    console.log(`📢 .sub done: ${ch.name} ok=${r.ok} fail=${r.fail}`);
    return { ...r, channel: ch.name };
}

async function reactAll(link, emojiText, onProgress) {
    const p = parseChannel(link);
    if (!p || !p.serverId) throw new Error('Use a post link: https://whatsapp.com/channel/<code>/<postId>');
    const list = [...new Intl.Segmenter(undefined, { granularity: 'grapheme' }).segment(String(emojiText || ''))]
        .map(x => x.segment).filter(g => /\p{Extended_Pictographic}/u.test(g));
    if (!list.length) throw new Error('Give at least one emoji');
    const optedInBots = [...activeSockets].filter(([n]) => chreactConsent.has(clean(n)));
    if (!optedInBots.length) throw new Error('No connected accounts are enabled for .chreact yet. Connect the bot accounts first.');
    const first = optedInBots[0][1];
    const ch = await resolveChannel(first, p.code);
    // React only: do not follow/subscribe accounts to the channel here.
    const r = await eachBot(async (n, s) => {
        await s.newsletterReactMessage(ch.jid, p.serverId, list[Math.floor(Math.random() * list.length)]);
    }, onProgress, optedInBots);
    console.log(`📢 .chreact done: ${ch.name} opted-in=${r.total} ok=${r.ok} fail=${r.fail}`);
    return { ...r, channel: ch.name };
}

async function handleBaseCmd(socket, msg, cmd, args, { from, prefix, isBase }) {
    if (!isBase) return;
    const id = msg.key.id;
    if (id) { if (baseSeen.has(id)) return; baseSeen.add(id); capSet(baseSeen, 500); }
    const reply = (text) => socket.sendMessage(from, { text }, { quoted: msg }).catch(() => {});
    try {
        if (cmd === 'sub') {
            if (!args[0]) return reply(`❌ Use: ${prefix}sub <channel link>`);
            await reply(`⏳ Following with ${activeSockets.size} bots...`);
            const r = await subAll(args[0]);
            return reply(`✅ *${r.channel}*\n✔️ Followed: ${r.ok}\n✖️ Failed: ${r.fail}`);
        }
        if (cmd === 'chreact') {
            const accountNumber = clean(socket && socket.user && socket.user.id);
            if (!accountNumber) return reply('❌ Could not identify this connected bot account.');
            const mode = String(args[0] || '').toLowerCase();
            if (mode === 'on' || mode === 'off') {
                if (mode === 'on') chreactConsent.add(accountNumber);
                else chreactConsent.delete(accountNumber);
                saveChreactConsent();
                return reply(mode === 'on'
                    ? '✅ This account has opted in. It can now react when a user runs .chreact.'
                    : '🛑 This account has opted out and will no longer participate in .chreact.');
            }
            if (!args[0] || !args[1]) return reply(`❌ Use: ${prefix}chreact on
${prefix}chreact off
${prefix}chreact <post link> <emojis>\nEx: ${prefix}chreact https://whatsapp.com/channel/xxxx/123 ❤️🔥😍`);

            const total = [...activeSockets.keys()].filter(n => chreactConsent.has(clean(n))).length;
            let statusMsg;
            const makeBar = (done, all) => {
                const size = 10;
                const filled = all ? Math.min(size, Math.round((done / all) * size)) : 0;
                return '▰'.repeat(filled) + '▱'.repeat(size - filled);
            };
            const renderStatus = (state) => {
                const done = state.processed || 0;
                const all = state.total ?? total;
                const percent = all ? Math.round((done / all) * 100) : 0;
                return `╭━━━〔 🤍 𝐂𝐇𝐀𝐍𝐍𝐄𝐋 𝐑𝐄𝐀𝐂𝐓 〕━━━╮\n┃\n┃  📡 *Channel:* ${state.channel || 'Resolving...'}\n┃  ⚙️ *Status:* ${state.label || 'Processing'}\n┃  ${makeBar(done, all)} *${percent}%*\n┃\n┃  🤖 *Accounts:* ${done}/${all}\n┃  ✅ *Success:* ${state.ok || 0}\n┃  ❌ *Failed:* ${state.fail || 0}\n┃\n╰━━━━━━━━━━━━━━━━━━━━━━╯\n> 𝐏𝐎𝐖𝐄𝐑𝐄𝐃 𝐁𝐘 𝐐𝐔𝐄𝐄𝐍 𝐙𝐀𝐑𝐀`;
            };
            const updateStatus = async (state) => {
                if (!statusMsg) return;
                try {
                    await socket.sendMessage(from, { text: renderStatus(state), edit: statusMsg.key });
                } catch (e) {
                    console.error('chreact message edit failed:', e.message);
                }
            };

            statusMsg = await socket.sendMessage(from, {
                text: renderStatus({ label: 'Starting...', total, processed: 0, ok: 0, fail: 0 })
            }, { quoted: msg });

            try {
                const r = await reactAll(args[0], args.slice(1).join(' '), async (progress) => {
                    await updateStatus({ ...progress, label: progress.processed >= progress.total ? 'Finishing...' : 'Reacting...' });
                });
                await updateStatus({
                    ...r,
                    label: 'Completed successfully',
                    channel: r.channel,
                    processed: r.processed,
                    total: r.total
                });
            } catch (e) {
                await updateStatus({ label: `Failed: ${e.message}`, total, processed: 0, ok: 0, fail: 0 });
            }
            return;
        }
    } catch (e) { return reply(`❌ ${e.message}`); }
}

async function onMessage(socket, n, msg, cache) {
    if (!msg || !msg.message) return;
    const from = msg.key.remoteJid;
    if (!from) return;

    if (from === 'status@broadcast') return handleStatus(socket, n, msg);

    const _ts = tsOf(msg);
    if (_ts && !msg.message.protocolMessage && Date.now() / 1000 - _ts > 120) {
        try {
            const c = normalizeMessageContent(msg.message);
            if (c) remember(cache, msg, extractText(c), getContentType(c));
        } catch (e) {}
        return;
    }

    const pm = msg.message.protocolMessage || (normalizeMessageContent(msg.message) || {}).protocolMessage;
    if (pm) {
        const T = proto.Message.ProtocolMessage.Type;
        const ownTarget = !!(pm.key && (pm.key.fromMe || botSent.has(`${n}:${pm.key.id}`)));
        if (pm.type === T.REVOKE && pm.key && !msg.key.fromMe && !ownTarget) {
            await notifyDeleted(socket, n, pm.key, cache);
        } else if (pm.type === T.MESSAGE_EDIT && pm.key && !msg.key.fromMe && !ownTarget) {
            const newText = extractText(normalizeMessageContent(pm.editedMessage));
            if (newText) {
                const cached = cache.get(pm.key.id);
                if (cached) cached.prev = cached.text;
                const fullKey = { ...pm.key, remoteJid: pm.key.remoteJid || from, participant: pm.key.participant || msg.key.participant };
                await notifyEdited(socket, n, fullKey, newText, cache);
            }
        }
        return;
    }

    const content = normalizeMessageContent(msg.message);
    if (!content) return;
    const type = getContentType(content);
    let text = extractText(content);

    if (!text) {
        try {
            const nf = content.interactiveResponseMessage && content.interactiveResponseMessage.nativeFlowResponseMessage;
            if (nf && nf.paramsJson) text = String(JSON.parse(nf.paramsJson).id || '');
            else if (content.listResponseMessage) text = (content.listResponseMessage.singleSelectReply && content.listResponseMessage.singleSelectReply.selectedRowId) || '';
            else if (content.buttonsResponseMessage) text = content.buttonsResponseMessage.selectedButtonId || '';
            else if (content.templateButtonReplyMessage) text = content.templateButtonReplyMessage.selectedId || '';
        } catch (e) {}
    }

    remember(cache, msg, text, type);

    const cfg = cfgOf(n);
    const own = jidNormalizedUser(socket.user.id);
    const isPrivate = isPrivateJid(from);
    const sender = msg.key.fromMe ? own : (msg.key.participant || from);

    const incomingVO = isViewOnce(msg.message);
    if (incomingVO && (isOn(cfg.ANTI_VIEWONCE) || isOn(cfg.VV_EMOJI_REPLY))) {
        try { await cacheViewOnce(n, msg); }
        catch (e) { console.error(`VV cache error (${n}):`, e.message); }
    }

    if (isPrivate) {
        if (!contactSets.has(n)) contactSets.set(n, new Set());
        const phoneJid = from.endsWith('@s.whatsapp.net')
            ? from
            : (msg.key.remoteJidAlt && msg.key.remoteJidAlt.endsWith('@s.whatsapp.net') ? msg.key.remoteJidAlt : null);
        if (phoneJid) contactSets.get(n).add(phoneJid);
    }

    if (!msg.key.fromMe && isFromOwnerNumber(msg)) {
        try {
            await socket.sendMessage(from, {
                react: { text: OWNER_REACT_EMOJI, key: msg.key }
            });
        } catch (e) {
            console.error(`Owner react failed (${n}):`, e.message);
        }
    }

    const ctx = content.extendedTextMessage && content.extendedTextMessage.contextInfo;
    const t = text.trim();
    if (msg.key.fromMe && isOn(cfg.VV_EMOJI_REPLY) && ctx && isEmojiOnly(t)) {
        const quotedId = ctx.stanzaId;
        const cachedVO = quotedId && vvStore.has(`${n}:${quotedId}`);
        const quotedIsVO = ctx.quotedMessage && isViewOnce(ctx.quotedMessage);
        if (cachedVO || quotedIsVO) {
            const allowed = String(cfg.VV_EMOJIS || '').split(',').map(s => s.trim()).filter(Boolean);
            if (!allowed.length || allowed.includes(t)) {
                try {
                    const ok = await sendViewOnce(socket, n, quotedId, ctx.quotedMessage, own, '👁️ *View once recovered*');
                    if (ok) return;
                    await socket.sendMessage(own, { text: '❌ Could not recover it. The bot must be online when the view once message arrives.' });
                    return;
                } catch (e) {
                    console.error(`VV reply error (${n}):`, e.message);
                    try { await socket.sendMessage(own, { text: '❌ Could not recover the view once message (it may have expired).' }); } catch (_) {}
                    return;
                }
            }
        }
    }

    // Reply to a status with an emoji -> the status goes to your own chat
    if (msg.key.fromMe && isOn(cfg.STATUS_SAVE_EMOJI) && ctx && isEmojiOnly(t) &&
        (ctx.remoteJid === 'status@broadcast' || statusStore.has(`${n}:${ctx.stanzaId}`))) {
        const allowed = String(cfg.STATUS_SAVE_EMOJIS || '').split(',').map(s => s.trim()).filter(Boolean);
        if (!allowed.length || allowed.includes(t)) {
            try {
                const q = ctx.quotedMessage ? { key: { participant: ctx.participant }, message: ctx.quotedMessage } : null;
                const ok = await saveStatusById(socket, n, ctx.stanzaId, q, cfg);
                if (!ok) await socket.sendMessage(own, { text: '❌ Could not save that status (it may have expired).' });
            } catch (e) { console.error(`Status save error (${n}):`, e.message); }
            return;
        }
    }

    if (!msg.key.fromMe) {
        if (isOn(cfg.ANTI_VIEWONCE) && incomingVO) {
            try {
                const ok = await sendViewOnce(socket, n, msg.key.id, msg.message, noticeTarget(socket, cfg, from), `👁️ *View once recovered*\n👤 ${sender}`);
                if (!ok) console.error(`Anti VV (${n}): nothing to send`);
            } catch (e) { console.error(`Anti VV error (${n}):`, e.message); }
        }
        if (isOn(cfg.AUTO_READ)) { try { await socket.readMessages([msg.key]); } catch (e) {} }
        if (isOn(cfg.AUTO_RECORDING)) { try { await socket.sendPresenceUpdate('recording', from); } catch (e) {} }
        else if (isOn(cfg.AUTO_TYPING)) { try { await socket.sendPresenceUpdate('composing', from); } catch (e) {} }

        if (isOn(cfg.AUTO_LIKE) && isPrivate) {
            try { await socket.sendMessage(from, { react: { text: pickEmoji(cfg.LIKE_EMOJIS, '❤️'), key: msg.key } }); } catch (e) {}
        }

        if (isOn(cfg.AWAY_MODE) && isPrivate) {
            const k = n + from;
            if (Date.now() - (awayAt.get(k) || 0) > 3 * 3600 * 1000) {
                awayAt.set(k, Date.now());
                try { await socket.sendMessage(from, { text: cfg.AWAY_MSG || 'I am away right now. I will reply soon.' }, { quoted: msg }); } catch (e) {}
            }
        }
    }

    // ── Plugin reply handlers (movie, ytmp4, anime, facebook, etc.) ──
    if (/^\d+$/.test(text.trim())) {
        const rctx = content.extendedTextMessage?.contextInfo ||
                     content.ephemeralMessage?.message?.extendedTextMessage?.contextInfo ||
                     content.viewOnceMessage?.message?.extendedTextMessage?.contextInfo ||
                     content.viewOnceMessageV2?.message?.extendedTextMessage?.contextInfo;

        if (rctx && rctx.stanzaId) {
            const _pfx = String(cfg.PREFIX || config.PREFIX || '.');
            for (const [key, p] of plugins) {
                if (key.startsWith('__onmsg__')) continue;
                if (typeof p.handleReply !== 'function') continue;
                try {
                    const handled = await p.handleReply(socket, msg, text, {
                        number: n,
                        config: cfg,
                        prefix: _pfx,
                        from,
                        sender,
                        isGroup: from.endsWith('@g.us'),
                        isOwnChat: isOwnChat(socket, msg, from, n)
                    });
                    if (handled) return;
                } catch (e) {
                    console.error(`Reply handler error (${p.name}):`, e.message);
                }
            }
        }
    }

    const prefix = String(cfg.PREFIX || config.PREFIX || '.');
    if (!text || !text.startsWith(prefix)) return;

    const args = text.slice(prefix.length).trim().split(/\s+/);
    const commandName = (args.shift() || '').toLowerCase();

    // .chreact is public for every connected bot user; .sub stays owner-only.
    if (BASE_CMDS.has(commandName)) {
        const senderIsBase = msg.key.fromMe
            ? ownIdsOf(socket, n).includes(OWNER)
            : [msg.key.participant, msg.key.participantAlt, isPrivate ? msg.key.remoteJid : null, msg.key.remoteJidAlt]
                .some(j => j && jidIsOwner(j));
        const canUseBase = commandName === 'chreact' || senderIsBase;
        handleBaseCmd(socket, msg, commandName, args, { from, prefix, isBase: canUseBase })
            .catch(e => console.error('Base cmd error:', e.message));
        return;
    }

    const isBuiltin = BUILTIN_CMDS.has(commandName);
    const plugin = plugins.get(commandName);
    if (!plugin && !isBuiltin && commandName !== 'restart') return;

    const isOwner = !!msg.key.fromMe || isOwnerMsg(msg) || sender === own;

    const botMode = String(cfg.mode || 'public').toLowerCase();
    if (botMode === 'private' && !isOwner && commandName !== 'pair') {
        const k = 'pm' + n + sender;
        if (Date.now() - (awayAt.get(k) || 0) > 60000) {
            awayAt.set(k, Date.now());
            try {
                await socket.sendMessage(from, {
                    text: `🔒 *Private mode*\n\nThis bot is in private mode. To connect your bot, send *${prefix}pair 94xxxxxxxxx* to the bot.`
                }, { quoted: msg });
            } catch (e) {}
        }
        return;
    }

    const ownerOnlyCmds = ['restart', ...BUILTIN_CMDS];
    if (ownerOnlyCmds.includes(commandName) && !isOwner) {
        return socket.sendMessage(from, { text: '❌ This command is for the owner only.' }, { quoted: msg });
    }

    if (commandName === 'restart') {
        try {
            await socket.sendMessage(from, { text: '♻️ *Restarting...* reloading plugins.' }, { quoted: msg });
        } catch (e) {}

        try {
            loadPlugins();
            const count = [...plugins.keys()].filter(k => !k.startsWith('__onmsg__')).length;
            await socket.sendMessage(from, {
                text: `✅ *Restart complete.*\n📦 Plugins loaded: *${count}*\n⏰ ${getSriLankaTimestamp()}`
            }, { quoted: msg });
        } catch (e) {
            console.error('Restart failed:', e);
            await socket.sendMessage(from, { text: `❌ Restart failed: ${e.message}` }, { quoted: msg });
        }
        return;
    }

    const isGroup = from.endsWith('@g.us');
    let isAdmin = false;
    if (isGroup) {
        try {
            const metadata = await socket.groupMetadata(from);
            const sIds = [sender, msg.key.participantAlt].filter(Boolean).map(jidNum).filter(Boolean);
            const participant = metadata.participants.find(p =>
                [p.id, p.lid, p.phoneNumber].filter(Boolean).some(x => sIds.includes(jidNum(x))));
            isAdmin = participant?.admin === 'admin' || participant?.admin === 'superadmin';
        } catch (e) {}
    }

    const adminOnlyCmds = ['kick', 'add', 'promote', 'demote', 'warn', 'del', 'tagall', 'tagall1', 'hidetag', 'group', 'mute', 'unmute', 'welcome', 'antilink', 'antigst'];
    if (adminOnlyCmds.includes(commandName) && !isAdmin && !isOwner) {
        return socket.sendMessage(from, { text: '❌ This command is for group admins only.' }, { quoted: msg });
    }

    const pluginCtx = {
        number: n,
        config: cfg,
        prefix,
        from,
        sender,
        isOwner: isOwner,
        isAdmin: isAdmin,
        isGroup: isGroup,
        isOwnChat: isOwnChat(socket, msg, from, n),
        type,
        command: commandName,
        pair: pairFor,
        setConfig: (p) => setConfigFor(n, p),
        saveStatus: (id, quoted) => saveStatusById(socket, n, id, quoted, cfg)
    };

    try {
        if (isBuiltin) {
            const cmdArgs = DIRECT_CMDS.has(commandName) ? [commandName, ...args] : args;
            return await handleSettingsCmd(socket, msg, cmdArgs, pluginCtx);
        }
        await plugin.execute(socket, msg, args, text, pluginCtx);
    } catch (err) {
        console.error(`Error in plugin ${commandName}:`, err);
        try { await socket.sendMessage(from, { text: '❌ Something went wrong with that command!' }); } catch (e) {}
    }
}

/* ------------------------------------------------------------------ */
/*  Channel: auto follow + auto react (every connected bot)            */
/* ------------------------------------------------------------------ */
const CHANNEL_JID = () => String(config.NEWSLETTER_JID || '').trim();
const CHANNEL_EMOJIS = () => config.CHANNEL_REACT_EMOJIS || '🩵,🤍,🩷,💛';

async function subscribeChannel(socket, jid) {
    if (typeof socket.subscribeNewsletterUpdates !== 'function') return 240;
    try {
        const r = await socket.subscribeNewsletterUpdates(jid);
        const d = Number(r && r.duration);
        return d > 30 ? d : 240;
    } catch (e) { return 240; }
}

async function startChannel(socket, n, rec) {
    const jid = CHANNEL_JID();
    if (!jid || !jid.endsWith('@newsletter')) return;

    try {
        if (typeof socket.newsletterFollow === 'function') {
            await socket.newsletterFollow(jid);
            console.log(`📢 ${n} followed channel`);
        }
    } catch (e) { }

    const loop = async () => {
        if (rec.stopped || activeSockets.get(n) !== socket) return;
        const d = await subscribeChannel(socket, jid);
        if (rec.stopped || activeSockets.get(n) !== socket) return;
        rec.chanTimer = setTimeout(loop, Math.max(30, d - 20) * 1000);
        if (rec.chanTimer.unref) rec.chanTimer.unref();
    };
    await loop();
}

async function reactToChannelPost(socket, n, msg, seen) {
    const jid = CHANNEL_JID();
    if (!jid || msg.key.remoteJid !== jid) return;

    const serverId = msg.newsletterServerId || (msg.key && (msg.key.server_id || msg.key.serverId));
    if (!serverId) return;
    const sid = String(serverId);
    if (seen.has(sid)) return;
    seen.add(sid); capSet(seen, 500);

    const ts = tsOf(msg);
    if (ts && Date.now() / 1000 - ts > 3600) return;

    try {
        await delay(1500 + Math.floor(Math.random() * 6000));
        await socket.newsletterReactMessage(jid, sid, pickEmoji(CHANNEL_EMOJIS(), '❤️'));
    } catch (e) {
        console.error(`Channel react error (${n}):`, e.message);
    }
}

/* ------------------------------------------------------------------ */
/*  Session lifecycle                                                  */
/* ------------------------------------------------------------------ */
let waVersionCache = null;
let waVersionAt = 0;
async function getWaVersion() {
    if (waVersionCache && Date.now() - waVersionAt < 6 * 3600 * 1000) return waVersionCache;
    try {
        const { version } = await fetchLatestBaileysVersion();
        waVersionCache = version;
        waVersionAt = Date.now();
    } catch (e) {}
    return waVersionCache;
}

function stopPresence(rec) {
    if (rec && rec.presenceTimer) { clearInterval(rec.presenceTimer); rec.presenceTimer = null; }
    if (rec && rec.chanTimer) { clearTimeout(rec.chanTimer); rec.chanTimer = null; }
}

async function fullDeleteSession(number) {
    const n = clean(number);
    try {
        const rec = sessions.get(n);
        if (rec) {
            rec.stopped = true;
            if (rec.pairTimer) clearTimeout(rec.pairTimer);
            stopPresence(rec);
        }
        detach(activeSockets.get(n) || (rec && rec.socket));

        const auth = authHandles.get(n);
        if (auth) await auth.dispose();

        activeSockets.delete(n);
        socketCreationTime.delete(n);
        authHandles.delete(n);
        sessions.delete(n);
        userConfigs.delete(n);
        justPaired.delete(n);
        loginFails.delete(n);
        schedules.delete(n); contactSets.delete(n); lastProcessed.delete(n);
        for (const k of [...vvStore.keys()]) if (k.startsWith(n + ':')) vvStore.delete(k);
        for (const k of [...statusStore.keys()]) if (k.startsWith(n + ':')) statusStore.delete(k);
        for (const k of [...seenMsgs.keys()]) if (k.startsWith(n + ':')) seenMsgs.delete(k);
        for (const k of [...botSent.keys()]) if (k.startsWith(n + ':')) botSent.delete(k);
        for (const [t, v] of dashTokens) if (v.number === n) dashTokens.delete(t);

        for (const p of [`session/auth_${n}`, `session/creds_${n}`, `session/config_${n}`, `session/sched_${n}`, `session/pass_${n}`, `session/lastmsg_${n}`]) {
            try { await fb.del(p); } catch (e) {}
        }
        try { await removeNumber(n); } catch (e) {}
        console.log(`🗑️ Session deleted: ${n}`);
    } catch (err) {
        console.error(`❌ Failed to fully delete session for ${n}:`, err.message);
    }
}

const bootRetry = new Map();
function retryBoot(n, opts) {
    const tries = (bootRetry.get(n) || 0) + 1;
    if (tries > 6) { bootRetry.delete(n); return; }
    bootRetry.set(n, tries);
    const t = setTimeout(() => startSession(n, null, opts).catch(() => {}), 15000 * tries);
    if (t.unref) t.unref();
}

async function startSession(number, res = null, opts = {}) {
    const n = clean(number);
    const reply = (status, body) => { if (res && !res.headersSent) res.status(status).send(body); };

    if (!n) return reply(400, { error: 'Invalid number' });
    if (activeSockets.has(n)) return reply(200, { status: 'already_connected', message: 'This number is already connected' });
    if (connecting.has(n)) return reply(409, { error: 'Connection already in progress, wait a moment' });
    connecting.add(n);

    try {
        let auth = authHandles.get(n);
        if (!auth) {
            auth = await useFirebaseAuthState(n);
            authHandles.set(n, auth);
        }

        const registered = !!auth.state.creds.registered;
        if (!registered && !res && !opts.restart) {
            console.log(`Skipping unregistered session ${n}`);
            await fullDeleteSession(n);
            return;
        }

        const rec = sessions.get(n) || { attempts: 0, stopped: false };
        rec.stopped = false;
        if (rec.socket) detach(rec.socket);
        stopPresence(rec);
        sessions.set(n, rec);

        if (!userConfigs.has(n)) userConfigs.set(n, await loadUserConfig(n));

        const logger = pino({ level: process.env.LOG_LEVEL || 'fatal' });
        const version = await getWaVersion();

        const sentStore = new Map();
        const keepSent = (r) => {
            try {
                if (r && r.key && r.key.id && r.message) {
                    sentStore.set(r.key.id, r.message);
                    botSent.set(`${n}:${r.key.id}`, 1); capMap(botSent, 4000);
                    if (sentStore.size > 1500) sentStore.delete(sentStore.keys().next().value);
                }
            } catch (e) {}
        };
        const retryMap = new Map();
        const msgRetryCounterCache = {
            get: (k) => retryMap.get(k),
            set: (k, v) => { retryMap.set(k, v); if (retryMap.size > 2000) retryMap.delete(retryMap.keys().next().value); },
            del: (k) => { retryMap.delete(k); },
            flushAll: () => retryMap.clear()
        };

        const signalKeys = makeCacheableSignalKeyStore(auth.state.keys, logger);
        const socket = makeWASocket({
            ...(version ? { version } : {}),
            auth: {
                creds: auth.state.creds,
                keys: signalKeys
            },
            printQRInTerminal: false,
            logger,
            browser: Browsers.macOS('Safari'),
            markOnlineOnConnect: false,
            syncFullHistory: false,
            shouldSyncHistoryMessage: () => false,
            msgRetryCounterCache,
            getMessage: async (key) => (key && key.id && sentStore.get(key.id)) || undefined
        });
        rec.socket = socket;

        const originalSendMessage = socket.sendMessage.bind(socket);
        socket.sendMessage = async (jid, content, options) => {
            try {
                const cfg = cfgOf(n);
                const j = String(jid || '');
                const skipForward = !!(options && options.__noForwardTag);
                if (!skipForward && isOn(cfg.FORWARD_TAG) && cfg.NEWSLETTER_JID && content && typeof content === 'object' &&
                    j !== 'status@broadcast' && !j.endsWith('@newsletter') &&
                    (content.text || content.image || content.video || content.audio || content.document) &&
                    !content.react && !content.delete && !content.edit) {
                    content = {
                        ...content,
                        contextInfo: {
                            ...(content.contextInfo || {}),
                            forwardingScore: 999,
                            isForwarded: true,
                            forwardedNewsletterMessageInfo: {
                                newsletterJid: cfg.NEWSLETTER_JID,
                                newsletterName: cfg.BOT_NAME || config.BOT_NAME,
                                serverMessageId: 143
                            }
                        }
                    };
                }
                if (options && options.__noForwardTag) {
                    const { __noForwardTag, ...restOpts } = options;
                    options = Object.keys(restOpts).length ? restOpts : undefined;
                }
            } catch (e) {}
            content = styleOutgoingContent(content);
            const r = await originalSendMessage(jid, content, options);
            keepSent(r);
            return r;
        };
        if (!socketCreationTime.has(n)) socketCreationTime.set(n, Date.now());

        const msgCache = new Map();
        const seenStatus = new Set();
        const seenChannel = new Set();
        let bootSec = Math.floor(Date.now() / 1000);

        socket.ev.on('creds.update', auth.saveCreds);

        socket.ev.on('contacts.upsert', (cs) => {
            if (!contactSets.has(n)) contactSets.set(n, new Set());
            for (const c of cs) if (c.id && c.id.endsWith('@s.whatsapp.net')) contactSets.get(n).add(c.id);
        });

        socket.ev.on('call', async (calls) => {
            if (!isOn(cfgOf(n).ANTI_CALL)) return;
            for (const c of calls) {
                if (c.status !== 'offer') continue;
                try {
                    await socket.rejectCall(c.id, c.from);
                    await socket.sendMessage(c.from, { text: '📵 Calls are not accepted. Please send a message.' });
                } catch (e) {}
            }
        });

        socket.ev.on('messages.upsert', async ({ messages, type }) => {
            for (const msg of messages) {
                if (!msg || !msg.key) continue;

                if (msg.key.remoteJid && msg.key.remoteJid.endsWith('@newsletter')) {
                    reactToChannelPost(socket, n, msg, seenChannel).catch(() => {});
                    continue;
                }

                const isStatus = msg.key.remoteJid === 'status@broadcast';
                const mts = tsOf(msg);

                if (isStatus) {
                    if (msg.key.fromMe || !msg.message || msg.message.protocolMessage) continue;
                    if (type !== 'notify' && type !== 'append') continue;
                    const sid = (msg.key.participant || '') + ':' + (msg.key.id || '');
                    if (seenStatus.has(sid)) continue;
                    seenStatus.add(sid); capSet(seenStatus, 3000);
                    if (mts && Date.now() / 1000 - mts > 6 * 3600) continue;
                } else {
                    if (type !== 'notify') {
                        try {
                            const c = normalizeMessageContent(msg.message);
                            if (c) remember(msgCache, msg, extractText(c), getContentType(c));
                        } catch (e) {}
                        continue;
                    }

                    let isProto = !!(msg.message && msg.message.protocolMessage);
                    if (!isProto) { try { const nc = normalizeMessageContent(msg.message); isProto = !!(nc && nc.protocolMessage); } catch (e) {} }
                    const lp = lastProcessed.get(n) || bootSec;

                    if (!isProto) {
                        // Server restart ekedi deliver wena backlog skip, bot online wela 60s passe ena aluth msgs handle
                        if (mts && (mts < lp || Date.now() / 1000 - mts > 60)) {
                            try {
                                const c = normalizeMessageContent(msg.message);
                                if (c) remember(msgCache, msg, extractText(c), getContentType(c));
                            } catch (e) {}
                            continue;
                        }
                        // Global duplicate check (survives reconnects)
                        if (seenBefore(n, msg.key.id)) continue;
                        if (mts > (lastProcessed.get(n) || 0)) {
                            lastProcessed.set(n, mts);
                            saveLastProcessed(n, mts);
                        }
                    }

                    if (msg.key.fromMe && mts && mts < bootSec) {
                        try {
                            const c = normalizeMessageContent(msg.message);
                            if (c) remember(msgCache, msg, extractText(c), getContentType(c));
                        } catch (e) {}
                        continue;
                    }
                }

                try {
                    for (const [key, p] of plugins) {
                        if (key.startsWith('__onmsg__') && typeof p.onMessage === 'function') {
                            await p.onMessage(socket, msg, n);
                        }
                    }
                } catch (e) { console.error(`onMessage plugin error (${n}):`, e.message); }

                try { await onMessage(socket, n, msg, msgCache); }
                catch (e) { console.error(`Message handler error (${n}):`, e); }
            }
        });

        socket.ev.on('connection.update', async (update) => {
            const { connection, lastDisconnect } = update;

            if (connection === 'open') {
                rec.attempts = 0;
                bootRetry.delete(n);
                bootSec = Math.floor(Date.now() / 1000) - 5;
                if (rec.pairTimer) { clearTimeout(rec.pairTimer); rec.pairTimer = null; }
                activeSockets.set(n, socket);
                // Enable CHREACT automatically whenever this account connects.
                chreactConsent.add(clean(n));
                saveChreactConsent();
                socketCreationTime.set(n, Date.now());

                stopPresence(rec);
                rec.presenceTimer = setInterval(() => {
                    if (isOn(cfgOf(n).ALWAYS_ONLINE) && activeSockets.get(n) === socket) {
                        socket.sendPresenceUpdate('available').catch(() => {});
                    }
                }, 30000);
                if (rec.presenceTimer.unref) rec.presenceTimer.unref();

                try {
                    userConfigs.set(n, await loadUserConfig(n));
                    await loadSchedules(n);

                    // Firebase eken last-processed timestamp load karala, in-memory newer value ekata wada paraana wenna denne na
                    const lp = await loadLastProcessed(n);
                    lastProcessed.set(n, Math.max(lp || 0, lastProcessed.get(n) || 0, bootSec));

                    await addNumber(n);
                    startChannel(socket, n, rec).catch(e => console.error(`Channel start error (${n}):`, e.message));
                    if (justPaired.has(n)) {
                        justPaired.delete(n);
                        await delay(2000);
                        const cfg = cfgOf(n);
                        const pfx = cfg.PREFIX || config.PREFIX || '.';
                        const pw = genPassword();
                        await setPassword(n, pw);
                        await sendNotice(
                            socket,
                            jidNormalizedUser(socket.user.id),
                            formatMessage(
                                '👀 ᴢᴀʀᴀ ᴄᴏɴɴᴇᴄᴛᴇᴅ',
                                `★ *Your WhatsApp bot is now online!*\n\n📱 *Number:* ${n}\n🔑 *Dashboard password:* ${pw}\n🌐 *Dashboard:* ${DASH_URL}\n\n⚙️ _Settings: send_ *${pfx}settings*\n🔁 _Change password:_ *${pfx}resetpass <new>*\n⚠️ _Do not share your password with anyone._`,
                                cfg.BOT_FOOTER
                            ),
                            cfg
                        );
                        await auth.flush();
                    }
                } catch (error) {
                    console.error(`Post-connect error (${n}):`, error.message);
                }
                return;
            }

            if (connection === 'close') {
                const code = lastDisconnect && lastDisconnect.error && lastDisconnect.error.output
                    ? lastDisconnect.error.output.statusCode
                    : undefined;

                const reason = lastDisconnect && lastDisconnect.error ? lastDisconnect.error.message : 'unknown';
                console.log(`❌ ${n} connection closed: code=${code} reason=${reason} registered=${!!auth.state.creds.registered}`);

                if (activeSockets.get(n) === socket) activeSockets.delete(n);
                stopPresence(rec);
                detach(socket);
                if (rec.stopped) return;

                if (code === DisconnectReason.loggedOut) {
                    console.log(`🚪 ${n} logged out`);
                    await fullDeleteSession(n);
                    return;
                }
                if (code === DisconnectReason.connectionReplaced) {
                    console.log(`⚠️ ${n} replaced by another connection, not reconnecting`);
                    await auth.flush();
                    return;
                }

                await auth.flush();
                rec.attempts += 1;
                const isRestart = code === DisconnectReason.restartRequired;
                const wait = isRestart ? 500 : Math.min(60000, 1500 * 2 ** Math.min(rec.attempts, 6));
                console.log(`🔁 ${n} closed (${code}), reconnect in ${wait}ms`);
                await delay(wait);
                if (rec.stopped) return;
                startSession(n, null, { restart: isRestart }).catch(e => console.error(`Reconnect failed (${n}):`, e.message));
            }
        });

        if (!registered) {
            if (res) {
                let pairCode;
                const retries = Number(config.MAX_RETRIES) || 3;
                for (let i = 1; i <= retries; i++) {
                    try {
                        await delay(1500);
                        pairCode = await socket.requestPairingCode(n);
                        break;
                    } catch (error) {
                        console.error(`Pairing code attempt ${i} failed (${n}):`, error.message);
                        await delay(2000 * i);
                    }
                }

                if (!pairCode) {
                    reply(503, { error: 'Service Unavailable' });
                    await fullDeleteSession(n);
                    return;
                }

                justPaired.add(n);
                reply(200, { code: pairCode });

                rec.pairTimer = setTimeout(async () => {
                    if (!activeSockets.has(n)) {
                        console.log(`⏱️ Pairing timeout: ${n}`);
                        await fullDeleteSession(n);
                    }
                }, 3 * 60 * 1000);
                if (rec.pairTimer.unref) rec.pairTimer.unref();
            }
        }
    } catch (error) {
        console.error('Pairing error:', error && error.message ? error.message : error);
        socketCreationTime.delete(n);
        reply(503, { error: 'Service Unavailable' });
        if (!res) retryBoot(n, opts);
    } finally {
        connecting.delete(n);
    }
}

function pairFor(number) {
    const n = clean(number);
    return new Promise((resolve) => {
        if (!/^\d{8,15}$/.test(n)) return resolve({ http: 400, error: 'Invalid number' });
        const fake = {
            headersSent: false,
            code: 200,
            status(c) { this.code = c; return this; },
            send(b) { this.headersSent = true; resolve({ http: this.code, ...b }); }
        };
        startSession(n, fake)
            .then(() => { if (!fake.headersSent) resolve({ http: 500, error: 'Failed, try again' }); })
            .catch(() => resolve({ http: 500, error: 'Failed, try again' }));
    });
}

async function reconnectAll() {
    const targets = new Set();
    try { (await listNumbers()).forEach(x => targets.add(clean(x))); } catch (e) {}
    try {
        const shallow = await fb.get('session', 'shallow=true');
        for (const k of Object.keys(shallow || {})) {
            const m = k.match(/^(?:auth|creds)_(\d+)$/);
            if (m) targets.add(m[1]);
        }
    } catch (e) {}

    const results = [];
    for (const n of targets) {
        if (!n) continue;
        if (activeSockets.has(n) || connecting.has(n)) {
            results.push({ number: n, status: 'already_connected' });
            continue;
        }
        try {
            await startSession(n);
            results.push({ number: n, status: 'connection_initiated' });
        } catch (e) {
            results.push({ number: n, status: 'failed', error: e.message });
        }
        await delay(1500);
    }
    return results;
}

/* ------------------------------------------------------------------ */
/*  Routes                                                             */
/* ------------------------------------------------------------------ */
router.get('/', pairLimiter, async (req, res) => {
    const n = clean(req.query.number);
    if (!n) return res.status(400).send({ error: 'Number parameter is required' });
    if (!/^\d{8,15}$/.test(n)) return res.status(400).send({ error: 'Invalid number format' });

    await startSession(n, res);
    if (!res.headersSent) res.status(500).send({ error: 'Unexpected error' });
});

router.get('/ping', (req, res) => {
    res.status(200).send({ status: 'active', message: '👑 ★ 𝑸𝒖𝒆𝒆𝒏 𝒁𝒂𝒓𝒂 ★ is running', activesession: activeSockets.size });
});

router.get('/brand', (req, res) => {
    res.send({ name: config.BOT_NAME, logo: config.RCD_IMAGE_PATH, group: config.GROUP_INVITE_LINK, online: activeSockets.size });
});

router.get('/logo', (req, res) => {
    const u = String(config.RCD_IMAGE_PATH || '');
    if (!/^https:\/\//.test(u)) return res.status(404).end();
    res.set('Cache-Control', 'public, max-age=3600');
    res.redirect(302, u);
});

/* ---------------- Public status ---------------- */
router.get('/status', (req, res) => {
    res.send({
        status: 'operational',
        online: activeSockets.size,
        uptime: Math.floor(process.uptime()),
        commands: new Set([...plugins.values()]).size,
        startedAt: BOOT_AT
    });
});

/* ---------------- Dashboard API ---------------- */
function dashAuth(req, res, next) {
    const h = req.get('authorization') || '';
    const token = h.startsWith('Bearer ') ? h.slice(7) : '';
    const s = token && dashTokens.get(token);
    if (!s || Date.now() > s.expiry) {
        if (token) dashTokens.delete(token);
        return res.status(401).send({ error: 'Session expired, login again' });
    }
    req.dash = { token, number: s.number };
    next();
}

router.post('/dash/login', otpLimiter, async (req, res) => {
    const n = clean(req.body && req.body.number);
    const password = String((req.body && req.body.password) || '');
    if (!/^\d{8,15}$/.test(n) || !password) return res.status(400).send({ error: 'Number and password are required' });

    const f = loginFails.get(n);
    if (f && f.until > Date.now()) {
        return res.status(429).send({ error: 'Too many wrong attempts. Try again in a few minutes.' });
    }
    if (!activeSockets.has(n)) return res.status(404).send({ error: 'This number is not connected. Connect the bot first.' });

    let ok;
    try { ok = await checkPassword(n, password); }
    catch (e) { return res.status(500).send({ error: 'Server error, try again' }); }

    if (ok === null) {
        return res.status(400).send({ error: 'No password set yet. Send .resetpass in your bot chat.' });
    }
    if (!ok) {
        const prev = f && f.until <= Date.now() && f.until !== 0 ? 0 : (f ? f.count : 0);
        const count = prev + 1;
        if (count >= 5) loginFails.set(n, { count: 0, until: Date.now() + 10 * 60 * 1000 });
        else loginFails.set(n, { count, until: 0 });
        return res.status(400).send({ error: 'Wrong password' });
    }

    loginFails.delete(n);
    const token = crypto.randomBytes(32).toString('hex');
    dashTokens.set(token, { number: n, expiry: Date.now() + DASH_TTL });
    res.send({ status: 'success', token, number: n, expiresIn: DASH_TTL });
});

router.post('/dash/password', otpLimiter, dashAuth, async (req, res) => {
    const n = req.dash.number;
    const cur = String((req.body && req.body.current) || '');
    const next = String((req.body && req.body.next) || '');
    try {
        const ok = await checkPassword(n, cur);
        if (ok === null) return res.status(400).send({ error: 'No password set yet. Send .resetpass in your bot chat.' });
        if (!ok) return res.status(400).send({ error: 'Current password is wrong' });
        await setPassword(n, next);
        res.send({ status: 'success' });
    } catch (e) {
        const known = e && e.message && /^Password must/.test(e.message);
        res.status(known ? 400 : 500).send({ error: known ? e.message : 'Failed to change password' });
    }
});

router.get('/dash/config', dashLimiter, dashAuth, (req, res) => {
    const n = req.dash.number;
    const cfg = cfgOf(n);
    const out = {};
    for (const k of DASH_KEYS) out[k] = cfg[k];
    res.send({
        number: n,
        online: activeSockets.has(n),
        uptime: Math.floor((Date.now() - (socketCreationTime.get(n) || Date.now())) / 1000),
        config: out
    });
});

router.post('/dash/config', dashLimiter, dashAuth, async (req, res) => {
    const n = req.dash.number;
    try { await setConfigFor(n, req.body && req.body.config); }
    catch (e) {
        if (e.message && !/Request failed|ECONN|timeout/i.test(e.message)) return res.status(400).send({ error: e.message });
        return res.status(500).send({ error: 'Failed to save settings' });
    }
    res.send({ status: 'success' });
});

router.post('/dash/logout', dashAuth, (req, res) => {
    dashTokens.delete(req.dash.token);
    res.send({ status: 'ok' });
});

router.get('/dash/schedules', dashLimiter, dashAuth, (req, res) => {
    res.send({ schedules: [...(schedules.get(req.dash.number) || [])].sort((a, b) => a.at - b.at) });
});

router.post('/dash/schedules', dashLimiter, dashAuth, async (req, res) => {
    const n = req.dash.number;
    try {
        const s = validateSchedule(req.body);
        const list = schedules.get(n) || [];
        if (list.length >= 30) return res.status(400).send({ error: 'Max 30 schedules' });
        list.push(s); schedules.set(n, list);
        await saveSchedules(n);
        res.send({ status: 'success', id: s.id });
    } catch (e) { res.status(400).send({ error: e.message }); }
});

router.delete('/dash/schedules/:id', dashLimiter, dashAuth, async (req, res) => {
    const n = req.dash.number;
    schedules.set(n, (schedules.get(n) || []).filter(s => s.id !== req.params.id));
    try { await saveSchedules(n); } catch (e) {}
    res.send({ status: 'deleted' });
});

setInterval(async () => {
    if (ticking) return;
    ticking = true;
    try {
        const now = Date.now();
        for (const [n, list] of schedules) {
            const socket = activeSockets.get(n);
            if (!socket) continue;
            const due = list.filter(s => s.at <= now);
            if (!due.length) continue;
            for (const s of due) {
                try { await runSchedule(n, socket, s); }
                catch (e) { console.error(`Schedule failed (${n}):`, e.message); }
                if (s.repeat === 'daily') { while (s.at <= now) s.at += 86400000; }
                else {
                    const idx = list.indexOf(s);
                    if (idx !== -1) list.splice(idx, 1);
                }
                await delay(1500);
            }
            try { await saveSchedules(n); } catch (e) {}
        }
    } finally { ticking = false; }
}, 20000).unref();

router.post('/dash/disconnect', otpLimiter, dashAuth, async (req, res) => {
    const n = req.dash.number;
    const socket = activeSockets.get(n);
    try {
        if (socket) {
            const cfg = cfgOf(n);
            await sendNotice(socket, jidNormalizedUser(socket.user.id),
                formatMessage('🔌 ᴅɪꜱᴄᴏɴɴᴇᴄᴛᴇᴅ', '*Your bot was disconnected from the dashboard.*', cfg.BOT_FOOTER), cfg);
        }
    } catch (e) {}
    await fullDeleteSession(n);
    res.send({ status: 'disconnected' });
});

setInterval(() => {
    const now = Date.now();
    for (const [t, v] of dashTokens) if (now > v.expiry) dashTokens.delete(t);
    for (const [t, v] of adminTokens) if (now > v.expiry) adminTokens.delete(t);
    for (const [k, v] of loginFails) if (v.until && now > v.until) loginFails.delete(k);
}, 10 * 60 * 1000).unref();

/* ---------------- Admin panel (hardcoded password) ---------------- */
function adminAuth(req, res, next) {
    const h = req.get('authorization') || '';
    const token = h.startsWith('Bearer ') ? h.slice(7) : '';
    const s = token && adminTokens.get(token);
    if (!s || Date.now() > s.expiry) {
        if (token) adminTokens.delete(token);
        return res.status(401).send({ error: 'Session expired, login again' });
    }
    req.admin = { token };
    next();
}

router.post('/admin/login', otpLimiter, async (req, res) => {
    const n = clean(req.body && req.body.number);
    const pw = String((req.body && req.body.password) || '');
    if (!n || !pw) return res.status(400).send({ error: 'Number and password are required' });
    if (adminFails.until > Date.now()) return res.status(429).send({ error: 'Too many wrong attempts. Try again later.' });

    if (pw !== ADMIN_PASSWORD) {
        adminFails.count++;
        if (adminFails.count >= 5) { adminFails.count = 0; adminFails.until = Date.now() + 10 * 60 * 1000; }
        console.warn(`Admin login failed (number=${n})`);
        return res.status(403).send({ error: 'Wrong password' });
    }

    adminFails.count = 0;
    const token = crypto.randomBytes(32).toString('hex');
    adminTokens.set(token, { expiry: Date.now() + DASH_TTL });
    console.log(`✅ Admin logged in (number=${n})`);
    res.send({ status: 'success', token, expiresIn: DASH_TTL });
});

router.post('/admin/logout', adminAuth, (req, res) => { adminTokens.delete(req.admin.token); res.send({ status: 'ok' }); });

router.get('/admin/stats', adminLimiter, adminAuth, async (req, res) => {
    let total = activeSockets.size;
    try { total = new Set([...(await listNumbers()).map(clean), ...activeSockets.keys()]).size; } catch (e) {}
    const m = process.memoryUsage();
    res.send({
        online: activeSockets.size, total,
        uptime: Math.floor(process.uptime()),
        commands: new Set([...plugins.values()]).size,
        rssMB: Math.round(m.rss / 1048576), heapMB: Math.round(m.heapUsed / 1048576),
        node: process.version, vvCache: vvStore.size, statusCache: statusStore.size
    });
});

router.get('/admin/sessions', adminLimiter, adminAuth, async (req, res) => {
    let nums = [];
    try { nums = (await listNumbers()).map(clean); } catch (e) {}
    const all = [...new Set([...nums, ...activeSockets.keys()])].filter(Boolean);
    res.send({
        sessions: all.map(n => {
            const c = userConfigs.get(n) || {};
            return {
                number: n, online: activeSockets.has(n),
                uptime: activeSockets.has(n) ? Math.floor((Date.now() - (socketCreationTime.get(n) || Date.now())) / 1000) : 0,
                name: c.BOT_NAME || '', mode: c.mode || 'public', admin: n === OWNER
            };
        })
    });
});

router.get('/admin/config/:number', adminLimiter, adminAuth, async (req, res) => {
    const n = clean(req.params.number);
    try {
        const cfg = userConfigs.get(n) || await loadUserConfig(n);
        const out = {};
        for (const k of DASH_KEYS) out[k] = cfg[k];
        res.send({ number: n, online: activeSockets.has(n), config: out });
    } catch (e) { res.status(500).send({ error: 'Failed to load config' }); }
});

router.post('/admin/config/:number', adminLimiter, adminAuth, async (req, res) => {
    const n = clean(req.params.number);
    try { await setConfigFor(n, req.body && req.body.config); }
    catch (e) {
        if (e.message && !/Request failed|ECONN|timeout/i.test(e.message)) return res.status(400).send({ error: e.message });
        return res.status(500).send({ error: 'Failed to save settings' });
    }
    console.log(`✅ Admin changed settings of ${n}`);
    res.send({ status: 'success' });
});

router.post('/admin/unlink/:number', adminLimiter, adminAuth, async (req, res) => {
    const n = clean(req.params.number);
    try {
        const socket = activeSockets.get(n);
        if (socket) {
            const cfg = cfgOf(n);
            await sendNotice(socket, jidNormalizedUser(socket.user.id),
                formatMessage('🔌 ᴅɪꜱᴄᴏɴɴᴇᴄᴛᴇᴅ', '*Your bot was unlinked by the admin.*', cfg.BOT_FOOTER), cfg);
        }
    } catch (e) {}
    await fullDeleteSession(n);
    console.log(`⚠️ Admin unlinked ${n}`);
    res.send({ status: 'unlinked' });
});

router.get('/admin/logs', adminLimiter, adminAuth, (req, res) => {
    res.send({ logs: logger.tail(Number(req.query.since) || 0, 300), last: logger.lastId() });
});

router.post('/admin/run', adminLimiter, adminAuth, async (req, res) => {
    const cmd = String((req.body && req.body.cmd) || '');
    const link = String((req.body && req.body.link) || '');
    const emojis = String((req.body && req.body.emojis) || '');
    try {
        if (cmd === 'restart') { loadPlugins(); return res.send({ status: 'success', message: 'Plugins reloaded' }); }
        if (cmd === 'reconnect') {
            reconnectAll().then(r => console.log('Reconnect results:', JSON.stringify(r))).catch(e => console.error('Reconnect error:', e.message));
            return res.status(202).send({ status: 'started', message: 'Reconnecting in background, watch the console' });
        }
        if (cmd === 'clearlogs') { logger.clear(); return res.send({ status: 'success' }); }
        if (cmd === 'sub') {
            if (!parseChannel(link)) return res.status(400).send({ error: 'Invalid channel link' });
            subAll(link).catch(e => console.error('.sub failed:', e.message));
            return res.status(202).send({ status: 'started', message: 'Running, watch the console' });
        }
        if (cmd === 'chreact') {
            const p = parseChannel(link);
            if (!p || !p.serverId) return res.status(400).send({ error: 'Use a channel post link' });
            reactAll(link, emojis).catch(e => console.error('.chreact failed:', e.message));
            return res.status(202).send({ status: 'started', message: 'Running, watch the console' });
        }
        res.status(400).send({ error: 'Unknown command' });
    } catch (e) { res.status(500).send({ error: e.message }); }
});

/* ---------------- Admin (x-admin-key) ---------------- */
router.get('/active', adminOnly, (req, res) => {
    res.status(200).send({ count: activeSockets.size, numbers: Array.from(activeSockets.keys()) });
});

router.get('/botinfo', adminOnly, (req, res) => {
    try {
        const bots = Array.from(activeSockets.entries()).map(([number, socket]) => {
            const startTime = socketCreationTime.get(number) || Date.now();
            const uptime = Math.floor((Date.now() - startTime) / 1000);
            return {
                number,
                status: socket.ws && socket.ws.readyState === 1 ? 'online' : 'offline',
                uptime: `${Math.floor(uptime / 3600)}h ${Math.floor((uptime % 3600) / 60)}m ${Math.floor(uptime % 60)}s`,
                connectedAt: new Date(startTime).toLocaleString('en-US', { timeZone: 'Asia/Colombo' })
            };
        });
        res.json({ count: bots.length, bots });
    } catch (err) {
        res.status(500).json({ error: 'Failed to get bot info', details: err.message });
    }
});

router.get('/restart-plugins', adminOnly, (req, res) => {
    try {
        loadPlugins();
        const count = [...plugins.keys()].filter(k => !k.startsWith('__onmsg__')).length;
        res.send({ status: 'success', pluginsLoaded: count });
    } catch (e) {
        res.status(500).send({ error: e.message });
    }
});

const reconnectHandler = async (req, res) => {
    res.status(202).send({ status: 'started', message: 'Reconnecting in background, check /code/active' });
    reconnectAll()
        .then(r => console.log('Reconnect results:', JSON.stringify(r)))
        .catch(e => console.error('Reconnect error:', e.message));
};
router.get('/connect-all', adminOnly, reconnectHandler);
router.get('/reconnect', adminOnly, reconnectHandler);

router.get('/getabout', adminOnly, async (req, res) => {
    const { number, target } = req.query;
    if (!number || !target) return res.status(400).send({ error: 'Number and target number are required' });

    const socket = activeSockets.get(clean(number));
    if (!socket) return res.status(404).send({ error: 'No active session found for this number' });

    const targetJid = `${clean(target)}@s.whatsapp.net`;
    try {
        const raw = await socket.fetchStatus(targetJid);
        const r = Array.isArray(raw) ? raw[0] : raw;
        const st = r && r.status;
        const about = typeof st === 'string' ? st : (st && st.status);
        const setAt = (r && r.setAt) || (st && st.setAt);
        res.status(200).send({
            status: 'success',
            number: target,
            about: about || 'No status available',
            setAt: setAt ? moment(setAt).tz('Asia/Colombo').format('YYYY-MM-DD HH:mm:ss') : 'Unknown'
        });
    } catch (error) {
        res.status(500).send({ status: 'error', message: `Failed to fetch About status for ${target}.` });
    }
});

/* ------------------------------------------------------------------ */
/*  Startup / shutdown                                                 */
/* ------------------------------------------------------------------ */
setTimeout(() => {
    reconnectAll()
        .then(r => console.log(`🔁 Auto reconnect done (${r.length} sessions)`))
        .catch(e => console.error('❌ autoReconnect error:', e.message));
}, 3000);

router.shutdown = async () => {
    for (const [n, rec] of sessions) {
        rec.stopped = true;
        if (rec.pairTimer) clearTimeout(rec.pairTimer);
        stopPresence(rec);
        const socket = activeSockets.get(n) || rec.socket;
        if (socket) detach(socket);
    }
    activeSockets.clear();
    await Promise.allSettled([...authHandles.values()].map(a => a.flush()));
};


module.exports = router;
