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
            await 
