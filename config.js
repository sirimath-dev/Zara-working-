'use strict';

const settings = require('./settings');
const env = process.env;

const number = (value, fallback) => {
    const parsed = Number(value);
    return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback;
};

// Queen Zara main configuration.
// Keep private credentials in Railway environment variables where possible.
module.exports = Object.freeze({
    ...settings,

    FIREBASE_URL: env.FIREBASE_URL || 'https://zara-md-default-rtdb.asia-southeast1.firebasedatabase.app/',
    FIREBASE_SECRET: env.FIREBASE_SECRET || '',

    BOT_NAME: env.BOT_NAME || '★ 𝑸𝒖𝒆𝒆𝒏 𝒁𝒂𝒓𝒂 ★',
    BOT_FOOTER: env.BOT_FOOTER || '© 𝑺𝒊𝒓𝒊𝒎𝒂𝒕𝒉',
    PREFIX: env.PREFIX || '.',
    MAX_RETRIES: number(env.MAX_RETRIES, 3),
    GROUP_INVITE_LINK: env.GROUP_INVITE_LINK || 'https://chat.whatsapp.com/LN5YMwLN5ZOEQeQwHb8aF0?s=cl&p=a&mlu=4&ilr=4&iam=2',
    RCD_IMAGE_PATH: env.RCD_IMAGE_PATH || 'https://files.catbox.moe/29hxc2.jpg',
    OTP_EXPIRY: number(env.OTP_EXPIRY, 300000),
    OWNER_NUMBER: env.OWNER_NUMBER || '94740430151',
    OCR_API_KEY: env.OCR_API_KEY || '',
    OMDB_API_KEY: env.OMDB_API_KEY || 'c51d1824',

    NEWSLETTER_JID: env.NEWSLETTER_JID || '120363431110439058@newsletter',
    CHANNEL_REACT_EMOJIS: env.CHANNEL_REACT_EMOJIS || '💚,❤️,🔥,😍,👏,😎',

    ADMIN_KEY: env.ADMIN_KEY || '',
    ADMIN_PASSWORD: env.ADMIN_PASSWORD || '',
    DASH_URL: env.DASH_URL || 'https://zara.anuhas.site/',
    LOG_LEVEL: env.LOG_LEVEL || 'info'
});
