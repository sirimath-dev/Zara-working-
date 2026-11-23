'use strict';

const MAX_LOGS = 1500;
const logs = [];
let sequence = 0;
let installed = false;

const original = {};
const stringify = (value) => {
    if (typeof value === 'string') return value;
    if (value instanceof Error) return value.stack || value.message;
    try { return JSON.stringify(value); }
    catch (_) { return String(value); }
};

function push(level, args) {
    const entry = {
        id: ++sequence,
        time: new Date().toISOString(),
        level,
        message: args.map(stringify).join(' ')
    };
    logs.push(entry);
    if (logs.length > MAX_LOGS) logs.splice(0, logs.length - MAX_LOGS);
}

function install() {
    if (installed) return;
    installed = true;
    for (const level of ['log', 'info', 'warn', 'error', 'debug']) {
        original[level] = console[level].bind(console);
        console[level] = (...args) => {
            push(level, args);
            original[level](...args);
        };
    }
}

install();

module.exports = {
    tail(since = 0, limit = 300) {
        const after = Number(since) || 0;
        const count = Math.max(1, Math.min(Number(limit) || 300, 1000));
        return logs.filter(item => item.id > after).slice(-count);
    },
    lastId() {
        return sequence;
    },
    clear() {
        logs.length = 0;
        return true;
    },
    restore() {
        if (!installed) return;
        for (const level of Object.keys(original)) console[level] = original[level];
        installed = false;
    }
};
