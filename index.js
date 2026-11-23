'use strict';

const express = require('express');
const http = require('http');
const path = require('path');

const app = express();
const PORT = Number(process.env.PORT) || 8000;

app.set('trust proxy', 1);
app.disable('x-powered-by');

// Serve the pairing website at the main Railway URL.
app.get('/', (_req, res) => {
    res.sendFile(path.join(__dirname, 'index.html'));
});

// WhatsApp pairing and bot API routes.
const pairRouter = require('./pair');
app.use('/code', pairRouter);

app.get('/health', (_req, res) => {
    res.status(200).json({ status: 'ok' });
});

app.use((req, res) => {
    res.status(404).json({
        status: 'not_found',
        message: 'Route not found',
        path: req.originalUrl
    });
});

app.use((err, _req, res, _next) => {
    console.error('Express error:', err);
    if (res.headersSent) return;
    res.status(500).json({ status: 'error', message: 'Internal server error' });
});

const server = http.createServer(app);
server.listen(PORT, '0.0.0.0', () => {
    console.log('\n╭──────────────────────────────────────╮');
    console.log('│       QUEEN ZARA BOT IS ONLINE        │');
    console.log('╰──────────────────────────────────────╯');
    console.log(`🌐 Port: ${PORT}`);
    console.log('🔗 Pairing Website: /');
    console.log('⚙️  Pairing API: /code/?number=94xxxxxxxxx');
});

let shuttingDown = false;
async function shutdown(signal) {
    if (shuttingDown) return;
    shuttingDown = true;
    console.log(`\n${signal} received. Shutting down...`);
    server.close(async () => {
        try {
            if (typeof pairRouter.shutdown === 'function') await pairRouter.shutdown();
        } catch (err) {
            console.error('Bot shutdown error:', err);
        }
        process.exit(0);
    });
    setTimeout(() => process.exit(1), 10000).unref();
}
process.once('SIGINT', () => shutdown('SIGINT'));
process.once('SIGTERM', () => shutdown('SIGTERM'));

module.exports = app;
