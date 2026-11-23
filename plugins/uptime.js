const os = require('os');

module.exports = {
    name: 'uptime',
    alias: ['up'],

    async execute(socket, msg, args, text, ctx) {
        const botName = ctx.config.BOT_NAME || 'QUEEN ZARA';
        const footer = ctx.config.BOT_FOOTER || '© Sirimath';

        const uptime = process.uptime();

        const days = Math.floor(uptime / 86400);
        const hours = Math.floor((uptime % 86400) / 3600);
        const minutes = Math.floor((uptime % 3600) / 60);
        const seconds = Math.floor(uptime % 60);

        const formatTime = [
            `${days}d`,
            `${hours}h`,
            `${minutes}m`,
            `${seconds}s`
        ].join(' ');

        const memory = process.memoryUsage();
        const usedRAM = (memory.rss / 1024 / 1024).toFixed(2);
        const totalRAM = (os.totalmem() / 1024 / 1024).toFixed(2);

        const message = `
╭━━〔 👑 〕━━╮
┃
┃  *${botName}*
┃
┃  🟢 Status : Online
┃  ⏱️ Uptime : ${formatTime}
┃  💾 RAM    : ${usedRAM} MB
┃  🖥️ System : ${os.platform()}
┃
╰━━━━━━━━━━╯

> ${footer}
`;

        await socket.sendMessage(ctx.from, {
            text: message
        }, { quoted: msg });
    }
};
