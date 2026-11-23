module.exports = {
    name: 'alive',
    alias: ['online'],

    async execute(socket, msg, args, text, ctx) {
        const botName = ctx.config.BOT_NAME || 'QUEEN ZARA';
        const footer = ctx.config.BOT_FOOTER || '© Sirimath';

        await socket.sendMessage(ctx.from, {
            text: `
╭━━〔 👑 〕━━╮
┃  *${botName}*
┃
┃  Status : Online 🟢
┃  Mode   : Active
┃
╰━━━━━━━━━━╯

> ${footer}
            `,
        }, { quoted: msg });
    }
};
