module.exports = {
    name: 'ping',
    alias: ['zara', 'speed'],

    async execute(socket, msg, args, text, ctx) {
        const botName = ctx.config.BOT_NAME || 'QUEEN ZARA';
        const footer = ctx.config.BOT_FOOTER || '© Sirimath';

        try {
            var startTime = new Date().getTime();
            let sentMessage = await socket.sendMessage(ctx.from, {
                text: "*_Pinging to Queen Zara Module..._* ❗"
            }, { quoted: msg });

            var endTime = new Date().getTime();

            const loadingStages = [
                "◍○○○○",
                "◍◍○○○",
                "◍◍◍○○",
                "◍◍◍◍○",
                "◍◍◍◍◍"
            ];

            for (let stage of loadingStages) {
                await socket.sendMessage(ctx.from, { text: stage, edit: sentMessage.key });
            }

            await socket.sendMessage(ctx.from, {
                text: `📍️ *𝐐ᴜᴇᴇɴ 𝐙ᴀʀᴀ 𝐒ᴘᴇᴇᴅ ${endTime - startTime} Ms* \n\n> ${footer}`,
                edit: sentMessage.key
            });

        } catch (e) {
            console.log(e);
            await socket.sendMessage(ctx.from, { text: "*Error !!*" }, { quoted: msg });
        }
    }
};
