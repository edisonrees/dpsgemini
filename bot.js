const mineflayer = require('mineflayer');
const { GoogleGenAI, ThinkingLevel } = require("@google/genai");
const fs = require('fs');

// --- CONFIGURATION ---
const botArgs = {
    host: '8b8t.me',
    port: 25565,
    username: 'DPS_Gemini',
    auth: 'offline',
    version: '1.20.1'
};

let approvedPlayers = new Set();

function loadApprovedPlayers() {
    try {
        const data = fs.readFileSync('approved_players.txt', 'utf8');
        approvedPlayers = new Set(
            data.split(/\r?\n/)
                .map(n => n.trim().toLowerCase())
                .filter(Boolean)
        );
        console.log(`[Auth] Loaded ${approvedPlayers.size} approved players`);
    } catch (err) {
        console.error('[Auth] Failed to load approved_players.txt:', err.message);
        approvedPlayers = new Set();
    }
}

const API_KEY = process.env.API_KEY;
const PASSWORD = process.env.MC_PASSWORD;

const ai = new GoogleGenAI({ apiKey: API_KEY });

// --- STORAGE ---
const userCooldowns = new Map();
const userConversations = new Map();
const MSG_LIMIT = 5;
const TIME_WINDOW = 2 * 60 * 1000;
let lastApiCall = 0;
const pendingRequests = new Set();
const MAX_RETRIES = 3;
const RETRY_DELAY = 2000;

let bot;
let reconnectAttempts = 0;
const MAX_RECONNECT_ATTEMPTS = 10000;
const RECONNECT_DELAY = 15000;

// -------------------------------------------------------------------
// RAW PACKET EXTRACTION
// The cosmetic nick plugin injects the REAL username into every chat
// message's clickEvent (suggestCommand: "/msg <realName> ") because
// it calls player.getName() there, not the display name.
// We read this before mineflayer touches anything.
// -------------------------------------------------------------------

function componentToPlainText(component) {
    if (typeof component === 'string') return component;
    let text = component.text || '';
    if (Array.isArray(component.extra)) {
        text += component.extra.map(componentToPlainText).join('');
    }
    if (Array.isArray(component.with)) {
        text += component.with.map(componentToPlainText).join('');
    }
    return text;
}

function extractRealNameFromClickEvent(component) {
    if (!component || typeof component !== 'object') return null;

    if (component.clickEvent) {
        const { action, value } = component.clickEvent;
        if (action === 'suggest_command' && typeof value === 'string') {
            const match = value.match(/^\/msg\s+(\S+)/i);
            if (match) return match[1];
        }
    }

    if (Array.isArray(component.extra)) {
        for (const child of component.extra) {
            const found = extractRealNameFromClickEvent(child);
            if (found) return found;
        }
    }

    if (Array.isArray(component.with)) {
        for (const child of component.with) {
            const found = extractRealNameFromClickEvent(child);
            if (found) return found;
        }
    }

    return null;
}

function parseRawChatPacket(data) {
    // Try every field that might contain the JSON chat component
    const rawFields = [
        data.message,
        data.signedChat,
        data.unsignedContent,
        data.chatMessage,
        data.data,
    ];

    for (const raw of rawFields) {
        if (!raw) continue;

        let component;
        try {
            component = typeof raw === 'string' ? JSON.parse(raw) : raw;
        } catch {
            continue;
        }

        const realUsername = extractRealNameFromClickEvent(component);
        if (realUsername) {
            const plainText = componentToPlainText(component);

            // Strip the display portion and isolate just the message body.
            // Chat lines look like: "[RANK] NickName: hello" or "<Nick> hello"
            let messageBody = plainText;
            // Remove rank/prefix blocks: [VIP], (Admin), etc.
            messageBody = messageBody.replace(/^(?:\s*[\[\(][^\]\)]*[\]\)]\s*)+/, '').trim();
            // Remove the leading name chunk (everything up to first ": " or "> " or " ")
            const separatorMatch = messageBody.match(/^[^\s:>»]+[\s:>»]+(.*)$/);
            if (separatorMatch) {
                messageBody = separatorMatch[1].trim();
            }

            return { realUsername, message: messageBody };
        }
    }

    return null;
}

function extractWhisperFromRaw(data) {
    const whisperPatterns = [
        /^(\w+)\s+whispers(?:\s+to\s+you)?:\s*(.+)$/i,
        /^(\w+)\s+whispers:\s*(.+)$/i,
        /^\[(\w+)\s*->\s*me\]\s*(.+)$/i,
        /^From\s+(\w+):\s*(.+)$/i,
        /^(\w+)\s*»\s*(.+)$/i,
        /^(\w+)\s*→\s*(.+)$/i,
    ];

    const rawFields = [data.content, data.message, data.data];

    for (const raw of rawFields) {
        if (!raw) continue;
        let plainText = raw;
        if (typeof raw === 'string' && raw.trim().startsWith('{')) {
            try {
                plainText = componentToPlainText(JSON.parse(raw));
            } catch { /* not JSON */ }
        }
        for (const pattern of whisperPatterns) {
            const match = plainText.match(pattern);
            if (match) return { realUsername: match[1], message: match[2].trim() };
        }
    }
    return null;
}

// -------------------------------------------------------------------
// BOT INITIALIZATION
// -------------------------------------------------------------------
function createBot() {
    try {
        bot = mineflayer.createBot(botArgs);
        setupBotEvents();
        reconnectAttempts = 0;
        console.log('[Bot] Initializing...');
    } catch (err) {
        console.error('[Fatal] Failed to create bot:', err);
        scheduleReconnect();
    }
}

loadApprovedPlayers();

function setupBotEvents() {
    bot.once('spawn', () => {
        console.log('[Bot] Spawned, waiting for chat readiness...');
        const tryLogin = () => {
            if (bot?.chat) {
                try {
                    bot.chat(`/login ${PASSWORD}`);
                    console.log('[Bot] Login command sent');
                } catch (err) {
                    console.error('[Error] Login failed, retrying...', err.message);
                    setTimeout(tryLogin, 3000);
                }
            } else {
                setTimeout(tryLogin, 3000);
            }
        };
        setTimeout(tryLogin, 5000);
    });

    // -------------------------------------------------------------------
    // PRIMARY: intercept raw packets via node-minecraft-protocol.
    // This fires before mineflayer parses anything, so we see the full
    // JSON component including the clickEvent with the real username.
    // -------------------------------------------------------------------
    bot._client.on('packet', (data, meta) => {
        try {
            const chatPackets = ['chat', 'player_chat', 'system_chat', 'profileless_chat'];
            if (!chatPackets.includes(meta.name)) return;

            // Debug: log packet structure so you can tune parsing if needed
            console.log(`[Packet] name=${meta.name} keys=${Object.keys(data).join(',')}`);

            // --- Whisper detection first ---
            const whisper = extractWhisperFromRaw(data);
            if (whisper) {
                const { realUsername, message } = whisper;
                if (realUsername === bot.username) return;
                console.log(`[Packet/Whisper] Real: ${realUsername} | Msg: ${message}`);
                handleGeminiRequest(realUsername, message, true);
                return;
            }

            // --- Public chat with clickEvent extraction ---
            const chat = parseRawChatPacket(data);
            if (chat) {
                const { realUsername, message } = chat;
                if (realUsername === bot.username) return;
                console.log(`[Packet/Chat] Real: ${realUsername} | Msg: ${message}`);
                handleGeminiRequest(realUsername, message, false);
                return;
            }

            // If neither matched, log the raw fields so you can debug
            console.log(`[Packet/NoMatch] Dumping fields for debugging:`);
            for (const [k, v] of Object.entries(data)) {
                if (v != null) console.log(`  ${k}: ${String(v).substring(0, 300)}`);
            }

        } catch (err) {
            console.error('[Error] Raw packet handler failed:', err);
        }
    });

    // Whisper fallback (mineflayer native, for vanilla-format servers)
    bot.on('whisper', (username, message) => {
        try {
            console.log(`[Whisper/fallback] ${username}: ${message}`);
            handleGeminiRequest(username, message, true);
        } catch (err) {
            console.error('[Error] Whisper handler failed:', err);
        }
    });

    bot.on('error', (err) => console.error('[Bot Error]', err));
    bot.on('kicked', (reason) => { console.log('[Kicked]', reason); scheduleReconnect(); });
    bot.on('end', (reason) => { console.log('[Bot] Disconnected:', reason); scheduleReconnect(); });
    bot.on('login', () => console.log('[Bot] Logged in successfully'));
}

function scheduleReconnect() {
    if (reconnectAttempts >= MAX_RECONNECT_ATTEMPTS) {
        console.error('[Fatal] Max reconnect attempts reached.');
        process.exit(1);
    }
    reconnectAttempts++;
    console.log(`[Reconnect] Attempt ${reconnectAttempts}/${MAX_RECONNECT_ATTEMPTS} in ${RECONNECT_DELAY / 1000}s...`);
    setTimeout(createBot, RECONNECT_DELAY);
}

// -------------------------------------------------------------------
// CORE HANDLER
// -------------------------------------------------------------------
async function handleGeminiRequest(username, message, isWhisper) {
    if (!username || !message) return;
    if (username === bot.username) return;

    if (!approvedPlayers.has(username.toLowerCase())) {
        console.log(`[Blocked] ${username} not in approved list`);
        return;
    }

    const normalizedMessage = message.trim();
    if (!normalizedMessage) return;

    const words = normalizedMessage.toLowerCase().split(/\s+/);
    const triggerIndex = words.findIndex(
        w => w === '!gemini' || w === '!g' || w === '> !g' || w === '> !gemini'
    );

    if ((triggerIndex !== -1 && triggerIndex < 3) || isWhisper === true) {
        const prompt = normalizedMessage
            .replace(/!gemini/gi, '')
            .replace(/!g(?:\s|$)/gi, '')
            .trim();

        if (!prompt) {
            safeChat(`/msg ${username} Please provide a message after !gemini`);
            return;
        }

        const requestId = `${username}-${Date.now()}`;
        if (pendingRequests.has(requestId)) return;
        pendingRequests.add(requestId);

        const history = userConversations.get(username) || [];
        userConversations.set(username, history);

        try {
            await processRequest(username, prompt, isWhisper, requestId, history);
        } catch (err) {
            console.error('[Error] Request processing failed:', err);
            safeChat(`/msg ${username} Request failed. Please try again.`);
        } finally {
            setTimeout(() => pendingRequests.delete(requestId), 10000);
        }
    }
}

async function processRequest(username, prompt, isWhisper, requestId, history) {
    const isExempt = username.toLowerCase() === 'freddison';

    if (!isExempt) {
        const now = Date.now();
        let timestamps = (userCooldowns.get(username) || []).filter(ts => now - ts < TIME_WINDOW);
        if (timestamps.length >= MSG_LIMIT) {
            const wait = Math.ceil((TIME_WINDOW - (now - timestamps[0])) / 1000);
            safeChat(`/msg ${username} Quota reached (${MSG_LIMIT} msgs/${TIME_WINDOW / 60000}min). Wait ${wait}s.`);
            return;
        }
        timestamps.push(now);
        userCooldowns.set(username, timestamps);
    }

    history.push({ role: "user", content: prompt });

    if (!isWhisper && !isExempt && !prompt.startsWith('!')) return;

    const delay = Math.max(0, (lastApiCall + 5000) - Date.now());
    if (delay > 0) await sleep(delay);
    lastApiCall = Date.now();

    console.log(`[Request] ${username}: ${prompt.substring(0, 100)}`);
    const response = await callGeminiWithRetry(username, history);
    if (response) sendSmartChat(response, username, isWhisper);
}

async function callGeminiWithRetry(username, history, attempt = 1) {
    try {
        const conversationText = history
            .map(m => `${m.role === "user" ? "User" : "Bot"}: ${m.content}`)
            .join("\n");

        const fullPrompt = `You are a helpful chat bot.

Conversation so far:
${conversationText}

Respond to the latest user message in under 200 characters. Be concise and friendly. No markdown. You are DPS_Gemini, a service bot for DPS (Dead Poets Society), a minecraft clan on 8b8t, who is the best 8b8t clan due to their unrivalled supremacy. DO NOT BE OVERLY PATRIOTIC! Do not bring up DPS in a chat unless it is 100% relevant. You were made by freddison for KurtzMC`;

        const response = await ai.models.generateContent({
            model: "gemini-2.5-flash",
            contents: fullPrompt,
            config: {
                systemInstruction: "You are a helpful chat bot. Keep responses under 200 characters. Be concise and friendly.",
                thinkingConfig: { thinkingLevel: ThinkingLevel.NONE },
                maxOutputTokens: 1000,
            }
        });

        if (!response?.text) throw new Error('Empty response from API');

        history.push({ role: "assistant", content: response.text });
        userConversations.set(username, history);
        if (history.length > 4) history.splice(0, history.length - 4);

        const responseText = response.text.trim();
        console.log(`[Response] ${responseText.length} chars`);
        return responseText;

    } catch (err) {
        console.error(`[API Error] Attempt ${attempt}/${MAX_RETRIES}:`, err.message);
        if (err.message?.includes('API_KEY_INVALID') || err.message?.includes('401')) {
            safeChat(`/msg ${username} Invalid API key. Contact admin.`); return null;
        }
        if (err.message?.includes('quota') || err.message?.includes('429')) {
            safeChat(`/msg ${username} API quota exceeded. Try later.`); return null;
        }
        if (err.message?.includes('SAFETY') || err.message?.includes('BLOCKED')) {
            safeChat(`/msg ${username} Content filtered by safety settings.`); return null;
        }
        if (err.message?.includes('RECITATION')) {
            safeChat(`/msg ${username} Response blocked (recitation). Rephrase?`); return null;
        }
        if (attempt < MAX_RETRIES) {
            await sleep(RETRY_DELAY * attempt);
            return callGeminiWithRetry(username, history, attempt + 1);
        }
        safeChat(`/msg ${username} API error after ${MAX_RETRIES} attempts. Try again later.`);
        return null;
    }
}

function sendSmartChat(text, targetUser) {
    if (!text) return;
    try {
        const cleanText = text.replace(/\n+/g, ' ').replace(/\s+/g, ' ').replace(/[*_`#]/g, '').trim();
        if (!cleanText) return;
        const prefix = `/msg ${targetUser} `;
        const limit = 256 - prefix.length - 10;
        if (cleanText.length <= limit) {
            safeChat(`${prefix}${cleanText}`);
        } else {
            const chunks = splitIntoChunks(cleanText, limit);
            chunks.forEach((chunk, i) => setTimeout(() => safeChat(`${prefix}${chunk}`), i * 2000));
        }
    } catch (err) {
        console.error('[Error] sendSmartChat:', err);
    }
}

function splitIntoChunks(text, maxLength) {
    const chunks = [];
    let current = '';
    const sentences = text.match(/[^.!?]+[.!?]+|[^.!?]+$/g) || [text];
    for (const sentence of sentences) {
        if ((current + sentence).length <= maxLength) {
            current += sentence;
        } else {
            if (current) chunks.push(current.trim());
            if (sentence.length > maxLength) {
                const words = sentence.split(' ');
                current = '';
                for (const word of words) {
                    if ((current + ' ' + word).length <= maxLength) {
                        current += (current ? ' ' : '') + word;
                    } else {
                        if (current) chunks.push(current.trim());
                        current = word;
                    }
                }
            } else {
                current = sentence;
            }
        }
    }
    if (current) chunks.push(current.trim());
    return chunks;
}

function safeChat(message) {
    try {
        if (bot?.chat) bot.chat(message);
        else console.error('[Error] Bot not ready');
    } catch (err) {
        console.error('[Error] safeChat:', err);
    }
}

function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }

process.on('SIGINT', () => { if (bot) bot.quit(); process.exit(0); });
process.on('uncaughtException', err => console.error('[Fatal] Uncaught:', err));
process.on('unhandledRejection', (r, p) => console.error('[Fatal] Rejection:', p, r));

console.log('[Bot] Starting...');
createBot();
