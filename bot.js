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
let reconnecting = false;
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
// TRIGGER DETECTION
// Matches: !g, !gemini, > !g, >!gemini, and variants with trailing comma
// -------------------------------------------------------------------
const TRIGGER_REGEX = /(?:^|>)\s*!g(?:emini)?,?\b/i;

function hasTrigger(text) {
    return TRIGGER_REGEX.test(text);
}

function stripTrigger(text) {
    return text.replace(/(?:^|>)\s*!g(?:emini)?,?\s*/gi, '').trim();
}

// -------------------------------------------------------------------
// COMPONENT TREE HELPERS
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

/**
 * Recursively walk a component tree.
 * Returns the first suggestCommand clickEvent value that starts with "/msg ".
 */
function findClickEventValue(component) {
    if (!component || typeof component !== 'object') return null;

    if (component.clickEvent?.action === 'suggest_command') {
        const val = component.clickEvent.value || '';
        if (val.startsWith('/msg ')) return val;
    }

    for (const child of (component.extra || [])) {
        const found = findClickEventValue(child);
        if (found) return found;
    }
    for (const child of (component.with || [])) {
        const found = findClickEventValue(child);
        if (found) return found;
    }

    return null;
}

/**
 * Strip "/msg " (and trailing space) from the clickEvent value to get the real username.
 * e.g. "/msg Alice " -> "Alice"
 */
function realUsernameFromClickValue(value) {
    // value is like "/msg Alice " or "/msg Alice"
    return value.replace(/^\/msg\s+/, '').trim();
}

/**
 * Parse a raw packet data object.
 * Returns { realUsername, plainText } or null.
 */
function parsePacket(data) {
    const candidates = [
        data.message,
        data.signedChat,
        data.unsignedContent,
        data.chatMessage,
        data.data,
        data.content,
    ];

    for (const raw of candidates) {
        if (!raw) continue;
        let component;
        try {
            component = typeof raw === 'string' ? JSON.parse(raw) : raw;
        } catch {
            continue;
        }
        if (typeof component !== 'object') continue;

        const clickValue = findClickEventValue(component);
        if (clickValue) {
            const realUsername = realUsernameFromClickValue(clickValue);
            const plainText = componentToPlainText(component);
            return { realUsername, plainText };
        }
    }
    return null;
}

// -------------------------------------------------------------------
// WHISPER EXTRACTION (system messages — real name in plain text)
// -------------------------------------------------------------------
const WHISPER_PATTERNS = [
    /^(\w+)\s+whispers(?:\s+to\s+you)?:\s*(.+)$/i,
    /^(\w+)\s+whispers:\s*(.+)$/i,
    /^\[(\w+)\s*->\s*me\]\s*(.+)$/i,
    /^From\s+(\w+):\s*(.+)$/i,
    /^(\w+)\s*»\s*(.+)$/i,
    /^(\w+)\s*→\s*(.+)$/i,
];

function parseWhisperPacket(data) {
    const candidates = [data.content, data.message, data.data];
    for (const raw of candidates) {
        if (!raw) continue;
        let text = raw;
        if (typeof raw === 'string' && raw.trim().startsWith('{')) {
            try { text = componentToPlainText(JSON.parse(raw)); } catch { /* not JSON */ }
        }
        for (const pattern of WHISPER_PATTERNS) {
            const match = text.match(pattern);
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
    // PRIMARY: raw packet interception via node-minecraft-protocol.
    // Fires before mineflayer processes anything.
    //
    // Public chat flow:
    //   1. Parse packet -> plainText + clickEvent value
    //   2. Check plainText for trigger word
    //   3. Strip "/msg " from clickEvent value -> real username
    //   4. Strip trigger from plainText -> prompt
    //
    // Whisper flow:
    //   1. Match whisper pattern -> real username + message
    //   2. Pass straight through (no trigger word needed)
    // -------------------------------------------------------------------
    bot._client.on('packet', (data, meta) => {
    try {
        const chatPackets = ['chat', 'player_chat', 'system_chat', 'profileless_chat'];
        if (!chatPackets.includes(meta.name)) return;

        // -------------------------
        // WHISPER FLOW
        // -------------------------
        const whisper = parseWhisperPacket(data);
        if (whisper) {
            const { realUsername, message } = whisper;

            if (realUsername === bot.username) return;

            console.log(`[Whisper] ${realUsername}: ${message}`);
            handleGeminiRequest(realUsername, message, true);
            return;
        }

        // -------------------------
        // PUBLIC CHAT FLOW
        // -------------------------
        const parsed = parsePacket(data);
        if (!parsed) return;

        let { realUsername, plainText } = parsed;

        if (realUsername === bot.username) return;

        // Remove "<username>" prefix if it exists
        let cleanText = plainText
    .replace(/^\[[^\]]+\]\s*/g, '')   // remove [Ultra]
    .replace(/^<[^>]+>\s*/g, '');     // remove <b>

        // Trigger check
        if (!hasTrigger(cleanText)) return;

        const prompt = stripTrigger(cleanText);

        if (!prompt) {
            safeChat(`/msg ${realUsername} Please provide a message after !gemini`);
            return;
        }

        console.log(`[Chat] ${realUsername}: ${prompt}`);
        handleGeminiRequest(realUsername, prompt, false, true);

    } catch (err) {
        console.error('[Error] Packet handler:', err);
    }
});

    // Whisper fallback (mineflayer native — fires if packet handler didn't catch it)
    bot.on('whisper', (username, message) => {
        try {
            console.log(`[Whisper] ${username}: ${message}`);
            handleGeminiRequest(username, message, true);
        } catch (err) {
            console.error('[Error] Whisper handler:', err);
        }
    });

    bot.on('error', (err) => console.error('[Bot Error]', err.message || err));
    bot.on('kicked', (reason) => { console.log('[Kicked]', reason); scheduleReconnect(); });
    bot.on('end', (reason) => { console.log('[Disconnected]', reason); scheduleReconnect(); });
    bot.on('login', () => console.log('[Bot] Logged in'));
}

function scheduleReconnect(reason = 'unknown') {
    if (reconnecting) {
        console.log('[Reconnect] Already scheduled, skipping...');
        return;
    }

    if (reconnectAttempts >= MAX_RECONNECT_ATTEMPTS) {
        console.error('[Fatal] Max reconnect attempts reached.');
        process.exit(1);
    }

    reconnecting = true;
    reconnectAttempts++;

    // 🔥 Exponential backoff (IMPORTANT)
    const delay = Math.min(300000, RECONNECT_DELAY * Math.pow(1.5, reconnectAttempts));

    console.log(`[Reconnect] Attempt ${reconnectAttempts} in ${Math.round(delay/1000)}s (${reason})`);

    setTimeout(() => {
        reconnecting = false;

        try {
            if (bot) {
                bot.removeAllListeners();
                bot.quit();
            }
        } catch {}

        createBot();
    }, delay);
}


// -------------------------------------------------------------------
// CORE HANDLER
// alreadyStripped = true means trigger word already removed from message
// -------------------------------------------------------------------
async function handleGeminiRequest(username, message, isWhisper, alreadyStripped = false) {
    if (!username || !message) return;
    if (username === bot.username) return;

    if (!approvedPlayers.has(username.toLowerCase())) {
        console.log(`[Blocked] ${username} is not an approved player`);
        return;
    }

    const normalizedMessage = message.trim();
    if (!normalizedMessage) return;

    let prompt;

    if (isWhisper) {
        // Whispers don't require a trigger word — the whole message is the prompt
        prompt = normalizedMessage;
    } else if (alreadyStripped) {
        // Packet handler already confirmed trigger + stripped it
        prompt = normalizedMessage;
    } else {
        // Fallback path: check for trigger ourselves
        if (!hasTrigger(normalizedMessage)) return;
        prompt = stripTrigger(normalizedMessage);
    }

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
        console.error(`[Error] Request from ${username} failed:`, err);
        safeChat(`/msg ${username} Request failed. Please try again.`);
    } finally {
        setTimeout(() => pendingRequests.delete(requestId), 10000);
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

Respond to the latest user message in under 600 characters (but lean to lower responses for easier questions). Be concise and friendly. No markdown. You are DPS_Gemini, a service bot for DPS (Dead Poets Society), a minecraft clan on 8b8t, who is the best 8b8t clan due to their unrivalled supremacy. DO NOT BE OVERLY PATRIOTIC! Do not bring up DPS in a chat unless it is 100% relevant. You were made by freddison for KurtzMC`;

        const response = await ai.models.generateContent({
            model: "gemini-2.5-flash",
            contents: fullPrompt,
            config: {
                systemInstruction: "You are a helpful chat bot. Keep responses under 200 characters. Be concise and friendly.",
                thinkingConfig: { thinkingLevel: ThinkingLevel.NONE },
                
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
