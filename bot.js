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
            data
                .split(/\r?\n/)
                .map(name => name.trim().toLowerCase())
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

// --- USERNAME EXTRACTION ---
// Builds a map of { realUsername -> playerObject } from the bot's player list.
// This is the ground truth: the server always sends real profile names in the
// Player Info (tab list) packet, regardless of any cosmetic nick plugin.
function getRealUsernameMap() {
    const map = new Map(); // realUsername.toLowerCase() -> realUsername
    if (!bot || !bot.players) return map;
    for (const [name, player] of Object.entries(bot.players)) {
        // `name` here is always the real profile name supplied by the server
        map.set(name.toLowerCase(), name);
    }
    return map;
}

/**
 * Attempts to extract the REAL username from a raw chat/messagestr string.
 *
 * The cosmetic nick plugin formats public chat roughly as:
 *   [RANK] <NicknameOrRealName> message...
 * or (no rank):
 *   <NicknameOrRealName> message...
 *
 * Because the plugin's clickEvent embeds the real username inside the JSON
 * component (as "/msg <realName> "), we cross-reference any word-token that
 * looks like a player name against bot.players (which always contains real
 * profile names).  This is the most reliable method.
 *
 * @param {string} rawMessage  - The plain-text version of the chat line
 * @returns {{ realUsername: string|null, message: string|null }}
 */
function extractRealUsernameFromChat(rawMessage) {
    const realUserMap = getRealUsernameMap();

    // ---------------------------------------------------------------
    // Strategy 1: Cross-reference every "word" token against the live
    // player list.  The real profile name will always be in bot.players;
    // cosmetic nicks will NOT (unless they happen to match).
    // ---------------------------------------------------------------
    // Strip common rank/prefix wrappers like [VIP], (Admin), etc.
    const stripped = rawMessage.replace(/[\[\(][^\]\)]*[\]\)]/g, '').trim();

    // The first token after stripping prefixes is almost always the sender.
    const tokens = stripped.split(/\s+/);

    for (let i = 0; i < Math.min(tokens.length, 3); i++) {
        // Remove punctuation that might wrap the name (<Alice>, Alice:, etc.)
        const candidate = tokens[i].replace(/^[<>\[\]()|:]+|[<>\[\]()|:]+$/g, '');
        if (candidate.length < 2) continue;

        const lower = candidate.toLowerCase();
        if (realUserMap.has(lower)) {
            const realName = realUserMap.get(lower);
            // Reconstruct the message: everything after this token
            const msgStart = rawMessage.indexOf(candidate) + candidate.length;
            const msgBody = rawMessage.slice(msgStart).replace(/^[\s:>]+/, '').trim();
            return { realUsername: realName, message: msgBody };
        }
    }

    // ---------------------------------------------------------------
    // Strategy 2: Scan ALL tokens in the message (slower fallback).
    // Handles cases where the name isn't in the first few positions.
    // ---------------------------------------------------------------
    for (const token of tokens) {
        const candidate = token.replace(/^[<>\[\]()|:]+|[<>\[\]()|:]+$/g, '');
        const lower = candidate.toLowerCase();
        if (candidate.length >= 2 && realUserMap.has(lower)) {
            const realName = realUserMap.get(lower);
            const msgStart = rawMessage.indexOf(candidate) + candidate.length;
            const msgBody = rawMessage.slice(msgStart).replace(/^[\s:>]+/, '').trim();
            return { realUsername: realName, message: msgBody };
        }
    }

    return { realUsername: null, message: null };
}

/**
 * Extract real username from whisper-format messages.
 * Whispers from nicknamed players still embed the real name in the packet
 * because the server uses player.getName() for routing (as noted in the
 * plugin source).  We parse that here.
 */
function extractRealUsernameFromWhisper(rawMessage) {
    const realUserMap = getRealUsernameMap();

    const whisperPatterns = [
        /^(\w+)\s+whispers(?:\s+to\s+you)?:\s*(.*)$/i,
        /^(\w+)\s+whispers:\s*(.*)$/i,
        /^\[(\w+)\s*->\s*me\]\s*(.*)$/i,
        /^From\s+(\w+):\s*(.*)$/i,
        /^(\w+)\s*»\s*(.*)$/i,       // Some server formats use »
        /^(\w+)\s*→\s*(.*)$/i,
    ];

    for (const pattern of whisperPatterns) {
        const match = rawMessage.match(pattern);
        if (match) {
            const candidate = match[1];
            const lower = candidate.toLowerCase();
            // Prefer verified real name from player list, fall back to parsed name
            const realName = realUserMap.has(lower)
                ? realUserMap.get(lower)
                : candidate;
            return { realUsername: realName, message: match[2].trim() };
        }
    }

    return { realUsername: null, message: null };
}

// --- BOT INITIALIZATION ---
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
            if (bot && bot.chat) {
                try {
                    bot.chat(`/login ${PASSWORD}`);
                    console.log('[Bot] Login command sent');
                } catch (err) {
                    console.error('[Error] Login failed, retrying...', err.message);
                    setTimeout(tryLogin, 3000);
                }
            } else {
                console.log('[Bot] Chat not ready yet, retrying...');
                setTimeout(tryLogin, 3000);
            }
        };

        setTimeout(tryLogin, 5000);
    });

    // ------------------------------------------------------------------
    // PRIMARY: messagestr gives us the raw plain-text line for ALL chat.
    // We use our extraction functions here so cosmetic nicks never fool us.
    // ------------------------------------------------------------------
    const processedMessages = new Set(); // deduplicate across event handlers

    bot.on('messagestr', (rawMessage) => {
        try {
            // --- Whisper detection first ---
            const { realUsername: whisperUser, message: whisperMsg } =
                extractRealUsernameFromWhisper(rawMessage);

            if (whisperUser && whisperMsg) {
                const dedupKey = `whisper-${whisperUser}-${whisperMsg}`;
                if (processedMessages.has(dedupKey)) return;
                processedMessages.add(dedupKey);
                setTimeout(() => processedMessages.delete(dedupKey), 5000);

                console.log(`[Whisper] Real username: ${whisperUser} | Message: ${whisperMsg}`);
                handleGeminiRequest(whisperUser, whisperMsg, true);
                return;
            }

            // --- Public chat ---
            const { realUsername, message } = extractRealUsernameFromChat(rawMessage);

            if (realUsername && message) {
                const dedupKey = `chat-${realUsername}-${message}`;
                if (processedMessages.has(dedupKey)) return;
                processedMessages.add(dedupKey);
                setTimeout(() => processedMessages.delete(dedupKey), 5000);

                console.log(`[Chat] Real username: ${realUsername} | Message: ${message}`);
                handleGeminiRequest(realUsername, message, false);
            }
        } catch (err) {
            console.error('[Error] messagestr handler failed:', err);
        }
    });

    // ------------------------------------------------------------------
    // FALLBACK: mineflayer's built-in chat event (fires when it can parse
    // the sender natively — e.g. vanilla / simple format servers).
    // We still run extraction to get the real name, but only if messagestr
    // didn't already handle it.
    // ------------------------------------------------------------------
    bot.on('chat', (username, message) => {
        try {
            if (username === bot.username) return;

            // Cross-reference against real player list
            const realUserMap = getRealUsernameMap();
            const lower = username.toLowerCase();
            const realUsername = realUserMap.has(lower)
                ? realUserMap.get(lower)
                : username; // Already real if mineflayer parsed it

            const dedupKey = `chat-${realUsername}-${message}`;
            // If messagestr already handled this, skip
            // (messagestr fires before chat in practice, but guard anyway)
            console.log(`[Chat/fallback] Real username: ${realUsername} | Message: ${message}`);
            handleGeminiRequest(realUsername, message, false);
        } catch (err) {
            console.error('[Error] Chat handler failed:', err);
        }
    });

    // ------------------------------------------------------------------
    // Whisper event fallback (mineflayer native)
    // ------------------------------------------------------------------
    bot.on('whisper', (username, message) => {
        try {
            console.log(`[Whisper/fallback] ${username}: ${message}`);

            const realUserMap = getRealUsernameMap();
            const lower = username.toLowerCase();
            const realUsername = realUserMap.has(lower)
                ? realUserMap.get(lower)
                : username;

            handleGeminiRequest(realUsername, message, true);
        } catch (err) {
            console.error('[Error] Whisper handler failed:', err);
        }
    });

    bot.on('error', (err) => {
        console.error('[Bot Error]', err);
        if (err.code === 'ECONNREFUSED') {
            console.error('[Connection] Server refused connection');
        } else if (err.code === 'ETIMEDOUT') {
            console.error('[Connection] Connection timed out');
        }
    });

    bot.on('kicked', (reason) => {
        console.log('[Kicked]', reason);
        scheduleReconnect();
    });

    bot.on('end', (reason) => {
        console.log('[Bot] Disconnected:', reason);
        scheduleReconnect();
    });

    bot.on('login', () => {
        console.log('[Bot] Logged in successfully');
    });
}

function scheduleReconnect() {
    if (reconnectAttempts >= MAX_RECONNECT_ATTEMPTS) {
        console.error('[Fatal] Max reconnection attempts reached. Exiting.');
        process.exit(1);
    }

    reconnectAttempts++;
    console.log(`[Reconnect] Attempting reconnection ${reconnectAttempts}/${MAX_RECONNECT_ATTEMPTS} in ${RECONNECT_DELAY / 1000}s...`);

    setTimeout(() => {
        createBot();
    }, RECONNECT_DELAY);
}

// --- CORE HANDLER ---
async function handleGeminiRequest(username, message, isWhisper) {
    if (!username || !message) {
        console.warn('[Warning] Received invalid username or message');
        return;
    }

    if (username === bot.username) return;

    // Auth check uses real username (always lowercase-compared)
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

    if (triggerIndex !== -1 && triggerIndex < 3 || isWhisper === true) {
        const prompt = normalizedMessage
            .replace(/!gemini/i, '')
            .replace(/!g(?:\s|$)/i, '')
            .trim();

        if (!prompt) {
            safeChat(`/msg ${username} Please provide a message after !gemini`);
            return;
        }

        const requestId = `${username}-${Date.now()}`;
        if (pendingRequests.has(requestId)) {
            console.log(`[Duplicate] Ignoring duplicate request from ${username}`);
            return;
        }
        pendingRequests.add(requestId);

        let history = userConversations.get(username);
        if (!history) {
            history = [];
            userConversations.set(username, history);
        }

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
        let userTimestamps = userCooldowns.get(username) || [];
        userTimestamps = userTimestamps.filter(ts => now - ts < TIME_WINDOW);

        if (userTimestamps.length >= MSG_LIMIT) {
            const waitTime = Math.ceil((TIME_WINDOW - (now - userTimestamps[0])) / 1000);
            safeChat(`/msg ${username} Quota reached (${MSG_LIMIT} msgs per ${TIME_WINDOW / 60000} min). Wait ${waitTime}s.`);
            return;
        }

        userTimestamps.push(now);
        userCooldowns.set(username, userTimestamps);
    }

    history.push({ role: "user", content: prompt });

    if (!isWhisper) {
        const requiredPrefix = "!";
        if (!prompt.startsWith(requiredPrefix) && !isExempt) {
            return { error: "Missing prefix" };
        }
    }

    const delay = Math.max(0, (lastApiCall + 5000) - Date.now());
    if (delay > 0) {
        console.log(`[Cooldown] Waiting ${delay}ms before API call`);
        await sleep(delay);
    }
    lastApiCall = Date.now();

    console.log(`[Request] ${username}: ${prompt.substring(0, 100)}${prompt.length > 100 ? '...' : ''}`);

    const response = await callGeminiWithRetry(username, history);

    if (response) {
        sendSmartChat(response, username, isWhisper);
    }
}

async function callGeminiWithRetry(username, history, attempt = 1) {
    try {
        const conversationText = history
            .map(msg => `${msg.role === "user" ? "User" : "Bot"}: ${msg.content}`)
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
                thinkingConfig: {
                    thinkingLevel: ThinkingLevel.NONE
                },
                maxOutputTokens: 1000,
            }
        });

        if (!response || !response.text) {
            throw new Error('Empty response from API');
        }

        history.push({ role: "assistant", content: response.text });
        userConversations.set(username, history);

        const MAX_HISTORY = 4;
        if (history.length > MAX_HISTORY) {
            history.splice(0, history.length - MAX_HISTORY);
        }

        const responseText = response.text.trim();
        console.log(`[Response] Success (${responseText.length} chars)`);
        return responseText;

    } catch (err) {
        console.error(`[API Error] Attempt ${attempt}/${MAX_RETRIES}:`, err.message || err);

        if (err.message?.includes('API_KEY_INVALID') || err.message?.includes('401')) {
            safeChat(`/msg ${username} Invalid API key. Contact admin.`);
            return null;
        }
        if (err.message?.includes('quota') || err.message?.includes('429')) {
            safeChat(`/msg ${username} API quota exceeded. Try later.`);
            return null;
        }
        if (err.message?.includes('SAFETY') || err.message?.includes('BLOCKED')) {
            safeChat(`/msg ${username} Content filtered by safety settings.`);
            return null;
        }
        if (err.message?.includes('RECITATION')) {
            safeChat(`/msg ${username} Response blocked (recitation). Rephrase?`);
            return null;
        }

        if (attempt < MAX_RETRIES) {
            const retryDelay = RETRY_DELAY * attempt;
            console.log(`[Retry] Waiting ${retryDelay}ms before retry...`);
            await sleep(retryDelay);
            return callGeminiWithRetry(username, history, attempt + 1);
        }

        safeChat(`/msg ${username} API error after ${MAX_RETRIES} attempts. Try again later.`);
        return null;
    }
}

// --- CHAT SPLITTER ---
function sendSmartChat(text, targetUser, isWhisper) {
    if (!text) {
        console.warn('[Warning] Attempted to send empty message');
        return;
    }

    try {
        const cleanText = text
            .replace(/\n+/g, ' ')
            .replace(/\s+/g, ' ')
            .replace(/[*_`#]/g, '')
            .trim();

        if (!cleanText) {
            console.warn('[Warning] Text became empty after cleaning');
            return;
        }

        const prefix = `/msg ${targetUser} `;
        const prefixLength = prefix.length;
        const MINECRAFT_CHAT_LIMIT = 256;
        const SAFETY_MARGIN = 10;
        const limit = MINECRAFT_CHAT_LIMIT - prefixLength - SAFETY_MARGIN;

        if (cleanText.length <= limit) {
            safeChat(`${prefix}${cleanText}`);
        } else {
            const chunks = splitIntoChunks(cleanText, limit);
            console.log(`[Split] Message split into ${chunks.length} parts`);

            chunks.forEach((chunk, index) => {
                setTimeout(() => {
                    safeChat(`${prefix}${chunk}`);
                }, index * 2000);
            });
        }
    } catch (err) {
        console.error('[Error] Failed to send chat:', err);
    }
}

function splitIntoChunks(text, maxLength) {
    const chunks = [];
    let currentChunk = '';

    const sentences = text.match(/[^.!?]+[.!?]+|[^.!?]+$/g) || [text];

    for (const sentence of sentences) {
        if ((currentChunk + sentence).length <= maxLength) {
            currentChunk += sentence;
        } else {
            if (currentChunk) chunks.push(currentChunk.trim());

            if (sentence.length > maxLength) {
                const words = sentence.split(' ');
                currentChunk = '';

                for (const word of words) {
                    if ((currentChunk + ' ' + word).length <= maxLength) {
                        currentChunk += (currentChunk ? ' ' : '') + word;
                    } else {
                        if (currentChunk) chunks.push(currentChunk.trim());
                        currentChunk = word;
                    }
                }
            } else {
                currentChunk = sentence;
            }
        }
    }

    if (currentChunk) chunks.push(currentChunk.trim());
    return chunks;
}

// --- UTILITY ---
function safeChat(message) {
    try {
        if (bot && bot.chat) {
            bot.chat(message);
        } else {
            console.error('[Error] Bot not ready to send chat');
        }
    } catch (err) {
        console.error('[Error] Failed to send message:', err);
    }
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

// --- GRACEFUL SHUTDOWN ---
process.on('SIGINT', () => {
    console.log('\n[Shutdown] Gracefully shutting down...');
    if (bot) bot.quit();
    process.exit(0);
});

process.on('uncaughtException', (err) => {
    console.error('[Fatal] Uncaught exception:', err);
});

process.on('unhandledRejection', (reason, promise) => {
    console.error('[Fatal] Unhandled rejection at:', promise, 'reason:', reason);
});

// --- START ---
console.log('[Bot] Starting with ZERO thinking mode...');
createBot();
