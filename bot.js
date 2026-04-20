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

// Initialize Gemini AI with proper SDK
const ai = new GoogleGenAI({
    apiKey: API_KEY
});

// --- STORAGE ---
const userCooldowns = new Map();
const userConversations = new Map();
const MSG_LIMIT = 5;
const TIME_WINDOW = 2 * 60 * 1000;
let lastApiCall = 0;
const pendingRequests = new Set(); // Track pending requests to avoid duplicates

// Retry configuration
const MAX_RETRIES = 3;
const RETRY_DELAY = 2000;

let bot;
let reconnectAttempts = 0;
const MAX_RECONNECT_ATTEMPTS = 10;
const RECONNECT_DELAY = 5000;

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
    bot.on('spawn', () => {
        console.log(`[Bot] Successfully spawned on ${botArgs.host}`);
        setTimeout(() => {
            try {
                bot.chat(`/login ${PASSWORD}`);
                console.log('[Bot] Login command sent');
            } catch (err) {
                console.error('[Error] Failed to send login command:', err);
            }
        }, 2000);
    });

    // Public Chat Listener with error handling
    bot.on('chat', (username, message) => {
        try {
            handleGeminiRequest(username, message, false);
        } catch (err) {
            console.error('[Error] Chat handler failed:', err);
        }
    });

    // Whisper Listener
    bot.on('whisper', (username, message) => {
        try {
            console.log(`[Whisper] ${username}: ${message}`);
            handleGeminiRequest(username, message, true);
        } catch (err) {
            console.error('[Error] Whisper handler failed:', err);
        }
    });

    // Fallback for messagestr
    bot.on('messagestr', (messagestr) => {
        try {
            // Match various whisper formats
            const whisperPatterns = [
                /^(\w+) whispers(?:\sto\syou)?: (.*)$/i,
                /^(\w+) whispers: (.*)$/i,
                /^\[(\w+) -> me\] (.*)$/i,
                /^From (\w+): (.*)$/i
            ];

            for (const pattern of whisperPatterns) {
                const match = messagestr.match(pattern);
                if (match) {
                    const sender = match[1];
                    const content = match[2];
                    console.log(`[Whisper Detected] ${sender}: ${content}`);
                    handleGeminiRequest(sender, content, true);
                    break;
                }
            }
        } catch (err) {
            console.error('[Error] Messagestr handler failed:', err);
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

    if (!approvedPlayers.has(username.toLowerCase())) {
        console.log(`[Blocked] ${username} not in approved list`);
        return;
    }

    // Normalize message
    const normalizedMessage = message.trim();
    if (!normalizedMessage) return;

    const words = normalizedMessage.toLowerCase().split(/\s+/);
    const triggerIndex = words.findIndex(w => w === '!gemini' || w === '!g' || w === '> !g' || w === '> !gemini');

    // Trigger if !gemini or !g is in first 3 words OR if it's a whisper
    if (triggerIndex !== -1 && triggerIndex < 3 || isWhisper === true) {
        // Extract prompt - handle both !gemini and !g
        const prompt = normalizedMessage
            .replace(/!gemini/i, '')
            .replace(/!g(?:\s|$)/i, '')
            .trim();

        if (!prompt) {
            safeChat(`/msg ${username} Please provide a message after !gemini`);
            return;
        }

        // Create unique request ID to prevent duplicate processing
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
            // Clean up request ID after a delay
            setTimeout(() => pendingRequests.delete(requestId), 10000);
        }
    }
}

async function processRequest(username, prompt, isWhisper, requestId, history) {
      
    // 1. Quota Check (freddison bypass)
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
            return {
                error: "Missing prefix"
            };
        }
    }

    // 2. Global API Cooldown
    const delay = Math.max(0, (lastApiCall + 5000) - Date.now());
    if (delay > 0) {
        console.log(`[Cooldown] Waiting ${delay}ms before API call`);
        await sleep(delay);
    }
    lastApiCall = Date.now();

    // 3. API Execution with retries
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

        // Using proper Gemini SDK with ZERO thinking mode
        const response = await ai.models.generateContent({
            model: "gemini-2.5-flash",
            contents: fullPrompt,
            config: {
                systemInstruction: "You are a helpful chat bot. Keep responses under 200 characters. Be concise and friendly.",
                thinkingConfig: {
                    thinkingLevel: ThinkingLevel.NONE  // ZERO THINKING
                },
                maxOutputTokens: 1000,
            }
        });

        if (!response || !response.text) {
            throw new Error('Empty response from API');
        }
        
        history.push({ role: "assistant", content: response.text });
        userConversations.set(username, history);
        
        const MAX_HISTORY = 4; // ~3 exchanges
        if (history.length > MAX_HISTORY) {
            history.splice(0, history.length - MAX_HISTORY);
        }
        
        const responseText = response.text.trim();
        console.log(`[Response] Success (${responseText.length} chars)`);
        return responseText;

    } catch (err) {
        console.error(`[API Error] Attempt ${attempt}/${MAX_RETRIES}:`, err.message || err);

        // Handle specific error types
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

        // Retry logic for transient errors
        if (attempt < MAX_RETRIES) {
            const retryDelay = RETRY_DELAY * attempt;
            console.log(`[Retry] Waiting ${retryDelay}ms before retry...`);
            await sleep(retryDelay);
            return callGeminiWithRetry(username, history, attempt + 1);
        }

        // Max retries exceeded
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
        // Clean and normalize text
        const cleanText = text
            .replace(/\n+/g, ' ')
            .replace(/\s+/g, ' ')
            .replace(/[*_`#]/g, '') // Remove markdown
            .trim();

        if (!cleanText) {
            console.warn('[Warning] Text became empty after cleaning');
            return;
        }

        // ALWAYS whisper back - never public chat
        const prefix = `/msg ${targetUser} `;
        const prefixLength = prefix.length;
        const MINECRAFT_CHAT_LIMIT = 256;
        const SAFETY_MARGIN = 10;
        const limit = MINECRAFT_CHAT_LIMIT - prefixLength - SAFETY_MARGIN;

        if (cleanText.length <= limit) {
            // Single message
            safeChat(`${prefix}${cleanText}`);
        } else {
            // Split into multiple messages
            const chunks = splitIntoChunks(cleanText, limit);
            console.log(`[Split] Message split into ${chunks.length} parts`);
            
            chunks.forEach((chunk, index) => {
                setTimeout(() => {
                    safeChat(`${prefix}${chunk}`);
                }, index * 2000); // 2s delay between chunks
            });
        }
    } catch (err) {
        console.error('[Error] Failed to send chat:', err);
    }
}

function splitIntoChunks(text, maxLength) {
    const chunks = [];
    let currentChunk = '';

    // Split by sentences first
    const sentences = text.match(/[^.!?]+[.!?]+|[^.!?]+$/g) || [text];

    for (const sentence of sentences) {
        if ((currentChunk + sentence).length <= maxLength) {
            currentChunk += sentence;
        } else {
            if (currentChunk) {
                chunks.push(currentChunk.trim());
            }
            
            // If single sentence is too long, split by words
            if (sentence.length > maxLength) {
                const words = sentence.split(' ');
                currentChunk = '';
                
                for (const word of words) {
                    if ((currentChunk + ' ' + word).length <= maxLength) {
                        currentChunk += (currentChunk ? ' ' : '') + word;
                    } else {
                        if (currentChunk) {
                            chunks.push(currentChunk.trim());
                        }
                        currentChunk = word;
                    }
                }
            } else {
                currentChunk = sentence;
            }
        }
    }

    if (currentChunk) {
        chunks.push(currentChunk.trim());
    }

    return chunks;
}

// --- UTILITY FUNCTIONS ---
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
    if (bot) {
        bot.quit();
    }
    process.exit(0);
});

process.on('uncaughtException', (err) => {
    console.error('[Fatal] Uncaught exception:', err);
    // Don't crash, try to continue
});

process.on('unhandledRejection', (reason, promise) => {
    console.error('[Fatal] Unhandled rejection at:', promise, 'reason:', reason);
    // Don't crash, try to continue
});

// --- START BOT ---
console.log('[Bot] Starting with ZERO thinking mode...');
createBot();
