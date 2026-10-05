'use strict';

const fs = require('node:fs');
const fsp = fs.promises;
const path = require('node:path');
const crypto = require('node:crypto');

const PROTOCOL = 8;
const SCHEMA = 8;

const info = {
    id: 'multi-client-sync',
    name: 'Multi-Client Chat Synchronization',
    description: 'Authenticated, per-chat synchronization and live generation coordination for SillyTavern clients.',
};

const LIMITS = Object.freeze({
    maxRequestBytes: 8 * 1024 * 1024,
    maxSnapshotBytes: 6 * 1024 * 1024,
    maxMetadataBytes: 512 * 1024,
    maxGroupSettingsBytes: 512 * 1024,
    maxEventBytes: 512 * 1024,

    maxMessages: 16_000,
    maxSwipesPerMessage: 128,
    maxFilesPerMessage: 64,
    maxMediaPerMessage: 64,
    maxToolInvocationsPerMessage: 128,

    maxEvents: 256,
    maxTombstones: 4_000,
    maxRecentOps: 4_096,
    maxBranches: 1_024,
    maxLiveGenerationMessages: 64,
    maxLiveGenerationBytes: 1_500_000,

    maxPersistedStateBytes: 12 * 1024 * 1024,
    maxPersistedBytesPerUser: 96 * 1024 * 1024,

    maxScopesPerProcess: 256,
    maxScopesPerUser: 128,

    maxSseTotal: 512,
    maxSsePerUser: 24,

    maxEventsPerClientPerMinute: 600,

    memberTtlMs: 45_000,
    generationLeaseMs: 15_000,
    generationMaxMs: 30 * 60_000,

    staleTempMs: 10 * 60_000,
    staleStateMs: 30 * 24 * 60 * 60_000,
});

const FORBIDDEN_KEYS = new Set(['__proto__', 'prototype', 'constructor']);
const MUTATION_TYPES = new Set(['snapshot', 'metadata', 'reconcile_local', 'group_settings', 'branch_announce']);
const GENERATION_TYPES = new Set([
    'generation_claim',
    'generation_heartbeat',
    'generation_started',
    'generation_stream',
    'generation_stop_request',
    'generation_terminal',
    'generation_recover',
]);
const ALL_EVENT_TYPES = new Set([...MUTATION_TYPES, ...GENERATION_TYPES]);

const scopes = new Map();
const members = new Map();
const subscriptions = new Map();
const operationChains = new Map();
const userOperationChains = new Map();
const persistenceChains = new Map();
const userPersistenceChains = new Map();
const rateWindows = new Map();
const stateFiles = new Map();
const stateLoads = new Map();

let totalSseConnections = 0;
let shuttingDown = false;
let cleanupTimer = null;

const now = () => Date.now();
const clone = value => structuredClone(value);
const randomId = (prefix = '') => `${prefix}${crypto.randomBytes(18).toString('hex')}`;
const sha256 = value => crypto.createHash('sha256').update(String(value)).digest('hex');
const stableJson = value => JSON.stringify(value);
const bytes = value => Buffer.byteLength(stableJson(value), 'utf8');

function isObject(value) {
    return value !== null && typeof value === 'object' && !Array.isArray(value);
}

function safeId(value, max = 256) {
    return typeof value === 'string'
        && value.length > 0
        && value.length <= max
        && !/[\\/\u0000-\u001f]/.test(value);
}

function safeName(value, max = 255) {
    return typeof value === 'string'
        && value.length > 0
        && value.length <= max
        && value !== '.'
        && value !== '..'
        && !/[\\/:*?"<>|\u0000-\u001f]/.test(value);
}

function pathIsUnder(parent, child) {
    const base = path.resolve(parent);
    const target = path.resolve(child);
    return target === base || target.startsWith(`${base}${path.sep}`);
}

function safeJoin(parent, ...parts) {
    const target = path.resolve(parent, ...parts);
    if (!pathIsUnder(parent, target)) throw new Error('Path escapes allowed directory');
    return target;
}

function userIdFromRequest(req) {
    const handle = req?.user?.profile?.handle;
    return typeof handle === 'string' && handle.trim() ? handle.trim() : null;
}

function userRootFromRequest(req) {
    const root = req?.user?.directories?.root;
    if (!root) throw new Error('Authenticated user root unavailable');
    return path.resolve(root);
}

function stateRootFromRequest(req) {
    return safeJoin(userRootFromRequest(req), 'multi-client-sync', 'state');
}

function sendError(res, status, code, message, extra = {}) {
    return res.status(status).json({ ok: false, error: { code, message, ...extra } });
}

function requestBodyTooLarge(req) {
    try { return bytes(req.body ?? {}) > LIMITS.maxRequestBytes; } catch { return true; }
}

function validateDataTree(value, depth = 0, seen = new WeakSet()) {
    if (depth > 40) return false;
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return true;
    if (typeof value === 'number') return Number.isFinite(value);
    if (typeof value !== 'object') return false;
    if (seen.has(value)) return false;
    seen.add(value);
    if (Array.isArray(value)) return value.every(child => validateDataTree(child, depth + 1, seen));
    for (const [key, child] of Object.entries(value)) {
        if (FORBIDDEN_KEYS.has(key)) return false;
        if (!validateDataTree(child, depth + 1, seen)) return false;
    }
    return true;
}

function validateAttachment(attachment) {
    if (!isObject(attachment)) return false;
    if (attachment.url !== undefined && (typeof attachment.url !== 'string' || attachment.url.length > 4096)) return false;
    if (attachment.name !== undefined && (typeof attachment.name !== 'string' || attachment.name.length > 1024)) return false;
    if (attachment.text !== undefined && (typeof attachment.text !== 'string' || attachment.text.length > 1_500_000)) return false;
    if (attachment.size !== undefined && (!Number.isFinite(Number(attachment.size)) || Number(attachment.size) < 0)) return false;
    return true;
}

function getMessageId(message) {
    return message?.extra?.multi_client_sync?.messageId || null;
}

function validateMessage(message, index) {
    if (!isObject(message)) return `message ${index} is invalid`;
    if (message.extra !== undefined && !isObject(message.extra)) return `message ${index}.extra is invalid`;
    if (!validateDataTree(message)) return `message ${index} contains unsupported values`;

    const syncId = getMessageId(message);
    if (syncId !== undefined && syncId !== null && !safeId(syncId, 128)) return `message ${index} has an invalid synchronization ID`;
    if (message.swipes !== undefined && !Array.isArray(message.swipes)) return `message ${index}.swipes is invalid`;
    if (Array.isArray(message.swipes) && message.swipes.length > LIMITS.maxSwipesPerMessage) return `message ${index} has too many swipes`;
    if (message.swipe_info !== undefined && !Array.isArray(message.swipe_info)) return `message ${index}.swipe_info is invalid`;
    if (Array.isArray(message.swipe_info) && message.swipe_info.length > LIMITS.maxSwipesPerMessage) return `message ${index} has too much swipe metadata`;
    if (message.swipe_id !== undefined && (!Number.isInteger(Number(message.swipe_id)) || Number(message.swipe_id) < 0)) return `message ${index}.swipe_id is invalid`;
    if (Array.isArray(message.swipes) && message.swipe_id !== undefined && Number(message.swipe_id) >= message.swipes.length) return `message ${index}.swipe_id is out of range`;

    const files = message?.extra?.files;
    if (files !== undefined && !Array.isArray(files)) return `message ${index}.extra.files is invalid`;
    if (Array.isArray(files) && files.length > LIMITS.maxFilesPerMessage) return `message ${index} has too many files`;
    if (Array.isArray(files) && !files.every(validateAttachment)) return `message ${index} has an invalid file attachment`;

    const media = message?.extra?.media;
    if (media !== undefined && !Array.isArray(media)) return `message ${index}.extra.media is invalid`;
    if (Array.isArray(media) && media.length > LIMITS.maxMediaPerMessage) return `message ${index} has too much media`;
    if (Array.isArray(media) && !media.every(validateAttachment)) return `message ${index} has invalid media`;

    const tools = message?.extra?.tool_invocations;
    if (tools !== undefined && !Array.isArray(tools)) return `message ${index}.extra.tool_invocations is invalid`;
    if (Array.isArray(tools) && tools.length > LIMITS.maxToolInvocationsPerMessage) return `message ${index} has too many tool invocations`;
    return null;
}

function validateSnapshot(snapshot) {
    if (!Array.isArray(snapshot)) return { ok: false, error: 'snapshot must be an array' };
    if (snapshot.length > LIMITS.maxMessages) return { ok: false, error: 'too many messages' };
    if (!validateDataTree(snapshot)) return { ok: false, error: 'snapshot contains unsupported values' };
    for (let index = 0; index < snapshot.length; index++) {
        const error = validateMessage(snapshot[index], index);
        if (error) return { ok: false, error };
    }
    if (bytes(snapshot) > LIMITS.maxSnapshotBytes) return { ok: false, error: 'snapshot exceeds payload limit' };
    return { ok: true };
}

function validateMetadata(metadata) {
    if (!isObject(metadata)) return { ok: false, error: 'chatMetadata must be an object' };
    if (!validateDataTree(metadata)) return { ok: false, error: 'chatMetadata contains unsupported values' };
    if (bytes(metadata) > LIMITS.maxMetadataBytes) return { ok: false, error: 'chatMetadata too large' };
    return { ok: true };
}

function validateGenerationId(value, max = 160) {
    return safeId(String(value ?? ''), max);
}

function ensureMessageIds(snapshot) {
    const out = clone(Array.isArray(snapshot) ? snapshot : []);
    const used = new Set();
    for (const message of out) {
        if (!isObject(message)) continue;
        if (!isObject(message.extra)) message.extra = {};
        if (!isObject(message.extra.multi_client_sync)) message.extra.multi_client_sync = {};
        let id = getMessageId(message);
        if (!safeId(id, 128) || used.has(id)) {
            id = randomId('m_');
            message.extra.multi_client_sync.messageId = id;
        }
        used.add(id);
    }
    return out;
}

function normalizeScope(req, raw) {
    const userId = userIdFromRequest(req);
    if (!userId) throw new Error('Authentication required');
    if (!isObject(raw)) throw new Error('scope must be an object');

    const kind = raw.kind === 'group' ? 'group' : raw.kind === 'character' ? 'character' : null;
    if (!kind) throw new Error('scope.kind must be character or group');

    const chatId = String(raw.chatId ?? '').trim();
    if (!safeName(chatId)) throw new Error('invalid chatId');

    const branchId = raw.branchId ? String(raw.branchId).trim() : '';
    if (branchId && !safeId(branchId, 128)) throw new Error('invalid branchId');

    const parentChatId = raw.parentChatId ? String(raw.parentChatId).trim() : '';
    if (parentChatId && !safeName(parentChatId)) throw new Error('invalid parentChatId');

    if (kind === 'character') {
        const character = String(raw.character ?? '').trim();
        if (!safeName(character)) throw new Error('invalid character');
        return { userId, kind, character, chatId, branchId, parentChatId };
    }

    const groupId = String(raw.groupId ?? '').trim();
    if (!safeId(groupId, 256)) throw new Error('invalid groupId');
    return { userId, kind, groupId, chatId, branchId, parentChatId };
}

function scopeKey(scope) {
    return JSON.stringify([
        scope.userId,
        scope.kind,
        scope.kind === 'character' ? scope.character : scope.groupId,
        scope.chatId,
        scope.branchId || 'main',
    ]);
}

function scopeHash(scope) {
    return sha256(scopeKey(scope)).slice(0, 40);
}

function storageFile(req, scope) {
    return safeJoin(stateRootFromRequest(req), `${scopeHash(scope)}.json`);
}

async function ensureStateRoot(req) {
    const root = stateRootFromRequest(req);
    await fsp.mkdir(root, { recursive: true, mode: 0o700 });
    return root;
}

function emptyState(scope) {
    return {
        protocol: PROTOCOL,
        schema: SCHEMA,
        scope: clone(scope),
        revision: 0,
        epoch: randomId('e_'),
        snapshot: [],
        chatMetadata: {},
        tombstones: [],
        events: [],
        recentOps: [],
        generation: null,
        groupSettings: null,
        branches: [],
        createdAt: now(),
        updatedAt: now(),
        hostSnapshotDigest: null,
    };
}

async function loadJson(file) {
    try { return JSON.parse(await fsp.readFile(file, 'utf8')); } catch { return null; }
}

async function atomicWrite(file, value) {
    const content = JSON.stringify(value);
    if (Buffer.byteLength(content, 'utf8') > LIMITS.maxPersistedStateBytes) throw new Error('Persisted synchronization state is too large');
    await fsp.mkdir(path.dirname(file), { recursive: true, mode: 0o700 });
    const temp = `${file}.${process.pid}.${randomId('tmp_')}.tmp`;
    try {
        await fsp.writeFile(temp, content, { encoding: 'utf8', mode: 0o600 });
        await fsp.rename(temp, file);
    } finally {
        await fsp.rm(temp, { force: true }).catch(() => {});
    }
}

function ensureGenerationShape(state) {
    const generation = state?.generation;
    if (generation === null || generation === undefined) return;
    if (!isObject(generation)
        || !safeId(String(generation.id || ''), 160)
        || !safeId(String(generation.ownerClientId || ''), 128)
        || !safeId(String(generation.ownerDeviceId || ''), 128)
        || !safeId(String(generation.generationType || ''), 64)
        || !['claimed', 'started', 'streaming', 'completed', 'stopped', 'failed'].includes(String(generation.phase))
        || !Number.isFinite(Number(generation.startedAt))
        || !Number.isFinite(Number(generation.leaseUntil))
    ) {
        state.generation = null;
        return;
    }
    if (!Array.isArray(generation.streamMessages)) generation.streamMessages = [];
    if (!Number.isInteger(generation.streamSeq) || generation.streamSeq < 0) generation.streamSeq = 0;
    if (generation.messageId !== null && generation.messageId !== undefined && !safeId(String(generation.messageId), 128)) generation.messageId = null;
    generation.stopRequested = !!generation.stopRequested;
    const validEntries = [];
    for (const entry of generation.streamMessages) {
        if (!isObject(entry) || !safeId(String(entry.messageId || ''), 128) || !isObject(entry.message)) continue;
        if (!validateSnapshot([entry.message]).ok) continue;
        const normalized = ensureMessageIds([entry.message])[0];
        const messageId = getMessageId(normalized);
        if (!messageId || messageId !== String(entry.messageId)) continue;
        validEntries.push({ messageId, message: normalized });
    }
    generation.streamMessages = validEntries;
    const totalBytes = () => Buffer.byteLength(JSON.stringify(generation), 'utf8');
    while (generation.streamMessages.length > LIMITS.maxLiveGenerationMessages || totalBytes() > LIMITS.maxLiveGenerationBytes) {
        if (generation.streamMessages.length <= 1) break;
        generation.streamMessages.shift();
    }
    const last = generation.streamMessages.at(-1);
    generation.streamMessage = last ? clone(last.message) : null;
    if (!generation.messageId && last) generation.messageId = last.messageId;
}

function expireGeneration(state) {
    ensureGenerationShape(state);
    if (!state.generation) return null;
    if (state.generation.leaseUntil < now() || state.generation.startedAt + LIMITS.generationMaxMs < now()) {
        const previous = clone(state.generation);
        state.generation = null;
        state.updatedAt = now();
        return previous;
    }
    return null;
}

function pruneState(state) {
    if (!Array.isArray(state.events)) state.events = [];
    if (state.events.length > LIMITS.maxEvents) state.events.splice(0, state.events.length - LIMITS.maxEvents);
    if (!Array.isArray(state.tombstones)) state.tombstones = [];
    if (state.tombstones.length > LIMITS.maxTombstones) state.tombstones.splice(0, state.tombstones.length - LIMITS.maxTombstones);
    if (!Array.isArray(state.recentOps)) state.recentOps = [];
    if (state.recentOps.length > LIMITS.maxRecentOps) state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
    if (!Array.isArray(state.snapshot)) state.snapshot = [];
    if (!isObject(state.chatMetadata)) state.chatMetadata = {};
    if (!Array.isArray(state.branches)) state.branches = [];
    if (state.branches.length > LIMITS.maxBranches) state.branches.splice(0, state.branches.length - LIMITS.maxBranches);
    if (!Number.isInteger(state.revision) || state.revision < 0) state.revision = 0;
    if (!state.epoch) state.epoch = randomId('e_');

    ensureGenerationShape(state);

    while (state.events.length > 1 && bytes(state) > Math.floor(LIMITS.maxPersistedStateBytes * 0.88)) state.events.shift();
}

function stateIdentityValid(state, scope) {
    return isObject(state)
        && state.protocol === PROTOCOL
        && state.schema === SCHEMA
        && isObject(state.scope)
        && scopeKey(state.scope) === scopeKey(scope);
}

async function loadState(req, scope) {
    const key = scopeKey(scope);
    const cached = scopes.get(key);
    if (cached) return cached;
    const pending = stateLoads.get(key);
    if (pending) return pending;
    if (scopes.size >= LIMITS.maxScopesPerProcess) evictMemoryScopes();

    const promise = (async () => {
        await ensureStateRoot(req);
        const file = storageFile(req, scope);
        stateFiles.set(key, file);
        let state = await loadJson(file);
        if (!stateIdentityValid(state, scope)) state = emptyState(scope);
        if (!validateSnapshot(state.snapshot).ok || !validateMetadata(state.chatMetadata).ok) state = emptyState(scope);
        state.scope = clone(scope);
        pruneState(state);
        scopes.set(key, state);
        return state;
    })();
    stateLoads.set(key, promise);
    try {
        return await promise;
    } finally {
        if (stateLoads.get(key) === promise) stateLoads.delete(key);
    }
}

function activeScopeCountForUser(userId) {
    const cutoff = now() - LIMITS.memberTtlMs;
    let count = 0;
    for (const [key, map] of members) {
        for (const [clientId, member] of map) if (member.lastSeen < cutoff) map.delete(clientId);
        if (!map.size) {
            members.delete(key);
            continue;
        }
        const member = map.values().next().value;
        if (member?.userId === userId) count++;
    }
    return count;
}


function withUserLock(userId, callback) {
    const previous = userOperationChains.get(userId) || Promise.resolve();
    const next = previous.catch(() => {}).then(callback);
    const tracked = next.finally(() => {
        if (userOperationChains.get(userId) === tracked) userOperationChains.delete(userId);
    });
    tracked.catch(() => {});
    userOperationChains.set(userId, tracked);
    return next;
}

function withScopeLock(scope, callback) {
    const key = scopeKey(scope);
    const previous = operationChains.get(key) || Promise.resolve();
    const next = previous.catch(() => {}).then(callback);
    const tracked = next.finally(() => {
        if (operationChains.get(key) === tracked) operationChains.delete(key);
    });
    tracked.catch(() => {});
    operationChains.set(key, tracked);
    return next;
}

function persistState(req, scope, state) {
    const key = scopeKey(scope);
    const userKey = scope.userId;
    const previousScope = persistenceChains.get(key) || Promise.resolve();
    const previousUser = userPersistenceChains.get(userKey) || Promise.resolve();
    const snapshot = clone(state);
    pruneState(snapshot);

    const next = Promise.all([previousScope, previousUser])
        .catch(() => {})
        .then(async () => {
            const root = await ensureStateRoot(req);
            const file = stateFiles.get(key) || storageFile(req, scope);
            stateFiles.set(key, file);
            const currentBytes = await calculateUserStateBytes(req);
            const existing = await fsp.stat(file).catch(() => null);
            const content = JSON.stringify(snapshot);
            const size = Buffer.byteLength(content, 'utf8');
            const projected = Math.max(0, currentBytes - Number(existing?.size || 0)) + size;
            if (projected > LIMITS.maxPersistedBytesPerUser) throw new Error('Synchronization storage quota exceeded');
            await atomicWrite(file, snapshot);
            return root;
        });

    const trackedScope = next.finally(() => {
        if (persistenceChains.get(key) === trackedScope) persistenceChains.delete(key);
    });
    const trackedUser = trackedScope.finally(() => {
        if (userPersistenceChains.get(userKey) === trackedUser) userPersistenceChains.delete(userKey);
    });
    trackedScope.catch(() => {});
    trackedUser.catch(() => {});
    persistenceChains.set(key, trackedScope);
    userPersistenceChains.set(userKey, trackedUser);
    return trackedUser;
}


async function calculateUserStateBytes(req) {
    const root = await ensureStateRoot(req);
    let total = 0;
    try {
        const entries = await fsp.readdir(root, { withFileTypes: true });
        for (const entry of entries) {
            if (!entry.isFile() || !entry.name.endsWith('.json')) continue;
            const stat = await fsp.stat(path.join(root, entry.name)).catch(() => null);
            total += Number(stat?.size || 0);
            if (total > LIMITS.maxPersistedBytesPerUser) break;
        }
    } catch {}
    return total;
}

function evictMemoryScopes() {
    const candidates = [...scopes.entries()]
        .filter(([key, state]) => !members.has(key) && !state.generation)
        .sort((a, b) => (a[1].updatedAt || 0) - (b[1].updatedAt || 0));
    while (scopes.size >= LIMITS.maxScopesPerProcess && candidates.length) scopes.delete(candidates.shift()[0]);
}

async function cleanupUserState(req) {
    let root;
    try { root = await ensureStateRoot(req); } catch { return; }
    let entries;
    try { entries = await fsp.readdir(root, { withFileTypes: true }); } catch { return; }
    const cutoff = now() - LIMITS.staleStateMs;
    for (const entry of entries) {
        const file = path.join(root, entry.name);
        if (entry.isFile() && entry.name.endsWith('.tmp')) {
            const stat = await fsp.stat(file).catch(() => null);
            if (stat && stat.mtimeMs < now() - LIMITS.staleTempMs) await fsp.rm(file, { force: true }).catch(() => {});
            continue;
        }
        if (!entry.isFile() || !entry.name.endsWith('.json')) continue;
        const stat = await fsp.stat(file).catch(() => null);
        if (!stat || stat.mtimeMs >= cutoff) continue;
        const state = await loadJson(file);
        const key = state?.scope ? scopeKey(state.scope) : null;
        if (key && members.has(key)) continue;
        await fsp.rm(file, { force: true }).catch(() => {});
    }
}

function membersForScope(scope) {
    const key = scopeKey(scope);
    const map = members.get(key);
    if (!map) return [];
    const cutoff = now() - LIMITS.memberTtlMs;
    for (const [clientId, member] of map) if (member.lastSeen < cutoff) map.delete(clientId);
    return [...map.values()];
}

function touchMember(scope, body) {
    const clientId = String(body.clientId ?? '');
    const deviceId = String(body.deviceId ?? '');
    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) throw new Error('Invalid clientId/deviceId');
    const key = scopeKey(scope);
    let map = members.get(key);
    if (!map) { map = new Map(); members.set(key, map); }
    map.set(clientId, {
        userId: scope.userId,
        clientId,
        deviceId,
        connectedAt: map.get(clientId)?.connectedAt || now(),
        lastSeen: now(),
    });
    return { clientId, deviceId };
}

function isMember(scope, clientId, deviceId) {
    const member = members.get(scopeKey(scope))?.get(clientId);
    return !!member && member.deviceId === deviceId && member.lastSeen >= now() - LIMITS.memberTtlMs;
}

function requireCurrentMember(scope, clientId, deviceId) {
    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) return false;
    const member = members.get(scopeKey(scope))?.get(clientId);
    if (!member || member.deviceId !== deviceId || member.lastSeen < now() - LIMITS.memberTtlMs) return false;
    member.lastSeen = now();
    return true;
}

function rateAllowed(scope, clientId) {
    const key = JSON.stringify([scope.userId, clientId]);
    const current = rateWindows.get(key);
    if (!current || current.expiresAt <= now()) {
        rateWindows.set(key, { count: 1, expiresAt: now() + 60_000 });
        return true;
    }
    current.count++;
    return current.count <= LIMITS.maxEventsPerClientPerMinute;
}

function countUserSse(userId) {
    let count = 0;
    for (const subscription of subscriptions.values()) if (subscription.userId === userId && subscription.res) count++;
    return count;
}

function serializePublicState(state, { includeSnapshot = true, includeGenerationStream = true } = {}) {
    const generation = clone(state.generation);
    if (generation && !includeGenerationStream) {
        generation.streamMessage = null;
        generation.streamMessages = [];
    }
    const result = {
        protocol: PROTOCOL,
        schema: SCHEMA,
        scope: clone(state.scope),
        revision: state.revision,
        epoch: state.epoch,
        generation,
        updatedAt: state.updatedAt,
    };

    // Live generation events are high-frequency. Do not retransmit the full
    // durable chat, tombstones, branch list, and group definition on every token.
    // Clients retain the durable state locally and the next full state/resync
    // remains authoritative.
    if (includeSnapshot) {
        result.snapshot = clone(state.snapshot);
        result.chatMetadata = clone(state.chatMetadata);
        result.tombstones = clone(state.tombstones);
        result.groupSettings = clone(state.groupSettings);
        result.branches = clone(state.branches);
    }
    return result;
}

function findCachedOperation(state, opId) {
    if (!safeId(opId, 160)) return null;
    return state.recentOps.find(item => item.opId === opId) || null;
}

function rememberOperation(state, opId, result, type) {
    state.recentOps.push({
        opId,
        type,
        eventId: Number(result?.eventId || result?.event?.id || 0),
        revision: Number(result?.revision ?? state.revision),
        epoch: result?.epoch || state.epoch,
        accepted: result?.ok !== false,
        generationId: result?.generation?.id || result?.event?.generationId || null,
        storedAt: now(),
    });
    if (state.recentOps.length > LIMITS.maxRecentOps) state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
}

function cachedResultResponse(state, cached) {
    const liveOnly = String(cached.type || '').startsWith('generation_')
        && !['generation_terminal', 'generation_recover'].includes(cached.type);
    const publicState = serializePublicState(state, { includeSnapshot: !liveOnly, includeGenerationStream: !liveOnly });
    return {
        ok: true,
        deduped: true,
        revision: cached.revision,
        epoch: cached.epoch,
        eventId: cached.eventId,
        state: publicState,
        generation: clone(state.generation),
    };
}

function recordEvent(state, event) {
    const id = Number(state.events.at(-1)?.id || 0) + 1;
    let stored = { ...clone(event), id, revision: state.revision, epoch: state.epoch, ts: now() };
    if (bytes(stored) > LIMITS.maxEventBytes) {
        stored.compacted = true;
        delete stored.snapshot;
        delete stored.patch;
        delete stored.message;
        delete stored.groupSettings;
        if (stored.generation) {
            stored.generation = { ...stored.generation, streamMessage: null, streamMessages: [] };
        }
    }
    state.events.push(stored);
    if (state.events.length > LIMITS.maxEvents) state.events.splice(0, state.events.length - LIMITS.maxEvents);
    state.updatedAt = now();
    return stored;
}

function writeSse(res, event, data, id = null) {
    if (id !== null) res.write(`id: ${id}\n`);
    res.write(`event: ${event}\n`);
    res.write(`data: ${JSON.stringify(data)}\n\n`);
}

function closeSubscription(token) {
    const subscription = subscriptions.get(token);
    if (!subscription) return;
    subscriptions.delete(token);
    if (subscription.res) {
        totalSseConnections = Math.max(0, totalSseConnections - 1);
        try { subscription.res.end(); } catch {}
    }
    subscription.res = null;
}

function publish(scope, eventType, payload, eventId) {
    const key = scopeKey(scope);
    for (const [token, subscription] of subscriptions) {
        if (subscription.scopeKey !== key || !subscription.res) continue;
        try { writeSse(subscription.res, eventType, payload, eventId); } catch { closeSubscription(token); }
    }
}

function chatFilePath(req, scope) {
    if (scope.kind === 'character') {
        const chatsRoot = req.user?.directories?.chats;
        if (!chatsRoot) return null;
        const avatar = scope.character.replace(/\.png$/i, '');
        return safeJoin(safeJoin(chatsRoot, avatar), `${scope.chatId}.jsonl`);
    }
    const groupChatsRoot = req.user?.directories?.groupChats;
    if (!groupChatsRoot) return null;
    return safeJoin(groupChatsRoot, `${scope.chatId}.jsonl`);
}

async function validateCharacterScope(req, scope) {
    const root = req.user?.directories?.chats;
    if (!root) return false;
    const avatar = scope.character.replace(/\.png$/i, '');
    if (!safeName(avatar)) return false;
    const dir = safeJoin(root, avatar);
    return fs.existsSync(dir);
}

async function loadGroupDefinition(req, groupId) {
    const groupsRoot = req.user?.directories?.groups;
    if (!groupsRoot) return null;
    return loadJson(safeJoin(groupsRoot, `${groupId}.json`));
}

async function validateGroupScope(req, scope) {
    const group = await loadGroupDefinition(req, scope.groupId);
    if (!group) return { ok: false, code: 'group_not_found', message: 'The requested group does not exist.' };
    if (!Array.isArray(group.members)) return { ok: false, code: 'group_invalid', message: 'The group definition is invalid.' };
    if (!Array.isArray(group.chats) || !group.chats.includes(scope.chatId)) return { ok: false, code: 'group_chat_not_found', message: 'The requested group chat does not belong to this group.' };
    return { ok: true, group };
}

async function validateScopeAgainstHost(req, scope) {
    if (scope.kind === 'character') {
        if (!(await validateCharacterScope(req, scope))) {
            return { ok: false, code: 'character_not_found', message: 'The character scope could not be resolved.' };
        }
    } else {
        const result = await validateGroupScope(req, scope);
        if (!result.ok) return result;
    }
    const file = chatFilePath(req, scope);
    if (!file) return { ok: false, code: 'chat_path_unavailable', message: 'The chat path could not be resolved.' };
    return { ok: true, file };
}

function projectSnapshotForDigest(snapshot, mode = 'full') {
    if (mode !== 'relevant') return clone(snapshot || []);
    const out = clone(snapshot || []);
    const messageFields = ['swipes', 'swipe_info', 'swipe_id'];
    const extraFields = ['reasoning', 'reasoning_duration', 'reasoning_signature', 'reasoning_display_text', 'tool_invocations'];
    for (const message of out) {
        if (!isObject(message)) continue;
        if (isObject(message.extra)) delete message.extra.multi_client_sync;
        for (const key of messageFields) delete message[key];
        if (isObject(message.extra)) for (const key of extraFields) delete message.extra[key];
    }
    return out;
}

function snapshotDigestForMode(snapshot, mode = 'full') {
    return sha256(stableJson(projectSnapshotForDigest(snapshot, mode)));
}

async function readHostChat(req, scope) {
    const validation = await validateScopeAgainstHost(req, scope);
    if (!validation.ok) return { ok: false, exists: false, hash: null, snapshotDigest: null, relevantSnapshotDigest: null, snapshot: [], metadata: {}, error: validation.code };
    const file = validation.file;
    if (!fs.existsSync(file)) return { ok: true, exists: false, hash: null, snapshotDigest: sha256('[]'), relevantSnapshotDigest: sha256('[]'), snapshot: [], metadata: {} };

    let raw;
    try { raw = await fsp.readFile(file, 'utf8'); } catch {
        return { ok: false, exists: true, hash: null, snapshotDigest: null, relevantSnapshotDigest: null, snapshot: [], metadata: {}, error: 'chat_read_failed' };
    }
    const hash = sha256(raw);
    const lines = raw.split(/\r?\n/).filter(line => line.trim());
    const parsed = [];
    for (const line of lines) {
        try { parsed.push(JSON.parse(line)); } catch {
            return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot: [], metadata: {}, error: 'chat_file_corrupt' };
        }
    }
    if (!parsed.length) return { ok: true, exists: true, hash, snapshotDigest: sha256('[]'), relevantSnapshotDigest: sha256('[]'), snapshot: [], metadata: {} };

    const header = isObject(parsed[0]) ? parsed[0] : {};
    const snapshot = parsed.slice(1);
    const snapshotCheck = validateSnapshot(snapshot);
    if (!snapshotCheck.ok) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot: [], metadata: {}, error: snapshotCheck.error };

    const metadata = isObject(header.chat_metadata) ? clone(header.chat_metadata) : {};
    const metadataCheck = validateMetadata(metadata);
    if (!metadataCheck.ok) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot: [], metadata: {}, error: metadataCheck.error };

    if (scope.branchId) {
        if (!metadata.integrity) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot, metadata, error: 'branch_integrity_missing' };
        if (String(metadata.integrity) !== String(scope.branchId)) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot, metadata, error: 'branch_integrity_mismatch' };
    }
    if (scope.parentChatId) {
        if (!metadata.main_chat) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot, metadata, error: 'branch_parent_missing' };
        if (String(metadata.main_chat) !== String(scope.parentChatId)) return { ok: false, exists: true, hash, snapshotDigest: null, relevantSnapshotDigest: null, snapshot, metadata, error: 'branch_parent_mismatch' };
    }

    const normalized = ensureMessageIds(snapshot);
    return {
        ok: true,
        exists: true,
        hash,
        snapshotDigest: sha256(stableJson(normalized)),
        relevantSnapshotDigest: snapshotDigestForMode(normalized, 'relevant'),
        snapshot: normalized,
        metadata,
    };
}

const UNSYNCED_MESSAGE_FIELDS = Object.freeze(['swipes', 'swipe_info', 'swipe_id']);
const UNSYNCED_EXTRA_FIELDS = Object.freeze(['reasoning', 'reasoning_duration', 'reasoning_signature', 'reasoning_display_text', 'tool_invocations']);

function applySyncPolicy(snapshot, previousSnapshot, syncSwipes = true) {
    const next = ensureMessageIds(snapshot || []);
    if (syncSwipes !== false) return next;
    const previousMap = new Map((Array.isArray(previousSnapshot) ? previousSnapshot : []).map(message => [getMessageId(message), message]));
    return next.map(message => {
        const output = clone(message);
        const previous = previousMap.get(getMessageId(message));
        for (const key of UNSYNCED_MESSAGE_FIELDS) {
            if (previous && Object.prototype.hasOwnProperty.call(previous, key)) output[key] = clone(previous[key]);
            else delete output[key];
        }
        if (!isObject(output.extra)) output.extra = {};
        for (const key of UNSYNCED_EXTRA_FIELDS) {
            if (previous?.extra && Object.prototype.hasOwnProperty.call(previous.extra, key)) output.extra[key] = clone(previous.extra[key]);
            else delete output.extra[key];
        }
        return output;
    });
}

function snapshotEquivalentForPolicy(a, b, syncSwipes = true) {
    return stableJson(projectSnapshotForDigest(a || [], syncSwipes === false ? 'relevant' : 'full'))
        === stableJson(projectSnapshotForDigest(b || [], syncSwipes === false ? 'relevant' : 'full'));
}

function currentGeneration(state) {
    expireGeneration(state);
    return state.generation || null;
}

function recoverExpiredGenerationEvent(state, source = {}, reason = 'expired') {
    const previousGeneration = expireGeneration(state);
    if (!previousGeneration) return null;
    return recordEvent(state, {
        type: 'generation_recover',
        source: {
            clientId: String(source.clientId || 'server'),
            deviceId: String(source.deviceId || 'server'),
        },
        previousGeneration,
        automatic: true,
        reason,
    });
}

function isGenerationOwner(state, body) {
    const generation = state.generation;
    return !!generation
        && generation.ownerClientId === body.clientId
        && generation.ownerDeviceId === body.deviceId;
}

function revisionCheck(state, body) {
    const baseRevision = Number(body.baseRevision);
    if (!Number.isInteger(baseRevision) || baseRevision < 0) return { ok: false, code: 'invalid_revision', message: 'baseRevision must be a non-negative integer.' };
    if (baseRevision !== state.revision) return { ok: false, code: 'revision_conflict', message: 'The synchronization revision has advanced.', currentRevision: state.revision };
    return { ok: true };
}

function hostDigestCheck(host, body) {
    if (body.hostSnapshotDigest === undefined) return { ok: true };
    if (!host.ok) return { ok: false, code: 'stale_host', message: 'The SillyTavern chat could not be verified.', currentDigest: host.snapshotDigest, hostError: host.error || null };
    const mode = body.hostSnapshotDigestMode === 'relevant' ? 'relevant' : 'full';
    const currentDigest = mode === 'relevant' ? host.relevantSnapshotDigest : host.snapshotDigest;
    if (currentDigest !== String(body.hostSnapshotDigest)) return { ok: false, code: 'stale_host', message: 'The local SillyTavern chat changed since this operation was created.', currentDigest };
    return { ok: true };
}

async function restoreAfterPersistFailure(req, scope, state) {
    const persisted = await loadJson(storageFile(req, scope));
    if (stateIdentityValid(persisted, scope)) {
        Object.keys(state).forEach(key => delete state[key]);
        Object.assign(state, clone(persisted));
        pruneState(state);
        return;
    }
    Object.assign(state, emptyState(scope));
}

function diffSnapshot(before, after) {
    const left = Array.isArray(before) ? before : [];
    const right = Array.isArray(after) ? after : [];
    let prefix = 0;
    while (prefix < left.length && prefix < right.length && JSON.stringify(left[prefix]) === JSON.stringify(right[prefix])) prefix++;
    let suffix = 0;
    while (suffix < left.length - prefix && suffix < right.length - prefix && JSON.stringify(left[left.length - 1 - suffix]) === JSON.stringify(right[right.length - 1 - suffix])) suffix++;
    const beforeEnd = left.length - suffix;
    const afterEnd = right.length - suffix;
    return {
        kind: prefix === left.length && right.length >= left.length ? 'insert' : prefix === right.length && left.length >= right.length ? 'delete' : 'replace',
        start: prefix,
        deleteCount: beforeEnd - prefix,
        messages: clone(right.slice(prefix, afterEnd)),
    };
}

function computeTombstones(before, after, revision) {
    const afterIds = new Set(after.map(getMessageId).filter(Boolean));
    const tombstones = [];
    for (const message of before) {
        const id = getMessageId(message);
        if (id && !afterIds.has(id)) tombstones.push({ messageId: id, revision, deletedAt: now() });
    }
    return tombstones;
}

function groupSettingsSnapshot(group) {
    const allowedKeys = [
        'name', 'members', 'disabled_members', 'chats',
        'generation_mode', 'generation_mode_join_prefix', 'generation_mode_join_suffix',
        'activation_strategy', 'auto_mode_delay', 'allow_self_responses',
        'avatar_url', 'hideMutedSprites', 'fav',
    ];
    const result = {};
    for (const key of allowedKeys) if (group?.[key] !== undefined) result[key] = clone(group[key]);
    return result;
}

async function handleJoin(req, res) {
    if (requestBodyTooLarge(req)) return sendError(res, 413, 'request_too_large', 'Request is too large.');
    const userId = userIdFromRequest(req);
    if (!userId) return sendError(res, 401, 'unauthenticated', 'SillyTavern authentication is required.');
    let scope;
    try { scope = normalizeScope(req, req.body?.scope); } catch (error) { return sendError(res, 400, 'invalid_scope', error.message); }
    if (Number(req.body?.protocol) !== PROTOCOL || Number(req.body?.schema) !== SCHEMA) return sendError(res, 409, 'protocol_mismatch', 'Synchronization protocol/schema mismatch.', { expectedProtocol: PROTOCOL, expectedSchema: SCHEMA });
    const requestedClientId = String(req.body?.clientId || ''), requestedDeviceId = String(req.body?.deviceId || '');
    if (!safeId(requestedClientId, 128) || !safeId(requestedDeviceId, 128)) return sendError(res, 400, 'invalid_client', 'clientId and deviceId are required.');
    const scopeValidation = await validateScopeAgainstHost(req, scope);
    if (!scopeValidation.ok && scopeValidation.code !== 'character_not_found') return sendError(res, scopeValidation.code === 'group_not_found' ? 404 : 400, scopeValidation.code, scopeValidation.message);

    let ids;
    try {
        ids = await withUserLock(userId, async () => {
            const key = scopeKey(scope);
            const existingMap = members.get(key);
            const existingMember = existingMap?.get(requestedClientId);
            if ((!existingMap || !existingMember) && activeScopeCountForUser(userId) >= LIMITS.maxScopesPerUser) {
                const error = new Error('Too many active synchronization scopes for this user.');
                error.code = 'scope_limit';
                throw error;
            }
            return touchMember(scope, req.body || {});
        });
    } catch (error) {
        return sendError(res, error.code === 'scope_limit' ? 429 : 400, error.code || 'invalid_client', error.message);
    }

    let resultState;
    let bootstrapped = false;
    let host;
    let subscriptionToken;

    try {
        await withScopeLock(scope, async () => {
            const state = await loadState(req, scope);
            const beforeGeneration = !!state.generation;
            host = await readHostChat(req, scope);
            const recoveryEvent = recoverExpiredGenerationEvent(state, ids, 'expired_on_join');
            let changed = !!recoveryEvent;
            if (scope.kind === 'group' && state.groupSettings === null) {
                const definition = await loadGroupDefinition(req, scope.groupId);
                if (definition) { state.groupSettings = groupSettingsSnapshot(definition); changed = true; }
            }

            if (state.revision === 0 && state.snapshot.length === 0 && host.ok && host.exists) {
                const normalized = ensureMessageIds(host.snapshot);
                state.snapshot = normalized;
                state.chatMetadata = clone(host.metadata);
                state.hostSnapshotDigest = snapshotDigestForMode(normalized, 'full');
                state.revision = 1;
                const event = recordEvent(state, {
                    type: 'bootstrap',
                    source: { clientId: ids.clientId, deviceId: ids.deviceId },
                    patch: { kind: 'replace', start: 0, deleteCount: 0, messages: clone(normalized) },
                    stateDigest: sha256(stableJson(normalized)),
                });
                bootstrapped = true;
                changed = true;
            }

            if (!beforeGeneration && state.generation) currentGeneration(state);
            if (changed) await persistState(req, scope, state);
            if (recoveryEvent) publish(scope, 'sync', { epoch: state.epoch, event: clone(recoveryEvent), state: serializePublicState(state) }, recoveryEvent.id);
            if (bootstrapped) {
                const bootstrapEvent = state.events.at(-1);
                if (bootstrapEvent?.type === 'bootstrap') publish(scope, 'sync', { epoch: state.epoch, event: clone(bootstrapEvent), state: serializePublicState(state) }, bootstrapEvent.id);
            }
            resultState = clone(state);
            subscriptionToken = randomId('sse_');
        });
    } catch (error) {
        if (error.code === 'scope_limit') return sendError(res, 429, error.code, error.message);
        return sendError(res, 507, 'persistence_failed', 'Synchronization state could not be initialized.');
    }

    for (const [oldToken, subscription] of subscriptions) {
        if (subscription.userId === userId && subscription.clientId === ids.clientId && subscription.deviceId === ids.deviceId) closeSubscription(oldToken);
    }
    subscriptions.set(subscriptionToken, { token: subscriptionToken, userId, clientId: ids.clientId, deviceId: ids.deviceId, scope: clone(scope), scopeKey: scopeKey(scope), createdAt: now(), res: null });

    await cleanupUserState(req);
    return res.json({
        ok: true,
        protocol: PROTOCOL,
        schema: SCHEMA,
        userId,
        scope: clone(scope),
        state: serializePublicState(resultState),
        serverNow: now(),
        membership: ids,
        subscriptionToken,
        bootstrap: bootstrapped,
        host: { exists: host?.exists || false, ok: host?.ok !== false, hash: host?.hash || null, snapshotDigest: host?.snapshotDigest || null, relevantSnapshotDigest: host?.relevantSnapshotDigest || null, error: host?.error || null },
        capabilities: {
            sse: true, revisions: true, durableQueue: true, idempotency: true,
            generationLease: true, generationStream: true, resumableGenerationPreview: true,
            branches: true, checkpoints: true, swipes: true, reasoning: true,
            toolInvocations: true, attachments: 'server-resident-reference', exactTokenReplay: false,
        },
    });
}

async function handleLeave(req, res) {
    let scope;
    try { scope = normalizeScope(req, req.body?.scope); } catch (error) { return sendError(res, 400, 'invalid_scope', error.message); }
    if (Number(req.body?.protocol) !== PROTOCOL || Number(req.body?.schema) !== SCHEMA) return sendError(res, 409, 'protocol_mismatch', 'Synchronization protocol/schema mismatch.');
    const clientId = String(req.body?.clientId || ''), deviceId = String(req.body?.deviceId || '');
    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) return sendError(res, 400, 'invalid_client', 'clientId and deviceId are required.');
    return withScopeLock(scope, async () => {
        const member = members.get(scopeKey(scope))?.get(clientId);
        if (member && member.deviceId === deviceId) members.get(scopeKey(scope))?.delete(clientId);
        for (const [token, subscription] of subscriptions) if (subscription.scopeKey === scopeKey(scope) && subscription.clientId === clientId && subscription.deviceId === deviceId) closeSubscription(token);
        return res.json({ ok: true, clientId, deviceId });
    });
}

async function handleHeartbeat(req, res) {
    let scope;
    try { scope = normalizeScope(req, req.body?.scope); } catch (error) { return sendError(res, 400, 'invalid_scope', error.message); }
    if (Number(req.body?.protocol) !== PROTOCOL || Number(req.body?.schema) !== SCHEMA) return sendError(res, 409, 'protocol_mismatch', 'Synchronization protocol/schema mismatch.');
    const clientId = String(req.body?.clientId || ''), deviceId = String(req.body?.deviceId || '');
    if (!requireCurrentMember(scope, clientId, deviceId)) return sendError(res, 403, 'not_member', 'Client is not a current member of this scope.');

    return withScopeLock(scope, async () => {
        const state = await loadState(req, scope);
        const recoveryEvent = recoverExpiredGenerationEvent(state, { clientId: 'server', deviceId: 'server' }, 'expired_on_heartbeat');
        if (recoveryEvent) {
            try {
                await persistState(req, scope, state);
                publish(scope, 'sync', { epoch: state.epoch, event: recoveryEvent, state: serializePublicState(state) }, recoveryEvent.id);
            } catch (error) {
                await restoreAfterPersistFailure(req, scope, state);
                return sendError(res, 507, 'persistence_failed', 'Synchronization state could not be recovered.');
            }
        }

        let renewed = false;
        if (isGenerationOwner(state, req.body || {}) && state.generation) {
            state.generation.leaseUntil = now() + LIMITS.generationLeaseMs;
            state.updatedAt = now();
            renewed = true;
            try { await persistState(req, scope, state); } catch (error) {
                await restoreAfterPersistFailure(req, scope, state);
                return sendError(res, 507, 'persistence_failed', 'Synchronization state could not be durably persisted.');
            }
        }
        return res.json({ ok: true, membership: { clientId, deviceId }, renewed, revision: state.revision, epoch: state.epoch, generation: clone(state.generation) });
    });
}

async function stateResponse(req, res) {
    const raw = req.method === 'GET' ? req.query : req.body;
    let scope;
    try { scope = normalizeScope(req, raw?.scope); } catch (error) { return sendError(res, 400, 'invalid_scope', error.message); }
    if (Number(raw?.protocol) !== PROTOCOL || Number(raw?.schema) !== SCHEMA) return sendError(res, 409, 'protocol_mismatch', 'Synchronization protocol/schema mismatch.', { expectedProtocol: PROTOCOL, expectedSchema: SCHEMA });
    const clientId = String(raw?.clientId || '');
    const deviceId = String(raw?.deviceId || '');
    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) return sendError(res, 400, 'invalid_client', 'clientId and deviceId are required.');
    if (!isMember(scope, clientId, deviceId)) return sendError(res, 403, 'not_member', 'Client is not a current member of this scope.');

    return withScopeLock(scope, async () => {
        const state = await loadState(req, scope);
        const recoveryEvent = recoverExpiredGenerationEvent(state, { clientId: 'server', deviceId: 'server' }, 'expired_on_state');
        if (recoveryEvent) {
            await persistState(req, scope, state).catch(() => {});
            publish(scope, 'sync', { epoch: state.epoch, event: clone(recoveryEvent), state: serializePublicState(state) }, recoveryEvent.id);
        }
        const host = await readHostChat(req, scope);
        return res.json({
            ok: true,
            protocol: PROTOCOL,
            schema: SCHEMA,
            state: serializePublicState(state),
            host: { ok: host.ok, exists: host.exists, hash: host.hash, snapshotDigest: host.snapshotDigest, relevantSnapshotDigest: host.relevantSnapshotDigest || null, error: host.error || null },
            cursor: { epoch: state.epoch, revision: state.revision, lastEventId: Number(state.events.at(-1)?.id || 0) },
        });
    });
}

async function handleSse(req, res) {
    const token = String(req.query?.token || '');
    const subscription = subscriptions.get(token);
    const userId = userIdFromRequest(req);
    if (!subscription || subscription.userId !== userId) return res.status(401).end('invalid subscription');
    if (!isMember(subscription.scope, subscription.clientId, subscription.deviceId)) return res.status(409).end('membership expired');
    if (totalSseConnections >= LIMITS.maxSseTotal) return res.status(503).end('SSE capacity reached');
    if (countUserSse(userId) >= LIMITS.maxSsePerUser && !subscription.res) return res.status(503).end('Per-user SSE capacity reached');

    if (subscription.res) {
        try { subscription.res.end(); } catch {}
        subscription.res = null;
        totalSseConnections = Math.max(0, totalSseConnections - 1);
    }

    totalSseConnections++;
    subscription.res = res;
    res.status(200).set({
        'Content-Type': 'text/event-stream',
        'Cache-Control': 'no-cache, no-transform',
        Connection: 'keep-alive',
        'X-Accel-Buffering': 'no',
    });
    res.flushHeaders?.();

    const state = await loadState(req, subscription.scope);
    const recoveryEvent = recoverExpiredGenerationEvent(state, { clientId: 'server', deviceId: 'server' }, 'expired_on_sse');
    if (recoveryEvent) {
        await persistState(req, subscription.scope, state).catch(() => {});
        publish(subscription.scope, 'sync', { epoch: state.epoch, event: clone(recoveryEvent), state: serializePublicState(state) }, recoveryEvent.id);
    }
    const lastEventId = Number.parseInt(req.get('Last-Event-ID') || req.query?.lastEventId || '0', 10) || 0;

    writeSse(res, 'hello', {
        protocol: PROTOCOL,
        schema: SCHEMA,
        epoch: state.epoch,
        revision: state.revision,
        eventId: Number(state.events.at(-1)?.id || 0),
        generation: clone(state.generation),
    });

    const oldest = Number(state.events[0]?.id || 0);
    if (lastEventId && oldest && lastEventId < oldest - 1) {
        writeSse(res, 'resync_required', { epoch: state.epoch, revision: state.revision, eventId: oldest, reason: 'replay_window_exhausted' });
    } else if (lastEventId) {
        for (const event of state.events) {
            if (Number(event.id) <= lastEventId) continue;
            writeSse(res, 'replay', { epoch: state.epoch, event: clone(event) }, event.id);
        }
    }

    writeSse(res, 'replay_complete', {
        epoch: state.epoch,
        revision: state.revision,
        eventId: Number(state.events.at(-1)?.id || 0),
    });

    const keepalive = setInterval(() => {
        if (res.writableEnded) {
            clearInterval(keepalive);
            return;
        }
        try { res.write(`: keepalive ${now()}\n\n`); } catch { clearInterval(keepalive); }
    }, 15_000);

    const close = () => {
        clearInterval(keepalive);
        if (subscription.res !== res) return;
        subscription.res = null;
        totalSseConnections = Math.max(0, totalSseConnections - 1);
    };
    req.on('close', close);
}

async function processSnapshotMutation(req, scope, state, body) {
    const revision = revisionCheck(state, body);
    if (!revision.ok) return { status: 409, payload: { ok: false, error: revision, generation: clone(state.generation) } };

    const host = await readHostChat(req, scope);
    const hostCheck = hostDigestCheck(host, body);
    if (!hostCheck.ok) return { status: 409, payload: { ok: false, error: hostCheck, generation: clone(state.generation) } };

    const validation = validateSnapshot(body.snapshot);
    if (!validation.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_snapshot', message: validation.error } } };

    const metadata = body.chatMetadata === undefined ? clone(state.chatMetadata) : clone(body.chatMetadata);
    const metadataCheck = validateMetadata(metadata);
    if (!metadataCheck.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_metadata', message: metadataCheck.error } } };

    if (scope.branchId && String(metadata.integrity || '') !== String(scope.branchId)) return { status: 400, payload: { ok: false, error: { code: metadata.integrity ? 'branch_integrity_mismatch' : 'branch_integrity_missing', message: metadata.integrity ? 'Branch integrity does not match this synchronized branch.' : 'Branch integrity metadata is required for this synchronized branch.' } } };
    if (scope.parentChatId && String(metadata.main_chat || '') !== String(scope.parentChatId)) return { status: 400, payload: { ok: false, error: { code: metadata.main_chat ? 'branch_parent_mismatch' : 'branch_parent_missing', message: metadata.main_chat ? 'Branch parent does not match this synchronized scope.' : 'Branch parent metadata is required for this synchronized branch.' } } };

    const next = applySyncPolicy(body.snapshot, state.snapshot, body.syncSwipes !== false);
    const previous = clone(state.snapshot);
    const snapshotChanged = !snapshotEquivalentForPolicy(previous, next, body.syncSwipes !== false);
    const metadataChanged = stableJson(state.chatMetadata || {}) !== stableJson(metadata);
    if (!snapshotChanged && !metadataChanged) return { status: 200, event: null, unchanged: true };
    state.revision++;
    state.snapshot = next;
    state.chatMetadata = metadata;
    state.hostSnapshotDigest = snapshotDigestForMode(next, 'full');
    state.tombstones.push(...computeTombstones(previous, next, state.revision));
    const event = recordEvent(state, {
        type: body.type,
        opId: body.opId,
        source: { clientId: body.clientId, deviceId: body.deviceId },
        patch: diffSnapshot(previous, next),
        stateDigest: sha256(stableJson(next)),
    });
    return { status: 200, event };
}

async function processMetadataMutation(req, scope, state, body) {
    const revision = revisionCheck(state, body);
    if (!revision.ok) return { status: 409, payload: { ok: false, error: revision } };
    const metadata = clone(body.chatMetadata);
    const check = validateMetadata(metadata);
    if (!check.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_metadata', message: check.error } } };

    if (scope.branchId && String(metadata.integrity || '') !== String(scope.branchId)) return { status: 400, payload: { ok: false, error: { code: metadata.integrity ? 'branch_integrity_mismatch' : 'branch_integrity_missing', message: metadata.integrity ? 'Branch integrity does not match this synchronized branch.' : 'Branch integrity metadata is required for this synchronized branch.' } } };
    if (scope.parentChatId && String(metadata.main_chat || '') !== String(scope.parentChatId)) return { status: 400, payload: { ok: false, error: { code: metadata.main_chat ? 'branch_parent_mismatch' : 'branch_parent_missing', message: metadata.main_chat ? 'Branch parent does not match this synchronized scope.' : 'Branch parent metadata is required for this synchronized branch.' } } };

    const previous = clone(state.chatMetadata);
    if (stableJson(previous || {}) === stableJson(metadata)) return { status: 200, event: null, unchanged: true };
    state.revision++;
    state.chatMetadata = metadata;
    const event = recordEvent(state, {
        type: 'metadata',
        opId: body.opId,
        source: { clientId: body.clientId, deviceId: body.deviceId },
        chatMetadata: clone(metadata),
        previousMetadataDigest: sha256(stableJson(previous)),
    });
    return { status: 200, event };
}

async function processGroupSettings(scope, state, body) {
    if (scope.kind !== 'group') return { status: 400, payload: { ok: false, error: { code: 'not_group', message: 'group_settings requires a group scope.' } } };
    const revision = revisionCheck(state, body);
    if (!revision.ok) return { status: 409, payload: { ok: false, error: revision } };
    if (!isObject(body.groupSettings) || !validateDataTree(body.groupSettings) || bytes(body.groupSettings) > LIMITS.maxGroupSettingsBytes) {
        return { status: 400, payload: { ok: false, error: { code: 'invalid_group_settings', message: 'groupSettings is invalid or too large.' } } };
    }
    const allowed = ['name', 'members', 'disabled_members', 'chats', 'generation_mode', 'generation_mode_join_prefix', 'generation_mode_join_suffix', 'activation_strategy', 'auto_mode_delay', 'allow_self_responses', 'avatar_url', 'hideMutedSprites', 'fav'];
    const sanitized = {};
    for (const key of allowed) if (Object.prototype.hasOwnProperty.call(body.groupSettings, key)) sanitized[key] = clone(body.groupSettings[key]);
    if (JSON.stringify(sanitized) === JSON.stringify(state.groupSettings || {})) return { status: 200, event: null, unchanged: true };
    state.revision++;
    state.groupSettings = sanitized;
    const event = recordEvent(state, {
        type: 'group_settings',
        opId: body.opId,
        source: { clientId: body.clientId, deviceId: body.deviceId },
        groupSettings: clone(sanitized),
    });
    return { status: 200, event };
}

async function processBranchAnnouncement(req, parentScope, parentState, body) {
    const revision = revisionCheck(parentState, body);
    if (!revision.ok) return { status: 409, payload: { ok: false, error: revision } };

    let childScope;
    try { childScope = normalizeScope(req, body.childScope); } catch (error) {
        return { status: 400, payload: { ok: false, error: { code: 'invalid_child_scope', message: error.message } } };
    }

    if (childScope.kind !== parentScope.kind) return { status: 400, payload: { ok: false, error: { code: 'branch_scope_mismatch', message: 'Parent and child scopes must have the same kind.' } } };
    if (parentScope.kind === 'character' && childScope.character !== parentScope.character) return { status: 400, payload: { ok: false, error: { code: 'branch_character_mismatch', message: 'Branch must belong to the same character.' } } };
    if (parentScope.kind === 'group' && childScope.groupId !== parentScope.groupId) return { status: 400, payload: { ok: false, error: { code: 'branch_group_mismatch', message: 'Branch must belong to the same group.' } } };
    if (!childScope.branchId) return { status: 400, payload: { ok: false, error: { code: 'branch_integrity_required', message: 'The child branch/checkpoint must provide its native integrity ID.' } } };

    const branchKind = body.branchKind === 'checkpoint' ? 'checkpoint' : 'branch';
    const expectedMainChat = branchKind === 'checkpoint'
        ? (parentScope.parentChatId || parentScope.chatId)
        : parentScope.chatId;
    if (childScope.parentChatId !== expectedMainChat) return { status: 400, payload: { ok: false, error: { code: 'branch_parent_mismatch', message: 'Child chat does not point to the expected native parent/main chat.' } } };

    const host = await readHostChat(req, childScope);
    if (!host.ok || !host.exists) return { status: 409, payload: { ok: false, error: { code: 'branch_host_missing', message: 'The newly-created branch/checkpoint chat is not yet available on the server.' } } };
    if (host.metadata?.main_chat && String(host.metadata.main_chat) !== String(expectedMainChat)) return { status: 400, payload: { ok: false, error: { code: 'branch_host_parent_mismatch', message: 'The native branch metadata points to a different parent.' } } };
    if (host.metadata?.integrity && String(host.metadata.integrity) !== String(childScope.branchId)) return { status: 400, payload: { ok: false, error: { code: 'branch_host_integrity_mismatch', message: 'The supplied branch ID does not match the native chat integrity.' } } };

    const childState = await loadState(req, childScope);
    if (childState.revision === 0) {
        childState.snapshot = ensureMessageIds(host.snapshot);
        childState.chatMetadata = clone(host.metadata);
        childState.revision = 1;
        childState.hostSnapshotDigest = snapshotDigestForMode(childState.snapshot, 'full');
        const childEvent = recordEvent(childState, {
            type: 'branch_bootstrap',
            source: { clientId: body.clientId, deviceId: body.deviceId },
            parentScope: clone(parentScope),
            branchKind,
        });
        try { await persistState(req, childScope, childState); } catch (error) {
            await restoreAfterPersistFailure(req, childScope, childState);
            return { status: 507, payload: { ok: false, error: { code: 'persistence_failed', message: 'Branch state could not be durably persisted.' } } };
        }
        publish(childScope, 'sync', { epoch: childState.epoch, event: childEvent, state: serializePublicState(childState) }, childEvent.id);
    }

    const duplicateBranch = parentState.branches.some(branch =>
        branch.childChatId === childScope.chatId && branch.branchId === childScope.branchId,
    );
    if (duplicateBranch) return { status: 200, event: null, childScope, childState: serializePublicState(childState), unchanged: true };

    parentState.revision++;
    const record = {
        childScope: clone(childScope),
        parentChatId: parentScope.chatId,
        childChatId: childScope.chatId,
        branchId: childScope.branchId,
        branchKind,
        nativeMainChat: childScope.parentChatId,
        createdAt: now(),
    };
    parentState.branches = parentState.branches.filter(branch => !(branch.childChatId === record.childChatId && branch.branchId === record.branchId));
    parentState.branches.push(record);
    if (parentState.branches.length > LIMITS.maxBranches) parentState.branches.splice(0, parentState.branches.length - LIMITS.maxBranches);
    const event = recordEvent(parentState, {
        type: 'branch_announce',
        opId: body.opId,
        source: { clientId: body.clientId, deviceId: body.deviceId },
        branch: clone(record),
    });
    return { status: 200, event, childScope, childState: serializePublicState(childState) };
}


async function processGenerationEvent(req, scope, state, body) {
    const expiredGeneration = expireGeneration(state);

    if (body.type === 'generation_claim') {
        if (state.generation) {
            return { status: 409, payload: { ok: false, error: { code: 'generation_busy', message: 'Another synchronized client currently owns generation.', currentGeneration: clone(state.generation) } } };
        }
        const generationId = body.generationId && validateGenerationId(body.generationId) ? String(body.generationId) : randomId('g_');
        const generationType = String(body.generationType || 'normal').slice(0, 64);
        if (!safeId(generationType, 64) || generationType === 'quiet') return { status: 400, payload: { ok: false, error: { code: 'invalid_generation_type', message: 'generationType is invalid for synchronized generation.' } } };
        if (generationType === 'group' && scope.kind !== 'group') return { status: 400, payload: { ok: false, error: { code: 'invalid_generation_type', message: 'Group generation requires a group scope.' } } };
        const requestedMessageId = body.messageId ? String(body.messageId) : null;
        if (requestedMessageId && !safeId(requestedMessageId, 128)) return { status: 400, payload: { ok: false, error: { code: 'invalid_message_id', message: 'messageId is invalid.' } } };
        state.generation = {
            id: generationId,
            ownerClientId: body.clientId,
            ownerDeviceId: body.deviceId,
            generationType,
            phase: 'claimed',
            startedAt: now(),
            leaseUntil: now() + LIMITS.generationLeaseMs,
            streamSeq: 0,
            messageId: requestedMessageId,
            streamMessage: null,
            streamMessages: [],
            stopRequested: false,
        };
        const event = recordEvent(state, { type: 'generation_claim', opId: body.opId, source: { clientId: body.clientId, deviceId: body.deviceId }, generation: clone(state.generation), ...(expiredGeneration ? { recoveredGeneration: expiredGeneration } : {}) });
        return { status: 200, event };
    }

    if (!state.generation) return { status: 409, payload: { ok: false, error: { code: 'no_generation', message: 'There is no active synchronized generation.' } } };
    if (String(body.generationId || '') !== state.generation.id) return { status: 409, payload: { ok: false, error: { code: 'generation_mismatch', message: 'The supplied generation ID does not match the active generation.' } } };

    if (body.type === 'generation_heartbeat') {
        if (!isGenerationOwner(state, body)) return { status: 403, payload: { ok: false, error: { code: 'not_generation_owner', message: 'Only the current generation owner can renew generation.' } } };
        state.generation.leaseUntil = now() + LIMITS.generationLeaseMs;
        state.updatedAt = now();
        ensureGenerationShape(state);
        return { status: 200, event: null };
    }

    if (body.type === 'generation_started') {
        if (!isGenerationOwner(state, body)) return { status: 403, payload: { ok: false, error: { code: 'not_generation_owner', message: 'Only the generation owner can acknowledge generation start.' } } };
        if (!['claimed', 'started', 'streaming'].includes(state.generation.phase)) return { status: 409, payload: { ok: false, error: { code: 'generation_invalid_phase', message: 'Generation is not in a startable phase.' } } };
        const messageId = body.messageId === undefined || body.messageId === null || body.messageId === '' ? null : String(body.messageId);
        if (messageId && !safeId(messageId, 128)) return { status: 400, payload: { ok: false, error: { code: 'invalid_message_id', message: 'messageId is invalid.' } } };
        state.generation.phase = 'started';
        state.generation.leaseUntil = now() + LIMITS.generationLeaseMs;
        if (messageId) state.generation.messageId = messageId;
        const event = recordEvent(state, { type: 'generation_started', opId: body.opId, source: { clientId: body.clientId, deviceId: body.deviceId }, generation: clone(state.generation) });
        return { status: 200, event };
    }

    if (body.type === 'generation_stream') {
        if (!isGenerationOwner(state, body)) return { status: 403, payload: { ok: false, error: { code: 'not_generation_owner', message: 'Only the generation owner can stream generation updates.' } } };
        if (!['started', 'streaming'].includes(state.generation.phase)) return { status: 409, payload: { ok: false, error: { code: 'generation_not_started', message: 'Generation has not started.' } } };
        const streamSeq = Number(body.streamSeq);
        if (!Number.isInteger(streamSeq) || streamSeq !== Number(state.generation.streamSeq || 0) + 1) return { status: 409, payload: { ok: false, error: { code: 'stream_sequence_gap', message: 'Stream sequence must advance contiguously.', expected: Number(state.generation.streamSeq || 0) + 1 } } };
        if (!isObject(body.message)) return { status: 400, payload: { ok: false, error: { code: 'invalid_stream_message', message: 'A streamed generation message is required.' } } };
        const validation = validateSnapshot([body.message]);
        if (!validation.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_stream_message', message: validation.error } } };
        if (bytes(body.message) > LIMITS.maxLiveGenerationBytes) return { status: 413, payload: { ok: false, error: { code: 'generation_stream_message_too_large', message: 'The streamed generation message is too large.' } } };
        const message = applySyncPolicy([body.message], state.generation.streamMessages.map(entry => entry.message), body.syncSwipes !== false)[0];
        const messageId = getMessageId(message);
        if (!messageId) return { status: 400, payload: { ok: false, error: { code: 'invalid_stream_message_id', message: 'Stream message has no valid synchronization ID.' } } };
        if (body.messageId !== undefined && String(body.messageId) !== String(messageId)) {
            return { status: 400, payload: { ok: false, error: { code: 'stream_message_id_mismatch', message: 'messageId does not match the streamed message.' } } };
        }
        if (state.generation.generationType !== 'group' && state.generation.messageId && state.generation.messageId !== messageId) {
            return { status: 409, payload: { ok: false, error: { code: 'generation_message_mismatch', message: 'A single-message generation cannot stream a different message ID.' } } };
        }

        state.generation.messageId ||= messageId;
        state.generation.streamSeq = streamSeq;
        state.generation.phase = 'streaming';
        state.generation.leaseUntil = now() + LIMITS.generationLeaseMs;
        const entries = Array.isArray(state.generation.streamMessages) ? state.generation.streamMessages : [];
        const index = entries.findIndex(entry => entry.messageId === messageId);
        const replacement = { messageId, message: clone(message) };
        if (index >= 0) entries[index] = replacement;
        else entries.push(replacement);
        state.generation.streamMessages = entries;
        ensureGenerationShape(state);
        const event = recordEvent(state, {
            type: 'generation_stream',
            opId: body.opId,
            source: { clientId: body.clientId, deviceId: body.deviceId },
            generationId: state.generation.id,
            streamSeq,
            messageId,
            message: clone(message),
        });
        return { status: 200, event };
    }

    if (body.type === 'generation_stop_request') {
        state.generation.stopRequested = true;
        const event = recordEvent(state, { type: 'generation_stop_request', opId: body.opId, source: { clientId: body.clientId, deviceId: body.deviceId }, generationId: state.generation.id, reason: String(body.reason || 'remote_stop').slice(0, 256) });
        return { status: 200, event };
    }

    if (body.type === 'generation_terminal') {
        if (!isGenerationOwner(state, body)) return { status: 403, payload: { ok: false, error: { code: 'not_generation_owner', message: 'Only the generation owner can finalize generation.' } } };
        const status = ['completed', 'stopped', 'failed'].includes(body.status) ? body.status : 'failed';
        if (body.snapshot === undefined) return { status: 400, payload: { ok: false, error: { code: 'final_snapshot_required', message: 'A final chat snapshot is required when generation terminates.' } } };
        const validation = validateSnapshot(body.snapshot);
        if (!validation.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_snapshot', message: validation.error } } };
        const metadata = body.chatMetadata === undefined ? clone(state.chatMetadata) : clone(body.chatMetadata);
        const metadataCheck = validateMetadata(metadata);
        if (!metadataCheck.ok) return { status: 400, payload: { ok: false, error: { code: 'invalid_metadata', message: metadataCheck.error } } };
        if (scope.branchId && metadata.integrity && String(metadata.integrity) !== String(scope.branchId)) return { status: 400, payload: { ok: false, error: { code: 'branch_integrity_mismatch', message: 'Branch integrity does not match this synchronized branch.' } } };
        if (scope.parentChatId && metadata.main_chat && String(metadata.main_chat) !== String(scope.parentChatId)) return { status: 400, payload: { ok: false, error: { code: 'branch_parent_mismatch', message: 'Branch parent does not match this synchronized scope.' } } };

        const host = await readHostChat(req, scope);
        const hostCheck = hostDigestCheck(host, body);
        if (!hostCheck.ok) return { status: 409, payload: { ok: false, error: hostCheck } };

        const previous = clone(state.snapshot);
        const next = applySyncPolicy(body.snapshot, state.snapshot, body.syncSwipes !== false);
        const snapshotChanged = JSON.stringify(previous) !== JSON.stringify(next);
        const metadataChanged = JSON.stringify(state.chatMetadata || {}) !== JSON.stringify(metadata);
        if (snapshotChanged || metadataChanged) {
            state.revision++;
            state.snapshot = next;
            state.chatMetadata = metadata;
            state.hostSnapshotDigest = snapshotDigestForMode(next, 'full');
            state.tombstones.push(...computeTombstones(previous, next, state.revision));
        }

        const finalGeneration = clone(state.generation);
        finalGeneration.phase = status;
        finalGeneration.leaseUntil = now();
        ensureGenerationShape({ generation: finalGeneration });
        const event = recordEvent(state, {
            type: 'generation_terminal',
            opId: body.opId,
            source: { clientId: body.clientId, deviceId: body.deviceId },
            generationId: finalGeneration.id,
            generation: finalGeneration,
            status,
            snapshot: clone(state.snapshot),
            chatMetadata: clone(state.chatMetadata),
        });
        state.generation = null;
        return { status: 200, event };
    }

    if (body.type === 'generation_recover') {
        if (state.generation) return { status: 409, payload: { ok: false, error: { code: 'generation_not_expired', message: 'Generation has not expired yet.' } } };
        const event = recordEvent(state, { type: 'generation_recover', opId: body.opId, source: { clientId: body.clientId, deviceId: body.deviceId }, previousGeneration: expiredGeneration });
        return { status: 200, event, recovered: !!expiredGeneration };
    }

    return { status: 400, payload: { ok: false, error: { code: 'invalid_generation_event', message: 'Unsupported generation event type.' } } };
}

async function handleEvent(req, res) {
    if (requestBodyTooLarge(req)) return sendError(res, 413, 'request_too_large', 'Request is too large.');
    let scope;
    try { scope = normalizeScope(req, req.body?.scope); } catch (error) { return sendError(res, 400, 'invalid_scope', error.message); }

    const body = req.body || {};
    if (Number(body.protocol) !== PROTOCOL || Number(body.schema) !== SCHEMA) return sendError(res, 409, 'protocol_mismatch', 'Synchronization protocol/schema mismatch.', { expectedProtocol: PROTOCOL, expectedSchema: SCHEMA });
    if (!ALL_EVENT_TYPES.has(body.type)) return sendError(res, 400, 'invalid_event_type', 'Unsupported synchronization event type.');

    const clientId = String(body.clientId || '');
    const deviceId = String(body.deviceId || '');
    const opId = String(body.opId || '');
    if (!safeId(clientId, 128) || !safeId(deviceId, 128) || !safeId(opId, 160)) return sendError(res, 400, 'invalid_client', 'clientId, deviceId, and opId are required.');
    if (!isMember(scope, clientId, deviceId)) return sendError(res, 403, 'not_member', 'Client is not an active member of this scope.');
    if (!rateAllowed(scope, clientId)) return sendError(res, 429, 'rate_limited', 'Too many synchronization operations.');

    return withScopeLock(scope, async () => {
        const state = await loadState(req, scope);
        const cached = findCachedOperation(state, opId);
        if (cached) return res.json(cachedResultResponse(state, cached));

        if (state.generation && ['snapshot', 'metadata', 'reconcile_local', 'group_settings', 'branch_announce'].includes(body.type)) {
            return res.status(409).json({
                ok: false,
                error: {
                    code: 'generation_active',
                    message: 'The synchronized chat is currently generating; ordinary chat mutations must wait for generation to finish.',
                },
                generation: clone(state.generation),
            });
        }

        let result;
        try {
            if (GENERATION_TYPES.has(body.type)) result = await processGenerationEvent(req, scope, state, body);
            else if (body.type === 'metadata') result = await processMetadataMutation(req, scope, state, body);
            else if (body.type === 'group_settings') result = await processGroupSettings(scope, state, body);
            else if (body.type === 'branch_announce') result = await processBranchAnnouncement(req, scope, state, body);
            else result = await processSnapshotMutation(req, scope, state, body);
        } catch (error) {
            return sendError(res, 500, 'internal_error', 'Synchronization operation failed.');
        }

        if (result.payload) return res.status(result.status).json(result.payload);

        state.updatedAt = now();
        rememberOperation(state, opId, { ok: true, eventId: result.event?.id || 0, revision: state.revision, epoch: state.epoch, generation: state.generation }, body.type);
        try { await persistState(req, scope, state); } catch (error) {
            await restoreAfterPersistFailure(req, scope, state);
            return sendError(res, 507, 'persistence_failed', 'Synchronization state could not be durably persisted.');
        }

        const publicState = serializePublicState(state);
        if (result.event) {
            const liveOnly = String(result.event.type || '').startsWith('generation_') && !['generation_terminal', 'generation_recover'].includes(result.event.type);
            publish(scope, 'sync', { epoch: state.epoch, event: clone(result.event), state: serializePublicState(state, { includeSnapshot: !liveOnly, includeGenerationStream: !liveOnly }) }, result.event.id);
        }
        const responseLiveOnly = String(body.type || '').startsWith('generation_')
            && !['generation_terminal', 'generation_recover'].includes(body.type);
        const responseState = responseLiveOnly
            ? serializePublicState(state, { includeSnapshot: false, includeGenerationStream: false })
            : publicState;
        return res.json({
            ok: true,
            protocol: PROTOCOL,
            schema: SCHEMA,
            revision: state.revision,
            epoch: state.epoch,
            eventId: result.event?.id || 0,
            event: clone(result.event),
            generation: clone(state.generation),
            state: responseState,
            ...(result.childScope ? { childScope: clone(result.childScope), childState: clone(result.childState) } : {}),
        });
    });
}

async function handleHealth(req, res) {
    const userId = userIdFromRequest(req);
    if (!userId) return sendError(res, 401, 'unauthenticated', 'SillyTavern authentication is required.');
    return res.json({ ok: true, plugin: info.id, version: '1.6.0', protocol: PROTOCOL, schema: SCHEMA, userId, node: process.version, storage: true, scopes: scopes.size, sse: totalSseConnections, shuttingDown });
}

async function init(router) {
    shuttingDown = false;
    cleanupTimer = setInterval(async () => {
        for (const [key, map] of members) {
            const cutoff = now() - LIMITS.memberTtlMs;
            for (const [clientId, member] of map) if (member.lastSeen < cutoff) map.delete(clientId);
            if (!map.size) members.delete(key);
        }
        const cutoff = now();
        for (const [key, window] of rateWindows) if (window.expiresAt <= cutoff) rateWindows.delete(key);
        await Promise.resolve();
    }, 10 * 60_000);
    cleanupTimer.unref?.();

    router.get('/health', handleHealth);
    router.post('/join', handleJoin);
    router.post('/leave', handleLeave);
    router.post('/heartbeat', handleHeartbeat);
    router.get('/state', stateResponse);
    router.post('/state', stateResponse);
    router.get('/events', handleSse);
    router.post('/event', handleEvent);

    console.log(`[multi-client-sync] loaded protocol=${PROTOCOL} schema=${SCHEMA}`);
}

async function exit() {
    shuttingDown = true;
    if (cleanupTimer) clearInterval(cleanupTimer);

    for (const [token, subscription] of subscriptions) {
        if (subscription.res) {
            try { writeSse(subscription.res, 'shutdown', { reason: 'server_shutdown' }); } catch {}
        }
        closeSubscription(token);
    }

    const pending = [];
    for (const state of scopes.values()) {
        const key = scopeKey(state.scope);
        const file = stateFiles.get(key);
        if (!file) continue;
        const snapshot = clone(state);
        pruneState(snapshot);
        pending.push((async () => {
            const content = JSON.stringify(snapshot);
            if (Buffer.byteLength(content, 'utf8') > LIMITS.maxPersistedStateBytes) return;
            await atomicWrite(file, snapshot);
        })().catch(() => {}));
    }
    await Promise.allSettled(pending);
    userOperationChains.clear();
    operationChains.clear();
    persistenceChains.clear();
    userPersistenceChains.clear();
    stateLoads.clear();
    stateFiles.clear();
    scopes.clear();
    members.clear();
    subscriptions.clear();
    rateWindows.clear();
    totalSseConnections = 0;
}

module.exports = { init, exit, info };

