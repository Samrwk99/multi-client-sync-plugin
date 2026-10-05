'use strict';

const fs = require('node:fs');
const fsp = fs.promises;
const path = require('node:path');
const crypto = require('node:crypto');

const PROTOCOL = 9;
const SCHEMA = 9;

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
    maxEventsPerUserPerMinute: 4_000,

    memberTtlMs: 45_000,
    generationLeaseMs: 15_000,
    generationMaxMs: 30 * 60_000,

    staleTempMs: 10 * 60_000,
    staleStateMs: 30 * 24 * 60 * 60_000,
});

const FORBIDDEN_KEYS = new Set(['__proto__', 'prototype', 'constructor']);
const MUTATION_TYPES = new Set(['snapshot', 'metadata', 'message_delete', 'reconcile_local', 'group_settings', 'branch_announce', 'chat_renamed', 'chat_deleted', 'group_chat_deleted']);
const GENERATION_TYPES = new Set([
    'generation_claim',
    'generation_heartbeat',
    'generation_started',
    'generation_input',
    'generation_stream',
    'generation_stop_request',
    'generation_terminal',
    'generation_terminal_recover',
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
const userRateWindows = new Map();
const stateFiles = new Map();
const stateLoads = new Map();

let totalSseConnections = 0;
let shuttingDown = false;
let cleanupTimer = null;
const LIVE_GENERATION_PERSIST_INTERVAL_MS = 1_000;
let serverInstanceId = '';

const now = () => Date.now();
const clone = value => structuredClone(value);
const randomId = (prefix = '') => `${prefix}${crypto.randomBytes(18).toString('hex')}`;
const sha256 = value => crypto.createHash('sha256').update(String(value)).digest('hex');

function canonicalize(value, seen = new WeakSet()) {
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return value;
    if (typeof value === 'number') {
        if (!Number.isFinite(value)) throw new Error('Non-finite number is not JSON-compatible');
        return value;
    }
    if (typeof value !== 'object') throw new Error('Unsupported non-JSON value');
    if (seen.has(value)) throw new Error('Cyclic value is not JSON-compatible');
    seen.add(value);
    try {
        if (Array.isArray(value)) return value.map(item => canonicalize(item, seen));
        const out = {};
        for (const key of Object.keys(value).sort()) {
            if (FORBIDDEN_KEYS.has(key)) throw new Error(`Forbidden object key: ${key}`);
            out[key] = canonicalize(value[key], seen);
        }
        return out;
    } finally {
        seen.delete(value);
    }
}

const canonicalJson = value => JSON.stringify(canonicalize(value));
const stableJson = canonicalJson;
const bytes = value => Buffer.byteLength(stableJson(value), 'utf8');

serverInstanceId = randomId('srv_');

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
    try {
        return bytes(req.body ?? {}) > LIMITS.maxRequestBytes;
    } catch {
        return true;
    }
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

function hasCompleteMessageIds(snapshot) {
    return Array.isArray(snapshot) && snapshot.every(message => safeId(getMessageId(message), 128));
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
    return canonicalJson([
        scope.userId,
        scope.kind,
        scope.kind === 'character' ? scope.character : scope.groupId,
        scope.chatId,
        scope.branchId || '',
        scope.parentChatId || '',
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
        recoverableGeneration: null,
        pendingGenerationRecovery: null,
        serverInstanceId,
        groupSettings: null,
        branches: [],
        createdAt: now(),
        updatedAt: now(),
        hostSnapshotDigest: null,
        hostMetadataDigest: sha256(canonicalJson({})),
        renamedTo: null,
        deleted: false,
    };
}

async function loadJsonDetailed(file) {
    try {
        const raw = await fsp.readFile(file, 'utf8');
        return { exists: true, ok: true, value: JSON.parse(raw) };
    } catch (error) {
        if (error?.code === 'ENOENT') return { exists: false, ok: false, value: null, error };
        return { exists: true, ok: false, value: null, error };
    }
}

async function loadJson(file) {
    const result = await loadJsonDetailed(file);
    return result.ok ? result.value : null;
}

async function quarantineStateFile(file) {
    try {
        const stamp = new Date().toISOString().replace(/[:.]/g, '-');
        const target = `${file}.corrupt.${stamp}`;
        await fsp.rename(file, target);
        return target;
    } catch {
        return null;
    }
}

async function atomicWrite(file, value) {
    const content = JSON.stringify(value);
    if (Buffer.byteLength(content, 'utf8') > LIMITS.maxPersistedStateBytes) {
        throw new Error('Persisted synchronization state is too large');
    }

    await fsp.mkdir(path.dirname(file), { recursive: true, mode: 0o700 });

    const temp = `${file}.${process.pid}.${randomId('tmp_')}.tmp`;

    try {
        await fsp.writeFile(temp, content, {
            encoding: 'utf8',
            mode: 0o600,
        });
        await fsp.rename(temp, file);
    } finally {
        await fsp.rm(temp, { force: true }).catch(() => {});
    }
}

function ensureGenerationShape(state) {
    const generation = state?.generation;
    if (generation === null || generation === undefined) return;

    if (
        !isObject(generation)
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

    if (
        generation.messageId !== null
        && generation.messageId !== undefined
        && !safeId(String(generation.messageId), 128)
    ) {
        generation.messageId = null;
    }

    generation.stopRequested = !!generation.stopRequested;
    generation.serverInstanceId = String(generation.serverInstanceId || serverInstanceId);
    generation.lastPersistedStreamSeq = Number.isInteger(generation.lastPersistedStreamSeq)
        ? generation.lastPersistedStreamSeq
        : 0;
    generation.lastPersistedAt = Number.isFinite(Number(generation.lastPersistedAt))
        ? Number(generation.lastPersistedAt)
        : 0;

    const validEntries = [];

    for (const entry of generation.streamMessages) {
        if (
            !isObject(entry)
            || !safeId(String(entry.messageId || ''), 128)
            || !isObject(entry.message)
        ) {
            continue;
        }

        if (!validateSnapshot([entry.message]).ok) continue;

        const normalized = ensureMessageIds([entry.message])[0];
        const messageId = getMessageId(normalized);

        if (!messageId || messageId !== String(entry.messageId)) continue;

        validEntries.push({
            messageId,
            message: normalized,
        });
    }

    generation.streamMessages = validEntries;

    const totalBytes = () => Buffer.byteLength(JSON.stringify(generation), 'utf8');

    while (
        generation.streamMessages.length > LIMITS.maxLiveGenerationMessages
        || totalBytes() > LIMITS.maxLiveGenerationBytes
    ) {
        if (generation.streamMessages.length <= 1) break;
        generation.streamMessages.shift();
    }

    const last = generation.streamMessages.at(-1);
    generation.streamMessage = last ? clone(last.message) : null;

    if (!generation.messageId && last) {
        generation.messageId = last.messageId;
    }
}

function expireGeneration(state) {
    ensureGenerationShape(state);

    if (!state.generation) return null;

    if (
        state.generation.leaseUntil < now()
        || state.generation.startedAt + LIMITS.generationMaxMs < now()
    ) {
        const previous = clone(state.generation);

        state.recoverableGeneration = {
            generation: clone(previous),
            expiredAt: now(),
            reason: 'lease_expired',
            serverInstanceId,
        };

        state.pendingGenerationRecovery = {
            reason: 'lease_expired',
            previousGeneration: clone(previous),
        };

        state.generation = null;
        state.updatedAt = now();

        return previous;
    }

    return null;
}

function pruneState(state) {
    if (!Array.isArray(state.events)) state.events = [];
    if (state.events.length > LIMITS.maxEvents) {
        state.events.splice(0, state.events.length - LIMITS.maxEvents);
    }

    if (!Array.isArray(state.tombstones)) state.tombstones = [];
    if (state.tombstones.length > LIMITS.maxTombstones) {
        state.tombstones.splice(0, state.tombstones.length - LIMITS.maxTombstones);
    }

    if (!Array.isArray(state.recentOps)) state.recentOps = [];
    if (state.recentOps.length > LIMITS.maxRecentOps) {
        state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
    }

    if (!Array.isArray(state.snapshot)) state.snapshot = [];
    if (!isObject(state.chatMetadata)) state.chatMetadata = {};

    if (!Array.isArray(state.branches)) state.branches = [];
    if (state.branches.length > LIMITS.maxBranches) {
        state.branches.splice(0, state.branches.length - LIMITS.maxBranches);
    }

    if (
        state.recoverableGeneration !== null
        && state.recoverableGeneration !== undefined
        && !isObject(state.recoverableGeneration)
    ) {
        state.recoverableGeneration = null;
    }

    if (
        state.pendingGenerationRecovery !== null
        && state.pendingGenerationRecovery !== undefined
        && !isObject(state.pendingGenerationRecovery)
    ) {
        state.pendingGenerationRecovery = null;
    }

    if (!state.serverInstanceId) state.serverInstanceId = serverInstanceId;
    if (!Number.isInteger(state.revision) || state.revision < 0) state.revision = 0;
    if (!state.epoch) state.epoch = randomId('e_');

    if (state.hostMetadataDigest == null) {
        state.hostMetadataDigest = sha256(canonicalJson(state.chatMetadata || {}));
    }

    if (state.renamedTo !== null && state.renamedTo !== undefined && !isObject(state.renamedTo)) {
        state.renamedTo = null;
    }

    state.deleted = !!state.deleted;

    ensureGenerationShape(state);

    while (
        state.events.length > 1
        && bytes(state) > Math.floor(LIMITS.maxPersistedStateBytes * 0.88)
    ) {
        state.events.shift();
    }
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

        const read = await loadJsonDetailed(file);

        let state;

        if (!read.exists) {
            state = emptyState(scope);
        } else if (!read.ok || !stateIdentityValid(read.value, scope)) {
            if (read.ok) {
                state = emptyState(scope);
            } else {
                await quarantineStateFile(file);
                state = emptyState(scope);
            }
        } else {
            state = read.value;

            if (
                !validateSnapshot(state.snapshot).ok
                || !validateMetadata(state.chatMetadata).ok
            ) {
                await quarantineStateFile(file);
                state = emptyState(scope);
            }
        }

        if (
            state.generation
            && state.serverInstanceId
            && state.serverInstanceId !== serverInstanceId
        ) {
            state.recoverableGeneration = {
                generation: clone(state.generation),
                expiredAt: now(),
                reason: 'server_restart',
                serverInstanceId: state.serverInstanceId,
            };

            state.pendingGenerationRecovery = {
                reason: 'server_restart',
                previousGeneration: clone(state.generation),
            };

            state.generation = null;
        } else if (state.generation && !state.serverInstanceId) {
            state.recoverableGeneration = {
                generation: clone(state.generation),
                expiredAt: now(),
                reason: 'unknown_server_instance',
                serverInstanceId: null,
            };

            state.pendingGenerationRecovery = {
                reason: 'unknown_server_instance',
                previousGeneration: clone(state.generation),
            };

            state.generation = null;
        }

        state.serverInstanceId = serverInstanceId;
        state.scope = clone(scope);

        if (state.hostMetadataDigest == null) {
            state.hostMetadataDigest = sha256(canonicalJson(state.chatMetadata || {}));
        }

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
        for (const [clientId, member] of map) {
            if (member.lastSeen < cutoff) map.delete(clientId);
        }

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
        if (userOperationChains.get(userId) === tracked) {
            userOperationChains.delete(userId);
        }
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
        if (operationChains.get(key) === tracked) {
            operationChains.delete(key);
        }
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

            const projected =
                Math.max(0, currentBytes - Number(existing?.size || 0))
                + size;

            if (projected > LIMITS.maxPersistedBytesPerUser) {
                throw new Error('Synchronization storage quota exceeded');
            }

            await atomicWrite(file, snapshot);

            return root;
        });

    const trackedScope = next.finally(() => {
        if (persistenceChains.get(key) === trackedScope) {
            persistenceChains.delete(key);
        }
    });

    const trackedUser = trackedScope.finally(() => {
        if (userPersistenceChains.get(userKey) === trackedUser) {
            userPersistenceChains.delete(userKey);
        }
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

    while (scopes.size >= LIMITS.maxScopesPerProcess && candidates.length) {
        scopes.delete(candidates.shift()[0]);
    }
}

async function cleanupUserState(req) {
    let root;

    try {
        root = await ensureStateRoot(req);
    } catch {
        return;
    }

    let entries;

    try {
        entries = await fsp.readdir(root, { withFileTypes: true });
    } catch {
        return;
    }

    const cutoff = now() - LIMITS.staleStateMs;

    for (const entry of entries) {
        const file = path.join(root, entry.name);

        if (entry.isFile() && entry.name.endsWith('.tmp')) {
            const stat = await fsp.stat(file).catch(() => null);

            if (
                stat
                && stat.mtimeMs < now() - LIMITS.staleTempMs
            ) {
                await fsp.rm(file, { force: true }).catch(() => {});
            }

            continue;
        }

        if (!entry.isFile() || !entry.name.endsWith('.json')) continue;

        const stat = await fsp.stat(file).catch(() => null);
        if (!stat || stat.mtimeMs >= cutoff) continue;

        const read = await loadJsonDetailed(file);

        if (!read.ok) {
            await quarantineStateFile(file).catch(() => {});
            continue;
        }

        const state = read.value;
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

    for (const [clientId, member] of map) {
        if (member.lastSeen < cutoff) map.delete(clientId);
    }

    return [...map.values()];
}

function touchMember(scope, body, { allowReplaceExpired = false } = {}) {
    const clientId = String(body.clientId ?? '');
    const deviceId = String(body.deviceId ?? '');

    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) {
        throw new Error('Invalid clientId/deviceId');
    }

    const key = scopeKey(scope);

    let map = members.get(key);
    if (!map) {
        map = new Map();
        members.set(key, map);
    }

    const existing = map.get(clientId);

    if (
        existing
        && existing.deviceId !== deviceId
        && existing.lastSeen >= now() - LIMITS.memberTtlMs
        && !allowReplaceExpired
    ) {
        const error = new Error(
            'clientId is already active on another device session.',
        );
        error.code = 'client_id_conflict';
        throw error;
    }

    map.set(clientId, {
        userId: scope.userId,
        clientId,
        deviceId,
        connectedAt: existing?.deviceId === deviceId
            ? existing.connectedAt
            : now(),
        lastSeen: now(),
    });

    return { clientId, deviceId };
}

function isMember(scope, clientId, deviceId) {
    const member = members.get(scopeKey(scope))?.get(clientId);

    return !!member
        && member.deviceId === deviceId
        && member.lastSeen >= now() - LIMITS.memberTtlMs;
}

function requireCurrentMember(scope, clientId, deviceId) {
    if (!safeId(clientId, 128) || !safeId(deviceId, 128)) return false;

    const member = members.get(scopeKey(scope))?.get(clientId);

    if (
        !member
        || member.deviceId !== deviceId
        || member.lastSeen < now() - LIMITS.memberTtlMs
    ) {
        return false;
    }

    member.lastSeen = now();
    return true;
}

function rateAllowed(scope, clientId) {
    const timestamp = now();
    const key = canonicalJson([scope.userId, clientId]);

    const current = rateWindows.get(key);

    if (
        !current
        || current.expiresAt <= timestamp
    ) {
        rateWindows.set(key, {
            count: 1,
            expiresAt: timestamp + 60_000,
        });
    } else {
        current.count++;
    }

    const userKey = String(scope.userId);
    const userCurrent = userRateWindows.get(userKey);

    if (
        !userCurrent
        || userCurrent.expiresAt <= timestamp
    ) {
        userRateWindows.set(userKey, {
            count: 1,
            expiresAt: timestamp + 60_000,
        });
    } else {
        userCurrent.count++;
    }

    const clientCount = rateWindows.get(key)?.count || 0;
    const userCount = userRateWindows.get(userKey)?.count || 0;

    return clientCount <= LIMITS.maxEventsPerClientPerMinute
        && userCount <= LIMITS.maxEventsPerUserPerMinute;
}

function shouldPersistEvent(state, eventType) {
    if (!String(eventType || '').startsWith('generation_')) return true;

    if (
        [
            'generation_claim',
            'generation_started',
            'generation_input',
            'generation_stop_request',
            'generation_terminal',
            'generation_terminal_recover',
            'generation_recover',
        ].includes(eventType)
    ) {
        return true;
    }

    if (eventType === 'generation_stream') {
        const generation = state.generation;
        if (!generation) return true;

        const last = Number(generation.lastPersistedAt || 0);

        if (now() - last >= LIVE_GENERATION_PERSIST_INTERVAL_MS) {
            generation.lastPersistedAt = now();
            generation.lastPersistedStreamSeq = Number(
                generation.streamSeq || 0,
            );
            return true;
        }

        return false;
    }

    return true;
}

function countUserSse(userId) {
    let count = 0;

    for (const subscription of subscriptions.values()) {
        if (subscription.userId === userId && subscription.res) count++;
    }

    return count;
}

function serializePublicState(
    state,
    { includeSnapshot = true, includeGenerationStream = true } = {},
) {
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
        serverInstanceId,
        updatedAt: state.updatedAt,
        hostSnapshotDigest: state.hostSnapshotDigest || null,
        hostMetadataDigest: state.hostMetadataDigest || null,
        renamedTo: clone(state.renamedTo || null),
        deleted: !!state.deleted,
    };

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

    if (state.recentOps.length > LIMITS.maxRecentOps) {
        state.recentOps.splice(
            0,
            state.recentOps.length - LIMITS.maxRecentOps,
        );
    }
}

function cachedResultResponse(state, cached) {
    const liveOnly =
        String(cached.type || '').startsWith('generation_')
        && !['generation_terminal', 'generation_recover'].includes(cached.type);

    const publicState = serializePublicState(state, {
        includeSnapshot: !liveOnly,
        includeGenerationStream: !liveOnly,
    });

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

    const live = {
        ...clone(event),
        id,
        revision: state.revision,
        epoch: state.epoch,
        ts: now(),
    };

    const stored = clone(live);

    if (bytes(stored) > LIMITS.maxEventBytes) {
        stored.compacted = true;
        delete stored.snapshot;
        delete stored.patch;
        delete stored.message;
        delete stored.groupSettings;

        if (stored.generation) {
            stored.generation = {
                ...stored.generation,
                streamMessage: null,
                streamMessages: [],
            };
        }
    }

    state.events.push(stored);

    if (state.events.length > LIMITS.maxEvents) {
        state.events.splice(
            0,
            state.events.length - LIMITS.maxEvents,
        );
    }

    state.updatedAt = now();

    return live;
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
        totalSseConnections = Math.max(
            0,
            totalSseConnections - 1,
        );

        try {
            subscription.res.end();
        } catch {}
    }

    subscription.res = null;
}

function publish(scope, eventType, payload, eventId) {
    const key = scopeKey(scope);

    for (const [token, subscription] of subscriptions) {
        if (
            subscription.scopeKey !== key
            || !subscription.res
        ) {
            continue;
        }

        try {
            writeSse(
                subscription.res,
                eventType,
                payload,
                eventId,
            );
        } catch {
            closeSubscription(token);
        }
    }
}

function chatFilePath(req, scope) {
    if (scope.kind === 'character') {
        const chatsRoot = req.user?.directories?.chats;
        if (!chatsRoot) return null;

        const avatar = scope.character.replace(/\.png$/i, '');

        return safeJoin(
            safeJoin(chatsRoot, avatar),
            `${scope.chatId}.jsonl`,
        );
    }

    const groupChatsRoot = req.user?.directories?.groupChats;
    if (!groupChatsRoot) return null;

    return safeJoin(
        groupChatsRoot,
        `${scope.chatId}.jsonl`,
    );
}

async function validateCharacterScope(req, scope) {
    const root = req.user?.directories?.chats;
    if (!root) return false;

    const avatar = scope.character.replace(/\.png$/i, '');
    if (!safeName(avatar)) return false;

    const dir = safeJoin(root, avatar);

    try {
        const stat = await fsp.stat(dir);
        return stat.isDirectory();
    } catch {
        return false;
    }
}

async function loadGroupDefinition(req, groupId) {
    const groupsRoot = req.user?.directories?.groups;
    if (!groupsRoot) {
        return {
            ok: false,
            code: 'groups_path_unavailable',
            value: null,
        };
    }

    const result = await loadJsonDetailed(
        safeJoin(groupsRoot, `${groupId}.json`),
    );

    if (!result.exists) {
        return {
            ok: false,
            code: 'group_not_found',
            value: null,
        };
    }

    if (!result.ok) {
        return {
            ok: false,
            code: 'group_read_failed',
            value: null,
        };
    }

    if (!isObject(result.value)) {
        return {
            ok: false,
            code: 'group_invalid',
            value: null,
        };
    }

    return {
        ok: true,
        code: null,
        value: result.value,
    };
}

async function validateGroupScope(req, scope) {
    const loaded = await loadGroupDefinition(
        req,
        scope.groupId,
    );

    if (!loaded.ok) {
        return {
            ok: false,
            code: loaded.code,
            message:
                loaded.code === 'group_not_found'
                    ? 'The requested group does not exist.'
                    : 'The group definition could not be read.',
        };
    }

    const group = loaded.value;

    if (!Array.isArray(group.members)) {
        return {
            ok: false,
            code: 'group_invalid',
            message: 'The group definition is invalid.',
        };
    }

    if (
        !Array.isArray(group.chats)
        || !group.chats.includes(scope.chatId)
    ) {
        return {
            ok: false,
            code: 'group_chat_not_found',
            message: 'The requested group chat does not belong to this group.',
        };
    }

    return {
        ok: true,
        group,
    };
}

async function validateScopeAgainstHost(req, scope) {
    if (scope.kind === 'character') {
        if (!(await validateCharacterScope(req, scope))) {
            return {
                ok: false,
                code: 'character_not_found',
                message: 'The character scope could not be resolved.',
            };
        }
    } else {
        const result = await validateGroupScope(req, scope);
        if (!result.ok) return result;
    }

    const file = chatFilePath(req, scope);

    if (!file) {
        return {
            ok: false,
            code: 'chat_path_unavailable',
            message: 'The chat path could not be resolved.',
        };
    }

    return {
        ok: true,
        file,
    };
}

function projectSnapshotForDigest(snapshot, mode = 'full') {
    if (mode !== 'relevant') return clone(snapshot || []);

    const out = clone(snapshot || []);
    const messageFields = [
        'swipes',
        'swipe_info',
        'swipe_id',
    ];
    const extraFields = [
        'reasoning',
        'reasoning_duration',
        'reasoning_signature',
        'reasoning_display_text',
        'tool_invocations',
    ];

    for (const message of out) {
        if (!isObject(message)) continue;

        if (isObject(message.extra)) {
            delete message.extra.multi_client_sync;
        }

        for (const key of messageFields) {
            delete message[key];
        }

        if (isObject(message.extra)) {
            for (const key of extraFields) {
                delete message.extra[key];
            }
        }
    }

    return out;
}

function snapshotDigestForMode(snapshot, mode = 'full') {
    return sha256(
        canonicalJson(
            projectSnapshotForDigest(
                snapshot,
                mode,
            ),
        ),
    );
}

function metadataDigest(metadata) {
    return sha256(
        canonicalJson(metadata || {}),
    );
}

async function readHostChat(req, scope) {
    const validation = await validateScopeAgainstHost(req, scope);

    if (!validation.ok) {
        return {
            ok: false,
            exists: false,
            hash: null,
            snapshotDigest: null,
            relevantSnapshotDigest: null,
            metadataDigest: null,
            snapshot: [],
            metadata: {},
            missingMessageIds: false,
            error: validation.code,
        };
    }

    const file = validation.file;

    let raw;

    try {
        raw = await fsp.readFile(file, 'utf8');
    } catch (error) {
        if (error?.code === 'ENOENT') {
            return {
                ok: true,
                exists: false,
                hash: null,
                snapshotDigest: sha256(canonicalJson([])),
                relevantSnapshotDigest: sha256(canonicalJson([])),
                metadataDigest: sha256(canonicalJson({})),
                snapshot: [],
                metadata: {},
                missingMessageIds: false,
            };
        }

        return {
            ok: false,
            exists: true,
            hash: null,
            snapshotDigest: null,
            relevantSnapshotDigest: null,
            metadataDigest: null,
            snapshot: [],
            metadata: {},
            missingMessageIds: false,
            error: 'chat_read_failed',
        };
    }

    const hash = sha256(raw);

    const lines = raw
        .split(/\r?\n/)
        .filter(line => line.trim());

    if (
        lines.length
        && lines[0].charCodeAt(0) === 0xFEFF
    ) {
        lines[0] = lines[0].slice(1);
    }

    const parsed = [];

    for (const line of lines) {
        try {
            parsed.push(JSON.parse(line));
        } catch {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                relevantSnapshotDigest: null,
                metadataDigest: null,
                snapshot: [],
                metadata: {},
                missingMessageIds: false,
                error: 'chat_file_corrupt',
            };
        }
    }

    if (!parsed.length) {
        return {
            ok: true,
            exists: true,
            hash,
            snapshotDigest: sha256(canonicalJson([])),
            relevantSnapshotDigest: sha256(canonicalJson([])),
            metadataDigest: sha256(canonicalJson({})),
            snapshot: [],
            metadata: {},
            missingMessageIds: false,
        };
    }

    const header = isObject(parsed[0]) ? parsed[0] : {};
    const snapshot = parsed.slice(1);

    const snapshotCheck = validateSnapshot(snapshot);

    if (!snapshotCheck.ok) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            relevantSnapshotDigest: null,
            metadataDigest: null,
            snapshot: [],
            metadata: {},
            missingMessageIds: false,
            error: snapshotCheck.error,
        };
    }

    const metadata = isObject(header.chat_metadata)
        ? clone(header.chat_metadata)
        : {};

    const metadataCheck = validateMetadata(metadata);

    if (!metadataCheck.ok) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            relevantSnapshotDigest: null,
            metadataDigest: null,
            snapshot: [],
            metadata: {},
            missingMessageIds: false,
            error: metadataCheck.error,
        };
    }

    if (scope.branchId) {
        if (!metadata.integrity) {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                relevantSnapshotDigest: null,
                metadataDigest: null,
                snapshot,
                metadata,
                missingMessageIds: false,
                error: 'branch_integrity_missing',
            };
        }

        if (String(metadata.integrity) !== String(scope.branchId)) {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                relevantSnapshotDigest: null,
                metadataDigest: null,
                snapshot,
                metadata,
                missingMessageIds: false,
                error: 'branch_integrity_mismatch',
            };
        }
    }

    if (scope.parentChatId) {
        if (!metadata.main_chat) {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                relevantSnapshotDigest: null,
                metadataDigest: null,
                snapshot,
                metadata,
                missingMessageIds: false,
                error: 'branch_parent_missing',
            };
        }

        if (String(metadata.main_chat) !== String(scope.parentChatId)) {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                relevantSnapshotDigest: null,
                metadataDigest: null,
                snapshot,
                metadata,
                missingMessageIds: false,
                error: 'branch_parent_mismatch',
            };
        }
    }

    const missingMessageIds = snapshot.some(
        message => !safeId(getMessageId(message), 128),
    );

    return {
        ok: true,
        exists: true,
        hash,
        snapshotDigest: sha256(canonicalJson(snapshot)),
        relevantSnapshotDigest: snapshotDigestForMode(
            snapshot,
            'relevant',
        ),
        metadataDigest: sha256(
            canonicalJson(metadata),
        ),
        snapshot,
        metadata,
        missingMessageIds,
    };
}

const UNSYNCED_MESSAGE_FIELDS = Object.freeze([
    'swipes',
    'swipe_info',
    'swipe_id',
]);

const UNSYNCED_EXTRA_FIELDS = Object.freeze([
    'reasoning',
    'reasoning_duration',
    'reasoning_signature',
    'reasoning_display_text',
    'tool_invocations',
]);

function applySyncPolicy(
    snapshot,
    previousSnapshot,
    syncSwipes = true,
) {
    const next = ensureMessageIds(snapshot || []);

    if (syncSwipes !== false) return next;

    const previousMap = new Map(
        (Array.isArray(previousSnapshot)
            ? previousSnapshot
            : []
        ).map(message => [
            getMessageId(message),
            message,
        ]),
    );

    return next.map(message => {
        const output = clone(message);
        const previous = previousMap.get(
            getMessageId(message),
        );

        for (const key of UNSYNCED_MESSAGE_FIELDS) {
            if (
                previous
                && Object.prototype.hasOwnProperty.call(
                    previous,
                    key,
                )
            ) {
                output[key] = clone(previous[key]);
            } else {
                delete output[key];
            }
        }

        if (!isObject(output.extra)) output.extra = {};

        for (const key of UNSYNCED_EXTRA_FIELDS) {
            if (
                previous?.extra
                && Object.prototype.hasOwnProperty.call(
                    previous.extra,
                    key,
                )
            ) {
                output.extra[key] = clone(previous.extra[key]);
            } else {
                delete output.extra[key];
            }
        }

        return output;
    });
}

function snapshotEquivalentForPolicy(
    a,
    b,
    syncSwipes = true,
) {
    return canonicalJson(
        projectSnapshotForDigest(
            a || [],
            syncSwipes === false ? 'relevant' : 'full',
        ),
    ) === canonicalJson(
        projectSnapshotForDigest(
            b || [],
            syncSwipes === false ? 'relevant' : 'full',
        ),
    );
}

function currentGeneration(state) {
    expireGeneration(state);
    return state.generation || null;
}

function consumePendingGenerationRecovery(
    state,
    source = {},
) {
    const pending = state.pendingGenerationRecovery;
    if (!pending) return null;

    state.pendingGenerationRecovery = null;

    return recordEvent(state, {
        type: 'generation_recover',
        source: {
            clientId: String(source.clientId || 'server'),
            deviceId: String(source.deviceId || 'server'),
        },
        previousGeneration: clone(
            pending.previousGeneration
            || state.recoverableGeneration?.generation
            || null,
        ),
        automatic: true,
        reason: String(
            pending.reason || 'expired',
        ).slice(0, 128),
    });
}

function recoverExpiredGenerationEvent(
    state,
    source = {},
    reason = 'expired',
) {
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

    if (
        !Number.isInteger(baseRevision)
        || baseRevision < 0
    ) {
        return {
            ok: false,
            code: 'invalid_revision',
            message: 'baseRevision must be a non-negative integer.',
        };
    }

    if (baseRevision !== state.revision) {
        return {
            ok: false,
            code: 'revision_conflict',
            message: 'The synchronization revision has advanced.',
            currentRevision: state.revision,
        };
    }

    return { ok: true };
}

function hostDigestCheck(host, body) {
    if (
        body.hostSnapshotDigest === undefined
        && body.hostMetadataDigest === undefined
    ) {
        return { ok: true };
    }

    if (!host.ok) {
        return {
            ok: false,
            code: 'stale_host',
            message: 'The SillyTavern chat could not be verified.',
            currentDigest: host.snapshotDigest,
            hostError: host.error || null,
        };
    }

    const mode =
        body.hostSnapshotDigestMode === 'relevant'
            ? 'relevant'
            : 'full';

    const currentDigest =
        mode === 'relevant'
            ? host.relevantSnapshotDigest
            : host.snapshotDigest;

    if (
        body.hostSnapshotDigest !== undefined
        && currentDigest !== String(
            body.hostSnapshotDigest,
        )
    ) {
        return {
            ok: false,
            code: 'stale_host',
            message: 'The local SillyTavern chat changed since this operation was created.',
            currentDigest,
        };
    }

    if (
        body.hostMetadataDigest !== undefined
        && String(host.metadataDigest || '')
            !== String(body.hostMetadataDigest)
    ) {
        return {
            ok: false,
            code: 'stale_host_metadata',
            message: 'The local SillyTavern chat metadata changed since this operation was created.',
            currentDigest:
                host.metadataDigest || null,
        };
    }

    return { ok: true };
}

async function restoreAfterPersistFailure(
    req,
    scope,
    state,
) {
    const persisted = await loadJson(
        storageFile(req, scope),
    );

    if (stateIdentityValid(persisted, scope)) {
        Object.keys(state).forEach(key => delete state[key]);
        Object.assign(state, clone(persisted));
        pruneState(state);
        return;
    }

    Object.assign(
        state,
        emptyState(scope),
    );
}

function diffSnapshot(before, after) {
    const left = Array.isArray(before) ? before : [];
    const right = Array.isArray(after) ? after : [];

    let prefix = 0;

    while (
        prefix < left.length
        && prefix < right.length
        && canonicalJson(left[prefix])
            === canonicalJson(right[prefix])
    ) {
        prefix++;
    }

    let suffix = 0;

    while (
        suffix < left.length - prefix
        && suffix < right.length - prefix
        && canonicalJson(
            left[left.length - 1 - suffix],
        ) === canonicalJson(
            right[right.length - 1 - suffix],
        )
    ) {
        suffix++;
    }

    const beforeEnd = left.length - suffix;
    const afterEnd = right.length - suffix;

    return {
        kind:
            prefix === left.length
            && right.length >= left.length
                ? 'insert'
                : prefix === right.length
                    && left.length >= right.length
                    ? 'delete'
                    : 'replace',
        start: prefix,
        deleteCount: beforeEnd - prefix,
        messages: clone(
            right.slice(prefix, afterEnd),
        ),
    };
}

function computeTombstones(
    before,
    after,
    revision,
) {
    const afterIds = new Set(
        after.map(getMessageId).filter(Boolean),
    );

    const tombstones = [];

    for (const message of before) {
        const id = getMessageId(message);

        if (id && !afterIds.has(id)) {
            tombstones.push({
                messageId: id,
                revision,
                deletedAt: now(),
            });
        }
    }

    return tombstones;
}

function groupSettingsSnapshot(group) {
    const allowedKeys = [
        'name',
        'members',
        'disabled_members',
        'chats',
        'generation_mode',
        'generation_mode_join_prefix',
        'generation_mode_join_suffix',
        'activation_strategy',
        'auto_mode_delay',
        'allow_self_responses',
        'avatar_url',
        'hideMutedSprites',
        'fav',
    ];

    const result = {};

    for (const key of allowedKeys) {
        if (group?.[key] !== undefined) {
            result[key] = clone(group[key]);
        }
    }

    return result;
}

async function handleJoin(req, res) {
    if (requestBodyTooLarge(req)) {
        return sendError(
            res,
            413,
            'request_too_large',
            'Request is too large.',
        );
    }

    const userId = userIdFromRequest(req);

    if (!userId) {
        return sendError(
            res,
            401,
            'unauthenticated',
            'SillyTavern authentication is required.',
        );
    }

    let scope;

    try {
        scope = normalizeScope(
            req,
            req.body?.scope,
        );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_scope',
            error.message,
        );
    }

    if (
        Number(req.body?.protocol) !== PROTOCOL
        || Number(req.body?.schema) !== SCHEMA
    ) {
        return sendError(
            res,
            409,
            'protocol_mismatch',
            'Synchronization protocol/schema mismatch.',
            {
                expectedProtocol: PROTOCOL,
                expectedSchema: SCHEMA,
            },
        );
    }

    const requestedClientId = String(
        req.body?.clientId || '',
    );

    const requestedDeviceId = String(
        req.body?.deviceId || '',
    );

    if (
        !safeId(requestedClientId, 128)
        || !safeId(requestedDeviceId, 128)
    ) {
        return sendError(
            res,
            400,
            'invalid_client',
            'clientId and deviceId are required.',
        );
    }

    const scopeValidation =
        await validateScopeAgainstHost(
            req,
            scope,
        );

    if (
        !scopeValidation.ok
        && scopeValidation.code !== 'character_not_found'
    ) {
        return sendError(
            res,
            scopeValidation.code === 'group_not_found'
                ? 404
                : 400,
            scopeValidation.code,
            scopeValidation.message,
        );
    }

    let ids;

    try {
        ids = await withUserLock(
            userId,
            async () => {
                const key = scopeKey(scope);
                const existingMap = members.get(key);
                const existingMember =
                    existingMap?.get(
                        requestedClientId,
                    );

                if (
                    (!existingMap || !existingMember)
                    && activeScopeCountForUser(
                        userId,
                    ) >= LIMITS.maxScopesPerUser
                ) {
                    const error = new Error(
                        'Too many active synchronization scopes for this user.',
                    );
                    error.code = 'scope_limit';
                    throw error;
                }

                return touchMember(
                    scope,
                    req.body || {},
                );
            },
        );
    } catch (error) {
        return sendError(
            res,
            error.code === 'scope_limit'
                ? 429
                : error.code === 'client_id_conflict'
                    ? 409
                    : 400,
            error.code || 'invalid_client',
            error.message,
        );
    }

    let resultState;
    let bootstrapped = false;
    let host;

    const subscriptionToken =
        randomId('sse_');

    try {
        await withScopeLock(
            scope,
            async () => {
                ids = touchMember(
                    scope,
                    req.body || {},
                );

                const state = await loadState(
                    req,
                    scope,
                );

                const pendingRecoveryEvent =
                    consumePendingGenerationRecovery(
                        state,
                        {
                            clientId: 'server',
                            deviceId: 'server',
                        },
                    );

                const beforeGeneration =
                    !!state.generation;

                host = await readHostChat(
                    req,
                    scope,
                );

                const recoveryEvent =
                    recoverExpiredGenerationEvent(
                        state,
                        ids,
                        'expired_on_join',
                    );

                const effectiveRecoveryEvent =
                    pendingRecoveryEvent
                    || recoveryEvent;

                let changed =
                    !!effectiveRecoveryEvent;

                if (
                    scope.kind === 'group'
                    && state.groupSettings === null
                ) {
                    const definition =
                        await loadGroupDefinition(
                            req,
                            scope.groupId,
                        );

                    if (definition?.ok) {
                        state.groupSettings =
                            groupSettingsSnapshot(
                                definition.value,
                            );
                        changed = true;
                    }
                }

                if (
                    state.revision === 0
                    && state.snapshot.length === 0
                    && host.ok
                    && host.exists
                ) {
                    if (!host.missingMessageIds) {
                        const normalized =
                            clone(host.snapshot);

                        state.snapshot = normalized;
                        state.chatMetadata =
                            clone(host.metadata);

                        state.hostSnapshotDigest =
                            snapshotDigestForMode(
                                normalized,
                                'full',
                            );

                        state.hostMetadataDigest =
                            metadataDigest(
                                host.metadata,
                            );

                        state.revision = 1;

                        recordEvent(state, {
                            type: 'bootstrap',
                            source: {
                                clientId: ids.clientId,
                                deviceId: ids.deviceId,
                            },
                            patch: {
                                kind: 'replace',
                                start: 0,
                                deleteCount: 0,
                                messages:
                                    clone(normalized),
                            },
                            stateDigest:
                                sha256(
                                    stableJson(
                                        normalized,
                                    ),
                                ),
                        });

                        bootstrapped = true;
                        changed = true;
                    }
                }

                if (
                    !beforeGeneration
                    && state.generation
                ) {
                    currentGeneration(state);
                }

                if (changed) {
                    await persistState(
                        req,
                        scope,
                        state,
                    );
                }

                if (effectiveRecoveryEvent) {
                    publish(
                        scope,
                        'sync',
                        {
                            epoch: state.epoch,
                            event: clone(
                                effectiveRecoveryEvent,
                            ),
                            state:
                                serializePublicState(
                                    state,
                                ),
                        },
                        effectiveRecoveryEvent.id,
                    );
                }

                if (bootstrapped) {
                    const bootstrapEvent =
                        state.events.at(-1);

                    if (
                        bootstrapEvent?.type
                        === 'bootstrap'
                    ) {
                        publish(
                            scope,
                            'sync',
                            {
                                epoch: state.epoch,
                                event: clone(
                                    bootstrapEvent,
                                ),
                                state:
                                    serializePublicState(
                                        state,
                                    ),
                            },
                            bootstrapEvent.id,
                        );
                    }
                }

                resultState = clone(state);

                for (
                    const [
                        oldToken,
                        subscription,
                    ] of subscriptions
                ) {
                    if (
                        subscription.userId === userId
                        && subscription.clientId
                            === ids.clientId
                        && subscription.deviceId
                            === ids.deviceId
                    ) {
                        closeSubscription(
                            oldToken,
                        );
                    }
                }

                subscriptions.set(
                    subscriptionToken,
                    {
                        token:
                            subscriptionToken,
                        userId,
                        clientId:
                            ids.clientId,
                        deviceId:
                            ids.deviceId,
                        scope: clone(scope),
                        scopeKey:
                            scopeKey(scope),
                        createdAt: now(),
                        res: null,
                    },
                );
            },
        );
    } catch (error) {
        if (error.code === 'scope_limit') {
            return sendError(
                res,
                429,
                error.code,
                error.message,
            );
        }

        return sendError(
            res,
            507,
            'persistence_failed',
            'Synchronization state could not be initialized.',
        );
    }

    await cleanupUserState(req);

    return res.json({
        ok: true,
        protocol: PROTOCOL,
        schema: SCHEMA,
        userId,
        scope: clone(scope),
        state:
            serializePublicState(
                resultState,
            ),
        serverNow: now(),
        membership: ids,
        subscriptionToken,
        bootstrap: bootstrapped,
        host: {
            exists:
                host?.exists || false,
            ok:
                host?.ok !== false,
            hash:
                host?.hash || null,
            snapshotDigest:
                host?.snapshotDigest || null,
            relevantSnapshotDigest:
                host?.relevantSnapshotDigest
                || null,
            metadataDigest:
                host?.metadataDigest
                || null,
            missingMessageIds:
                !!host?.missingMessageIds,
            error:
                host?.error || null,
        },
        capabilities: {
            sse: true,
            revisions: true,
            durableQueue: true,
            idempotency: true,
            generationLease: true,
            generationStream: true,
            resumableGenerationPreview: true,
            branches: true,
            checkpoints: true,
            swipes: true,
            reasoning: true,
            toolInvocations: true,
            attachments:
                'server-resident-reference',
            exactTokenReplay: false,
        },
    });
}

async function handleLeave(req, res) {
    let scope;

    try {
        scope = normalizeScope(
            req,
            req.body?.scope,
        );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_scope',
            error.message,
        );
    }

    if (
        Number(req.body?.protocol) !== PROTOCOL
        || Number(req.body?.schema) !== SCHEMA
    ) {
        return sendError(
            res,
            409,
            'protocol_mismatch',
            'Synchronization protocol/schema mismatch.',
        );
    }

    const clientId = String(
        req.body?.clientId || '',
    );

    const deviceId = String(
        req.body?.deviceId || '',
    );

    const subscriptionToken = String(
        req.body?.subscriptionToken || '',
    );

    if (
        !safeId(clientId, 128)
        || !safeId(deviceId, 128)
    ) {
        return sendError(
            res,
            400,
            'invalid_client',
            'clientId and deviceId are required.',
        );
    }

    if (!safeId(subscriptionToken, 160)) {
        return sendError(
            res,
            400,
            'invalid_subscription',
            'subscriptionToken is required for a synchronized leave.',
        );
    }

    return withScopeLock(
        scope,
        async () => {
            const subscription =
                subscriptions.get(
                    subscriptionToken,
                );

            const validSubscription =
                subscription
                && subscription.scopeKey
                    === scopeKey(scope)
                && subscription.clientId
                    === clientId
                && subscription.deviceId
                    === deviceId;

            if (!validSubscription) {
                return res.json({
                    ok: true,
                    clientId,
                    deviceId,
                    ignored: true,
                });
            }

            closeSubscription(
                subscriptionToken,
            );

            const member =
                members.get(
                    scopeKey(scope),
                )?.get(clientId);

            if (
                member
                && member.deviceId === deviceId
            ) {
                members
                    .get(scopeKey(scope))
                    ?.delete(clientId);
            }

            return res.json({
                ok: true,
                clientId,
                deviceId,
            });
        },
    );
}

async function handleHeartbeat(req, res) {
    let scope;

    try {
        scope = normalizeScope(
            req,
            req.body?.scope,
        );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_scope',
            error.message,
        );
    }

    if (
        Number(req.body?.protocol) !== PROTOCOL
        || Number(req.body?.schema) !== SCHEMA
    ) {
        return sendError(
            res,
            409,
            'protocol_mismatch',
            'Synchronization protocol/schema mismatch.',
        );
    }

    const clientId = String(
        req.body?.clientId || '',
    );

    const deviceId = String(
        req.body?.deviceId || '',
    );

    if (
        !requireCurrentMember(
            scope,
            clientId,
            deviceId,
        )
    ) {
        return sendError(
            res,
            403,
            'not_member',
            'Client is not a current member of this scope.',
        );
    }

    return withScopeLock(
        scope,
        async () => {
            const state =
                await loadState(
                    req,
                    scope,
                );

            if (
                !requireCurrentMember(
                    scope,
                    clientId,
                    deviceId,
                )
            ) {
                return sendError(
                    res,
                    403,
                    'not_member',
                    'Client is no longer a current member of this scope.',
                );
            }

            const recoveryEvent =
                recoverExpiredGenerationEvent(
                    state,
                    {
                        clientId: 'server',
                        deviceId: 'server',
                    },
                    'expired_on_heartbeat',
                );

            if (recoveryEvent) {
                try {
                    await persistState(
                        req,
                        scope,
                        state,
                    );

                    publish(
                        scope,
                        'sync',
                        {
                            epoch: state.epoch,
                            event: recoveryEvent,
                            state:
                                serializePublicState(
                                    state,
                                ),
                        },
                        recoveryEvent.id,
                    );
                } catch {
                    await restoreAfterPersistFailure(
                        req,
                        scope,
                        state,
                    );

                    return sendError(
                        res,
                        507,
                        'persistence_failed',
                        'Synchronization state could not be recovered.',
                    );
                }
            }

            let renewed = false;

            if (
                isGenerationOwner(
                    state,
                    req.body || {},
                )
                && state.generation
            ) {
                state.generation.leaseUntil =
                    now()
                    + LIMITS.generationLeaseMs;

                state.updatedAt = now();
                renewed = true;

                try {
                    await persistState(
                        req,
                        scope,
                        state,
                    );
                } catch {
                    await restoreAfterPersistFailure(
                        req,
                        scope,
                        state,
                    );

                    return sendError(
                        res,
                        507,
                        'persistence_failed',
                        'Synchronization state could not be durably persisted.',
                    );
                }
            }

            return res.json({
                ok: true,
                membership: {
                    clientId,
                    deviceId,
                },
                renewed,
                revision: state.revision,
                epoch: state.epoch,
                generation:
                    clone(state.generation),
            });
        },
    );
}

async function stateResponse(req, res) {
    const raw =
        req.method === 'GET'
            ? req.query
            : req.body;

    let scope;

    try {
        scope = normalizeScope(
            req,
            raw?.scope,
        );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_scope',
            error.message,
        );
    }

    if (
        Number(raw?.protocol) !== PROTOCOL
        || Number(raw?.schema) !== SCHEMA
    ) {
        return sendError(
            res,
            409,
            'protocol_mismatch',
            'Synchronization protocol/schema mismatch.',
            {
                expectedProtocol: PROTOCOL,
                expectedSchema: SCHEMA,
            },
        );
    }

    const clientId = String(
        raw?.clientId || '',
    );

    const deviceId = String(
        raw?.deviceId || '',
    );

    if (
        !safeId(clientId, 128)
        || !safeId(deviceId, 128)
    ) {
        return sendError(
            res,
            400,
            'invalid_client',
            'clientId and deviceId are required.',
        );
    }

    if (
        !isMember(
            scope,
            clientId,
            deviceId,
        )
    ) {
        return sendError(
            res,
            403,
            'not_member',
            'Client is not a current member of this scope.',
        );
    }

    return withScopeLock(
        scope,
        async () => {
            if (
                !requireCurrentMember(
                    scope,
                    clientId,
                    deviceId,
                )
            ) {
                return sendError(
                    res,
                    403,
                    'not_member',
                    'Client is no longer a current member of this scope.',
                );
            }

            const state =
                await loadState(
                    req,
                    scope,
                );

            const recoveryEvent =
                recoverExpiredGenerationEvent(
                    state,
                    {
                        clientId: 'server',
                        deviceId: 'server',
                    },
                    'expired_on_state',
                );

            if (recoveryEvent) {
                await persistState(
                    req,
                    scope,
                    state,
                ).catch(() => {});

                publish(
                    scope,
                    'sync',
                    {
                        epoch: state.epoch,
                        event: clone(
                            recoveryEvent,
                        ),
                        state:
                            serializePublicState(
                                state,
                            ),
                    },
                    recoveryEvent.id,
                );
            }

            const host =
                await readHostChat(
                    req,
                    scope,
                );

            return res.json({
                ok: true,
                protocol: PROTOCOL,
                schema: SCHEMA,
                state:
                    serializePublicState(
                        state,
                    ),
                host: {
                    ok: host.ok,
                    exists: host.exists,
                    hash: host.hash,
                    snapshotDigest:
                        host.snapshotDigest,
                    relevantSnapshotDigest:
                        host.relevantSnapshotDigest
                        || null,
                    metadataDigest:
                        host.metadataDigest
                        || null,
                    missingMessageIds:
                        !!host.missingMessageIds,
                    error:
                        host.error || null,
                },
                cursor: {
                    epoch: state.epoch,
                    revision: state.revision,
                    lastEventId:
                        Number(
                            state.events.at(-1)?.id
                            || 0,
                        ),
                    serverInstanceId,
                },
            });
        },
    );
}

async function handleSse(req, res) {
    const token = String(
        req.query?.token || '',
    );

    const subscription =
        subscriptions.get(token);

    const userId =
        userIdFromRequest(req);

    if (
        !subscription
        || subscription.userId !== userId
    ) {
        return res
            .status(401)
            .end('invalid subscription');
    }

    if (
        !isMember(
            subscription.scope,
            subscription.clientId,
            subscription.deviceId,
        )
    ) {
        return res
            .status(409)
            .end('membership expired');
    }

    if (
        totalSseConnections
        >= LIMITS.maxSseTotal
    ) {
        return res
            .status(503)
            .end('SSE capacity reached');
    }

    if (
        countUserSse(userId)
        >= LIMITS.maxSsePerUser
        && !subscription.res
    ) {
        return res
            .status(503)
            .end('Per-user SSE capacity reached');
    }

    if (subscription.res) {
        try {
            subscription.res.end();
        } catch {}

        subscription.res = null;

        totalSseConnections =
            Math.max(
                0,
                totalSseConnections - 1,
            );
    }

    totalSseConnections++;
    subscription.res = res;

    res.status(200).set({
        'Content-Type':
            'text/event-stream',
        'Cache-Control':
            'no-cache, no-transform',
        Connection: 'keep-alive',
        'X-Accel-Buffering': 'no',
    });

    res.flushHeaders?.();

    const state =
        await loadState(
            req,
            subscription.scope,
        );

    const recoveryEvent =
        recoverExpiredGenerationEvent(
            state,
            {
                clientId: 'server',
                deviceId: 'server',
            },
            'expired_on_sse',
        );

    if (recoveryEvent) {
        await persistState(
            req,
            subscription.scope,
            state,
        ).catch(() => {});

        publish(
            subscription.scope,
            'sync',
            {
                epoch: state.epoch,
                event: clone(
                    recoveryEvent,
                ),
                state:
                    serializePublicState(
                        state,
                    ),
            },
            recoveryEvent.id,
        );
    }

    const lastEventId =
        Number.parseInt(
            req.get('Last-Event-ID')
            || req.query?.lastEventId
            || '0',
            10,
        ) || 0;

    writeSse(
        res,
        'hello',
        {
            protocol: PROTOCOL,
            schema: SCHEMA,
            epoch: state.epoch,
            revision: state.revision,
            eventId:
                Number(
                    state.events.at(-1)?.id
                    || 0,
                ),
            generation:
                clone(state.generation),
            serverInstanceId,
        },
    );

    const oldest =
        Number(
            state.events[0]?.id
            || 0,
        );

    if (
        lastEventId
        && oldest
        && lastEventId < oldest - 1
    ) {
        writeSse(
            res,
            'resync_required',
            {
                epoch: state.epoch,
                revision: state.revision,
                eventId: oldest,
                reason:
                    'replay_window_exhausted',
            },
        );
    } else if (lastEventId) {
        for (const event of state.events) {
            if (Number(event.id) <= lastEventId) continue;

            writeSse(
                res,
                'replay',
                {
                    epoch: state.epoch,
                    event: clone(event),
                },
                event.id,
            );
        }
    }

    writeSse(
        res,
        'replay_complete',
        {
            epoch: state.epoch,
            revision: state.revision,
            eventId:
                Number(
                    state.events.at(-1)?.id
                    || 0,
                ),
        },
    );

    const keepalive =
        setInterval(() => {
            if (res.writableEnded) {
                clearInterval(keepalive);
                return;
            }

            if (
                !isMember(
                    subscription.scope,
                    subscription.clientId,
                    subscription.deviceId,
                )
            ) {
                clearInterval(keepalive);
                closeSubscription(
                    subscription.token,
                );
                return;
            }

            try {
                res.write(
                    `: keepalive ${now()}\n\n`,
                );
            } catch {
                clearInterval(keepalive);
            }
        }, 15_000);

    const close = () => {
        clearInterval(keepalive);

        if (subscription.res !== res) return;

        subscription.res = null;

        totalSseConnections =
            Math.max(
                0,
                totalSseConnections - 1,
            );
    };

    req.on('close', close);
}

async function processSnapshotMutation(
    req,
    scope,
    state,
    body,
) {
    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
                generation:
                    clone(state.generation),
            },
        };
    }

    const host =
        await readHostChat(
            req,
            scope,
        );

    const hostCheck =
        hostDigestCheck(
            host,
            body,
        );

    if (!hostCheck.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: hostCheck,
                generation:
                    clone(state.generation),
            },
        };
    }

    const validation =
        validateSnapshot(
            body.snapshot,
        );

    if (!validation.ok) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code: 'invalid_snapshot',
                    message:
                        validation.error,
                },
            },
        };
    }

    const metadata =
        body.chatMetadata === undefined
            ? clone(state.chatMetadata)
            : clone(body.chatMetadata);

    const metadataCheck =
        validateMetadata(
            metadata,
        );

    if (!metadataCheck.ok) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code: 'invalid_metadata',
                    message:
                        metadataCheck.error,
                },
            },
        };
    }

    if (
        scope.branchId
        && String(
            metadata.integrity || '',
        ) !== String(scope.branchId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.integrity
                            ? 'branch_integrity_mismatch'
                            : 'branch_integrity_missing',
                    message:
                        metadata.integrity
                            ? 'Branch integrity does not match this synchronized branch.'
                            : 'Branch integrity metadata is required for this synchronized branch.',
                },
            },
        };
    }

    if (
        scope.parentChatId
        && String(
            metadata.main_chat || '',
        ) !== String(scope.parentChatId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.main_chat
                            ? 'branch_parent_mismatch'
                            : 'branch_parent_missing',
                    message:
                        metadata.main_chat
                            ? 'Branch parent does not match this synchronized scope.'
                            : 'Branch parent metadata is required for this synchronized branch.',
                },
            },
        };
    }

    const next =
        applySyncPolicy(
            body.snapshot,
            state.snapshot,
            body.syncSwipes !== false,
        );

    const previous =
        clone(state.snapshot);

    const snapshotChanged =
        !snapshotEquivalentForPolicy(
            previous,
            next,
            body.syncSwipes !== false,
        );

    if (
        !hasCompleteMessageIds(
            body.snapshot,
        )
    ) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'message_ids_required',
                    message:
                        'All messages must have synchronization IDs. Refresh/reconcile the chat before retrying.',
                },
            },
        };
    }

    const metadataChanged =
        canonicalJson(
            state.chatMetadata || {},
        ) !== canonicalJson(
            metadata,
        );

    if (
        !snapshotChanged
        && !metadataChanged
    ) {
        return {
            status: 200,
            event: null,
            unchanged: true,
        };
    }

    state.revision++;
    state.snapshot = next;
    state.chatMetadata = metadata;

    state.hostSnapshotDigest =
        snapshotDigestForMode(
            next,
            body.syncSwipes === false
                ? 'relevant'
                : 'full',
        );

    state.hostMetadataDigest =
        metadataDigest(
            metadata,
        );

    state.tombstones.push(
        ...computeTombstones(
            previous,
            next,
            state.revision,
        ),
    );

    const event =
        recordEvent(
            state,
            {
                type: body.type,
                opId: body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                patch:
                    diffSnapshot(
                        previous,
                        next,
                    ),
                stateDigest:
                    sha256(
                        canonicalJson(next),
                    ),
            },
        );

    return {
        status: 200,
        event,
    };
}

async function processMessageDelete(
    req,
    scope,
    state,
    body,
) {
    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
                generation:
                    clone(state.generation),
            },
        };
    }

    const rawIds =
        Array.isArray(
            body.deletedMessageIds,
        )
            ? body.deletedMessageIds
            : [];

    const deletedMessageIds = [
        ...new Set(
            rawIds
                .map(value =>
                    String(
                        value || '',
                    ).trim(),
                )
                .filter(Boolean),
        ),
    ];

    if (
        !deletedMessageIds.length
        || deletedMessageIds.length > 4096
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_deleted_message_ids',
                    message:
                        'deletedMessageIds must contain between 1 and 4096 synchronization IDs.',
                },
            },
        };
    }

    if (
        deletedMessageIds.some(
            id => !safeId(id, 128),
        )
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_message_id',
                    message:
                        'A deleted message synchronization ID is invalid.',
                },
            },
        };
    }

    const host =
        await readHostChat(
            req,
            scope,
        );

    const hostCheck =
        hostDigestCheck(
            host,
            body,
        );

    if (!hostCheck.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: hostCheck,
                generation:
                    clone(state.generation),
            },
        };
    }

    if (
        !host.ok
        || !Array.isArray(host.snapshot)
    ) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'stale_host',
                    message:
                        'The SillyTavern chat could not be verified.',
                },
            },
        };
    }

    if (
        !hasCompleteMessageIds(
            host.snapshot,
        )
    ) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'message_ids_required',
                    message:
                        'The host chat must have synchronization IDs before a message can be deleted.',
                },
            },
        };
    }

    let metadata =
        body.chatMetadata === undefined
            ? clone(state.chatMetadata)
            : clone(body.chatMetadata);

    const metadataCheck =
        validateMetadata(
            metadata,
        );

    if (!metadataCheck.ok) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_metadata',
                    message:
                        metadataCheck.error,
                },
            },
        };
    }

    if (
        scope.branchId
        && String(
            metadata.integrity || '',
        ) !== String(scope.branchId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.integrity
                            ? 'branch_integrity_mismatch'
                            : 'branch_integrity_missing',
                    message:
                        metadata.integrity
                            ? 'Branch integrity does not match this synchronized branch.'
                            : 'Branch integrity metadata is required for this synchronized branch.',
                },
            },
        };
    }

    if (
        scope.parentChatId
        && String(
            metadata.main_chat || '',
        ) !== String(scope.parentChatId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.main_chat
                            ? 'branch_parent_mismatch'
                            : 'branch_parent_missing',
                    message:
                        metadata.main_chat
                            ? 'Branch parent does not match this synchronized scope.'
                            : 'Branch parent metadata is required for this synchronized branch.',
                },
            },
        };
    }

    const deleteSet =
        new Set(
            deletedMessageIds,
        );

    const previous =
        clone(state.snapshot);

    const actuallyRemoved =
        previous
            .filter(message =>
                deleteSet.has(
                    getMessageId(
                        message,
                    ),
                ),
            )
            .map(getMessageId);

    const next =
        previous.filter(
            message =>
                !deleteSet.has(
                    getMessageId(
                        message,
                    ),
                ),
        );

    const metadataChanged =
        canonicalJson(
            state.chatMetadata || {},
        ) !== canonicalJson(
            metadata,
        );

    if (
        !actuallyRemoved.length
        && !metadataChanged
    ) {
        return {
            status: 200,
            event: null,
            unchanged: true,
        };
    }

    state.revision++;
    state.snapshot = next;
    state.chatMetadata = metadata;

    state.hostSnapshotDigest =
        snapshotDigestForMode(
            next,
            body.syncSwipes === false
                ? 'relevant'
                : 'full',
        );

    state.hostMetadataDigest =
        metadataDigest(
            metadata,
        );

    state.hostMessageIdsPending = false;

    state.tombstones.push(
        ...actuallyRemoved.map(
            messageId => ({
                messageId,
                revision:
                    state.revision,
                deletedAt: now(),
            }),
        ),
    );

    const event =
        recordEvent(
            state,
            {
                type: 'message_delete',
                opId: body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                deletedMessageIds:
                    actuallyRemoved,
                revision:
                    state.revision,
                ...(metadataChanged
                    ? {
                        chatMetadata:
                            clone(metadata),
                        previousMetadataDigest:
                            sha256(
                                canonicalJson(
                                    state.chatMetadata
                                    || {},
                                ),
                            ),
                    }
                    : {}),
                stateDigest:
                    sha256(
                        canonicalJson(next),
                    ),
            },
        );

    return {
        status: 200,
        event,
    };
}

async function processMetadataMutation(
    req,
    scope,
    state,
    body,
) {
    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
            },
        };
    }

    const host =
        await readHostChat(
            req,
            scope,
        );

    if (
        body.hostMetadataDigest
        !== undefined
    ) {
        const hostCheck =
            hostDigestCheck(
                host,
                body,
            );

        if (!hostCheck.ok) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: hostCheck,
                },
            };
        }
    }

    const metadata =
        clone(body.chatMetadata);

    const check =
        validateMetadata(
            metadata,
        );

    if (!check.ok) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_metadata',
                    message:
                        check.error,
                },
            },
        };
    }

    if (
        scope.branchId
        && String(
            metadata.integrity || '',
        ) !== String(scope.branchId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.integrity
                            ? 'branch_integrity_mismatch'
                            : 'branch_integrity_missing',
                    message:
                        metadata.integrity
                            ? 'Branch integrity does not match this synchronized branch.'
                            : 'Branch integrity metadata is required for this synchronized branch.',
                },
            },
        };
    }

    if (
        scope.parentChatId
        && String(
            metadata.main_chat || '',
        ) !== String(scope.parentChatId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        metadata.main_chat
                            ? 'branch_parent_mismatch'
                            : 'branch_parent_missing',
                    message:
                        metadata.main_chat
                            ? 'Branch parent does not match this synchronized scope.'
                            : 'Branch parent metadata is required for this synchronized branch.',
                },
            },
        };
    }

    const previous =
        clone(state.chatMetadata);

    if (
        stableJson(previous || {})
        === stableJson(metadata)
    ) {
        return {
            status: 200,
            event: null,
            unchanged: true,
        };
    }

    state.revision++;
    state.chatMetadata = metadata;
    state.hostMetadataDigest =
        metadataDigest(metadata);

    const event =
        recordEvent(
            state,
            {
                type: 'metadata',
                opId: body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                chatMetadata:
                    clone(metadata),
                previousMetadataDigest:
                    sha256(
                        canonicalJson(
                            previous,
                        ),
                    ),
            },
        );

    return {
        status: 200,
        event,
    };
}

async function processGroupSettings(
    scope,
    state,
    body,
) {
    if (scope.kind !== 'group') {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code: 'not_group',
                    message:
                        'group_settings requires a group scope.',
                },
            },
        };
    }

    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
            },
        };
    }

    if (
        !isObject(body.groupSettings)
        || !validateDataTree(
            body.groupSettings,
        )
        || bytes(
            body.groupSettings,
        ) > LIMITS.maxGroupSettingsBytes
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_group_settings',
                    message:
                        'groupSettings is invalid or too large.',
                },
            },
        };
    }

    const allowed = [
        'name',
        'members',
        'disabled_members',
        'chats',
        'generation_mode',
        'generation_mode_join_prefix',
        'generation_mode_join_suffix',
        'activation_strategy',
        'auto_mode_delay',
        'allow_self_responses',
        'avatar_url',
        'hideMutedSprites',
        'fav',
    ];

    const sanitized = {};

    for (const key of allowed) {
        if (
            Object.prototype.hasOwnProperty.call(
                body.groupSettings,
                key,
            )
        ) {
            sanitized[key] =
                clone(
                    body.groupSettings[key],
                );
        }
    }

    if (
        canonicalJson(sanitized)
        === canonicalJson(
            state.groupSettings || {},
        )
    ) {
        return {
            status: 200,
            event: null,
            unchanged: true,
        };
    }

    state.revision++;
    state.groupSettings = sanitized;

    const event =
        recordEvent(
            state,
            {
                type: 'group_settings',
                opId: body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                groupSettings:
                    clone(sanitized),
            },
        );

    return {
        status: 200,
        event,
    };
}

async function processBranchAnnouncement(
    req,
    parentScope,
    parentState,
    body,
) {
    const revision =
        revisionCheck(
            parentState,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
            },
        };
    }

    let childScope;

    try {
        childScope =
            normalizeScope(
                req,
                body.childScope,
            );
    } catch (error) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_child_scope',
                    message:
                        error.message,
                },
            },
        };
    }

    if (
        childScope.kind
        !== parentScope.kind
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_scope_mismatch',
                    message:
                        'Parent and child scopes must have the same kind.',
                },
            },
        };
    }

    if (
        parentScope.kind === 'character'
        && childScope.character
            !== parentScope.character
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_character_mismatch',
                    message:
                        'Branch must belong to the same character.',
                },
            },
        };
    }

    if (
        parentScope.kind === 'group'
        && childScope.groupId
            !== parentScope.groupId
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_group_mismatch',
                    message:
                        'Branch must belong to the same group.',
                },
            },
        };
    }

    if (!childScope.branchId) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_integrity_required',
                    message:
                        'The child branch/checkpoint must provide its native integrity ID.',
                },
            },
        };
    }

    const branchKind =
        body.branchKind === 'checkpoint'
            ? 'checkpoint'
            : 'branch';

    const expectedMainChat =
        branchKind === 'checkpoint'
            ? (
                parentScope.parentChatId
                || parentScope.chatId
            )
            : parentScope.chatId;

    if (
        childScope.parentChatId
        !== expectedMainChat
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_parent_mismatch',
                    message:
                        'Child chat does not point to the expected native parent/main chat.',
                },
            },
        };
    }

    const host =
        await readHostChat(
            req,
            childScope,
        );

    if (!host.ok || !host.exists) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_host_missing',
                    message:
                        'The newly-created branch/checkpoint chat is not yet available on the server.',
                },
            },
        };
    }

    if (
        host.metadata?.main_chat
        && String(
            host.metadata.main_chat,
        ) !== String(expectedMainChat)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_host_parent_mismatch',
                    message:
                        'The native branch metadata points to a different parent.',
                },
            },
        };
    }

    if (
        host.metadata?.integrity
        && String(
            host.metadata.integrity,
        ) !== String(childScope.branchId)
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_host_integrity_mismatch',
                    message:
                        'The supplied branch ID does not match the native chat integrity.',
                },
            },
        };
    }

    const childState =
        await loadState(
            req,
            childScope,
        );

    if (childState.revision === 0) {
        if (host.missingMessageIds) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'branch_message_ids_missing',
                        message:
                            'The native child chat does not yet contain synchronization message IDs.',
                    },
                },
            };
        }

        childState.snapshot =
            clone(host.snapshot);

        childState.chatMetadata =
            clone(host.metadata);

        childState.revision = 1;

        childState.hostSnapshotDigest =
            snapshotDigestForMode(
                childState.snapshot,
                'full',
            );

        childState.hostMetadataDigest =
            metadataDigest(
                childState.chatMetadata,
            );

        const childEvent =
            recordEvent(
                childState,
                {
                    type:
                        'branch_bootstrap',
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    parentScope:
                        clone(parentScope),
                    branchKind,
                },
            );

        try {
            await persistState(
                req,
                childScope,
                childState,
            );
        } catch {
            await restoreAfterPersistFailure(
                req,
                childScope,
                childState,
            );

            return {
                status: 507,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'persistence_failed',
                        message:
                            'Branch state could not be durably persisted.',
                    },
                },
            };
        }

        publish(
            childScope,
            'sync',
            {
                epoch:
                    childState.epoch,
                event:
                    childEvent,
                state:
                    serializePublicState(
                        childState,
                    ),
            },
            childEvent.id,
        );
    }

    const duplicateBranch =
        parentState.branches.some(
            branch =>
                branch.childChatId
                    === childScope.chatId
                && branch.branchId
                    === childScope.branchId,
        );

    if (duplicateBranch) {
        return {
            status: 200,
            event: null,
            childScope,
            childState:
                serializePublicState(
                    childState,
                ),
            unchanged: true,
        };
    }

    parentState.revision++;

    const record = {
        childScope:
            clone(childScope),
        parentChatId:
            parentScope.chatId,
        childChatId:
            childScope.chatId,
        branchId:
            childScope.branchId,
        branchKind,
        nativeMainChat:
            childScope.parentChatId,
        createdAt: now(),
    };

    parentState.branches =
        parentState.branches.filter(
            branch =>
                !(
                    branch.childChatId
                        === record.childChatId
                    && branch.branchId
                        === record.branchId
                ),
        );

    parentState.branches.push(
        record,
    );

    if (
        parentState.branches.length
        > LIMITS.maxBranches
    ) {
        parentState.branches.splice(
            0,
            parentState.branches.length
                - LIMITS.maxBranches,
        );
    }

    const event =
        recordEvent(
            parentState,
            {
                type:
                    'branch_announce',
                opId:
                    body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                branch:
                    clone(record),
            },
        );

    return {
        status: 200,
        event,
        childScope,
        childState:
            serializePublicState(
                childState,
            ),
    };
}

async function processGenerationEvent(
    req,
    scope,
    state,
    body,
) {
    const expiredGeneration =
        expireGeneration(state);

    if (body.type === 'generation_claim') {
        if (state.generation) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_busy',
                        message:
                            'Another synchronized client currently owns generation.',
                        currentGeneration:
                            clone(
                                state.generation,
                            ),
                    },
                },
            };
        }

        const generationId =
            body.generationId
            && validateGenerationId(
                body.generationId,
            )
                ? String(
                    body.generationId,
                )
                : randomId('g_');

        const generationType =
            String(
                body.generationType
                || 'normal',
            ).slice(0, 64);

        if (
            !safeId(
                generationType,
                64,
            )
            || generationType === 'quiet'
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_generation_type',
                        message:
                            'generationType is invalid for synchronized generation.',
                    },
                },
            };
        }

        if (
            generationType === 'group'
            && scope.kind !== 'group'
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_generation_type',
                        message:
                            'Group generation requires a group scope.',
                    },
                },
            };
        }

        const requestedMessageId =
            body.messageId
                ? String(body.messageId)
                : null;

        if (
            requestedMessageId
            && !safeId(
                requestedMessageId,
                128,
            )
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_message_id',
                        message:
                            'messageId is invalid.',
                    },
                },
            };
        }

        if (
            state.recoverableGeneration
                ?.generation?.id
                === generationId
        ) {
            state.recoverableGeneration = null;
            state.pendingGenerationRecovery = null;
        }

        state.generation = {
            id: generationId,
            ownerClientId:
                body.clientId,
            ownerDeviceId:
                body.deviceId,
            generationType,
            phase:
                'claimed',
            startedAt: now(),
            leaseUntil:
                now()
                + LIMITS.generationLeaseMs,
            streamSeq: 0,
            messageId:
                requestedMessageId,
            streamMessage:
                null,
            streamMessages: [],
            stopRequested:
                false,
            serverInstanceId,
            lastPersistedStreamSeq:
                0,
            lastPersistedAt:
                now(),
        };

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_claim',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generation:
                        clone(
                            state.generation,
                        ),
                    ...(expiredGeneration
                        ? {
                            recoveredGeneration:
                                expiredGeneration,
                        }
                        : {}),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (!state.generation) {
        if (
            body.type ===
                'generation_terminal'
            && state.recoverableGeneration
                ?.generation?.id
                === String(
                    body.generationId
                    || '',
                )
        ) {
            body.type =
                'generation_terminal_recover';

            return processGenerationEvent(
                req,
                scope,
                state,
                body,
            );
        }

        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'no_generation',
                    message:
                        'There is no active synchronized generation.',
                },
            },
        };
    }

    if (
        String(
            body.generationId || '',
        ) !== state.generation.id
    ) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'generation_mismatch',
                    message:
                        'The supplied generation ID does not match the active generation.',
                },
            },
        };
    }

    if (
        body.type ===
        'generation_heartbeat'
    ) {
        if (
            !isGenerationOwner(
                state,
                body,
            )
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the current generation owner can renew generation.',
                    },
                },
            };
        }

        state.generation.leaseUntil =
            now()
            + LIMITS.generationLeaseMs;

        state.updatedAt = now();
        ensureGenerationShape(state);

        return {
            status: 200,
            event: null,
        };
    }

    if (
        body.type ===
        'generation_started'
    ) {
        if (
            !isGenerationOwner(
                state,
                body,
            )
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the generation owner can acknowledge generation start.',
                    },
                },
            };
        }

        if (
            ![
                'claimed',
                'started',
                'streaming',
            ].includes(
                state.generation.phase,
            )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_invalid_phase',
                        message:
                            'Generation is not in a startable phase.',
                    },
                },
            };
        }

        const messageId =
            body.messageId === undefined
            || body.messageId === null
            || body.messageId === ''
                ? null
                : String(
                    body.messageId,
                );

        if (
            messageId
            && !safeId(
                messageId,
                128,
            )
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_message_id',
                        message:
                            'messageId is invalid.',
                    },
                },
            };
        }

        state.generation.phase =
            'started';

        state.generation.leaseUntil =
            now()
            + LIMITS.generationLeaseMs;

        if (messageId) {
            state.generation.messageId =
                messageId;
        }

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_started',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generation:
                        clone(
                            state.generation,
                        ),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_input'
    ) {
        if (
            !isGenerationOwner(
                state,
                body,
            )
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the generation owner can publish generation input.',
                    },
                },
            };
        }

        if (
            ![
                'claimed',
                'started',
                'streaming',
            ].includes(
                state.generation.phase,
            )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_invalid_phase',
                        message:
                            'Generation input cannot be published in the current phase.',
                    },
                },
            };
        }

        const revision =
            revisionCheck(
                state,
                body,
            );

        if (!revision.ok) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: revision,
                },
            };
        }

        const validation =
            validateSnapshot(
                body.snapshot,
            );

        if (!validation.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_generation_input',
                        message:
                            validation.error,
                    },
                },
            };
        }

        if (
            !hasCompleteMessageIds(
                body.snapshot,
            )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'message_ids_required',
                        message:
                            'All generation input messages must have synchronization IDs.',
                    },
                },
            };
        }

        const metadata =
            body.chatMetadata === undefined
                ? clone(
                    state.chatMetadata,
                )
                : clone(
                    body.chatMetadata,
                );

        const metadataCheck =
            validateMetadata(
                metadata,
            );

        if (!metadataCheck.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_metadata',
                        message:
                            metadataCheck.error,
                    },
                },
            };
        }

        if (
            scope.branchId
            && String(
                metadata.integrity || '',
            ) !== String(scope.branchId)
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.integrity
                                ? 'branch_integrity_mismatch'
                                : 'branch_integrity_missing',
                        message:
                            metadata.integrity
                                ? 'Branch integrity does not match this synchronized branch.'
                                : 'Branch integrity metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        if (
            scope.parentChatId
            && String(
                metadata.main_chat || '',
            ) !== String(
                scope.parentChatId,
            )
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.main_chat
                                ? 'branch_parent_mismatch'
                                : 'branch_parent_missing',
                        message:
                            metadata.main_chat
                                ? 'Branch parent does not match this synchronized scope.'
                                : 'Branch parent metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        const host =
            await readHostChat(
                req,
                scope,
            );

        const hostCheck =
            hostDigestCheck(
                host,
                body,
            );

        if (!hostCheck.ok) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: hostCheck,
                },
            };
        }

        const previous =
            clone(state.snapshot);

        const next =
            applySyncPolicy(
                body.snapshot,
                state.snapshot,
                body.syncSwipes !== false,
            );

        const snapshotChanged =
            !snapshotEquivalentForPolicy(
                previous,
                next,
                body.syncSwipes !== false,
            );

        const metadataChanged =
            canonicalJson(
                state.chatMetadata || {},
            ) !== canonicalJson(
                metadata,
            );

        if (
            snapshotChanged
            || metadataChanged
        ) {
            state.revision++;
            state.snapshot = next;
            state.chatMetadata =
                metadata;

            state.hostSnapshotDigest =
                snapshotDigestForMode(
                    next,
                    body.syncSwipes === false
                        ? 'relevant'
                        : 'full',
                );

            state.hostMetadataDigest =
                metadataDigest(
                    metadata,
                );

            state.tombstones.push(
                ...computeTombstones(
                    previous,
                    next,
                    state.revision,
                ),
            );
        }

        state.generation.phase =
            'started';

        state.generation.leaseUntil =
            now()
            + LIMITS.generationLeaseMs;

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_input',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generationId:
                        state.generation.id,
                    snapshot:
                        clone(state.snapshot),
                    chatMetadata:
                        clone(state.chatMetadata),
                    generation:
                        clone(
                            state.generation,
                        ),
                    stateDigest:
                        sha256(
                            canonicalJson(
                                state.snapshot,
                            ),
                        ),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_stream'
    ) {
        if (
            !isGenerationOwner(
                state,
                body,
            )
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the generation owner can stream generation updates.',
                    },
                },
            };
        }

        if (
            ![
                'started',
                'streaming',
            ].includes(
                state.generation.phase,
            )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_not_started',
                        message:
                            'Generation has not started.',
                    },
                },
            };
        }

        const streamSeq =
            Number(
                body.streamSeq,
            );

        if (
            !Number.isInteger(streamSeq)
            || streamSeq !==
                Number(
                    state.generation
                        .streamSeq
                    || 0,
                ) + 1
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'stream_sequence_gap',
                        message:
                            'Stream sequence must advance contiguously.',
                        expected:
                            Number(
                                state.generation
                                    .streamSeq
                                || 0,
                            ) + 1,
                    },
                },
            };
        }

        if (!isObject(body.message)) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_stream_message',
                        message:
                            'A streamed generation message is required.',
                    },
                },
            };
        }

        const validation =
            validateSnapshot([
                body.message,
            ]);

        if (!validation.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_stream_message',
                        message:
                            validation.error,
                    },
                },
            };
        }

        if (
            !hasCompleteMessageIds([
                body.message,
            ])
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'message_ids_required',
                        message:
                            'Streamed messages must have synchronization IDs.',
                    },
                },
            };
        }

        if (
            bytes(body.message)
            > LIMITS.maxLiveGenerationBytes
        ) {
            return {
                status: 413,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_stream_message_too_large',
                        message:
                            'The streamed generation message is too large.',
                    },
                },
            };
        }

        const message =
            applySyncPolicy(
                [body.message],
                state.generation.streamMessages
                    .map(entry => entry.message),
                body.syncSwipes !== false,
            )[0];

        const messageId =
            getMessageId(message);

        if (!messageId) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_stream_message_id',
                        message:
                            'Stream message has no valid synchronization ID.',
                    },
                },
            };
        }

        if (
            body.messageId !== undefined
            && String(
                body.messageId,
            ) !== String(messageId)
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'stream_message_id_mismatch',
                        message:
                            'messageId does not match the streamed message.',
                    },
                },
            };
        }

        if (
            state.generation
                .generationType
                !== 'group'
            && state.generation.messageId
            && state.generation.messageId
                !== messageId
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_message_mismatch',
                        message:
                            'A single-message generation cannot stream a different message ID.',
                    },
                },
            };
        }

        state.generation.messageId ||=
            messageId;

        state.generation.streamSeq =
            streamSeq;

        state.generation.phase =
            'streaming';

        state.generation.leaseUntil =
            now()
            + LIMITS.generationLeaseMs;

        const entries =
            Array.isArray(
                state.generation.streamMessages,
            )
                ? state.generation
                    .streamMessages
                : [];

        const index =
            entries.findIndex(
                entry =>
                    entry.messageId
                    === messageId,
            );

        const replacement = {
            messageId,
            message:
                clone(message),
        };

        if (index >= 0) {
            entries[index] =
                replacement;
        } else {
            entries.push(
                replacement,
            );
        }

        state.generation.streamMessages =
            entries;

        ensureGenerationShape(
            state,
        );

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_stream',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generationId:
                        state.generation.id,
                    streamSeq,
                    messageId,
                    message:
                        clone(message),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_stop_request'
    ) {
        state.generation.stopRequested =
            true;

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_stop_request',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generationId:
                        state.generation.id,
                    reason:
                        String(
                            body.reason
                            || 'remote_stop',
                        ).slice(0, 256),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_terminal_recover'
    ) {
        const recoverable =
            state.recoverableGeneration
                ?.generation;

        if (state.generation) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_busy',
                        message:
                            'A new generation is already active.',
                    },
                },
            };
        }

        if (
            !recoverable
            || recoverable.id
                !== String(
                    body.generationId
                    || '',
                )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_recovery_unavailable',
                        message:
                            'The expired generation can no longer be safely recovered.',
                    },
                },
            };
        }

        if (
            recoverable.ownerClientId
                !== body.clientId
            || recoverable.ownerDeviceId
                !== body.deviceId
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the original generation owner can recover the generation.',
                    },
                },
            };
        }

        const baseRevision =
            Number(
                body.baseRevision,
            );

        if (
            !Number.isInteger(
                baseRevision,
            )
            || baseRevision
                !== state.revision
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'revision_conflict',
                        message:
                            'The chat changed while the generation was disconnected.',
                        currentRevision:
                            state.revision,
                    },
                },
            };
        }

        const validation =
            validateSnapshot(
                body.snapshot,
            );

        if (!validation.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_snapshot',
                        message:
                            validation.error,
                    },
                },
            };
        }

        if (
            !hasCompleteMessageIds(
                body.snapshot,
            )
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'message_ids_required',
                        message:
                            'All messages must have synchronization IDs.',
                    },
                },
            };
        }

        const metadata =
            body.chatMetadata === undefined
                ? clone(
                    state.chatMetadata,
                )
                : clone(
                    body.chatMetadata,
                );

        const metadataCheck =
            validateMetadata(
                metadata,
            );

        if (!metadataCheck.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_metadata',
                        message:
                            metadataCheck.error,
                    },
                },
            };
        }

        if (
            scope.branchId
            && String(
                metadata.integrity || '',
            ) !== String(scope.branchId)
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.integrity
                                ? 'branch_integrity_mismatch'
                                : 'branch_integrity_missing',
                        message:
                            metadata.integrity
                                ? 'Branch integrity does not match this synchronized branch.'
                                : 'Branch integrity metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        if (
            scope.parentChatId
            && String(
                metadata.main_chat || '',
            ) !== String(
                scope.parentChatId,
            )
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.main_chat
                                ? 'branch_parent_mismatch'
                                : 'branch_parent_missing',
                        message:
                            metadata.main_chat
                                ? 'Branch parent does not match this synchronized scope.'
                                : 'Branch parent metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        const host =
            await readHostChat(
                req,
                scope,
            );

        const hostCheck =
            hostDigestCheck(
                host,
                body,
            );

        if (!hostCheck.ok) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: hostCheck,
                },
            };
        }

        const previous =
            clone(state.snapshot);

        const next =
            applySyncPolicy(
                body.snapshot,
                state.snapshot,
                body.syncSwipes !== false,
            );

        const changed =
            !snapshotEquivalentForPolicy(
                previous,
                next,
                body.syncSwipes !== false,
            )
            || canonicalJson(
                state.chatMetadata
                || {},
            )
                !== canonicalJson(
                    metadata,
                );

        if (changed) {
            state.revision++;
            state.snapshot = next;
            state.chatMetadata =
                metadata;

            state.hostSnapshotDigest =
                snapshotDigestForMode(
                    next,
                    body.syncSwipes === false
                        ? 'relevant'
                        : 'full',
                );

            state.hostMetadataDigest =
                metadataDigest(
                    metadata,
                );

            state.tombstones.push(
                ...computeTombstones(
                    previous,
                    next,
                    state.revision,
                ),
            );
        }

        const finalGeneration = {
            ...clone(
                recoverable,
            ),
            phase:
                [
                    'completed',
                    'stopped',
                    'failed',
                ].includes(
                    body.status,
                )
                    ? body.status
                    : 'failed',
            leaseUntil:
                now(),
        };

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_terminal_recover',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generationId:
                        finalGeneration.id,
                    generation:
                        finalGeneration,
                    status:
                        finalGeneration.phase,
                    snapshot:
                        clone(
                            state.snapshot,
                        ),
                    chatMetadata:
                        clone(
                            state.chatMetadata,
                        ),
                    recovered: true,
                },
            );

        state.recoverableGeneration =
            null;

        state.pendingGenerationRecovery =
            null;

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_terminal'
    ) {
        if (
            !isGenerationOwner(
                state,
                body,
            )
        ) {
            return {
                status: 403,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'not_generation_owner',
                        message:
                            'Only the generation owner can finalize generation.',
                    },
                },
            };
        }

        const status =
            [
                'completed',
                'stopped',
                'failed',
            ].includes(
                body.status,
            )
                ? body.status
                : 'failed';

        if (
            body.snapshot === undefined
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'final_snapshot_required',
                        message:
                            'A final chat snapshot is required when generation terminates.',
                    },
                },
            };
        }

        const validation =
            validateSnapshot(
                body.snapshot,
            );

        if (!validation.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_snapshot',
                        message:
                            validation.error,
                    },
                },
            };
        }

        const metadata =
            body.chatMetadata === undefined
                ? clone(
                    state.chatMetadata,
                )
                : clone(
                    body.chatMetadata,
                );

        const metadataCheck =
            validateMetadata(
                metadata,
            );

        if (!metadataCheck.ok) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'invalid_metadata',
                        message:
                            metadataCheck.error,
                    },
                },
            };
        }

        if (
            scope.branchId
            && String(
                metadata.integrity || '',
            ) !== String(scope.branchId)
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.integrity
                                ? 'branch_integrity_mismatch'
                                : 'branch_integrity_missing',
                        message:
                            metadata.integrity
                                ? 'Branch integrity does not match this synchronized branch.'
                                : 'Branch integrity metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        if (
            scope.parentChatId
            && String(
                metadata.main_chat || '',
            ) !== String(
                scope.parentChatId,
            )
        ) {
            return {
                status: 400,
                payload: {
                    ok: false,
                    error: {
                        code:
                            metadata.main_chat
                                ? 'branch_parent_mismatch'
                                : 'branch_parent_missing',
                        message:
                            metadata.main_chat
                                ? 'Branch parent does not match this synchronized scope.'
                                : 'Branch parent metadata is required for this synchronized branch.',
                    },
                },
            };
        }

        const host =
            await readHostChat(
                req,
                scope,
            );

        const hostCheck =
            hostDigestCheck(
                host,
                body,
            );

        if (!hostCheck.ok) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: hostCheck,
                },
            };
        }

        const previous =
            clone(state.snapshot);

        const next =
            applySyncPolicy(
                body.snapshot,
                state.snapshot,
                body.syncSwipes !== false,
            );

        const snapshotChanged =
            !snapshotEquivalentForPolicy(
                previous,
                next,
                body.syncSwipes !== false,
            );

        const metadataChanged =
            canonicalJson(
                state.chatMetadata || {},
            ) !== canonicalJson(
                metadata,
            );

        if (
            snapshotChanged
            || metadataChanged
        ) {
            state.revision++;
            state.snapshot = next;
            state.chatMetadata =
                metadata;

            state.hostSnapshotDigest =
                snapshotDigestForMode(
                    next,
                    body.syncSwipes === false
                        ? 'relevant'
                        : 'full',
                );

            state.hostMetadataDigest =
                metadataDigest(
                    metadata,
                );

            state.tombstones.push(
                ...computeTombstones(
                    previous,
                    next,
                    state.revision,
                ),
            );
        }

        const finalGeneration =
            clone(
                state.generation,
            );

        finalGeneration.phase =
            status;

        finalGeneration.leaseUntil =
            now();

        ensureGenerationShape({
            generation:
                finalGeneration,
        });

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_terminal',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    generationId:
                        finalGeneration.id,
                    generation:
                        finalGeneration,
                    status,
                    snapshot:
                        clone(
                            state.snapshot,
                        ),
                    chatMetadata:
                        clone(
                            state.chatMetadata,
                        ),
                },
            );

        state.generation = null;
        state.recoverableGeneration = null;
        state.pendingGenerationRecovery = null;

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type ===
        'generation_recover'
    ) {
        if (state.generation) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_not_expired',
                        message:
                            'Generation has not expired yet.',
                    },
                },
            };
        }

        const previousGeneration =
            expiredGeneration
            || state.recoverableGeneration
                ?.generation
            || null;

        state.pendingGenerationRecovery =
            null;

        state.recoverableGeneration =
            null;

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_recover',
                    opId:
                        body.opId,
                    source: {
                        clientId:
                            body.clientId,
                        deviceId:
                            body.deviceId,
                    },
                    previousGeneration:
                        clone(
                            previousGeneration,
                        ),
                    recovered:
                        !!previousGeneration,
                },
            );

        return {
            status: 200,
            event,
            recovered:
                !!previousGeneration,
        };
    }

    return {
        status: 400,
        payload: {
            ok: false,
            error: {
                code:
                    'invalid_generation_event',
                message:
                    'Unsupported generation event type.',
            },
        },
    };
}

async function processChatRenamed(
    req,
    scope,
    state,
    body,
) {
    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
            },
        };
    }

    const newChatId =
        String(
            body.newChatId || '',
        ).trim();

    if (
        !safeName(newChatId)
        || newChatId === scope.chatId
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_new_chat_id',
                    message:
                        'newChatId is invalid.',
                },
            },
        };
    }

    const targetScope = {
        ...clone(scope),
        chatId: newChatId,
    };

    const validation =
        await validateScopeAgainstHost(
            req,
            targetScope,
        );

    if (!validation.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'rename_target_invalid',
                    message:
                        'The renamed chat could not be resolved on the server.',
                    detail:
                        validation.code,
                },
            },
        };
    }

    const targetHost =
        await readHostChat(
            req,
            targetScope,
        );

    if (
        !targetHost.ok
        || !targetHost.exists
    ) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: {
                    code:
                        'rename_target_missing',
                    message:
                        'The renamed chat file is not available on the server yet.',
                },
            },
        };
    }

    state.revision++;

    state.renamedTo = {
        chatId:
            newChatId,
        scope:
            targetScope,
        renamedAt:
            now(),
    };

    const event =
        recordEvent(
            state,
            {
                type:
                    'chat_renamed',
                opId:
                    body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                oldChatId:
                    scope.chatId,
                newChatId,
                newScope:
                    targetScope,
            },
        );

    return {
        status: 200,
        event,
    };
}

async function processChatDeleted(
    scope,
    state,
    body,
    type = 'chat_deleted',
) {
    const revision =
        revisionCheck(
            state,
            body,
        );

    if (!revision.ok) {
        return {
            status: 409,
            payload: {
                ok: false,
                error: revision,
            },
        };
    }

    state.revision++;
    state.deleted = true;

    const event =
        recordEvent(
            state,
            {
                type,
                opId:
                    body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                chatId:
                    scope.chatId,
                deletedAt:
                    now(),
            },
        );

    return {
        status: 200,
        event,
    };
}

async function handleEvent(req, res) {
    if (requestBodyTooLarge(req)) {
        return sendError(
            res,
            413,
            'request_too_large',
            'Request is too large.',
        );
    }

    let scope;

    try {
        scope = normalizeScope(
            req,
            req.body?.scope,
        );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_scope',
            error.message,
        );
    }

    const body = req.body || {};

    if (
        Number(body.protocol)
            !== PROTOCOL
        || Number(body.schema)
            !== SCHEMA
    ) {
        return sendError(
            res,
            409,
            'protocol_mismatch',
            'Synchronization protocol/schema mismatch.',
            {
                expectedProtocol:
                    PROTOCOL,
                expectedSchema:
                    SCHEMA,
            },
        );
    }

    if (
        !ALL_EVENT_TYPES.has(
            body.type,
        )
    ) {
        return sendError(
            res,
            400,
            'invalid_event_type',
            'Unsupported synchronization event type.',
        );
    }

    const clientId =
        String(
            body.clientId || '',
        );

    const deviceId =
        String(
            body.deviceId || '',
        );

    const opId =
        String(
            body.opId || '',
        );

    if (
        !safeId(clientId, 128)
        || !safeId(deviceId, 128)
        || !safeId(opId, 160)
    ) {
        return sendError(
            res,
            400,
            'invalid_client',
            'clientId, deviceId, and opId are required.',
        );
    }

    if (
        !isMember(
            scope,
            clientId,
            deviceId,
        )
    ) {
        return sendError(
            res,
            403,
            'not_member',
            'Client is not an active member of this scope.',
        );
    }

    if (
        !rateAllowed(
            scope,
            clientId,
        )
    ) {
        return sendError(
            res,
            429,
            'rate_limited',
            'Too many synchronization operations.',
        );
    }

    return withScopeLock(
        scope,
        async () => {
            if (
                !requireCurrentMember(
                    scope,
                    clientId,
                    deviceId,
                )
            ) {
                return sendError(
                    res,
                    403,
                    'not_member',
                    'Client is no longer an active member of this scope.',
                );
            }

            const state =
                await loadState(
                    req,
                    scope,
                );

            const cached =
                findCachedOperation(
                    state,
                    opId,
                );

            if (cached) {
                return res.json(
                    cachedResultResponse(
                        state,
                        cached,
                    ),
                );
            }

            if (
                state.generation
                && [
                    'snapshot',
                    'metadata',
                    'message_delete',
                    'reconcile_local',
                    'group_settings',
                    'branch_announce',
                    'chat_renamed',
                    'chat_deleted',
                    'group_chat_deleted',
                ].includes(
                    body.type,
                )
            ) {
                return res.status(409).json({
                    ok: false,
                    error: {
                        code:
                            'generation_active',
                        message:
                            'The synchronized chat is currently generating; ordinary chat mutations must wait for generation to finish.',
                    },
                    generation:
                        clone(
                            state.generation,
                        ),
                });
            }

            let result;

            try {
                if (
                    GENERATION_TYPES.has(
                        body.type,
                    )
                ) {
                    result =
                        await processGenerationEvent(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type ===
                    'chat_renamed'
                ) {
                    result =
                        await processChatRenamed(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type ===
                    'chat_deleted'
                ) {
                    result =
                        await processChatDeleted(
                            scope,
                            state,
                            body,
                            'chat_deleted',
                        );
                } else if (
                    body.type ===
                    'group_chat_deleted'
                ) {
                    result =
                        await processChatDeleted(
                            scope,
                            state,
                            body,
                            'group_chat_deleted',
                        );
                } else if (
                    body.type ===
                    'message_delete'
                ) {
                    result =
                        await processMessageDelete(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type ===
                    'metadata'
                ) {
                    result =
                        await processMetadataMutation(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type ===
                    'group_settings'
                ) {
                    result =
                        await processGroupSettings(
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type ===
                    'branch_announce'
                ) {
                    result =
                        await processBranchAnnouncement(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else {
                    result =
                        await processSnapshotMutation(
                            req,
                            scope,
                            state,
                            body,
                        );
                }
            } catch {
                return sendError(
                    res,
                    500,
                    'internal_error',
                    'Synchronization operation failed.',
                );
            }

            if (result.payload) {
                return res
                    .status(result.status)
                    .json(
                        result.payload,
                    );
            }

            state.updatedAt = now();

            rememberOperation(
                state,
                opId,
                {
                    ok: true,
                    eventId:
                        result.event?.id
                        || 0,
                    revision:
                        state.revision,
                    epoch:
                        state.epoch,
                    generation:
                        state.generation,
                },
                body.type,
            );

            if (
                shouldPersistEvent(
                    state,
                    body.type,
                )
            ) {
                try {
                    await persistState(
                        req,
                        scope,
                        state,
                    );
                } catch {
                    await restoreAfterPersistFailure(
                        req,
                        scope,
                        state,
                    );

                    return sendError(
                        res,
                        507,
                        'persistence_failed',
                        'Synchronization state could not be durably persisted.',
                    );
                }
            }

            const publicState =
                serializePublicState(
                    state,
                );

            if (result.event) {
                const liveOnly = [
                    'generation_claim',
                    'generation_started',
                    'generation_heartbeat',
                    'generation_stream',
                    'generation_stop_request',
                ].includes(
                    String(
                        result.event.type
                        || '',
                    ),
                );

                publish(
                    scope,
                    'sync',
                    {
                        epoch:
                            state.epoch,
                        event:
                            clone(
                                result.event,
                            ),
                        state:
                            serializePublicState(
                                state,
                                {
                                    includeSnapshot:
                                        !liveOnly,
                                    includeGenerationStream:
                                        !liveOnly,
                                },
                            ),
                    },
                    result.event.id,
                );
            }

            const responseLiveOnly = [
                'generation_claim',
                'generation_started',
                'generation_heartbeat',
                'generation_stream',
                'generation_stop_request',
            ].includes(
                String(
                    body.type || '',
                ),
            );

            const responseState =
                responseLiveOnly
                    ? serializePublicState(
                        state,
                        {
                            includeSnapshot:
                                false,
                            includeGenerationStream:
                                false,
                        },
                    )
                    : publicState;

            return res.json({
                ok: true,
                protocol:
                    PROTOCOL,
                schema:
                    SCHEMA,
                revision:
                    state.revision,
                epoch:
                    state.epoch,
                eventId:
                    result.event?.id
                    || 0,
                event:
                    clone(
                        result.event,
                    ),
                generation:
                    clone(
                        state.generation,
                    ),
                state:
                    responseState,
                ...(result.childScope
                    ? {
                        childScope:
                            clone(
                                result.childScope,
                            ),
                        childState:
                            clone(
                                result.childState,
                            ),
                    }
                    : {}),
            });
        },
    );
}

async function handleHealth(req, res) {
    const userId =
        userIdFromRequest(req);

    if (!userId) {
        return sendError(
            res,
            401,
            'unauthenticated',
            'SillyTavern authentication is required.',
        );
    }

    return res.json({
        ok: true,
        plugin:
            info.id,
        version:
            '1.7.0',
        protocol:
            PROTOCOL,
        schema:
            SCHEMA,
        userId,
        node:
            process.version,
        storage: true,
        scopes:
            scopes.size,
        sse:
            totalSseConnections,
        serverInstanceId,
        shuttingDown,
    });
}

async function init(router) {
    shuttingDown = false;

    cleanupTimer = setInterval(
        async () => {
            for (const [key, map] of members) {
                const cutoff =
                    now()
                    - LIMITS.memberTtlMs;

                for (
                    const [
                        clientId,
                        member,
                    ] of map
                ) {
                    if (
                        member.lastSeen
                        < cutoff
                    ) {
                        map.delete(
                            clientId,
                        );
                    }
                }

                if (!map.size) {
                    members.delete(
                        key,
                    );
                }
            }

            const cutoff = now();

            for (
                const [
                    key,
                    window,
                ] of rateWindows
            ) {
                if (
                    window.expiresAt
                    <= cutoff
                ) {
                    rateWindows.delete(
                        key,
                    );
                }
            }

            for (
                const [
                    key,
                    state,
                ] of scopes
            ) {
                const recovered =
                    recoverExpiredGenerationEvent(
                        state,
                        {
                            clientId:
                                'server',
                            deviceId:
                                'server',
                        },
                        'expired_on_cleanup',
                    );

                if (!recovered) continue;

                const file =
                    stateFiles.get(
                        key,
                    );

                if (file) {
                    try {
                        await atomicWrite(
                            file,
                            state,
                        );
                    } catch {}
                }

                publish(
                    state.scope,
                    'sync',
                    {
                        epoch:
                            state.epoch,
                        event:
                            clone(
                                recovered,
                            ),
                        state:
                            serializePublicState(
                                state,
                            ),
                    },
                    recovered.id,
                );
            }

            await Promise.resolve();
        },
        10 * 60_000,
    );

    cleanupTimer.unref?.();

    router.get(
        '/health',
        handleHealth,
    );

    router.post(
        '/join',
        handleJoin,
    );

    router.post(
        '/leave',
        handleLeave,
    );

    router.post(
        '/heartbeat',
        handleHeartbeat,
    );

    router.get(
        '/state',
        stateResponse,
    );

    router.post(
        '/state',
        stateResponse,
    );

    router.get(
        '/events',
        handleSse,
    );

    router.post(
        '/event',
        handleEvent,
    );

    console.log(
        `[multi-client-sync] loaded protocol=${PROTOCOL} schema=${SCHEMA}`,
    );
}

async function exit() {
    shuttingDown = true;

    if (cleanupTimer) {
        clearInterval(
            cleanupTimer,
        );
    }

    for (
        const [
            token,
            subscription,
        ] of subscriptions
    ) {
        if (subscription.res) {
            try {
                writeSse(
                    subscription.res,
                    'shutdown',
                    {
                        reason:
                            'server_shutdown',
                    },
                );
            } catch {}
        }

        closeSubscription(
            token,
        );
    }

    const pending = [];

    for (const state of scopes.values()) {
        if (state.generation) {
            state.recoverableGeneration =
                {
                    generation:
                        clone(
                            state.generation,
                        ),
                    expiredAt:
                        now(),
                    reason:
                        'server_shutdown',
                    serverInstanceId,
                };

            state.pendingGenerationRecovery =
                {
                    reason:
                        'server_shutdown',
                    previousGeneration:
                        clone(
                            state.generation,
                        ),
                };

            state.generation = null;

            const recovery =
                consumePendingGenerationRecovery(
                    state,
                    {
                        clientId:
                            'server',
                        deviceId:
                            'server',
                    },
                );

            if (recovery) {
                state.events.push(
                    recovery,
                );
            }
        }

        state.serverInstanceId =
            serverInstanceId;

        state.updatedAt = now();

        const key =
            scopeKey(
                state.scope,
            );

        const file =
            stateFiles.get(
                key,
            );

        if (!file) continue;

        const snapshot =
            clone(state);

        pruneState(snapshot);

        pending.push(
            (async () => {
                const content =
                    canonicalJson(
                        snapshot,
                    );

                if (
                    Buffer.byteLength(
                        content,
                        'utf8',
                    )
                    > LIMITS.maxPersistedStateBytes
                ) {
                    return;
                }

                await atomicWrite(
                    file,
                    snapshot,
                );
            })().catch(() => {}),
        );
    }

    await Promise.allSettled(
        pending,
    );

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
    userRateWindows.clear();

    totalSseConnections = 0;
}

module.exports = {
    init,
    exit,
    info,
};