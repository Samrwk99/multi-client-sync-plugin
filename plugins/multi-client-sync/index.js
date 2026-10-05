'use strict';

const fs = require('node:fs');
const fsp = fs.promises;
const path = require('node:path');
const crypto = require('node:crypto');

const PROTOCOL = 6;
const SCHEMA = 6;

const info = {
    id: 'multi-client-sync',
    name: 'Multi-Client Chat Synchronization',
    description: 'Authenticated, per-chat synchronization and generation coordination for SillyTavern clients.',
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

const FORBIDDEN_KEYS = new Set([
    '__proto__',
    'prototype',
    'constructor',
]);

const MUTATION_TYPES = new Set([
    'snapshot',
    'metadata',
    'reconcile_local',
    'group_settings',
    'branch_announce',
]);

const GENERATION_TYPES = new Set([
    'generation_claim',
    'generation_heartbeat',
    'generation_started',
    'generation_stream',
    'generation_stop_request',
    'generation_terminal',
    'generation_recover',
]);

const ALL_EVENT_TYPES = new Set([
    ...MUTATION_TYPES,
    ...GENERATION_TYPES,
]);

const scopes = new Map();
const members = new Map();
const subscriptions = new Map();
const operationChains = new Map();
const persistenceChains = new Map();
const rateWindows = new Map();

let totalSseConnections = 0;
let shuttingDown = false;
let cleanupTimer = null;

function now() {
    return Date.now();
}

function randomId(prefix = '') {
    return `${prefix}${crypto.randomBytes(18).toString('hex')}`;
}

function sha256(value) {
    return crypto
        .createHash('sha256')
        .update(String(value))
        .digest('hex');
}

function stableJson(value) {
    return JSON.stringify(value);
}

function bytes(value) {
    return Buffer.byteLength(
        stableJson(value),
        'utf8',
    );
}

function isObject(value) {
    return value !== null
        && typeof value === 'object'
        && !Array.isArray(value);
}

function clone(value) {
    return structuredClone(value);
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

    return target === base
        || target.startsWith(`${base}${path.sep}`);
}

function safeJoin(parent, ...parts) {
    const target =
        path.resolve(
            parent,
            ...parts,
        );

    if (!pathIsUnder(parent, target)) {
        throw new Error(
            'Path escapes allowed directory',
        );
    }

    return target;
}

function userIdFromRequest(req) {
    const handle =
        req?.user?.profile?.handle;

    return typeof handle === 'string'
        && handle.trim()
        ? handle.trim()
        : null;
}

function userRootFromRequest(req) {
    const root =
        req?.user?.directories?.root;

    if (!root) {
        throw new Error(
            'Authenticated user root unavailable',
        );
    }

    return path.resolve(root);
}

function stateRootFromRequest(req) {
    return safeJoin(
        userRootFromRequest(req),
        'multi-client-sync',
        'state',
    );
}

function sendError(
    res,
    status,
    code,
    message,
    extra = {},
) {
    return res.status(status).json({
        ok: false,
        error: {
            code,
            message,
            ...extra,
        },
    });
}

function requestBodyTooLarge(req) {
    try {
        return bytes(req.body ?? {}) >
            LIMITS.maxRequestBytes;
    } catch {
        return true;
    }
}

function validateDataTree(
    value,
    depth = 0,
    seen = new WeakSet(),
) {
    if (depth > 40) {
        return false;
    }

    if (
        value === null
        || typeof value === 'string'
        || typeof value === 'boolean'
    ) {
        return true;
    }

    if (typeof value === 'number') {
        return Number.isFinite(value);
    }

    if (typeof value !== 'object') {
        return false;
    }

    if (seen.has(value)) {
        return false;
    }

    seen.add(value);

    if (Array.isArray(value)) {
        return value.every(
            child =>
                validateDataTree(
                    child,
                    depth + 1,
                    seen,
                ),
        );
    }

    for (
        const [key, child]
        of Object.entries(value)
    ) {
        if (FORBIDDEN_KEYS.has(key)) {
            return false;
        }

        if (
            !validateDataTree(
                child,
                depth + 1,
                seen,
            )
        ) {
            return false;
        }
    }

    return true;
}

function validateAttachment(
    attachment,
) {
    if (!isObject(attachment)) {
        return false;
    }

    if (
        attachment.url !== undefined
        && (
            typeof attachment.url
            !== 'string'
            || attachment.url.length > 4096
        )
    ) {
        return false;
    }

    if (
        attachment.name !== undefined
        && (
            typeof attachment.name
            !== 'string'
            || attachment.name.length > 1024
        )
    ) {
        return false;
    }

    if (
        attachment.text !== undefined
        && (
            typeof attachment.text
            !== 'string'
            || attachment.text.length > 1_500_000
        )
    ) {
        return false;
    }

    if (
        attachment.size !== undefined
        && (
            !Number.isFinite(
                Number(attachment.size),
            )
            || Number(attachment.size) < 0
        )
    ) {
        return false;
    }

    return true;
}

function validateMessage(
    message,
    index,
) {
    if (!isObject(message)) {
        return `message ${index} is invalid`;
    }

    if (
        message.extra !== undefined
        && !isObject(message.extra)
    ) {
        return `message ${index}.extra is invalid`;
    }

    if (
        !validateDataTree(message)
    ) {
        return `message ${index} contains unsupported values`;
    }

    const syncId =
        message?.extra
            ?.multi_client_sync
            ?.messageId;

    if (
        syncId !== undefined
        && !safeId(
            syncId,
            128,
        )
    ) {
        return `message ${index} has an invalid synchronization ID`;
    }

    if (
        message.swipes !== undefined
        && !Array.isArray(
            message.swipes,
        )
    ) {
        return `message ${index}.swipes is invalid`;
    }

    if (
        Array.isArray(message.swipes)
        && message.swipes.length
            > LIMITS.maxSwipesPerMessage
    ) {
        return `message ${index} has too many swipes`;
    }

    if (
        message.swipe_info !== undefined
        && !Array.isArray(
            message.swipe_info,
        )
    ) {
        return `message ${index}.swipe_info is invalid`;
    }

    if (
        Array.isArray(message.swipe_info)
        && message.swipe_info.length
            > LIMITS.maxSwipesPerMessage
    ) {
        return `message ${index} has too much swipe metadata`;
    }

    if (
        message.swipe_id !== undefined
        && (
            !Number.isInteger(
                Number(message.swipe_id),
            )
            || Number(message.swipe_id) < 0
        )
    ) {
        return `message ${index}.swipe_id is invalid`;
    }

    if (
        Array.isArray(message.swipes)
        && message.swipe_id !== undefined
        && Number(message.swipe_id)
            >= message.swipes.length
    ) {
        return `message ${index}.swipe_id is out of range`;
    }

    const files =
        message?.extra?.files;

    if (
        files !== undefined
        && !Array.isArray(files)
    ) {
        return `message ${index}.extra.files is invalid`;
    }

    if (
        Array.isArray(files)
        && files.length
            > LIMITS.maxFilesPerMessage
    ) {
        return `message ${index} has too many files`;
    }

    if (
        Array.isArray(files)
        && !files.every(
            validateAttachment,
        )
    ) {
        return `message ${index} has an invalid file attachment`;
    }

    const media =
        message?.extra?.media;

    if (
        media !== undefined
        && !Array.isArray(media)
    ) {
        return `message ${index}.extra.media is invalid`;
    }

    if (
        Array.isArray(media)
        && media.length
            > LIMITS.maxMediaPerMessage
    ) {
        return `message ${index} has too much media`;
    }

    if (
        Array.isArray(media)
        && !media.every(
            validateAttachment,
        )
    ) {
        return `message ${index} has invalid media`;
    }

    const tools =
        message?.extra?.tool_invocations;

    if (
        tools !== undefined
        && !Array.isArray(tools)
    ) {
        return `message ${index}.extra.tool_invocations is invalid`;
    }

    if (
        Array.isArray(tools)
        && tools.length
            > LIMITS.maxToolInvocationsPerMessage
    ) {
        return `message ${index} has too many tool invocations`;
    }

    return null;
}

function validateSnapshot(
    snapshot,
) {
    if (!Array.isArray(snapshot)) {
        return {
            ok: false,
            error:
                'snapshot must be an array',
        };
    }

    if (
        snapshot.length
        > LIMITS.maxMessages
    ) {
        return {
            ok: false,
            error: 'too many messages',
        };
    }

    if (
        !validateDataTree(snapshot)
    ) {
        return {
            ok: false,
            error:
                'snapshot contains unsupported values',
        };
    }

    for (
        let index = 0;
        index < snapshot.length;
        index++
    ) {
        const error =
            validateMessage(
                snapshot[index],
                index,
            );

        if (error) {
            return {
                ok: false,
                error,
            };
        }
    }

    if (
        bytes(snapshot)
        > LIMITS.maxSnapshotBytes
    ) {
        return {
            ok: false,
            error:
                'snapshot exceeds payload limit',
        };
    }

    return {
        ok: true,
    };
}

function validateMetadata(
    metadata,
) {
    if (!isObject(metadata)) {
        return {
            ok: false,
            error:
                'chatMetadata must be an object',
        };
    }

    if (
        !validateDataTree(metadata)
    ) {
        return {
            ok: false,
            error:
                'chatMetadata contains unsupported values',
        };
    }

    if (
        bytes(metadata)
        > LIMITS.maxMetadataBytes
    ) {
        return {
            ok: false,
            error:
                'chatMetadata too large',
        };
    }

    return {
        ok: true,
    };
}

function ensureMessageIds(
    snapshot,
) {
    const out =
        clone(snapshot || []);

    const used = new Set();

    for (
        const message
        of out
    ) {
        if (
            !isObject(message.extra)
        ) {
            message.extra = {};
        }

        if (
            !isObject(
                message.extra
                    .multi_client_sync,
            )
        ) {
            message.extra
                .multi_client_sync = {};
        }

        let id =
            message.extra
                .multi_client_sync
                .messageId;

        if (
            !safeId(id, 128)
            || used.has(id)
        ) {
            id = randomId('m_');

            message.extra
                .multi_client_sync
                .messageId = id;
        }

        used.add(id);
    }

    return out;
}

function getMessageId(message) {
    return message?.extra
        ?.multi_client_sync
        ?.messageId
        || null;
}

function normalizeScope(
    req,
    raw,
) {
    const userId =
        userIdFromRequest(req);

    if (!userId) {
        throw new Error(
            'Authentication required',
        );
    }

    if (!isObject(raw)) {
        throw new Error(
            'scope must be an object',
        );
    }

    const kind =
        raw.kind === 'group'
            ? 'group'
            : raw.kind === 'character'
                ? 'character'
                : null;

    if (!kind) {
        throw new Error(
            'scope.kind must be character or group',
        );
    }

    const chatId =
        String(
            raw.chatId ?? '',
        ).trim();

    if (!safeName(chatId)) {
        throw new Error(
            'invalid chatId',
        );
    }

    const branchId =
        raw.branchId
            ? String(raw.branchId).trim()
            : '';

    if (
        branchId
        && !safeId(
            branchId,
            128,
        )
    ) {
        throw new Error(
            'invalid branchId',
        );
    }

    const parentChatId =
        raw.parentChatId
            ? String(
                raw.parentChatId,
            ).trim()
            : '';

    if (
        parentChatId
        && !safeName(parentChatId)
    ) {
        throw new Error(
            'invalid parentChatId',
        );
    }

    if (
        kind === 'character'
    ) {
        const character =
            String(
                raw.character
                ?? '',
            ).trim();

        if (!safeName(character)) {
            throw new Error(
                'invalid character',
            );
        }

        return {
            userId,
            kind,
            character,
            chatId,
            branchId,
            parentChatId,
        };
    }

    const groupId =
        String(
            raw.groupId
            ?? '',
        ).trim();

    if (!safeId(groupId, 256)) {
        throw new Error(
            'invalid groupId',
        );
    }

    return {
        userId,
        kind,
        groupId,
        chatId,
        branchId,
        parentChatId,
    };
}

function scopeKey(scope) {
    return [
        scope.userId,
        scope.kind,
        scope.kind === 'character'
            ? scope.character
            : scope.groupId,
        scope.chatId,
        scope.branchId || 'main',
    ].join('|');
}

function scopeHash(scope) {
    return sha256(
        scopeKey(scope),
    ).slice(0, 40);
}

function storageFile(
    req,
    scope,
) {
    return safeJoin(
        stateRootFromRequest(req),
        `${scopeHash(scope)}.json`,
    );
}

async function ensureStateRoot(req) {
    const root =
        stateRootFromRequest(req);

    await fsp.mkdir(
        root,
        {
            recursive: true,
            mode: 0o700,
        },
    );

    return root;
}

function emptyState(
    scope,
) {
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
    try {
        return JSON.parse(
            await fsp.readFile(
                file,
                'utf8',
            ),
        );
    } catch {
        return null;
    }
}

async function atomicWrite(
    file,
    value,
) {
    const content =
        JSON.stringify(
            value,
        );

    if (
        Buffer.byteLength(
            content,
            'utf8',
        )
        > LIMITS.maxPersistedStateBytes
    ) {
        throw new Error(
            'Persisted synchronization state is too large',
        );
    }

    await fsp.mkdir(
        path.dirname(file),
        {
            recursive: true,
            mode: 0o700,
        },
    );

    const temp =
        `${file}.${process.pid}.${randomId('tmp_')}.tmp`;

    try {
        await fsp.writeFile(
            temp,
            content,
            {
                encoding: 'utf8',
                mode: 0o600,
            },
        );

        await fsp.rename(
            temp,
            file,
        );
    } finally {
        await fsp.rm(
            temp,
            { force: true },
        ).catch(() => {});
    }
}

function pruneState(
    state,
) {
    if (!Array.isArray(state.events)) {
        state.events = [];
    }

    if (
        state.events.length
        > LIMITS.maxEvents
    ) {
        state.events.splice(
            0,
            state.events.length
                - LIMITS.maxEvents,
        );
    }

    if (
        !Array.isArray(
            state.tombstones,
        )
    ) {
        state.tombstones = [];
    }

    if (
        state.tombstones.length
        > LIMITS.maxTombstones
    ) {
        state.tombstones.splice(
            0,
            state.tombstones.length
                - LIMITS.maxTombstones,
        );
    }

    if (
        !Array.isArray(
            state.recentOps,
        )
    ) {
        state.recentOps = [];
    }

    if (
        state.recentOps.length
        > LIMITS.maxRecentOps
    ) {
        state.recentOps.splice(
            0,
            state.recentOps.length
                - LIMITS.maxRecentOps,
        );
    }

    if (
        !Array.isArray(state.snapshot)
    ) {
        state.snapshot = [];
    }

    if (
        !isObject(
            state.chatMetadata,
        )
    ) {
        state.chatMetadata = {};
    }

    if (
        !Array.isArray(state.branches)
    ) {
        state.branches = [];
    }

    if (state.revision === undefined) {
        state.revision = 0;
    }

    if (!state.epoch) {
        state.epoch = randomId('e_');
    }

    if (
        state.generation
        && (
            state.generation.startedAt
            + LIMITS.generationMaxMs
            < now()
            || state.generation.leaseUntil
            < now()
        )
    ) {
        state.generation = null;
    }

    while (
        state.events.length > 1
        && bytes(state)
            > Math.floor(
                LIMITS.maxPersistedStateBytes
                * 0.88,
            )
    ) {
        state.events.shift();
    }
}

function stateIdentityValid(
    state,
    scope,
) {
    return isObject(state)
        && state.protocol === PROTOCOL
        && state.schema === SCHEMA
        && isObject(state.scope)
        && scopeKey(state.scope)
            === scopeKey(scope);
}

async function loadState(
    req,
    scope,
) {
    const key =
        scopeKey(scope);

    const cached =
        scopes.get(key);

    if (cached) {
        return cached;
    }

    if (
        scopes.size
        >= LIMITS.maxScopesPerProcess
    ) {
        evictMemoryScopes();
    }

    await ensureStateRoot(req);

    const file =
        storageFile(
            req,
            scope,
        );

    let state =
        await loadJson(file);

    const expectedHash =
        scopeHash(scope);

    const basename =
        path.basename(file)
            .replace(
                /\.json$/,
                '',
            );

    if (
        basename !== expectedHash
        || !stateIdentityValid(
            state,
            scope,
        )
    ) {
        state =
            emptyState(scope);
    }

    const snapshotCheck =
        validateSnapshot(
            state.snapshot,
        );

    const metadataCheck =
        validateMetadata(
            state.chatMetadata,
        );

    if (
        !snapshotCheck.ok
        || !metadataCheck.ok
    ) {
        state =
            emptyState(scope);
    }

    state.scope =
        clone(scope);

    pruneState(state);

    scopes.set(
        key,
        state,
    );

    return state;
}

function withScopeLock(
    scope,
    callback,
) {
    const key =
        scopeKey(scope);

    const previous =
        operationChains.get(key)
        || Promise.resolve();

    const next =
        previous
            .catch(() => {})
            .then(callback);

    const tracked =
        next.finally(() => {
            if (
                operationChains.get(key)
                === tracked
            ) {
                operationChains.delete(
                    key,
                );
            }
        });

    tracked.catch(() => {});

    operationChains.set(
        key,
        tracked,
    );

    return next;
}

function persistState(
    req,
    scope,
    state,
) {
    const key =
        scopeKey(scope);

    const previous =
        persistenceChains.get(key)
        || Promise.resolve();

    const next =
        previous
            .catch(() => {})
            .then(
                async () => {
                    pruneState(state);

                    const root =
                        await ensureStateRoot(
                            req,
                        );

                    const file =
                        storageFile(
                            req,
                            scope,
                        );

                    const currentBytes =
                        await calculateUserStateBytes(
                            req,
                        );

                    const existing =
                        await fsp.stat(
                            file,
                        ).catch(
                            () => null,
                        );

                    const content =
                        JSON.stringify(state);

                    const size =
                        Buffer.byteLength(
                            content,
                            'utf8',
                        );

                    const projected =
                        Math.max(
                            0,
                            currentBytes
                                - Number(
                                    existing?.size
                                    || 0,
                                ),
                        )
                        + size;

                    if (
                        projected
                        > LIMITS.maxPersistedBytesPerUser
                    ) {
                        throw new Error(
                            'Synchronization storage quota exceeded',
                        );
                    }

                    await atomicWrite(
                        file,
                        state,
                    );

                    return root;
                },
            );

    const tracked =
        next.finally(() => {
            if (
                persistenceChains.get(
                    key,
                )
                === tracked
            ) {
                persistenceChains.delete(
                    key,
                );
            }
        });

    tracked.catch(() => {});

    persistenceChains.set(
        key,
        tracked,
    );

    return next;
}

async function calculateUserStateBytes(
    req,
) {
    const root =
        await ensureStateRoot(
            req,
        );

    let total = 0;

    try {
        const entries =
            await fsp.readdir(
                root,
                {
                    withFileTypes: true,
                },
            );

        for (
            const entry
            of entries
        ) {
            if (
                !entry.isFile()
                || !entry.name.endsWith(
                    '.json',
                )
            ) {
                continue;
            }

            const file =
                path.join(
                    root,
                    entry.name,
                );

            const stat =
                await fsp.stat(
                    file,
                ).catch(
                    () => null,
                );

            total +=
                Number(
                    stat?.size
                    || 0,
                );

            if (
                total
                > LIMITS.maxPersistedBytesPerUser
            ) {
                break;
            }
        }
    } catch {
        return total;
    }

    return total;
}

function evictMemoryScopes() {
    const candidates =
        [...scopes.entries()]
            .filter(
                ([key, state]) =>
                    !members.has(key)
                    && !state.generation,
            )
            .sort(
                (a, b) =>
                    (
                        a[1].updatedAt
                        || 0
                    )
                    - (
                        b[1].updatedAt
                        || 0
                    ),
            );

    while (
        scopes.size
        >= LIMITS.maxScopesPerProcess
        && candidates.length
    ) {
        scopes.delete(
            candidates.shift()[0],
        );
    }
}

async function cleanupUserState(
    req,
) {
    let root;

    try {
        root =
            await ensureStateRoot(req);
    } catch {
        return;
    }

    const cutoff =
        now() - LIMITS.staleStateMs;

    let entries;

    try {
        entries =
            await fsp.readdir(
                root,
                {
                    withFileTypes: true,
                },
            );
    } catch {
        return;
    }

    for (
        const entry
        of entries
    ) {
        const file =
            path.join(
                root,
                entry.name,
            );

        if (
            entry.isFile()
            && entry.name.endsWith(
                '.tmp',
            )
        ) {
            const stat =
                await fsp.stat(
                    file,
                ).catch(
                    () => null,
                );

            if (
                stat
                && stat.mtimeMs
                    < now()
                    - LIMITS.staleTempMs
            ) {
                await fsp.rm(
                    file,
                    { force: true },
                ).catch(
                    () => {},
                );
            }

            continue;
        }

        if (
            !entry.isFile()
            || !entry.name.endsWith(
                '.json',
            )
        ) {
            continue;
        }

        const stat =
            await fsp.stat(
                file,
            ).catch(
                () => null,
            );

        if (
            !stat
            || stat.mtimeMs >= cutoff
        ) {
            continue;
        }

        const state =
            await loadJson(file);

        const key =
            state?.scope
                ? scopeKey(
                    state.scope,
                )
                : null;

        if (
            key
            && members.has(key)
        ) {
            continue;
        }

        await fsp.rm(
            file,
            {
                force: true,
            },
        ).catch(
            () => {},
        );
    }
}

function membersForScope(
    scope,
) {
    const key =
        scopeKey(scope);

    const map =
        members.get(key);

    if (!map) {
        return [];
    }

    const cutoff =
        now() - LIMITS.memberTtlMs;

    for (
        const [clientId, member]
        of map
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

    return [
        ...map.values(),
    ];
}

function touchMember(
    scope,
    body,
) {
    const clientId =
        String(
            body.clientId
            ?? '',
        );

    const deviceId =
        String(
            body.deviceId
            ?? '',
        );

    if (
        !safeId(clientId, 128)
        || !safeId(deviceId, 128)
    ) {
        throw new Error(
            'Invalid clientId/deviceId',
        );
    }

    const key =
        scopeKey(scope);

    let map =
        members.get(key);

    if (!map) {
        map = new Map();
        members.set(
            key,
            map,
        );
    }

    map.set(
        clientId,
        {
            userId:
                scope.userId,
            clientId,
            deviceId,
            connectedAt:
                map.get(clientId)
                    ?.connectedAt
                || now(),
            lastSeen: now(),
        },
    );

    return {
        clientId,
        deviceId,
    };
}

function isMember(
    scope,
    clientId,
    deviceId,
) {
    const map =
        members.get(
            scopeKey(scope),
        );

    const member =
        map?.get(
            clientId,
        );

    return !!member
        && member.deviceId === deviceId
        && member.lastSeen
            >= now()
            - LIMITS.memberTtlMs;
}

function rateAllowed(
    scope,
    clientId,
) {
    const key =
        `${scope.userId}|${clientId}`;

    const current =
        rateWindows.get(key);

    if (
        !current
        || current.expiresAt
            <= now()
    ) {
        rateWindows.set(
            key,
            {
                count: 1,
                expiresAt:
                    now()
                    + 60_000,
            },
        );

        return true;
    }

    current.count++;

    return current.count
        <= LIMITS.maxEventsPerClientPerMinute;
}

function serializePublicState(
    state,
) {
    return {
        protocol: PROTOCOL,
        schema: SCHEMA,
        scope: clone(state.scope),

        revision: state.revision,
        epoch: state.epoch,

        snapshot: clone(
            state.snapshot,
        ),

        chatMetadata: clone(
            state.chatMetadata,
        ),

        tombstones: clone(
            state.tombstones,
        ),

        generation: clone(
            state.generation,
        ),

        groupSettings: clone(
            state.groupSettings,
        ),

        branches: clone(
            state.branches,
        ),

        updatedAt: state.updatedAt,
    };
}

function findCachedOperation(
    state,
    opId,
) {
    if (!safeId(opId, 160)) {
        return null;
    }

    return state.recentOps.find(
        item =>
            item.opId === opId,
    ) || null;
}

function rememberOperation(
    state,
    opId,
    result,
    type,
) {
    state.recentOps.push({
        opId,
        type,
        eventId:
            Number(
                result?.eventId
                || result?.event?.id
                || 0,
            ),
        revision:
            Number(
                result?.revision
                ?? state.revision,
            ),
        epoch:
            result?.epoch
            || state.epoch,

        accepted:
            result?.ok !== false,

        generationId:
            result?.generation?.id
            || result?.event
                ?.generationId
            || null,

        storedAt: now(),
    });

    if (
        state.recentOps.length
        > LIMITS.maxRecentOps
    ) {
        state.recentOps.splice(
            0,
            state.recentOps.length
                - LIMITS.maxRecentOps,
        );
    }
}

function cachedResultResponse(
    state,
    cached,
) {
    return {
        ok: true,
        deduped: true,
        revision:
            cached.revision,
        epoch:
            cached.epoch,
        eventId:
            cached.eventId,
        state:
            serializePublicState(
                state,
            ),
        generation:
            clone(
                state.generation,
            ),
    };
}

function recordEvent(
    state,
    event,
) {
    const previous =
        state.events.at(-1);

    const id =
        Number(
            previous?.id
            || 0,
        ) + 1;

    let stored = {
        ...clone(event),
        id,
        revision:
            state.revision,
        epoch:
            state.epoch,
        ts: now(),
    };

    if (
        bytes(stored)
        > LIMITS.maxEventBytes
    ) {
        stored = {
            ...stored,
            compacted: true,
        };

        delete stored.snapshot;
        delete stored.patch;
        delete stored.message;
        delete stored.groupSettings;
    }

    state.events.push(
        stored,
    );

    if (
        state.events.length
        > LIMITS.maxEvents
    ) {
        state.events.splice(
            0,
            state.events.length
                - LIMITS.maxEvents,
        );
    }

    return stored;
}

function publish(
    scope,
    eventType,
    payload,
    eventId,
) {
    const key =
        scopeKey(scope);

    for (
        const [token, subscription]
        of subscriptions
    ) {
        if (
            subscription.scopeKey
            !== key
        ) {
            continue;
        }

        if (!subscription.res) {
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
            closeSubscription(
                token,
            );
        }
    }
}

function writeSse(
    res,
    event,
    data,
    id = null,
) {
    if (id !== null) {
        res.write(
            `id: ${id}\n`,
        );
    }

    res.write(
        `event: ${event}\n`,
    );

    res.write(
        `data: ${JSON.stringify(data)}\n\n`,
    );
}

function closeSubscription(
    token,
) {
    const subscription =
        subscriptions.get(
            token,
        );

    if (!subscription) {
        return;
    }

    subscriptions.delete(
        token,
    );

    if (subscription.res) {
        totalSseConnections =
            Math.max(
                0,
                totalSseConnections
                    - 1,
            );

        try {
            subscription.res.end();
        } catch {}
    }

    subscription.res = null;
}

function chatFilePath(
    req,
    scope,
) {
    if (
        scope.kind === 'character'
    ) {
        const chatsRoot =
            req.user?.directories
                ?.chats;

        if (!chatsRoot) {
            return null;
        }

        const avatar =
            scope.character
                .replace(
                    /\.png$/i,
                    '',
                );

        const chatDir =
            safeJoin(
                chatsRoot,
                avatar,
            );

        return safeJoin(
            chatDir,
            `${scope.chatId}.jsonl`,
        );
    }

    const groupChatsRoot =
        req.user?.directories
            ?.groupChats;

    if (!groupChatsRoot) {
        return null;
    }

    return safeJoin(
        groupChatsRoot,
        `${scope.chatId}.jsonl`,
    );
}

async function validateCharacterScope(
    req,
    scope,
) {
    const root =
        req.user.directories.chats;

    const avatar =
        scope.character.replace(
            /\.png$/i,
            '',
        );

    const dir =
        safeJoin(
            root,
            avatar,
        );

    if (
        fs.existsSync(dir)
    ) {
        return true;
    }

    return false;
}

async function loadGroupDefinition(
    req,
    groupId,
) {
    const groupsRoot =
        req.user?.directories
            ?.groups;

    if (!groupsRoot) {
        return null;
    }

    const file =
        safeJoin(
            groupsRoot,
            `${groupId}.json`,
        );

    return loadJson(file);
}

async function validateGroupScope(
    req,
    scope,
) {
    const group =
        await loadGroupDefinition(
            req,
            scope.groupId,
        );

    if (!group) {
        return {
            ok: false,
            code: 'group_not_found',
            message:
                'The requested group does not exist.',
        };
    }

    if (
        !Array.isArray(group.members)
    ) {
        return {
            ok: false,
            code: 'group_invalid',
            message:
                'The group definition is invalid.',
        };
    }

    if (
        !Array.isArray(group.chats)
        || !group.chats.includes(
            scope.chatId,
        )
    ) {
        return {
            ok: false,
            code: 'group_chat_not_found',
            message:
                'The requested group chat does not belong to this group.',
        };
    }

    return {
        ok: true,
        group,
    };
}

async function validateScopeAgainstHost(
    req,
    scope,
) {
    if (
        scope.kind === 'character'
    ) {
        const valid =
            await validateCharacterScope(
                req,
                scope,
            );

        if (!valid) {
            return {
                ok: false,
                code: 'character_not_found',
                message:
                    'The character scope could not be resolved.',
            };
        }
    } else {
        const result =
            await validateGroupScope(
                req,
                scope,
            );

        if (!result.ok) {
            return result;
        }
    }

    const file =
        chatFilePath(
            req,
            scope,
        );

    if (!file) {
        return {
            ok: false,
            code: 'chat_path_unavailable',
            message:
                'The chat path could not be resolved.',
        };
    }

    return {
        ok: true,
        file,
    };
}

async function readHostChat(
    req,
    scope,
) {
    const validation =
        await validateScopeAgainstHost(
            req,
            scope,
        );

    if (!validation.ok) {
        return {
            ok: false,
            exists: false,
            hash: null,
            snapshotDigest: null,
            snapshot: [],
            metadata: {},
            error:
                validation.code,
        };
    }

    const file =
        validation.file;

    if (
        !fs.existsSync(file)
    ) {
        return {
            ok: true,
            exists: false,
            hash: null,
            snapshotDigest:
                sha256('[]'),
            snapshot: [],
            metadata: {},
        };
    }

    let raw;

    try {
        raw =
            await fsp.readFile(
                file,
                'utf8',
            );
    } catch {
        return {
            ok: false,
            exists: true,
            hash: null,
            snapshotDigest: null,
            snapshot: [],
            metadata: {},
            error:
                'chat_read_failed',
        };
    }

    const hash =
        sha256(raw);

    const lines =
        raw.split(/\r?\n/)
            .filter(
                line =>
                    line.trim(),
            );

    const parsed = [];

    for (
        const line
        of lines
    ) {
        try {
            parsed.push(
                JSON.parse(line),
            );
        } catch {
            return {
                ok: false,
                exists: true,
                hash,
                snapshotDigest: null,
                snapshot: [],
                metadata: {},
                error:
                    'chat_file_corrupt',
            };
        }
    }

    if (!parsed.length) {
        return {
            ok: true,
            exists: true,
            hash,
            snapshotDigest:
                sha256('[]'),
            snapshot: [],
            metadata: {},
        };
    }

    const header =
        isObject(parsed[0])
            ? parsed[0]
            : {};

    const snapshot =
        parsed.slice(1);

    const snapshotCheck =
        validateSnapshot(
            snapshot,
        );

    if (!snapshotCheck.ok) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            snapshot: [],
            metadata: {},
            error:
                snapshotCheck.error,
        };
    }

    const metadata =
        isObject(
            header.chat_metadata,
        )
            ? clone(
                header.chat_metadata,
            )
            : {};

    const metadataCheck =
        validateMetadata(
            metadata,
        );

    if (!metadataCheck.ok) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            snapshot: [],
            metadata: {},
            error:
                metadataCheck.error,
        };
    }

    if (
        scope.branchId
        && metadata.integrity
        && String(
            metadata.integrity,
        )
        !== String(
            scope.branchId,
        )
    ) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            snapshot,
            metadata,
            error:
                'branch_integrity_mismatch',
        };
    }

    if (
        scope.parentChatId
        && metadata.main_chat
        && String(
            metadata.main_chat,
        )
        !== String(
            scope.parentChatId,
        )
    ) {
        return {
            ok: false,
            exists: true,
            hash,
            snapshotDigest: null,
            snapshot,
            metadata,
            error:
                'branch_parent_mismatch',
        };
    }

    return {
        ok: true,
        exists: true,
        hash,
        snapshotDigest:
            sha256(
                stableJson(
                    snapshot,
                ),
            ),
        snapshot,
        metadata,
    };
}

function currentGeneration(
    state,
) {
    if (
        !state.generation
    ) {
        return null;
    }

    if (
        state.generation.leaseUntil
            < now()
        || state.generation.startedAt
            + LIMITS.generationMaxMs
            < now()
    ) {
        state.generation = null;
        return null;
    }

    return state.generation;
}

function isGenerationOwner(
    state,
    body,
) {
    const generation =
        state.generation;

    return !!generation
        && generation.ownerClientId
            === body.clientId
        && generation.ownerDeviceId
            === body.deviceId;
}

function revisionCheck(
    state,
    body,
) {
    const baseRevision =
        Number(
            body.baseRevision,
        );

    if (
        !Number.isInteger(
            baseRevision,
        )
        || baseRevision < 0
    ) {
        return {
            ok: false,
            code: 'invalid_revision',
            message:
                'baseRevision must be a non-negative integer.',
        };
    }

    if (
        baseRevision
        !== state.revision
    ) {
        return {
            ok: false,
            code: 'revision_conflict',
            message:
                'The synchronization revision has advanced.',
            currentRevision:
                state.revision,
        };
    }

    return {
        ok: true,
    };
}

function hostDigestCheck(
    host,
    body,
) {
    if (
        body.hostSnapshotDigest
        === undefined
    ) {
        return {
            ok: true,
        };
    }

    if (!host.ok) {
        return {
            ok: false,
            code: 'stale_host',
            message:
                'The SillyTavern chat could not be verified.',
            currentDigest:
                host.snapshotDigest,
            hostError:
                host.error || null,
        };
    }

    if (
        host.snapshotDigest
        !== String(
            body.hostSnapshotDigest,
        )
    ) {
        return {
            ok: false,
            code: 'stale_host',
            message:
                'The local SillyTavern chat changed since this operation was created.',
            currentDigest:
                host.snapshotDigest,
        };
    }

    return {
        ok: true,
    };
}

async function restoreAfterPersistFailure(
    req,
    scope,
    state,
) {
    const persisted =
        await loadJson(
            storageFile(
                req,
                scope,
            ),
        );

    if (
        stateIdentityValid(
            persisted,
            scope,
        )
    ) {
        Object.keys(state).forEach(
            key =>
                delete state[key],
        );

        Object.assign(
            state,
            clone(persisted),
        );

        pruneState(state);

        return;
    }

    Object.assign(
        state,
        emptyState(scope),
    );
}

function diffSnapshot(
    before,
    after,
) {
    const left =
        Array.isArray(before)
            ? before
            : [];

    const right =
        Array.isArray(after)
            ? after
            : [];

    let prefix = 0;

    while (
        prefix
            < left.length
        && prefix
            < right.length
        && JSON.stringify(
            left[prefix],
        )
            === JSON.stringify(
                right[prefix],
            )
    ) {
        prefix++;
    }

    let suffix = 0;

    while (
        suffix
            < left.length
            - prefix
        && suffix
            < right.length
            - prefix
        && JSON.stringify(
            left[
                left.length
                    - 1
                    - suffix
            ],
        )
            === JSON.stringify(
                right[
                    right.length
                        - 1
                        - suffix
                ],
            )
    ) {
        suffix++;
    }

    const beforeEnd =
        left.length - suffix;

    const afterEnd =
        right.length - suffix;

    return {
        kind:
            prefix === left.length
            && right.length
                >= left.length
                ? 'insert'
                : prefix === right.length
                    && left.length
                        >= right.length
                    ? 'delete'
                    : 'replace',

        start: prefix,

        deleteCount:
            beforeEnd - prefix,

        messages:
            clone(
                right.slice(
                    prefix,
                    afterEnd,
                ),
            ),
    };
}

function computeTombstones(
    before,
    after,
    revision,
) {
    const afterIds =
        new Set(
            after
                .map(
                    getMessageId,
                )
                .filter(Boolean),
        );

    const tombstones = [];

    for (
        const message
        of before
    ) {
        const id =
            getMessageId(message);

        if (
            id
            && !afterIds.has(id)
        ) {
            tombstones.push({
                messageId: id,
                revision,
                deletedAt: now(),
            });
        }
    }

    return tombstones;
}

async function handleJoin(
    req,
    res,
) {
    if (requestBodyTooLarge(req)) {
        return sendError(
            res,
            413,
            'request_too_large',
            'Request is too large.',
        );
    }

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

    let scope;

    try {
        scope =
            normalizeScope(
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

    let ids;

    try {
        ids =
            touchMember(
                scope,
                req.body || {},
            );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_client',
            error.message,
        );
    }

    const scopeValidation =
        await validateScopeAgainstHost(
            req,
            scope,
        );

    if (
        !scopeValidation.ok
        && scopeValidation.code
            !== 'character_not_found'
    ) {
        return sendError(
            res,
            scopeValidation.code
                === 'group_not_found'
                ? 404
                : 400,
            scopeValidation.code,
            scopeValidation.message,
        );
    }

    const state =
        await loadState(
            req,
            scope,
        );

    const beforeGeneration =
        !!state.generation;

    currentGeneration(state);

    const host =
        await readHostChat(
            req,
            scope,
        );

    let bootstrapped = false;

    if (
        state.revision === 0
        && state.snapshot.length === 0
        && host.ok
        && host.exists
        && host.snapshot.length
    ) {
        const normalized =
            ensureMessageIds(
                host.snapshot,
            );

        state.snapshot =
            normalized;

        state.chatMetadata =
            clone(
                host.metadata,
            );

        state.hostSnapshotDigest =
            sha256(
                stableJson(
                    normalized,
                ),
            );

        state.revision = 1;

        const event =
            recordEvent(
                state,
                {
                    type:
                        'bootstrap',
                    source: {
                        clientId:
                            ids.clientId,
                        deviceId:
                            ids.deviceId,
                    },
                    patch: {
                        kind:
                            'replace',
                        start: 0,
                        deleteCount: 0,
                        messages:
                            clone(
                                normalized,
                            ),
                    },
                    stateDigest:
                        sha256(
                            stableJson(
                                normalized,
                            ),
                        ),
                },
            );

        bootstrapped = true;

        try {
            await persistState(
                req,
                scope,
                state,
            );
        } catch (error) {
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
                {
                    detail:
                        error.message,
                },
            );
        }

        publish(
            scope,
            'sync',
            {
                epoch:
                    state.epoch,
                event,
                state:
                    serializePublicState(
                        state,
                    ),
            },
            event.id,
        );
    }

    if (
        !beforeGeneration
        && state.generation
    ) {
        currentGeneration(state);
    }

    const token =
        randomId('sse_');

    for (
        const [
            oldToken,
            subscription,
        ] of subscriptions
    ) {
        if (
            subscription.userId
                === userId
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
        token,
        {
            token,
            userId,
            clientId:
                ids.clientId,
            deviceId:
                ids.deviceId,
            scope:
                clone(scope),
            scopeKey:
                scopeKey(scope),
            createdAt:
                now(),
            res: null,
        },
    );

    await cleanupUserState(
        req,
    );

    return res.json({
        ok: true,
        protocol: PROTOCOL,
        schema: SCHEMA,

        userId,

        scope:
            clone(scope),

        state:
            serializePublicState(
                state,
            ),

        serverNow:
            now(),

        membership:
            ids,

        subscriptionToken:
            token,

        bootstrap:
            bootstrapped,

        host: {
            exists:
                host.exists,
            ok:
                host.ok,
            hash:
                host.hash,
            snapshotDigest:
                host.snapshotDigest,
            error:
                host.error || null,
        },

        capabilities: {
            sse: true,
            revisions: true,
            durableQueue: true,
            idempotency: true,
            generationLease: true,
            branches: true,
            checkpoints: true,
            swipes: true,
            reasoning: true,
            toolInvocations: true,
            attachments:
                'server-resident-reference',
            exactTokenReplay:
                false,
        },
    });
}

async function handleLeave(
    req,
    res,
) {
    let scope;

    try {
        scope =
            normalizeScope(
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

    try {
        const {
            clientId,
            deviceId,
        } =
            touchMember(
                scope,
                req.body || {},
            );

        members
            .get(scopeKey(scope))
            ?.delete(
                clientId,
            );

        for (
            const [
                token,
                subscription,
            ] of subscriptions
        ) {
            if (
                subscription.scopeKey
                    === scopeKey(scope)
                && subscription.clientId
                    === clientId
                && subscription.deviceId
                    === deviceId
            ) {
                closeSubscription(
                    token,
                );
            }
        }

        return res.json({
            ok: true,
            clientId,
            deviceId,
        });
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_client',
            error.message,
        );
    }
}

async function handleHeartbeat(
    req,
    res,
) {
    let scope;

    try {
        scope =
            normalizeScope(
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

    let ids;

    try {
        ids =
            touchMember(
                scope,
                req.body || {},
            );
    } catch (error) {
        return sendError(
            res,
            400,
            'invalid_client',
            error.message,
        );
    }

    const state =
        await loadState(
            req,
            scope,
        );

    currentGeneration(state);

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

        renewed = true;

        try {
            await persistState(
                req,
                scope,
                state,
            );
        } catch (error) {
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
                {
                    detail:
                        error.message,
                },
            );
        }
    }

    return res.json({
        ok: true,
        membership:
            ids,
        renewed,
        revision:
            state.revision,
        epoch:
            state.epoch,
        generation:
            clone(
                state.generation,
            ),
    });
}

async function stateResponse(
    req,
    res,
) {
    const raw =
        req.method === 'GET'
            ? req.query
            : req.body;

    let scope;

    try {
        scope =
            normalizeScope(
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

    const clientId =
        String(
            raw?.clientId
            || '',
        );

    const deviceId =
        String(
            raw?.deviceId
            || '',
        );

    if (
        !safeId(
            clientId,
            128,
        )
        || !safeId(
            deviceId,
            128,
        )
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

    const state =
        await loadState(
            req,
            scope,
        );

    currentGeneration(state);

    const host =
        await readHostChat(
            req,
            scope,
        );

    return res.json({
        ok: true,

        protocol:
            PROTOCOL,
        schema:
            SCHEMA,

        state:
            serializePublicState(
                state,
            ),

        host: {
            ok:
                host.ok,
            exists:
                host.exists,
            hash:
                host.hash,
            snapshotDigest:
                host.snapshotDigest,
            error:
                host.error || null,
        },

        cursor: {
            epoch:
                state.epoch,
            revision:
                state.revision,
            lastEventId:
                Number(
                    state.events.at(-1)
                        ?.id
                    || 0,
                ),
        },
    });
}

async function handleSse(
    req,
    res,
) {
    const token =
        String(
            req.query?.token
            || '',
        );

    const subscription =
        subscriptions.get(
            token,
        );

    const userId =
        userIdFromRequest(req);

    if (
        !subscription
        || subscription.userId
            !== userId
    ) {
        return res
            .status(401)
            .end(
                'invalid subscription',
            );
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
            .end(
                'membership expired',
            );
    }

    if (
        totalSseConnections
        >= LIMITS.maxSseTotal
    ) {
        return res
            .status(503)
            .end(
                'SSE capacity reached',
            );
    }

    if (subscription.res) {
        try {
            subscription.res.end();
        } catch {}

        subscription.res = null;
        totalSseConnections =
            Math.max(
                0,
                totalSseConnections
                    - 1,
            );
    }

    totalSseConnections++;
    subscription.res = res;

    res.status(200);

    res.set({
        'Content-Type':
            'text/event-stream',
        'Cache-Control':
            'no-cache, no-transform',
        Connection:
            'keep-alive',
        'X-Accel-Buffering':
            'no',
    });

    res.flushHeaders?.();

    const state =
        await loadState(
            req,
            subscription.scope,
        );

    currentGeneration(state);

    const lastEventId =
        Number.parseInt(
            req.get(
                'Last-Event-ID',
            )
            || req.query?.lastEventId
            || '0',
            10,
        ) || 0;

    writeSse(
        res,
        'hello',
        {
            protocol:
                PROTOCOL,
            schema:
                SCHEMA,
            epoch:
                state.epoch,
            revision:
                state.revision,
            eventId:
                Number(
                    state.events.at(-1)
                        ?.id
                    || 0,
                ),
            generation:
                clone(
                    state.generation,
                ),
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
        && lastEventId
            < oldest - 1
    ) {
        writeSse(
            res,
            'resync_required',
            {
                epoch:
                    state.epoch,
                revision:
                    state.revision,
                eventId:
                    oldest,
                reason:
                    'replay_window_exhausted',
            },
        );
    } else if (
        lastEventId
    ) {
        for (
            const event
            of state.events
        ) {
            if (
                Number(event.id)
                <= lastEventId
            ) {
                continue;
            }

            writeSse(
                res,
                'replay',
                {
                    epoch:
                        state.epoch,
                    event:
                        clone(event),
                },
                event.id,
            );
        }
    }

    writeSse(
        res,
        'replay_complete',
        {
            epoch:
                state.epoch,
            revision:
                state.revision,
            eventId:
                Number(
                    state.events.at(-1)
                        ?.id
                    || 0,
                ),
        },
    );

    const keepalive =
        setInterval(
            () => {
                if (
                    res.writableEnded
                ) {
                    clearInterval(
                        keepalive,
                    );
                    return;
                }

                try {
                    res.write(
                        `: keepalive ${now()}\n\n`,
                    );
                } catch {
                    clearInterval(
                        keepalive,
                    );
                }
            },
            15_000,
        );

    const close =
        () => {
            clearInterval(
                keepalive,
            );

            if (
                subscription.res
                    !== res
            ) {
                return;
            }

            subscription.res =
                null;

            totalSseConnections =
                Math.max(
                    0,
                    totalSseConnections
                        - 1,
                );
        };

    req.on(
        'close',
        close,
    );
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
                error:
                    revision,
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
                error:
                    hostCheck,
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
        && metadata.integrity
        && String(
            metadata.integrity,
        )
        !== String(
            scope.branchId,
        )
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_integrity_mismatch',
                    message:
                        'Branch integrity does not match this synchronized branch.',
                },
            },
        };
    }

    if (
        scope.parentChatId
        && metadata.main_chat
        && String(
            metadata.main_chat,
        )
        !== String(
            scope.parentChatId,
        )
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_parent_mismatch',
                    message:
                        'Branch parent does not match this synchronized scope.',
                },
            },
        };
    }

    const next =
        ensureMessageIds(
            body.snapshot,
        );

    const previous =
        clone(
            state.snapshot,
        );

    state.revision++;

    state.snapshot =
        next;

    state.chatMetadata =
        metadata;

    state.hostSnapshotDigest =
        sha256(
            stableJson(
                next,
            ),
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
                type:
                    body.type,
                opId:
                    body.opId,
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
                        stableJson(
                            next,
                        ),
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
                error:
                    revision,
            },
        };
    }

    const metadata =
        clone(
            body.chatMetadata,
        );

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

    const previous =
        clone(
            state.chatMetadata,
        );

    state.revision++;

    state.chatMetadata =
        metadata;

    const event =
        recordEvent(
            state,
            {
                type:
                    'metadata',
                opId:
                    body.opId,
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
                        stableJson(
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
    if (
        scope.kind !== 'group'
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'not_group',
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
                error:
                    revision,
            },
        };
    }

    if (
        !isObject(
            body.groupSettings,
        )
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_group_settings',
                    message:
                        'groupSettings must be an object.',
                },
            },
        };
    }

    if (
        !validateDataTree(
            body.groupSettings,
        )
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'invalid_group_settings',
                    message:
                        'groupSettings contains unsupported data.',
                },
            },
        };
    }

    if (
        bytes(body.groupSettings)
        > LIMITS.maxGroupSettingsBytes
    ) {
        return {
            status: 413,
            payload: {
                ok: false,
                error: {
                    code:
                        'group_settings_too_large',
                    message:
                        'groupSettings is too large.',
                },
            },
        };
    }

    state.revision++;

    state.groupSettings =
        clone(
            body.groupSettings,
        );

    const event =
        recordEvent(
            state,
            {
                type:
                    'group_settings',
                opId:
                    body.opId,
                source: {
                    clientId:
                        body.clientId,
                    deviceId:
                        body.deviceId,
                },
                groupSettings:
                    clone(
                        body.groupSettings,
                    ),
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
                error:
                    revision,
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

    if (
        childScope.parentChatId
        !== parentScope.chatId
    ) {
        return {
            status: 400,
            payload: {
                ok: false,
                error: {
                    code:
                        'branch_parent_mismatch',
                    message:
                        'Child branch must point at this parent chat.',
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
                        'The child branch must provide its native integrity ID.',
                },
            },
        };
    }

    const host =
        await readHostChat(
            req,
            childScope,
        );

    if (
        !host.ok
        || !host.exists
    ) {
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
        )
        !== String(
            parentScope.chatId,
        )
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
        )
        !== String(
            childScope.branchId,
        )
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

    if (
        childState.revision === 0
    ) {
        childState.snapshot =
            ensureMessageIds(
                host.snapshot,
            );

        childState.chatMetadata =
            clone(
                host.metadata,
            );

        childState.revision = 1;

        childState.hostSnapshotDigest =
            sha256(
                stableJson(
                    childState.snapshot,
                ),
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
                        clone(
                            parentScope,
                        ),
                },
            );

        try {
            await persistState(
                req,
                childScope,
                childState,
            );
        } catch (error) {
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
                        detail:
                            error.message,
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
        branchKind:
            body.branchKind === 'checkpoint'
                ? 'checkpoint'
                : 'branch',
        createdAt:
            now(),
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
        > 1024
    ) {
        parentState.branches.splice(
            0,
            parentState.branches.length
                - 1024,
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
    currentGeneration(state);

    if (
        body.type
            === 'generation_claim'
    ) {
        if (
            state.generation
        ) {
            return {
                status: 409,
                payload: {
                    ok: false,
                    error: {
                        code:
                            'generation_busy',
                        message:
                            'Another synchronized client currently owns generation.',
                    },
                    generation:
                        clone(
                            state.generation,
                        ),
                },
            };
        }

        const generationId =
            body.generationId
            && safeId(
                String(
                    body.generationId,
                ),
                160,
            )
                ? String(
                    body.generationId,
                )
                : randomId('g_');

        state.generation = {
            id:
                generationId,

            ownerClientId:
                body.clientId,

            ownerDeviceId:
                body.deviceId,

            generationType:
                String(
                    body.generationType
                    || 'normal',
                ),

            phase:
                'claimed',

            startedAt:
                now(),

            leaseUntil:
                now()
                + LIMITS.generationLeaseMs,

            streamSeq:
                0,

            messageId:
                body.messageId
                    ? String(
                        body.messageId,
                    )
                    : null,

            stopRequested:
                false,
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
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (!state.generation) {
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

    const generationId =
        String(
            body.generationId
            || '',
        );

    if (
        generationId
        !== state.generation.id
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
        body.type
            === 'generation_heartbeat'
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

        const event =
            recordEvent(
                state,
                {
                    type:
                        'generation_heartbeat',
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
        body.type
            === 'generation_started'
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

        state.generation.phase =
            'started';

        if (
            body.messageId
        ) {
            state.generation.messageId =
                String(
                    body.messageId,
                );
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
        body.type
            === 'generation_stream'
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
            !Number.isInteger(
                streamSeq,
            )
            || streamSeq
                !== state.generation.streamSeq
                    + 1
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
                    },
                    expected:
                        state.generation
                            .streamSeq
                        + 1,
                },
            };
        }

        let message = null;

        if (
            body.message !== undefined
        ) {
            const validation =
                validateSnapshot(
                    [body.message],
                );

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

            message =
                ensureMessageIds(
                    [body.message],
                )[0];
        }

        state.generation.streamSeq =
            streamSeq;

        state.generation.phase =
            'streaming';

        if (
            body.messageId
        ) {
            state.generation.messageId =
                String(
                    body.messageId,
                );
        }

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
                    generationId,
                    streamSeq,
                    messageId:
                        state.generation
                            .messageId,
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
        body.type
            === 'generation_stop_request'
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
                    generationId,
                    reason:
                        String(
                            body.reason
                            || 'remote_stop',
                        ),
                },
            );

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type
            === 'generation_terminal'
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
            body.snapshot !== undefined
        ) {
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
                        error:
                            hostCheck,
                    },
                };
            }

            const previous =
                clone(
                    state.snapshot,
                );

            const next =
                ensureMessageIds(
                    body.snapshot,
                );

            const metadata =
                body.chatMetadata
                === undefined
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

            state.revision++;

            state.snapshot =
                next;

            state.chatMetadata =
                metadata;

            state.hostSnapshotDigest =
                sha256(
                    stableJson(
                        next,
                    ),
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
            status;

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
                    generationId,
                    status,
                    snapshot:
                        body.snapshot !== undefined
                            ? clone(
                                state.snapshot,
                            )
                            : null,
                },
            );

        state.generation = null;

        return {
            status: 200,
            event,
        };
    }

    if (
        body.type
            === 'generation_recover'
    ) {
        if (
            state.generation
            && state.generation
                .leaseUntil
                > now()
            && state.generation
                .startedAt
                    + LIMITS.generationMaxMs
                > now()
        ) {
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

        const previous =
            clone(
                state.generation,
            );

        state.generation =
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
                        previous,
                },
            );

        return {
            status: 200,
            event,
            recovered: true,
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

async function handleEvent(
    req,
    res,
) {
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
        scope =
            normalizeScope(
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

    const body =
        req.body || {};

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
            body.clientId
            || '',
        );

    const deviceId =
        String(
            body.deviceId
            || '',
        );

    const opId =
        String(
            body.opId
            || '',
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
                    body.type === 'metadata'
                ) {
                    result =
                        await processMetadataMutation(
                            req,
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type === 'group_settings'
                ) {
                    result =
                        await processGroupSettings(
                            scope,
                            state,
                            body,
                        );
                } else if (
                    body.type
                        === 'branch_announce'
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
            } catch (error) {
                return sendError(
                    res,
                    500,
                    'internal_error',
                    'Synchronization operation failed.',
                    {
                        detail:
                            error.message,
                    },
                );
            }

            if (
                result.payload
            ) {
                return res
                    .status(
                        result.status,
                    )
                    .json(
                        result.payload,
                    );
            }

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

            try {
                await persistState(
                    req,
                    scope,
                    state,
                );
            } catch (error) {
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
                    {
                        detail:
                            error.message,
                    },
                );
            }

            const publicState =
                serializePublicState(
                    state,
                );

            if (
                result.event
            ) {
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
                            publicState,
                    },
                    result.event.id,
                );
            }

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
                    publicState,
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

async function handleHealth(
    req,
    res,
) {
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
            '1.2.0',
        protocol:
            PROTOCOL,
        schema:
            SCHEMA,
        userId,
        node:
            process.version,
        storage:
            true,
        scopes:
            scopes.size,
        sse:
            totalSseConnections,
        shuttingDown,
    });
}

async function init(router) {
    shuttingDown =
        false;

    cleanupTimer =
        setInterval(
            async () => {
                const activeUsers =
                    new Set();

                for (
                    const memberMap
                    of members.values()
                ) {
                    for (
                        const member
                        of memberMap.values()
                    ) {
                        activeUsers.add(
                            member.userId,
                        );
                    }
                }

                /*
                 * User directories are only known from authenticated requests.
                 * No global scan is performed here intentionally.
                 */
                for (
                    const key
                    of scopes.keys()
                ) {
                    if (
                        !activeUsers.has(
                            key.split('|')[0],
                        )
                    ) {
                        continue;
                    }
                }
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
        `[multi-client-sync] loaded `
        + `protocol=${PROTOCOL} `
        + `schema=${SCHEMA}`,
    );
}

async function exit() {
    shuttingDown =
        true;

    if (cleanupTimer) {
        clearInterval(
            cleanupTimer,
        );
    }

    for (
        const [
            token,
            subscription,
        ]
        of subscriptions
    ) {
        if (
            subscription.res
        ) {
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

    /*
     * Persist currently-loaded state objects.
     * The per-scope persistence chains serialize writes.
     */
    const pending = [];

    for (
        const state
        of scopes.values()
    ) {
        pending.push(
            persistState(
                {
                    user: {
                        profile: {
                            handle:
                                state
                                    .scope
                                    .userId,
                        },
                        directories: {
                            root:
                                path.join(
                                    process.cwd(),
                                    'data',
                                    state
                                        .scope
                                        .userId,
                                ),
                            chats:
                                path.join(
                                    process.cwd(),
                                    'data',
                                    state
                                        .scope
                                        .userId,
                                    'chats',
                                ),
                            groupChats:
                                path.join(
                                    process.cwd(),
                                    'data',
                                    state
                                        .scope
                                        .userId,
                                    'group chats',
                                ),
                            groups:
                                path.join(
                                    process.cwd(),
                                    'data',
                                    state
                                        .scope
                                        .userId,
                                    'groups',
                                ),
                        },
                    },
                },
                state.scope,
                state,
            ).catch(
                () => {},
            ),
        );
    }

    await Promise.allSettled(
        pending,
    );
}

module.exports = {
    init,
    exit,
    info,
};
