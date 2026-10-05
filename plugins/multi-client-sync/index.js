'use strict';

/**
 * Multi-Client Sync
 * -----------------
 *
 * Server-side authority for the browser extension.
 *
 * Core guarantees implemented here:
 *
 * - authenticated user scoping using SillyTavern's req.user
 * - character/group + exact chat scoping
 * - branch/checkpoint lineage validation where ST metadata exposes it
 * - server epoch fencing
 * - per-scope monotonic revisions
 * - per-scope monotonic event sequence
 * - operation idempotency
 * - stale-write rejection
 * - bounded replay log
 * - SSE live delivery
 * - resumable SSE using opaque subscription tokens
 * - replay-window detection
 * - explicit resync requirements
 * - generation ownership
 * - generation leases
 * - stale generation fencing
 * - generation stream sequence enforcement
 * - remote generation stop requests
 * - crash/timeout owner release
 * - bounded membership lifetime
 * - per-user/per-category rate limiting
 * - payload/snapshot limits
 * - safe event/schema validation
 * - durable server mirror
 * - per-scope persistence serialization
 * - persistence revision tracking
 * - persisted-state corruption tolerance
 * - bounded in-memory scope count
 * - bounded replay storage
 * - safe path handling
 * - ST chat-file verification for durable mutations
 *
 * Important:
 *
 * The plugin is intentionally passive until a compatible client connects.
 * It never changes SillyTavern chats merely because the plugin is installed.
 *
 * Ordinary chat mutations are verified against the authenticated user's actual
 * ST chat file before becoming canonical on the server.
 *
 * Generation streaming is intentionally represented as synchronization state.
 * The browser extension remains responsible for actually invoking ST's
 * generation functions.
 */

const fs = require('node:fs');
const fsp = require('node:fs/promises');
const path = require('node:path');
const crypto = require('node:crypto');


/* -------------------------------------------------------------------------- */
/* Constants                                                                  */
/* -------------------------------------------------------------------------- */

const PLUGIN_ID = 'multi-client-sync';

const PROTOCOL_VERSION = 4;
const STATE_SCHEMA_VERSION = 4;

const MAX_REQUEST_BYTES = 32 * 1024 * 1024;
const MAX_SNAPSHOT_BYTES = 24 * 1024 * 1024;
const MAX_MESSAGES = 200_000;

const MAX_REPLAY_EVENTS = 2_000;
const MAX_REPLAY_BYTES = 2 * 1024 * 1024;

const MAX_OPERATION_HISTORY = 5_000;

const MAX_CLIENTS_PER_SCOPE = 8;
const MAX_SSE_PER_CLIENT = 2;

const MEMBER_TTL_MS = 45_000;
const GENERATION_LEASE_MS = 20_000;
const GENERATION_MAX_MS = 6 * 60 * 60 * 1000;

const SSE_KEEPALIVE_MS = 15_000;

const RATE_WINDOW_MS = 10_000;

const RATE_LIMITS = Object.freeze({
    read: 120,
    mutate: 60,
    heartbeat: 30,
    join: 20,
});

const MAX_SCOPES_IN_MEMORY = 5_000;
const SCOPE_MEMORY_IDLE_MS = 15 * 60 * 1000;

const GROUP_CACHE_MS = 2_000;
const CHAT_FILE_CACHE_MAX = 512;

const SUBSCRIPTION_TOKEN_TTL_MS =
    24 * 60 * 60 * 1000;

const MAX_PERSISTED_BYTES_PER_USER =
    4 * 1024 * 1024 * 1024;

const DATA_DIR_NAME =
    'multi-client-sync';

const STATE_DIR_NAME =
    'state';

const SECRET_FILE_NAME =
    'server-secret.bin';


/* -------------------------------------------------------------------------- */
/* Plugin metadata                                                            */
/* -------------------------------------------------------------------------- */

const info = {
    id: PLUGIN_ID,
    name: 'Multi-Client Sync',
    description:
        'Authoritative multi-client SillyTavern synchronization with revisions, replay, SSE, generation leases and durable recovery.',
};


/* -------------------------------------------------------------------------- */
/* Runtime                                                                    */
/* -------------------------------------------------------------------------- */

let initialized = false;
let shuttingDown = false;

let runtimeEpoch =
    crypto.randomUUID();

let dataRoot = null;
let pluginRoot = null;
let stateRoot = null;
let secretPath = null;
let principalSecret = null;

let watchdogTimer = null;


/* -------------------------------------------------------------------------- */
/* Runtime maps                                                               */
/* -------------------------------------------------------------------------- */

/**
 * @typedef {{
 *   schemaVersion: number,
 *   key: string,
 *   userId: string,
 *   scope: object,
 *   revision: number,
 *   seq: number,
 *   snapshot: object|null,
 *   snapshotHash: string|null,
 *   events: object[],
 *   seenOps: string[],
 *   opResults: Map<string, object>,
 *   members: Map<string, object>,
 *   generation: object|null,
 *   stopRequestIds: Set<string>,
 *   lastAccessAt: number,
 *   persistChain: Promise<any>,
 *   persistedRevision: number,
 *   persistedBytes: number,
 * }} ScopeRecord
 */

/** @type {Map<string, ScopeRecord>} */
const scopes =
    new Map();

/**
 * scopeKey -> Map<clientId, Set<Response>>
 * @type {Map<string, Map<string, Set<object>>>}
 */
const sseClients =
    new Map();

/** @type {Map<string, object>} */
const rateBuckets =
    new Map();

/** @type {Map<string, object>} */
const groupCache =
    new Map();

/**
 * filePath -> {
 *   mtimeMs,
 *   size,
 *   result,
 *   cachedAt
 * }
 *
 * @type {Map<string, object>}
 */
const chatFileCache =
    new Map();

/** userId -> persisted bytes */
const persistedBytesByUser =
    new Map();


/* -------------------------------------------------------------------------- */
/* Errors                                                                     */
/* -------------------------------------------------------------------------- */

class SyncError extends Error {
    constructor(
        code,
        message,
        status = 400,
        extra = {},
    ) {
        super(message);

        this.name = 'SyncError';
        this.code = code;
        this.status = status;

        Object.assign(
            this,
            extra,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* General helpers                                                            */
/* -------------------------------------------------------------------------- */

function clone(value) {
    return value === undefined
        ? undefined
        : structuredClone(value);
}

function now() {
    return Date.now();
}

function byteLength(value) {
    return Buffer.byteLength(
        JSON.stringify(value),
        'utf8',
    );
}

function stableStringify(value) {
    if (
        value === null ||
        typeof value !== 'object'
    ) {
        return JSON.stringify(value);
    }

    if (Array.isArray(value)) {
        return `[${value.map(
            stableStringify,
        ).join(',')}]`;
    }

    return `{${Object.keys(value)
        .sort()
        .map(
            key =>
                `${JSON.stringify(
                    key,
                )}:${stableStringify(
                    value[key],
                )}`,
        )
        .join(',')}}`;
}

function sha256(value) {
    const input =
        typeof value === 'string'
            ? value
            : stableStringify(value);

    return crypto
        .createHash('sha256')
        .update(input, 'utf8')
        .digest('hex');
}

function hmac(value) {
    return crypto
        .createHmac(
            'sha256',
            principalSecret,
        )
        .update(
            value,
            'utf8',
        )
        .digest('hex');
}

function base64urlEncode(
    value,
) {
    return Buffer
        .from(
            value,
            'utf8',
        )
        .toString(
            'base64',
        )
        .replaceAll(
            '+',
            '-',
        )
        .replaceAll(
            '/',
            '_',
        )
        .replaceAll(
            '=',
            '',
        );
}

function base64urlDecode(
    value,
) {
    const padded =
        value
            .replaceAll(
                '-',
                '+',
            )
            .replaceAll(
                '_',
                '/',
            )
            .padEnd(
                Math.ceil(
                    value.length / 4,
                ) * 4,
                '=',
            );

    return Buffer
        .from(
            padded,
            'base64',
        )
        .toString(
            'utf8',
        );
}

function randomId() {
    return crypto.randomUUID();
}

function eventId(
    seq,
) {
    return `${runtimeEpoch}:${seq}`;
}

function parseEventId(
    value,
) {
    if (!value) {
        return null;
    }

    const stringValue =
        String(value);

    const separator =
        stringValue.lastIndexOf(
            ':',
        );

    if (separator <= 0) {
        return null;
    }

    const epoch =
        stringValue.slice(
            0,
            separator,
        );

    const seq =
        Number(
            stringValue.slice(
                separator + 1,
            ),
        );

    if (
        !Number.isSafeInteger(
            seq,
        ) ||
        seq < 0
    ) {
        return null;
    }

    return {
        epoch,
        seq,
    };
}

function normalizeString(
    value,
    field,
    maxLength = 1024,
) {
    if (
        typeof value !== 'string' ||
        value.length < 1 ||
        value.length > maxLength
    ) {
        throw new SyncError(
            'invalid_request',
            `Invalid ${field}`,
        );
    }

    return value;
}

function safeStorageHash(
    value,
) {
    return crypto
        .createHash('sha256')
        .update(
            value,
            'utf8',
        )
        .digest('hex');
}

function sameValue(
    a,
    b,
) {
    return (
        stableStringify(a) ===
        stableStringify(b)
    );
}


/* -------------------------------------------------------------------------- */
/* Recursive payload validation                                                */
/* -------------------------------------------------------------------------- */

const FORBIDDEN_KEYS =
    new Set([
        '__proto__',
        'prototype',
        'constructor',
    ]);

function validateDataTree(
    value,
    depth = 0,
) {
    if (depth > 20) {
        throw new SyncError(
            'invalid_request',
            'Payload nesting is too deep',
        );
    }

    if (
        value === null ||
        value === undefined ||
        typeof value ===
            'boolean' ||
        typeof value ===
            'number'
    ) {
        return;
    }

    if (
        typeof value === 'string'
    ) {
        if (
            value.length >
            8 * 1024 * 1024
        ) {
            throw new SyncError(
                'payload_too_large',
                'Payload string is too large',
                413,
            );
        }

        return;
    }

    if (
        Array.isArray(value)
    ) {
        for (
            const item of value
        ) {
            validateDataTree(
                item,
                depth + 1,
            );
        }

        return;
    }

    if (
        typeof value ===
            'object'
    ) {
        for (
            const [
                key,
                child,
            ] of Object.entries(
                value,
            )
        ) {
            if (
                FORBIDDEN_KEYS.has(
                    key,
                )
            ) {
                throw new SyncError(
                    'invalid_request',
                    `Unsafe object key: ${key}`,
                );
            }

            validateDataTree(
                child,
                depth + 1,
            );
        }

        return;
    }

    throw new SyncError(
        'invalid_request',
        'Unsupported payload value',
    );
}


/* -------------------------------------------------------------------------- */
/* User identity                                                              */
/* -------------------------------------------------------------------------- */

function getAuthenticatedUserId(
    req,
) {
    const handle =
        req?.user?.profile?.handle;

    if (
        typeof handle !== 'string' ||
        !handle
    ) {
        throw new SyncError(
            'auth_required',
            'Authenticated SillyTavern user required',
            403,
        );
    }

    return handle;
}

function makePrincipalKey(
    userId,
) {
    return hmac(
        `principal:${userId}`,
    );
}


/* -------------------------------------------------------------------------- */
/* Scope                                                                      */
/* -------------------------------------------------------------------------- */

function normalizeScope(
    raw,
) {
    if (
        !raw ||
        typeof raw !== 'object'
    ) {
        throw new SyncError(
            'invalid_scope',
            'Missing scope',
        );
    }

    const scopeType =
        raw.scopeType === 'group'
            ? 'group'
            : raw.scopeType ===
                  'character'
                ? 'character'
                : null;

    if (!scopeType) {
        throw new SyncError(
            'invalid_scope',
            'Invalid scope type',
        );
    }

    const chatId =
        normalizeString(
            String(raw.chatId),
            'chatId',
            2048,
        );

    const characterId =
        raw.characterId ==
            null
            ? null
            : normalizeString(
                String(
                    raw.characterId,
                ),
                'characterId',
                512,
            );

    const groupId =
        raw.groupId ==
            null
            ? null
            : normalizeString(
                String(
                    raw.groupId,
                ),
                'groupId',
                512,
            );

    const branchId =
        raw.branchId ==
            null
            ? null
            : normalizeString(
                String(
                    raw.branchId,
                ),
                'branchId',
                512,
            );

    const parentChatId =
        raw.parentChatId ==
            null
            ? null
            : normalizeString(
                String(
                    raw.parentChatId,
                ),
                'parentChatId',
                2048,
            );

    if (
        scopeType ===
            'character' &&
        !characterId
    ) {
        throw new SyncError(
            'invalid_scope',
            'characterId is required',
        );
    }

    if (
        scopeType ===
            'group' &&
        !groupId
    ) {
        throw new SyncError(
            'invalid_scope',
            'groupId is required',
        );
    }

    return {
        scopeType,
        characterId:
            scopeType ===
            'character'
                ? characterId
                : null,
        groupId:
            scopeType === 'group'
                ? groupId
                : null,
        chatId,
        branchId,
        parentChatId,
    };
}

function scopeKey(
    userId,
    scope,
) {
    return stableStringify({
        userId,
        ...scope,
    });
}

function parseScopeKey(
    key,
) {
    return JSON.parse(
        key,
    );
}


/* -------------------------------------------------------------------------- */
/* Scope records                                                              */
/* -------------------------------------------------------------------------- */

function createScopeRecord(
    key,
    userId,
    scope,
) {
    const record = {
        schemaVersion:
            STATE_SCHEMA_VERSION,

        key,

        userId,

        scope:
            clone(scope),

        revision:
            0,

        seq:
            0,

        snapshot:
            null,

        snapshotHash:
            null,

        events:
            [],

        seenOps:
            [],

        opResults:
            new Map(),

        members:
            new Map(),

        generation:
            null,

        stopRequestIds:
            new Set(),

        lastAccessAt:
            now(),

        persistChain:
            Promise.resolve(),

        persistedRevision:
            0,

        persistedBytes:
            0,
    };

    scopes.set(
        key,
        record,
    );

    return record;
}

function getOrCreateScope(
    userId,
    scope,
) {
    const key =
        scopeKey(
            userId,
            scope,
        );

    return (
        scopes.get(key) ||
        createScopeRecord(
            key,
            userId,
            scope,
        )
    );
}

function getScope(
    userId,
    scope,
) {
    return scopes.get(
        scopeKey(
            userId,
            scope,
        ),
    );
}


/* -------------------------------------------------------------------------- */
/* Snapshot validation                                                        */
/* -------------------------------------------------------------------------- */

function validateSnapshotShape(
    snapshot,
) {
    if (
        !snapshot ||
        typeof snapshot !==
            'object'
    ) {
        throw new SyncError(
            'invalid_snapshot',
            'Snapshot must be an object',
        );
    }

    if (
        !Array.isArray(
            snapshot.chat,
        )
    ) {
        throw new SyncError(
            'invalid_snapshot',
            'snapshot.chat must be an array',
        );
    }

    if (
        snapshot.chat.length >
        MAX_MESSAGES
    ) {
        throw new SyncError(
            'snapshot_too_large',
            'Too many messages',
            413,
        );
    }

    if (
        snapshot.chatMetadata !=
            null &&
        (
            typeof snapshot.chatMetadata !==
                'object' ||
            Array.isArray(
                snapshot.chatMetadata,
            )
        )
    ) {
        throw new SyncError(
            'invalid_snapshot',
            'snapshot.chatMetadata must be an object',
        );
    }

    const bytes =
        byteLength(
            snapshot,
        );

    if (
        bytes >
        MAX_SNAPSHOT_BYTES
    ) {
        throw new SyncError(
            'snapshot_too_large',
            'Snapshot exceeds the synchronization limit',
            413,
        );
    }

    validateDataTree(
        snapshot,
    );
}

function messageSyncId(
    message,
) {
    return (
        message
            ?.extra
            ?.multi_client_sync
            ?.messageId ||
        null
    );
}

function validateNoDuplicateMessageIds(
    snapshot,
) {
    const seen =
        new Set();

    for (
        let i = 1;
        i < snapshot.chat.length;
        i++
    ) {
        const id =
            messageSyncId(
                snapshot.chat[i],
            );

        if (!id) {
            continue;
        }

        if (
            seen.has(id)
        ) {
            throw new SyncError(
                'invalid_snapshot',
                'Duplicate synchronization message ID',
            );
        }

        seen.add(id);
    }
}


/* -------------------------------------------------------------------------- */
/* Snapshot lineage validation                                                */
/* -------------------------------------------------------------------------- */

function validateSnapshotLineage(
    snapshot,
    scope,
) {
    const metadata =
        snapshot.chatMetadata ||
        snapshot.chat?.[0]
            ?.chat_metadata ||
        {};

    const snapshotParent =
        metadata.main_chat !=
            null
            ? String(
                metadata.main_chat,
            )
            : null;

    const snapshotIntegrity =
        metadata.integrity !=
            null
            ? String(
                metadata.integrity,
            )
            : null;

    if (
        scope.branchId
    ) {
        if (
            !snapshotIntegrity ||
            snapshotIntegrity !==
                scope.branchId
        ) {
            throw new SyncError(
                'invalid_snapshot',
                'Branch integrity does not match sync scope',
            );
        }

        if (
            scope.parentChatId &&
            snapshotParent !==
                scope.parentChatId
        ) {
            throw new SyncError(
                'invalid_snapshot',
                'Branch parent chat does not match sync scope',
            );
        }
    }
}


/* -------------------------------------------------------------------------- */
/* Chat-file identity / path safety                                           */
/* -------------------------------------------------------------------------- */

function safeBasename(
    value,
    field,
) {
    const name =
        normalizeString(
            value,
            field,
            2048,
        );

    if (
        name.includes('/') ||
        name.includes('\\') ||
        name.includes('\0') ||
        name === '.' ||
        name === '..'
    ) {
        throw new SyncError(
            'invalid_scope',
            `Invalid ${field}`,
        );
    }

    return name;
}

function underParent(
    parent,
    target,
) {
    const parentResolved =
        path.resolve(
            parent,
        );

    const targetResolved =
        path.resolve(
            target,
        );

    if (
        targetResolved !==
            parentResolved &&
        !targetResolved.startsWith(
            `${parentResolved}${path.sep}`,
        )
    ) {
        throw new SyncError(
            'invalid_scope',
            'Resolved path escapes the user directory',
        );
    }

    return targetResolved;
}


/* -------------------------------------------------------------------------- */
/* Group validation                                                            */
/* -------------------------------------------------------------------------- */

async function getGroupForUser(
    req,
    groupId,
) {
    const userId =
        getAuthenticatedUserId(
            req,
        );

    const cacheKey =
        `${userId}:${groupId}`;

    const cached =
        groupCache.get(
            cacheKey,
        );

    if (
        cached &&
        now() -
            cached.at <
            GROUP_CACHE_MS
    ) {
        return cached.group;
    }

    const groupsDir =
        req.user
            ?.directories
            ?.groups;

    if (!groupsDir) {
        return null;
    }

    let files;

    try {
        files =
            await fsp.readdir(
                groupsDir,
            );
    } catch {
        return null;
    }

    for (
        const fileName of files
    ) {
        if (
            !fileName.endsWith(
                '.json',
            )
        ) {
            continue;
        }

        const fullPath =
            underParent(
                groupsDir,
                path.join(
                    groupsDir,
                    fileName,
                ),
            );

        try {
            const parsed =
                JSON.parse(
                    await fsp.readFile(
                        fullPath,
                        'utf8',
                    ),
                );

            if (
                String(parsed?.id) ===
                String(groupId)
            ) {
                groupCache.set(
                    cacheKey,
                    {
                        at:
                            now(),
                        group:
                            parsed,
                    },
                );

                return parsed;
            }
        } catch {
            // Ignore unrelated malformed files.
        }
    }

    return null;
}


/* -------------------------------------------------------------------------- */
/* Resolve actual ST chat file                                                */
/* -------------------------------------------------------------------------- */

async function resolveStChatPath(
    req,
    scope,
) {
    const userDirs =
        req.user?.directories;

    if (!userDirs) {
        throw new SyncError(
            'auth_required',
            'User directories unavailable',
            403,
        );
    }

    if (
        scope.scopeType ===
        'character'
    ) {
        /*
         * Current ST stores character chats under:
         *
         * <user>/chats/<character-avatar>/<chat>.jsonl
         *
         * The character avatar filename is the extension's characterId.
         */
        const characterDir =
            underParent(
                userDirs.chats,
                path.join(
                    userDirs.chats,
                    safeBasename(
                        scope.characterId,
                        'characterId',
                    ),
                ),
            );

        const fileName =
            safeBasename(
                scope.chatId,
                'chatId',
            );

        return {
            path:
                underParent(
                    characterDir,
                    path.join(
                        characterDir,
                        `${fileName}.jsonl`,
                    ),
                ),
            group:
                null,
        };
    }

    const group =
        await getGroupForUser(
            req,
            scope.groupId,
        );

    if (!group) {
        throw new SyncError(
            'invalid_scope',
            'Requested group does not belong to authenticated user',
            403,
        );
    }

    const groupChats =
        Array.isArray(
            group.chats,
        )
            ? group.chats.map(
                value =>
                    String(value),
            )
            : [];

    if (
        !groupChats.includes(
            String(scope.chatId),
        )
    ) {
        throw new SyncError(
            'invalid_scope',
            'Requested chat is not associated with the requested group',
            403,
        );
    }

    const groupChatsDir =
        userDirs.groupChats;

    const fileName =
        safeBasename(
            scope.chatId,
            'chatId',
        );

    return {
        path:
            underParent(
                groupChatsDir,
                path.join(
                    groupChatsDir,
                    `${fileName}.jsonl`,
                ),
            ),

        group,
    };
}


/* -------------------------------------------------------------------------- */
/* ST chat-file read cache                                                    */
/* -------------------------------------------------------------------------- */

function trimChatFileCache() {
    if (
        chatFileCache.size <=
        CHAT_FILE_CACHE_MAX
    ) {
        return;
    }

    const entries =
        [...chatFileCache.entries()]
            .sort(
                (
                    [, a],
                    [, b],
                ) =>
                    a.cachedAt -
                    b.cachedAt,
            );

    while (
        chatFileCache.size >
            CHAT_FILE_CACHE_MAX &&
        entries.length
    ) {
        const [
            key,
        ] =
            entries.shift();

        chatFileCache.delete(
            key,
        );
    }
}

async function readStChatSnapshot(
    req,
    scope,
    {
        force = false,
    } = {},
) {
    const {
        path: filePath,
    } =
        await resolveStChatPath(
            req,
            scope,
        );

    let stat;

    try {
        stat =
            await fsp.stat(
                filePath,
            );
    } catch (error) {
        if (
            error?.code ===
            'ENOENT'
        ) {
            return {
                exists: false,
                snapshot:
                    null,
                hash:
                    null,
                mtimeMs:
                    0,
                size:
                    0,
                filePath,
            };
        }

        throw error;
    }

    const cached =
        chatFileCache.get(
            filePath,
        );

    if (
        !force &&
        cached &&
        cached.mtimeMs ===
            stat.mtimeMs &&
        cached.size ===
            stat.size
    ) {
        return clone(
            cached.result,
        );
    }

    const raw =
        await fsp.readFile(
            filePath,
            'utf8',
        );

    const lines =
        raw
            .replace(
                /^\uFEFF/,
                '',
            )
            .split(/\r?\n/)
            .filter(
                line =>
                    line.trim() !== '',
            );

    if (!lines.length) {
        const result = {
            exists: true,
            snapshot:
                null,
            hash:
                null,
            mtimeMs:
                stat.mtimeMs,
            size:
                stat.size,
            filePath,
        };

        chatFileCache.set(
            filePath,
            {
                ...result,
                cachedAt:
                    now(),
            },
        );

        trimChatFileCache();

        return clone(result);
    }

    const chat = [];

    for (
        const line of lines
    ) {
        let parsed;

        try {
            parsed =
                JSON.parse(
                    line,
                );
        } catch {
            throw new SyncError(
                'st_file_invalid',
                'SillyTavern chat file contains invalid JSON',
                409,
            );
        }

        if (
            !parsed ||
            typeof parsed !==
                'object' ||
            Array.isArray(
                parsed,
            )
        ) {
            throw new SyncError(
                'st_file_invalid',
                'SillyTavern chat file contains an invalid record',
                409,
            );
        }

        chat.push(
            parsed,
        );
    }

    const chatMetadata =
        chat[0]
            ?.chat_metadata &&
        typeof chat[0]
            .chat_metadata ===
            'object'
            ? clone(
                chat[0]
                    .chat_metadata,
            )
            : {};

    const snapshot = {
        chat,
        chatMetadata,
    };

    validateSnapshotShape(
        snapshot,
    );

    validateNoDuplicateMessageIds(
        snapshot,
    );

    const result = {
        exists: true,

        snapshot,

        hash:
            sha256(
                snapshot,
            ),

        mtimeMs:
            stat.mtimeMs,

        size:
            stat.size,

        filePath,
    };

    chatFileCache.set(
        filePath,
        {
            ...clone(result),
            cachedAt:
                now(),
        },
    );

    trimChatFileCache();

    return clone(
        result,
    );
}


/* -------------------------------------------------------------------------- */
/* Message-ID migration comparison                                            */
/* -------------------------------------------------------------------------- */

function stripSyncIds(
    snapshot,
) {
    const result =
        clone(snapshot);

    for (
        let i = 1;
        i <
            result.chat.length;
        i++
    ) {
        const extra =
            result.chat[i]?.extra;

        if (
            extra &&
            typeof extra ===
                'object'
        ) {
            const sync =
                extra.multi_client_sync;

            if (
                sync &&
                typeof sync ===
                    'object'
            ) {
                delete extra.multi_client_sync;

                if (
                    Object.keys(
                        sync,
                    ).length ===
                        0
                ) {
                    delete extra.multi_client_sync;
                }
            }
        }
    }

    return result;
}

function sameIgnoringSyncIds(
    a,
    b,
) {
    if (!a || !b) {
        return false;
    }

    return sameValue(
        stripSyncIds(a),
        stripSyncIds(b),
    );
}


/* -------------------------------------------------------------------------- */
/* Public state                                                               */
/* -------------------------------------------------------------------------- */

function publicGeneration(
    generation,
) {
    if (!generation) {
        return null;
    }

    return {
        id:
            generation.id,

        ownerClientId:
            generation.ownerClientId,

        ownerDeviceId:
            generation.ownerDeviceId,

        type:
            generation.type,

        targetMessageId:
            generation.targetMessageId ||
            null,

        state:
            generation.state,

        startedAt:
            generation.startedAt,

        leaseUntil:
            generation.leaseUntil,

        streamSeq:
            generation.streamSeq,

        stopRequested:
            Boolean(
                generation.stopRequested,
            ),

        stopRequesterClientId:
            generation.stopRequesterClientId ||
            null,
    };
}

function publicState(
    record,
    {
        includeSnapshot = true,
    } = {},
) {
    return {
        protocolVersion:
            PROTOCOL_VERSION,

        schemaVersion:
            STATE_SCHEMA_VERSION,

        epoch:
            runtimeEpoch,

        scope:
            clone(record.scope),

        revision:
            record.revision,

        seq:
            record.seq,

        lastEventId:
            record.seq > 0
                ? eventId(
                    record.seq,
                )
                : null,

        snapshot:
            includeSnapshot &&
            record.snapshot
                ? clone(
                    record.snapshot,
                )
                : null,

        snapshotHash:
            record.snapshotHash,

        generation:
            publicGeneration(
                record.generation,
            ),
    };
}


/* -------------------------------------------------------------------------- */
/* Operation idempotency                                                      */
/* -------------------------------------------------------------------------- */

function rememberOperation(
    record,
    opId,
    result,
) {
    if (!opId) {
        return;
    }

    if (
        !record.seenOps.includes(
            opId,
        )
    ) {
        record.seenOps.push(
            opId,
        );
    }

    record.opResults.set(
        opId,
        clone(result),
    );

    while (
        record.seenOps.length >
        MAX_OPERATION_HISTORY
    ) {
        const oldest =
            record.seenOps.shift();

        record.opResults.delete(
            oldest,
        );
    }
}

function findOperation(
    record,
    opId,
) {
    if (
        !opId ||
        !record.seenOps.includes(
            opId,
        )
    ) {
        return null;
    }

    return clone(
        record.opResults.get(
            opId,
        ) || {
            duplicate:
                true,
            state:
                publicState(
                    record,
                ),
        },
    );
}


/* -------------------------------------------------------------------------- */
/* Replay event storage                                                       */
/* -------------------------------------------------------------------------- */

function appendEvent(
    record,
    {
        type,
        opId = null,
        sourceClientId = null,
        sourceDeviceId = null,
        baseRevision = null,
        payload = {},
        generation = null,
    },
) {
    record.seq += 1;

    const stored = {
        id:
            eventId(
                record.seq,
            ),

        epoch:
            runtimeEpoch,

        seq:
            record.seq,

        revision:
            record.revision,

        baseRevision,

        timestamp:
            now(),

        type,

        opId,

        sourceClientId,

        sourceDeviceId,

        payload:
            clone(payload),

        generation:
            generation
                ? publicGeneration(
                    generation,
                )
                : null,
    };

    record.events.push(
        stored,
    );

    if (
        record.events.length >
        MAX_REPLAY_EVENTS
    ) {
        record.events =
            record.events.slice(
                -MAX_REPLAY_EVENTS,
            );
    }

    while (
        record.events.length &&
        byteLength(
            record.events,
        ) >
            MAX_REPLAY_BYTES
    ) {
        record.events.shift();
    }

    return clone(
        stored,
    );
}


/* -------------------------------------------------------------------------- */
/* Snapshot live patch generation                                             */
/* -------------------------------------------------------------------------- */

function makeSnapshotPatch(
    previous,
    next,
) {
    if (!previous) {
        return {
            kind:
                'full',

            snapshot:
                clone(next),
        };
    }

    const prevChat =
        previous.chat || [];

    const nextChat =
        next.chat || [];

    /*
     * Append-only optimization.
     */
    if (
        nextChat.length >
        prevChat.length
    ) {
        let prefixMatches =
            true;

        for (
            let i = 1;
            i <
                prevChat.length;
            i++
        ) {
            if (
                messageSyncId(
                    prevChat[i],
                ) !==
                messageSyncId(
                    nextChat[i],
                )
            ) {
                prefixMatches =
                    false;
                break;
            }
        }

        if (
            prefixMatches
        ) {
            const appended =
                nextChat
                    .slice(
                        prevChat.length,
                    )
                    .map(
                        clone,
                    );

            return {
                kind:
                    'append',

                startIndex:
                    prevChat.length,

                messages:
                    appended,

                chatMetadata:
                    sameValue(
                        previous.chatMetadata ||
                            {},
                        next.chatMetadata ||
                            {},
                    )
                        ? null
                        : clone(
                            next.chatMetadata ||
                                {},
                        ),
            };
        }
    }

    /*
     * If the number/order of stable message IDs changed, a full snapshot is
     * the safest representation.
     */
    if (
        prevChat.length !==
        nextChat.length
    ) {
        return {
            kind:
                'full',

            snapshot:
                clone(next),
        };
    }

    for (
        let i = 1;
        i <
            prevChat.length;
        i++
    ) {
        if (
            messageSyncId(
                prevChat[i],
            ) !==
            messageSyncId(
                nextChat[i],
            )
        ) {
            return {
                kind:
                    'full',

                snapshot:
                    clone(next),
            };
        }
    }

    const changes = [];

    for (
        let i = 1;
        i <
            nextChat.length;
        i++
    ) {
        if (
            !sameValue(
                prevChat[i],
                nextChat[i],
            )
        ) {
            changes.push({
                index:
                    i,

                message:
                    clone(
                        nextChat[i],
                    ),
            });
        }
    }

    const metadataChanged =
        !sameValue(
            previous.chatMetadata ||
                {},
            next.chatMetadata ||
                {},
        );

    return {
        kind:
            'patch',

        changes,

        chatMetadata:
            metadataChanged
                ? clone(
                    next.chatMetadata ||
                        {},
                )
                : null,
    };
}


/* -------------------------------------------------------------------------- */
/* SSE delivery                                                               */
/* -------------------------------------------------------------------------- */

function sendSse(
    res,
    event,
    data,
    id = null,
) {
    if (
        res.writableEnded
    ) {
        return;
    }

    if (id) {
        res.write(
            `id: ${id}\n`,
        );
    }

    if (event) {
        res.write(
            `event: ${event}\n`,
        );
    }

    const encoded =
        JSON.stringify(
            data,
        );

    for (
        const line of
            encoded.split('\n')
    ) {
        res.write(
            `data: ${line}\n`,
        );
    }

    res.write('\n');
}

function addSseClient(
    record,
    clientId,
    response,
) {
    let clientMap =
        sseClients.get(
            record.key,
        );

    if (!clientMap) {
        clientMap =
            new Map();

        sseClients.set(
            record.key,
            clientMap,
        );
    }

    let responseSet =
        clientMap.get(
            clientId,
        );

    if (!responseSet) {
        responseSet =
            new Set();

        clientMap.set(
            clientId,
            responseSet,
        );
    }

    if (
        responseSet.size >=
        MAX_SSE_PER_CLIENT
    ) {
        throw new SyncError(
            'sse_limit',
            'Too many SSE connections',
            429,
        );
    }

    responseSet.add(
        response,
    );

    return () => {
        responseSet.delete(
            response,
        );

        if (
            responseSet.size ===
            0
        ) {
            clientMap.delete(
                clientId,
            );
        }

        if (
            clientMap.size ===
            0
        ) {
            sseClients.delete(
                record.key,
            );
        }
    };
}

function broadcastLiveEvent(
    record,
    event,
    patch,
) {
    const clients =
        sseClients.get(
            record.key,
        );

    if (!clients) {
        return;
    }

    const state =
        publicState(
            record,
            {
                includeSnapshot:
                    false,
            },
        );

    const envelope = {
        ...clone(event),

        state,

        patch:
            patch
                ? clone(
                    patch,
                )
                : null,
    };

    for (
        const responseSet of
            clients.values()
    ) {
        for (
            const res of
                responseSet
        ) {
            try {
                sendSse(
                    res,
                    'sync',
                    envelope,
                    event.id,
                );
            } catch {
                try {
                    res.end();
                } catch {
                    // ignored
                }
            }
        }
    }
}


/* -------------------------------------------------------------------------- */
/* Subscription token                                                         */
/* -------------------------------------------------------------------------- */

function issueSubscriptionToken(
    userId,
    scope,
    clientId,
    deviceId,
) {
    const payload = {
        v:
            PROTOCOL_VERSION,

        user:
            userId,

        scope:
            scopeKey(
                userId,
                scope,
            ),

        clientId,

        deviceId,

        exp:
            now() +
            SUBSCRIPTION_TOKEN_TTL_MS,

        nonce:
            randomId(),
    };

    const body =
        base64urlEncode(
            JSON.stringify(
                payload,
            ),
        );

    const signature =
        hmac(
            `sub:${body}`,
        );

    return `${body}.${signature}`;
}

function verifySubscriptionToken(
    token,
) {
    if (
        typeof token !==
            'string' ||
        !token.includes('.')
    ) {
        throw new SyncError(
            'invalid_subscription',
            'Invalid SSE subscription',
            403,
        );
    }

    const [
        body,
        suppliedSignature,
    ] =
        token.split(
            '.',
        );

    const expectedSignature =
        hmac(
            `sub:${body}`,
        );

    const left =
        Buffer.from(
            suppliedSignature,
        );

    const right =
        Buffer.from(
            expectedSignature,
        );

    if (
        left.length !==
            right.length ||
        !crypto.timingSafeEqual(
            left,
            right,
        )
    ) {
        throw new SyncError(
            'invalid_subscription',
            'Invalid SSE subscription',
            403,
        );
    }

    let parsed;

    try {
        parsed =
            JSON.parse(
                base64urlDecode(
                    body,
                ),
            );
    } catch {
        throw new SyncError(
            'invalid_subscription',
            'Invalid SSE subscription',
            403,
        );
    }

    if (
        parsed.v !==
        PROTOCOL_VERSION ||
        parsed.exp <=
            now()
    ) {
        throw new SyncError(
            'subscription_expired',
            'SSE subscription expired',
            403,
        );
    }

    return parsed;
}


/* -------------------------------------------------------------------------- */
/* Rate limiting                                                              */
/* -------------------------------------------------------------------------- */

function consumeRate(
    userId,
    category,
) {
    const limit =
        RATE_LIMITS[
            category
        ] ??
        RATE_LIMITS.read;

    const key =
        `${userId}:${category}`;

    let bucket =
        rateBuckets.get(
            key,
        );

    const timestamp =
        now();

    if (
        !bucket ||
        timestamp -
            bucket.startedAt >=
            RATE_WINDOW_MS
    ) {
        bucket = {
            startedAt:
                timestamp,

            count:
                0,
        };

        rateBuckets.set(
            key,
            bucket,
        );
    }

    bucket.count +=
        1;

    if (
        bucket.count >
        limit
    ) {
        throw new SyncError(
            'rate_limited',
            'Too many synchronization requests',
            429,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Membership                                                                  */
/* -------------------------------------------------------------------------- */

function requireMember(
    record,
    clientId,
    deviceId,
) {
    const member =
        record.members.get(
            clientId,
        );

    if (!member) {
        throw new SyncError(
            'not_member',
            'Client has not joined this synchronization scope',
            403,
        );
    }

    if (
        member.deviceId !==
        deviceId
    ) {
        throw new SyncError(
            'device_mismatch',
            'Client/device identity mismatch',
            409,
        );
    }

    if (
        member.expiresAt <=
        now()
    ) {
        record.members.delete(
            clientId,
        );

        throw new SyncError(
            'membership_expired',
            'Synchronization membership expired',
            403,
        );
    }

    member.lastSeen =
        now();

    member.expiresAt =
        now() +
        MEMBER_TTL_MS;

    record.lastAccessAt =
        now();

    return member;
}


/* -------------------------------------------------------------------------- */
/* Generation expiry                                                          */
/* -------------------------------------------------------------------------- */

function abandonGeneration(
    record,
    reason,
) {
    const generation =
        record.generation;

    if (!generation) {
        return;
    }

    const previousRevision =
        record.revision;

    generation.state =
        'abandoned';

    generation.leaseUntil =
        0;

    record.revision +=
        1;

    const event =
        appendEvent(
            record,
            {
                type:
                    'generation_abandoned',

                opId:
                    null,

                sourceClientId:
                    generation.ownerClientId,

                sourceDeviceId:
                    generation.ownerDeviceId,

                baseRevision:
                    previousRevision,

                payload: {
                    generationId:
                        generation.id,

                    reason,
                },

                generation,
            },
        );

    record.generation =
        null;

    rememberOperation(
        record,
        randomId(),
        {
            state:
                publicState(
                    record,
                ),
        },
    );

    broadcastLiveEvent(
        record,
        event,
        null,
    );

    void persistScope(
        record,
        true,
    );
}

function checkGenerationLease(
    record,
) {
    const generation =
        record.generation;

    if (!generation) {
        return;
    }

    const timestamp =
        now();

    if (
        timestamp -
            generation.startedAt >
        GENERATION_MAX_MS
    ) {
        abandonGeneration(
            record,
            'maximum_generation_lifetime',
        );

        return;
    }

    if (
        generation.leaseUntil <=
        timestamp
    ) {
        abandonGeneration(
            record,
            'lease_expired',
        );

        return;
    }

    if (
        !record.members.has(
            generation.ownerClientId,
        )
    ) {
        abandonGeneration(
            record,
            'owner_membership_lost',
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Revision helpers                                                           */
/* -------------------------------------------------------------------------- */

function requireBaseRevision(
    record,
    baseRevision,
) {
    const numeric =
        Number(
            baseRevision,
        );

    if (
        !Number.isSafeInteger(
            numeric,
        ) ||
        numeric < 0
    ) {
        throw new SyncError(
            'invalid_revision',
            'Invalid base revision',
        );
    }

    if (
        numeric !==
        record.revision
    ) {
        throw new SyncError(
            'stale_revision',
            'Client state is stale',
            409,
            {
                state:
                    publicState(
                        record,
                    ),
            },
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Persistence                                                                */
/* -------------------------------------------------------------------------- */

function getRecordFilePath(
    record,
) {
    return path.join(
        stateRoot,
        `${safeStorageHash(
            record.key,
        )}.json`,
    );
}

async function ensurePersistenceRoot() {
    dataRoot =
        path.resolve(
            globalThis.DATA_ROOT ||
                path.join(
                    process.cwd(),
                    'data',
                ),
        );

    pluginRoot =
        path.join(
            dataRoot,
            DATA_DIR_NAME,
        );

    stateRoot =
        path.join(
            pluginRoot,
            STATE_DIR_NAME,
        );

    secretPath =
        path.join(
            pluginRoot,
            SECRET_FILE_NAME,
        );

    await fsp.mkdir(
        stateRoot,
        {
            recursive:
                true,
        },
    );

    try {
        principalSecret =
            await fsp.readFile(
                secretPath,
            );
    } catch {
        principalSecret =
            crypto.randomBytes(
                32,
            );

        const temp =
            `${secretPath}.${process.pid}.tmp`;

        await fsp.writeFile(
            temp,
            principalSecret,
            {
                mode:
                    0o600,
            },
        );

        await fsp.rename(
            temp,
            secretPath,
        );
    }
}

function persistedRepresentation(
    record,
) {
    return {
        schemaVersion:
            STATE_SCHEMA_VERSION,

        key:
            record.key,

        userId:
            record.userId,

        scope:
            record.scope,

        revision:
            record.revision,

        seq:
            record.seq,

        snapshot:
            record.snapshot,

        snapshotHash:
            record.snapshotHash,

        events:
            record.events,

        seenOps:
            record.seenOps,

        opResults:
            Object.fromEntries(
                record.opResults
                    .entries(),
            ),

        lastAccessAt:
            record.lastAccessAt,

        persistedRevision:
            record.persistedRevision,
    };
}

function rebuildPersistedBytesByUser() {
    persistedBytesByUser.clear();

    for (
        const record of
            scopes.values()
    ) {
        const previous =
            persistedBytesByUser.get(
                record.userId,
            ) || 0;

        persistedBytesByUser.set(
            record.userId,
            previous +
                record.persistedBytes,
        );
    }
}

async function writeScopeNow(
    record,
) {
    if (
        !stateRoot
    ) {
        return;
    }

    const serialized =
        JSON.stringify(
            persistedRepresentation(
                record,
            ),
        );

    const newBytes =
        Buffer.byteLength(
            serialized,
            'utf8',
        );

    const currentUserBytes =
        persistedBytesByUser.get(
            record.userId,
        ) || 0;

    const proposed =
        currentUserBytes -
        record.persistedBytes +
        newBytes;

    if (
        proposed >
        MAX_PERSISTED_BYTES_PER_USER
    ) {
        throw new SyncError(
            'storage_quota',
            'Synchronization mirror storage quota exceeded',
            507,
        );
    }

    const filePath =
        getRecordFilePath(
            record,
        );

    const tempPath =
        `${filePath}.${process.pid}.tmp`;

    await fsp.writeFile(
        tempPath,
        serialized,
        {
            encoding:
                'utf8',

            mode:
                0o600,
        },
    );

    await fsp.rename(
        tempPath,
        filePath,
    );

    persistedBytesByUser.set(
        record.userId,
        proposed,
    );

    record.persistedBytes =
        newBytes;

    record.persistedRevision =
        record.revision;
}

function persistScope(
    record,
    immediate = false,
) {
    record.persistChain =
        record.persistChain.then(
            async () => {
                if (
                    !immediate &&
                    record.persistedRevision ===
                        record.revision
                ) {
                    return;
                }

                await writeScopeNow(
                    record,
                );
            },
        ).catch(
            error => {
                console.error(
                    `[${PLUGIN_ID}] persistence failure for scope`,
                    record.key,
                    error,
                );

                throw error;
            },
        );

    return record.persistChain;
}

async function loadPersistedState() {
    const files =
        await fsp.readdir(
            stateRoot,
        );

    for (
        const filename of
            files
    ) {
        if (
            !filename.endsWith(
                '.json',
            )
        ) {
            continue;
        }

        const filePath =
            path.join(
                stateRoot,
                filename,
            );

        try {
            const raw =
                await fsp.readFile(
                    filePath,
                    'utf8',
                );

            const parsed =
                JSON.parse(
                    raw,
                );

            if (
                parsed?.schemaVersion !==
                    STATE_SCHEMA_VERSION ||
                typeof parsed?.key !==
                    'string' ||
                typeof parsed?.userId !==
                    'string' ||
                !parsed?.scope
            ) {
                continue;
            }

            const scope =
                normalizeScope(
                    parsed.scope,
                );

            const record =
                createScopeRecord(
                    parsed.key,
                    parsed.userId,
                    scope,
                );

            record.revision =
                Number.isSafeInteger(
                    parsed.revision,
                )
                    ? parsed.revision
                    : 0;

            record.seq =
                Number.isSafeInteger(
                    parsed.seq,
                )
                    ? parsed.seq
                    : 0;

            record.snapshot =
                parsed.snapshot
                    ? clone(
                        parsed.snapshot,
                    )
                    : null;

            record.snapshotHash =
                typeof parsed.snapshotHash ===
                    'string'
                    ? parsed.snapshotHash
                    : record.snapshot
                        ? sha256(
                            record.snapshot,
                        )
                        : null;

            record.events =
                Array.isArray(
                    parsed.events,
                )
                    ? parsed.events
                        .slice(
                            -MAX_REPLAY_EVENTS,
                        )
                        .map(
                            clone,
                        )
                    : [];

            record.seenOps =
                Array.isArray(
                    parsed.seenOps,
                )
                    ? parsed.seenOps
                        .slice(
                            -MAX_OPERATION_HISTORY,
                        )
                    : [];

            record.opResults =
                new Map(
                    Object.entries(
                        parsed.opResults ||
                            {},
                    ),
                );

            record.lastAccessAt =
                Number.isFinite(
                    parsed.lastAccessAt,
                )
                    ? parsed.lastAccessAt
                    : now();

            try {
                const stat =
                    await fsp.stat(
                        filePath,
                    );

                record.persistedBytes =
                    stat.size;
            } catch {
                record.persistedBytes =
                    0;
            }

            record.persistedRevision =
                Number.isSafeInteger(
                    parsed.persistedRevision,
                )
                    ? parsed.persistedRevision
                    : record.revision;

            /*
             * Never restore active generation ownership across server restart.
             * The new server epoch fences every previous owner.
             */
            record.generation =
                null;
        } catch (error) {
            console.warn(
                `[${PLUGIN_ID}] Ignoring invalid persisted state ${filename}:`,
                error?.message ||
                    error,
            );
        }
    }

    rebuildPersistedBytesByUser();
}


/* -------------------------------------------------------------------------- */
/* Liveness / memory cleanup                                                  */
/* -------------------------------------------------------------------------- */

function cleanRuntimeState() {
    const timestamp =
        now();

    for (
        const record of
            scopes.values()
    ) {
        for (
            const [
                clientId,
                member,
            ] of record.members
        ) {
            if (
                member.expiresAt <=
                timestamp
            ) {
                record.members.delete(
                    clientId,
                );
            }
        }

        if (
            record.generation
        ) {
            checkGenerationLease(
                record,
            );
        }
    }

    if (
        scopes.size >
        MAX_SCOPES_IN_MEMORY
    ) {
        const candidates =
            [
                ...scopes.values(),
            ]
                .filter(
                    record =>
                        record.members.size ===
                            0 &&
                        !record.generation &&
                        timestamp -
                            record.lastAccessAt >
                            SCOPE_MEMORY_IDLE_MS,
                )
                .sort(
                    (
                        a,
                        b,
                    ) =>
                        a.lastAccessAt -
                        b.lastAccessAt,
                );

        while (
            scopes.size >
                MAX_SCOPES_IN_MEMORY &&
            candidates.length
        ) {
            const record =
                candidates.shift();

            scopes.delete(
                record.key,
            );
        }
    }

    for (
        const [
            key,
            bucket,
        ] of rateBuckets
    ) {
        if (
            timestamp -
                bucket.startedAt >
            RATE_WINDOW_MS * 2
        ) {
            rateBuckets.delete(
                key,
            );
        }
    }

    for (
        const [
            key,
            cached,
        ] of groupCache
    ) {
        if (
            timestamp -
                cached.at >
            GROUP_CACHE_MS * 10
        ) {
            groupCache.delete(
                key,
            );
        }
    }

    for (
        const [
            key,
            cached,
        ] of chatFileCache
    ) {
        if (
            timestamp -
                cached.cachedAt >
            60_000
        ) {
            chatFileCache.delete(
                key,
            );
        }
    }
}


/* -------------------------------------------------------------------------- */
/* Error response                                                             */
/* -------------------------------------------------------------------------- */

function sendError(
    res,
    error,
) {
    const syncError =
        error instanceof SyncError
            ? error
            : new SyncError(
                'internal_error',
                'Synchronization request failed',
                500,
            );

    const body = {
        ok:
            false,

        code:
            syncError.code,

        message:
            syncError.message,
    };

    if (
        syncError.state
    ) {
        body.state =
            syncError.state;
    }

    if (
        syncError.expectedHash
    ) {
        body.expectedHash =
            syncError.expectedHash;
    }

    if (
        syncError.actualHash
    ) {
        body.actualHash =
            syncError.actualHash;
    }

    return res
        .status(
            syncError.status,
        )
        .json(
            body,
        );
}


/* -------------------------------------------------------------------------- */
/* Initialization                                                             */
/* -------------------------------------------------------------------------- */

async function init(
    router,
) {
    if (
        initialized
    ) {
        return;
    }

    shuttingDown =
        false;

    /*
     * If persistence setup fails, the plugin remains available as a memory-only
     * synchronization server rather than throwing and risking the host.
     */
    try {
        await ensurePersistenceRoot();
        await loadPersistedState();
    } catch (error) {
        console.error(
            `[${PLUGIN_ID}] durable mirror unavailable; continuing memory-only:`,
            error,
        );

        dataRoot =
            path.resolve(
                globalThis.DATA_ROOT ||
                    path.join(
                        process.cwd(),
                        'data',
                    ),
            );

        pluginRoot =
            path.join(
                dataRoot,
                DATA_DIR_NAME,
            );

        stateRoot =
            path.join(
                pluginRoot,
                STATE_DIR_NAME,
            );

        principalSecret =
            crypto.randomBytes(
                32,
            );
    }


    /* ---------------------------------------------------------------------- */
    /* Common middleware                                                       */
    /* ---------------------------------------------------------------------- */

    router.use(
        (req, res, next) => {
            try {
                /*
                 * ST's current server puts req.user and global CSRF protection
                 * in front of private API routes. We still enforce the user
                 * check here so the plugin never trusts routing order alone.
                 */
                const userId =
                    getAuthenticatedUserId(
                        req,
                    );

                req.mcsUserId =
                    userId;

                consumeRate(
                    userId,
                    req.method ===
                        'GET'
                        ? 'read'
                        : 'mutate',
                );

                const bodySize =
                    req.body &&
                    typeof req.body ===
                        'object'
                        ? byteLength(
                            req.body,
                        )
                        : 0;

                if (
                    bodySize >
                    MAX_REQUEST_BYTES
                ) {
                    throw new SyncError(
                        'payload_too_large',
                        'Request exceeds synchronization payload limit',
                        413,
                    );
                }

                if (
                    req.body
                ) {
                    validateDataTree(
                        req.body,
                    );
                }

                res.setHeader(
                    'Cache-Control',
                    'no-store',
                );

                next();
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* HEALTH                                                                  */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/health',
        async (
            req,
            res,
        ) => {
            try {
                return res.json({
                    ok:
                        true,

                    plugin:
                        PLUGIN_ID,

                    protocolVersion:
                        PROTOCOL_VERSION,

                    schemaVersion:
                        STATE_SCHEMA_VERSION,

                    userKey:
                        makePrincipalKey(
                            req.mcsUserId,
                        ),

                    epoch:
                        runtimeEpoch,

                    capabilities: {
                        revisions:
                            true,

                        idempotency:
                            true,

                        replay:
                            true,

                        sse:
                            true,

                        generationLease:
                            true,

                        generationStop:
                            true,

                        messageStableIds:
                            true,

                        branchLineage:
                            true,

                        durableMirror:
                            true,

                        stFileVerification:
                            true,

                        snapshotPatches:
                            true,
                    },
                });
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* JOIN                                                                    */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/join',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    req.mcsUserId;

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const clientId =
                    normalizeString(
                        req.body?.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.body?.deviceId,
                        'deviceId',
                        256,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                let record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    record =
                        createScopeRecord(
                            key,
                            userId,
                            scope,
                        );
                }

                if (
                    !record.members.has(
                        clientId,
                    ) &&
                    record.members.size >=
                        MAX_CLIENTS_PER_SCOPE
                ) {
                    throw new SyncError(
                        'scope_client_limit',
                        'Too many connected clients for this chat',
                        429,
                    );
                }

                const actual =
                    await readStChatSnapshot(
                        req,
                        scope,
                        {
                            force:
                                true,
                        },
                    );

                /*
                 * First connection initializes the server mirror from the
                 * actual ST file whenever that file exists.
                 */
                if (
                    record.revision ===
                        0 &&
                    !record.snapshot &&
                    actual.snapshot
                ) {
                    validateSnapshotLineage(
                        actual.snapshot,
                        scope,
                    );

                    record.snapshot =
                        clone(
                            actual.snapshot,
                        );

                    record.snapshotHash =
                        actual.hash;

                    record.lastAccessAt =
                        now();

                    await persistScope(
                        record,
                        true,
                    );
                } else if (
                    record.snapshot &&
                    actual.snapshot &&
                    record.snapshotHash !==
                        actual.hash &&
                    sameIgnoringSyncIds(
                        record.snapshot,
                        actual.snapshot,
                    )
                ) {
                    /*
                     * Automatic legacy message-ID migration. The actual ST file
                     * is accepted as the newer canonical representation because
                     * the only semantic difference is our own sync metadata.
                     */
                    const previousRevision =
                        record.revision;

                    record.snapshot =
                        clone(
                            actual.snapshot,
                        );

                    record.snapshotHash =
                        actual.hash;

                    record.revision =
                        previousRevision +
                        1;

                    const migrationEvent =
                        appendEvent(
                            record,
                            {
                                type:
                                    'message_id_migration',

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    reason:
                                        'sync-id-normalization',
                                },
                            },
                        );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        migrationEvent,
                        makeSnapshotPatch(
                            null,
                            record.snapshot,
                        ),
                    );
                }

                const member =
                    record.members.get(
                        clientId,
                    );

                record.members.set(
                    clientId,
                    {
                        clientId,

                        deviceId,

                        joinedAt:
                            member?.joinedAt ||
                            now(),

                        lastSeen:
                            now(),

                        expiresAt:
                            now() +
                            MEMBER_TTL_MS,
                    },
                );

                record.lastAccessAt =
                    now();

                checkGenerationLease(
                    record,
                );

                const subscriptionToken =
                    issueSubscriptionToken(
                        userId,
                        scope,
                        clientId,
                        deviceId,
                    );

                await persistScope(
                    record,
                    false,
                );

                return res.json({
                    ok:
                        true,

                    principalKey:
                        makePrincipalKey(
                            userId,
                        ),

                    subscriptionToken,

                    scope:
                        clone(
                            scope,
                        ),

                    divergence:
                        actual.snapshot &&
                        record.snapshot &&
                        record.snapshotHash !==
                            actual.hash
                            ? {
                                detected:
                                    true,

                                serverHash:
                                    record.snapshotHash,

                                stHash:
                                    actual.hash,

                                stMtimeMs:
                                    actual.mtimeMs,

                                stSize:
                                    actual.size,
                            }
                            : null,

                    state:
                        publicState(
                            record,
                            {
                                includeSnapshot:
                                    true,
                            },
                        ),
                });
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* LEAVE                                                                   */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/leave',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    req.mcsUserId;

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const clientId =
                    normalizeString(
                        req.body?.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.body?.deviceId,
                        'deviceId',
                        256,
                    );

                const record =
                    getScope(
                        userId,
                        scope,
                    );

                if (!record) {
                    return res.json({
                        ok:
                            true,

                        left:
                            false,
                    });
                }

                const member =
                    record.members.get(
                        clientId,
                    );

                if (
                    member &&
                    member.deviceId !==
                        deviceId
                ) {
                    throw new SyncError(
                        'device_mismatch',
                        'Client/device identity mismatch',
                        409,
                    );
                }

                record.members.delete(
                    clientId,
                );

                if (
                    record.generation
                        ?.ownerClientId ===
                    clientId
                ) {
                    abandonGeneration(
                        record,
                        'owner_left',
                    );
                }

                record.lastAccessAt =
                    now();

                await persistScope(
                    record,
                    true,
                );

                return res.json({
                    ok:
                        true,

                    left:
                        true,
                });
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* HEARTBEAT                                                               */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/heartbeat',
        async (
            req,
            res,
        ) => {
            try {
                consumeRate(
                    req.mcsUserId,
                    'heartbeat',
                );

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const clientId =
                    normalizeString(
                        req.body?.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.body?.deviceId,
                        'deviceId',
                        256,
                    );

                const record =
                    getScope(
                        req.mcsUserId,
                        scope,
                    );

                if (!record) {
                    throw new SyncError(
                        'scope_not_found',
                        'Synchronization scope not found',
                        404,
                    );
                }

                const member =
                    requireMember(
                        record,
                        clientId,
                        deviceId,
                    );

                record.lastAccessAt =
                    now();

                checkGenerationLease(
                    record,
                );

                const generationId =
                    req.body?.generationId
                        ? String(
                            req.body
                                .generationId,
                        )
                        : null;

                if (
                    generationId &&
                    record.generation &&
                    record.generation.id ===
                        generationId &&
                    record.generation
                        .ownerClientId ===
                        clientId
                ) {
                    record.generation
                        .leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;
                }

                member.lastSeen =
                    now();

                member.expiresAt =
                    now() +
                    MEMBER_TTL_MS;

                return res.json({
                    ok:
                        true,

                    serverTime:
                        now(),

                    subscriptionToken:
                        issueSubscriptionToken(
                            req.mcsUserId,
                            scope,
                            clientId,
                            deviceId,
                        ),

                    state:
                        publicState(
                            record,
                            {
                                includeSnapshot:
                                    false,
                            },
                        ),
                });
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* STATE GET                                                               */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/state',
        async (
            req,
            res,
        ) => {
            try {
                const clientId =
                    normalizeString(
                        req.query.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.query.deviceId,
                        'deviceId',
                        256,
                    );

                const scope =
                    normalizeScope(
                        JSON.parse(
                            String(
                                req.query.scope,
                            ),
                        ),
                    );

                return stateHandler(
                    req,
                    res,
                    clientId,
                    deviceId,
                    scope,
                );
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* STATE POST                                                              */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/state',
        async (
            req,
            res,
        ) => {
            try {
                const clientId =
                    normalizeString(
                        req.body.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.body.deviceId,
                        'deviceId',
                        256,
                    );

                const scope =
                    normalizeScope(
                        req.body.scope,
                    );

                return stateHandler(
                    req,
                    res,
                    clientId,
                    deviceId,
                    scope,
                );
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    async function stateHandler(
        req,
        res,
        clientId,
        deviceId,
        scope,
    ) {
        const record =
            getScope(
                req.mcsUserId,
                scope,
            );

        if (!record) {
            throw new SyncError(
                'scope_not_found',
                'Synchronization scope not found',
                404,
            );
        }

        requireMember(
            record,
            clientId,
            deviceId,
        );

        checkGenerationLease(
            record,
        );

        return res.json({
            ok:
                true,

            state:
                publicState(
                    record,
                    {
                        includeSnapshot:
                            true,
                    },
                ),
        });
    }


    /* ---------------------------------------------------------------------- */
    /* SSE                                                                     */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/events',
        async (
            req,
            res,
        ) => {
            let cleanup =
                null;

            let keepalive =
                null;

            try {
                const token =
                    verifySubscriptionToken(
                        String(
                            req.query.token ||
                                '',
                        ),
                    );

                if (
                    token.user !==
                    req.mcsUserId
                ) {
                    throw new SyncError(
                        'invalid_subscription',
                        'Subscription user mismatch',
                        403,
                    );
                }

                const clientId =
                    normalizeString(
                        token.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        token.deviceId,
                        'deviceId',
                        256,
                    );

                const parsedScope =
                    parseScopeKey(
                        token.scope,
                    );

                const scope =
                    normalizeScope(
                        {
                            scopeType:
                                parsedScope
                                    .scopeType,

                            characterId:
                                parsedScope
                                    .characterId,

                            groupId:
                                parsedScope
                                    .groupId,

                            chatId:
                                parsedScope
                                    .chatId,

                            branchId:
                                parsedScope
                                    .branchId,

                            parentChatId:
                                parsedScope
                                    .parentChatId,
                        },
                    );

                const record =
                    getScope(
                        req.mcsUserId,
                        scope,
                    );

                if (!record) {
                    throw new SyncError(
                        'scope_not_found',
                        'Synchronization scope not found',
                        404,
                    );
                }

                requireMember(
                    record,
                    clientId,
                    deviceId,
                );

                checkGenerationLease(
                    record,
                );

                res.status(
                    200,
                );

                res.setHeader(
                    'Content-Type',
                    'text/event-stream; charset=utf-8',
                );

                res.setHeader(
                    'Cache-Control',
                    'no-cache, no-transform',
                );

                res.setHeader(
                    'Connection',
                    'keep-alive',
                );

                res.setHeader(
                    'X-Accel-Buffering',
                    'no',
                );

                if (
                    typeof res.flushHeaders ===
                    'function'
                ) {
                    res.flushHeaders();
                }

                cleanup =
                    addSseClient(
                        record,
                        clientId,
                        res,
                    );

                sendSse(
                    res,
                    'hello',
                    {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        schemaVersion:
                            STATE_SCHEMA_VERSION,

                        epoch:
                            runtimeEpoch,

                        seq:
                            record.seq,

                        revision:
                            record.revision,

                        lastEventId:
                            record.seq > 0
                                ? eventId(
                                    record.seq,
                                )
                                : null,

                        snapshotHash:
                            record.snapshotHash,

                        generation:
                            publicGeneration(
                                record.generation,
                            ),
                    },
                );

                const cursor =
                    parseEventId(
                        req.get(
                            'Last-Event-ID',
                        ) ||
                            req.query.since ||
                            '',
                    );

                if (
                    cursor
                ) {
                    if (
                        cursor.epoch !==
                        runtimeEpoch
                    ) {
                        sendSse(
                            res,
                            'resync_required',
                            {
                                reason:
                                    'server_epoch_changed',

                                epoch:
                                    runtimeEpoch,

                                seq:
                                    record.seq,

                                revision:
                                    record.revision,
                            },
                        );
                    } else {
                        const firstSeq =
                            record.events.length
                                ? record.events[0]
                                      .seq
                                : record.seq +
                                      1;

                        if (
                            cursor.seq <
                            firstSeq -
                                1
                        ) {
                            sendSse(
                                res,
                                'resync_required',
                                {
                                    reason:
                                        'replay_window_exceeded',

                                    epoch:
                                        runtimeEpoch,

                                    seq:
                                        record.seq,

                                    revision:
                                        record.revision,
                                },
                            );
                        } else {
                            let replayed =
                                0;

                            for (
                                const event of
                                    record.events
                            ) {
                                if (
                                    event.seq <=
                                    cursor.seq
                                ) {
                                    continue;
                                }

                                /*
                                 * Historical replay contains metadata only.
                                 * The client requests /state at replay completion.
                                 */
                                sendSse(
                                    res,
                                    'replay',
                                    clone(
                                        event,
                                    ),
                                    event.id,
                                );

                                replayed +=
                                    1;
                            }

                            sendSse(
                                res,
                                'replay_complete',
                                {
                                    replayed,

                                    currentSeq:
                                        record.seq,

                                    currentRevision:
                                        record.revision,

                                    epoch:
                                        runtimeEpoch,
                                },
                            );
                        }
                    }
                }

                keepalive =
                    setInterval(
                        () => {
                            try {
                                if (
                                    res.writableEnded
                                ) {
                                    return;
                                }

                                res.write(
                                    `: keepalive ${now()}\n\n`,
                                );

                                const member =
                                    record.members.get(
                                        clientId,
                                    );

                                if (
                                    member
                                ) {
                                    member.lastSeen =
                                        now();

                                    member.expiresAt =
                                        now() +
                                        MEMBER_TTL_MS;
                                }

                                if (
                                    record
                                        .generation
                                        ?.ownerClientId ===
                                    clientId
                                ) {
                                    record
                                        .generation
                                        .leaseUntil =
                                        now() +
                                        GENERATION_LEASE_MS;
                                }
                            } catch {
                                try {
                                    res.end();
                                } catch {
                                    // ignored
                                }
                            }
                        },
                        SSE_KEEPALIVE_MS,
                    );

                const close =
                    () => {
                        if (
                            keepalive
                        ) {
                            clearInterval(
                                keepalive,
                            );

                            keepalive =
                                null;
                        }

                        if (
                            cleanup
                        ) {
                            cleanup();
                            cleanup =
                                null;
                        }
                    };

                req.on(
                    'close',
                    close,
                );

                res.on(
                    'close',
                    close,
                );
            } catch (error) {
                if (
                    keepalive
                ) {
                    clearInterval(
                        keepalive,
                    );
                }

                if (
                    cleanup
                ) {
                    cleanup();
                }

                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* EVENT                                                                   */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/event',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    req.mcsUserId;

                const clientId =
                    normalizeString(
                        req.body.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    normalizeString(
                        req.body.deviceId,
                        'deviceId',
                        256,
                    );

                const opId =
                    normalizeString(
                        req.body.opId,
                        'opId',
                        256,
                    );

                const type =
                    normalizeString(
                        req.body.type,
                        'type',
                        128,
                    );

                const scope =
                    normalizeScope(
                        req.body.scope,
                    );

                const record =
                    getScope(
                        userId,
                        scope,
                    );

                if (!record) {
                    throw new SyncError(
                        'scope_not_found',
                        'Synchronization scope not found',
                        404,
                    );
                }

                requireMember(
                    record,
                    clientId,
                    deviceId,
                );

                checkGenerationLease(
                    record,
                );

                const duplicate =
                    findOperation(
                        record,
                        opId,
                    );

                if (
                    duplicate
                ) {
                    return res.json({
                        ok:
                            true,

                        ...duplicate,
                    });
                }

                const baseRevision =
                    Number(
                        req.body
                            .baseRevision,
                    );

                const payload =
                    req.body.payload ||
                    {};

                validateDataTree(
                    payload,
                );

                /*
                 * Generation claim.
                 */
                if (
                    type ===
                    'generation_claim'
                ) {
                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    if (
                        record.generation
                    ) {
                        throw new SyncError(
                            'generation_owned',
                            'Another client already owns generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const generationId =
                        normalizeString(
                            req.body
                                .generationId,
                            'generationId',
                            256,
                        );

                    const generation = {
                        id:
                            generationId,

                        ownerClientId:
                            clientId,

                        ownerDeviceId:
                            deviceId,

                        type:
                            normalizeString(
                                String(
                                    req.body
                                        .generationType ||
                                        'unknown',
                                ),
                                'generationType',
                                128,
                            ),

                        targetMessageId:
                            req.body
                                .targetMessageId
                                ? String(
                                    req.body
                                        .targetMessageId,
                                )
                                : null,

                        state:
                            'claimed',

                        startedAt:
                            now(),

                        leaseUntil:
                            now() +
                            GENERATION_LEASE_MS,

                        streamSeq:
                            0,

                        stopRequested:
                            false,

                        stopRequesterClientId:
                            null,
                    };

                    record.generation =
                        generation;

                    const previousRevision =
                        record.revision;

                    record.revision +=
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'generation_claimed',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    generationId,

                                    generationType:
                                        generation.type,

                                    targetMessageId:
                                        generation.targetMessageId,
                                },

                                generation,
                            },
                        );

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        null,
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Generation started.
                 */
                if (
                    type ===
                    'generation_started'
                ) {
                    const generation =
                        record.generation;

                    if (!generation) {
                        throw new SyncError(
                            'generation_stale',
                            'No active generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        generation.ownerClientId !==
                        clientId
                    ) {
                        throw new SyncError(
                            'generation_not_owner',
                            'Only the generation owner can start the claimed generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    /*
                     * Idempotent state transition.
                     */
                    if (
                        generation.state ===
                        'streaming'
                    ) {
                        const state =
                            publicState(
                                record,
                            );

                        const result = {
                            accepted:
                                true,

                            duplicate:
                                true,

                            state,
                        };

                        rememberOperation(
                            record,
                            opId,
                            result,
                        );

                        return res.json({
                            ok:
                                true,

                            ...result,
                        });
                    }

                    generation.state =
                        'streaming';

                    generation.leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;

                    const previousRevision =
                        record.revision;

                    record.revision +=
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'generation_started',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    generationId:
                                        generation.id,
                                },

                                generation,
                            },
                        );

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        null,
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Generation stream.
                 */
                if (
                    type ===
                    'generation_stream'
                ) {
                    const generation =
                        record.generation;

                    if (!generation) {
                        throw new SyncError(
                            'generation_stale',
                            'No active generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        generation.ownerClientId !==
                        clientId
                    ) {
                        throw new SyncError(
                            'generation_not_owner',
                            'Only generation owner may publish stream state',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        req.body
                            .generationId !==
                        generation.id
                    ) {
                        throw new SyncError(
                            'generation_stale',
                            'Generation ID is no longer active',
                            409,
                        );
                    }

                    if (
                        generation.leaseUntil <=
                        now()
                    ) {
                        abandonGeneration(
                            record,
                            'lease_expired',
                        );

                        throw new SyncError(
                            'generation_expired',
                            'Generation lease expired',
                            409,
                        );
                    }

                    const streamSeq =
                        Number(
                            req.body
                                .streamSeq,
                        );

                    if (
                        !Number.isSafeInteger(
                            streamSeq,
                        )
                    ) {
                        throw new SyncError(
                            'invalid_stream_sequence',
                            'Invalid stream sequence',
                        );
                    }

                    if (
                        streamSeq <=
                        generation.streamSeq
                    ) {
                        const result = {
                            accepted:
                                true,

                            duplicate:
                                true,

                            state:
                                publicState(
                                    record,
                                ),
                        };

                        rememberOperation(
                            record,
                            opId,
                            result,
                        );

                        return res.json({
                            ok:
                                true,

                            ...result,
                        });
                    }

                    if (
                        streamSeq !==
                        generation.streamSeq +
                            1
                    ) {
                        throw new SyncError(
                            'stream_sequence_gap',
                            'Generation stream sequence is not contiguous',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    validateSnapshotShape(
                        req.body.snapshot,
                    );

                    validateNoDuplicateMessageIds(
                        req.body.snapshot,
                    );

                    validateSnapshotLineage(
                        req.body.snapshot,
                        scope,
                    );

                    const previousSnapshot =
                        record.snapshot
                            ? clone(
                                record.snapshot,
                            )
                            : null;

                    record.snapshot =
                        clone(
                            req.body.snapshot,
                        );

                    record.snapshotHash =
                        sha256(
                            record.snapshot,
                        );

                    generation.streamSeq =
                        streamSeq;

                    generation.leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;

                    generation.state =
                        'streaming';

                    const previousRevision =
                        record.revision;

                    record.revision +=
                        1;

                    const patch =
                        makeSnapshotPatch(
                            previousSnapshot,
                            record.snapshot,
                        );

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'generation_stream',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    generationId:
                                        generation.id,

                                    streamSeq,

                                    reason:
                                        req.body
                                            .payload
                                            ?.reason ||
                                        'stream',
                                },

                                generation,
                            },
                        );

                    const state =
                        publicState(
                            record,
                            {
                                includeSnapshot:
                                    false,
                            },
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    /*
                     * Stream state is persisted through the serialized scope
                     * writer, but not forced to disk for every batch.
                     */
                    void persistScope(
                        record,
                        false,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        patch,
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Remote stop request.
                 *
                 * This is a control command rather than a content mutation, so
                 * it intentionally does not fail merely because the chat's
                 * revision advanced during streaming. The exact generation ID
                 * remains the authority.
                 */
                if (
                    type ===
                    'generation_stop_request'
                ) {
                    const generation =
                        record.generation;

                    if (!generation) {
                        const result = {
                            accepted:
                                false,

                            reason:
                                'no_active_generation',

                            state:
                                publicState(
                                    record,
                                ),
                        };

                        rememberOperation(
                            record,
                            opId,
                            result,
                        );

                        return res.json({
                            ok:
                                true,

                            ...result,
                        });
                    }

                    if (
                        String(
                            req.body
                                .generationId ||
                                '',
                        ) !==
                        generation.id
                    ) {
                        throw new SyncError(
                            'generation_stale',
                            'Generation ID is no longer active',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        record.stopRequestIds.has(
                            opId,
                        )
                    ) {
                        const result = {
                            accepted:
                                true,

                            duplicate:
                                true,

                            state:
                                publicState(
                                    record,
                                ),
                        };

                        rememberOperation(
                            record,
                            opId,
                            result,
                        );

                        return res.json({
                            ok:
                                true,

                            ...result,
                        });
                    }

                    record.stopRequestIds.add(
                        opId,
                    );

                    generation.stopRequested =
                        true;

                    generation.stopRequesterClientId =
                        clientId;

                    generation.leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;

                    const previousRevision =
                        record.revision;

                    record.revision +=
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'generation_stop_requested',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    generationId:
                                        generation.id,

                                    requesterClientId:
                                        clientId,
                                },

                                generation,
                            },
                        );

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        false,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        null,
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Generation terminal.
                 */
                if (
                    type ===
                    'generation_terminal'
                ) {
                    const generation =
                        record.generation;

                    if (!generation) {
                        throw new SyncError(
                            'generation_stale',
                            'No active generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        generation.ownerClientId !==
                        clientId
                    ) {
                        throw new SyncError(
                            'generation_not_owner',
                            'Only the generation owner may finish generation',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        req.body
                            .generationId !==
                        generation.id
                    ) {
                        throw new SyncError(
                            'generation_stale',
                            'Generation ID is no longer active',
                            409,
                        );
                    }

                    const status =
                        [
                            'completed',
                            'stopped',
                            'failed',
                            'abandoned',
                        ].includes(
                            req.body.status,
                        )
                            ? req.body.status
                            : null;

                    if (!status) {
                        throw new SyncError(
                            'invalid_generation_status',
                            'Invalid generation terminal status',
                        );
                    }

                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    validateSnapshotShape(
                        req.body.snapshot,
                    );

                    validateNoDuplicateMessageIds(
                        req.body.snapshot,
                    );

                    validateSnapshotLineage(
                        req.body.snapshot,
                        scope,
                    );

                    /*
                     * Terminal state gets a fresh, uncached ST-file check. The
                     * extension is expected to have saved final chat state
                     * through ST before asking us to close the generation.
                     */
                    const actual =
                        await readStChatSnapshot(
                            req,
                            scope,
                            {
                                force:
                                    true,
                            },
                        );

                    const incomingHash =
                        sha256(
                            req.body.snapshot,
                        );

                    if (
                        actual.hash !==
                        incomingHash
                    ) {
                        throw new SyncError(
                            'st_not_persisted',
                            'SillyTavern disk state does not match the terminal synchronization snapshot',
                            409,
                            {
                                expectedHash:
                                    incomingHash,

                                actualHash:
                                    actual.hash,

                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const previousRevision =
                        record.revision;

                    record.snapshot =
                        clone(
                            actual.snapshot,
                        );

                    record.snapshotHash =
                        actual.hash;

                    generation.state =
                        status;

                    generation.leaseUntil =
                        0;

                    const finishedGeneration =
                        clone(
                            generation,
                        );

                    record.revision +=
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'generation_terminal',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    generationId:
                                        generation.id,

                                    status,

                                    generationType:
                                        generation.type,
                                },

                                generation:
                                    finishedGeneration,
                            },
                        );

                    record.generation =
                        null;

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        {
                            kind:
                                'full',

                            snapshot:
                                clone(
                                    record.snapshot,
                                ),
                        },
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Bootstrap.
                 */
                if (
                    type ===
                    'bootstrap'
                ) {
                    if (
                        record.revision !==
                            0 ||
                        record.snapshot
                    ) {
                        throw new SyncError(
                            'stale_revision',
                            'Synchronization scope is already initialized',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    validateSnapshotShape(
                        req.body.snapshot,
                    );

                    validateNoDuplicateMessageIds(
                        req.body.snapshot,
                    );

                    validateSnapshotLineage(
                        req.body.snapshot,
                        scope,
                    );

                    const actual =
                        await readStChatSnapshot(
                            req,
                            scope,
                            {
                                force:
                                    true,
                            },
                        );

                    const incomingHash =
                        sha256(
                            req.body.snapshot,
                        );

                    if (
                        actual.exists &&
                        actual.hash &&
                        actual.hash !==
                            incomingHash
                    ) {
                        throw new SyncError(
                            'st_not_persisted',
                            'Existing SillyTavern chat differs from bootstrap snapshot',
                            409,
                            {
                                expectedHash:
                                    incomingHash,

                                actualHash:
                                    actual.hash,
                            },
                        );
                    }

                    record.snapshot =
                        clone(
                            req.body.snapshot,
                        );

                    record.snapshotHash =
                        incomingHash;

                    record.revision =
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'bootstrap',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    0,

                                payload: {},
                            },
                        );

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        {
                            kind:
                                'full',

                            snapshot:
                                clone(
                                    record.snapshot,
                                ),
                        },
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Reconcile an out-of-band local ST save.
                 */
                if (
                    type ===
                    'reconcile_local'
                ) {
                    if (
                        record.generation
                    ) {
                        throw new SyncError(
                            'generation_lock',
                            'Cannot reconcile while generation is active',
                            409,
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    requireBaseRevision(
                        record,
                        baseRevision,
                    );

                    validateSnapshotShape(
                        req.body.snapshot,
                    );

                    validateNoDuplicateMessageIds(
                        req.body.snapshot,
                    );

                    validateSnapshotLineage(
                        req.body.snapshot,
                        scope,
                    );

                    const actual =
                        await readStChatSnapshot(
                            req,
                            scope,
                            {
                                force:
                                    true,
                            },
                        );

                    const incomingHash =
                        sha256(
                            req.body.snapshot,
                        );

                    if (
                        actual.hash !==
                        incomingHash
                    ) {
                        throw new SyncError(
                            'st_not_persisted',
                            'Current SillyTavern file does not match the reconciliation snapshot',
                            409,
                            {
                                expectedHash:
                                    incomingHash,

                                actualHash:
                                    actual.hash,
                            },
                        );
                    }

                    const previousRevision =
                        record.revision;

                    record.snapshot =
                        clone(
                            actual.snapshot,
                        );

                    record.snapshotHash =
                        actual.hash;

                    record.revision +=
                        1;

                    const event =
                        appendEvent(
                            record,
                            {
                                type:
                                    'state_reconciled',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                baseRevision:
                                    previousRevision,

                                payload: {
                                    strategy:
                                        'current_st_file',
                                },
                            },
                        );

                    const state =
                        publicState(
                            record,
                        );

                    const result = {
                        accepted:
                            true,

                        event,

                        state,
                    };

                    rememberOperation(
                        record,
                        opId,
                        result,
                    );

                    await persistScope(
                        record,
                        true,
                    );

                    broadcastLiveEvent(
                        record,
                        event,
                        {
                            kind:
                                'full',

                            snapshot:
                                clone(
                                    record.snapshot,
                                ),
                        },
                    );

                    return res.json({
                        ok:
                            true,

                        ...result,
                    });
                }


                /*
                 * Ordinary full-state mutation.
                 *
                 * Keep the accepted event types explicit so arbitrary remote
                 * RPC-like commands cannot be smuggled through this endpoint.
                 */
                const allowedTypes =
                    new Set([
                        'message_sent',
                        'message_received',
                        'message_edited',
                        'message_deleted',
                        'message_updated',

                        'message_swiped',
                        'message_swipe_deleted',

                        'message_file_embedded',
                        'file_attachment_deleted',
                        'media_attachment_deleted',

                        'message_reasoning_edited',
                        'message_reasoning_deleted',
                        'stream_reasoning_done',

                        'tool_calls_performed',

                        'chat_loaded',
                        'chat_changed',
                        'chat_created',
                        'chat_deleted',
                        'chat_renamed',

                        'group_chat_created',
                        'group_chat_deleted',
                        'group_updated',

                        'chat_lifecycle',
                    ]);

                if (
                    !allowedTypes.has(
                        type,
                    )
                ) {
                    throw new SyncError(
                        'unknown_event_type',
                        `Unsupported synchronization event type: ${type}`,
                    );
                }

                if (
                    record.generation
                ) {
                    throw new SyncError(
                        'generation_lock',
                        'Chat mutations are locked during active generation',
                        409,
                        {
                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }

                requireBaseRevision(
                    record,
                    baseRevision,
                );

                validateSnapshotShape(
                    req.body.snapshot,
                );

                validateNoDuplicateMessageIds(
                    req.body.snapshot,
                );

                validateSnapshotLineage(
                    req.body.snapshot,
                    scope,
                );

                const incomingHash =
                    sha256(
                        req.body.snapshot,
                    );

                /*
                 * Read the user's actual ST chat to prevent the plugin mirror
                 * from becoming a separate authority for ordinary committed
                 * chat mutations.
                 */
                const actual =
                    await readStChatSnapshot(
                        req,
                        scope,
                        {
                            force:
                                true,
                        },
                    );

                if (
                    !actual.snapshot
                ) {
                    throw new SyncError(
                        'st_not_persisted',
                        'SillyTavern chat file is not currently available',
                        409,
                    );
                }

                if (
                    actual.hash !==
                    incomingHash
                ) {
                    throw new SyncError(
                        'st_not_persisted',
                        'SillyTavern file does not match submitted synchronization state',
                        409,
                        {
                            expectedHash:
                                incomingHash,

                            actualHash:
                                actual.hash,
                        },
                    );
                }

                const previousSnapshot =
                    record.snapshot
                        ? clone(
                            record.snapshot,
                        )
                        : null;

                const canonicalSnapshot =
                    clone(
                        actual.snapshot,
                    );

                record.snapshot =
                    canonicalSnapshot;

                record.snapshotHash =
                    actual.hash;

                const previousRevision =
                    record.revision;

                record.revision +=
                    1;

                const patch =
                    makeSnapshotPatch(
                        previousSnapshot,
                        record.snapshot,
                    );

                const event =
                    appendEvent(
                        record,
                        {
                            type,

                            opId,

                            sourceClientId:
                                clientId,

                            sourceDeviceId:
                                deviceId,

                            baseRevision:
                                previousRevision,

                            payload:
                                clone(
                                    payload,
                                ),

                            generation:
                                null,
                        },
                    );

                const state =
                    publicState(
                        record,
                        {
                            includeSnapshot:
                                false,
                        },
                    );

                const result = {
                    accepted:
                        true,

                    event,

                    state,
                };

                rememberOperation(
                    record,
                    opId,
                    result,
                );

                await persistScope(
                    record,
                    true,
                );

                broadcastLiveEvent(
                    record,
                    event,
                    patch,
                );

                return res.json({
                    ok:
                        true,

                    ...result,
                });
            } catch (error) {
                return sendError(
                    res,
                    error,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* WATCHDOG                                                               */
    /* ---------------------------------------------------------------------- */

    watchdogTimer =
        setInterval(
            cleanRuntimeState,
            5_000,
        );

    if (
        typeof watchdogTimer.unref ===
        'function'
    ) {
        watchdogTimer.unref();
    }

    initialized =
        true;

    console.log(
        `[${PLUGIN_ID}] loaded: protocol=${PROTOCOL_VERSION}, epoch=${runtimeEpoch}`,
    );
}


/* -------------------------------------------------------------------------- */
/* Shutdown                                                                  */
/* -------------------------------------------------------------------------- */

async function exit() {
    shuttingDown =
        true;

    if (
        watchdogTimer
    ) {
        clearInterval(
            watchdogTimer,
        );

        watchdogTimer =
            null;
    }

    /*
     * Gracefully tell connected clients to reconnect.
     */
    for (
        const [
            ,
            clients,
        ] of sseClients
    ) {
        for (
            const responseSet of
                clients.values()
        ) {
            for (
                const res of
                    responseSet
            ) {
                try {
                    sendSse(
                        res,
                        'shutdown',
                        {
                            reason:
                                'server_shutdown',

                            epoch:
                                runtimeEpoch,
                        },
                    );

                    res.end();
                } catch {
                    // ignored
                }
            }
        }
    }

    sseClients.clear();

    /*
     * Flush every scope through its own serialized persistence chain.
     */
    await Promise.allSettled(
        [
            ...scopes.values(),
        ].map(
            record =>
                persistScope(
                    record,
                    true,
                ),
        ),
    );

    initialized =
        false;

    console.log(
        `[${PLUGIN_ID}] unloaded`,
    );
}


/* -------------------------------------------------------------------------- */
/* Exports                                                                    */
/* -------------------------------------------------------------------------- */

module.exports = {
    init,
    exit,
    info,
};