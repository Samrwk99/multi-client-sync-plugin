'use strict';

/**
 * Multi Client Sync - SillyTavern server plugin.
 *
 * Responsibilities:
 * - Authenticated per-user/per-chat scoping
 * - Membership/heartbeat leases
 * - Authoritative revisions
 * - Monotonic event sequence numbers
 * - Idempotent operation IDs
 * - SSE live delivery
 * - SSE replay / resync signalling
 * - Server epoch fencing across restarts
 * - Generation ownership / leases / stop requests
 * - Atomic-ish JSON persistence of sync state
 * - Bounded retained event history
 *
 * The plugin does not write ST chat files directly.
 * The client applies authoritative snapshots through ST's own save path.
 */

const fs = require('fs/promises');
const path = require('path');
const crypto = require('crypto');


/* -------------------------------------------------------------------------- */
/* Configuration                                                               */
/* -------------------------------------------------------------------------- */

const PLUGIN_ID =
    'multi-client-sync';

const PROTOCOL_VERSION =
    2;

const STATE_SCHEMA_VERSION =
    2;

const MAX_EVENT_BYTES =
    8 * 1024 * 1024;

const MAX_EVENTS =
    2000;

const MAX_SEEN_OPS =
    5000;

const MAX_MEMBERS_PER_SCOPE =
    32;

const MEMBER_TTL_MS =
    45_000;

const GENERATION_LEASE_MS =
    20_000;

const GENERATION_SCAN_MS =
    5_000;

const PERSIST_DEBOUNCE_MS =
    750;

const KEEPALIVE_MS =
    15_000;


/* -------------------------------------------------------------------------- */
/* Runtime state                                                               */
/* -------------------------------------------------------------------------- */

const runtimeEpoch =
    crypto.randomUUID();

const scopes =
    new Map();

const sseByScope =
    new Map();

const persistTimers =
    new Map();

const persistDir =
    path.join(
        __dirname,
        '.data',
        'scopes',
    );

let scanTimer =
    null;

const info = {
    id:
        PLUGIN_ID,

    name:
        'Multi Client Sync',

    description:
        'Authoritative multi-client SillyTavern chat synchronization with SSE, replay, revisions, and generation leases.',
};


/* -------------------------------------------------------------------------- */
/* Utilities                                                                   */
/* -------------------------------------------------------------------------- */

function now() {
    return Date.now();
}

function clone(value) {
    if (value === undefined) {
        return undefined;
    }

    return structuredClone(value);
}

function jsonBytes(value) {
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
        return `[${value.map(stableStringify).join(',')}]`;
    }

    return `{${Object.keys(value).sort().map(
        key =>
            `${JSON.stringify(key)}:${stableStringify(value[key])}`,
    ).join(',')}}`;
}

function safeString(
    value,
    max = 512,
) {
    if (
        typeof value !== 'string'
    ) {
        return '';
    }

    return value.length > max
        ? value.slice(0, max)
        : value;
}

function validateId(
    value,
    field,
    max = 256,
) {
    if (
        typeof value !== 'string' ||
        value.length < 1 ||
        value.length > max
    ) {
        const error =
            new Error(
                `Invalid ${field}`,
            );

        error.code =
            'invalid_request';

        throw error;
    }

    return value;
}


/* -------------------------------------------------------------------------- */
/* Scope/auth                                                                  */
/* -------------------------------------------------------------------------- */

function normalizeScope(raw) {
    if (
        !raw ||
        typeof raw !== 'object'
    ) {
        const error =
            new Error(
                'Missing scope',
            );

        error.code =
            'invalid_scope';

        throw error;
    }

    const scopeType =
        raw.scopeType === 'group'
            ? 'group'
            : raw.scopeType === 'character'
                ? 'character'
                : null;

    if (!scopeType) {
        const error =
            new Error(
                'Invalid scopeType',
            );

        error.code =
            'invalid_scope';

        throw error;
    }

    const chatId =
        validateId(
            raw.chatId,
            'chatId',
            1024,
        );

    const characterId =
        raw.characterId === null ||
        raw.characterId === undefined
            ? null
            : safeString(
                String(
                    raw.characterId,
                ),
                128,
            );

    const groupId =
        raw.groupId === null ||
        raw.groupId === undefined
            ? null
            : safeString(
                String(
                    raw.groupId,
                ),
                256,
            );

    if (
        scopeType === 'character' &&
        !characterId
    ) {
        const error =
            new Error(
                'characterId required for character scope',
            );

        error.code =
            'invalid_scope';

        throw error;
    }

    if (
        scopeType === 'group' &&
        !groupId
    ) {
        const error =
            new Error(
                'groupId required for group scope',
            );

        error.code =
            'invalid_scope';

        throw error;
    }

    return {
        scopeType,
        chatId,

        characterId:
            scopeType === 'character'
                ? characterId
                : null,

        groupId:
            scopeType === 'group'
                ? groupId
                : null,
    };
}

function userIdFromRequest(
    req,
) {
    /*
     * The browser never supplies the authoritative user identity.
     *
     * ST's authenticated middleware supplies req.user. We derive the sync
     * namespace from that authenticated identity.
     */
    const handle =
        req?.user?.profile?.handle ??
        req?.user?.handle ??
        req?.user?.name;

    return (
        safeString(
            handle
                ? String(handle)
                : 'default',
            256,
        ) ||
        'default'
    );
}

function scopeKey(
    userId,
    scope,
) {
    return JSON.stringify({
        userId,
        ...scope,
    });
}

function scopeHash(key) {
    return crypto
        .createHash('sha256')
        .update(key)
        .digest('hex');
}

function eventId(seq) {
    return `${runtimeEpoch}:${seq}`;
}

function parseEventCursor(
    value,
) {
    if (!value) {
        return null;
    }

    const text =
        String(value);

    const index =
        text.lastIndexOf(':');

    if (index <= 0) {
        return null;
    }

    const epoch =
        text.slice(
            0,
            index,
        );

    const seq =
        Number(
            text.slice(
                index + 1,
            ),
        );

    if (
        !Number.isSafeInteger(seq) ||
        seq < 0
    ) {
        return null;
    }

    return {
        epoch,
        seq,
    };
}


/* -------------------------------------------------------------------------- */
/* HTTP helpers                                                                */
/* -------------------------------------------------------------------------- */

function httpError(
    res,
    status,
    code,
    message,
    extra = {},
) {
    res.status(status).json({
        ok: false,
        code,
        message,
        ...extra,
    });
}

function ok(
    res,
    payload = {},
) {
    res.setHeader(
        'Cache-Control',
        'no-store',
    );

    res.json({
        ok: true,
        ...payload,
    });
}

function noStore(res) {
    res.setHeader(
        'Cache-Control',
        'no-store',
    );
}


/* -------------------------------------------------------------------------- */
/* Snapshot validation                                                         */
/* -------------------------------------------------------------------------- */

function validateSnapshot(
    snapshot,
) {
    if (
        !snapshot ||
        typeof snapshot !== 'object'
    ) {
        const error =
            new Error(
                'Missing snapshot',
            );

        error.code =
            'invalid_snapshot';

        throw error;
    }

    if (
        !Array.isArray(
            snapshot.chat,
        )
    ) {
        const error =
            new Error(
                'snapshot.chat must be an array',
            );

        error.code =
            'invalid_snapshot';

        throw error;
    }

    if (
        snapshot.chat.length >
        100_000
    ) {
        const error =
            new Error(
                'Chat is too large',
            );

        error.code =
            'snapshot_too_large';

        throw error;
    }

    if (
        snapshot.chatMetadata !==
            undefined &&
        (
            snapshot.chatMetadata === null ||
            typeof snapshot.chatMetadata !==
                'object' ||
            Array.isArray(
                snapshot.chatMetadata,
            )
        )
    ) {
        const error =
            new Error(
                'snapshot.chatMetadata must be an object',
            );

        error.code =
            'invalid_snapshot';

        throw error;
    }

    const bytes =
        jsonBytes(
            snapshot,
        );

    if (
        bytes >
        MAX_EVENT_BYTES
    ) {
        const error =
            new Error(
                `Snapshot exceeds ${MAX_EVENT_BYTES} bytes`,
            );

        error.code =
            'snapshot_too_large';

        throw error;
    }

    return true;
}


/* -------------------------------------------------------------------------- */
/* Scope records                                                               */
/* -------------------------------------------------------------------------- */

function ensureScopeRecord(
    key,
    userId,
    scope,
) {
    let record =
        scopes.get(key);

    if (!record) {
        record = {
            schemaVersion:
                STATE_SCHEMA_VERSION,

            key,

            userId,

            scope:
                clone(scope),

            serverEpoch:
                runtimeEpoch,

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

            members:
                new Map(),

            generation:
                null,

            stopRequestIds:
                new Set(),

            persistVersion:
                0,
        };

        scopes.set(
            key,
            record,
        );
    }

    return record;
}

function publicState(
    record,
) {
    return {
        protocolVersion:
            PROTOCOL_VERSION,

        schemaVersion:
            STATE_SCHEMA_VERSION,

        epoch:
            runtimeEpoch,

        revision:
            record.revision,

        seq:
            record.seq,

        snapshot:
            record.snapshot
                ? clone(
                    record.snapshot,
                )
                : null,

        snapshotHash:
            record.snapshotHash,

        generation:
            record.generation
                ? clone(
                    record.generation,
                )
                : null,

        memberCount:
            record.members.size,
    };
}

function compactGeneration(
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

        state:
            generation.state,

        leaseUntil:
            generation.leaseUntil,

        startedAt:
            generation.startedAt,

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


/* -------------------------------------------------------------------------- */
/* Events                                                                      */
/* -------------------------------------------------------------------------- */

function makeEvent(
    record,
    {
        type,
        opId = null,
        sourceClientId = null,
        sourceDeviceId = null,
        payload = {},
        includeSnapshot = false,
        generation = null,
    },
) {
    record.seq += 1;

    const event = {
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
                ? compactGeneration(
                    generation,
                )
                : null,
    };

    if (
        includeSnapshot &&
        record.snapshot
    ) {
        event.snapshot =
            clone(
                record.snapshot,
            );
    }

    /*
     * Streaming snapshots are delivered live but are deliberately not retained
     * as full copies in the replay history. A replay through a stream event
     * causes /state recovery instead.
     */
    const storedEvent =
        event.type ===
            'generation_stream'
            ? {
                ...event,
                snapshot:
                    undefined,
            }
            : event;

    if (
        storedEvent.snapshot ===
            undefined
    ) {
        delete storedEvent.snapshot;
    }

    record.events.push(
        storedEvent,
    );

    if (
        record.events.length >
        MAX_EVENTS
    ) {
        record.events.splice(
            0,
            record.events.length -
                MAX_EVENTS,
        );
    }

    return event;
}

function rememberOp(
    record,
    opId,
) {
    if (!opId) {
        return;
    }

    record.seenOps.push(
        opId,
    );

    if (
        record.seenOps.length >
        MAX_SEEN_OPS
    ) {
        record.seenOps.splice(
            0,
            record.seenOps.length -
                MAX_SEEN_OPS,
        );
    }
}

function hasSeenOp(
    record,
    opId,
) {
    return Boolean(
        opId &&
        record.seenOps.includes(
            opId,
        ),
    );
}


/* -------------------------------------------------------------------------- */
/* SSE                                                                          */
/* -------------------------------------------------------------------------- */

function sendSse(
    res,
    event,
    data,
    id = null,
) {
    if (res.writableEnded) {
        return;
    }

    if (id !== null) {
        res.write(
            `id: ${id}\n`,
        );
    }

    if (event) {
        res.write(
            `event: ${event}\n`,
        );
    }

    const text =
        JSON.stringify(
            data,
        );

    for (
        const line of text.split('\n')
    ) {
        res.write(
            `data: ${line}\n`,
        );
    }

    res.write('\n');
}

function broadcast(
    record,
    event,
) {
    const clients =
        sseByScope.get(
            record.key,
        );

    if (
        !clients ||
        clients.size === 0
    ) {
        return;
    }

    const data = {
        ...clone(event),

        state: {
            epoch:
                runtimeEpoch,

            revision:
                record.revision,

            seq:
                record.seq,

            snapshotHash:
                record.snapshotHash,

            generation:
                record.generation
                    ? compactGeneration(
                        record.generation,
                    )
                    : null,
        },
    };

    /*
     * Live delivery always carries the latest authoritative snapshot.
     */
    data.snapshot =
        record.snapshot
            ? clone(
                record.snapshot,
            )
            : null;

    for (
        const res of clients
    ) {
        try {
            sendSse(
                res,
                'sync',
                data,
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


/* -------------------------------------------------------------------------- */
/* Persistence                                                                  */
/* -------------------------------------------------------------------------- */

async function atomicWrite(
    file,
    data,
) {
    const temp =
        `${file}.${process.pid}.${Date.now()}.tmp`;

    await fs.writeFile(
        temp,
        data,
        'utf8',
    );

    await fs.rename(
        temp,
        file,
    );
}

function persistentView(
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

        generation:
            record.generation
                ? compactGeneration(
                    record.generation,
                )
                : null,

        persistedAt:
            now(),
    };
}

async function persistScope(
    record,
) {
    try {
        await fs.mkdir(
            persistDir,
            {
                recursive:
                    true,
            },
        );

        const file =
            path.join(
                persistDir,
                `${scopeHash(record.key)}.json`,
            );

        await atomicWrite(
            file,
            JSON.stringify(
                persistentView(
                    record,
                ),
            ),
        );

        record.persistVersion += 1;
    } catch (error) {
        console.error(
            `[${PLUGIN_ID}] persistence failed for scope`,
            record.key,
            error,
        );
    }
}

function schedulePersist(
    record,
    immediate = false,
) {
    if (immediate) {
        const current =
            persistTimers.get(
                record.key,
            );

        if (current) {
            clearTimeout(
                current,
            );
        }

        persistTimers.delete(
            record.key,
        );

        return persistScope(
            record,
        );
    }

    if (
        persistTimers.has(
            record.key,
        )
    ) {
        return;
    }

    const timer =
        setTimeout(
            () => {
                persistTimers.delete(
                    record.key,
                );

                void persistScope(
                    record,
                );
            },
            PERSIST_DEBOUNCE_MS,
        );

    persistTimers.set(
        record.key,
        timer,
    );
}

async function loadPersisted() {
    try {
        await fs.mkdir(
            persistDir,
            {
                recursive:
                    true,
            },
        );

        const files =
            await fs.readdir(
                persistDir,
            );

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

            const file =
                path.join(
                    persistDir,
                    fileName,
                );

            try {
                const parsed =
                    JSON.parse(
                        await fs.readFile(
                            file,
                            'utf8',
                        ),
                    );

                if (
                    parsed?.schemaVersion !==
                        STATE_SCHEMA_VERSION ||
                    !parsed?.key ||
                    !parsed?.scope ||
                    !parsed?.userId
                ) {
                    continue;
                }

                const record =
                    ensureScopeRecord(
                        parsed.key,
                        parsed.userId,
                        parsed.scope,
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
                        : null;

                record.events =
                    Array.isArray(
                        parsed.events,
                    )
                        ? parsed.events
                            .slice(
                                -MAX_EVENTS,
                            )
                            .map(clone)
                        : [];

                record.seenOps =
                    Array.isArray(
                        parsed.seenOps,
                    )
                        ? parsed.seenOps
                            .slice(
                                -MAX_SEEN_OPS,
                            )
                        : [];

                record.generation =
                    parsed.generation
                        ? clone(
                            parsed.generation,
                        )
                        : null;

                /*
                 * Never restore generation ownership from a previous runtime.
                 * Server epoch changed, therefore prior ownership is fenced out.
                 */
                if (
                    record.generation
                ) {
                    record.generation.state =
                        'abandoned';

                    record.generation.leaseUntil =
                        0;
                }

                record.serverEpoch =
                    runtimeEpoch;
            } catch (error) {
                console.warn(
                    `[${PLUGIN_ID}] ignoring unreadable persisted scope ${fileName}`,
                    error?.message ||
                        error,
                );
            }
        }
    } catch (error) {
        console.warn(
            `[${PLUGIN_ID}] persistent state unavailable; running memory-only`,
            error?.message ||
                error,
        );
    }
}


/* -------------------------------------------------------------------------- */
/* Membership                                                                   */
/* -------------------------------------------------------------------------- */

function requireMember(
    record,
    clientId,
) {
    const member =
        record.members.get(
            clientId,
        );

    if (!member) {
        const error =
            new Error(
                'Client is not a member of this sync scope',
            );

        error.code =
            'not_member';

        throw error;
    }

    if (
        member.expiresAt <=
        now()
    ) {
        record.members.delete(
            clientId,
        );

        const error =
            new Error(
                'Client membership expired',
            );

        error.code =
            'membership_expired';

        throw error;
    }

    member.lastSeen =
        now();

    member.expiresAt =
        now() +
        MEMBER_TTL_MS;

    return member;
}


/* -------------------------------------------------------------------------- */
/* Generation expiry                                                            */
/* -------------------------------------------------------------------------- */

function expireGeneration(
    record,
) {
    const generation =
        record.generation;

    if (!generation) {
        return null;
    }

    if (
        generation.leaseUntil >
        now()
    ) {
        return null;
    }

    generation.state =
        'abandoned';

    /*
     * Increment revision before making the event so the event advertises the
     * authoritative new revision.
     */
    record.revision += 1;

    const event =
        makeEvent(
            record,
            {
                type:
                    'generation_abandoned',

                sourceClientId:
                    generation.ownerClientId,

                sourceDeviceId:
                    generation.ownerDeviceId,

                payload: {
                    reason:
                        'lease_expired',

                    generationId:
                        generation.id,
                },

                generation:
                    generation,
            },
        );

    event.revision =
        record.revision;

    record.generation =
        null;

    broadcast(
        record,
        event,
    );

    void schedulePersist(
        record,
        true,
    );

    return event;
}


/* -------------------------------------------------------------------------- */
/* Request parsing                                                              */
/* -------------------------------------------------------------------------- */

function scopeFromRequest(
    req,
) {
    let raw =
        req.body?.scope;

    if (
        !raw &&
        req.query?.scope
    ) {
        try {
            raw =
                JSON.parse(
                    String(
                        req.query.scope,
                    ),
                );
        } catch {
            raw =
                null;
        }
    }

    return normalizeScope(
        raw,
    );
}

function clientEnvelope(
    req,
) {
    const body =
        req.body || {};

    const clientId =
        validateId(
            body.clientId,
            'clientId',
            256,
        );

    const deviceId =
        validateId(
            body.deviceId,
            'deviceId',
            256,
        );

    const protocolVersion =
        Number(
            body.protocolVersion,
        );

    if (
        protocolVersion !==
        PROTOCOL_VERSION
    ) {
        const error =
            new Error(
                `Protocol version ${protocolVersion} is not supported; expected ${PROTOCOL_VERSION}`,
            );

        error.code =
            'protocol_mismatch';

        throw error;
    }

    return {
        clientId,
        deviceId,
        body,
    };
}

function checkBaseRevision(
    record,
    body,
) {
    const baseRevision =
        Number(
            body.baseRevision,
        );

    if (
        !Number.isSafeInteger(
            baseRevision,
        ) ||
        baseRevision < 0
    ) {
        const error =
            new Error(
                'Invalid baseRevision',
            );

        error.code =
            'invalid_revision';

        throw error;
    }

    if (
        baseRevision !==
        record.revision
    ) {
        const error =
            new Error(
                'Client revision is stale',
            );

        error.code =
            'stale_revision';

        error.currentState =
            publicState(
                record,
            );

        throw error;
    }
}


/* -------------------------------------------------------------------------- */
/* Plugin init                                                                  */
/* -------------------------------------------------------------------------- */

async function init(
    router,
) {
    /*
     * Route-level body size guard.
     *
     * ST generally parses API bodies globally, so the actual snapshot/event
     * is also size-validated below.
     */
    router.use(
        (
            req,
            res,
            next,
        ) => {
            const length =
                Number(
                    req.headers[
                        'content-length'
                    ],
                );

            if (
                Number.isFinite(length) &&
                length >
                    MAX_EVENT_BYTES
            ) {
                return httpError(
                    res,
                    413,
                    'payload_too_large',
                    'Request body exceeds sync limit',
                );
            }

            noStore(res);

            return next();
        },
    );

    await loadPersisted();


    /* ---------------------------------------------------------------------- */
    /* Health                                                                  */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/health',
        async (
            req,
            res,
        ) => {
            const members =
                [...scopes.values()]
                    .reduce(
                        (
                            sum,
                            record,
                        ) =>
                            sum +
                            record.members.size,
                        0,
                    );

            const activeGenerations =
                [...scopes.values()]
                    .filter(
                        record =>
                            record.generation &&
                            record.generation.leaseUntil >
                                now(),
                    )
                    .length;

            return ok(
                res,
                {
                    plugin:
                        PLUGIN_ID,

                    protocolVersion:
                        PROTOCOL_VERSION,

                    epoch:
                        runtimeEpoch,

                    scopes:
                        scopes.size,

                    members,

                    activeGenerations,
                },
            );
        },
    );


    /* ---------------------------------------------------------------------- */
    /* Join                                                                    */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/join',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const {
                    clientId,
                    deviceId,
                } =
                    clientEnvelope(
                        req,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                const record =
                    ensureScopeRecord(
                        key,
                        userId,
                        scope,
                    );

                expireGeneration(
                    record,
                );

                const existing =
                    record.members.get(
                        clientId,
                    );

                if (
                    !existing &&
                    record.members.size >=
                        MAX_MEMBERS_PER_SCOPE
                ) {
                    return httpError(
                        res,
                        429,
                        'scope_client_limit',
                        'Too many clients in this sync scope',
                    );
                }

                record.members.set(
                    clientId,
                    {
                        clientId,
                        deviceId,

                        joinedAt:
                            existing?.joinedAt ??
                            now(),

                        lastSeen:
                            now(),

                        expiresAt:
                            now() +
                            MEMBER_TTL_MS,
                    },
                );

                schedulePersist(
                    record,
                );

                return ok(
                    res,
                    {
                        scope:
                            clone(
                                scope,
                            ),

                        state:
                            publicState(
                                record,
                            ),

                        member: {
                            clientId,
                            deviceId,
                        },
                    },
                );
            } catch (error) {
                return httpError(
                    res,
                    error.code ===
                        'protocol_mismatch'
                        ? 426
                        : 400,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* Leave                                                                   */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/leave',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const {
                    clientId,
                } =
                    clientEnvelope(
                        req,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                const record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    return ok(
                        res,
                        {
                            left:
                                false,
                        },
                    );
                }

                record.members.delete(
                    clientId,
                );

                if (
                    record.generation?.ownerClientId ===
                    clientId
                ) {
                    record.generation = {
                        ...record.generation,

                        state:
                            'abandoned',

                        leaseUntil:
                            0,
                    };

                    const oldGeneration =
                        record.generation;

                    record.revision += 1;

                    const event =
                        makeEvent(
                            record,
                            {
                                type:
                                    'generation_abandoned',

                                sourceClientId:
                                    clientId,

                                payload: {
                                    reason:
                                        'owner_left',

                                    generationId:
                                        oldGeneration.id,
                                },

                                generation:
                                    oldGeneration,
                            },
                        );

                    event.revision =
                        record.revision;

                    record.generation =
                        null;

                    broadcast(
                        record,
                        event,
                    );
                }

                await schedulePersist(
                    record,
                    true,
                );

                return ok(
                    res,
                    {
                        left:
                            true,
                    },
                );
            } catch (error) {
                return httpError(
                    res,
                    400,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* Heartbeat                                                               */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/heartbeat',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const {
                    clientId,
                    deviceId,
                } =
                    clientEnvelope(
                        req,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                const record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    return httpError(
                        res,
                        404,
                        'scope_not_found',
                        'Sync scope does not exist yet',
                    );
                }

                const member =
                    requireMember(
                        record,
                        clientId,
                    );

                if (
                    member.deviceId !==
                    deviceId
                ) {
                    return httpError(
                        res,
                        409,
                        'device_mismatch',
                        'Client identity changed for this membership',
                    );
                }

                expireGeneration(
                    record,
                );

                if (
                    record.generation &&
                    record.generation.ownerClientId ===
                        clientId
                ) {
                    const generationId =
                        String(
                            req.body?.generationId ||
                                '',
                        );

                    if (
                        generationId ===
                        record.generation.id
                    ) {
                        record.generation.leaseUntil =
                            now() +
                            GENERATION_LEASE_MS;
                    }
                }

                return ok(
                    res,
                    {
                        serverTime:
                            now(),

                        state:
                            publicState(
                                record,
                            ),
                    },
                );
            } catch (error) {
                return httpError(
                    res,
                    error.code ===
                        'not_member' ||
                    error.code ===
                        'membership_expired'
                        ? 403
                        : 400,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* SSE                                                                     */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/events',
        async (
            req,
            res,
        ) => {
            let record;
            let keepaliveTimer;

            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    scopeFromRequest(
                        req,
                    );

                const clientId =
                    validateId(
                        req.query.clientId,
                        'clientId',
                        256,
                    );

                const deviceId =
                    validateId(
                        req.query.deviceId,
                        'deviceId',
                        256,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    return httpError(
                        res,
                        404,
                        'scope_not_found',
                        'Join the scope before opening SSE',
                    );
                }

                const member =
                    requireMember(
                        record,
                        clientId,
                    );

                if (
                    member.deviceId !==
                    deviceId
                ) {
                    return httpError(
                        res,
                        409,
                        'device_mismatch',
                        'Client identity changed for this membership',
                    );
                }

                expireGeneration(
                    record,
                );

                const cursor =
                    parseEventCursor(
                        req.get(
                            'Last-Event-ID',
                        ) ||
                        req.query.since ||
                        '',
                    );

                res.status(200);

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

                let clients =
                    sseByScope.get(
                        key,
                    );

                if (!clients) {
                    clients =
                        new Set();

                    sseByScope.set(
                        key,
                        clients,
                    );
                }

                clients.add(
                    res,
                );

                sendSse(
                    res,
                    'hello',
                    {
                        protocolVersion:
                            PROTOCOL_VERSION,

                        epoch:
                            runtimeEpoch,

                        revision:
                            record.revision,

                        seq:
                            record.seq,

                        snapshotHash:
                            record.snapshotHash,

                        generation:
                            record.generation
                                ? compactGeneration(
                                    record.generation,
                                )
                                : null,
                    },
                );

                if (cursor) {
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

                                revision:
                                    record.revision,

                                seq:
                                    record.seq,
                            },
                        );
                    } else {
                        const oldest =
                            record.events.length
                                ? record.events[0].seq
                                : record.seq + 1;

                        if (
                            cursor.seq <
                            oldest - 1
                        ) {
                            sendSse(
                                res,
                                'resync_required',
                                {
                                    reason:
                                        'replay_window_exceeded',

                                    epoch:
                                        runtimeEpoch,

                                    revision:
                                        record.revision,

                                    seq:
                                        record.seq,
                                },
                            );
                        } else {
                            for (
                                const event of
                                    record.events
                            ) {
                                if (
                                    event.epoch !==
                                    runtimeEpoch
                                ) {
                                    continue;
                                }

                                if (
                                    event.seq <=
                                    cursor.seq
                                ) {
                                    continue;
                                }

                                /*
                                 * Stream events cannot reconstruct an exact
                                 * stream state from replay alone. Pull /state.
                                 */
                                if (
                                    event.type ===
                                    'generation_stream'
                                ) {
                                    sendSse(
                                        res,
                                        'resync_required',
                                        {
                                            reason:
                                                'stream_replay_requires_state',

                                            epoch:
                                                runtimeEpoch,

                                            revision:
                                                record.revision,

                                            seq:
                                                record.seq,
                                        },
                                    );

                                    break;
                                }

                                sendSse(
                                    res,
                                    'sync',
                                    {
                                        ...clone(
                                            event,
                                        ),

                                        state: {
                                            epoch:
                                                runtimeEpoch,

                                            revision:
                                                record.revision,

                                            seq:
                                                record.seq,

                                            snapshotHash:
                                                record.snapshotHash,

                                            generation:
                                                record.generation
                                                    ? compactGeneration(
                                                        record.generation,
                                                    )
                                                    : null,
                                        },

                                        snapshot:
                                            event.snapshot ??
                                            (
                                                record.snapshot
                                                    ? clone(
                                                        record.snapshot,
                                                    )
                                                    : null
                                            ),
                                    },
                                    event.id,
                                );
                            }
                        }
                    }
                }

                keepaliveTimer =
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

                                member.lastSeen =
                                    now();

                                member.expiresAt =
                                    now() +
                                    MEMBER_TTL_MS;

                                if (
                                    record.generation?.ownerClientId ===
                                    clientId
                                ) {
                                    record.generation.leaseUntil =
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
                        KEEPALIVE_MS,
                    );

                const cleanup =
                    () => {
                        if (
                            keepaliveTimer
                        ) {
                            clearInterval(
                                keepaliveTimer,
                            );
                        }

                        const set =
                            sseByScope.get(
                                key,
                            );

                        if (set) {
                            set.delete(
                                res,
                            );

                            if (
                                set.size ===
                                0
                            ) {
                                sseByScope.delete(
                                    key,
                                );
                            }
                        }
                    };

                req.on(
                    'close',
                    cleanup,
                );

                res.on(
                    'close',
                    cleanup,
                );
            } catch (error) {
                return httpError(
                    res,
                    error.code ===
                        'not_member' ||
                    error.code ===
                        'membership_expired'
                        ? 403
                        : 400,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* State                                                                    */
    /* ---------------------------------------------------------------------- */

    router.get(
        '/state',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    scopeFromRequest(
                        req,
                    );

                const clientId =
                    validateId(
                        req.query.clientId,
                        'clientId',
                        256,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                const record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    return httpError(
                        res,
                        404,
                        'scope_not_found',
                        'Sync scope does not exist yet',
                    );
                }

                requireMember(
                    record,
                    clientId,
                );

                expireGeneration(
                    record,
                );

                return ok(
                    res,
                    {
                        scope:
                            clone(scope),

                        state:
                            publicState(
                                record,
                            ),
                    },
                );
            } catch (error) {
                return httpError(
                    res,
                    error.code ===
                        'not_member' ||
                    error.code ===
                        'membership_expired'
                        ? 403
                        : 400,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* Event                                                                     */
    /* ---------------------------------------------------------------------- */

    router.post(
        '/event',
        async (
            req,
            res,
        ) => {
            try {
                const userId =
                    userIdFromRequest(
                        req,
                    );

                const scope =
                    normalizeScope(
                        req.body?.scope,
                    );

                const {
                    clientId,
                    deviceId,
                    body,
                } =
                    clientEnvelope(
                        req,
                    );

                const key =
                    scopeKey(
                        userId,
                        scope,
                    );

                const record =
                    scopes.get(
                        key,
                    );

                if (!record) {
                    return httpError(
                        res,
                        404,
                        'scope_not_found',
                        'Join the sync scope first',
                    );
                }

                const member =
                    requireMember(
                        record,
                        clientId,
                    );

                if (
                    member.deviceId !==
                    deviceId
                ) {
                    return httpError(
                        res,
                        409,
                        'device_mismatch',
                        'Client identity changed for this membership',
                    );
                }

                expireGeneration(
                    record,
                );

                const opId =
                    validateId(
                        body.opId,
                        'opId',
                        256,
                    );

                const type =
                    validateId(
                        body.type,
                        'type',
                        128,
                    );

                const bytes =
                    jsonBytes(
                        body,
                    );

                if (
                    bytes >
                    MAX_EVENT_BYTES
                ) {
                    return httpError(
                        res,
                        413,
                        'payload_too_large',
                        'Event exceeds sync limit',
                    );
                }

                /*
                 * Idempotency.
                 */
                if (
                    hasSeenOp(
                        record,
                        opId,
                    )
                ) {
                    return ok(
                        res,
                        {
                            duplicate:
                                true,

                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }


                /* ---------------------------------------------------------- */
                /* Generation claim                                            */
                /* ---------------------------------------------------------- */

                if (
                    type ===
                    'generation_claim'
                ) {
                    checkBaseRevision(
                        record,
                        body,
                    );

                    if (
                        record.generation
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_owned',
                            'Another client already owns generation',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const generationId =
                        validateId(
                            body.generationId,
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

                        state:
                            'running',

                        leaseUntil:
                            now() +
                            GENERATION_LEASE_MS,

                        startedAt:
                            now(),

                        streamSeq:
                            0,

                        stopRequested:
                            false,

                        stopRequesterClientId:
                            null,
                    };

                    record.generation =
                        generation;

                    record.revision += 1;

                    rememberOp(
                        record,
                        opId,
                    );

                    const event =
                        makeEvent(
                            record,
                            {
                                type:
                                    'generation_claimed',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                payload: {
                                    generationId,
                                },

                                generation,
                            },
                        );

                    event.revision =
                        record.revision;

                    broadcast(
                        record,
                        event,
                    );

                    await schedulePersist(
                        record,
                        true,
                    );

                    return ok(
                        res,
                        {
                            accepted:
                                true,

                            event,

                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }


                /* ---------------------------------------------------------- */
                /* Generation stop request                                     */
                /* ---------------------------------------------------------- */

                if (
                    type ===
                    'generation_stop_request'
                ) {
                    checkBaseRevision(
                        record,
                        body,
                    );

                    if (
                        !record.generation
                    ) {
                        return ok(
                            res,
                            {
                                accepted:
                                    false,

                                reason:
                                    'no_active_generation',

                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const generationId =
                        validateId(
                            body.generationId,
                            'generationId',
                            256,
                        );

                    if (
                        generationId !==
                        record.generation.id
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_stale',
                            'Generation ID is no longer active',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    record.stopRequestIds.add(
                        opId,
                    );

                    if (
                        record.stopRequestIds.size >
                        MAX_SEEN_OPS
                    ) {
                        record.stopRequestIds =
                            new Set(
                                [
                                    ...record.stopRequestIds,
                                ].slice(
                                    -MAX_SEEN_OPS,
                                ),
                            );
                    }

                    record.generation.stopRequested =
                        true;

                    record.generation.stopRequesterClientId =
                        clientId;

                    record.generation.leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;

                    record.revision += 1;

                    rememberOp(
                        record,
                        opId,
                    );

                    const event =
                        makeEvent(
                            record,
                            {
                                type:
                                    'generation_stop_requested',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                payload: {
                                    generationId,

                                    requesterClientId:
                                        clientId,
                                },

                                generation:
                                    record.generation,
                            },
                        );

                    event.revision =
                        record.revision;

                    broadcast(
                        record,
                        event,
                    );

                    schedulePersist(
                        record,
                    );

                    return ok(
                        res,
                        {
                            accepted:
                                true,

                            event,

                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }


                /* ---------------------------------------------------------- */
                /* Generation streaming                                        */
                /* ---------------------------------------------------------- */

                if (
                    type ===
                    'generation_stream'
                ) {
                    if (
                        !record.generation
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_stale',
                            'No active generation',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        record.generation.ownerClientId !==
                        clientId
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_not_owner',
                            'Only the generation owner may publish stream state',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const generationId =
                        validateId(
                            body.generationId,
                            'generationId',
                            256,
                        );

                    if (
                        generationId !==
                        record.generation.id
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_stale',
                            'Generation ID is no longer active',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        record.generation.leaseUntil <=
                        now()
                    ) {
                        expireGeneration(
                            record,
                        );

                        return httpError(
                            res,
                            409,
                            'generation_expired',
                            'Generation lease expired',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const streamSeq =
                        Number(
                            body.streamSeq,
                        );

                    if (
                        !Number.isSafeInteger(
                            streamSeq,
                        ) ||
                        streamSeq <=
                            record.generation.streamSeq
                    ) {
                        return ok(
                            res,
                            {
                                duplicate:
                                    true,

                                reason:
                                    'stream_sequence',

                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    /*
                     * Streaming is still revision guarded. This prevents a
                     * stream chunk from overwriting a newer accepted state.
                     */
                    checkBaseRevision(
                        record,
                        body,
                    );

                    validateSnapshot(
                        body.snapshot,
                    );

                    record.snapshot =
                        clone(
                            body.snapshot,
                        );

                    record.snapshotHash =
                        crypto
                            .createHash(
                                'sha256',
                            )
                            .update(
                                stableStringify(
                                    record.snapshot,
                                ),
                            )
                            .digest(
                                'hex',
                            );

                    record.generation.streamSeq =
                        streamSeq;

                    record.generation.leaseUntil =
                        now() +
                        GENERATION_LEASE_MS;

                    record.revision += 1;

                    rememberOp(
                        record,
                        opId,
                    );

                    const event =
                        makeEvent(
                            record,
                            {
                                type:
                                    'generation_stream',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                payload: {
                                    generationId,

                                    streamSeq,
                                },

                                generation:
                                    record.generation,

                                includeSnapshot:
                                    true,
                            },
                        );

                    event.revision =
                        record.revision;

                    broadcast(
                        record,
                        event,
                    );

                    schedulePersist(
                        record,
                    );

                    return ok(
                        res,
                        {
                            accepted:
                                true,

                            event,

                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }


                /* ---------------------------------------------------------- */
                /* Generation terminal                                         */
                /* ---------------------------------------------------------- */

                if (
                    type ===
                    'generation_terminal'
                ) {
                    if (
                        !record.generation
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_stale',
                            'No active generation',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    if (
                        record.generation.ownerClientId !==
                        clientId
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_not_owner',
                            'Only the generation owner may finish the generation',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const generationId =
                        validateId(
                            body.generationId,
                            'generationId',
                            256,
                        );

                    if (
                        generationId !==
                        record.generation.id
                    ) {
                        return httpError(
                            res,
                            409,
                            'generation_stale',
                            'Generation ID is no longer active',
                            {
                                state:
                                    publicState(
                                        record,
                                    ),
                            },
                        );
                    }

                    const status =
                        [
                            'completed',
                            'stopped',
                            'failed',
                            'abandoned',
                        ].includes(
                            body.status,
                        )
                            ? body.status
                            : null;

                    if (!status) {
                        return httpError(
                            res,
                            400,
                            'invalid_generation_status',
                            'Invalid generation terminal state',
                        );
                    }

                    checkBaseRevision(
                        record,
                        body,
                    );

                    validateSnapshot(
                        body.snapshot,
                    );

                    record.snapshot =
                        clone(
                            body.snapshot,
                        );

                    record.snapshotHash =
                        crypto
                            .createHash(
                                'sha256',
                            )
                            .update(
                                stableStringify(
                                    record.snapshot,
                                ),
                            )
                            .digest(
                                'hex',
                            );

                    record.generation.state =
                        status;

                    record.generation.leaseUntil =
                        0;

                    record.revision += 1;

                    rememberOp(
                        record,
                        opId,
                    );

                    const oldGeneration =
                        clone(
                            record.generation,
                        );

                    const event =
                        makeEvent(
                            record,
                            {
                                type:
                                    'generation_terminal',

                                opId,

                                sourceClientId:
                                    clientId,

                                sourceDeviceId:
                                    deviceId,

                                payload: {
                                    generationId,

                                    status,
                                },

                                generation:
                                    oldGeneration,

                                includeSnapshot:
                                    true,
                            },
                        );

                    event.revision =
                        record.revision;

                    record.generation =
                        null;

                    broadcast(
                        record,
                        event,
                    );

                    await schedulePersist(
                        record,
                        true,
                    );

                    return ok(
                        res,
                        {
                            accepted:
                                true,

                            event,

                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }


                /* ---------------------------------------------------------- */
                /* Ordinary state mutation                                     */
                /* ---------------------------------------------------------- */

                checkBaseRevision(
                    record,
                    body,
                );

                /*
                 * Non-owner clients cannot mutate chat content while another
                 * client is generating.
                 */
                if (
                    record.generation &&
                    record.generation.ownerClientId !==
                        clientId
                ) {
                    return httpError(
                        res,
                        409,
                        'generation_lock',
                        'Chat mutations are locked while another client is generating',
                        {
                            state:
                                publicState(
                                    record,
                                ),
                        },
                    );
                }

                const snapshot =
                    body.snapshot;

                validateSnapshot(
                    snapshot,
                );

                record.snapshot =
                    clone(
                        snapshot,
                    );

                record.snapshotHash =
                    crypto
                        .createHash(
                            'sha256',
                        )
                        .update(
                            stableStringify(
                                record.snapshot,
                            ),
                        )
                        .digest(
                            'hex',
                        );

                record.revision += 1;

                rememberOp(
                    record,
                    opId,
                );

                const event =
                    makeEvent(
                        record,
                        {
                            type,

                            opId,

                            sourceClientId:
                                clientId,

                            sourceDeviceId:
                                deviceId,

                            payload:
                                clone(
                                    body.payload ||
                                    {},
                                ),

                            generation:
                                record.generation,

                            includeSnapshot:
                                true,
                        },
                    );

                event.revision =
                    record.revision;

                broadcast(
                    record,
                    event,
                );

                await schedulePersist(
                    record,
                    true,
                );

                return ok(
                    res,
                    {
                        accepted:
                            true,

                        event,

                        state:
                            publicState(
                                record,
                            ),
                    },
                );
            } catch (error) {
                if (
                    error.currentState
                ) {
                    return httpError(
                        res,
                        409,

                        error.code ||
                            'conflict',

                        error.message,

                        {
                            state:
                                error.currentState,
                        },
                    );
                }

                const status =
                    error.code ===
                        'not_member' ||
                    error.code ===
                        'membership_expired'
                        ? 403
                        : error.code ===
                            'protocol_mismatch'
                            ? 426
                            : error.code ===
                                'snapshot_too_large' ||
                              error.code ===
                                'payload_too_large'
                                ? 413
                                : error.code ===
                                    'device_mismatch'
                                    ? 409
                                    : 400;

                return httpError(
                    res,
                    status,

                    error.code ||
                        'invalid_request',

                    error.message,
                );
            }
        },
    );


    /* ---------------------------------------------------------------------- */
    /* Server watchdog                                                         */
    /* ---------------------------------------------------------------------- */

    scanTimer =
        setInterval(
            () => {
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

                    expireGeneration(
                        record,
                    );
                }
            },
            GENERATION_SCAN_MS,
        );

    console.log(
        `[${PLUGIN_ID}] loaded (protocol ${PROTOCOL_VERSION}, epoch ${runtimeEpoch})`,
    );
}


/* -------------------------------------------------------------------------- */
/* Plugin shutdown                                                             */
/* -------------------------------------------------------------------------- */

async function exit() {
    if (scanTimer) {
        clearInterval(
            scanTimer,
        );
    }

    scanTimer =
        null;

    for (
        const timer of
            persistTimers.values()
    ) {
        clearTimeout(
            timer,
        );
    }

    persistTimers.clear();

    for (
        const clients of
            sseByScope.values()
    ) {
        for (
            const res of clients
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

    sseByScope.clear();

    await Promise.all(
        [
            ...scopes.values(),
        ].map(
            record =>
                persistScope(
                    record,
                ),
        ),
    );

    console.log(
        `[${PLUGIN_ID}] unloaded`,
    );
}


/* -------------------------------------------------------------------------- */
/* Exports                                                                     */
/* -------------------------------------------------------------------------- */

module.exports = {
    init,
    exit,
    info,
};