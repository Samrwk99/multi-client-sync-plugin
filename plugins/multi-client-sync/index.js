/**
 * SillyTavern Multi-Client Chat Synchronization
 * Server Plugin
 *
 * Authoritative server-side synchronization layer for the companion UI extension.
 *
 * Provides:
 *   POST /join
 *   POST /event
 *   POST /heartbeat
 *   POST /leave
 *   GET  /events
 *   GET  /state
 *   GET  /health
 *
 * Important:
 * - State is intentionally scoped by authenticated SillyTavern user + chatKey.
 * - The authenticated server user is authoritative; client-supplied userId is
 *   never used for authorization.
 * - Server sequence numbers are authoritative.
 * - Event history is kept in memory and bounded.
 * - Generation ownership is lease/heartbeat based.
 * - A dead generation owner causes deterministic generation termination rather
 *   than attempting to continue a browser-owned generation on the server.
 *
 * This plugin does NOT replace SillyTavern's chat persistence system.
 * It coordinates clients around the normal SillyTavern chat state.
 */

const crypto = require('node:crypto');
const express = require('express');

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

const PLUGIN_ID = 'multi-client-sync';
const LOG_PREFIX = '[MCS Server]';

const MAX_EVENTS_PER_GROUP = 10000;
const MAX_JOIN_REPLAY_EVENTS = 2000;
const MAX_GROUPS = 1000;

const CLIENT_TTL_MS = 35000;
const EMPTY_GROUP_RETENTION_MS = 10 * 60 * 1000;

const CLEANUP_INTERVAL_MS = 5000;
const SSE_KEEPALIVE_INTERVAL_MS = 15000;

const MAX_ID_LENGTH = 256;
const MAX_CHAT_KEY_LENGTH = 1024;
const MAX_EVENT_ID_LENGTH = 512;
const MAX_EVENT_BYTES = 1024 * 1024;

const ALLOWED_EVENT_TYPES = new Set([
    'MESSAGE_SENT',
    'MESSAGE_RECEIVED',
    'MESSAGE_EDITED',
    'MESSAGE_DELETED',
    'MESSAGE_SWIPED',

    'CHAT_CHANGED',
    'CHAT_RELOADED',

    'GENERATION_STARTED',
    'GENERATION_STREAM',
    'GENERATION_STOP_REQUESTED',
    'GENERATION_STOPPED',
    'GENERATION_COMPLETED',
    'GENERATION_FAILED',
    'GENERATION_OWNER_RELEASED',
]);

// ---------------------------------------------------------------------------
// Server state
// ---------------------------------------------------------------------------

/**
 * Map:
 *   authenticatedUser + chatKey
 *      -> synchronization group
 *
 * @type {Map<string, GroupState>}
 */
const groups = new Map();

let cleanupTimer = null;
let keepaliveTimer = null;

const serverInstanceId = crypto.randomUUID();

// ---------------------------------------------------------------------------
// Logging
// ---------------------------------------------------------------------------

function log(...args) {
    console.log(LOG_PREFIX, ...args);
}

function warn(...args) {
    console.warn(LOG_PREFIX, ...args);
}

function error(...args) {
    console.error(LOG_PREFIX, ...args);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function randomId() {
    return crypto.randomUUID();
}

function cleanString(value, maxLength = MAX_ID_LENGTH) {
    if (value === undefined || value === null) {
        return '';
    }

    const result = String(value);

    if (result.length > maxLength) {
        return result.slice(0, maxLength);
    }

    return result;
}

function isPlainObject(value) {
    return (
        value !== null &&
        typeof value === 'object' &&
        !Array.isArray(value)
    );
}

function byteLength(value) {
    try {
        return Buffer.byteLength(
            JSON.stringify(value),
            'utf8',
        );
    } catch {
        return Infinity;
    }
}

function safeClone(value) {
    if (value === undefined) {
        return undefined;
    }

    try {
        return JSON.parse(
            JSON.stringify(value),
        );
    } catch {
        return value;
    }
}

function buildChatKey(body) {
    const characterId =
        cleanString(
            body.characterId,
            MAX_ID_LENGTH,
        );

    const groupId =
        cleanString(
            body.groupId,
            MAX_ID_LENGTH,
        );

    const chatId =
        cleanString(
            body.chatId,
            MAX_ID_LENGTH,
        );

    if (!chatId) {
        return null;
    }

    const scope =
        groupId
            ? `g:${groupId}`
            : `c:${characterId}`;

    return `${scope}::${chatId}`;
}

function scopeKey(
    userHandle,
    chatKey,
) {
    return `${userHandle}::${chatKey}`;
}

// ---------------------------------------------------------------------------
// Authentication
// ---------------------------------------------------------------------------

/**
 * SillyTavern exposes authenticated user information through req.user.
 *
 * We deliberately do NOT trust body.userId as the authorization identity.
 *
 * @param {import('express').Request} req
 * @returns {{handle:string}}
 */
function getAuthenticatedUser(req) {
    const handle =
        req?.user?.profile?.handle;

    if (!handle) {
        throw new Error(
            'Authenticated SillyTavern user is unavailable',
        );
    }

    return {
        handle: String(handle),
    };
}

function requireAuthenticatedUser(
    req,
    res,
) {
    try {
        return getAuthenticatedUser(req);
    } catch (e) {
        res.status(401).json({
            success: false,
            error:
                'Authentication required',
        });

        return null;
    }
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

function validateClientId(
    clientId,
) {
    const value =
        cleanString(
            clientId,
            MAX_ID_LENGTH,
        );

    if (
        !value ||
        value.length > MAX_ID_LENGTH
    ) {
        return null;
    }

    return value;
}

function validateDeviceId(
    deviceId,
) {
    const value =
        cleanString(
            deviceId,
            MAX_ID_LENGTH,
        );

    return value || 'unknown';
}

function validateChatKey(
    chatKey,
) {
    const value =
        cleanString(
            chatKey,
            MAX_CHAT_KEY_LENGTH,
        );

    return value || null;
}

function validateJoinBody(
    body,
) {
    if (!isPlainObject(body)) {
        return {
            ok: false,
            error: 'Request body must be an object',
        };
    }

    const clientId =
        validateClientId(
            body.clientId,
        );

    const chatKey =
        validateChatKey(
            body.chatKey,
        ) || buildChatKey(body);

    if (!clientId) {
        return {
            ok: false,
            error: 'Valid clientId is required',
        };
    }

    if (!chatKey) {
        return {
            ok: false,
            error:
                'Valid chat identity is required',
        };
    }

    const derivedChatKey =
        buildChatKey(body);

    if (
        body.chatKey &&
        derivedChatKey &&
        body.chatKey !== derivedChatKey
    ) {
        return {
            ok: false,
            error:
                'chatKey does not match supplied chat identity',
        };
    }

    const lastSequence =
        Number(body.lastSequence);

    return {
        ok: true,
        clientId,
        deviceId:
            validateDeviceId(
                body.deviceId,
            ),
        chatKey,
        lastSequence:
            Number.isSafeInteger(
                lastSequence,
            ) && lastSequence >= 0
                ? lastSequence
                : 0,
    };
}

function validateEventBody(
    body,
) {
    if (!isPlainObject(body)) {
        return {
            ok: false,
            error:
                'Request body must be an object',
        };
    }

    const clientId =
        validateClientId(
            body.clientId,
        );

    const chatKey =
        validateChatKey(
            body.chatKey,
        );

    if (!clientId) {
        return {
            ok: false,
            error: 'Valid clientId is required',
        };
    }

    if (!chatKey) {
        return {
            ok: false,
            error: 'chatKey is required',
        };
    }

    if (!isPlainObject(body.event)) {
        return {
            ok: false,
            error: 'event object is required',
        };
    }

    const eventId =
        cleanString(
            body.event.eventId,
            MAX_EVENT_ID_LENGTH,
        );

    const type =
        cleanString(
            body.event.type,
            MAX_ID_LENGTH,
        );

    if (!eventId) {
        return {
            ok: false,
            error:
                'event.eventId is required',
        };
    }

    if (!ALLOWED_EVENT_TYPES.has(type)) {
        return {
            ok: false,
            error:
                `Unsupported event type: ${type}`,
        };
    }

    if (
        byteLength(body.event) >
        MAX_EVENT_BYTES
    ) {
        return {
            ok: false,
            error:
                'Event payload is too large',
        };
    }

    return {
        ok: true,
        clientId,
        deviceId:
            validateDeviceId(
                body.deviceId,
            ),
        chatKey,
        event:
            safeClone(body.event),
    };
}

// ---------------------------------------------------------------------------
// Group state
// ---------------------------------------------------------------------------

function createGroup(
    userHandle,
    chatKey,
) {
    return {
        userHandle,
        chatKey,
        scopeKey:
            scopeKey(
                userHandle,
                chatKey,
            ),

        /**
         * Authoritative per-chat sequence.
         */
        sequence: 0,

        /**
         * Oldest retained sequence after
         * history pruning.
         */
        oldestSequence: 1,

        /**
         * @type {Array<object>}
         */
        events: [],

        /**
         * Recent event IDs for duplicate
         * detection.
         *
         * eventId -> {clientId, sequence}
         */
        eventIds: new Map(),

        /**
         * Client membership:
         *
         * clientId -> {
         *   clientId,
         *   deviceId,
         *   userHandle,
         *   joinedAt,
         *   lastHeartbeat,
         *   response
         * }
         */
        clients: new Map(),

        /**
         * Current generation state or null.
         */
        generation: null,

        createdAt: Date.now(),
        lastActivityAt: Date.now(),
    };
}

function getOrCreateGroup(
    userHandle,
    chatKey,
) {
    const key =
        scopeKey(
            userHandle,
            chatKey,
        );

    let group =
        groups.get(key);

    if (!group) {
        if (
            groups.size >=
            MAX_GROUPS
        ) {
            cleanupGroups();

            if (
                groups.size >=
                MAX_GROUPS
            ) {
                throw new Error(
                    'Synchronization server is at group capacity',
                );
            }
        }

        group =
            createGroup(
                userHandle,
                chatKey,
            );

        groups.set(
            key,
            group,
        );
    }

    group.lastActivityAt =
        Date.now();

    return group;
}

function getGroupForUser(
    userHandle,
    chatKey,
) {
    return groups.get(
        scopeKey(
            userHandle,
            chatKey,
        ),
    ) || null;
}

function touchClient(
    group,
    clientId,
    metadata = {},
) {
    const client =
        group.clients.get(
            clientId,
        );

    if (!client) {
        return null;
    }

    client.lastHeartbeat =
        Date.now();

    if (metadata.deviceId) {
        client.deviceId =
            metadata.deviceId;
    }

    group.lastActivityAt =
        Date.now();

    return client;
}

// ---------------------------------------------------------------------------
// SSE
// ---------------------------------------------------------------------------

function writeSse(
    res,
    data,
) {
    if (
        !res ||
        res.writableEnded ||
        res.destroyed
    ) {
        return false;
    }

    try {
        res.write(
            `data: ${JSON.stringify(
                data,
            )}\n\n`,
        );

        return true;
    } catch (e) {
        return false;
    }
}

function writeSseComment(
    res,
    text = 'keepalive',
) {
    if (
        !res ||
        res.writableEnded ||
        res.destroyed
    ) {
        return false;
    }

    try {
        res.write(
            `: ${text}\n\n`,
        );

        return true;
    } catch {
        return false;
    }
}

function closeSseConnection(
    member,
) {
    if (!member?.response) {
        return;
    }

    const response =
        member.response;

    member.response = null;

    try {
        response.end();
    } catch {
        try {
            response.destroy();
        } catch {
            // ignore
        }
    }
}

function attachSse(
    group,
    member,
    req,
    res,
) {
    if (member.response) {
        closeSseConnection(
            member,
        );
    }

    res.statusCode = 200;

    res.setHeader(
        'Content-Type',
        'text/event-stream',
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

    member.response = res;

    writeSse(
        res,
        {
            type: 'CONNECTED',
            chatKey:
                group.chatKey,
            sequence:
                group.sequence,
            serverInstanceId,
        },
    );

    const cleanupConnection =
        () => {
            if (
                member.response ===
                res
            ) {
                member.response = null;
            }
        };

    res.on(
        'close',
        cleanupConnection,
    );

    res.on(
        'error',
        cleanupConnection,
    );

    req.on(
        'close',
        cleanupConnection,
    );

    log(
        'SSE attached',
        member.clientId,
        group.chatKey,
    );
}

function broadcast(
    group,
    event,
) {
    for (
        const member of
        group.clients.values()
    ) {
        if (!member.response) {
            continue;
        }

        const ok =
            writeSse(
                member.response,
                event,
            );

        if (!ok) {
            member.response = null;
        }
    }
}

function broadcastComment(
    group,
) {
    for (
        const member of
        group.clients.values()
    ) {
        if (!member.response) {
            continue;
        }

        const ok =
            writeSseComment(
                member.response,
            );

        if (!ok) {
            member.response = null;
        }
    }
}

// ---------------------------------------------------------------------------
// Event history
// ---------------------------------------------------------------------------

function pruneEventHistory(
    group,
) {
    while (
        group.events.length >
        MAX_EVENTS_PER_GROUP
    ) {
        const removed =
            group.events.shift();

        if (
            removed?.eventId
        ) {
            group.eventIds.delete(
                removed.eventId,
            );
        }
    }

    group.oldestSequence =
        group.events.length > 0
            ? group.events[0].sequence
            : group.sequence + 1;
}

function findStoredEvent(
    group,
    eventId,
) {
    const metadata =
        group.eventIds.get(
            eventId,
        );

    if (!metadata) {
        return null;
    }

    const event =
        group.events.find(
            (item) =>
                item.sequence ===
                metadata.sequence,
        );

    if (!event) {
        return null;
    }

    return event;
}

function appendEvent(
    group,
    incomingEvent,
    source,
) {
    const event = {
        eventId:
            cleanString(
                incomingEvent.eventId ||
                    randomId(),
                MAX_EVENT_ID_LENGTH,
            ),

        clientId:
            cleanString(
                source.clientId,
                MAX_ID_LENGTH,
            ),

        deviceId:
            cleanString(
                source.deviceId ||
                    'unknown',
                MAX_ID_LENGTH,
            ),

        userId:
            group.userHandle,

        chatKey:
            group.chatKey,

        type:
            cleanString(
                incomingEvent.type,
                MAX_ID_LENGTH,
            ),

        payload:
            safeClone(
                incomingEvent.payload,
            ),

        generationId:
            incomingEvent.generationId ||
            undefined,

        streamSeq:
            incomingEvent.streamSeq ||
            undefined,

        timestamp:
            Number.isFinite(
                Number(
                    incomingEvent.timestamp,
                ),
            )
                ? Number(
                    incomingEvent.timestamp,
                )
                : Date.now(),
    };

    group.sequence += 1;

    event.sequence =
        group.sequence;

    group.events.push(
        event,
    );

    group.eventIds.set(
        event.eventId,
        {
            clientId:
                event.clientId,
            sequence:
                event.sequence,
        },
    );

    pruneEventHistory(
        group,
    );

    group.lastActivityAt =
        Date.now();

    broadcast(
        group,
        event,
    );

    return event;
}

function appendServerEvent(
    group,
    type,
    payload = {},
    extra = {},
) {
    return appendEvent(
        group,
        {
            eventId:
                `server-${randomId()}`,

            type,
            payload,

            timestamp:
                Date.now(),

            ...extra,
        },
        {
            clientId:
                'server',
            deviceId:
                'server',
        },
    );
}

// ---------------------------------------------------------------------------
// Generation state
// ---------------------------------------------------------------------------

function serializeGeneration(
    generation,
) {
    if (!generation) {
        return null;
    }

    return {
        generationId:
            generation.generationId,

        ownerId:
            generation.ownerId,

        ownerDevice:
            generation.ownerDevice,

        status:
            generation.status,

        startedAt:
            generation.startedAt,

        serverSequence:
            generation.serverSequence,

        streamSeq:
            generation.streamSeq,

        streamSeqApplied:
            generation.streamSeq,

        messageId:
            generation.messageId,

        messageKey:
            generation.messageKey,

        currentText:
            generation.currentText,

        lastActivityAt:
            generation.lastActivityAt,
    };
}

function getCurrentGeneration(
    group,
) {
    return group.generation;
}

function generationMatches(
    group,
    event,
) {
    return (
        group.generation &&
        group.generation.generationId ===
            event.generationId
    );
}

function updateGenerationTextFromPayload(
    generation,
    payload,
) {
    if (
        !generation ||
        !payload
    ) {
        return;
    }

    if (
        isPlainObject(
            payload.message,
        ) &&
        typeof payload.message.mes ===
            'string'
    ) {
        generation.currentText =
            payload.message.mes;
    } else if (
        typeof payload.currentText ===
        'string'
    ) {
        generation.currentText =
            payload.currentText;
    }
}

function startGeneration(
    group,
    event,
    source,
) {
    if (
        group.generation &&
        group.generation.status ===
            'active'
    ) {
        if (
            group.generation.generationId ===
            event.generationId &&
            group.generation.ownerId ===
            source.clientId
        ) {
            return {
                ok: true,
                duplicate: true,
            };
        }

        return {
            ok: false,
            status: 409,
            error:
                'generation_already_active',
        };
    }

    if (
        !event.generationId
    ) {
        return {
            ok: false,
            status: 400,
            error:
                'generationId is required',
        };
    }

    const payload =
        isPlainObject(
            event.payload,
        )
            ? event.payload
            : {};

    const generation = {
        generationId:
            cleanString(
                event.generationId,
                MAX_ID_LENGTH,
            ),

        ownerId:
            source.clientId,

        ownerDevice:
            source.deviceId,

        status:
            'active',

        startedAt:
            Number.isFinite(
                Number(
                    event.timestamp,
                ),
            )
                ? Number(
                    event.timestamp,
                )
                : Date.now(),

        serverSequence:
            group.sequence + 1,

        streamSeq:
            0,

        messageId:
            Number.isInteger(
                payload.messageId,
            )
                ? payload.messageId
                : Number.isInteger(
                    payload.insertAt,
                )
                    ? payload.insertAt
                    : null,

        messageKey:
            payload.messageKey ||
            null,

        currentText:
            isPlainObject(
                payload.message,
            ) &&
            typeof payload.message.mes ===
                'string'
                ? payload.message.mes
                : '',

        lastActivityAt:
            Date.now(),
    };

    group.generation =
        generation;

    const accepted =
        appendEvent(
            group,
            event,
            source,
        );

    generation.serverSequence =
        accepted.sequence;

    return {
        ok: true,
        duplicate: false,
        event: accepted,
    };
}

function updateGenerationStream(
    group,
    event,
    source,
) {
    const generation =
        group.generation;

    if (!generation) {
        return {
            ok: false,
            status: 409,
            error:
                'no_active_generation',
        };
    }

    if (
        generation.generationId !==
        event.generationId
    ) {
        return {
            ok: false,
            status: 409,
            error:
                'generation_id_mismatch',
        };
    }

    if (
        generation.ownerId !==
        source.clientId
    ) {
        return {
            ok: false,
            status: 403,
            error:
                'generation_owner_required',
        };
    }

    const streamSeq =
        Number(
            event.streamSeq,
        );

    if (
        !Number.isSafeInteger(
            streamSeq,
        ) ||
        streamSeq <= 0
    ) {
        return {
            ok: false,
            status: 400,
            error:
                'valid streamSeq is required',
        };
    }

    if (
        streamSeq <=
        generation.streamSeq
    ) {
        return {
            ok: false,
            status: 409,
            error:
                'stale_stream_sequence',
        };
    }

    const payload =
        isPlainObject(
            event.payload,
        )
            ? event.payload
            : {};

    updateGenerationTextFromPayload(
        generation,
        payload,
    );

    generation.streamSeq =
        streamSeq;

    generation.lastActivityAt =
        Date.now();

    const accepted =
        appendEvent(
            group,
            event,
            source,
        );

    return {
        ok: true,
        event: accepted,
    };
}

function finishGeneration(
    group,
    event,
    source,
) {
    const generation =
        group.generation;

    if (!generation) {
        return {
            ok: false,
            status: 409,
            error:
                'no_active_generation',
        };
    }

    if (
        generation.generationId !==
        event.generationId
    ) {
        return {
            ok: false,
            status: 409,
            error:
                'generation_id_mismatch',
        };
    }

    if (
        generation.ownerId !==
        source.clientId
    ) {
        return {
            ok: false,
            status: 403,
            error:
                'generation_owner_required',
        };
    }

    updateGenerationTextFromPayload(
        generation,
        isPlainObject(
            event.payload,
        )
            ? event.payload
            : {},
    );

    generation.lastActivityAt =
        Date.now();

    const accepted =
        appendEvent(
            group,
            event,
            source,
        );

    group.generation =
        null;

    return {
        ok: true,
        event: accepted,
    };
}

function terminateOrphanedGeneration(
    group,
    reason,
) {
    const generation =
        group.generation;

    if (!generation) {
        return;
    }

    const generationId =
        generation.generationId;

    const ownerId =
        generation.ownerId;

    appendServerEvent(
        group,
        'GENERATION_OWNER_RELEASED',
        {
            ownerId,
            ownerDevice:
                generation.ownerDevice,
            reason,
        },
        {
            generationId,
        },
    );

    appendServerEvent(
        group,
        'GENERATION_FAILED',
        {
            reason:
                'generation_owner_lost',
            ownerId,
            ownerDevice:
                generation.ownerDevice,
            messageKey:
                generation.messageKey,
            messageId:
                generation.messageId,
            finalText:
                generation.currentText,
        },
        {
            generationId,
        },
    );

    group.generation =
        null;

    log(
        'terminated orphaned generation',
        generationId,
        reason,
        group.chatKey,
    );
}

// ---------------------------------------------------------------------------
// Event authorization / application
// ---------------------------------------------------------------------------

function handleEvent(
    group,
    incomingEvent,
    source,
) {
    const event = {
        ...incomingEvent,
        clientId:
            source.clientId,
        deviceId:
            source.deviceId,
        chatKey:
            group.chatKey,
        userId:
            group.userHandle,
    };

    const existing =
        findStoredEvent(
            group,
            event.eventId,
        );

    if (existing) {
        if (
            existing.clientId !==
            source.clientId
        ) {
            return {
                ok: false,
                status: 409,
                error:
                    'event_id_conflict',
            };
        }

        return {
            ok: true,
            duplicate: true,
            event: existing,
            sequence:
                existing.sequence,
        };
    }

    const type =
        event.type;

    if (
        type ===
        'GENERATION_STARTED'
    ) {
        return startGeneration(
            group,
            event,
            source,
        );
    }

    if (
        type ===
        'GENERATION_STREAM'
    ) {
        return updateGenerationStream(
            group,
            event,
            source,
        );
    }

    if (
        type ===
        'GENERATION_STOP_REQUESTED'
    ) {
        if (
            !group.generation
        ) {
            return {
                ok: false,
                status: 409,
                error:
                    'no_active_generation',
            };
        }

        if (
            group.generation.generationId !==
            event.generationId
        ) {
            return {
                ok: false,
                status: 409,
                error:
                    'generation_id_mismatch',
            };
        }

        /*
         * Any authorized member may request
         * that the owner stop the active
         * generation.
         */
        const accepted =
            appendEvent(
                group,
                event,
                source,
            );

        return {
            ok: true,
            event: accepted,
        };
    }

    if (
        type ===
            'GENERATION_STOPPED' ||
        type ===
            'GENERATION_COMPLETED' ||
        type ===
            'GENERATION_FAILED'
    ) {
        return finishGeneration(
            group,
            event,
            source,
        );
    }

    if (
        type ===
        'GENERATION_OWNER_RELEASED'
    ) {
        const generation =
            group.generation;

        if (!generation) {
            return {
                ok: false,
                status: 409,
                error:
                    'no_active_generation',
            };
        }

        if (
            generation.generationId !==
            event.generationId
        ) {
            return {
                ok: false,
                status: 409,
                error:
                    'generation_id_mismatch',
            };
        }

        if (
            generation.ownerId !==
            source.clientId
        ) {
            return {
                ok: false,
                status: 403,
                error:
                    'generation_owner_required',
            };
        }

        appendEvent(
            group,
            event,
            source,
        );

        appendServerEvent(
            group,
            'GENERATION_FAILED',
            {
                reason:
                    'generation_owner_released',
                ownerId:
                    generation.ownerId,
                ownerDevice:
                    generation.ownerDevice,
                messageKey:
                    generation.messageKey,
                messageId:
                    generation.messageId,
                finalText:
                    generation.currentText,
            },
            {
                generationId:
                    generation.generationId,
            },
        );

        group.generation =
            null;

        return {
            ok: true,
        };
    }

    /*
     * Normal chat mutations.
     */
    const accepted =
        appendEvent(
            group,
            event,
            source,
        );

    return {
        ok: true,
        event: accepted,
    };
}

// ---------------------------------------------------------------------------
// Recovery
// ---------------------------------------------------------------------------

function buildJoinReplay(
    group,
    lastSequence,
) {
    const headSequence =
        group.sequence;

    if (
        lastSequence >=
        headSequence
    ) {
        return {
            recoveryRequired: false,
            missedEvents: [],
        };
    }

    if (
        group.events.length ===
        0
    ) {
        return {
            recoveryRequired:
                lastSequence >
                headSequence,
            missedEvents: [],
        };
    }

    const earliestAvailable =
        group.events[0].sequence;

    /*
     * The requested starting point is
     * older than the retained history.
     *
     * The client must fall back to its
     * authoritative SillyTavern chat reload.
     */
    if (
        lastSequence <
        earliestAvailable - 1
    ) {
        return {
            recoveryRequired: true,
            missedEvents: [],
        };
    }

    const missed =
        group.events.filter(
            (event) =>
                event.sequence >
                lastSequence,
        );

    /*
     * Don't send enormous replay
     * payloads to a reconnecting browser.
     * Force authoritative reload instead.
     */
    if (
        missed.length >
        MAX_JOIN_REPLAY_EVENTS
    ) {
        return {
            recoveryRequired: true,
            missedEvents: [],
        };
    }

    return {
        recoveryRequired: false,
        missedEvents:
            safeClone(missed),
    };
}

// ---------------------------------------------------------------------------
// Cleanup
// ---------------------------------------------------------------------------

function removeClient(
    group,
    clientId,
) {
    const member =
        group.clients.get(
            clientId,
        );

    if (!member) {
        return false;
    }

    closeSseConnection(
        member,
    );

    group.clients.delete(
        clientId,
    );

    group.lastActivityAt =
        Date.now();

    return true;
}

function cleanupStaleClients() {
    const now =
        Date.now();

    for (
        const group of
        groups.values()
    ) {
        const staleClients = [];

        for (
            const member of
            group.clients.values()
        ) {
            if (
                now -
                member.lastHeartbeat >
                CLIENT_TTL_MS
            ) {
                staleClients.push(
                    member,
                );
            }
        }

        for (
            const member of staleClients
        ) {
            const wasOwner =
                group.generation &&
                group.generation.ownerId ===
                    member.clientId;

            if (wasOwner) {
                terminateOrphanedGeneration(
                    group,
                    'heartbeat_expired',
                );
            }

            removeClient(
                group,
                member.clientId,
            );

            log(
                'removed stale client',
                member.clientId,
                group.chatKey,
            );
        }
    }
}

function cleanupGroups() {
    cleanupStaleClients();

    const now =
        Date.now();

    for (
        const [
            key,
            group,
        ] of groups
    ) {
        if (
            group.clients.size === 0 &&
            !group.generation &&
            now -
                group.lastActivityAt >
                EMPTY_GROUP_RETENTION_MS
        ) {
            groups.delete(
                key,
            );
        }
    }

    if (
        groups.size <=
        MAX_GROUPS
    ) {
        return;
    }

    /*
     * Last-resort bounded-memory cleanup.
     * Prefer groups with no active clients.
     */
    const removable =
        [...groups.values()]
            .filter(
                (group) =>
                    group.clients.size ===
                    0 &&
                    !group.generation,
            )
            .sort(
                (a, b) =>
                    a.lastActivityAt -
                    b.lastActivityAt,
            );

    while (
        groups.size >
            MAX_GROUPS &&
        removable.length > 0
    ) {
        const group =
            removable.shift();

        groups.delete(
            group.scopeKey,
        );
    }
}

function sendKeepalives() {
    for (
        const group of
        groups.values()
    ) {
        if (
            group.clients.size ===
            0
        ) {
            continue;
        }

        broadcastComment(
            group,
        );
    }
}

// ---------------------------------------------------------------------------
// Routes
// ---------------------------------------------------------------------------

function registerRoutes(
    router,
) {
    router.use(
        express.json({
            limit:
                `${MAX_EVENT_BYTES}b`,
        }),
    );

    // -------------------------------------------------------
    // Health
    // -------------------------------------------------------

    router.get(
        '/health',
        (req, res) => {
            res.json({
                success: true,
                plugin:
                    PLUGIN_ID,
                serverInstanceId,
                groups:
                    groups.size,
                uptime:
                    process.uptime(),
            });
        },
    );

    // -------------------------------------------------------
    // Join
    // -------------------------------------------------------

    router.post(
        '/join',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const validation =
                validateJoinBody(
                    req.body,
                );

            if (!validation.ok) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            validation.error,
                    });
            }

            const {
                clientId,
                deviceId,
                chatKey,
                lastSequence,
            } = validation;

            try {
                const group =
                    getOrCreateGroup(
                        auth.handle,
                        chatKey,
                    );

                /*
                 * A reload/rejoin using the
                 * same client ID replaces its
                 * previous membership heartbeat.
                 */
                let member =
                    group.clients.get(
                        clientId,
                    );

                if (!member) {
                    member = {
                        clientId,
                        deviceId,
                        userHandle:
                            auth.handle,
                        joinedAt:
                            Date.now(),
                        lastHeartbeat:
                            Date.now(),
                        response:
                            null,
                    };

                    group.clients.set(
                        clientId,
                        member,
                    );
                } else {
                    member.deviceId =
                        deviceId;

                    member.lastHeartbeat =
                        Date.now();
                }

                group.lastActivityAt =
                    Date.now();

                const replay =
                    buildJoinReplay(
                        group,
                        lastSequence,
                    );

                res.json({
                    success:
                        true,

                    chatKey:
                        group.chatKey,

                    nextSequence:
                        group.sequence +
                        1,

                    serverInstanceId,

                    clientCount:
                        group.clients.size,

                    missedEvents:
                        replay.missedEvents,

                    recoveryRequired:
                        replay.recoveryRequired,

                    state: {
                        generation:
                            serializeGeneration(
                                group.generation,
                            ),
                    },
                });

                log(
                    'client joined',
                    {
                        clientId,
                        user:
                            auth.handle,
                        chatKey,
                        lastSequence,
                        serverSequence:
                            group.sequence,
                        recoveryRequired:
                            replay.recoveryRequired,
                    },
                );
            } catch (e) {
                error(
                    'join failed',
                    e,
                );

                res.status(
                    503,
                ).json({
                    success:
                        false,
                    error:
                        e.message ||
                        'Unable to join synchronization group',
                });
            }
        },
    );

    // -------------------------------------------------------
    // SSE Events
    // -------------------------------------------------------

    router.get(
        '/events',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const clientId =
                validateClientId(
                    req.query.clientId,
                );

            const chatKey =
                validateChatKey(
                    req.query.chatKey,
                );

            if (
                !clientId ||
                !chatKey
            ) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'clientId and chatKey are required',
                    });
            }

            const group =
                getGroupForUser(
                    auth.handle,
                    chatKey,
                );

            if (!group) {
                return res
                    .status(404)
                    .json({
                        success:
                            false,
                        error:
                            'Synchronization group not found',
                    });
            }

            const member =
                group.clients.get(
                    clientId,
                );

            if (!member) {
                return res
                    .status(403)
                    .json({
                        success:
                            false,
                        error:
                            'Client is not a member of this synchronization group',
                    });
            }

            touchClient(
                group,
                clientId,
            );

            attachSse(
                group,
                member,
                req,
                res,
            );
        },
    );

    // -------------------------------------------------------
    // State
    // -------------------------------------------------------

    router.get(
        '/state',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const chatKey =
                validateChatKey(
                    req.query.chatKey,
                );

            if (!chatKey) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'chatKey is required',
                    });
            }

            const group =
                getGroupForUser(
                    auth.handle,
                    chatKey,
                );

            if (!group) {
                return res.json({
                    success:
                        true,
                    chatKey,
                    sequence:
                        0,
                    clientCount:
                        0,
                    generation:
                        null,
                    eventsAvailable:
                        false,
                });
            }

            res.json({
                success:
                    true,

                chatKey:
                    group.chatKey,

                sequence:
                    group.sequence,

                oldestSequence:
                    group.oldestSequence,

                clientCount:
                    group.clients.size,

                generation:
                    serializeGeneration(
                        group.generation,
                    ),

                eventsAvailable:
                    group.events.length >
                    0,

                serverInstanceId,
            });
        },
    );

    // -------------------------------------------------------
    // Event
    // -------------------------------------------------------

    router.post(
        '/event',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const validation =
                validateEventBody(
                    req.body,
                );

            if (!validation.ok) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            validation.error,
                    });
            }

            const {
                clientId,
                deviceId,
                chatKey,
                event,
            } = validation;

            const group =
                getGroupForUser(
                    auth.handle,
                    chatKey,
                );

            if (!group) {
                return res
                    .status(403)
                    .json({
                        success:
                            false,
                        error:
                            'Client is not a member of this synchronization group',
                    });
            }

            const member =
                group.clients.get(
                    clientId,
                );

            if (!member) {
                return res
                    .status(403)
                    .json({
                        success:
                            false,
                        error:
                            'Client is not a member of this synchronization group',
                    });
            }

            /*
             * Client identity is authenticated
             * through the SillyTavern session,
             * while clientId/deviceId are only
             * identifiers inside that session.
             */
            touchClient(
                group,
                clientId,
                {
                    deviceId,
                },
            );

            if (
                event.clientId &&
                event.clientId !==
                    clientId
            ) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'event.clientId does not match request clientId',
                    });
            }

            if (
                event.chatKey &&
                event.chatKey !==
                    chatKey
            ) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'event.chatKey does not match request chatKey',
                    });
            }

            event.clientId =
                clientId;

            event.deviceId =
                deviceId;

            event.chatKey =
                chatKey;

            event.userId =
                auth.handle;

            try {
                const result =
                    handleEvent(
                        group,
                        event,
                        {
                            clientId,
                            deviceId,
                        },
                    );

                if (!result.ok) {
                    return res
                        .status(
                            result.status ||
                                400,
                        )
                        .json({
                            success:
                                false,
                            error:
                                result.error,
                            generation:
                                serializeGeneration(
                                    group.generation,
                                ),
                            sequence:
                                group.sequence,
                        });
                }

                return res.json({
                    success:
                        true,

                    duplicate:
                        Boolean(
                            result.duplicate,
                        ),

                    event:
                        result.event
                            ? safeClone(
                                result.event,
                            )
                            : undefined,

                    sequence:
                        result.event
                            ?.sequence ??
                        group.sequence,

                    generation:
                        serializeGeneration(
                            group.generation,
                        ),
                });
            } catch (e) {
                error(
                    'event handling failed',
                    e,
                );

                return res
                    .status(500)
                    .json({
                        success:
                            false,
                        error:
                            'Internal synchronization error',
                    });
            }
        },
    );

    // -------------------------------------------------------
    // Heartbeat
    // -------------------------------------------------------

    router.post(
        '/heartbeat',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const clientId =
                validateClientId(
                    req.body?.clientId,
                );

            const chatKey =
                validateChatKey(
                    req.body?.chatKey,
                );

            if (
                !clientId ||
                !chatKey
            ) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'clientId and chatKey are required',
                    });
            }

            const group =
                getGroupForUser(
                    auth.handle,
                    chatKey,
                );

            if (!group) {
                return res
                    .status(404)
                    .json({
                        success:
                            false,
                        error:
                            'Synchronization group not found',
                    });
            }

            const member =
                group.clients.get(
                    clientId,
                );

            if (!member) {
                return res
                    .status(403)
                    .json({
                        success:
                            false,
                        error:
                            'Client is not a member of this synchronization group',
                    });
            }

            touchClient(
                group,
                clientId,
            );

            res.json({
                success:
                    true,

                sequence:
                    group.sequence,

                generation:
                    serializeGeneration(
                        group.generation,
                    ),
            });
        },
    );

    // -------------------------------------------------------
    // Leave
    // -------------------------------------------------------

    router.post(
        '/leave',
        (req, res) => {
            const auth =
                requireAuthenticatedUser(
                    req,
                    res,
                );

            if (!auth) {
                return;
            }

            const clientId =
                validateClientId(
                    req.body?.clientId,
                );

            const chatKey =
                validateChatKey(
                    req.body?.chatKey,
                );

            if (
                !clientId ||
                !chatKey
            ) {
                return res
                    .status(400)
                    .json({
                        success:
                            false,
                        error:
                            'clientId and chatKey are required',
                    });
            }

            const group =
                getGroupForUser(
                    auth.handle,
                    chatKey,
                );

            if (!group) {
                return res.json({
                    success:
                        true,
                    alreadyAbsent:
                        true,
                });
            }

            const member =
                group.clients.get(
                    clientId,
                );

            if (!member) {
                return res.json({
                    success:
                        true,
                    alreadyAbsent:
                        true,
                });
            }

            /*
             * If this client owns the
             * active generation, terminate it
             * before removing the membership.
             *
             * This is also the crash-safety fallback:
             * if the explicit owner-release event
             * was lost, leave() still cleans it up.
             */
            if (
                group.generation &&
                group.generation.ownerId ===
                    clientId
            ) {
                terminateOrphanedGeneration(
                    group,
                    'owner_left',
                );
            }

            removeClient(
                group,
                clientId,
            );

            res.json({
                success:
                    true,

                clientCount:
                    group.clients.size,

                sequence:
                    group.sequence,
            });

            log(
                'client left',
                {
                    clientId,
                    user:
                        auth.handle,
                    chatKey,
                },
            );
        },
    );
}

// ---------------------------------------------------------------------------
// Init / Exit
// ---------------------------------------------------------------------------

async function init(router) {
    registerRoutes(
        router,
    );

    cleanupTimer =
        setInterval(
            cleanupGroups,
            CLEANUP_INTERVAL_MS,
        );

    keepaliveTimer =
        setInterval(
            () => {
                cleanupStaleClients();

                for (
                    const group of
                    groups.values()
                ) {
                    if (
                        group.clients.size >
                        0
                    ) {
                        broadcastComment(
                            group,
                        );
                    }
                }
            },
            SSE_KEEPALIVE_INTERVAL_MS,
        );

    log(
        'Multi-Client Sync server plugin loaded',
        {
            serverInstanceId,
            maxEventsPerGroup:
                MAX_EVENTS_PER_GROUP,
            clientTtlMs:
                CLIENT_TTL_MS,
        },
    );
}

async function exit() {
    if (cleanupTimer) {
        clearInterval(
            cleanupTimer,
        );

        cleanupTimer =
            null;
    }

    if (keepaliveTimer) {
        clearInterval(
            keepaliveTimer,
        );

        keepaliveTimer =
            null;
    }

    for (
        const group of
        groups.values()
    ) {
        if (
            group.generation
        ) {
            terminateOrphanedGeneration(
                group,
                'server_shutdown',
            );
        }

        for (
            const member of
            group.clients.values()
        ) {
            closeSseConnection(
                member,
            );
        }

        group.clients.clear();
    }

    groups.clear();

    log(
        'Multi-Client Sync server plugin stopped',
    );
}

// ---------------------------------------------------------------------------
// Plugin export
// ---------------------------------------------------------------------------

module.exports = {
    init,
    exit,

    info: {
        id:
            PLUGIN_ID,

        name:
            'Multi-Client Chat Synchronization',

        description:
            'Authoritative server-side synchronization for multiple SillyTavern clients viewing the same chat.',
    },
};