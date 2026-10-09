'use strict';

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const crypto = require('crypto');

const PROTOCOL = 11;
const SCHEMA = 11;
const PLUGIN_ID = 'multi-client-sync';

const LIMITS = Object.freeze({
    maxSnapshotBytes: 12 * 1024 * 1024,
    maxEventBytes: 512 * 1024,
    chunkPayloadBytes: 256 * 1024,
    // Headroom above maxSnapshotBytes: the event envelope (wrapper keys +
    // JSON escaping inflation) can push a legal 12 MiB snapshot past the
    // assembly ceiling and turn a valid publish into event_too_large.
    maxChunkAssemblyBytes: 12 * 1024 * 1024 + 256 * 1024,
    maxEventHistoryBytes: 4 * 1024 * 1024,
    maxEvents: 300,
    maxRecentOps: 1000,
    maxDeltaOps: 500,
    maxDeltaBytes: 256 * 1024,
    maxDeltaJournalBytes: 4 * 1024 * 1024,
    maxDeltaJournalHardBytes: 8 * 1024 * 1024,
    memberTtlMs: 60_000,
    heartbeatMinMs: 3_000,
    generationLeaseMs: 30_000,
    generationMaxMs: 30 * 60_000,
    maxScopesPerUser: 200,
    maxSubscribersPerScope: 25,
    maxBufferedSseBytes: 4 * 1024 * 1024,
    fsyncState: false,
});

const scopes = new Map();
const userLocks = new Map();
const subscribers = new Map();
let routerRef = null;
let serverInstanceId = null;
let transferIdCounter = 0;

function now() { return Date.now(); }
function clone(value) { return value === undefined ? undefined : JSON.parse(JSON.stringify(value)); }
function newTransferId() { return `${serverInstanceId || 'srv'}-${++transferIdCounter}`; }

function jsonToUtf8Bytes(value) { return Buffer.from(JSON.stringify(value), 'utf8'); }
function utf8ByteLength(value) { return Buffer.byteLength(JSON.stringify(value ?? null), 'utf8'); }
function sha256Bytes(buffer) { return crypto.createHash('sha256').update(buffer).digest('hex'); }
function base64Encode(buffer) { return buffer.toString('base64'); }

function bytes(value) { return utf8ByteLength(value); }
function sha256(value) { return crypto.createHash('sha256').update(String(value)).digest('hex'); }
function jsonSafeId(value) { return typeof value === 'string' && /^[A-Za-z0-9._~:-]{1,240}$/.test(value); }
function isObject(value) { return value && typeof value === 'object' && !Array.isArray(value); }

function operationFingerprint(parts) {
    return sha256Bytes(Buffer.from(JSON.stringify(parts), 'utf8'));
}

function userRoot(req) {
    return req?.user?.directories?.root || req?.user?.directories?.data || req?.user?.directories?.user || null;
}

function userKey(req) {
    const root = userRoot(req);
    if (root) return path.resolve(root);
    const user = req?.user;
    return String(user?.profile?.handle || user?.handle || user?.username || user?.id || 'unknown-user');
}

function requireAuth(req, res) {
    if (!req?.user) {
        res.status(401).json({ ok: false, error: 'unauthenticated' });
        return false;
    }
    return true;
}

function scopeKey(scope) {
    return JSON.stringify([
        String(scope?.kind || ''),
        String(scope?.ownerId || ''),
        String(scope?.chatId || ''),
        String(scope?.branchId || ''),
    ]);
}

function validateScope(scope) {
    if (!isObject(scope)) return 'invalid_scope';
    if (!['character', 'group'].includes(scope.kind)) return 'invalid_scope_kind';
    for (const field of ['ownerId', 'chatId']) {
        const value = String(scope[field] ?? '');
        if (!value || value.length > 500 || value.includes('\0') || value.includes('/') || value.includes('\\')) {
            return `invalid_scope_${field}`;
        }
    }
    if (scope.branchId != null) {
        const value = String(scope.branchId);
        if (value.length > 500 || value.includes('\0') || value.includes('/') || value.includes('\\')) {
            return 'invalid_scope_branch';
        }
    }
    return null;
}

function canonicalSnapshot(input) {
    if (!isObject(input)) throw new Error('snapshot_required');
    if (!Array.isArray(input.messages)) throw new Error('snapshot_messages_required');
    const messages = clone(input.messages);
    const seen = new Set();
    for (const message of messages) {
        if (!isObject(message)) throw new Error('invalid_message');
        // Message identity must be a validated string — never a numeric or
        // otherwise coercible value that could alias across representations.
        const rawId = message?.extra?.multi_client_sync?.messageId;
        if (typeof rawId !== 'string' || !jsonSafeId(rawId)) throw new Error('message_ids_required');
        if (seen.has(rawId)) throw new Error('duplicate_message_id');
        seen.add(rawId);
    }
    return { messages, metadata: clone(isObject(input.metadata) ? input.metadata : {}) };
}

function preserveTerminalSnapshot(state, incoming, generation) {
    // A non-empty terminal snapshot can still be stale (for example, a tab
    // switched chats and supplied its pre-generation baseline). Preserve the
    // established history, then merge the terminal snapshot by stable message
    // ID. Never use messageIndex as permission to overwrite another assistant.
    const result = canonicalSnapshot(incoming);
    const existingMessages = Array.isArray(state?.snapshot?.messages)
        ? clone(state.snapshot.messages)
        : [];
    const incomingIds = new Set(result.messages.map(messageIdFromMessage).filter(Boolean));
    let tombstones = readDeltaTombstones(result.metadata);

    // Reinsert existing messages omitted from the terminal payload unless the
    // payload carries an explicit tombstone proving intentional deletion.
    for (let i = 0; i < existingMessages.length; i += 1) {
        const oldMessage = existingMessages[i];
        const oldId = messageIdFromMessage(oldMessage);
        if (!oldId || incomingIds.has(oldId) || Object.hasOwn(tombstones, oldId)) continue;

        let insertAt = -1;
        for (let j = i - 1; j >= 0; j -= 1) {
            const priorId = messageIdFromMessage(existingMessages[j]);
            if (!priorId) continue;
            const priorIndex = result.messages.findIndex(message => messageIdFromMessage(message) === priorId);
            if (priorIndex >= 0) {
                insertAt = priorIndex + 1;
                break;
            }
        }
        if (insertAt < 0) {
            for (let j = i + 1; j < existingMessages.length; j += 1) {
                const nextId = messageIdFromMessage(existingMessages[j]);
                if (!nextId) continue;
                const nextIndex = result.messages.findIndex(message => messageIdFromMessage(message) === nextId);
                if (nextIndex >= 0) {
                    insertAt = nextIndex;
                    break;
                }
            }
        }
        if (insertAt < 0) insertAt = Math.min(i, result.messages.length);
        result.messages.splice(insertAt, 0, clone(oldMessage));
        incomingIds.add(oldId);
    }

    const streamed = isObject(generation?.message) ? clone(generation.message) : null;
    const streamedId = messageIdFromMessage(streamed);
    if (streamed && typeof streamedId === 'string' && jsonSafeId(streamedId) && !streamed.is_user && !streamed.is_system) {
        const streamIndex = result.messages.findIndex(message => messageIdFromMessage(message) === streamedId);
        if (streamIndex >= 0) {
            result.messages[streamIndex] = streamed;
        } else {
            // The last cumulative frame is authoritative for this generated
            // message. Append it; never substitute it for an unrelated index.
            result.messages.push(streamed);
        }
        if (Object.hasOwn(tombstones, streamedId)) {
            delete tombstones[streamedId];
            result.metadata = writeDeltaTombstones(result.metadata, tombstones);
        }
    }

    return canonicalSnapshot(result);
}

function defaultState(scope) {
    return {
        protocol: PROTOCOL,
        schema: SCHEMA,
        scope: clone(scope),
        revision: 0,
        seeded: false,
        snapshot: { messages: [], metadata: {} },
        generation: null,
        events: [],
        nextEventId: 1,
        recentOps: [],
        createdAt: now(),
        updatedAt: now(),
    };
}

function migrateState(parsed, scope) {
    if (!isObject(parsed)) throw new Error('invalid_state_structure');
    if (parsed.protocol !== PROTOCOL || parsed.schema !== SCHEMA) {
        throw new Error(`unsupported_state_version:${parsed.protocol || '?'}/${parsed.schema || '?'}`);
    }
    if (!parsed.scope || scopeKey(parsed.scope) !== scopeKey(scope)) {
        throw new Error('state_scope_mismatch');
    }
    const state = defaultState(scope);
    state.revision = Number(parsed.revision || 0);
    // revision 0 = never seeded; revision >= 1 = established state.
    state.seeded = parsed.seeded === true || state.revision > 0;
    state.snapshot = canonicalSnapshot(parsed.snapshot || { messages: [], metadata: {} });
    // A previous process cannot resume ownership, but it can recover the last
    // accepted cumulative assistant frame stored by a heartbeat/state write.
    // Merge by stable ID; never overwrite an unrelated assistant by index.
    const checkpointMessage = isObject(parsed.generation?.message) ? clone(parsed.generation.message) : null;
    const checkpointId = messageIdFromMessage(checkpointMessage);
    if (
        checkpointMessage &&
        typeof checkpointId === 'string' &&
        jsonSafeId(checkpointId) &&
        !checkpointMessage.is_user &&
        !checkpointMessage.is_system
    ) {
        const checkpointIndex = state.snapshot.messages.findIndex(message => messageIdFromMessage(message) === checkpointId);
        if (checkpointIndex >= 0) state.snapshot.messages[checkpointIndex] = checkpointMessage;
        else state.snapshot.messages.push(checkpointMessage);
        state.snapshot = canonicalSnapshot(state.snapshot);
    }
    state.events = Array.isArray(parsed.events) ? clone(parsed.events) : [];
    state.nextEventId = Number(parsed.nextEventId || 1);
    state.recentOps = (Array.isArray(parsed.recentOps) ? parsed.recentOps : [])
        .map(entry => {
            if (typeof entry === 'string') return { id: entry, fp: null };
            if (isObject(entry) && entry.id) return { id: String(entry.id), fp: entry.fp || null };
            return null;
        })
        .filter(Boolean);
    state.createdAt = Number(parsed.createdAt || now());
    state.updatedAt = Number(parsed.updatedAt || now());
    // A generation owned by a previous server process can never be resumed.
    state.generation = null;
    return state;
}

function stateRoot(req) {
    const root = userRoot(req);
    if (!root) throw new Error('user_directory_unavailable');
    return path.join(root, PLUGIN_ID, 'state');
}

function statePath(req, scope) {
    return path.join(stateRoot(req), `${sha256(scopeKey(scope))}.json`);
}

async function ensureDir(dir) {
    await fsp.mkdir(dir, { recursive: true, mode: 0o700 });
    try { await fsp.chmod(dir, 0o700); } catch { /* best effort */ }
}

async function loadState(req, scope) {
    const key = `${userKey(req)}::${scopeKey(scope)}`;
    let entry = scopes.get(key);
    if (entry?.state) {
        entry.lastAccessed = now();
        return entry.state;
    }
    if (entry?.loading) return entry.loading;

    const loading = (async () => {
        let state = defaultState(scope);
        let recovered = false;
        try {
            const raw = await fsp.readFile(statePath(req, scope), 'utf8');
            const parsed = JSON.parse(raw);
            state = migrateState(parsed, scope);
            // A state file written by a broken intermediate version may omit
            // event history. Normalize before anything reads .length on these.
            if (!Array.isArray(state.events)) state.events = [];
            if (!Array.isArray(state.recentOps)) state.recentOps = [];
            if (parsed.generation) recovered = true;
        } catch (error) {
            if (error?.code === 'ENOENT') {
                // No base state exists. Preserve an orphan journal for recovery;
                // never apply deltas to a fabricated empty baseline.
                const quarantineSuffix = `.orphan-${Date.now()}-${crypto.randomBytes(4).toString('hex')}`;
                for (const orphanJournal of [deltaJournalPath(req, scope), generationJournalPath(req, scope)]) {
                    try {
                        await fsp.rename(orphanJournal, `${orphanJournal}${quarantineSuffix}`);
                        console.warn(`[multi-client-sync] quarantined orphan journal for ${sha256(scopeKey(scope))}: ${path.basename(orphanJournal)}${quarantineSuffix}`);
                    } catch (journalError) {
                        if (journalError?.code !== 'ENOENT') throw journalError;
                    }
                }
            } else if (
                error instanceof SyntaxError ||
                (error instanceof Error && (
                    error.message.startsWith('unsupported_state_version') ||
                    [
                        'state_scope_mismatch',
                        'invalid_state_structure',
                        'snapshot_required',
                        'snapshot_messages_required',
                        'invalid_message',
                        'message_ids_required',
                        'duplicate_message_id',
                    ].includes(error.message)
                ))
            ) {
                // Never destroy the last recoverable checkpoint on parse/schema
                // failure. Quarantine it, start an unseeded in-memory state, and
                // let normal snapshot reconciliation repair it.
                const file = statePath(req, scope);
                const suffix = `.quarantine-${Date.now()}-${crypto.randomBytes(4).toString('hex')}`;
                const quarantine = `${file}${suffix}`;
                try {
                    await fsp.rename(file, quarantine);
                    console.warn(`[multi-client-sync] quarantined incompatible state for ${sha256(scopeKey(scope))}: ${error.message}; saved as ${path.basename(quarantine)}`);
                } catch (quarantineError) {
                    if (quarantineError?.code !== 'ENOENT') {
                        // If quarantine itself fails, refuse to silently throw
                        // the only persisted data away or pretend it was safe.
                        throw quarantineError;
                    }
                    console.warn(`[multi-client-sync] no state file to quarantine for ${sha256(scopeKey(scope))}: ${error.message}`);
                }
                // The journal is meaningful only relative to its exact base state.
                // Never replay it against defaultState after the base was quarantined.
                const journalFile = deltaJournalPath(req, scope);
                try {
                    await fsp.rename(journalFile, `${journalFile}${suffix}`);
                } catch (journalError) {
                    if (journalError?.code !== 'ENOENT') throw journalError;
                }
                const streamFile = generationJournalPath(req, scope);
                try {
                    await fsp.rename(streamFile, `${streamFile}${suffix}`);
                } catch (streamError) {
                    if (streamError?.code !== 'ENOENT') throw streamError;
                }
            } else {
                throw error;
            }
        }

        // Replay deltas journaled since the last full state write. On
        // corruption: keep the valid persisted state and the checksum-valid
        // replayed prefix, discard only the journal, and bump nextEventId
        // past the observed high-water mark — clients that already consumed
        // journaled events must never see those event IDs reused.
        const journal = await replayDeltaJournal(req, scope, state);
        if (!journal.ok) {
            console.warn(`[multi-client-sync] delta journal corrupt for ${sha256(scopeKey(scope))}; compacting valid replayed prefix through event ${journal.highestEventId}`);
            state.nextEventId = Math.max(state.nextEventId, journal.highestEventId + 1000);
            // persistState atomically saves the checksum-valid replayed prefix
            // and clears the journal only after the replacement state is durable.
            // If persistence fails, loading fails and the journal remains intact.
            await persistState(req, scope, state);
            if (streamCheckpoint?.recovered) {
                if (streamCheckpoint.corrupt) {
                    // The last valid frame has been merged and persisted. Retain the
                    // damaged journal for diagnosis instead of destroying evidence.
                    await quarantineGenerationJournal(req, scope, 'corrupt');
                } else {
                    await clearGenerationJournal(req, scope);
                }
            }
        }

        const streamCheckpoint = await replayGenerationJournal(req, scope, state);
        if (streamCheckpoint.recovered) recovered = true;
        if (streamCheckpoint.terminal) await clearGenerationJournal(req, scope);
        if (streamCheckpoint.orphan) await quarantineGenerationJournal(req, scope, 'orphan');

        state.updatedAt = now();
        const freshEntry = scopes.get(key) || {};
        freshEntry.state = state;
        freshEntry.loading = null;
        freshEntry.lastAccessed = now();
        scopes.set(key, freshEntry);

        if (recovered) {
            const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null }, { id: state.nextEventId });
            commitPreparedEvents(state, [recovery]);

}
        return state;
    })();

    scopes.set(key, { ...(entry || {}), loading });

    loading.catch(() => {
        const current = scopes.get(key);
        if (current?.loading === loading) {
            current.loading = null;
            scopes.set(key, current);
        }
    });

    return loading;
}

// Direct projection: NO full-state clone. The snapshot/scope are referenced —
// JSON serialization never mutates them. The durable generation is
// metadata-only; the live message is transient and must never hit disk.
async function persistState(req, scope, state, { fsync = LIMITS.fsyncState } = {}) {
    const file = statePath(req, scope);
    await ensureDir(path.dirname(file));

    const projected = {
        protocol: state.protocol,
        schema: state.schema,
        scope: state.scope,
        revision: state.revision,
        seeded: state.seeded === true || Number(state.revision || 0) > 0,
        snapshot: state.snapshot,
        // Persist the latest accepted cumulative stream message on durable state
        // writes (heartbeats/start/terminal), not on every token. This bounds I/O
        // while keeping a recoverable checkpoint if the process restarts mid-run.
        generation: state.generation ? generationPublic(state.generation, true) : null,
        nextEventId: state.nextEventId,
        recentOps: state.recentOps,
        createdAt: state.createdAt,
        updatedAt: now(),
    };
    // pruneEventHistory mutates in place and returns undefined — build a
    // pruned COPY for the projected payload (assigning its return value
    // would silently null out the event history).
    projected.events = Array.isArray(state.events) ? state.events.slice() : [];
    pruneEventHistory(projected);

    const payload = JSON.stringify(projected);
    if (Buffer.byteLength(payload, 'utf8') > LIMITS.maxSnapshotBytes + 2 * 1024 * 1024) {
        throw Object.assign(new Error('state_too_large'), { code: 'state_too_large' });
    }

    const tmp = `${file}.${process.pid}.${crypto.randomBytes(6).toString('hex')}.tmp`;
    try {
        await fsp.writeFile(tmp, payload, { mode: 0o600 });
        if (fsync) {
            const fd = await fsp.open(tmp, 'r+');
            try { await fd.sync(); } finally { await fd.close(); }
        }
        await fsp.rename(tmp, file);
        if (fsync) {
            let dirFd = null;
            try { dirFd = await fsp.open(path.dirname(file), 'r'); await dirFd.sync(); }
            catch { /* directory fsync not supported everywhere */ }
            finally { if (dirFd) await dirFd.close().catch(() => {}); }
        }
        try { await fsp.chmod(file, 0o600); } catch { /* best effort */ }

        // The compacted state file now contains everything the delta journal
        // held. Never let journal cleanup fail an already-successful commit.
        await clearDeltaJournal(req, scope);
    } catch (error) {
        try { await fsp.unlink(tmp); } catch { /* ignore */ }
        throw error;
    }

    // Mirror compaction/pruning onto in-memory state so the cache matches disk
    // and long generations cannot grow memory without bound.
    state.updatedAt = projected.updatedAt;
    if (!Array.isArray(state.events)) state.events = [];
    pruneEventHistory(state);
}

function pruneEventHistory(state) {
    if (!Array.isArray(state.events)) return;
    let total = 0;
    for (const event of state.events) total += utf8ByteLength(event);
    while (state.events.length > 0 && (total > LIMITS.maxEventHistoryBytes || state.events.length > LIMITS.maxEvents)) {
        const removed = state.events.shift();
        total -= utf8ByteLength(removed);
    }
}

function lockFor(key) {
    const previous = userLocks.get(key) || Promise.resolve();
    let release;
    const current = new Promise(resolve => { release = resolve; });
    const chain = previous.catch(() => {}).then(() => current);

    const cleanup = () => {
        if (userLocks.get(key) === chain) userLocks.delete(key);
    };
    chain.then(cleanup, cleanup);

    userLocks.set(key, chain);
    return previous.catch(() => {}).then(() => release);
}

// Transaction model: one API mutation may contain multiple commit points
// (recovery event, then the main mutation). Rollback restores to the LAST
// successful commit, not to the initial state — otherwise a failed second
// persist after a successful first one would leave un-persisted mutations in
// memory. The generation object is snapshotted BY VALUE: handlers mutate it
// in place, so a reference would roll back to the already-mutated object.
function beginStateTransaction(state) {
    const snap = {
        revision: state.revision,
        nextEventId: state.nextEventId,
        eventsLength: state.events.length,
        recentOpsLength: state.recentOps.length,
        snapshot: state.snapshot,
        generation: state.generation ? clone(state.generation) : null,
    };
    return { initial: snap, commitPoint: snap, persisted: false };
}

function markPersisted(state, tx) {
    tx.persisted = true;
    tx.commitPoint = {
        revision: state.revision,
        nextEventId: state.nextEventId,
        eventsLength: state.events.length,
        recentOpsLength: state.recentOps.length,
        snapshot: state.snapshot,
        generation: state.generation ? clone(state.generation) : null,
    };
}

function rollbackTransaction(state, tx) {
    const p = tx.persisted ? tx.commitPoint : tx.initial;
    state.revision = p.revision;
    state.nextEventId = p.nextEventId;
    state.events.length = p.eventsLength;
    state.recentOps.length = p.recentOpsLength;
    state.snapshot = p.snapshot;
    state.generation = p.generation;
}

async function withLock(req, scope, fn) {
    const release = await lockFor(`${userKey(req)}::${scopeKey(scope)}`);
    let state = null;
    let tx = null;
    try {
        state = await loadState(req, scope);
        tx = beginStateTransaction(state);
        const result = await fn(state, tx);
        return result;
    } catch (error) {
        if (state && tx) rollbackTransaction(state, tx);
        throw error;
    } finally {
        release();
    }
}

// Idempotency entries carry an operation fingerprint: a retried opId with the
// SAME payload is a duplicate; the same opId with a DIFFERENT payload is an
// op_id_reuse conflict, never a silent discard.
function rememberOp(state, opId, fp = null) {
    if (!opId) return;
    state.recentOps.push({ id: String(opId), fp: fp || null });
    if (state.recentOps.length > LIMITS.maxRecentOps) {
        state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
    }
}

function findOp(state, opId) {
    if (!opId) return null;
    for (let i = state.recentOps.length - 1; i >= 0; i -= 1) {
        const entry = state.recentOps[i];
        if (typeof entry === 'string') {
            if (entry === opId) return { id: entry, fp: null };
            continue;
        }
        if (entry?.id === opId) return entry;
    }
    return null;
}

function duplicateOpResponse(res, state, prior, fp, compact = false) {
    if (prior.fp && fp && prior.fp !== fp) {
        return res.status(409).json({ ok: false, error: 'op_id_reuse' });
    }
    return res.json({ ok: true, state: compact ? publicStateCompact(state) : publicState(state), duplicate: true });
}

function revisionError(state) {
    return {
        ok: false,
        error: 'revision_conflict',
        revision: state.revision,
        snapshot: clone(state.snapshot),
        generation: generationPublic(state.generation, false),
    };
}

// ---------------------------------------------------------------------------
// Event preparation / chunking
//
// prepareEvent never mutates state. nextEventId only advances in
// commitPreparedEvents. For generation_stream, the LIVE frames carry the full
// message (SSE delivery needs it) but the durable storedEvent is compacted —
// stream messages never sit in event history, in memory or on disk.
// ---------------------------------------------------------------------------

function prepareEvent(state, logicalEvent, { id = null, opId = null, transferId = null, fp = null } = {}) {
    const eventId = id ?? state.nextEventId;
    const at = now();

    const fullEvent = {
        ...clone(logicalEvent),
        id: eventId,
        at,
        eventVersion: 1,
    };

    const serialized = jsonToUtf8Bytes(fullEvent);
    const totalBytes = serialized.length;

    const durableEvent = logicalEvent.type === 'generation_stream'
        ? { ...fullEvent, message: undefined, compacted: true }
        : fullEvent;

    if (totalBytes <= LIMITS.maxEventBytes - 256) {
        return {
            kind: 'normal',
            id: eventId,
            at,
            opId,
            fp,
            storedEvent: durableEvent,
            frames: [fullEvent],
            totalBytes,
            transferId,
        };
    }

    if (totalBytes > LIMITS.maxChunkAssemblyBytes) {
        throw new Error('event_too_large');
    }

    const effectiveTransferId = transferId || newTransferId();
    const eventSha256 = sha256Bytes(serialized);
    const chunkPayloadLimit = LIMITS.chunkPayloadBytes;
    const chunkCount = Math.ceil(totalBytes / chunkPayloadLimit);
    const frames = [];

    for (let i = 0; i < chunkCount; i += 1) {
        const start = i * chunkPayloadLimit;
        const end = Math.min(start + chunkPayloadLimit, totalBytes);
        const chunkBytes = serialized.subarray(start, end);
        frames.push({
            type: 'event_chunk',
            transferVersion: 1,
            logicalEventId: eventId,
            transferId: effectiveTransferId,
            logicalType: logicalEvent.type,
            chunkIndex: i,
            chunkCount,
            totalBytes,
            chunkBytes: chunkBytes.length,
            eventSha256,
            chunkSha256: sha256Bytes(chunkBytes),
            encoding: 'base64',
            payload: base64Encode(chunkBytes),
        });
    }

    const compactMarker = {
        id: eventId,
        at,
        type: 'event_chunked',
        logicalType: logicalEvent.type,
        totalBytes,
        chunkCount,
        eventSha256,
        replayable: false,
    };

    return {
        kind: 'chunked',
        id: eventId,
        at,
        opId,
        fp,
        storedEvent: compactMarker,
        frames,
        totalBytes,
        transferId: effectiveTransferId,
    };
}

function prepareEvents(state, logicalEvents) {
    let nextId = state.nextEventId;
    const prepared = [];
    for (const { event, opId, transferId, fp } of logicalEvents) {
        prepared.push(prepareEvent(state, event, { id: nextId++, opId, transferId, fp }));
    }
    return prepared;
}

function commitPreparedEvents(state, preparedEvents) {
    if (!Array.isArray(state.events)) state.events = [];
    for (const prepared of preparedEvents) {
        state.events.push(clone(prepared.storedEvent));
        state.nextEventId = Math.max(state.nextEventId, prepared.id + 1);
        if (prepared.opId) rememberOp(state, prepared.opId, prepared.fp);
    }
}

function publishPreparedEvent(req, scope, prepared) {
    const set = subscribers.get(`${userKey(req)}::${scopeKey(scope)}`) || new Map();
    const isDelta = prepared?.storedEvent?.type === 'snapshot_delta';

    for (const sub of set.values()) {
        // Member-only placeholders (join without SSE, or a closed SSE
        // connection kept for membership) are not deliverable targets.
        if (sub.closed || !sub.outboundQueue) continue;

        // Old clients do not understand snapshot_delta. Never let them
        // silently miss the mutation: force an authoritative resync.
        if (isDelta && !sub.supportsDelta) {
            try {
                enqueueSseFrame(sub, { type: 'resync_required' }, null);
            } catch {
                closeSubscriber(sub, 'delta_compatibility_failure');
            }
            continue;
        }

        for (let i = 0; i < prepared.frames.length; i += 1) {
            // Only the FINAL frame of a transfer advances the native SSE
            // cursor. Intermediate chunks carry no id, so a mid-transfer
            // disconnect reconnects with Last-Event-ID = the previous logical
            // event; replay then hits the event_chunked marker and forces a
            // clean resync instead of silently skipping the remainder.
            const sseId = prepared.id > 0 && i === prepared.frames.length - 1
                ? prepared.id
                : null;
            try {
                enqueueSseFrame(sub, prepared.frames[i], sseId);
            } catch {
                closeSubscriber(sub, 'enqueue_error');
                break;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SSE framing / subscriber backpressure
// ---------------------------------------------------------------------------

function sendSseFrame(res, event, id = null) {
    const payload = JSON.stringify(event);
    const frameSize = Buffer.byteLength(payload, 'utf8') + (id != null ? String(id).length + 8 : 0) + 32;
    if (frameSize > LIMITS.maxEventBytes) {
        throw new Error('frame_too_large');
    }
    let out = '';
    if (id != null) out += `id: ${id}\n`;
    out += `event: ${String(event.type || 'message')}\n`;
    out += `data: ${payload}\n\n`;
    const ok = res.write(out);
    // Flush every SSE frame immediately; the transport must not buffer
    // latency-sensitive generation events.
    if (typeof res.flush === 'function') {
        res.flush();
    }
    return ok;
}

function enqueueSseFrame(sub, frame, logicalEventId) {
    if (sub.closed || !sub.outboundQueue) return;

    const type = String(frame?.type || '');
    const generationId = String(frame?.generationId || frame?.generation?.generationId || '');
    const coalescibleStream = type === 'generation_stream' && !!generationId && frame?.cumulative === true;
    const terminalOrStop = [
        'generation_stop_requested', 'generation_terminal', 'generation_stopped', 'generation_completed',
    ].includes(type);

    // Cumulative stream frames supersede queued frames for the same generation. This bounds
    // memory and keeps the remote tab close to the live edge when the client/socket is slow.
    // Stop/terminal is authoritative, so discard queued transient stream frames for that generation;
    // the terminal checkpoint carries the final durable content.
    if ((coalescibleStream || terminalOrStop) && generationId) {
        for (let i = sub.outboundQueue.length - 1; i >= 0; i -= 1) {
            const queued = sub.outboundQueue[i];
            const queuedType = String(queued?.frame?.type || '');
            const queuedGenerationId = String(queued?.frame?.generationId || queued?.frame?.generation?.generationId || '');
            if (queuedGenerationId !== generationId || queuedType !== 'generation_stream') continue;
            const removed = sub.outboundQueue.splice(i, 1)[0];
            sub.outboundBytes = Math.max(0, sub.outboundBytes - utf8ByteLength(removed.frame));
        }
    }

    // Never duplicate a queued cumulative frame, but preserve ordering around durable events.
    const item = { frame, logicalEventId };
    sub.outboundQueue.push(item);
    sub.outboundBytes += utf8ByteLength(frame);
    if (sub.outboundBytes > LIMITS.maxBufferedSseBytes) {
        closeSubscriber(sub, 'buffer_overflow');
        return;
    }
    if (sub.replaying) return;
    flushSubscriberQueue(sub);
}

// Once res.write(frame) returns false, that frame has ALREADY been accepted
// by the writable stream — it must never be written again. Frames are
// therefore dequeued BEFORE the write; a false return only pauses the loop
// until the drain event resumes it.
function flushSubscriberQueue(sub) {
    if (sub.closed || sub.replaying) return;
    while (sub.outboundQueue.length > 0) {
        const item = sub.outboundQueue.shift();
        let ok;
        try {
            ok = sendSseFrame(sub.res, item.frame, item.logicalEventId);
        } catch {
            closeSubscriber(sub, 'send_error');
            return;
        }
        sub.outboundBytes = Math.max(0, sub.outboundBytes - utf8ByteLength(item.frame));
        if (!ok) {
            if (!sub.waitingForDrain) sub.waitingForDrain = true;
            return; // 'drain' handler resumes flushing
        }
    }
}

function closeSubscriber(sub, reason) {
    if (!sub || sub.closed) return;
    sub.closed = true;
    sub.waitingForDrain = false;
    if (sub.outboundQueue) {
        sub.outboundQueue.length = 0;
        sub.outboundBytes = 0;
    }
    try { sub.res?.end(); } catch { /* ignore */ }
    void reason;
}

function createSubscriber(res, member, { supportsDelta = false } = {}) {
    const sub = {
        res,
        member,
        supportsDelta,
        replaying: true,
        outboundQueue: [],
        outboundBytes: 0,
        waitingForDrain: false,
        closed: false,
    };
    sub.res.on('drain', () => {
        if (sub.closed) return;
        sub.waitingForDrain = false;
        flushSubscriberQueue(sub);
    });
    return sub;
}

// ---------------------------------------------------------------------------
// Public state / generation
//
// publicState: full authoritative checkpoint (snapshot included) — /state,
// /join, snapshot/claim/terminal success, and all 409 conflict bodies.
// publicStateCompact: no snapshot — the hot generation paths (heartbeat,
// started, stream, stop) and delta success must never clone/serialize a
// 12 MB chat.
// ---------------------------------------------------------------------------

function publicState(state) {
    return {
        protocol: state.protocol,
        schema: state.schema,
        scope: clone(state.scope),
        revision: state.revision,
        snapshot: state.snapshot,
        generation: generationPublic(state.generation, false),
        updatedAt: state.updatedAt,
        lastEventId: state.nextEventId - 1,
    };
}

function publicStateCompact(state) {
    return {
        protocol: state.protocol,
        schema: state.schema,
        scope: clone(state.scope),
        revision: state.revision,
        generation: generationPublic(state.generation, false),
        updatedAt: state.updatedAt,
        lastEventId: state.nextEventId - 1,
    };
}

function generationPublic(g, includeMessage = true) {
    if (!g) return null;
    const value = {
        generationId: g.generationId,
        clientId: g.clientId,
        deviceId: g.deviceId,
        phase: g.phase,
        generationType: g.generationType,
        startedAt: g.startedAt,
        leaseUntil: g.leaseUntil,
        seq: g.seq,
        messageId: g.messageId || null,
        messageIndex: Number.isInteger(g.messageIndex) ? g.messageIndex : null,
        stopRequested: !!g.stopRequested,
    };
    if (includeMessage) value.message = g.message ? clone(g.message) : null;
    return value;
}

function expireGeneration(state) {
    if (!state.generation) return false;
    const g = state.generation;
    const t = now();
    if (t - g.claimedAt > LIMITS.generationMaxMs || t > g.leaseUntil) {
        state.generation = null;
        state.updatedAt = t;
        return true;
    }
    return false;
}

function makeGeneration(body, serverInstanceIdValue) {
    const generationId = String(body.generationId || crypto.randomUUID());
    return {
        generationId,
        clientId: String(body.clientId),
        deviceId: String(body.deviceId),
        generationType: String(body.generationType || 'normal'),
        phase: 'claimed',
        claimedAt: now(),
        startedAt: null,
        lastHeartbeat: now(),
        leaseUntil: now() + LIMITS.generationLeaseMs,
        seq: 0,
        messageId: null,
        messageIndex: null,
        message: null,
        stopRequested: false,
        serverInstanceId: serverInstanceIdValue,
    };
}

function generationOwner(g, body) {
    return !!g &&
        g.clientId === String(body.clientId) &&
        g.deviceId === String(body.deviceId) &&
        g.generationId === String(body.generationId);
}

function publicMembers(req, scope) {
    return activeMembers(req, scope).map(member => ({
        clientId: member.clientId,
        deviceId: member.deviceId,
        lastSeenAt: member.lastSeenAt,
    }));
}

// ---------------------------------------------------------------------------
// Scope cache limits / membership
// ---------------------------------------------------------------------------

function isScopeLocked(key) { return userLocks.has(key); }

function isScopeActive(key) {
    const set = subscribers.get(key);
    if (!set) return false;
    for (const entry of set.values()) {
        if (entry?.res && !entry.closed) return true;
    }
    return false;
}

function isScopeLoading(key) {
    const entry = scopes.get(key);
    return !!entry?.loading;
}

function evictScopeCache(key) {
    if (!scopes.has(key)) return true;
    if (isScopeLocked(key)) return false;
    if (isScopeActive(key)) return false;
    if (isScopeLoading(key)) return false;
    scopes.delete(key);
    return true;
}

function enforceScopeCacheLimit(req) {
    const prefix = `${userKey(req)}::`;
    const entries = [];
    for (const [key, value] of scopes.entries()) {
        if (!key.startsWith(prefix)) continue;
        entries.push({ key, lastAccessed: value.lastAccessed || 0 });
    }
    if (entries.length <= LIMITS.maxScopesPerUser) return;
    entries.sort((a, b) => a.lastAccessed - b.lastAccessed);
    let toEvict = entries.length - LIMITS.maxScopesPerUser;
    for (const { key } of entries) {
        if (toEvict <= 0) break;
        if (evictScopeCache(key)) toEvict -= 1;
    }
}

function pruneExpiredMembers(skey) {
    const map = subscribers.get(skey);
    if (!map) return null;
    const cutoff = now() - LIMITS.memberTtlMs;
    for (const [clientId, entry] of map.entries()) {
        if (!entry?.member || Number(entry.member.lastSeenAt || 0) < cutoff) {
            if (entry?.res && !entry.closed) {
                try { entry.res.end(); } catch { /* ignore */ }
            }
            map.delete(clientId);
        }
    }
    if (map.size === 0) {
        subscribers.delete(skey);
        return null;
    }
    return map;
}

function activeMembers(req, scope) {
    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    const map = pruneExpiredMembers(skey);
    if (!map) return [];
    return [...map.values()].map(x => x.member);
}

function isMember(req, scope, clientId, deviceId) {
    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    const map = pruneExpiredMembers(skey);
    const member = map?.get(clientId)?.member;
    if (!member) return false;
    if (member.deviceId !== deviceId) return false;
    return now() - member.lastSeenAt <= LIMITS.memberTtlMs;
}

function requireMember(req, res, scope, body) {
    const clientId = String(body?.clientId || '');
    const deviceId = String(body?.deviceId || '');
    if (!jsonSafeId(clientId) || !jsonSafeId(deviceId)) {
        res.status(400).json({ ok: false, error: 'invalid_client' });
        return null;
    }
    if (!isMember(req, scope, clientId, deviceId)) {
        res.status(403).json({ ok: false, error: 'not_member' });
        return null;
    }
    return { clientId, deviceId };
}

// ---------------------------------------------------------------------------
// Delta fast path
// ---------------------------------------------------------------------------

const MCS_META_KEY = 'multi_client_sync';
const forbiddenKeys = new Set(['__proto__', 'prototype', 'constructor']);

// Null-prototype containers: message IDs are arbitrary attacker-adjacent
// strings and must never resolve through Object.prototype.
function snapshotDropsUnexplainedMessages(existingSnapshot, incomingSnapshot) {
    if (!Array.isArray(existingSnapshot?.messages) || !Array.isArray(incomingSnapshot?.messages)) {
        return true;
    }

    const incomingIds = new Set();
    for (const message of incomingSnapshot.messages) {
        const id = messageIdFromMessage(message);
        if (typeof id !== 'string' || !jsonSafeId(id)) return true;
        incomingIds.add(id);
    }

    const tombstones = readDeltaTombstones(incomingSnapshot.metadata);
    for (const message of existingSnapshot.messages) {
        const id = messageIdFromMessage(message);
        if (typeof id !== 'string' || !jsonSafeId(id)) return true;
        if (!incomingIds.has(id) && !Object.hasOwn(tombstones, id)) return true;
    }

    return false;
}

function readDeltaTombstones(metadata) {
    const meta = metadata?.[MCS_META_KEY];
    const tomb = meta?.tombstones;
    if (!tomb || typeof tomb !== 'object' || Array.isArray(tomb)) return Object.create(null);
    const out = Object.create(null);
    for (const [id, value] of Object.entries(tomb)) {
        if (forbiddenKeys.has(id)) continue;
        const ts = Number(value);
        if (Number.isFinite(ts) && ts > 0) out[id] = ts;
    }
    return out;
}

function writeDeltaTombstones(metadata, tombstones) {
    if (!Object.keys(tombstones).length) {
        if (metadata?.[MCS_META_KEY]?.tombstones) {
            const next = clone(metadata);
            if (next[MCS_META_KEY]) {
                delete next[MCS_META_KEY].tombstones;
                if (Object.keys(next[MCS_META_KEY]).length === 0) delete next[MCS_META_KEY];
            }
            return next;
        }
        return metadata;
    }
    const next = clone(metadata || {});
    const bucket = isObject(next[MCS_META_KEY]) ? next[MCS_META_KEY] : {};
    bucket.tombstones = JSON.parse(JSON.stringify(tombstones));
    next[MCS_META_KEY] = bucket;
    return next;
}

// Shared operation model: server and client project deltas with identical
// semantics (anchored inserts, timestamped deletes, explicit moves).
function applyDeltaToSnapshot(baseSnapshot, ops) {
    const messages = Array.isArray(baseSnapshot?.messages) ? baseSnapshot.messages.slice() : [];
    let metadata = baseSnapshot?.metadata || {};
    const tombstones = readDeltaTombstones(metadata);
    let metadataChanged = false;
    const ensureMetadataCopy = () => {
        if (metadataChanged) return;
        metadata = clone(metadata);
        metadataChanged = true;
    };
    const reindex = () => {
        const map = new Map();
        for (let i = 0; i < messages.length; i += 1) {
            const id = messages[i]?.extra?.multi_client_sync?.messageId;
            if (jsonSafeId(String(id || ''))) map.set(String(id), i);
        }
        return map;
    };
    let indexById = reindex();

    for (const op of ops) {
        if (op.op === 'delete') {
            const id = String(op.messageId);
            const deletedAt = Number(op.deletedAt || now());
            if (!Number.isFinite(deletedAt) || deletedAt <= 0) throw new Error('invalid_delete_timestamp');
            const currentIndex = indexById.get(id);
            if (currentIndex !== undefined) {
                messages.splice(currentIndex, 1);
                indexById = reindex();
            }
            ensureMetadataCopy();
            if (!Object.hasOwn(tombstones, id) || deletedAt > tombstones[id]) tombstones[id] = deletedAt;
            continue;
        }

        if (op.op === 'upsert') {
            const msg = clone(op.message);
            const id = String(msg?.extra?.multi_client_sync?.messageId || '');
            const modifiedAt = Number(op.modifiedAt || now());
            if (!jsonSafeId(id)) throw new Error('message_ids_required');
            if (!Number.isFinite(modifiedAt) || modifiedAt <= 0) throw new Error('invalid_modified_timestamp');
            if (Object.hasOwn(tombstones, id) && modifiedAt <= tombstones[id]) throw new Error('delta_stale_message');

            const currentIndex = indexById.get(id);
            if (currentIndex !== undefined) {
                messages[currentIndex] = msg;
            } else {
                const afterId = op.afterMessageId == null ? null : String(op.afterMessageId);
                let insertAt = 0;
                if (afterId) {
                    const afterIndex = indexById.get(afterId);
                    if (afterIndex === undefined) throw new Error('delta_anchor_missing');
                    insertAt = afterIndex + 1;
                }
                messages.splice(insertAt, 0, msg);
                indexById = reindex();
            }
            if (Object.hasOwn(tombstones, id)) {
                ensureMetadataCopy();
                delete tombstones[id];
            }
            continue;
        }

        if (op.op === 'move') {
            const id = String(op.messageId);
            const currentIndex = indexById.get(id);
            if (currentIndex === undefined) throw new Error('delta_move_target_missing');
            const afterId = op.afterMessageId == null ? null : String(op.afterMessageId);
            if (afterId === id) throw new Error('delta_move_self');
            const moved = messages[currentIndex];
            messages.splice(currentIndex, 1);
            indexById = reindex();
            let insertAt = 0;
            if (afterId) {
                const afterIndex = indexById.get(afterId);
                if (afterIndex === undefined) throw new Error('delta_move_anchor_missing');
                insertAt = afterIndex + 1;
            }
            messages.splice(insertAt, 0, moved);
            indexById = reindex();
            continue;
        }

        throw new Error('invalid_delta_operation');
    }

    if (metadataChanged) metadata = writeDeltaTombstones(metadata, tombstones);

    const ids = new Set();
    for (const message of messages) {
        const id = String(message?.extra?.multi_client_sync?.messageId || '');
        if (!jsonSafeId(id)) throw new Error('message_ids_required');
        if (ids.has(id)) throw new Error('duplicate_message_id');
        ids.add(id);
    }

    return { messages, metadata };
}

// --- delta journal: small durable appends instead of full state rewrites ---

function deltaJournalPath(req, scope) {
    return path.join(stateRoot(req), `${sha256(scopeKey(scope))}.delta.ndjson`);
}

function generationJournalPath(req, scope) {
    return path.join(stateRoot(req), `${sha256(scopeKey(scope))}.generation.ndjson`);
}

async function clearGenerationJournal(req, scope) {
    try {
        await fsp.unlink(generationJournalPath(req, scope));
    } catch (error) {
        if (error?.code !== 'ENOENT') {
            console.warn('[multi-client-sync] failed to clear generation journal:', error?.message || error);
        }
    }
}

async function quarantineGenerationJournal(req, scope, reason = 'corrupt') {
    const file = generationJournalPath(req, scope);
    const target = `${file}.${reason}-${Date.now()}-${crypto.randomBytes(4).toString('hex')}`;
    try {
        await fsp.rename(file, target);
        console.warn(`[multi-client-sync] quarantined generation journal for ${sha256(scopeKey(scope))}: ${path.basename(target)}`);
        return true;
    } catch (error) {
        if (error?.code === 'ENOENT') return false;
        throw error;
    }
}

async function appendGenerationCheckpoint(req, scope, generation, message, seq, messageIndex) {
    const generationId = String(generation?.generationId || '');
    const messageId = messageIdFromMessage(message);
    if (
        !jsonSafeId(generationId) ||
        !jsonSafeId(messageId) ||
        !isObject(message) ||
        !Number.isInteger(seq) || seq < 1
    ) {
        throw new Error('invalid_generation_checkpoint');
    }

    const file = generationJournalPath(req, scope);
    await ensureDir(path.dirname(file));
    const core = {
        version: 1,
        scopeKey: scopeKey(scope),
        generationId,
        seq,
        messageId,
        messageIndex: Number.isInteger(messageIndex) ? messageIndex : null,
        message: clone(message),
        at: now(),
    };
    const recordSha256 = sha256Bytes(Buffer.from(JSON.stringify(core), 'utf8'));
    const payload = `${JSON.stringify({ ...core, recordSha256 })}\n`;

    // A stream POST is not acknowledged as accepted until this compact record is
    // durable. Do not fsync the entire state file per frame.
    const handle = await fsp.open(file, 'a', 0o600);
    let originalSize = 0;
    try {
        originalSize = (await handle.stat()).size;
        await handle.writeFile(payload, 'utf8');
        await handle.sync();
    } catch (error) {
        // If this process remains alive after a write/fsync error, roll back a
        // partial tail before any retry can append another record after it.
        try {
            await handle.truncate(originalSize);
            await handle.sync();
        } catch (truncateError) {
            console.warn('[multi-client-sync] failed to roll back partial generation-journal append:', truncateError?.message || truncateError);
        }
        throw error;
    } finally {
        await handle.close();
    }
}

async function replayGenerationJournal(req, scope, state) {
    const file = generationJournalPath(req, scope);
    let raw;
    try {
        raw = await fsp.readFile(file, 'utf8');
    } catch (error) {
        if (error?.code === 'ENOENT') return { recovered: false, corrupt: false };
        throw error;
    }

    let latest = null;
    let corrupt = false;
    const lines = raw.split('\n');
    for (const line of lines) {
        if (!line.trim()) continue;
        let record;
        try {
            record = JSON.parse(line);
        } catch {
            corrupt = true;
            break;
        }
        const { recordSha256, ...core } = record || {};
        const id = messageIdFromMessage(core.message);
        const valid =
            core.version === 1 &&
            core.scopeKey === scopeKey(scope) &&
            jsonSafeId(core.generationId) &&
            Number.isInteger(core.seq) && core.seq >= 1 &&
            jsonSafeId(core.messageId) &&
            id === core.messageId &&
            isObject(core.message) &&
            typeof recordSha256 === 'string' &&
            recordSha256 === sha256Bytes(Buffer.from(JSON.stringify(core), 'utf8'));
        if (!valid) {
            corrupt = true;
            break;
        }
        latest = core;
    }

    if (!latest) return { recovered: false, corrupt, orphan: true };

    const terminalWasCommitted = (Array.isArray(state.events) ? state.events : []).some(event =>
        event?.type === 'generation_terminal' &&
        String(event?.generation?.generationId || event?.generationId || '') === latest.generationId
    );
    if (terminalWasCommitted) return { recovered: false, corrupt, terminal: true };

    if (!state.seeded && Number(state.revision || 0) === 0) {
        return { recovered: false, corrupt, orphan: true };
    }

    const snapshot = canonicalSnapshot(state.snapshot || { messages: [], metadata: {} });
    const existingIndex = snapshot.messages.findIndex(message => messageIdFromMessage(message) === latest.messageId);
    if (existingIndex >= 0) {
        snapshot.messages[existingIndex] = clone(latest.message);
    } else if (!latest.message.is_user && !latest.message.is_system) {
        // Never replace an unrelated message by index during recovery.
        snapshot.messages.push(clone(latest.message));
    }
    state.snapshot = canonicalSnapshot(snapshot);
    state.seeded = true;
    state.updatedAt = now();

    // A valid unterminated last record is repaired before any subsequent append.
    if (!corrupt && raw && !raw.endsWith('\n')) {
        await fsp.appendFile(file, '\n', { mode: 0o600 });
    }
    return { recovered: true, corrupt, generationId: latest.generationId, seq: latest.seq };
}

async function appendDeltaJournal(req, scope, prepared) {
    const file = deltaJournalPath(req, scope);
    await ensureDir(path.dirname(file));

    const recordCore = { version: 1, id: prepared.id, opId: prepared.opId || null, event: prepared.storedEvent };
    const record = { ...recordCore, recordSha256: sha256Bytes(Buffer.from(JSON.stringify(recordCore), 'utf8')) };
    const payload = `${JSON.stringify(record)}\n`;

    await fsp.appendFile(file, payload, { mode: 0o600 });
    if (LIMITS.fsyncState) {
        const fd = await fsp.open(file, 'r+');
        try { await fd.sync(); } finally { await fd.close(); }
    }

    const stat = await fsp.stat(file);
    return stat.size;
}

async function clearDeltaJournal(req, scope) {
    try {
        await fsp.unlink(deltaJournalPath(req, scope));
    } catch (error) {
        if (error?.code !== 'ENOENT') console.warn('[multi-client-sync] failed to clear delta journal:', error?.message || error);
    }
}

async function replayDeltaJournal(req, scope, state) {
    let raw;
    try {
        raw = await fsp.readFile(deltaJournalPath(req, scope), 'utf8');
    } catch (error) {
        if (error?.code === 'ENOENT') return { ok: true, highestEventId: 0 };
        throw error;
    }

    const lines = raw.split('\n');
    let replayed = false;
    let highestEventId = 0;

    for (let i = 0; i < lines.length; i += 1) {
        const line = lines[i];
        if (!line.trim()) continue;

        let record;
        try {
            record = JSON.parse(line);
        } catch (error) {
            // Truncated final append is discardable; mid-file corruption is not.
            if (i === lines.length - 1) {
                console.warn('[multi-client-sync] truncating incomplete final delta journal record');
                const lastNewline = raw.lastIndexOf('\n');
                const validPrefix = lastNewline >= 0 ? raw.slice(0, lastNewline + 1) : '';
                await fsp.truncate(deltaJournalPath(req, scope), Buffer.byteLength(validPrefix, 'utf8'));
                break;
            }
            return { ok: false, highestEventId };
        }

        if (
            !isObject(record) ||
            record.version !== 1 ||
            !isObject(record.event) ||
            record.event.type !== 'snapshot_delta' ||
            typeof record.recordSha256 !== 'string' ||
            !/^[a-f0-9]{64}$/.test(record.recordSha256)
        ) {
            return { ok: false, highestEventId };
        }

        const { recordSha256, ...recordCore } = record;
        if (recordSha256 !== sha256Bytes(Buffer.from(JSON.stringify(recordCore), 'utf8'))) {
            return { ok: false, highestEventId };
        }

        const event = record.event;
        const eventId = Number(event.id);
        highestEventId = Math.max(highestEventId, Number.isFinite(eventId) ? eventId : 0);
        if (eventId < state.nextEventId) continue; // already compacted
        if (eventId !== state.nextEventId) return { ok: false, highestEventId };
        if (Number(event.baseRevision) !== Number(state.revision)) return { ok: false, highestEventId };

        state.snapshot = applyDeltaToSnapshot(state.snapshot, event.ops);
        state.revision = Number(event.revision);
        state.updatedAt = Number(event.at || now());
        if (!Array.isArray(state.events)) state.events = [];
        state.events.push(clone(event));
        state.nextEventId = eventId + 1;
        highestEventId = eventId;
        if (record.opId) rememberOp(state, record.opId);
        replayed = true;
    }

    // appendDeltaJournal always appends newline-delimited records. Repair a
    // valid final JSON record missing its newline so the next append cannot
    // concatenate two records into one corrupt line.
    const repairedRaw = await fsp.readFile(deltaJournalPath(req, scope), 'utf8').catch(() => '');
    if (repairedRaw && !repairedRaw.endsWith('\n')) {
        await fsp.appendFile(deltaJournalPath(req, scope), '\n', { mode: 0o600 });
    }
    if (replayed) pruneEventHistory(state);
    return { ok: true, highestEventId };
}

async function handleDelta(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    const opId = String(body.opId || '');
    if (!jsonSafeId(opId)) return res.status(400).json({ ok: false, error: 'invalid_op_id' });

    const ops = Array.isArray(body.ops) ? body.ops : null;
    // Server-side validation is authoritative: never trust the client's
    // DELTA_MAX_OPS / DELTA_MAX_BYTES for safety.
    if (!ops || ops.length === 0 || ops.length > LIMITS.maxDeltaOps) {
        return res.status(400).json({ ok: false, error: 'invalid_ops' });
    }

    try {
        const seenOperationKeys = new Set();
        for (const op of ops) {
            if (!isObject(op) || !['upsert', 'delete', 'move'].includes(op.op)) throw new Error('invalid_op');
            const opMessageId = String(op.messageId || op.message?.extra?.multi_client_sync?.messageId || '');
            if (!jsonSafeId(opMessageId)) throw new Error('message_ids_required');

            const operationKey = `${op.op}:${opMessageId}:${String(op.afterMessageId ?? '')}`;
            if (seenOperationKeys.has(operationKey)) throw new Error('duplicate_delta_operation');
            seenOperationKeys.add(operationKey);

            if (op.op === 'upsert') {
                const modifiedAt = Number(op.modifiedAt);
                if (!Number.isFinite(modifiedAt) || modifiedAt <= 0) throw new Error('invalid_modified_timestamp');
                if (op.afterMessageId != null && !jsonSafeId(String(op.afterMessageId))) throw new Error('invalid_delta_anchor');
            } else if (op.op === 'delete') {
                const deletedAt = Number(op.deletedAt);
                if (!Number.isFinite(deletedAt) || deletedAt <= 0) throw new Error('invalid_delete_timestamp');
            } else if (op.op === 'move') {
                if (op.afterMessageId != null && !jsonSafeId(String(op.afterMessageId))) throw new Error('invalid_delta_anchor');
                if (op.afterMessageId != null && String(op.afterMessageId) === opMessageId) throw new Error('delta_move_self');
            }
        }
        if (bytes({ ops }) > LIMITS.maxDeltaBytes) throw new Error('delta_too_large');
    } catch (error) {
        return res.status(error.message === 'delta_too_large' ? 413 : 400).json({ ok: false, error: error.message });
    }

    const deltaFp = operationFingerprint([member.clientId, 'delta', ops]);

    return withLock(req, scope, async (state, tx) => {
        // A duplicate may be a timed-out client retrying: return the authoritative state.
        const prior = findOp(state, opId);
        if (prior) return duplicateOpResponse(res, state, prior, deltaFp);
        if (expireGeneration(state)) {
            const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [recovery]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, recovery);
        }
        if (state.generation) {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) {
            return res.status(409).json(revisionError(state));
        }

        let projected;
        try {
            projected = applyDeltaToSnapshot(state.snapshot, ops);
        } catch (error) {
            return res.status(409).json({ ok: false, error: 'delta_conflict', reason: error.message, state: publicState(state) });
        }

        // A small delta can still add a huge message: verify the RESULT fits.
        if (bytes(projected) > LIMITS.maxSnapshotBytes) {
            return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
        }

        const newRevision = state.revision + 1;
        const prepared = prepareEvent(state, {
            type: 'snapshot_delta',
            revision: newRevision,
            baseRevision: Number(body.baseRevision),
            ops: clone(ops),
            sourceClientId: member.clientId,
        }, { opId, fp: deltaFp });

        // A delta that would chunk cannot be journaled or replayed: reject it
        // so the client falls back to the full snapshot path.
        if (prepared.kind === 'chunked') {
            return res.status(413).json({ ok: false, error: 'delta_too_large' });
        }

        state.snapshot = projected;
        state.revision = newRevision;
        state.updatedAt = now();
        commitPreparedEvents(state, [prepared]);

        // Fast path: small durable append instead of rewriting the state file.
        // Journal durability commits the mutation; a failed compaction must
        // never roll it back.
        const journalSize = await appendDeltaJournal(req, scope, prepared);
        markPersisted(state, tx);

        if (journalSize >= LIMITS.maxDeltaJournalBytes) {
            try {
                await persistState(req, scope, state);
            } catch (error) {
                console.warn('[multi-client-sync] delta journal compaction deferred:', error?.message || error);
            }
        }

        // Hard ceiling: force compaction. If the journal somehow still
        // exceeds it, fail the request so the client falls back to the
        // snapshot path instead of allowing unbounded journal growth.
        if (journalSize > LIMITS.maxDeltaJournalHardBytes) {
            let remaining = journalSize;
            try {
                await persistState(req, scope, state);
                const stat = await fsp.stat(deltaJournalPath(req, scope)).catch(() => null);
                remaining = stat ? stat.size : 0;
            } catch (error) {
                console.warn('[multi-client-sync] delta journal hard-limit compaction failed:', error?.message || error);
            }
            if (remaining > LIMITS.maxDeltaJournalHardBytes) {
                console.warn('[multi-client-sync] delta journal exceeded hard limit:', remaining);
                return res.status(500).json({ ok: false, error: 'delta_journal_hard_limit_exceeded' });
            }
        }

        publishPreparedEvent(req, scope, prepared);

        // NEVER publicState() here — compact response only.
        return res.json({
            ok: true,
            state: publicStateCompact(state),
            deltaRevision: newRevision,
            deltaEventId: prepared.id,
        });
    });
}

// ---------------------------------------------------------------------------
// Handlers
// ---------------------------------------------------------------------------

async function handlePing(req, res) {
    if (!requireAuth(req, res)) return;
    res.json({ ok: true, plugin: PLUGIN_ID, protocol: PROTOCOL, schema: SCHEMA, serverInstanceId });
}

// Two-phase join: an established scope never needs the client's snapshot, so
// the client joins WITHOUT it first. Only when the server has never been
// seeded at all does it ask for a seed, and only then does the client upload
// the chat. `seeded` (not member count, not revision alone) decides.
async function handleJoin(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const clientId = String(body.clientId || '');
    const deviceId = String(body.deviceId || '');
    if (!jsonSafeId(clientId) || !jsonSafeId(deviceId)) {
        return res.status(400).json({ ok: false, error: 'invalid_client' });
    }
    // Membership is bound to an exact connection identity so a delayed
    // /leave or /heartbeat from a previous connection cannot evict the
    // current one.
    const connectionId = String(body.connectionId || '');
    if (!jsonSafeId(connectionId)) {
        return res.status(400).json({ ok: false, error: 'invalid_connection_id' });
    }

    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    let set = pruneExpiredMembers(skey);
    if (!set) { set = new Map(); subscribers.set(skey, set); }
    if (set.size >= LIMITS.maxSubscribersPerScope && !set.has(clientId)) {
        return res.status(429).json({ ok: false, error: 'too_many_clients' });
    }
    const existing = set.get(clientId)?.member;
    if (existing && existing.deviceId !== deviceId && now() - existing.lastSeenAt <= LIMITS.memberTtlMs) {
        return res.status(409).json({ ok: false, error: 'client_id_in_use' });
    }

    const release = await lockFor(skey);
    try {
        enforceScopeCacheLimit(req);
        const state = await loadState(req, scope);

        if (!state.seeded && set.size === 0 && !body.snapshot) {
            // No server state and no other members: this client must seed.
            return res.json({ ok: true, seedRequired: true, state: publicState(state), members: publicMembers(req, scope) });
        }

        if (!state.seeded && set.size === 0 && body.snapshot) {
            // Initial seed is a real state transition: revision 1, a durable
            // snapshot event, and the seeded marker so an established scope is
            // never re-seeded regardless of member count or future revisions.
            const tx = beginStateTransaction(state);
            try {
                const seededSnapshot = canonicalSnapshot(body.snapshot);
                if (bytes(seededSnapshot) > LIMITS.maxSnapshotBytes) {
                    rollbackTransaction(state, tx);
                    return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
                }
                state.snapshot = seededSnapshot;
                state.seeded = true;
                state.revision = Math.max(1, Number(state.revision || 0));
                state.updatedAt = now();
                if (!Array.isArray(state.events)) state.events = [];
                const prepared = prepareEvent(state, {
                    type: 'snapshot',
                    revision: state.revision,
                    snapshot: state.snapshot,
                    sourceClientId: clientId,
                });
                commitPreparedEvents(state, [prepared]);
                await persistState(req, scope, state);
                markPersisted(state, tx);
                publishPreparedEvent(req, scope, prepared);
            } catch (error) {
                if (!tx.persisted) rollbackTransaction(state, tx);
                if (error instanceof Error && ['snapshot_required', 'snapshot_messages_required', 'invalid_message', 'message_ids_required', 'duplicate_message_id'].includes(error.message)) {
                    return res.status(400).json({ ok: false, error: error.message });
                }
                throw error;
            }
        }

        const liveEntry = set.get(clientId);
        if (liveEntry?.res && !liveEntry.closed) {
            // A live SSE connection exists for this client: refresh membership
            // in place instead of replacing the entry with a placeholder.
            liveEntry.member = {
                clientId,
                deviceId,
                connectionId,
                joinedAt: liveEntry.member?.joinedAt || now(),
                lastSeenAt: now(),
            };
        } else {
            set.set(clientId, {
                member: { clientId, deviceId, connectionId, joinedAt: now(), lastSeenAt: now() },
                res: null,
            });
        }
        return res.json({ ok: true, state: publicState(state), members: publicMembers(req, scope) });
    } finally {
        release();
    }
}

async function handleLeave(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    const set = subscribers.get(skey);
    if (set) {
        const entry = set.get(String(body.clientId || ''));
        if (entry?.member?.deviceId === String(body.deviceId || '')) {
            // A leave must match the exact membership connection: a delayed
            // leave from an older connection must not evict the current one.
            const memberConnectionId = entry.member.connectionId || '';
            const matchesConnection = !memberConnectionId || memberConnectionId === String(body.connectionId || '');
            if (matchesConnection) {
                if (entry.res && !entry.closed) {
                    try { entry.res.end(); } catch { /* ignore */ }
                }
                set.delete(String(body.clientId || ''));
            }
        }
        if (set.size === 0) subscribers.delete(skey);
    }
    res.json({ ok: true });
}

async function handleHeartbeat(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    const set = subscribers.get(skey);
    const clientId = String(body.clientId || '');
    const deviceId = String(body.deviceId || '');
    const entry = set?.get(clientId);
    if (!entry || entry.member.deviceId !== deviceId) {
        return res.status(403).json({ ok: false, error: 'not_member' });
    }
    if (entry.member.lastHeartbeat && now() - entry.member.lastHeartbeat < LIMITS.heartbeatMinMs) {
        return res.json({ ok: true });
    }
    entry.member.lastSeenAt = now();
    entry.member.lastHeartbeat = now();
    return withLock(req, scope, async (state, tx) => {
        if (expireGeneration(state)) {
            const prepared = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [prepared]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            // The final snapshot is durable now. A crash before this unlink is safe:
            // replay detects the matching terminal event and will not restore stale text.
            await clearGenerationJournal(req, scope);
            publishPreparedEvent(req, scope, prepared);
        }
        // Lean: revision + generation metadata only.
        return res.json({ ok: true, revision: state.revision, generation: generationPublic(state.generation, false) });
    });
}

async function handleState(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    return withLock(req, scope, async (state, tx) => {
        enforceScopeCacheLimit(req);
        if (expireGeneration(state)) {
            const prepared = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [prepared]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, prepared);
        }
        return res.json({ ok: true, state: publicState(state), members: publicMembers(req, scope) });
    });
}

async function handleSnapshot(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    const opId = String(body.opId || '');
    if (!jsonSafeId(opId)) return res.status(400).json({ ok: false, error: 'invalid_op_id' });

    let snap;
    try { snap = canonicalSnapshot(body.snapshot); } catch (e) {
        return res.status(400).json({ ok: false, error: e.message });
    }
    if (bytes(snap) > LIMITS.maxSnapshotBytes) {
        return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
    }

    const snapFp = operationFingerprint([member.clientId, 'snapshot', snap]);

    return withLock(req, scope, async (state, tx) => {
        const prior = findOp(state, opId);
        if (prior) return duplicateOpResponse(res, state, prior, snapFp);
        if (expireGeneration(state)) {
            const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [recovery]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, recovery);
        }
        if (state.generation) {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) {
            return res.status(409).json(revisionError(state));
        }
        if (snap.messages.length === 0 && Array.isArray(state.snapshot?.messages) && state.snapshot.messages.length > 0) {
            return res.status(409).json({
                ok: false,
                error: 'empty_snapshot_would_clear_chat',
                state: publicState(state),
            });
        }
        if (snapshotDropsUnexplainedMessages(state.snapshot, snap)) {
            return res.status(409).json({
                ok: false,
                error: 'snapshot_would_drop_existing_messages',
                state: publicState(state),
            });
        }

        const newRevision = state.revision + 1;
        const prepared = prepareEvent(state, {
            type: 'snapshot',
            revision: newRevision,
            snapshot: snap,
            sourceClientId: member.clientId,
        }, { opId, fp: snapFp });

        state.snapshot = snap;
        state.seeded = true;
        state.revision = newRevision;
        state.updatedAt = now();
        commitPreparedEvents(state, [prepared]);

        await persistState(req, scope, state);
        markPersisted(state, tx);
        publishPreparedEvent(req, scope, prepared);
        return res.json({ ok: true, state: publicState(state) });
    });
}

async function handleGenerationClaim(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    const opId = String(body.opId || '');
    if (!jsonSafeId(opId)) return res.status(400).json({ ok: false, error: 'invalid_op_id' });
    let snap;
    try { snap = canonicalSnapshot(body.snapshot); } catch (e) {
        return res.status(400).json({ ok: false, error: e.message });
    }

    const claimFp = operationFingerprint([member.clientId, 'claim', String(body.generationId || ''), snap]);

    return withLock(req, scope, async (state, tx) => {
        const prior = findOp(state, opId);
        if (prior) return duplicateOpResponse(res, state, prior, claimFp);
        if (state.generation) {
            const expired = expireGeneration(state);
            if (expired) {
                const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null });
                commitPreparedEvents(state, [recovery]);
                await persistState(req, scope, state);
                markPersisted(state, tx);
                publishPreparedEvent(req, scope, recovery);
            }
        }
        if (state.generation) {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) {
            return res.status(409).json(revisionError(state));
        }
        if (snap.messages.length === 0 && Array.isArray(state.snapshot?.messages) && state.snapshot.messages.length > 0) {
            return res.status(409).json({
                ok: false,
                error: 'empty_snapshot_would_clear_chat',
                state: publicState(state),
            });
        }
        if (snapshotDropsUnexplainedMessages(state.snapshot, snap)) {
            return res.status(409).json({
                ok: false,
                error: 'snapshot_would_drop_existing_messages',
                state: publicState(state),
            });
        }
        if (bytes(snap) > LIMITS.maxSnapshotBytes) {
            return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
        }

        const newRevision = state.revision + 1;
        const generation = makeGeneration(body, serverInstanceId);

        const [snapshotEvent, claimEvent] = prepareEvents(state, [
            {
                event: {
                    type: 'snapshot',
                    revision: newRevision,
                    snapshot: snap,
                    sourceClientId: member.clientId,
                    generationId: generation.generationId,
                },
            },
            {
                event: {
                    type: 'generation_claimed',
                    generation: generationPublic(generation, false),
                    revision: newRevision,
                },
                opId,
                fp: claimFp,
            },
        ]);

        state.snapshot = snap;
        state.seeded = true;
        state.revision = newRevision;
        state.updatedAt = now();
        state.generation = generation;
        commitPreparedEvents(state, [snapshotEvent, claimEvent]);

        await persistState(req, scope, state);
        markPersisted(state, tx);
        publishPreparedEvent(req, scope, snapshotEvent);
        publishPreparedEvent(req, scope, claimEvent);
        return res.json({ ok: true, state: publicState(state) });
    });
}

async function handleGenerationUpdate(req, res, kind) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;

    return withLock(req, scope, async (state, tx) => {
        if (!state.generation || !generationOwner(state.generation, body)) {
            return res.status(409).json({ ok: false, error: 'generation_not_owned', state: publicState(state) });
        }
        if (expireGeneration(state)) {
            return res.status(409).json({ ok: false, error: 'generation_expired', state: publicState(state) });
        }
        const g = state.generation;

        if (kind === 'heartbeat') {
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            // Compact: no snapshot in a 5-second-interval response.
            return res.json({
                ok: true,
                state: publicStateCompact(state),
                stopRequested: !!g.stopRequested,
            });
        }

        if (kind === 'started') {
            if (['started', 'streaming'].includes(g.phase)) {
                return res.json({ ok: true, state: publicStateCompact(state), duplicate: true });
            }
            g.phase = 'started';
            g.startedAt = g.startedAt || now();
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;

            const prepared = prepareEvent(state, {
                type: 'generation_started',
                generation: generationPublic(g, false),
            });
            commitPreparedEvents(state, [prepared]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, prepared);
            return res.json({ ok: true, state: publicStateCompact(state) });
        }

        if (kind === 'stream') {
            // The server is the final authority on generation end-state: a
            // terminalizing or stop-requested generation never accepts more
            // stream frames, regardless of client timing.
            const currentPhase = String(g.phase || '');
            if (['completed', 'stopped', 'failed', 'terminal'].includes(currentPhase)) {
                return res.status(409).json({ ok: false, error: 'generation_terminal', state: publicStateCompact(state) });
            }
            if (g.stopRequested) {
                return res.status(409).json({ ok: false, error: 'generation_stop_requested', state: publicStateCompact(state) });
            }
            if (!['started', 'streaming'].includes(g.phase)) {
                return res.status(409).json({ ok: false, error: 'generation_not_started' });
            }
            const seq = Number(body.seq);
            if (!Number.isInteger(seq)) {
                return res.status(400).json({ ok: false, error: 'invalid_sequence' });
            }
            if (seq === g.seq) {
                const sameMessageId = messageIdFromMessage(body.message) === g.messageId;
                const sameCumulativePayload = sameMessageId &&
                    operationFingerprint([body.message]) === operationFingerprint([g.message]);
                if (sameCumulativePayload) {
                    return res.json({ ok: true, state: publicStateCompact(state), stopRequested: !!g.stopRequested, duplicate: true });
                }
                // Same sequence with different text is not a duplicate. Require the
                // owner to rebase the newest cumulative frame to the next sequence.
                return res.status(409).json({
                    ok: false,
                    error: 'stream_sequence_conflict',
                    expected: Number(g.seq || 0) + 1,
                    latestSeq: Number(g.seq || 0),
                });
            }
            if (seq !== g.seq + 1) {
                return res.status(409).json({
                    ok: false,
                    error: 'stream_sequence_conflict',
                    expected: Number(g.seq || 0) + 1,
                    latestSeq: Number(g.seq || 0),
                });
            }

            const message = clone(body.message);
            if (!isObject(message)) {
                return res.status(400).json({ ok: false, error: 'stream_message_required' });
            }
            const rawId = message?.extra?.multi_client_sync?.messageId;
            if (typeof rawId !== 'string' || !jsonSafeId(rawId)) {
                return res.status(400).json({ ok: false, error: 'message_ids_required' });
            }
            const id = rawId;
            const messageIndex = Number.isInteger(body.messageIndex) ? body.messageIndex : null;

            // Event metadata reflects the POST-update state, built without
            // mutating g so a failed prepare changes nothing.
            const updatedPublic = generationPublic(g, false);
            updatedPublic.phase = 'streaming';
            updatedPublic.seq = seq;
            updatedPublic.messageId = id;
            updatedPublic.messageIndex = messageIndex;

            // generation_stream is fully transient: no durable event ID, no
            // event history, no state-file write. SSE delivery only. The
            // durable generation is metadata-only and nulled on load anyway,
            // so persisting stream state bought nothing.
            const prepared = prepareEvent({ nextEventId: 0 }, {
                type: 'generation_stream',
                generation: updatedPublic,
                messageIndex,
                seq,
                message,
                cumulative: true,
            }, { id: 0, transferId: newTransferId() });

            g.phase = 'streaming';
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            g.seq = seq;
            g.messageId = id;
            g.messageIndex = messageIndex;
            g.message = message;
            state.updatedAt = now();
            // If the checkpoint write/fsync fails, do not publish or acknowledge
            // this frame. withLock rolls the in-memory generation mutation back.
            await appendGenerationCheckpoint(req, scope, g, message, seq, messageIndex);

            publishPreparedEvent(req, scope, prepared);
            // Compact response: never the snapshot.
            return res.json({ ok: true, state: publicStateCompact(state), stopRequested: !!g.stopRequested });
        }

        if (kind === 'terminal') {
            const opId = String(body.opId || '');
            if (!jsonSafeId(opId)) return res.status(400).json({ ok: false, error: 'invalid_op_id' });

            let snap;
            try { snap = canonicalSnapshot(body.snapshot); } catch (error) {
                return res.status(400).json({ ok: false, error: error.message });
            }
            snap = preserveTerminalSnapshot(state, snap, g);
            if (bytes(snap) > LIMITS.maxSnapshotBytes) {
                return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
            }

            const terminalPhase = g.stopRequested ? 'stopped' : String(body.phase || 'completed');
            const terminalFp = operationFingerprint([member.clientId, 'terminal', g.generationId, terminalPhase, snap]);

            const prior = findOp(state, opId);
            if (prior) return duplicateOpResponse(res, state, prior, terminalFp);

            const newRevision = state.revision + 1;
            const finished = generationPublic(g, false);
            finished.phase = terminalPhase;

            const prepared = prepareEvent(state, {
                type: 'generation_terminal',
                generation: finished,
                revision: newRevision,
                finalSeq: Number(g.seq || 0),
                snapshot: snap,
            }, { opId, fp: terminalFp });

            state.snapshot = snap;
            state.seeded = true;
            state.revision = newRevision;
            state.updatedAt = now();
            state.generation = null;
            commitPreparedEvents(state, [prepared]);

            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, prepared);
            // Terminal returns the full state: it is the authoritative final
            // checkpoint and runs once per generation, not on a hot path.
            return res.json({ ok: true, state: publicState(state) });
        }

        return res.status(400).json({ ok: false, error: 'unknown_generation_update' });
    });
}

function messageIdFromMessage(message) {
    return message?.extra?.multi_client_sync?.messageId || null;
}

async function handleGenerationStopRequest(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    const opId = String(body.opId || '');
    const stopFp = operationFingerprint([member.clientId, 'stop', String(body.generationId || '')]);
    return withLock(req, scope, async (state, tx) => {
        if (opId) {
            const prior = findOp(state, opId);
            if (prior) return duplicateOpResponse(res, state, prior, stopFp, true);
        }
        if (expireGeneration(state)) {
            const recovered = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [recovered]);
            await persistState(req, scope, state);
            markPersisted(state, tx);
            publishPreparedEvent(req, scope, recovered);
        }
        if (!state.generation) {
            return res.json({ ok: true, state: publicStateCompact(state), alreadyStopped: true });
        }
        const requestedGenerationId = String(body.generationId || '');
        if (requestedGenerationId && requestedGenerationId !== state.generation.generationId) {
            // A delayed Stop from an old chat/generation must never stop the
            // generation that currently owns this scope.
            return res.status(409).json({
                ok: false,
                error: 'generation_mismatch',
                state: publicStateCompact(state),
            });
        }
        state.generation.stopRequested = true;
        state.updatedAt = now();
        const prepared = prepareEvent(state, {
            type: 'generation_stop_requested',
            generation: generationPublic(state.generation, false),
            requesterClientId: member.clientId,
        }, { opId: opId || null, fp: opId ? stopFp : null });
        commitPreparedEvents(state, [prepared]);
        // An event cannot be retracted if persistence fails and the in-memory
        // transaction rolls back. Commit durability first; then broadcast the
        // low-latency Stop decision to all subscribers.
        await persistState(req, scope, state);
        markPersisted(state, tx);
        publishPreparedEvent(req, scope, prepared);
        return res.json({ ok: true, state: publicStateCompact(state) });
    });
}

// ---------------------------------------------------------------------------
// SSE endpoint
// ---------------------------------------------------------------------------

async function handleSse(req, res) {
    if (!req?.user) return res.status(401).end();

    let scope;
    try {
        scope = JSON.parse(Buffer.from(String(req.query?.scope || ''), 'base64url').toString('utf8'));
    } catch { return res.status(400).end(); }

    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).end();

    const clientId = String(req.query?.clientId || '');
    const deviceId = String(req.query?.deviceId || '');
    if (!jsonSafeId(clientId) || !jsonSafeId(deviceId)) return res.status(400).end();
    if (!isMember(req, scope, clientId, deviceId)) return res.status(403).end();

    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    let set = pruneExpiredMembers(skey);
    if (!set) { set = new Map(); subscribers.set(skey, set); }
    if (set.size >= LIMITS.maxSubscribersPerScope && !set.has(clientId)) return res.status(429).end();

    const lastId = Number(req.query?.lastEventId || req.get('last-event-id') || 0);
    const supportsDelta = req.query?.delta === '1';

    res.status(200);
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache, no-transform');
    res.setHeader('Connection', 'keep-alive');
    res.setHeader('X-Accel-Buffering', 'no');
    res.flushHeaders?.();

    const existing = set.get(clientId);
    const member = existing?.member && existing.member.deviceId === deviceId
        ? existing.member
        : { clientId, deviceId, joinedAt: now() };
    member.lastSeenAt = now();

    const sub = createSubscriber(res, member, { supportsDelta });

    let replayEvents = null;
    let needResync = false;
    let helloBase = null;
    let state = null;
    let rejectTooManyClients = false;

    // Read and build the initial replay plan without holding the mutation lock.
    // Existing event objects are immutable after commit, so keeping references
    // here avoids a large deep-clone of the entire replay history.
    try {
        state = await loadState(req, scope);

        const initialLastEventId = state.nextEventId - 1;
        const oldest = state.events[0]?.id || state.nextEventId;

        if (Number.isInteger(lastId) && lastId > 0) {
            // History no longer reaches the client's cursor.
            if (lastId < oldest - 1) {
                needResync = true;
            } else {
                replayEvents = [];

                for (const event of state.events) {
                    if (event.id <= lastId) continue;

                    // Stream history is intentionally transient and is never
                    // replayed. The current generation_state is sent separately.
                    if (event.type === 'generation_stream') continue;

                    // A chunked durable event has no replayable payload in the
                    // state file. The only safe recovery is authoritative /state.
                    if (event.type === 'event_chunked') {
                        needResync = true;
                        replayEvents = null;
                        break;
                    }

                    // Legacy clients cannot replay deltas.
                    if (event.type === 'snapshot_delta' && !supportsDelta) {
                        needResync = true;
                        replayEvents = null;
                        break;
                    }

                    replayEvents.push(event);
                }
            }
        }

        // Avoid cloning the potentially enormous live generation message here.
        // prepareEvent() will perform the one required serialization clone later.
        const generationFull = state.generation
            ? {
                ...generationPublic(state.generation, false),
                message: state.generation.message || null,
            }
            : null;

        helloBase = {
            revision: state.revision,
            lastEventId: initialLastEventId,
            generationMeta: generationPublic(state.generation, false),
            generationFull,
            scope: clone(scope),
            members: publicMembers(req, scope),
        };
    } catch {
        try { res.end(); } catch { /* ignore */ }
        return;
    }

    // The lock is intentionally tiny. It reconciles anything committed while
    // the unlocked replay plan was being built, then atomically installs the
    // subscriber. This avoids forcing a resync merely because a normal event
    // arrived during replay construction.
    const release = await lockFor(skey);
    try {
        // Re-read the current state through loadState(). With the per-scope
        // lock this is effectively a cheap cached lookup, while guaranteeing
        // that the subscriber swap and event-history reconciliation use the
        // current authoritative state.
        const currentState = await loadState(req, scope);
        const currentLastEventId = currentState.nextEventId - 1;
        const currentOldest = currentState.events[0]?.id || currentState.nextEventId;

        // If the requested cursor has fallen behind history pruning, there is
        // no safe replay path left.
        if (Number.isInteger(lastId) && lastId > 0 && lastId < currentOldest - 1) {
            needResync = true;
            replayEvents = null;
        }

        // Reconcile events committed after the unlocked read. Since event IDs
        // are monotonically increasing and existing event objects are immutable,
        // only the newly committed suffix needs to be added.
        if (!needResync && currentLastEventId > helloBase.lastEventId) {
            if (!replayEvents) replayEvents = [];

            for (const event of currentState.events) {
                if (event.id <= helloBase.lastEventId) continue;

                if (event.type === 'generation_stream') continue;

                if (event.type === 'event_chunked') {
                    needResync = true;
                    replayEvents = null;
                    break;
                }

                // Legacy clients cannot replay deltas.
                if (event.type === 'snapshot_delta' && !supportsDelta) {
                    needResync = true;
                    replayEvents = null;
                    break;
                }

                // Avoid duplicating anything already present in the unlocked
                // replay plan.
                if (
                    replayEvents.length === 0 ||
                    replayEvents[replayEvents.length - 1]?.id !== event.id
                ) {
                    if (!replayEvents.some(existing => existing.id === event.id)) {
                        replayEvents.push(event);
                    }
                }
            }
        }

        // Refresh the hello snapshot from the current state after reconciliation.
        // This makes the hello cursor describe exactly the replay boundary that
        // was current when the subscriber was installed.
        if (!needResync) {
            helloBase.revision = currentState.revision;
            helloBase.lastEventId = currentLastEventId;
            helloBase.generationMeta = generationPublic(currentState.generation, false);

            // Do not deep-clone the giant live message here. The object is only
            // read later by prepareEvent(), which performs the serialization
            // needed for the actual SSE transfer.
            helloBase.generationFull = currentState.generation
                ? {
                    ...generationPublic(currentState.generation, false),
                    message: currentState.generation.message || null,
                }
                : null;
        }

        // The subscriber map may have changed while the unlocked state read was
        // running, so always reacquire the current map under the lock.
        set = pruneExpiredMembers(skey);
        if (!set) {
            set = new Map();
            subscribers.set(skey, set);
        }

        if (!needResync) {
            if (set.size >= LIMITS.maxSubscribersPerScope && !set.has(clientId)) {
                rejectTooManyClients = true;
            } else {
                const prev = set.get(clientId);

                // Same client reconnecting: retire the old SSE connection before
                // installing the new one. Its close handler cannot overwrite the
                // new subscriber because it checks identity before replacing it.
                if (prev && prev !== sub && prev.res && !prev.closed) {
                    try { prev.res.end(); } catch { /* ignore */ }
                }

                member.lastSeenAt = now();
                set.set(clientId, sub);
            }
        }
    } catch {
        needResync = true;
        replayEvents = null;
    } finally {
        release();
    }

    if (rejectTooManyClients) {
        closeSubscriber(sub, 'too_many_clients');
        return res.status(429).end();
    }

    const transientState = { nextEventId: 0 };

    try {
        if (needResync) {
            sendSseFrame(res, {
                type: 'resync_required',
                revision: helloBase.revision,
                lastEventId: helloBase.lastEventId,
            }, null);
            closeSubscriber(sub, 'unreplayable_history');
            return;
        }

        const hello = prepareEvent(transientState, {
            type: 'hello',
            protocol: PROTOCOL,
            schema: SCHEMA,
            revision: helloBase.revision,
            generation: helloBase.generationMeta,
            scope: helloBase.scope,
            members: helloBase.members,
        }, { id: 0 });
        for (const frame of hello.frames) sendSseFrame(res, frame, null);

        const generationState = prepareEvent(transientState, {
            type: 'generation_state',
            revision: helloBase.revision,
            generation: helloBase.generationFull,
        }, { id: 0, transferId: newTransferId() });
        for (const frame of generationState.frames) sendSseFrame(res, frame, null);

        if (replayEvents) {
            for (const event of replayEvents) {
                sendSseFrame(res, event, event.id);
            }
            sendSseFrame(res, { type: 'replay_complete', revision: helloBase.revision }, null);
        }
    } catch {
        closeSubscriber(sub, 'replay_error');
        return;
    }

    sub.replaying = false;
    flushSubscriberQueue(sub);

    const timer = setInterval(() => {
        try { res.write(': keepalive\n\n'); } catch { clearInterval(timer); }
    }, 15_000);

    req.on('close', () => {
        clearInterval(timer);
        const current = set.get(clientId);
        if (current === sub) {
            set.set(clientId, { member: current.member, res: null });
        }
    });
}

// ---------------------------------------------------------------------------
// Router wiring
// ---------------------------------------------------------------------------

function init(router) {
    routerRef = router;
    serverInstanceId = crypto.randomUUID();
    router.get('/ping', handlePing);
    router.post('/join', handleJoin);
    router.post('/leave', handleLeave);
    router.post('/heartbeat', handleHeartbeat);
    router.post('/state', handleState);
    router.post('/snapshot', handleSnapshot);
    router.post('/delta', handleDelta);
    router.post('/generation/claim', handleGenerationClaim);
    router.post('/generation/heartbeat', (req, res) => handleGenerationUpdate(req, res, 'heartbeat'));
    router.post('/generation/started', (req, res) => handleGenerationUpdate(req, res, 'started'));
    router.post('/generation/stream', (req, res) => handleGenerationUpdate(req, res, 'stream'));
    router.post('/generation/terminal', (req, res) => handleGenerationUpdate(req, res, 'terminal'));
    router.post('/generation/stop', handleGenerationStopRequest);
    router.get('/events', handleSse);
    console.log(`[multi-client-sync] server plugin ready (${serverInstanceId})`);
}

function exit() {
    for (const map of subscribers.values()) {
        for (const sub of map.values()) {
            try { sub.res?.end(); } catch { /* ignore */ }
        }
    }
    subscribers.clear();
    scopes.clear();
    userLocks.clear();
    routerRef = null;
}

const info = {
    id: PLUGIN_ID,
    name: 'Multi-Client Sync',
    description: 'Synchronize the same SillyTavern chat across browser tabs/devices with live generation mirroring.',
    version: '1.0.0',
};

module.exports = { init, exit, info };