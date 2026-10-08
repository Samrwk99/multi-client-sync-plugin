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
    maxChunkAssemblyBytes: 12 * 1024 * 1024,
    maxEventHistoryBytes: 4 * 1024 * 1024,
    maxEvents: 300,
    maxRecentOps: 500,
    memberTtlMs: 60_000,
    heartbeatMinMs: 3_000,
    generationLeaseMs: 30_000,
    generationMaxMs: 30 * 60_000,
    maxScopesPerUser: 200,
    maxSubscribersPerScope: 25,
    maxBufferedSseBytes: 4 * 1024 * 1024,
    // Strongest-durability switch (temp-file fsync + rename + dir fsync).
    // Off by default: it is noticeably slower on every mutation.
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
        const id = message?.extra?.multi_client_sync?.messageId;
        if (!jsonSafeId(String(id ?? ''))) throw new Error('message_ids_required');
        if (seen.has(id)) throw new Error('duplicate_message_id');
        seen.add(id);
    }
    return { messages, metadata: clone(isObject(input.metadata) ? input.metadata : {}) };
}

function defaultState(scope) {
    return {
        protocol: PROTOCOL,
        schema: SCHEMA,
        scope: clone(scope),
        revision: 0,
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
    state.snapshot = canonicalSnapshot(parsed.snapshot || { messages: [], metadata: {} });
    state.events = Array.isArray(parsed.events) ? clone(parsed.events) : [];
    state.nextEventId = Number(parsed.nextEventId || 1);
    state.recentOps = Array.isArray(parsed.recentOps) ? clone(parsed.recentOps) : [];
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
            if (parsed.generation) recovered = true;
        } catch (error) {
            if (error?.code !== 'ENOENT') throw error;
            // No file: fresh default state. Version/scope mismatches throw above
            // and surface to the caller; persisted state is never silently reset.
        }

        state.updatedAt = now();
        const freshEntry = scopes.get(key) || {};
        freshEntry.state = state;
        freshEntry.loading = null;
        freshEntry.lastAccessed = now();
        scopes.set(key, freshEntry);

        // Stale generation from a previous server instance: clear once, record
        // the recovery event, persist — so the on-disk file stops carrying it.
        if (recovered) {
            const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null }, { id: state.nextEventId });
            commitPreparedEvents(state, [recovery]);
            await persistState(req, scope, state);
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

// Stream events are transient: the live message never lives in durable history.
// Applied to both the persisted projection AND the in-memory event list so the
// two can never diverge and memory stays bounded.
function compactEvents(events) {
    if (!Array.isArray(events)) return events;
    return events.map(event => {
        if (event?.type === 'generation_stream') {
            return { ...event, message: undefined, compacted: true };
        }
        return event;
    });
}

async function persistState(req, scope, state, { fsync = LIMITS.fsyncState } = {}) {
    const file = statePath(req, scope);
    await ensureDir(path.dirname(file));

    const projected = clone(state);
    projected.updatedAt = now();
    projected.events = compactEvents(projected.events);
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
    } catch (error) {
        try { await fsp.unlink(tmp); } catch { /* ignore */ }
        throw error;
    }

    // Mirror the same compaction/pruning onto the in-memory state so the cache
    // matches disk and long generations cannot grow memory without bound.
    state.updatedAt = projected.updatedAt;
    if (Array.isArray(state.events)) {
        state.events = compactEvents(state.events);
        pruneEventHistory(state);
    }
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

    // Self-cleaning lock map: drop the entry once this link resolves and no
    // newer waiter has replaced it.
    const cleanup = () => {
        if (userLocks.get(key) === chain) userLocks.delete(key);
    };
    chain.then(cleanup, cleanup);

    userLocks.set(key, chain);
    return previous.catch(() => {}).then(() => release);
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
        // Rollback in-memory state only when nothing reached disk. Once any
        // persist succeeded, disk is authoritative and memory must match it.
        if (state && tx && !tx.persisted) rollbackTransaction(state, tx);
        throw error;
    } finally {
        release();
    }
}

function beginStateTransaction(state) {
    return {
        originalRevision: state.revision,
        originalNextEventId: state.nextEventId,
        originalEventsLength: state.events.length,
        originalRecentOpsLength: state.recentOps.length,
        originalSnapshot: state.snapshot,
        originalGeneration: state.generation,
        persisted: false,
    };
}

function rollbackTransaction(state, tx) {
    state.revision = tx.originalRevision;
    state.nextEventId = tx.originalNextEventId;
    state.events.length = tx.originalEventsLength;
    state.recentOps.length = tx.originalRecentOpsLength;
    state.snapshot = tx.originalSnapshot;
    state.generation = tx.originalGeneration;
}

function rememberOp(state, opId) {
    if (!opId) return;
    state.recentOps.push(opId);
    if (state.recentOps.length > LIMITS.maxRecentOps) {
        state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
    }
}

function hasOp(state, opId) { return !!opId && state.recentOps.includes(opId); }

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
// prepareEvent never mutates state. It assigns a candidate id (caller-supplied
// or state.nextEventId), serializes once, and either returns a single normal
// frame or chunk frames sharing one logical id plus a compact marker for
// durable history. nextEventId only advances in commitPreparedEvents.
// ---------------------------------------------------------------------------

function prepareEvent(state, logicalEvent, { id = null, opId = null, transferId = null } = {}) {
    const eventId = id ?? state.nextEventId;
    const at = now();

    const storedEvent = {
        ...clone(logicalEvent),
        id: eventId,
        at,
        eventVersion: 1,
    };

    const serialized = jsonToUtf8Bytes(storedEvent);
    const totalBytes = serialized.length;

    if (totalBytes <= LIMITS.maxEventBytes - 256) {
        return {
            kind: 'normal',
            id: eventId,
            at,
            opId,
            storedEvent,
            frames: [storedEvent],
            totalBytes,
            transferId,
        };
    }

    // Hard ceiling: no single logical event may exceed the assembly budget.
    if (totalBytes > LIMITS.maxChunkAssemblyBytes) {
        throw new Error('event_too_large');
    }

    // Oversized: chunk the serialized bytes. Every chunked transfer gets a
    // unique transferId so the client can key assembly safely for both
    // durable logical events and transient (hello/generation_state) sends.
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
        storedEvent: compactMarker,
        frames,
        totalBytes,
        transferId: effectiveTransferId,
    };
}

function prepareEvents(state, logicalEvents) {
    // Sequential candidate ids across a batch; nothing is committed here.
    let nextId = state.nextEventId;
    const prepared = [];
    for (const { event, opId, transferId } of logicalEvents) {
        prepared.push(prepareEvent(state, event, { id: nextId++, opId, transferId }));
    }
    return prepared;
}

function commitPreparedEvents(state, preparedEvents) {
    for (const prepared of preparedEvents) {
        state.events.push(clone(prepared.storedEvent));
        state.nextEventId = Math.max(state.nextEventId, prepared.id + 1);
        if (prepared.opId) rememberOp(state, prepared.opId);
    }
}

function publishPreparedEvent(req, scope, prepared) {
    const set = subscribers.get(`${userKey(req)}::${scopeKey(scope)}`) || new Map();
    // Durable logical events carry their id on every frame so the client can
    // dedupe and advance its cursor only after full reassembly. Transient
    // sends (id 0) never touch the cursor.
    const sseId = prepared.id > 0 ? prepared.id : null;
    for (const sub of set.values()) {
        if (sub.closed) continue;
        for (const frame of prepared.frames) {
            try {
                enqueueSseFrame(sub, frame, sseId);
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
    return res.write(out);
}

function enqueueSseFrame(sub, frame, logicalEventId) {
    if (sub.closed) return;
    sub.outboundQueue.push({ frame, logicalEventId });
    sub.outboundBytes += utf8ByteLength(frame);
    // Overflow check runs BEFORE the replaying early-return: a slow replay
    // plus a burst of live chunked events must still hit the cap.
    if (sub.outboundBytes > LIMITS.maxBufferedSseBytes) {
        closeSubscriber(sub, 'buffer_overflow');
        return;
    }
    if (sub.replaying) return;
    flushSubscriberQueue(sub);
}

function flushSubscriberQueue(sub) {
    if (sub.closed || sub.replaying) return;
    while (sub.outboundQueue.length > 0) {
        const item = sub.outboundQueue[0];
        let ok;
        try {
            ok = sendSseFrame(sub.res, item.frame, item.logicalEventId);
        } catch {
            closeSubscriber(sub, 'send_error');
            return;
        }
        if (!ok) break; // wait for drain
        sub.outboundQueue.shift();
        sub.outboundBytes -= utf8ByteLength(item.frame);
    }
}

function closeSubscriber(sub, reason) {
    if (sub.closed) return;
    sub.closed = true;
    sub.outboundQueue.length = 0;
    sub.outboundBytes = 0;
    try { sub.res.end(); } catch { /* ignore */ }
    void reason;
}

function createSubscriber(res, member) {
    const sub = {
        res,
        member,
        replaying: true,
        outboundQueue: [],
        outboundBytes: 0,
        closed: false,
    };
    sub.res.on('drain', () => flushSubscriberQueue(sub));
    return sub;
}

// ---------------------------------------------------------------------------
// Public state / generation
// ---------------------------------------------------------------------------

function publicState(state) {
    return {
        protocol: state.protocol,
        schema: state.schema,
        scope: clone(state.scope),
        revision: state.revision,
        snapshot: clone(state.snapshot),
        // Routine HTTP state never carries the giant live message; that travels
        // through SSE generation_state only.
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
            // If a live SSE connection is attached, close it so the client
            // reconnects instead of silently rotting as an unsubscribe ghost.
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
// Handlers
// ---------------------------------------------------------------------------

async function handlePing(req, res) {
    if (!requireAuth(req, res)) return;
    res.json({ ok: true, plugin: PLUGIN_ID, protocol: PROTOCOL, schema: SCHEMA, serverInstanceId });
}

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
        if (state.revision === 0 && set.size === 0 && body.snapshot) {
            // Initial seed is transactional: a failed persist rolls memory back.
            const tx = beginStateTransaction(state);
            try {
                state.snapshot = canonicalSnapshot(body.snapshot);
                if (bytes(state.snapshot) > LIMITS.maxSnapshotBytes) {
                    rollbackTransaction(state, tx);
                    return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
                }
                await persistState(req, scope, state);
                tx.persisted = true;
            } catch (error) {
                if (!tx.persisted) rollbackTransaction(state, tx);
                if (error instanceof Error && ['snapshot_required', 'snapshot_messages_required', 'invalid_message', 'message_ids_required', 'duplicate_message_id'].includes(error.message)) {
                    return res.status(400).json({ ok: false, error: error.message });
                }
                throw error;
            }
        }
        set.set(clientId, { member: { clientId, deviceId, joinedAt: now(), lastSeenAt: now() }, res: null });
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
            if (entry.res && !entry.closed) {
                try { entry.res.end(); } catch { /* ignore */ }
            }
            set.delete(String(body.clientId || ''));
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
            tx.persisted = true;
            publishPreparedEvent(req, scope, prepared);
        }
        // Deliberately lean: revision + generation metadata only. The client's
        // heartbeat handler uses exactly these fields; no snapshot payload.
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
            tx.persisted = true;
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

    return withLock(req, scope, async (state, tx) => {
        if (hasOp(state, opId)) {
            return res.json({ ok: true, state: publicState(state), duplicate: true });
        }
        if (expireGeneration(state)) {
            const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [recovery]);
            await persistState(req, scope, state);
            tx.persisted = true;
            publishPreparedEvent(req, scope, recovery);
        }
        if (state.generation) {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) {
            return res.status(409).json(revisionError(state));
        }

        // Prepare the event fully before any mutation. A failed prepare
        // consumes no event id and changes nothing.
        const newRevision = state.revision + 1;
        const prepared = prepareEvent(state, {
            type: 'snapshot',
            revision: newRevision,
            snapshot: snap,
            sourceClientId: member.clientId,
        }, { opId });

        state.snapshot = snap;
        state.revision = newRevision;
        state.updatedAt = now();
        commitPreparedEvents(state, [prepared]);

        await persistState(req, scope, state);
        tx.persisted = true;
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

    return withLock(req, scope, async (state, tx) => {
        if (hasOp(state, opId)) {
            return res.json({ ok: true, state: publicState(state), duplicate: true });
        }
        if (state.generation) {
            const expired = expireGeneration(state);
            if (expired) {
                const recovery = prepareEvent(state, { type: 'generation_recovered', generation: null });
                commitPreparedEvents(state, [recovery]);
                await persistState(req, scope, state);
                tx.persisted = true;
                publishPreparedEvent(req, scope, recovery);
            }
        }
        if (state.generation) {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) {
            return res.status(409).json(revisionError(state));
        }
        if (bytes(snap) > LIMITS.maxSnapshotBytes) {
            return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
        }

        const newRevision = state.revision + 1;
        const generation = makeGeneration(body, serverInstanceId);

        // Both events prepared together with sequential ids; either both
        // commit or neither does.
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
            },
        ]);

        state.snapshot = snap;
        state.revision = newRevision;
        state.updatedAt = now();
        state.generation = generation;
        commitPreparedEvents(state, [snapshotEvent, claimEvent]);

        await persistState(req, scope, state);
        tx.persisted = true;
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
            return res.json({
                ok: true,
                state: publicState(state),
                stopRequested: !!g.stopRequested,
            });
        }

        if (kind === 'started') {
            // Idempotent: a retried start after a lost response must not
            // produce a second generation_started event.
            if (['started', 'streaming'].includes(g.phase)) {
                return res.json({ ok: true, state: publicState(state), duplicate: true });
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
            tx.persisted = true;
            publishPreparedEvent(req, scope, prepared);
            return res.json({ ok: true, state: publicState(state) });
        }

        if (kind === 'stream') {
            if (!['started', 'streaming'].includes(g.phase)) {
                return res.status(409).json({ ok: false, error: 'generation_not_started' });
            }
            const seq = Number(body.seq);
            if (!Number.isInteger(seq)) {
                return res.status(400).json({ ok: false, error: 'invalid_sequence' });
            }
            // Idempotent same-seq retry: a timed-out accepted update returns
            // the current state instead of corrupting the sequence.
            if (seq === g.seq) {
                const sameMessageId = messageIdFromMessage(body.message) === g.messageId;
                if (sameMessageId) {
                    return res.json({ ok: true, state: publicState(state), stopRequested: !!g.stopRequested, duplicate: true });
                }
                return res.status(409).json({ ok: false, error: 'stream_sequence_conflict', expected: g.seq + 1 });
            }
            if (seq !== g.seq + 1) {
                return res.status(409).json({ ok: false, error: 'stream_sequence_conflict', expected: g.seq + 1 });
            }

            const message = clone(body.message);
            if (!isObject(message)) {
                return res.status(400).json({ ok: false, error: 'stream_message_required' });
            }
            const id = message?.extra?.multi_client_sync?.messageId;
            if (!jsonSafeId(String(id || ''))) {
                return res.status(400).json({ ok: false, error: 'message_ids_required' });
            }
            const messageIndex = Number.isInteger(body.messageIndex) ? body.messageIndex : null;

            // The event's generation metadata must reflect the POST-update
            // state (phase/seq/messageId/messageIndex), built without mutating
            // g so a failed prepare changes nothing.
            const updatedPublic = generationPublic(g, false);
            updatedPublic.phase = 'streaming';
            updatedPublic.seq = seq;
            updatedPublic.messageId = id;
            updatedPublic.messageIndex = messageIndex;

            const prepared = prepareEvent(state, {
                type: 'generation_stream',
                generation: updatedPublic,
                messageIndex,
                seq,
                message,
            });

            g.phase = 'streaming';
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            g.seq = seq;
            g.messageId = id;
            g.messageIndex = messageIndex;
            g.message = message;
            state.updatedAt = now();

            commitPreparedEvents(state, [prepared]);
            await persistState(req, scope, state);
            tx.persisted = true;
            publishPreparedEvent(req, scope, prepared);
            return res.json({ ok: true, state: publicState(state), stopRequested: !!g.stopRequested });
        }

        if (kind === 'terminal') {
            const opId = String(body.opId || '');
            if (!jsonSafeId(opId)) return res.status(400).json({ ok: false, error: 'invalid_op_id' });
            if (hasOp(state, opId)) {
                return res.json({ ok: true, state: publicState(state), duplicate: true });
            }

            let snap;
            try { snap = canonicalSnapshot(body.snapshot); } catch (error) {
                return res.status(400).json({ ok: false, error: error.message });
            }
            if (bytes(snap) > LIMITS.maxSnapshotBytes) {
                return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
            }

            const newRevision = state.revision + 1;
            const finished = generationPublic(g, false);
            finished.phase = String(body.phase || 'completed');

            const prepared = prepareEvent(state, {
                type: 'generation_terminal',
                generation: finished,
                revision: newRevision,
                snapshot: snap,
            }, { opId });

            state.snapshot = snap;
            state.revision = newRevision;
            state.updatedAt = now();
            state.generation = null;
            commitPreparedEvents(state, [prepared]);

            await persistState(req, scope, state);
            tx.persisted = true;
            publishPreparedEvent(req, scope, prepared);
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
    return withLock(req, scope, async (state, tx) => {
        if (opId && hasOp(state, opId)) {
            return res.json({ ok: true, state: publicState(state), duplicate: true });
        }
        if (expireGeneration(state)) {
            const recovered = prepareEvent(state, { type: 'generation_recovered', generation: null });
            commitPreparedEvents(state, [recovered]);
            await persistState(req, scope, state);
            tx.persisted = true;
            publishPreparedEvent(req, scope, recovered);
        }
        if (!state.generation) {
            return res.json({ ok: true, state: publicState(state), alreadyStopped: true });
        }
        state.generation.stopRequested = true;
        state.updatedAt = now();
        // Stop events never carry the giant live message.
        const prepared = prepareEvent(state, {
            type: 'generation_stop_requested',
            generation: generationPublic(state.generation, false),
            requesterClientId: member.clientId,
        }, { opId: opId || null });
        commitPreparedEvents(state, [prepared]);
        await persistState(req, scope, state);
        tx.persisted = true;
        publishPreparedEvent(req, scope, prepared);
        return res.json({ ok: true, state: publicState(state) });
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

    // The explicit query cursor reflects the client's accepted logical cursor
    // at connect time and wins over the browser's Last-Event-ID header (which
    // may be ahead of it mid-chunked-event).
    const lastId = Number(req.query?.lastEventId || req.get('last-event-id') || 0);

    res.status(200);
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache, no-transform');
    res.setHeader('Connection', 'keep-alive');
    res.flushHeaders?.();

    const existing = set.get(clientId);
    const member = existing?.member && existing.member.deviceId === deviceId
        ? existing.member
        : { clientId, deviceId, joinedAt: now() };
    member.lastSeenAt = now();

    const sub = createSubscriber(res, member);

    // Capture the replay plan AND the hello snapshot data under the lock, then
    // register the subscriber. Everything committed before this moment is in
    // the captured data; everything after is buffered while replaying. No gap,
    // no duplicates, and hello cannot race a concurrent commit.
    const release = await lockFor(skey);
    let replayEvents = null;
    let needResync = false;
    let helloBase = null;
    try {
        const state = await loadState(req, scope);
        const oldest = state.events[0]?.id || state.nextEventId;

        helloBase = {
            revision: state.revision,
            lastEventId: state.nextEventId - 1,
            generationMeta: generationPublic(state.generation, false),
            generationFull: generationPublic(state.generation, true),
            scope: clone(scope),
            members: publicMembers(req, scope),
        };

        if (Number.isInteger(lastId) && lastId > 0) {
            if (lastId < oldest - 1) {
                needResync = true;
            } else {
                replayEvents = [];
                for (const event of state.events) {
                    if (event.id <= lastId) continue;
                    if (event.type === 'generation_stream') continue; // transient: live state comes via generation_state
                    if (event.type === 'event_chunked') { needResync = true; replayEvents = null; break; }
                    replayEvents.push(clone(event));
                }
            }
        }
        if (!needResync) set.set(clientId, sub);
    } catch {
        release();
        try { res.end(); } catch { /* ignore */ }
        return;
    }
    release();

    // Dummy state: prepareEvent with an explicit id never reads nextEventId.
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

        // hello stays small: generation metadata only.
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

        // Full current generation (including the live message) follows via a
        // transient generation_state transfer; chunked if large.
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

    // Replay finished: deliver anything buffered during it, then go live.
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
