'use strict';

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const crypto = require('crypto');

const PROTOCOL = 10;
const SCHEMA = 10;
const PLUGIN_ID = 'multi-client-sync';

const LIMITS = Object.freeze({
    maxSnapshotBytes: 12 * 1024 * 1024,
    maxEventBytes: 512 * 1024,
    maxEvents: 300,
    maxRecentOps: 500,
    memberTtlMs: 60_000,
    heartbeatMinMs: 3_000,
    generationLeaseMs: 30_000,
    generationMaxMs: 30 * 60_000,
    maxScopesPerUser: 200,
    maxSubscribersPerScope: 25,
});

const scopes = new Map();
const userLocks = new Map();
const subscribers = new Map();
let routerRef = null;
let serverInstanceId = null;

function now() { return Date.now(); }
function clone(value) { return value === undefined ? undefined : JSON.parse(JSON.stringify(value)); }
function bytes(value) { return Buffer.byteLength(JSON.stringify(value ?? null), 'utf8'); }
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
    return [scope.kind, scope.ownerId, scope.chatId, scope.branchId || ''].join('|');
}
function validateScope(scope) {
    if (!isObject(scope)) return 'invalid_scope';
    if (!['character', 'group'].includes(scope.kind)) return 'invalid_scope_kind';
    for (const field of ['ownerId', 'chatId']) {
        const value = String(scope[field] ?? '');
        if (!value || value.length > 500 || value.includes('\0') || value.includes('/') || value.includes('\\')) return `invalid_scope_${field}`;
    }
    if (scope.branchId != null) {
        const value = String(scope.branchId);
        if (value.length > 500 || value.includes('\0') || value.includes('/') || value.includes('\\')) return 'invalid_scope_branch';
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
    if (entry?.state) return entry.state;
    if (entry?.loading) return entry.loading;

    const loading = (async () => {
        let state = defaultState(scope);
        try {
            const raw = await fsp.readFile(statePath(req, scope), 'utf8');
            const parsed = JSON.parse(raw);
            if (parsed?.protocol === PROTOCOL && parsed?.schema === SCHEMA && parsed?.scope) {
                state = { ...state, ...parsed, scope: clone(scope) };
            }
        } catch (error) {
            if (error?.code !== 'ENOENT') throw error;
        }
        if (state.generation) {
            // A generation owned by a previous server process cannot safely be resumed.
            state.generation = null;
        }
        state.updatedAt = now();
        const freshEntry = scopes.get(key) || {};
        freshEntry.state = state;
        freshEntry.loading = null;
        scopes.set(key, freshEntry);
        return state;
    })();

    scopes.set(key, { ...(entry || {}), loading });
    return loading;
}
async function persistState(req, scope, state) {
    const file = statePath(req, scope);
    await ensureDir(path.dirname(file));
    const projected = clone(state);
    projected.updatedAt = now();
    const payload = JSON.stringify(projected);
    if (Buffer.byteLength(payload, 'utf8') > LIMITS.maxSnapshotBytes + 2 * 1024 * 1024) {
        throw Object.assign(new Error('state_too_large'), { code: 'state_too_large' });
    }
    const tmp = `${file}.${process.pid}.${crypto.randomBytes(6).toString('hex')}.tmp`;
    await fsp.writeFile(tmp, payload, { mode: 0o600 });
    await fsp.rename(tmp, file);
    try { await fsp.chmod(file, 0o600); } catch { /* best effort */ }
    state.updatedAt = projected.updatedAt;
}
function lockFor(key) {
    const previous = userLocks.get(key) || Promise.resolve();
    let release;
    const current = new Promise(resolve => { release = resolve; });
    const chain = previous.catch(() => {}).then(() => current);
    userLocks.set(key, chain);
    return previous.catch(() => {}).then(() => release);
}
async function withLock(req, scope, fn) {
    const release = await lockFor(`${userKey(req)}::${scopeKey(scope)}`);
    try {
        const state = await loadState(req, scope);
        return await fn(state);
    } finally {
        release();
    }
}
function activeMembers(req, scope) {
    const map = subscribers.get(`${userKey(req)}::${scopeKey(scope)}`);
    if (!map) return [];
    return [...map.values()].map(x => x.member);
}
function isMember(req, scope, clientId, deviceId) {
    const map = subscribers.get(`${userKey(req)}::${scopeKey(scope)}`);
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
function rememberOp(state, opId) {
    if (!opId) return;
    state.recentOps.push(opId);
    if (state.recentOps.length > LIMITS.maxRecentOps) state.recentOps.splice(0, state.recentOps.length - LIMITS.maxRecentOps);
}
function hasOp(state, opId) { return !!opId && state.recentOps.includes(opId); }
function revisionError(state) {
    return { ok: false, error: 'revision_conflict', revision: state.revision, snapshot: clone(state.snapshot), generation: clone(state.generation) };
}
function bumpRevision(state) { state.revision += 1; state.updatedAt = now(); }
function pushEvent(state, event) {
    const stored = { ...clone(event), id: state.nextEventId++, at: now() };
    if (stored.type === 'generation_stream') {
        delete stored.message;
        stored.compacted = true;
    }
    if (bytes(stored) > LIMITS.maxEventBytes) throw new Error('event_too_large');
    state.events.push(stored);
    if (state.events.length > LIMITS.maxEvents) state.events.splice(0, state.events.length - LIMITS.maxEvents);
    if (stored.type === 'generation_stream') {
        let streamCount = 0;
        for (let i = state.events.length - 1; i >= 0; i--) {
            if (state.events[i]?.type !== 'generation_stream') continue;
            streamCount += 1;
            if (streamCount > 32) state.events.splice(i, 1);
        }
    }
    return stored;
}
function sendSse(res, event, id = null) {
    if (id != null) res.write(`id: ${id}\n`);
    res.write(`event: ${String(event.type || 'message')}\n`);
    res.write(`data: ${JSON.stringify(event)}\n\n`);
}
function publish(req, scope, event) {
    const set = subscribers.get(`${userKey(req)}::${scopeKey(scope)}`) || new Map();
    for (const sub of set.values()) {
        try { sendSse(sub.res, event, event.id); } catch { /* closed response */ }
    }
}
function publicState(state) {
    return {
        protocol: state.protocol,
        schema: state.schema,
        scope: clone(state.scope),
        revision: state.revision,
        snapshot: clone(state.snapshot),
        generation: clone(state.generation),
        updatedAt: state.updatedAt,
    };
}
function generationPublic(g) {
    return g ? {
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
        message: g.message ? clone(g.message) : null,
        stopRequested: !!g.stopRequested,
    } : null;
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
    return !!g && g.clientId === String(body.clientId) && g.deviceId === String(body.deviceId) && g.generationId === String(body.generationId);
}
function publicMembers(req, scope) {
    return activeMembers(req, scope).map(member => ({
        clientId: member.clientId,
        deviceId: member.deviceId,
        lastSeenAt: member.lastSeenAt,
    }));
}

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
    if (!jsonSafeId(clientId) || !jsonSafeId(deviceId)) return res.status(400).json({ ok: false, error: 'invalid_client' });

    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    let set = subscribers.get(skey);
    if (!set) { set = new Map(); subscribers.set(skey, set); }
    if (set.size > LIMITS.maxSubscribersPerScope && !set.has(clientId)) return res.status(429).json({ ok: false, error: 'too_many_clients' });

    const existing = set.get(clientId)?.member;
    if (existing && existing.deviceId !== deviceId && now() - existing.lastSeenAt <= LIMITS.memberTtlMs) {
        return res.status(409).json({ ok: false, error: 'client_id_in_use' });
    }

    const release = await lockFor(skey);
    try {
        const state = await loadState(req, scope);
        if (state.revision === 0 && body.snapshot) {
            try {
                state.snapshot = canonicalSnapshot(body.snapshot);
            } catch (e) {
                return res.status(400).json({ ok: false, error: e.message });
            }
            if (bytes(state.snapshot) > LIMITS.maxSnapshotBytes) return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
            await persistState(req, scope, state);
        }
        set.set(clientId, {
            member: { clientId, deviceId, joinedAt: now(), lastSeenAt: now() },
            res: null,
        });
        const payload = { ok: true, state: publicState(state), members: publicMembers(req, scope) };
        return res.json(payload);
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
        const member = set.get(String(body.clientId || ''))?.member;
        if (member?.deviceId === String(body.deviceId || '')) set.delete(String(body.clientId || ''));
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
    if (!entry || entry.member.deviceId !== deviceId) return res.status(403).json({ ok: false, error: 'not_member' });
    if (entry.member.lastHeartbeat && now() - entry.member.lastHeartbeat < LIMITS.heartbeatMinMs) return res.json({ ok: true });
    entry.member.lastSeenAt = now();
    entry.member.lastHeartbeat = now();
    return withLock(req, scope, async state => {
        if (expireGeneration(state)) {
            const event = pushEvent(state, { type: 'generation_recovered', generation: null });
            await persistState(req, scope, state);
            publish(req, scope, event);
        }
        return res.json({ ok: true, revision: state.revision, generation: generationPublic(state.generation) });
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
    return withLock(req, scope, async state => {
        if (expireGeneration(state)) {
            const event = pushEvent(state, { type: 'generation_recovered', generation: null });
            await persistState(req, scope, state);
            publish(req, scope, event);
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
    try { snap = canonicalSnapshot(body.snapshot); } catch (e) { return res.status(400).json({ ok: false, error: e.message }); }
    if (bytes(snap) > LIMITS.maxSnapshotBytes) return res.status(413).json({ ok: false, error: 'snapshot_too_large' });

    return withLock(req, scope, async state => {
        if (hasOp(state, opId)) return res.json({ ok: true, state: publicState(state), duplicate: true });
        if (expireGeneration(state)) {
            const recoveryEvent = pushEvent(state, { type: 'generation_recovered', generation: null });
            publish(req, scope, recoveryEvent);
        }
        if (state.generation && state.generation.phase === 'streaming') {
            return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        }
        if (Number(body.baseRevision) !== state.revision) return res.status(409).json(revisionError(state));

        state.snapshot = snap;
        bumpRevision(state);
        rememberOp(state, opId);
        const event = pushEvent(state, { type: 'snapshot', revision: state.revision, snapshot: snap, sourceClientId: member.clientId });
        await persistState(req, scope, state);
        publish(req, scope, event);
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
    try { snap = canonicalSnapshot(body.snapshot); } catch (e) { return res.status(400).json({ ok: false, error: e.message }); }

    return withLock(req, scope, async state => {
        if (hasOp(state, opId)) return res.json({ ok: true, state: publicState(state), duplicate: true });
        let expired = false;
        if (state.generation) {
            expired = expireGeneration(state);
            if (expired) {
                const event = pushEvent(state, { type: 'generation_recovered', generation: null });
                publish(req, scope, event);
            }
        }
        if (state.generation) return res.status(409).json({ ok: false, error: 'generation_active', state: publicState(state) });
        if (Number(body.baseRevision) !== state.revision) return res.status(409).json(revisionError(state));
        if (bytes(snap) > LIMITS.maxSnapshotBytes) return res.status(413).json({ ok: false, error: 'snapshot_too_large' });

        state.snapshot = snap;
        bumpRevision(state);
        const generation = makeGeneration(body, serverInstanceId);
        state.generation = generation;
        rememberOp(state, opId);

        const snapshotEvent = pushEvent(state, {
            type: 'snapshot', revision: state.revision, snapshot: snap, sourceClientId: member.clientId, generationId: generation.generationId,
        });
        const claimEvent = pushEvent(state, { type: 'generation_claimed', generation: generationPublic(generation), revision: state.revision });
        await persistState(req, scope, state);
        publish(req, scope, snapshotEvent);
        publish(req, scope, claimEvent);
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

    return withLock(req, scope, async state => {
        if (!state.generation || !generationOwner(state.generation, body)) return res.status(409).json({ ok: false, error: 'generation_not_owned', state: publicState(state) });
        if (expireGeneration(state)) return res.status(409).json({ ok: false, error: 'generation_expired', state: publicState(state) });
        const g = state.generation;

        if (kind === 'heartbeat') {
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            await persistState(req, scope, state);
            return res.json({ ok: true, state: publicState(state) });
        }

        if (kind === 'started') {
            g.phase = 'started';
            g.startedAt = g.startedAt || now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            const event = pushEvent(state, { type: 'generation_started', generation: generationPublic(g) });
            await persistState(req, scope, state);
            publish(req, scope, event);
            return res.json({ ok: true, state: publicState(state) });
        }

        if (kind === 'stream') {
            if (!['started', 'streaming'].includes(g.phase)) return res.status(409).json({ ok: false, error: 'generation_not_started' });
            const seq = Number(body.seq);
            if (!Number.isInteger(seq) || seq !== g.seq + 1) return res.status(409).json({ ok: false, error: 'stream_sequence_conflict', expected: g.seq + 1 });
            const message = clone(body.message);
            if (!isObject(message)) return res.status(400).json({ ok: false, error: 'stream_message_required' });
            const id = message?.extra?.multi_client_sync?.messageId;
            if (!jsonSafeId(String(id || ''))) return res.status(400).json({ ok: false, error: 'message_ids_required' });
            g.phase = 'streaming';
            g.lastHeartbeat = now();
            g.leaseUntil = now() + LIMITS.generationLeaseMs;
            g.seq = seq;
            g.messageId = id;
            g.messageIndex = Number.isInteger(body.messageIndex) ? body.messageIndex : null;
            g.message = message;
            const live = pushEvent(state, {
                type: 'generation_stream', generation: generationPublic(g), message, messageIndex: g.messageIndex, seq,
            });
            await persistState(req, scope, state);
            publish(req, scope, { ...live, message });
            return res.json({ ok: true, state: publicState(state) });
        }

        if (kind === 'terminal') {
            const snap = canonicalSnapshot(body.snapshot);
            if (bytes(snap) > LIMITS.maxSnapshotBytes) return res.status(413).json({ ok: false, error: 'snapshot_too_large' });
            state.snapshot = snap;
            bumpRevision(state);
            const finished = generationPublic(g);
            finished.phase = String(body.phase || 'completed');
            const event = pushEvent(state, { type: 'generation_terminal', generation: { ...finished, message: clone(g.message) }, revision: state.revision, snapshot: snap });
            state.generation = null;
            await persistState(req, scope, state);
            publish(req, scope, event);
            return res.json({ ok: true, state: publicState(state) });
        }

        return res.status(400).json({ ok: false, error: 'unknown_generation_update' });
    });
}

async function handleGenerationStopRequest(req, res) {
    if (!requireAuth(req, res)) return;
    const body = req.body || {};
    const scope = body.scope;
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).json({ ok: false, error: scopeError });
    const member = requireMember(req, res, scope, body);
    if (!member) return;
    return withLock(req, scope, async state => {
        if (expireGeneration(state)) {
            const recovered = pushEvent(state, { type: 'generation_recovered', generation: null });
            await persistState(req, scope, state);
            publish(req, scope, recovered);
        }
        if (!state.generation) return res.json({ ok: true, state: publicState(state), alreadyStopped: true });
        state.generation.stopRequested = true;
        const event = pushEvent(state, { type: 'generation_stop_requested', generation: generationPublic(state.generation), requesterClientId: member.clientId });
        await persistState(req, scope, state);
        publish(req, scope, event);
        return res.json({ ok: true, state: publicState(state) });
    });
}

async function handleSse(req, res) {
    if (!req?.user) return res.status(401).end();
    let scope;
    try {
        scope = JSON.parse(Buffer.from(String(req.query?.scope || ''), 'base64url').toString('utf8'));
    } catch {
        return res.status(400).end();
    }
    const scopeError = validateScope(scope);
    if (scopeError) return res.status(400).end();
    const clientId = String(req.query?.clientId || '');
    const deviceId = String(req.query?.deviceId || '');
    if (!jsonSafeId(clientId) || !jsonSafeId(deviceId)) return res.status(400).end();
    if (!isMember(req, scope, clientId, deviceId)) return res.status(403).end();

    const state = await loadState(req, scope);
    const skey = `${userKey(req)}::${scopeKey(scope)}`;
    let set = subscribers.get(skey);
    if (!set) { set = new Map(); subscribers.set(skey, set); }
    if (set.size >= LIMITS.maxSubscribersPerScope && !set.has(clientId)) return res.status(429).end();

    res.status(200);
    res.setHeader('Content-Type', 'text/event-stream');
    res.setHeader('Cache-Control', 'no-cache, no-transform');
    res.setHeader('Connection', 'keep-alive');
    res.flushHeaders?.();

    const lastId = Number(req.get('last-event-id') || req.query?.lastEventId || 0);
    sendSse(res, {
        type: 'hello', protocol: PROTOCOL, schema: SCHEMA, revision: state.revision, generation: generationPublic(state.generation), scope: clone(scope), members: publicMembers(req, scope),
    });

    if (Number.isInteger(lastId) && lastId > 0) {
        const oldest = state.events[0]?.id || state.nextEventId;
        if (lastId < oldest - 1) {
            sendSse(res, { type: 'resync_required', revision: state.revision });
        } else {
            for (const event of state.events) if (event.id > lastId) sendSse(res, event, event.id);
            sendSse(res, { type: 'replay_complete', revision: state.revision });
        }
    }

    const member = set.get(clientId)?.member;
    if (member && member.deviceId === deviceId) member.lastSeenAt = now();
    const sub = { res, member: { clientId, deviceId } };
    set.set(clientId, sub);

    const timer = setInterval(() => {
        try { res.write(': keepalive\n\n'); } catch { clearInterval(timer); }
    }, 15_000);
    req.on('close', () => {
        clearInterval(timer);
        const current = set.get(clientId);
        if (current?.res === res) {
            set.set(clientId, { ...current, res: null });
        }
    });
}

async function handleRoute(req, res) {
    const route = req.path || req.url?.split('?')[0] || '';
    try {
        if (route === '/ping' && req.method === 'GET') return handlePing(req, res);
        if (route === '/join' && req.method === 'POST') return handleJoin(req, res);
        if (route === '/leave' && req.method === 'POST') return handleLeave(req, res);
        if (route === '/heartbeat' && req.method === 'POST') return handleHeartbeat(req, res);
        if (route === '/state' && req.method === 'POST') return handleState(req, res);
        if (route === '/snapshot' && req.method === 'POST') return handleSnapshot(req, res);
        if (route === '/generation/claim' && req.method === 'POST') return handleGenerationClaim(req, res);
        if (route === '/generation/heartbeat' && req.method === 'POST') return handleGenerationUpdate(req, res, 'heartbeat');
        if (route === '/generation/started' && req.method === 'POST') return handleGenerationUpdate(req, res, 'started');
        if (route === '/generation/stream' && req.method === 'POST') return handleGenerationUpdate(req, res, 'stream');
        if (route === '/generation/terminal' && req.method === 'POST') return handleGenerationUpdate(req, res, 'terminal');
        if (route === '/generation/stop' && req.method === 'POST') return handleGenerationStopRequest(req, res);
        if (route === '/events' && req.method === 'GET') return handleSse(req, res);
        return res.status(404).json({ ok: false, error: 'not_found' });
    } catch (error) {
        console.error('[multi-client-sync] route error', error);
        if (!res.headersSent) return res.status(500).json({ ok: false, error: 'server_error' });
    }
}

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