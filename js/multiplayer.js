/*
 * n-gon multiplayer v8.1  (permission-based joins/invites + UI polish; v6 + support for the newer n-gon: training, checkpoints, level editor/pool, local levels)
 *
 * Design
 *  - Every client runs its OWN player, guns, techs and fields with the game's normal code.
 *  - Other players are lightweight "ghost" mobs (interpolated), so every existing bullet,
 *    explosion or laser that damages mobs automatically supports PvP.
 *  - Other players' bullets are streamed as generic shapes (visual only).
 *  - Mobs are simulated by one host. Other clients get puppets that are position-interpolated;
 *    damage they deal is forwarded to the host.
 *  - Any number of players can join (full mesh, late join supported, in any join order).
 *
 * v4 features (kept)
 *  - MAP SYNC: every level is built from a seed derived from (run seed + level number) with Math.random swapped
 *    for the shared seeded generator, so every player builds the IDENTICAL level.
 *  - PAUSE / UPGRADE SCREEN: a paused player is shown to the others as a faded, invulnerable ghost that falls to
 *    the ground instead of floating, and mobs ignore it.
 *  - simulation.cycle is nudged towards the host's so cycle-driven moving platforms stay in sync.
 *  - Late join works whichever player has the smaller id.
 *
 * v5 features (kept)
 *  - Level buttons are host-authoritative and account for every connected player's ghost position.
 *  - Guests no longer create runtime enemies independently; the host replicates enemy spawn/death events.
 *  - Enemy roster reconciliation compares stable mob IDs, not only enemy counts.
 *  - Host snapshots include shared level bodies, including static doors moved with setPosition().
 *  - Level custom-layer random effects use a per-run/per-level/per-cycle deterministic stream.
 *
 * v6 (this version): the two sets of features now work together
 *  - The player you joined stays the session host (v5), BUT if the host pauses / opens the upgrade screen / hides the
 *    tab for more than half a second, the host role moves to a non-paused player, so one player can no longer freeze
 *    the mobs, doors and buttons for everybody. It moves back as soon as the preferred host is active again.
 *  - Host messages are accepted from whoever is the current host, so role changes never drop packets.
 *  - A new host re-publishes all button states so doors don't get stuck after a hand-over.
 *
 * v7: support for newer n-gon builds (written from the new index.html; every new hook is feature-detected,
 *     run ngonMP.diag() in the console to see which hooks were found in your build)
 *  - Training mode is a private solo run: nothing is synced and nobody else is pulled into it.
 *  - Checkpoints (continue / import file / import code): only the host can load one; guests are told so. When the host
 *    finishes loading, everybody restarts from the same seed and catches up to the same level ("resync").
 *  - Level editor is blocked while connected (local levels differ per player).
 *  - Level pool / local levels: the host sends which level it is on; a player whose level order differs gets a warning.
 *  - level.start() may now finish asynchronously (local levels with code): the shared seeding and "level built" step
 *    wait for it to finish.
 *  - Moving/breaking level geometry is synced generically: every static map body gets an id, the host streams the
 *    ones that move (doors, platforms, lifts from any level element) and which ones were destroyed, so levels built
 *    by the new level-elements system stay in sync even if its API differs from the old level.button().
 *  - The cycle nudge is skipped when players use different "limit frames per second" settings.
 */
(function () {
    'use strict';
    if (window.__ngonMP) return;
    window.__ngonMP = true;

    const DEBUG = false;
    const CFG = {
        tickMs: 50,          // network send rate (20 Hz)
        interpMs: 100,       // render delay for interpolation
        maxBullets: 150,
        pvpScale: 0.01,
        syncCycle: true,     // keep simulation.cycle close to the host (moving platforms etc.)
        staleMs: 1500,       // no state packet for this long => treat peer as paused
        hostPauseMs: 500,    // a player must be paused this long before the host role moves away from them
        peerjsSrc: 'https://unpkg.com/peerjs@1.5.4/dist/peerjs.min.js',
    };
    const NOOP = function () { };
    const SKIP_SPAWN = /^(mapRect|mapVertex|mapRectNow|mapVertexNow|bodyRect|bodyVertex|bodyRectCorner|debris|pickList|fullPickList|setMobTypeSpawnOrder|setSpawnList|randomizeSpawnList|dmg\w*|mobDmg\w*|props\w*|spawnBuilding|spawnStairs|addResearchToLevel|sandPaper)$/;
    const PUPPET_NOOPS = ['locatePlayer', 'seePlayerCheck', 'seePlayerByLookingAt', 'seePlayerByHistory', 'seePlayerCheckByDistance', 'seePlayerByDistOrLOS', 'alwaysSeePlayer', 'alertNearByMobs', 'attraction', 'repulsion', 'gravity'];

    // ---- helpers (NOTE: never use Math.random here, n-gon seeds it and we must not disturb the RNG) ----
    const q = (v, k = 1) => Number.isFinite(v) ? Math.round(v * k) : 0;
    const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
    const now = () => performance.now();
    const log = (...a) => { if (DEBUG) console.log('[MP]', ...a); };
    function lerpAngle(a, b2, t) { let d = b2 - a; while (d > Math.PI) d -= 2 * Math.PI; while (d < -Math.PI) d += 2 * Math.PI; return a + d * t; }
    function sample(buf, t) {
        const n = buf.length; if (!n) return null;
        if (t <= buf[0].t) return buf[0];
        for (let i = 0; i < n - 1; i++) {
            const A = buf[i], B = buf[i + 1];
            if (t >= A.t && t <= B.t) {
                const k = (t - A.t) / Math.max(1, B.t - A.t);
                return { x: A.x + (B.x - A.x) * k, y: A.y + (B.y - A.y) * k, vx: B.vx, vy: B.vy, a: lerpAngle(A.a, B.a, k) };
            }
        }
        const L = buf[n - 1]; const fr = Math.max(0, Math.min(8, (t - L.t) / 16.7));
        return { x: L.x + L.vx * fr, y: L.y + L.vy * fr, vx: L.vx, vy: L.vy, a: L.a };
    }

    const rnd = () => crypto.getRandomValues(new Uint32Array(1))[0];
    const errCount = {};
    function guard(name, fn) {
        return function () {
            if ((errCount[name] | 0) >= 500) return undefined;
            try { return fn.apply(this, arguments); }
            catch (e) {
                const n = errCount[name] = (errCount[name] | 0) + 1;
                if (n <= 3) console.warn('[MP] error in ' + name + ':', e);
                if (n === 500) console.warn('[MP] ' + name + ' switched off after repeated errors');
                return undefined;
            }
        };
    }
    const HOOKS = {};   // label -> true/false (was the function found in this n-gon build?)  see ngonMP.diag()
    function wrapFn(obj, key, label, make) {
        const orig = obj && obj[key];
        if (typeof orig !== 'function') { HOOKS[label] = false; console.warn('[MP] ' + label + ' not found in this build - that part of the mod is skipped'); return false; }
        if (orig._mpw) return true;
        HOOKS[label] = true;
        const w = make(orig); w._mpw = true; obj[key] = w; return true;
    }

    const NEEDED = ['simulation', 'level', 'm', 'mobs', 'spawn', 'Matter', 'b', 'engine', 'cat', 'mob', 'body', 'bullet', 'powerUp', 'powerUps', 'map', 'ctx'];
    function missingGlobals() {
        return NEEDED.filter(n => { try { return (0, eval)('typeof ' + n) === 'undefined'; } catch (e) { return false; } });
    }
    function whenReady(cb) {
        let tries = 0;
        const t = setInterval(() => {
            tries++;
            const miss = missingGlobals();
            if (!miss.length) { clearInterval(t); cb(); }
            else if (tries === 100) console.warn('[MP] still waiting for the game to load, missing: ' + miss.join(', '));
        }, 200);
    }
    function loadPeer(cb) {
        if (typeof Peer !== 'undefined') return cb();
        const s = document.createElement('script'); s.src = CFG.peerjsSrc; s.onload = cb;
        s.onerror = () => console.error('[MP] failed to load PeerJS (blocked by an extension or network?)'); document.head.appendChild(s);
    }

    function init() {
        const Body = Matter.Body, Composite = Matter.Composite, Bodies = Matter.Bodies;
        const LC = () => (level.levelsCleared | 0);

        const S = {
            id: null, hostId: null, sessionHostId: null, isHost: true,
            name: localStorage.getItem('p2pUsername') || 'player',
            peers: new Map(),
            together: true, pvp: true,
            inGame: false, loading: false, applying: false, replay: false, inPuppet: false,
            replayNew: [], grp: 0, ctr: 0, tickN: 0,
            aliveIds: null, mc: null,
            catchTarget: -1, catchRunning: false,
            runSeed: null, remotePending: false,
            paused: false, pausedAt: 0, stuck: 0, lastCycle: -1, hostCy: null,
            buttons: [], buttonSeq: 0, buttonSent: new Map(), remoteButtons: new Map(),
            buildingLevel: false, lastRosterAt: 0, lastButtonSnapshotAt: 0,
            solo: false, savePending: false, saveStarted: false, saveWatching: false, olWarned: -1, forceLv: null, forceFlip: null,
            mapIds: null, mapSent: new Map(), mapBase: new Map(),
        };
        const ghosts = new Map();       // peerId -> ghost mob
        const mobMap = new Map();       // netId -> mob
        const bodyMap = new Map();      // netId -> block
        const puMap = new Map();        // pid -> powerUp
        let spawnQ = [], deathQ = [], opsQ = [], dropQ = [];
        const dmgOut = new Map();       // netId -> [dmg, pierce]
        const pvpOut = new Map();       // peerId -> dmg

        // ------------------------------------------------------------------ networking
        const PREFIX = 'ngonmp-', LOBBY_ID = 'ngonmp_lobby_v1';
        const slug = s => String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 24);
        const sessionSuffix = () => {
            try {
                const bytes = new Uint8Array(8);
                crypto.getRandomValues(bytes);
                return Array.from(bytes, b => b.toString(16).padStart(2, '0')).join('');
            } catch (e) { return Math.random().toString(36).slice(2, 14); }
        };
        const idFor = (name, n) => PREFIX + (slug(name) || 'player') + '-' + sessionSuffix() + (n > 1 ? '-' + n : '');
        const validId = id => typeof id === 'string' && /^[\w-]{1,64}$/.test(id);
        const cleanName = s => String(s == null ? '' : s).replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, 20);
        let peer = null, peerGen = 0;
        S.baseName = cleanName(localStorage.getItem('p2pUsername')) || ('player' + (rnd() % 9000 + 1000));
        S.name = S.baseName;

        function openPeers() { const r = []; for (const p of S.peers.values()) if (p.ev && p.ev.open) r.push(p); return r; }
        function teardown() {
            S.tearing = true;
            try {
                for (const p of [...S.peers.values()]) {
                    try { removeGhost(p.id); } catch (e) { }
                    try { if (p.ev) p.ev.close(); } catch (e) { }
                    try { if (p.st) p.st.close(); } catch (e) { }
                }
                S.peers.clear();
                closeLobby();
                try { if (peer) peer.destroy(); } catch (e) { }
            } finally { S.tearing = false; }
            peer = null; S.id = null; S.hostId = null; S.sessionHostId = null; S.isHost = true; S.firstRole = undefined;
        }
        function startPeer(name) {
            const gen = ++peerGen;
            S.baseName = cleanName(name) || S.baseName;
            S.name = S.baseName;
            teardown();
            ui.status('connecting to network...');
            let attempt = 1, waited = false;
            const tryOpen = () => {
                if (gen !== peerGen) return;
                const p = new Peer(idFor(S.baseName, attempt), { debug: 1 });
                peer = p; let opened = false;
                p.on('open', id => {
                    if (gen !== peerGen) { try { p.destroy(); } catch (e) { } return; }
                    opened = true; S.id = id; S.hostId = id; S.sessionHostId = id; S.firstRole = undefined;
                    S.name = attempt > 1 ? S.baseName + ' ' + attempt : S.baseName;
                    ui.setId(id); ui.status('online as ' + S.name + (attempt > 1 ? ' (name was taken)' : ''));
                    refreshRole(); connectLobby();
                });
                p.on('connection', c => { if (c.label === 'lobby') { try { c.close(); } catch (e) { } return; } if (c.label === 'mp-control') { handleControl(c); return; } if (!approvedPeers.has(c.peer)) { try { c.close(); } catch (e) {} return; } attach(c, false); });
                p.on('error', e => {
                    if (gen !== peerGen) return;
                    const type = e && e.type;
                    if (type === 'unavailable-id' && !opened) {
                        try { p.destroy(); } catch (er) { }
                        if (!waited) { waited = true; setTimeout(tryOpen, 2500); }
                        else if (++attempt <= 20) tryOpen();
                        else ui.status('could not get a free name, pick another');
                        return;
                    }
                    if (type === 'peer-unavailable') { onUnavailable(e); return; }
                    ui.status('network: ' + (type || e));
                });
                p.on('disconnected', () => { if (gen === peerGen && !p.destroyed) { try { p.reconnect(); } catch (e) { } } });
            };
            tryOpen();
        }
        window.addEventListener('beforeunload', () => { try { closeLobby(); if (peer) peer.destroy(); } catch (e) { } });

        const pendingJoin = new Map();
        function joinByName(input) {
            input = String(input || '').trim(); if (!input) return;
            const lower = input.toLowerCase();
            let target = null;
            for (const u of dir.values()) if (u.name.toLowerCase() === lower || u.id === input) { target = u.id; break; }
            if (!target) target = /^ngonmp[-_]/i.test(input) ? input : idFor(input);
            if (target === S.id) { ui.status('that is you'); return; }
            requestJoin(target);
        }
        const controlPending = new Map();
        const approvedPeers = new Set();
        function sendControl(target, payload) {
            if (!peer || !S.id || !validId(target) || target === S.id) return;
            let c;
            try { c = peer.connect(target, { label: 'mp-control', reliable: true }); }
            catch (e) { ui.status('could not contact that player'); return; }
            const timer = setTimeout(() => { try { c.close(); } catch (e) {} }, 12000);
            c.on('open', () => { try { c.send({ ...payload, from: S.id, name: S.name }); } catch (e) {} });
            c.on('data', d => {
                if (!d || d.t !== 'control-result') return;
                clearTimeout(timer); try { c.close(); } catch (e) {}
                if (d.ok && payload.t === 'join-request') {
                    approvedPeers.add(target);
                    S.sessionHostId = target; S.hostId = target; S.isHost = false; S.firstRole = undefined;
                    ui.status('request accepted — connecting...'); connectTo(target);
                } else if (d.ok && payload.t === 'invite') {
                    approvedPeers.add(target);
                    ui.notify('Invitation sent', 'Waiting for ' + (payload.targetName || 'the player') + ' to respond.');
                } else if (!d.ok) ui.notify('Request declined', d.reason || 'The player declined the request.');
            });
            c.on('error', () => { clearTimeout(timer); ui.notify('Player unavailable', 'Could not reach that player.'); });
            c.on('close', () => clearTimeout(timer));
        }
        function requestJoin(target) {
            if (!target || target === S.id) return;
            ui.status('sending join request...');
            sendControl(target, { t: 'join-request' });
        }
        function invitePlayer(target, targetName) {
            if (!target || target === S.id) return;
            sendControl(target, { t: 'invite', targetName: targetName || 'player' });
            ui.status('sending invitation...');
        }
        function handleControl(c) {
            c.on('data', d => {
                if (!d || typeof d !== 'object') return;
                const from = String(d.from || c.peer || '');
                const who = cleanName(d.name) || 'A player';
                if (d.t === 'join-request' || d.t === 'invite') {
                    const isInvite = d.t === 'invite';
                    ui.notify(isInvite ? 'Multiplayer invitation' : 'Join request',
                        who + (isInvite ? ' invited you to play.' : ' wants to join your session.'),
                        () => {
                            approvedPeers.add(from);
                            try { c.send({ t: 'control-result', ok: true }); } catch (e) {}
                            if (isInvite) {
                                S.sessionHostId = from; S.hostId = from; S.isHost = false; S.firstRole = undefined;
                                ui.status('joining ' + who + '...'); connectTo(from);
                            }
                        },
                        () => { try { c.send({ t: 'control-result', ok: false, reason: 'The request was declined.' }); } catch (e) {} }
                    );
                }
            });
            c.on('error', () => {});
        }
        function onUnavailable(e) {
            const mt = /peer\s+(\S+)/.exec((e && e.message) || ''); const id = mt && mt[1];
            if (id === LOBBY_ID) { lobbyMissing(); return; }
            if (!id) { ui.status('player not found'); return; }
            const sp = S.peers.get(id); if (sp && !(sp.ev && sp.ev.open)) S.peers.delete(id);
            if (pendingJoin.has(id)) { const alt = pendingJoin.get(id); pendingJoin.delete(id); connectTo(alt); return; }
            ui.status('could not find "' + id.replace(PREFIX, '') + '" (are they online?)');
        }

        // ------------------------------------------------------------------ online directory (lobby)
        const dir = new Map();          // id -> {id,name,g,lc,n}
        let hub = null, hubConn = null, hubTimer = null, hubStarting = false, lastReg = '', lastRegAt = 0;
        const myInfo = () => ({ id: S.id, name: S.name, g: S.inGame ? 1 : 0, lc: LC(), n: openPeers().length });
        function setDir(list) {
            dir.clear();
            for (const e of list || []) {
                if (!Array.isArray(e) || !validId(e[0])) continue;
                dir.set(e[0], { id: e[0], name: cleanName(e[1]) || 'player', g: e[2] ? 1 : 0, lc: e[3] | 0, n: e[4] | 0 });
            }
            ui.refreshDir();
        }
        function connectLobby() {
            if (!peer || !S.id || hub) return;
            if (hubConn && hubConn.open) return;
            const gen = peerGen;
            let c;
            try { c = peer.connect(LOBBY_ID, { label: 'lobby', reliable: true }); } catch (e) { scheduleLobby(); return; }
            hubConn = c;
            c.on('open', () => { lastReg = ''; sendReg(); });
            c.on('data', d => { if (d && d.t === 'dir' && Array.isArray(d.l)) setDir(d.l); });
            c.on('close', () => { if (hubConn === c) { hubConn = null; if (gen === peerGen && !S.tearing) scheduleLobby(); } });
            c.on('error', () => { });
        }
        function scheduleLobby(ms) {
            clearTimeout(hubTimer);
            hubTimer = setTimeout(() => { if (S.id && !hub && !(hubConn && hubConn.open)) connectLobby(); }, ms != null ? ms : 1200 + rnd() % 1800);
        }
        function sendReg() {
            const info = myInfo(), key = [info.name, info.g, info.lc, info.n].join('|'), t = now();
            if (hub) { hub.set(info); return; }
            if (!hubConn || !hubConn.open) return;
            if (key === lastReg && t - lastRegAt < 5000) return;
            lastReg = key; lastRegAt = t;
            try { hubConn.send({ t: 'reg', name: info.name, g: info.g, lc: info.lc, n: info.n }); } catch (e) { }
        }
        function lobbyMissing() {
            hubConn = null;
            if (hub || hubStarting || !S.id || !peer) return;
            const gen = peerGen;
            let hp;
            hubStarting = true;
            try { hp = new Peer(LOBBY_ID, { debug: 0 }); } catch (e) { hubStarting = false; scheduleLobby(); return; }
            const users = new Map(), conns = new Map(); let dirty = false, timer = null, up = false;
            const api = {
                peer: hp,
                set(info) {
                    if (!info.id) return;
                    const o = users.get(info.id), k = o ? [o.name, o.g, o.lc, o.n].join('|') : '';
                    users.set(info.id, { ...info, t: now() });
                    if (k !== [info.name, info.g, info.lc, info.n].join('|')) dirty = true;
                },
                push() {
                    const l = [...users.values()].map(u => [u.id, u.name, u.g, u.lc, u.n]);
                    for (const c of conns.values()) { try { if (c.open) c.send({ t: 'dir', l }); } catch (e) { } }
                    setDir(l);
                },
                stop() { clearInterval(timer); try { hp.destroy(); } catch (e) { } if (hub === api) hub = null; }
            };
            hp.on('open', () => {
                if (gen !== peerGen) { try { hp.destroy(); } catch (e) { } return; }
                up = true; hubStarting = false; hub = api; clearTimeout(hubTimer);
                api.set(myInfo()); api.push();
                timer = setInterval(() => {
                    const t = now();
                    for (const [id, u] of users) if (id !== S.id && t - u.t > 20000) { users.delete(id); dirty = true; }
                    api.set(myInfo());
                    if (dirty) { dirty = false; api.push(); }
                }, 2000);
            });
            hp.on('connection', c => {
                conns.set(c.peer, c);
                c.on('data', d => {
                    if (!d || d.t !== 'reg') return;
                    api.set({ id: c.peer, name: cleanName(d.name) || 'player', g: d.g ? 1 : 0, lc: d.lc | 0, n: d.n | 0 });
                    if (dirty) { dirty = false; api.push(); }
                });
                c.on('close', () => { conns.delete(c.peer); if (users.delete(c.peer)) { dirty = false; api.push(); } });
                c.on('error', () => { });
                c.on('open', () => { try { c.send({ t: 'dir', l: [...users.values()].map(u => [u.id, u.name, u.g, u.lc, u.n]) }); } catch (e) { } });
            });
            hp.on('error', e => {
                if (!up) { hubStarting = false; try { hp.destroy(); } catch (er) { } if (gen === peerGen) scheduleLobby(300 + rnd() % 700); }
            });
            hp.on('disconnected', () => { try { if (!hp.destroyed) hp.reconnect(); } catch (e) { } });
            hp.on('close', () => { clearInterval(timer); hubStarting = false; if (hub === api) { hub = null; if (gen === peerGen && !S.tearing) scheduleLobby(); } });
        }
        function closeLobby() {
            clearTimeout(hubTimer);
            if (hub) { const h = hub; hub = null; h.stop(); }
            try { if (hubConn) hubConn.close(); } catch (e) { }
            hubConn = null; dir.clear();
        }
        setInterval(guard('lobbyBeat', () => { if (S.id) sendReg(); }), 1000);

        function newPeer(id) {
            const p = { id, name: 'player', ev: null, st: null, buf: [], lc: -1, pvp: true, alive: false, bl: null, blAt: 0, hello: false, cur: null, hue: 0, paused: false, pausedAt: 0, seenAt: now(), fy: undefined, fv: 0 };
            let h = 0; for (let i = 0; i < id.length; i++) h = (h * 31 + id.charCodeAt(i)) % 360; p.hue = h;
            S.peers.set(id, p); return p;
        }
        // a peer counts as paused when it says so, or when it stopped sending state (hidden tab, frozen page)
        const peerPaused = p => !!(p.paused || now() - p.seenAt > CFG.staleMs);
        // ...but the host role only moves away after the pause has lasted a while (avoids flapping during level loads)
        const peerHostPaused = p => (p.paused && now() - p.pausedAt > CFG.hostPauseMs) || now() - p.seenAt > CFG.staleMs;
        const meHostPaused = () => S.paused && now() - S.pausedAt > CFG.hostPauseMs;
        function connectTo(id) {
            id = String(id || '').trim();
            if (!validId(id) || !peer || !S.id || id === S.id || id === LOBBY_ID) return;
            const p = S.peers.get(id);
            if (p && p.ev && p.ev.open) return;
            try {
                attach(peer.connect(id, { label: 'ev', reliable: true }), true);
                attach(peer.connect(id, { label: 'st', reliable: false }), true);
            } catch (e) { ui.status('connect failed'); }
        }
        function attach(c, outgoing) {
            const pid = c.peer; const slot = c.label === 'st' ? 'st' : 'ev';
            const initiator = outgoing ? S.id : pid; c._init = initiator;
            const p = S.peers.get(pid) || newPeer(pid);
            const cur = p[slot];
            if (cur && cur !== c && cur.open) { // duplicate: keep the one initiated by the smaller id (both sides agree)
                if (cur._init <= initiator) { try { c.close(); } catch (e) { } return; }
                try { cur.close(); } catch (e) { }
            }
            p[slot] = c;
            c.on('data', d => { onDataSafe(p, d); });
            c.on('close', () => { if (S.tearing) return; if (p[slot] === c) { p[slot] = null; if (slot === 'ev') dropPeer(p); } });
            c.on('error', () => { });
            const opened = () => { if (slot === 'ev') { sendHello(p); } ui.refresh(); };
            if (c.open) opened(); else c.on('open', opened);
        }
        function dropPeer(p) {
            removeGhost(p.id);
            try { if (p.st) p.st.close(); } catch (e) { }
            S.peers.delete(p.id);
            say(p.name + ' left');
            refreshRole(); ui.refresh();
        }
        function sendEv(msg, to) {
            for (const p of S.peers.values()) {
                if (to && p.id !== to) continue;
                if (p.ev && p.ev.open) { try { p.ev.send(msg); } catch (e) { } }
            }
        }
        function sendSt(msg) {
            for (const p of S.peers.values()) {
                const c = (p.st && p.st.open) ? p.st : ((p.ev && p.ev.open) ? p.ev : null);
                if (c) { try { c.send(msg); } catch (e) { } }
            }
        }
        const hasPeers = () => { for (const p of S.peers.values()) if (p.ev && p.ev.open) return true; return false; };

        function sendHello(p) {
            sendEv({ t: 'hello', name: S.name, hostId: (S.sessionHostId || S.hostId || S.id), seed: S.inGame ? (S.runSeed != null ? S.runSeed : getSeed()) : getSeed(), inGame: S.inGame && !S.solo, lc: LC(), pvp: S.pvp, peers: [...S.peers.keys()], ...(S.inGame && !S.solo ? lvInfo() : {}) }, p.id);
            refreshRole();
        }

        // ------------------------------------------------------------------ roles
        // The player you joined is the preferred host (sessionHostId). While in a run, if the preferred host is paused
        // (pause menu, upgrade screen, hidden tab, frozen page) for longer than CFG.hostPauseMs, the host role moves to the
        // lowest-id active player, so a single paused player can't freeze mobs / doors / buttons for everybody.
        // Every client computes this from the same information, so they agree on who the host is.
        function computeHost() {
            if (!S.id) return S.sessionHostId || S.hostId;
            if (S.solo) return S.id;                                                  // training: private run, we are our own host
            const open = openPeers();
            const all = [S.id, ...open.map(p => p.id)].sort();
            let pref = S.sessionHostId || S.hostId || S.id;
            if (!all.includes(pref)) pref = all[0];                                   // preferred host left / not connected yet
            if (!S.inGame) return pref;
            const active = [];
            if (!meHostPaused()) active.push(S.id);
            for (const p of open) if (!peerHostPaused(p)) active.push(p.id);
            if (!active.length) return pref;                                          // everybody paused: nothing to move
            if (active.includes(pref)) return pref;
            active.sort();
            return active[0];
        }
        const isHostPeer = p => p.id === computeHost();                              // accept host messages from the CURRENT host
        function refreshRole() {
            if (!S.id) { ui.refresh(); return; }
            const was = S.isHost;
            S.hostId = computeHost(); S.isHost = (S.hostId === S.id);
            if (S.isHost && !was) {
                for (const mo of mob) unpuppetize(mo);
                S.aliveIds = null;
                S.buttonSent.clear();                                                // re-publish every button state as the new host
                if (S.inGame && !S.loading && !S.solo) { sendEv({ t: 'mc', lc: LC(), n: realMobs().length, ids: realMobs().filter(mo => mo.alive && mo._nid != null).map(mo => mo._nid) }); sendButtonSnapshot(); }
            } else if (!S.isHost && (was || S.firstRole === undefined)) {
                for (const mo of mob) puppetize(mo);
                if (S.inGame && S.firstRole === undefined) sendEv({ t: 'mreq', lc: LC() }, S.hostId);   // only the first time; later swaps keep the mobs we already have
            }
            S.firstRole = true;
            ui.refresh();
        }

        // ------------------------------------------------------------------ message handlers
        const H = {};
        function onData(p, d) { if (!d || typeof d !== 'object') return; const f = H[d.t]; if (f) f(p, d); }
        const onDataSafe = guard('net.data', onData);

        H.hello = (p, d) => {
            p.name = String(d.name || 'player').slice(0, 20); p.hello = true; p.pvp = d.pvp !== false; p.seenAt = now();
            if (!S.inGame && d.hostId && (p.id === S.sessionHostId || !S.sessionHostId)) { S.sessionHostId = String(d.hostId); S.hostId = S.sessionHostId; }
            // Peer connections are now permission-based; never auto-connect from a peer roster.
            if (d.inGame && !S.inGame && !S.loading && !S.starting) {          // they are already in a run: join it (whoever has the smaller id), then catch up
                if (d.seed == null) return;
                S.runSeed = String(d.seed);
                S.catchTarget = Math.max(0, d.lc | 0);
                beginRun(S.runSeed, d.lv, d.fl);
            } else if (!S.inGame && !d.inGame && p.id === (S.sessionHostId || S.hostId) && d.seed != null) {
                setSeed(String(d.seed));                                        // the joined session host supplies the lobby seed
            } else if (d.inGame && S.inGame && S.together && (d.lc | 0) > LC()) {
                syncToLevel(d.lc | 0);
            }
            refreshRole();
            if (S.isHost && S.inGame && !S.solo) {
                sendMobRoster(p.id);
                sendButtonSnapshot(p.id);
            }
            say(p.name + ' joined');
            ui.refresh();
        };
        H.peers = () => {}; // legacy roster packets cannot bypass join approval
        H.seed = (p, d) => { if (isHostPeer(p) && !S.inGame && d.seed != null) setSeed(String(d.seed)); };
        // Only the deterministic lobby leader may start a shared run.
        H.startReq = (p) => {
            if (!S.isHost || S.inGame || S.loading || S.starting) return;
            simulation.startGame();
        };
        H.start = (p, d) => {
            if (!isHostPeer(p) || S.inGame || S.loading || S.starting || d.seed == null) return;
            S.runSeed = String(d.seed);
            beginRun(S.runSeed, d.lv, d.fl);
        };
        H.lvl = (p, d) => {
            if (!S.together || !S.inGame || S.solo || !Number.isFinite(Number(d.lc))) return;
            const target = Math.max(0, d.lc | 0);
            if (LC() < target) syncToLevel(target);
        };
        H.chat = (p, d) => say(esc(p.name) + ': ' + esc(String(d.x || '').slice(0, 200)), true);
        H.pvp = (p, d) => { if (S.pvp && !S.paused && m.alive && typeof m.takeDamage === 'function' && Number.isFinite(d.d)) m.takeDamage(Math.min(d.d, 2)); };
        H.mc = (p, d) => {
            if (!isHostPeer(p) || S.isHost || S.solo) return;
            // the host is on a different level than us at the same level count => our level pool / local levels / seed differ
            if (d.ol != null && !S.loading && (d.lc | 0) === LC() && String(level.onLevel) !== String(d.ol) && S.olWarned !== LC()) {
                S.olWarned = LC();
                say('your level order differs from the host (level pool or local levels). Make your level pool match the host, otherwise the maps will not match.');
            }
            S.mc = d; checkMc();
        };
        H.resync = (p, d) => {            // the host loaded a checkpoint: restart from its seed and catch up to its level
            if (!isHostPeer(p) || S.solo || d.seed == null) return;
            S.runSeed = String(d.seed); S.catchTarget = Math.max(0, d.lc | 0);
            beginRun(S.runSeed, d.lv, d.fl);
        };
        H.mg = (p, d) => {                // map bodies destroyed by the host
            if (S.isHost || !isHostPeer(p) || (d.lc | 0) !== LC() || !S.mapIds || !Array.isArray(d.l)) return;
            for (const id of d.l.slice(0, 200)) {
                const bd = S.mapIds.get(id); if (!bd) continue;
                S.mapIds.delete(id);
                try { Composite.remove(engine.world, bd); } catch (e) { }
                const i = map.indexOf(bd); if (i !== -1) map.splice(i, 1);
            }
        };
        H.mreq = (p, d) => { if (S.isHost && !S.solo) sendEv({ t: 'mfull', lc: LC(), l: buildSpawnEvents(realMobs()), ids: realMobs().filter(mo => mo.alive && mo._nid != null).map(mo => mo._nid) }, p.id); };
        H.mfull = (p, d) => {
            if (S.isHost || !isHostPeer(p) || (d.lc | 0) !== LC()) return;
            for (const mo of realMobs()) { mobMap.delete(mo._nid); killSilently(mo); }
            applySpawnEvents(d.l);
            S.mc = null;
        };
        H.sp = (p, d) => { if (!S.isHost && isHostPeer(p) && (d.lc | 0) === LC()) applySpawnEvents(d.l); };
        H.md = (p, d) => {
            if (S.isHost || !isHostPeer(p) || !Array.isArray(d.l)) return;
            for (const id of d.l) {
                const mo = mobMap.get(id); mobMap.delete(id);
                if (!mo || !mo.alive) continue;
                mo.isDropPowerUp = false;
                S.inPuppet = true;
                try { (mo._realDeath || mo.death).call(mo); } catch (e) { } finally { S.inPuppet = false; }
                if (mo.alive) killSilently(mo);
            }
        };
        H.btn = (p, d) => {
            if (S.isHost || !isHostPeer(p) || (d.lc | 0) !== LC() || !Number.isInteger(d.i) || d.i < 0) return;
            const state = { up: !!d.up, cy: Number.isFinite(d.cy) ? d.cy : simulation.cycle };
            S.remoteButtons.set(d.i, state);
            const button = S.buttons[d.i]; if (button) button.isUp = state.up;
        };
        H.btns = (p, d) => {
            if (S.isHost || !isHostPeer(p) || (d.lc | 0) !== LC() || !Array.isArray(d.l)) return;
            for (const e of d.l.slice(0, 300)) {
                if (!Array.isArray(e) || !Number.isInteger(e[0]) || e[0] < 0) continue;
                const state = { up: !!e[1], cy: Number.isFinite(d.cy) ? d.cy : simulation.cycle };
                S.remoteButtons.set(e[0], state);
                const button = S.buttons[e[0]]; if (button) button.isUp = state.up;
            }
        };
        H.dm = (p, d) => {
            if (!S.isHost) return;
            for (const e of d.l) { const mo = mobMap.get(e[0]); if (mo && mo.alive && !mo._puppet) { try { mo.damage(e[1], !!e[2]); } catch (er) { } } }
        };
        H.bk = (p, d) => {
            if (S.solo || (d.lc | 0) !== LC()) return;
            for (const op of d.l) {
                if (op[0] === 'a') { const bd = createBody(op[1]); if (bd) bd._owner = p.id; }
                else if (op[0] === 'r') {
                    const bd = bodyMap.get(op[1]); if (!bd) continue;
                    bodyMap.delete(op[1]); bd._gone = true;
                    Composite.remove(engine.world, bd); const i = body.indexOf(bd); if (i !== -1) body.splice(i, 1);
                } else if (op[0] === 'c') { const bd = bodyMap.get(op[1]); if (bd) bd._owner = p.id; }
            }
        };
        // Pickups are per-person: the host tells everyone what dropped and each player spawns their own copy.
        H.pd = (p, d) => {
            if (!isHostPeer(p) || S.isHost || S.loading || (d.lc | 0) !== LC() || !Array.isArray(d.l)) return;
            for (const e of d.l.slice(0, 60)) {
                const x = Number(e[1]), y = Number(e[2]), size = Number(e[3]);
                if (typeof e[0] !== 'string' || !powerUps[e[0]] || !Number.isFinite(x) || !Number.isFinite(y)) continue;
                const before = powerUp.length;
                S.replayDrop = true;
                try { powerUps.directSpawn(x, y, e[0], true, (Number.isFinite(size) && size > 0) ? size : undefined); }
                catch (er) { } finally { S.replayDrop = false; }
                const pu = powerUp.length > before ? powerUp[powerUp.length - 1] : null;
                if (pu && !finiteBody(pu)) dropBody(pu);
            }
        };
        H.s = (p, d) => {
            p.lc = d.lc | 0; p.seenAt = now();
            const a = d.p;
            if (a) {
                const wasPaused = p.paused;
                p.alive = !!a[5]; p.pvp = !!a[12]; p.hp = a[10] / 1000; p.mhp = a[11] / 1000; p.og = !!a[13]; p.yOff = a[14]; p.paused = !!a[15];
                if (p.paused && !wasPaused) p.pausedAt = now();
                p.buf.push({ t: now(), x: a[0], y: a[1], vx: a[2] / 100, vy: a[3] / 100, a: a[4] / 1000 });
                if (p.buf.length > 10) p.buf.shift();
            }
            p.bl = d.bl || null; p.blAt = now();
            const fromHost = isHostPeer(p);
            if (d.cy != null && fromHost && !S.isHost && !p.paused) S.hostCy = { cy: Number(d.cy), t: now(), lc: p.lc, fi: d.fi };
            if (p.lc !== LC() || S.loading) return;
            if (d.bk) applyBlocks(p, d.bk);
            if (d.mo && !S.isHost && fromHost) applyMobs(d.mo);
            if (d.mm && !S.isHost && fromHost) applyMapMovers(d.mm);
        };

        // ------------------------------------------------------------------ seed / start / level lockstep
        const seedEl = () => document.getElementById('seed');
        function getSeed() { const e = seedEl(); return String((e && e.value.trim()) || (e && e.placeholder) || Math.initialSeed || ''); }
        function setSeed(s) {
            s = String(s == null ? '' : s);
            const e = seedEl(); if (e) e.value = s;
            Math.initialSeed = s;
            if (typeof Math.hash === 'function') Math.seed = Math.abs(Math.hash(s));
        }
        function rollHostSeed() {
            // Roll once on the session host; this value is broadcast and reused by every client.
            try {
                const a = new Uint32Array(1);
                if (window.crypto && typeof window.crypto.getRandomValues === 'function') {
                    window.crypto.getRandomValues(a); return String(a[0]);
                }
            } catch (e) { }
            const stamp = Date.now().toString(36) + ':' + (performance.now() * 1000 | 0).toString(36) + ':' + S.id;
            return String(Math.abs(typeof Math.hash === 'function' ? Math.hash(stamp) : stamp.split('').reduce((h, c) => (h * 31 + c.charCodeAt(0)) | 0, 0)));
        }
        // ---- level order: the host's list is authoritative (level pools / local levels may differ per player) ----
        function lvInfo() { return { lv: Array.isArray(level.levels) ? level.levels.slice() : null, fl: !!simulation.isHorizontalFlipped }; }
        function mapsAvailable(name) {
            try { return [level.maps, level.localMaps, typeof moreLevels === 'undefined' ? null : moreLevels].some(m_ => m_ && Object.prototype.hasOwnProperty.call(m_, name) && typeof m_[name] === 'function'); }
            catch (e) { return true; }
        }
        // make sure every level of the host's route exists here (community levels load lazily); resolves to false if one is missing
        function prepareRoute(lv) {
            if (!Array.isArray(lv)) return Promise.resolve(true);
            const missing = () => lv.filter(n => !mapsAvailable(n));
            if (!missing().length) return Promise.resolve(true);
            const go = (typeof level.loadMoreLevels === 'function') ? Promise.resolve().then(() => level.loadMoreLevels()).catch(() => { }) : Promise.resolve();
            return go.then(() => {
                const m_ = missing();
                if (m_.length) { say('the host\'s level list needs maps you do not have: ' + esc(m_.join(', '))); return false; }
                return true;
            });
        }
        function beginRun(seed, lv, fl) {      // join a run started by someone else
            S.forceLv = Array.isArray(lv) ? lv.map(String).slice(0, 64) : null;
            S.forceFlip = typeof fl === 'boolean' ? fl : null;
            return prepareRoute(S.forceLv).then(ok => {
                if (!ok) { S.forceLv = null; S.forceFlip = null; }
                if (S.inGame || S.starting) return;
                startLocalGame(seed);
            });
        }
        // level.populateLevels uses plain Math.random for the late "factory/reservoir/interferometer" pick and reads the PER-PLAYER level pool:
        // make the random part deterministic and let the host's list win
        function wrapPopulateLevels() {
            wrapFn(level, 'populateLevels', 'level.populateLevels', orig => function () {
                if (!hasPeers() || !S.together || S.solo || simulation.isTraining) return orig.apply(this, arguments);
                const realRandom = Math.random, seeded = Math.seededRandom;
                if (typeof seeded === 'function') Math.random = function () { return seeded(); };
                try { orig.apply(this, arguments); }
                finally { Math.random = realRandom; }
                if (S.forceLv && S.forceLv.length) { level.levels = S.forceLv.slice(); }
                if (S.forceFlip !== null) simulation.isHorizontalFlipped = S.forceFlip;
                S.forceLv = null; S.forceFlip = null;
                return undefined;
            });
        }
        function startLocalGame(seed) {
            if (seed != null) {
                S.runSeed = String(seed);
                setSeed(S.runSeed);
            }
            S.applying = true;
            try { simulation.startGame(); }
            catch (e) { console.warn('[MP] could not start game', e); }
            finally { S.applying = false; }
        }
        // n-gon changes level in two phases: level.nextLevel() bumps the counters and sets simulation.clearNow;
        // on the NEXT frame the game runs simulation.clearMap() + level.start(). The map is built in level.start from a seed
        // that depends only on (run seed, level number), so every player gets the same map even if they are paused or busy.
        function syncToLevel(target) {
            if (target > S.catchTarget) S.catchTarget = target;
            if (S.catchRunning) return;
            S.catchRunning = true;
            let guardN = 0;
            const step = () => {
                if (!S.inGame || LC() >= S.catchTarget || ++guardN > 2000) { S.catchRunning = false; return; }
                if (simulation.clearNow || S.loading) { setTimeout(step, 40); return; }   // previous level still being built (or this player is paused)
                S.remotePending = true;                                                   // consumed by the next clearMap
                S.applying = true;
                try { level.nextLevel(); } catch (e) { console.warn('[MP] could not advance level', e); S.catchRunning = false; S.remotePending = false; return; } finally { S.applying = false; }
                if (!simulation.clearNow) S.remotePending = false;
                setTimeout(step, 60);
            };
            step();
        }
        function runCatchup() { if (S.inGame && !S.loading && S.catchTarget > LC() && !S.catchRunning) syncToLevel(S.catchTarget); }

        const onStartPre = guard('startGame.pre', () => {
            S.starting = true; destroyGhosts(); resetSync();
            if (!S.applying) S.catchTarget = 0;
            S.catchRunning = false;
            S.loading = true; S.loadingSince = now(); S.inGame = false;
        });
        wrapFn(simulation, 'startGame', 'simulation.startGame', orig => function () {
            // Training (startGame(false, true)) and build runs (startGame(true)) are private solo runs: nothing is synced.
            if ((arguments[0] === true || arguments[1] === true) && !S.applying) {
                S.solo = true; refreshRole();
                S.runSeed = getSeed(); setSeed(S.runSeed);
                onStartPre();
                let r;
                try { r = orig.apply(this, arguments); }
                catch (e) { S.starting = false; throw e; }
                const fin = () => { S.inGame = true; S.loadingSince = now(); S.starting = false; };
                if (r && typeof r.then === 'function') return r.then(v => { fin(); return v; }, e => { S.starting = false; throw e; });
                fin(); return r;
            }
            if (S.solo) { S.solo = false; refreshRole(); }
            const loadingSave = !!S.savePending;             // a checkpoint is being loaded: keep ITS seed, then resync everyone
            if (loadingSave) S.saveStarted = true;
            // A guest asks the lobby leader to start; it never starts a divergent local run.
            if (!S.applying && hasPeers() && !S.isHost && !loadingSave) {
                sendEv({ t: 'startReq' }, S.hostId);
                return;
            }
            let announce = false;
            if (!S.applying) {
                if (loadingSave) S.runSeed = String(Math.initialSeed != null ? Math.initialSeed : getSeed());
                else {
                    S.runSeed = hasPeers() ? rollHostSeed() : getSeed();
                    setSeed(S.runSeed);
                    announce = hasPeers();
                }
            } else if (S.runSeed == null) {
                S.runSeed = getSeed();
            }
            // these two persist between runs and are NOT reset by n-gon: a player who already played a run would otherwise get
            // a different constraint order than a fresh one
            if (!loadingSave && !simulation.isTraining) { canonConstraints(); }
            onStartPre();
            let r;
            try { r = orig.apply(this, arguments); }
            catch (e) { S.starting = false; S.loading = false; throw e; }
            const fin = () => {
                S.inGame = true; S.loadingSince = now(); S.starting = false;
                if (S.runSeed == null) S.runSeed = String(getSeed());
                if (!loadingSave) setSeed(S.runSeed);
                // tell everyone only NOW: populateLevels has run, so the host's level order and flip are known
                if (announce && hasPeers()) sendEv({ t: 'start', seed: S.runSeed, ...lvInfo() });
            };
            // startGame is async (community maps / training load extra levels first): everything after that await runs later
            if (r && typeof r.then === 'function') return r.then(v => { fin(); return v; }, e => { S.starting = false; S.loading = false; throw e; });
            fin();
            return r;
        });
        function canonConstraints() {
            try {
                if (Array.isArray(level.constraint)) level.constraint.sort((a, b) => String(a.description).localeCompare(String(b.description)));
                level.constraintIndex = 0;
            } catch (e) { }
        }
        const onClearPre = guard('clearMap.pre', () => {
            destroyGhosts(); resetSync(); S.loading = true; S.loadingSince = now();
            if (S.starting) { S.starting = false; }
            else if (S.remotePending) { S.remotePending = false; }                  // level change requested by another player
            else if (S.inGame && S.together && !S.solo && hasPeers()) {              // we changed level: tell everybody
                sendEv({ t: 'lvl', lc: LC() });
            }
        });
        wrapFn(simulation, 'clearMap', 'simulation.clearMap', orig => function () { onClearPre(); return orig.apply(this, arguments); });
        const onLevelStart = guard('level.start.post', () => { S.inGame = true; S.starting = false; afterLevelLoaded(); });
        // Build every level from the SAME random numbers on every client:
        //  1. the seed is derived from (run seed, level number), independent of anything else that happened in the run
        //  2. plain Math.random (used by some map generators for sizes, counts and drops) is swapped for the seeded generator
        const hooked = wrapFn(level, 'start', 'level.start', orig => function () {
            S.buildingLevel = true;
            S.buttons = []; S.buttonSeq = 0; S.buttonSent.clear(); S.remoteButtons.clear();
            const realRandom = Math.random;
            const realSeed = Math.seed;
            const seeded = Math.seededRandom;
            if (S.savePending && S.saveStarted && Math.initialSeed != null) S.runSeed = String(Math.initialSeed);   // checkpoint: the SAVE's seed
            const runSeed = String(S.runSeed != null ? S.runSeed : getSeed());
            const swap = hasPeers() && S.together && !S.solo && typeof seeded === 'function' && typeof Math.hash === 'function';
            if (swap) {
                // Every player starts the level's random stream from the same run-seed/level pair.
                Math.seed = Math.abs(Math.hash(runSeed + '|LEVEL|' + LC()));
                Math.random = function () { return seeded(); };
            }
            // newer n-gon builds can finish level.start() asynchronously (local levels with code), so wait for it
            let finished = false;
            const finish = () => {
                if (finished) return; finished = true;
                Math.random = realRandom;
                if (swap) Math.seed = realSeed;
                S.buildingLevel = false;
                onLevelStart();
            };
            let r;
            try { r = orig.apply(this, arguments); }
            catch (e) { finish(); throw e; }
            if (r && typeof r.then === 'function') return r.then(v => { finish(); return v; }, e => { finish(); throw e; });
            finish();
            return r;
        });
        if (!hooked) console.warn('[MP] level changes will be detected by polling instead');

        function sendButtonSnapshot(to) {
            if (!S.isHost || !S.inGame || S.solo || !hasPeers()) return;
            const list = [];
            for (let i = 0; i < S.buttons.length; i++) {
                const b = S.buttons[i]; if (b) list.push([i, !!b.isUp]);
            }
            sendEv({ t: 'btns', lc: LC(), cy: simulation.cycle, l: list }, to);
        }
        function publishButtonState(button) {
            if (!S.isHost || S.solo || !hasPeers() || !button || !Number.isInteger(button._mpButtonId)) return;
            const i = button._mpButtonId, up = !!button.isUp;
            if (S.buttonSent.get(i) === up) return;
            S.buttonSent.set(i, up);
            sendEv({ t: 'btn', lc: LC(), cy: simulation.cycle, i, up });
        }
        function withAllPlayersInButtonQuery(fn) {
            if (!S.isHost || !ghosts.size) return fn();
            const region = Matter.Query.region;
            Matter.Query.region = function (bodies, bounds) {
                if (Array.isArray(bodies) && bodies.length === 1 && bodies[0] === player) {
                    const all = [player];
                    // paused players are standing still and can't press buttons on purpose
                    for (const g of ghosts.values()) { const pp = S.peers.get(g.gid); if (g && g.alive && g.position && pp && !peerPaused(pp)) all.push(g); }
                    return region.call(this, all, bounds);
                }
                return region.apply(this, arguments);
            };
            try { return fn(); } finally { Matter.Query.region = region; }
        }
        function wrapButtons() {
            wrapFn(level, 'button', 'level.button', orig => function () {
                const button = orig.apply(this, arguments);
                const id = S.buttonSeq++;
                button._mpButtonId = id;
                S.buttons[id] = button;
                for (const method of ['query', 'queryRemove', 'queryPlayer']) {
                    const original = button[method];
                    if (typeof original !== 'function' || original._mpButtonWrapped) continue;
                    const wrapped = function () {
                        if (S.isHost) {
                            const result = withAllPlayersInButtonQuery(() => original.apply(this, arguments));
                            publishButtonState(this);
                            return result;
                        }
                        const state = S.remoteButtons.get(id);
                        if (state) this.isUp = state.up;
                        return undefined;
                    };
                    wrapped._mpButtonWrapped = true;
                    button[method] = wrapped;
                }
                return button;
            });
        }
        function frameRandom(key) {
            const text = String(S.runSeed || getSeed()) + '|' + LC() + '|' + simulation.cycle + '|' + key;
            let x = 2166136261;
            for (let i = 0; i < text.length; i++) { x ^= text.charCodeAt(i); x = Math.imul(x, 16777619); }
            return function () {
                x ^= x << 13; x ^= x >>> 17; x ^= x << 5;
                return (x >>> 0) / 4294967296;
            };
        }
        // level.custom / level.customTopLayer are REASSIGNED by every level, so wrap them through an accessor
        function wrapLevelFrameRandom() {
            for (const key of ['custom', 'customTopLayer']) {
                try {
                    const wrap = f => {
                        if (typeof f !== 'function' || f._mpw) return f;
                        const w = function () {
                            if (!hasPeers() || !S.together || !S.inGame || S.solo || S.runSeed == null) return f.apply(this, arguments);
                            const realRandom = Math.random;
                            Math.random = frameRandom(key);
                            try { return f.apply(this, arguments); }
                            finally { Math.random = realRandom; }
                        };
                        w._mpw = true; return w;
                    };
                    let val = wrap(level[key]);
                    Object.defineProperty(level, key, { configurable: true, enumerable: true, get() { return val; }, set(v) { val = wrap(v); } });
                } catch (e) { console.warn('[MP] could not wrap level.' + key, e); }
            }
        }
        // ---- generic sync of moving / destroyed level geometry (works whatever level-elements API builds it) ----
        function assignMapIds() {
            S.mapIds = new Map(); S.mapSent = new Map(); S.mapBase = new Map();
            if (typeof map === 'undefined' || !Array.isArray(map)) return;
            let i = 0;
            for (const bd of map) {
                if (!bd || !bd.position) continue;
                if (bd._mid === undefined) bd._mid = 'M' + LC() + '_' + i;
                i++;
                S.mapIds.set(bd._mid, bd);
                S.mapBase.set(bd._mid, [q(bd.position.x, 10), q(bd.position.y, 10), q(bd.angle, 1000)]);
                S.mapSent.set(bd._mid, S.mapBase.get(bd._mid));
            }
        }
        function scanMapMovers() {
            if (!S.isHost || !S.mapIds || S.solo) return null;
            const out = [], periodic = S.tickN % 40 === 0;
            if (S.tickN % 10 === 0) {                                                   // destroyed map bodies
                const present = new Set(map), gone = [];
                for (const [id, bd] of S.mapIds) if (!present.has(bd)) gone.push(id);
                if (gone.length) { for (const id of gone) S.mapIds.delete(id); sendEv({ t: 'mg', lc: LC(), l: gone }); }
            }
            for (const [id, bd] of S.mapIds) {
                if (!bd.position) continue;
                const x = q(bd.position.x, 10), y = q(bd.position.y, 10), a = q(bd.angle, 1000), l = S.mapSent.get(id), base = S.mapBase.get(id);
                if (l && (Math.abs(l[0] - x) > 1 || Math.abs(l[1] - y) > 1 || Math.abs(l[2] - a) > 2)) { out.push([id, x, y, a]); S.mapSent.set(id, [x, y, a]); }
                else if (periodic && base && (Math.abs(base[0] - x) > 1 || Math.abs(base[1] - y) > 1 || Math.abs(base[2] - a) > 2)) out.push([id, x, y, a]);   // re-send moved bodies now and then (late joiners, lost packets)
                if (out.length >= 150) break;
            }
            return out;
        }
        function applyMapMovers(list) {
            if (!S.mapIds || !Array.isArray(list)) return;
            for (const e of list.slice(0, 200)) {
                const bd = S.mapIds.get(e[0]); if (!bd || !Number.isFinite(e[1]) || !Number.isFinite(e[2])) continue;
                Body.setPosition(bd, { x: e[1] / 10, y: e[2] / 10 });
                if (Number.isFinite(e[3])) Body.setAngle(bd, e[3] / 1000);
            }
        }
        // ---- features of newer n-gon builds: checkpoints, level editor ----
        function watchSaveLoad() {
            if (S.saveWatching) return;
            S.saveWatching = true; S.saveStarted = false;
            const t0 = now();
            const iv = setInterval(guard('saveWatch', () => {
                if (now() - t0 > 20000) { clearInterval(iv); S.saveWatching = false; S.savePending = false; return; }
                if (S.saveStarted && S.inGame && !S.loading && !simulation.clearNow) {
                    clearInterval(iv); S.saveWatching = false; S.savePending = false; S.saveStarted = false;
                    S.runSeed = String(Math.initialSeed != null ? Math.initialSeed : getSeed());
                    if (hasPeers() && !S.solo) sendEv({ t: 'resync', seed: S.runSeed, lc: LC(), ...lvInfo() });
                }
            }), 250);
        }
        function wrapNewFeatures() {
            if (typeof levelEditor !== 'undefined' && levelEditor) {
                wrapFn(levelEditor, 'open', 'levelEditor.open', orig => function () {
                    if (hasPeers()) { say('the level editor is disabled while connected to other players (local levels differ per player)'); return undefined; }
                    return orig.apply(this, arguments);
                });
            } else HOOKS['levelEditor'] = false;
            // saveGame.load is the single entry for continueRun / import / rewind
            if (typeof saveGame !== 'undefined' && saveGame && typeof saveGame.load === 'function') {
                wrapFn(saveGame, 'load', 'saveGame.load', orig => function () {
                    if (hasPeers() && !S.isHost) { say('only the host can load a checkpoint while connected'); return undefined; }
                    S.savePending = true; watchSaveLoad();
                    const done = () => { if (!S.saveStarted) { S.savePending = false; } };   // load bailed out before starting a game
                    let r;
                    try { r = orig.apply(this, arguments); } catch (e) { done(); throw e; }
                    if (r && typeof r.then === 'function') return r.then(v => { done(); return v; }, e => { done(); throw e; });
                    done(); return r;
                });
            } else HOOKS['saveGame'] = false;
        }
        function sendMobRoster(to) {
            if (!S.isHost || !S.inGame || S.solo) return;
            const list = realMobs().filter(mo => mo.alive && mo._nid != null);
            sendEv({ t: 'mc', lc: LC(), n: list.length, ids: list.map(mo => mo._nid), ol: String(level.onLevel) }, to);
        }
        function resetSync() {
            mobMap.clear(); bodyMap.clear(); puMap.clear();
            spawnQ = []; deathQ = []; opsQ = []; dropQ = []; dmgOut.clear(); pvpOut.clear();
            S.aliveIds = null; S.mc = null; S.ctr = 0; S.hostCy = null;
            S.buttons = []; S.buttonSeq = 0; S.buttonSent.clear(); S.remoteButtons.clear();
            S.mapIds = null; S.mapSent = new Map(); S.mapBase = new Map();
        }
        function afterLevelLoaded() {
            try { afterLevelLoaded2(); } finally { S.loading = false; }
        }
        function afterLevelLoaded2() {
            const lc = LC(); let i = 0;
            for (const mo of mob) { if (!mo || mo.isGhost) continue; if (mo._nid === undefined) mo._nid = 'L' + lc + '_' + (i++); mobMap.set(mo._nid, mo); }
            i = 0;
            for (const bd of body) { if (!bd) continue; if (bd._nid === undefined) { bd._nid = 'L' + lc + '_' + (i++); bd._owner = null; } bodyMap.set(bd._nid, bd); }
            i = 0;
            for (const pu of powerUp) { if (!pu) continue; if (pu._pid === undefined) pu._pid = 'L' + lc + '_' + (i++); puMap.set(pu._pid, pu); }
            assignMapIds();
            if (!S.isHost) for (const mo of mob) puppetize(mo);
            S.aliveIds = new Set(); for (const mo of mob) if (mo && !mo.isGhost && mo._nid !== undefined && mo.alive) S.aliveIds.add(mo._nid);
            S.loading = false;
            if (S.isHost && hasPeers()) { sendMobRoster(); sendButtonSnapshot(); }
        }
        function checkMc() {
            if (S.isHost || !S.mc || S.loading || S.catchRunning || !S.inGame) return;
            if (S.mc.lc !== LC()) return;
            const local = realMobs().filter(mo => mo.alive && mo._nid != null).map(mo => mo._nid);
            const wanted = Array.isArray(S.mc.ids) ? S.mc.ids : null;
            const mismatch = wanted
                ? (local.length !== wanted.length || wanted.some(id => !local.includes(id)))
                : (local.length !== S.mc.n);
            S.mc = null;
            if (mismatch) sendEv({ t: 'mreq', lc: LC() }, S.hostId);
        }
        let lastKey = null;
        function levelWatch() {
            const k = LC() + ':' + level.onLevel;
            if (S.loading && !simulation.clearNow && !S.paused && now() - (S.loadingSince || 0) > 2000) afterLevelLoaded();     // never stay "loading" forever
            else if (!hooked && lastKey !== null && k !== lastKey && !S.loading && S.inGame && !simulation.clearNow) { destroyGhosts(); resetSync(); afterLevelLoaded(); }
            lastKey = k;
        }

        // ------------------------------------------------------------------ mobs
        const realMobs = () => mob.filter(mo => mo && !mo.isGhost);
        function removeBodyAndConstraints(t) {
            if (!t) return;
            try {
                const att = Composite.allConstraints(engine.world).filter(c => c.bodyA === t || c.bodyB === t);
                for (const c of att) Composite.remove(engine.world, c);
                Composite.remove(engine.world, t);
            } catch (e) { }
        }
        function killSilently(mo) {
            mo.alive = false; mo.isDropPowerUp = false; removeBodyAndConstraints(mo);
            const i = mob.indexOf(mo); if (i !== -1) mob.splice(i, 1);
        }
        function safeArgs(args) {
            for (const v of args) if (!(v == null || ['number', 'string', 'boolean'].includes(typeof v))) return null;
            return args.slice();
        }
        function wrapSpawns() {
            for (const key of Object.keys(spawn)) {
                let fn; try { fn = spawn[key]; } catch (e) { continue; }
                if (typeof fn !== 'function' || fn._mp || SKIP_SPAWN.test(key)) continue;
                try { if (!Object.getOwnPropertyDescriptor(spawn, key).writable) continue; } catch (e) { continue; }
                const w = function (...args) {
                    if (S.inPuppet && !S.replay) return undefined;   // puppets never spawn on their own
                    if (!S.isHost && !S.buildingLevel && !S.replay) return undefined; // runtime enemy spawns are host-authoritative
                    const before = mob.length;
                    const r = fn.apply(this, args);
                    try {
                        const grp = ++S.grp;
                        for (let i = before; i < mob.length; i++) {
                            const mo = mob[i]; if (!mo || mo.isGhost || mo._mt) continue;
                            mo._mt = key; mo._ma = safeArgs(args); mo._grp = grp;
                            if (S.replay) S.replayNew.push(mo);
                        }
                    } catch (e) { }
                    return r;
                };
                w._mp = true; spawn[key] = w;
            }
        }
        function buildSpawnEvents(list) {
            const groups = new Map(), out = [];
            for (const mo of list) {
                if (!mo || !mo.alive || mo._nid === undefined) continue;
                if (mo._grp && mo._mt && mo._ma) { if (!groups.has(mo._grp)) groups.set(mo._grp, []); groups.get(mo._grp).push(mo); }
                else out.push({ ids: [mo._nid], k: null, x: q(mo.position.x), y: q(mo.position.y), r: q(mo.radius || 25), f: mo.fill || '#888' });
            }
            for (const arr of groups.values()) out.push({ ids: arr.map(mo => mo._nid), k: arr[0]._mt, a: arr[0]._ma, x: q(arr[0].position.x), y: q(arr[0].position.y) });
            return out;
        }
        function applySpawnEvents(list) {
            for (const ev of list || []) {
                if (ev.ids.every(id => mobMap.has(id))) continue;
                let made = [];
                if (ev.k && ev.a && typeof spawn[ev.k] === 'function') {
                    S.replay = true; S.replayNew = [];
                    try { spawn[ev.k](...ev.a); } catch (e) { } finally { S.replay = false; }
                    made = S.replayNew; S.replayNew = [];
                } else {
                    try {
                        const before = mob.length;
                        S.replay = true;
                        mobs.spawn(ev.x, ev.y, 8, ev.r || 25, ev.f || '#888');
                        if (mob.length > before) {
                            const g = mob[mob.length - 1];
                            if (typeof g.do !== 'function') g.do = function () { if (typeof this.checkStatus === 'function') this.checkStatus(); };
                            made = [g];
                        }
                    } catch (e) { }
                    finally { S.replay = false; }
                }
                for (let i = 0; i < made.length; i++) {
                    const mo = made[i];
                    if (i < ev.ids.length) { mo._nid = ev.ids[i]; mobMap.set(mo._nid, mo); puppetize(mo); }
                    else killSilently(mo);
                }
            }
        }
        function puppetize(mo) {
            if (!mo || mo.isGhost || mo._puppet || mo._nid === undefined) return;
            mo._puppet = true; mo._orig = {};
            for (const k of PUPPET_NOOPS) if (typeof mo[k] === 'function') { mo._orig[k] = mo[k]; mo[k] = NOOP; }
            mo._origDrop = mo.isDropPowerUp; mo.isDropPowerUp = false;   // the host spawns drops
            mo._origDamage = mo.damage; mo._realDeath = mo.death;
            mo.damage = function (d, pierce) {
                const e = dmgOut.get(this._nid) || [0, 0]; e[0] += d; e[1] = (e[1] || pierce) ? 1 : 0; dmgOut.set(this._nid, e);
                const keep = this.death; this.death = NOOP;   // death only comes from the host
                try { return mo._origDamage.call(this, d, pierce); } finally { this.death = keep; }
            };
            mo._buf = [];
        }
        function unpuppetize(mo) {
            if (!mo || !mo._puppet) return;
            for (const k in mo._orig) mo[k] = mo._orig[k];
            mo.damage = mo._origDamage; mo.death = mo._realDeath; mo.isDropPowerUp = mo._origDrop;
            mo._puppet = false; mo._orig = null; mo._buf = null;
        }
        function applyMobs(list) {
            const t = now();
            for (const e of list) {
                const mo = mobMap.get(e[0]); if (!mo || !mo.alive || !mo._buf) continue;
                mo._buf.push({ t, x: e[1], y: e[2], vx: e[3] / 100, vy: e[4] / 100, a: e[5] / 1000 });
                if (mo._buf.length > 6) mo._buf.shift();
                mo.health = e[6] / 1000;
            }
        }
        // host: all mobs chase the nearest ACTIVE player, not just the host's player
        function retarget() {
            if (simulation.cycle % 4) return;
            const targets = [];
            if (m.alive && !m.isCloak) targets.push(player.position);
            for (const g of ghosts.values()) { const p = S.peers.get(g.gid); if (p && p.alive && !peerPaused(p) && g.position) targets.push(g.position); }
            if (targets.length < 2) return;
            for (const mo of mob) {
                if (!mo || mo.isGhost || !mo.alive || !mo.seePlayer || mo._puppet) continue;
                const sp = mo.seePlayer; let best = null, bd2 = mo.alertRange2 || 1e12;
                for (const tp of targets) {
                    const dx = tp.x - mo.position.x, dy = tp.y - mo.position.y, d2 = dx * dx + dy * dy;
                    if (d2 < bd2) { try { if (Matter.Query.ray(map, mo.position, tp).length) continue; } catch (e) { continue; } bd2 = d2; best = tp; }
                }
                if (best && (sp.yes || best !== player.position)) {
                    sp.position.x = best.x; sp.position.y = best.y; sp.yes = true;
                    if (typeof sp.recall === 'number') sp.recall = Math.max(sp.recall, 30);
                }
            }
        }
        const doRetarget = guard('retarget', retarget);
        const ensureDo = guard('ensureDo', () => { for (let i = 0; i < mob.length; i++) { const mo = mob[i]; if (mo && typeof mo.do !== 'function') mo.do = NOOP; } });
        wrapFn(mobs, 'loop', 'mobs.loop', orig => function () {
            ensureDo();
            if (!S.isHost) { S.inPuppet = true; try { return orig.apply(this, arguments); } finally { S.inPuppet = false; } }
            const r = orig.apply(this, arguments);
            if (ghosts.size) doRetarget();
            return r;
        });

        // ------------------------------------------------------------------ safety net
        function finiteBody(bd) {
            if (!bd || !bd.position || !Number.isFinite(bd.position.x) || !Number.isFinite(bd.position.y)) return false;
            const vt = bd.vertices; if (!vt) return true;
            for (let i = 0; i < vt.length; i++) if (!Number.isFinite(vt[i].x) || !Number.isFinite(vt[i].y)) return false;
            return true;
        }
        function dropBody(bd) {
            try { removeBodyAndConstraints(bd); } catch (e) { try { Composite.remove(engine.world, bd, true); } catch (er) { } }
            for (const arr of [mob, body, powerUp, bullet]) { const i = arr.indexOf(bd); if (i !== -1) arr.splice(i, 1); }
        }
        const sanitizeWorld = guard('sanitize', () => {
            let bad = null;
            for (const bd of Composite.allBodies(engine.world)) if (!finiteBody(bd)) (bad = bad || []).push(bd);
            if (bad) { for (const bd of bad) dropBody(bd); console.warn('[MP] removed ' + bad.length + ' body/bodies with invalid geometry'); }
        });
        Matter.Events.on(engine, 'beforeUpdate', guard('beforeUpdate', () => { if (S.tickN !== S._lastSan) { S._lastSan = S.tickN; sanitizeWorld(); } }));

        // ------------------------------------------------------------------ blocks & power ups
        function descBody(bd) {
            const cos = Math.cos(-bd.angle), sin = Math.sin(-bd.angle), cx = bd.position.x, cy = bd.position.y, v = [];
            for (const vt of bd.vertices) { const dx = vt.x - cx, dy = vt.y - cy; v.push(q(dx * cos - dy * sin, 10), q(dx * sin + dy * cos, 10)); }
            return [bd._nid, q(cx, 10), q(cy, 10), q(bd.angle, 1000), v, bd.friction, bd.frictionAir, bd.restitution, bd.density];
        }
        function createBody(e) {
            if (bodyMap.has(e[0])) return bodyMap.get(e[0]);
            if (!Array.isArray(e[4]) || e[4].length < 6 || e[4].length > 200) return null;
            const verts = []; for (let i = 0; i + 1 < e[4].length; i += 2) verts.push({ x: e[4][i] / 10, y: e[4][i + 1] / 10 });
            if (!verts.every(v => Number.isFinite(v.x) && Number.isFinite(v.y)) || !Number.isFinite(e[1]) || !Number.isFinite(e[2])) return null;
            let bd = null;
            try {
                bd = Bodies.fromVertices(e[1] / 10, e[2] / 10, [verts], {
                    friction: Number.isFinite(e[5]) ? e[5] : 0.1, frictionAir: Number.isFinite(e[6]) ? e[6] : 0.01, restitution: Number.isFinite(e[7]) ? e[7] : 0,
                    collisionFilter: { category: cat.body, mask: cat.player | cat.map | cat.body | cat.bullet | cat.mob | cat.mobBullet }
                });
            } catch (er) { }
            if (!bd) return null;
            if (Number.isFinite(e[8]) && e[8] > 0) Body.setDensity(bd, e[8]);
            Body.setAngle(bd, (e[3] || 0) / 1000); Body.setPosition(bd, { x: e[1] / 10, y: e[2] / 10 });
            if (!finiteBody(bd)) return null;
            bd.classType = 'body'; bd._nid = e[0];
            Composite.add(engine.world, bd); body.push(bd); bodyMap.set(e[0], bd);
            return bd;
        }
        function claim(bd) { bd._owner = S.id; opsQ.push(['c', bd._nid]); }
        function applyBlocks(p, list) {
            const fromHost = isHostPeer(p);
            for (const e of list) {
                const bd = bodyMap.get(e[0]);
                if (!bd || bd === m.holdingTarget) continue;
                if (fromHost) { if (bd._owner !== null && bd._owner !== p.id) continue; }
                else if (bd._owner !== p.id) continue;
                const nx = e[1] / 10, ny = e[2] / 10, dx = nx - bd.position.x, dy = ny - bd.position.y;
                if (dx * dx + dy * dy > 6400) Body.setPosition(bd, { x: nx, y: ny });
                else Body.setPosition(bd, { x: bd.position.x + dx * 0.6, y: bd.position.y + dy * 0.6 });
                Body.setAngle(bd, e[3] / 1000);
                Body.setVelocity(bd, { x: e[4] / 100, y: e[5] / 100 });
                Body.setAngularVelocity(bd, e[6] / 1000);
            }
        }
        function scanWorld() {
            const cur = new Set();
            for (const bd of body) {
                if (!bd) continue;
                if (bd._nid === undefined) {
                    bd._nid = 'D' + LC() + '_' + S.id + '_' + (S.ctr++); bd._owner = S.id; bodyMap.set(bd._nid, bd);
                    if (!bd.isNotHoldable) opsQ.push(['a', descBody(bd)]);
                }
                cur.add(bd._nid);
            }
            for (const [id, bd] of bodyMap) if (!cur.has(id)) { bodyMap.delete(id); if (!bd._gone && !bd.isNotHoldable) opsQ.push(['r', id]); }
            const h = m.holdingTarget; if (h && h._nid !== undefined && h._owner !== S.id) claim(h);
            if (player && player.position) for (const bd of bodyMap.values()) {
                if (bd._owner === S.id || bd.isNotHoldable) continue;
                const dx = bd.position.x - player.position.x, dy = bd.position.y - player.position.y;
                if (dx * dx + dy * dy < 14400 && bd.speed > 2) claim(bd);
            }
            if (S.isHost) {
                const curM = new Set(), fresh = [];
                for (const mo of mob) {
                    if (!mo || mo.isGhost) continue;
                    if (mo._nid === undefined) { mo._nid = 'D' + LC() + '_' + S.id + '_' + (S.ctr++); mobMap.set(mo._nid, mo); fresh.push(mo); }
                    if (mo.alive) curM.add(mo._nid);
                }
                if (fresh.length) for (const ev of buildSpawnEvents(fresh)) spawnQ.push(ev);
                if (S.aliveIds) for (const id of S.aliveIds) if (!curM.has(id)) deathQ.push(id);
                S.aliveIds = curM;
            }
        }

        // ------------------------------------------------------------------ ghosts (other players)
        function drawRemotePlayer(p, s, flash) {
            const L1 = (m && m.legLength1) || 55, L2 = (m && m.legLength2) || 45, HT = (m && m.height) || 42;
            const flip = Math.cos(s.a) >= 0 ? 1 : -1;
            const yOff = Number.isFinite(p.yOff) ? p.yOff : 49;
            const vx = Number.isFinite(s.vx) ? s.vx : 0;
            p.walk = (p.walk || 0) + flip * vx;
            p.step = 0.8 * (p.step || 0) + 0.2 * (7 * Math.sqrt(Math.min(9, Math.abs(vx))) * (p.og ? 1 : 0));
            const fill = flash ? '#f55' : `hsl(${p.hue},55%,75%)`;
            ctx.save();
            ctx.translate(s.x, s.y);
            const leg = (cycle, off, stroke) => {
                const hx = 12 + off, hy = 24 + off;
                const ang = 0.034 * p.walk + cycle;
                const fx = 2.2 * p.step * Math.cos(ang) + off;
                const fy = Math.min(yOff + HT, off + 1.2 * p.step * Math.sin(ang) + yOff + HT);
                const dx = fx - hx, dy = fy - hy, d = Math.max(1, Math.hypot(dx, dy));
                const l = (L1 * L1 - L2 * L2 + d * d) / (2 * d), h = Math.sqrt(Math.max(0, L1 * L1 - l * l));
                const kx = (l / d) * dx - (h / d) * dy + hx + off, ky = (l / d) * dy + (h / d) * dx + hy;
                ctx.save(); ctx.scale(flip, 1);
                ctx.beginPath(); ctx.moveTo(hx, hy); ctx.lineTo(kx, ky); ctx.lineTo(fx, fy);
                ctx.strokeStyle = stroke; ctx.lineWidth = 5; ctx.stroke();
                const tx = p.og ? 14 : 12, ty = p.og ? 5 : 8;
                ctx.beginPath(); ctx.moveTo(fx, fy); ctx.lineTo(fx - tx, fy + ty); ctx.moveTo(fx, fy); ctx.lineTo(fx + tx, fy + ty);
                ctx.lineWidth = 4; ctx.stroke();
                ctx.beginPath(); ctx.arc(hx, hy, 9, 0, 2 * Math.PI);
                ctx.moveTo(kx + 5, ky); ctx.arc(kx, ky, 5, 0, 2 * Math.PI);
                ctx.moveTo(fx + 4, fy + 1); ctx.arc(fx, fy + 1, 4, 0, 2 * Math.PI);
                ctx.fillStyle = fill; ctx.fill(); ctx.strokeStyle = stroke; ctx.lineWidth = 2; ctx.stroke();
                ctx.restore();
            };
            leg(Math.PI, -3, '#4a4a4a');
            leg(0, 0, '#333');
            ctx.rotate(s.a);
            ctx.beginPath(); ctx.moveTo(22, 0); ctx.lineTo(44, 0); ctx.lineCap = 'round'; ctx.lineWidth = 8; ctx.strokeStyle = '#333'; ctx.stroke();   // gun
            ctx.beginPath(); ctx.arc(0, 0, 30, 0, 2 * Math.PI);
            ctx.fillStyle = fill; ctx.fill();
            ctx.strokeStyle = '#333'; ctx.lineWidth = 2; ctx.stroke();
            ctx.beginPath(); ctx.arc(15, 0, 4, 0, 2 * Math.PI); ctx.stroke();
            ctx.restore();
        }
        function makeGhost(p) {
            const before = mob.length;
            S.creatingGhost = true;
            try { mobs.spawn(0, 0, 12, 30, 'rgba(0,0,0,0)'); } catch (e) { return null; }
            finally { S.creatingGhost = false; }
            const g = mob[mob.length - 1]; if (!g || mob.length === before) return null;
            g.isGhost = true; g.gid = p.id; g.alive = true; g.health = 1; g.damageReduction = 1;
            g.isBadTarget = true; g.isDropPowerUp = false; g.showHealthBar = false; g.leaveBody = false; g.isUnblockable = true;
            g.locatePlayer = NOOP; g.foundPlayer = NOOP; g.death = NOOP;
            g.collisionFilter.category = cat.mob; g.collisionFilter.mask = cat.bullet | cat.body;
            Body.setStatic(g, true);
            g.damage = function (d) {
                const pp = S.peers.get(this.gid);
                if (!pp || !S.pvp || !pp.pvp || !pp.alive || peerPaused(pp) || !Number.isFinite(d)) return;   // paused players are invulnerable
                pvpOut.set(pp.id, (pvpOut.get(pp.id) || 0) + d * CFG.pvpScale);
                this._flash = 4;
            };
            g.do = guard('ghost.do', function () {
                const pp = S.peers.get(this.gid); if (!pp) return;
                const pz = peerPaused(pp);
                this.isInvulnerable = pz || !(S.pvp && pp.pvp && pp.alive);
                if (!pz) drawPeerBullets(pp);
                const s = pp.cur; if (!s || !pp.alive) return;
                ctx.save();
                if (pz) ctx.globalAlpha = 0.4;
                drawRemotePlayer(pp, s, this._flash > 0);
                if (this._flash > 0) this._flash--;
                const w = 60, hp = Math.max(0, Math.min(1, (pp.hp || 0) / Math.max(0.0001, pp.mhp || 1)));
                ctx.fillStyle = 'rgba(100,100,100,0.4)'; ctx.fillRect(s.x - w / 2, s.y - 55, w, 6);
                ctx.fillStyle = 'rgba(255,0,0,0.75)'; ctx.fillRect(s.x - w / 2, s.y - 55, w * hp, 6);
                ctx.fillStyle = '#000'; ctx.font = '24px Arial'; ctx.textAlign = 'center'; ctx.fillText(pp.name + (pz ? ' (paused)' : ''), s.x, s.y - 65);
                ctx.restore();
            });
            ghosts.set(p.id, g); return g;
        }
        function removeGhost(id) {
            const g = ghosts.get(id); if (!g) return;
            ghosts.delete(id); removeBodyAndConstraints(g);
            const i = mob.indexOf(g); if (i !== -1) mob.splice(i, 1);
        }
        function destroyGhosts() { for (const id of [...ghosts.keys()]) removeGhost(id); }
        function maintainGhosts() {
            for (const p of S.peers.values()) {
                const want = S.inGame && !S.loading && p.buf.length && p.lc === LC();
                if (want && !ghosts.has(p.id)) makeGhost(p);
                else if (!want && ghosts.has(p.id)) removeGhost(p.id);
            }
        }
        function drawPeerBullets(p) {
            const a = p.bl; if (!a || !a.length) return;
            const fr = Math.min(6, (now() - p.blAt) / 16.7);
            const fill = (typeof color !== 'undefined' && color.bullet) || '#000';
            for (let i = 0; i + 7 < a.length; i += 8) {
                const x = a[i] + a[i + 2] / 10 * fr, y = a[i + 1] + a[i + 3] / 10 * fr;
                ctx.save(); ctx.fillStyle = fill; ctx.beginPath();
                if (a[i + 4] === 0) ctx.arc(x, y, Math.max(1.5, a[i + 6]), 0, 2 * Math.PI);
                else { ctx.translate(x, y); ctx.rotate(a[i + 5] / 100); ctx.rect(-a[i + 6] / 2, -a[i + 7] / 2, a[i + 6], a[i + 7]); }
                ctx.fill(); ctx.restore();
            }
        }
        // smooth ghosts + puppet mobs right after each physics step
        Matter.Events.on(engine, 'afterUpdate', guard('afterUpdate', () => {
            const t = now() - CFG.interpMs;
            for (const [pid, g] of ghosts) {
                const p = S.peers.get(pid); if (!p || !p.buf.length) continue;
                let s;
                if (peerPaused(p)) {
                    // paused (pause menu / upgrade screen): no extrapolation, and a player paused in mid-air falls to the floor instead of hovering
                    const L = p.buf[p.buf.length - 1];
                    if (p.fy === undefined) { p.fy = 0; p.fv = 0; }
                    if (!p.og) {
                        p.fv = Math.min(p.fv + 0.35, 25);
                        let hit = false;
                        try { hit = Matter.Query.ray(map, { x: L.x, y: L.y + p.fy }, { x: L.x, y: L.y + p.fy + 55 + p.fv }).length > 0; } catch (e) { hit = true; }
                        if (hit) p.fv = 0; else p.fy += p.fv;
                    }
                    s = { x: L.x, y: L.y + p.fy, vx: 0, vy: 0, a: L.a };
                } else {
                    p.fy = undefined; p.fv = 0;
                    s = sample(p.buf, t);
                }
                if (!s) continue; p.cur = s;
                Body.setPosition(g, { x: s.x, y: s.y });
            }
            if (!S.isHost) for (const mo of mobMap.values()) {
                if (!mo._buf || !mo._buf.length || !mo.alive) continue;
                const s = sample(mo._buf, t); if (!s) continue;
                Body.setPosition(mo, { x: s.x, y: s.y }); Body.setVelocity(mo, { x: s.vx, y: s.vy }); Body.setAngle(mo, s.a);
            }
        }));

        // ------------------------------------------------------------------ sending
        function localPlayer() {
            const pos = m.pos || player.position, mi = simulation.mouseInGame || { x: 0, y: 0 };
            const pz = S.paused;
            return [q(pos.x), q(pos.y), pz ? 0 : q(player.velocity.x, 100), pz ? 0 : q(player.velocity.y, 100), q(m.angle, 1000), m.alive ? 1 : 0,
            b.activeGun == null ? 255 : b.activeGun, m.fieldMode == null ? 255 : m.fieldMode, q(mi.x), q(mi.y),
            q(m.health, 1000), q(m.maxHealth, 1000), S.pvp ? 1 : 0, m.onGround ? 1 : 0, q(m.yOff), pz ? 1 : 0];
        }
        function bulletSnap() {
            const out = [], n = bullet.length;
            if (S.paused) return out;
            for (let i = Math.max(0, n - CFG.maxBullets); i < n; i++) {
                const bl = bullet[i]; if (!bl || !bl.position) continue;
                let kind = 0, w = 0, h = 0; const vt = bl.vertices;
                if (bl.circleRadius) w = bl.circleRadius;
                else if (vt && vt.length === 4) { kind = 1; w = Math.hypot(vt[1].x - vt[0].x, vt[1].y - vt[0].y); h = Math.hypot(vt[2].x - vt[1].x, vt[2].y - vt[1].y); }
                else if (bl.bounds) w = (bl.bounds.max.x - bl.bounds.min.x) / 2;
                if (w < 0.5) continue;
                out.push(q(bl.position.x), q(bl.position.y), q(bl.velocity.x, 10), q(bl.velocity.y, 10), kind, q(bl.angle, 100), q(w, 10) / 10, q(h, 10) / 10);
            }
            return out;
        }
        function sendState() {
            const pkt = { t: 's', lc: LC(), p: localPlayer(), bl: bulletSnap() };
            const bk = [];
            for (const bd of bodyMap.values()) {
                // Include non-holdable shared doors and moving level machinery too.
                if (S.isHost) { if (bd._owner !== null && bd._owner !== S.id) continue; }
                else if (bd._owner !== S.id) continue;
                const x = q(bd.position.x, 10), y = q(bd.position.y, 10), a = q(bd.angle, 1000);
                const last = bd._mpLast;
                const changed = !last || Math.abs(last[0] - x) > 1 || Math.abs(last[1] - y) > 1 || Math.abs(last[2] - a) > 2;
                const mv = bd.speed > 0.15 || Math.abs(bd.angularSpeed) > 0.002 || bd === m.holdingTarget;
                // Some n-gon doors/platforms are static Matter bodies moved with setPosition().
                // Their Matter speed remains zero, so compare transforms rather than speed alone.
                const periodic = S.isHost && S.tickN % 10 === 0;
                if (changed || mv || !bd._rest || periodic) {
                    bk.push([bd._nid, x, y, a, q(bd.velocity.x, 100), q(bd.velocity.y, 100), q(bd.angularVelocity, 1000)]);
                    bd._mpLast = [x, y, a]; bd._rest = !mv && !changed;
                }
                if (bk.length >= 120) break;
            }
            if (bk.length) pkt.bk = bk;
            if (S.isHost) {
                pkt.cy = simulation.cycle; pkt.fi = simulation.fpsInterval;
                const mm = scanMapMovers(); if (mm && mm.length) pkt.mm = mm;
                const mo = [];
                for (const mb of mob) {
                    if (!mb || mb.isGhost || mb._nid === undefined || !mb.alive) continue;
                    const x = q(mb.position.x), y = q(mb.position.y), hp = q(mb.health, 1000), l = mb._ls;
                    if (!l || Math.abs(l[0] - x) + Math.abs(l[1] - y) > 1 || l[2] !== hp || S.tickN % 20 === 0) {
                        mo.push([mb._nid, x, y, q(mb.velocity.x, 100), q(mb.velocity.y, 100), q(mb.angle, 1000), hp]); mb._ls = [x, y, hp];
                    }
                    if (mo.length >= 300) break;
                }
                if (mo.length) pkt.mo = mo;
            }
            sendSt(pkt);
        }
        function flush() {
            const lc = LC();
            if (spawnQ.length) { sendEv({ t: 'sp', lc, l: spawnQ }); spawnQ = []; }
            if (deathQ.length) { sendEv({ t: 'md', l: deathQ }); deathQ = []; }
            if (opsQ.length) { sendEv({ t: 'bk', lc, l: opsQ }); opsQ = []; }
            if (dropQ.length) { sendEv({ t: 'pd', lc, l: dropQ }); dropQ = []; }
            if (dmgOut.size) {
                const l = []; for (const [id, e] of dmgOut) l.push([id, e[0], e[1]]);
                dmgOut.clear(); sendEv({ t: 'dm', l }, S.hostId);
            }
            if (pvpOut.size) { for (const [id, d] of pvpOut) sendEv({ t: 'pvp', d }, id); pvpOut.clear(); }
        }
        // am I paused? (pause menu, upgrade screen, hidden tab, or the game loop simply stopped advancing)
        function updatePaused() {
            const c = simulation.cycle;
            S.stuck = (c === S.lastCycle) ? S.stuck + 1 : 0; S.lastCycle = c;
            const was = S.paused;
            S.paused = !!(S.inGame && (simulation.paused === true || document.hidden || S.stuck >= 4));
            if (S.paused && !was) S.pausedAt = now();
        }
        // keep simulation.cycle close to the host's (cycle-driven moving platforms / timers)
        function syncCycle() {
            const h = S.hostCy;
            if (!CFG.syncCycle || S.isHost || S.paused || !h || h.lc !== LC() || now() - h.t > 400 || simulation.clearNow) return;
            if (!Number.isFinite(h.cy)) return;
            if (h.fi != null && simulation.fpsInterval != null && Math.abs(Number(h.fi) - simulation.fpsInterval) > 1) return;   // different fps caps: cycles are not comparable
            // simulation.cycle advances at the game's configured update cadence.
            // Extrapolate using the host's actual frame interval rather than assuming 60 Hz.
            const hostStep = Number.isFinite(Number(h.fi)) && Number(h.fi) > 0 ? Number(h.fi) :
                (Number.isFinite(simulation.fpsInterval) && simulation.fpsInterval > 0 ? simulation.fpsInterval : 1000 / 60);
            const exp = h.cy + (now() - h.t) / hostStep, diff = exp - simulation.cycle;
            if (Math.abs(diff) > 30) simulation.cycle = Math.round(exp);
            else if (Math.abs(diff) > 6) simulation.cycle += Math.sign(diff);
        }
        function tick() {
            S.tickN++;
            try {
                updatePaused();
                levelWatch();
                if (!S.inGame || S.loading || S.solo) return;
                wrapSpawns();
                if (S.tickN % 4 === 0 && S.id && computeHost() !== S.hostId) refreshRole();   // hand the host role to / back from an active player
                maintainGhosts(); checkMc(); runCatchup();
                if (!hasPeers()) { opsQ = []; dropQ = []; spawnQ = []; deathQ = []; dmgOut.clear(); pvpOut.clear(); scanWorld(); return; }
                syncCycle();
                scanWorld(); flush(); sendState();
                if (S.isHost && hasPeers() && !S.paused) {
                    const t = now();
                    if (t - S.lastRosterAt > 2000) { S.lastRosterAt = t; sendMobRoster(); }
                    if (t - S.lastButtonSnapshotAt > 500) { S.lastButtonSnapshotAt = t; sendButtonSnapshot(); }
                }
            } catch (e) { const n = errCount.tick = (errCount.tick | 0) + 1; if (n <= 3) console.warn('[MP] tick', e); }
        }
        setInterval(tick, CFG.tickMs);

        // ------------------------------------------------------------------ chat + UI
        function say(text, isHtml) {
            const msg = isHtml ? text : esc(text);
            try { if (simulation.inGameConsole) simulation.inGameConsole(msg); else console.log('[MP]', text); } catch (e) { }
        }
        const ui = (function () {
            const mk = (tag, txt, parent, cls) => {
                const e = document.createElement(tag);
                if (txt) e.textContent = txt;
                if (cls) e.className = cls;
                if (parent) parent.appendChild(e);
                return e;
            };
            const css = document.createElement('style');
            css.textContent = `
#mp-panel{width:min(350px,calc(100vw - 24px));max-height:55vh;overflow:auto;box-sizing:border-box;font:13px Arial,sans-serif;color:#eee;background:var(--card-color,rgba(20,24,30,.96));border:1px solid rgba(255,255,255,.22);border-radius:8px;padding:10px;margin-top:6px;box-shadow:0 6px 24px rgba(0,0,0,.25)}
#mp-namebar{position:fixed;top:10px;right:12px;z-index:9998;display:flex;gap:5px;align-items:center;padding:6px 8px;border:1px solid rgba(255,255,255,.2);border-radius:8px;background:rgba(20,24,30,.9);color:#eee;font:12px Arial,sans-serif;backdrop-filter:blur(8px)}
#mp-namebar input{width:130px;max-width:30vw;background:#101318;color:#fff;border:1px solid #59616c;border-radius:5px;padding:5px}
#mp-namebar button,#mp-panel button{background:#343d49;color:#f5f5f5;border:1px solid #657080;border-radius:5px;padding:5px 9px;cursor:pointer}
#mp-notice{position:fixed;right:14px;top:54px;z-index:10001;width:min(340px,calc(100vw - 28px));padding:12px;background:rgba(24,29,37,.98);color:#fff;border:1px solid #647184;border-radius:10px;box-shadow:0 8px 28px rgba(0,0,0,.45);font:13px Arial,sans-serif}
#mp-notice strong{display:block;margin-bottom:5px;font-size:14px}#mp-notice .actions{display:flex;gap:7px;margin-top:10px}#mp-notice button{flex:1;padding:7px;border-radius:6px;border:1px solid #68778b;background:#394657;color:white;cursor:pointer}#mp-notice button.primary{background:#287a58;border-color:#43a77b}
#mp-panel *{box-sizing:border-box}
#mp-panel h3{margin:0 0 6px;font-size:15px;display:flex;justify-content:space-between;align-items:center}
#mp-panel .r{display:flex;gap:4px;align-items:center;margin:5px 0;flex-wrap:wrap}
#mp-panel input[type=text]{flex:1;min-width:0;padding:3px 5px;background:#111820;color:#fff;border:1px solid #586474;border-radius:5px}
#mp-panel button{cursor:pointer;padding:2px 8px}
#mp-panel .pl{display:flex;align-items:center;gap:6px;padding:7px 2px;border-top:1px solid rgba(255,255,255,.13)}
#mp-panel .pl .nm{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:bold}
#mp-panel .pl .sub{font-size:11px;color:#aab3c0;font-weight:normal}
#mp-panel .muted{color:#aab3c0;font-size:12px}
#mp-panel .dot{width:8px;height:8px;border-radius:50%;background:#3a3;flex:none}
#multiplayer-details>summary{cursor:pointer;pointer-events:auto}
@media(max-width:600px){#mp-namebar{top:8px;right:8px}#mp-namebar input{width:95px}#mp-panel{max-height:45vh}}
`;
            document.head.appendChild(css);

            const details = document.getElementById('multiplayer-details');
            if (!details) {
                console.error('[MP] #multiplayer-details is missing from index.html');
            }
            const panel = document.createElement('div');
            panel.id = 'mp-panel';
            panel.className = 'details-div';
            if (details) details.appendChild(panel);

            const namebar = document.createElement('div');
            namebar.id = 'mp-namebar';
            mk('span', 'Username', namebar);
            const topName = mk('input', '', namebar);
            topName.type = 'text'; topName.maxLength = 20;
            topName.value = S.baseName; topName.placeholder = 'username';
            const topSet = mk('button', 'Set', namebar);
            document.body.appendChild(namebar);

            const mkStop = e => e.stopPropagation();
            const notice = document.createElement('div');
            notice.id = 'mp-notice'; notice.style.display = 'none';
            document.body.appendChild(notice);
            for (const ev of ['keydown','keyup','keypress','mousedown','mouseup','pointerdown','pointerup','wheel','contextmenu','click','dblclick']) {
                panel.addEventListener(ev, mkStop);
                namebar.addEventListener(ev, mkStop);
                notice.addEventListener(ev, mkStop);
            }

            const h = mk('h3', '', panel);
            mk('span', 'Online players', h);
            const me = mk('div', '', panel, 'muted');
            const list = mk('div', '', panel);
            const r = mk('div', '', panel, 'r');
            const t1 = mk('label', '', r);
            const tcb = mk('input', '', t1); tcb.type = 'checkbox'; tcb.checked = S.together;
            mk('span', ' stay together', t1);
            const t2 = mk('label', '', r);
            const pcb = mk('input', '', t2); pcb.type = 'checkbox'; pcb.checked = S.pvp;
            mk('span', ' pvp', t2);
            const st = mk('div', 'Status: ...', panel, 'muted');
            tcb.onchange = () => { S.together = tcb.checked; };
            pcb.onchange = () => { S.pvp = pcb.checked; };

            const applyName = () => {
                const n = cleanName(topName.value);
                if (!n) return;
                try { localStorage.setItem('p2pUsername', n); } catch (e) {}
                startPeer(n);
            };
            topSet.onclick = applyName;
            topName.addEventListener('keydown', e => { if (e.key === 'Enter') applyName(); });

            if (details) {
                details.addEventListener('toggle', () => {
                    try { localStorage.setItem('ngonmp_open', details.open ? '1' : '0'); } catch (e) {}
                });
                try { details.open = localStorage.getItem('ngonmp_open') === '1'; } catch (e) {}
            }

            const seed = seedEl();
            if (seed) seed.addEventListener('input', () => { if (!S.inGame) sendEv({ t: 'seed', seed: getSeed() }); });

            function refreshDir() {
                const users = [...dir.values()].sort((a, b) => a.name.localeCompare(b.name));
                const summary = details && details.querySelector('summary');
                if (summary) summary.textContent = 'multiplayer (' + Math.max(users.length, S.id ? 1 : 0) + ' online)';
                list.textContent = '';
                if (!users.length) mk('div', S.id ? 'Looking for other players...' : 'Connecting...', list, 'muted');
                for (const u of users) {
                    const p = S.peers.get(u.id), conn = !!(p && p.ev && p.ev.open);
                    const row = mk('div', '', list, 'pl');
                    mk('span', '', row, 'dot').style.background = u.g ? '#3a3' : '#aaa';
                    const nm = mk('span', '', row, 'nm');
                    nm.textContent = u.name + (u.id === S.id ? ' (you)' : '');
                    mk('div', u.g ? 'level ' + (u.lc + 1) : 'in menu', nm, 'sub').style.display = 'block';
                    if (u.id === S.id) continue;
                    if (conn) mk('span', 'connected', row, 'muted');
                    else {
                        const jb = mk('button', 'Request to join', row);
                        jb.title = 'Ask this player for permission to join';
                        jb.onclick = () => requestJoin(u.id);
                        const ib = mk('button', 'Invite', row);
                        ib.title = 'Invite this player to your session';
                        ib.onclick = () => invitePlayer(u.id, u.name);
                    }
                }
            }
            function refresh() {
                const open = openPeers();
                const people = S.id ? (open.length ? 'connected to ' + open.map(p => p.name).join(', ') + ' (' + (open.length + 1) + ' players, you are the ' + (S.isHost ? 'host' : 'client') + ')' : 'not connected to anyone yet') : 'connecting...';
                st.textContent = 'Status: ' + people;
                refreshDir();
            }
            function notify(title, message, accept, decline) {
                notice.textContent = '';
                mk('strong', title, notice);
                mk('div', message, notice);
                const actions = mk('div', '', notice, 'actions');
                const yes = mk('button', accept ? 'Accept' : 'OK', actions);
                yes.className = 'primary';
                yes.onclick = () => { notice.style.display = 'none'; if (accept) accept(); };
                if (decline) {
                    const no = mk('button', 'Decline', actions);
                    no.onclick = () => { notice.style.display = 'none'; decline(); };
                }
                notice.style.display = 'block';
            }
            return {
                setId(id) {
                    me.textContent = 'Your session ID: ' + id;
                    if (document.activeElement !== topName) topName.value = S.baseName;
                },
                status(s) { st.textContent = 'Status: ' + s; },
                notify, refresh, refreshDir
            };
        })();

        // chat: Enter opens a box
        (function () {
            const inp = document.createElement('input'); inp.maxLength = 200; inp.placeholder = 'chat (Enter to send, Esc to cancel)';
            inp.style.cssText = 'display:none;position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);width:min(70vw,800px);z-index:9999;padding:10px;font-size:16px;background:#e8e8e8cf;border:0;';
            document.body.appendChild(inp);
            let open = false;
            const close = () => { open = false; inp.style.display = 'none'; inp.blur(); };
            document.addEventListener('keydown', e => {
                if (open) {
                    e.stopPropagation();
                    if (e.key === 'Enter') { const t = inp.value.trim(); if (t) { sendEv({ t: 'chat', x: t }); say(esc(S.name) + ': ' + esc(t), true); } close(); e.preventDefault(); }
                    else if (e.key === 'Escape') { close(); e.preventDefault(); }
                    return;
                }
                if (e.key === 'Enter') {
                    const t = e.target; const typing = t && (t.tagName === 'TEXTAREA' || t.isContentEditable || (t.tagName === 'INPUT' && !['button', 'submit', 'checkbox', 'radio', 'range', 'color', 'file'].includes(t.type)));
                    if (!typing && S.inGame) { e.preventDefault(); e.stopPropagation(); open = true; inp.value = ''; inp.style.display = 'block'; setTimeout(() => inp.focus(), 0); }
                }
            }, true);
        })();

        // ------------------------------------------------------------------ install
        const gameRunning = () => typeof simulation.onTitlePage === 'boolean' ? !simulation.onTitlePage : (() => { const sp = document.getElementById('splash'); return sp ? getComputedStyle(sp).display === 'none' : false; })();
        for (const key of ['spawnRandomPowerUp', 'spawnBossPowerUp', 'spawnTechPowerUps']) {
            if (typeof powerUps[key] !== 'function') continue;
            wrapFn(powerUps, key, 'powerUps.' + key, orig => function () {
                S.dropCtx = (S.dropCtx | 0) + 1;
                try { return orig.apply(this, arguments); } finally { S.dropCtx--; }
            });
        }
        const recordDrop = guard('drop.record', (name, before) => {
            if (!(S.dropCtx > 0) || !S.isHost || S.replayDrop || !hasPeers() || powerUp.length <= before) return;
            const pu = powerUp[powerUp.length - 1];
            if (pu && pu.position) dropQ.push([String(name), q(pu.position.x), q(pu.position.y), q(pu.size)]);
        });
        wrapFn(powerUps, 'directSpawn', 'powerUps.directSpawn', orig => function (x, y, name) {
            const before = powerUp.length;
            const r = orig.apply(this, arguments);
            recordDrop(name, before);
            return r;
        });
        wrapSpawns();
        wrapFn(mobs, 'spawn', 'mobs.spawn.authority', orig => function () {
            if (!S.isHost && !S.buildingLevel && !S.replay && !S.creatingGhost) return undefined;
            return orig.apply(this, arguments);
        });
        wrapButtons();
        wrapPopulateLevels();
        wrapLevelFrameRandom();
        wrapNewFeatures();

        // Keep n-gon's native 72 Hz simulation speed regardless of the selected FPS cap.
        // The original game advances one simulation cycle per rendered frame, so selecting
        // 60/45/30 FPS also slows the simulation. This accumulator runs fixed 72 Hz updates
        // and lets requestAnimationFrame render at whatever cadence the display supports.
        (function installFixedRateSimulation() {
            const FIXED_STEP_MS = 1000 / 72;
            let lastFrameTime = null;
            let accumulator = 0;

            // Keep the public interval consistent for multiplayer cycle synchronization.
            try {
                Object.defineProperty(simulation, 'fpsInterval', {
                    configurable: true,
                    enumerable: true,
                    get() { return FIXED_STEP_MS; },
                    set(_value) { /* FPS preference no longer changes simulation speed. */ }
                });
            } catch (e) {
                simulation.fpsInterval = FIXED_STEP_MS;
            }

            function fixedRateCycle(timestamp) {
                if (simulation.paused) {
                    lastFrameTime = null;
                    accumulator = 0;
                    return;
                }

                requestAnimationFrame(fixedRateCycle);

                const frameTime = Number.isFinite(timestamp) ? timestamp : performance.now();

                // Starting a new run resets the accumulator, then immediately performs
                // the first cycle so the game's clearMap()/level.start() startup still runs.
                if (simulation.clearNow) {
                    lastFrameTime = frameTime;
                    accumulator = FIXED_STEP_MS;
                } else if (lastFrameTime === null) {
                    lastFrameTime = frameTime;
                    accumulator = 0;
                    return;
                } else {
                    const elapsed = Math.max(0, Math.min(250, frameTime - lastFrameTime));
                    lastFrameTime = frameTime;
                    accumulator += elapsed;
                }

                // Catch up when the display/selected cap is below 72 Hz.
                // The cap prevents a long background-tab pause from causing an unbounded loop.
                let steps = 0;
                while (accumulator + 0.001 >= FIXED_STEP_MS && steps < 18 && !simulation.paused) {
                    accumulator -= FIXED_STEP_MS;
                    steps++;

                    simulation.cycle++;
                    m.cycle++;
                    if (input.fire || input.field) m.lastFireFieldCycle = m.cycle;

                    try {
                        if (simulation.clearNow) {
                            simulation.clearNow = false;
                            simulation.clearMap();
                            level.start();
                            consoleMirror.showTitleLogs();
                        }
                        if (simulation.extraCycles) simulation.timeSkip(simulation.extraCycles);
                        simulation.loop();
                    } catch (error) {
                        consoleMirror.showError(error);
                        consoleMirror.isShownByLoop = true;
                        throw error;
                    }
                }
            }

            if (typeof window.cycle === 'function') {
                window.cycle = fixedRateCycle;
            } else {
                console.warn('[MP] Could not replace the game cycle function; using a fixed 72 Hz interval as fallback.');
                simulation.fpsInterval = FIXED_STEP_MS;
            }
            simulation.fpsInterval = FIXED_STEP_MS;
        })();

        if (gameRunning()) { S.inGame = true; S.runSeed = String(Math.initialSeed != null ? Math.initialSeed : getSeed()); guard('initial.load', afterLevelLoaded)(); }
        setInterval(guard('detect', () => {
            const run = gameRunning();
            if (!S.inGame && !S.loading && run) { S.inGame = true; if (S.runSeed == null) S.runSeed = String(Math.initialSeed != null ? Math.initialSeed : getSeed()); afterLevelLoaded(); }
            else if (S.inGame && !run && typeof simulation.onTitlePage === 'boolean') { S.inGame = false; S.loading = false; S.paused = false; if (S.solo) { S.solo = false; refreshRole(); } destroyGhosts(); resetSync(); }   // back on the title screen
        }), 500);
        startPeer(S.baseName);
        window.ngonMP = {
            S, peers: S.peers, dir, ghosts, mobMap, connect: connectTo, join: joinByName, rename: startPeer, hooks: HOOKS,
            diag() {   // paste the output of ngonMP.diag() if something does not sync in your n-gon build
                const g = n => { try { return (0, eval)('typeof ' + n); } catch (e) { return 'error'; } };
                const o = {
                    hooks: HOOKS,
                    globals: { simulation: g('simulation'), level: g('level'), levelData: g('levelData'), levelEditor: g('levelEditor'), saveGame: g('saveGame'), map: g('map'), body: g('body'), mob: g('mob') },
                    fns: { 'level.button': typeof level.button, 'level.nextLevel': typeof level.nextLevel, 'simulation.clearMap': typeof simulation.clearMap, 'simulation.startGame': typeof simulation.startGame },
                    state: { id: S.id, host: S.hostId, isHost: S.isHost, inGame: S.inGame, solo: S.solo, level: LC(), onLevel: String(level.onLevel), runSeed: S.runSeed, mapBodies: S.mapIds ? S.mapIds.size : 0, buttons: S.buttons.length, peers: openPeers().map(p => p.name) }
                };
                console.log('[MP] diag', JSON.stringify(o, null, 1)); return o;
            }
        };
        console.log('[MP] n-gon multiplayer v8 ready - use Multiplayer at the bottom-left to see players.');
    }

    whenReady(() => loadPeer(guard('init', init)));
})();
