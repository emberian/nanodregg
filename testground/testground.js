// testground.js — the desktop. Pixels only: windows, a taskbar, a terminal per member, dialogs.
// Every word a window shows is printed by the member's own follow (Lean) or is a name from the
// kernel's table; this file lays it out and never decides what it means.
import factory from './kernel.mjs';
import { compositor } from './compositor.js';
import { element as $, confirmAction, submitForm, listen, disposeEvents } from './toolkit.js';
import { loadKernel, client, genesis, hex, quoteArg } from './nd.js';
import { joinIn, resumeIn, rosterOf, worldOf, httpOf } from './hosted.mjs';
import { demos, runDemo, lieScenes, memberLies, runScene, head0Of, outcomeOf } from './demos.js';
import { teach } from './teach.js';
import { residentDriver } from './resident.js';

const short = (h) => (h && h.length > 12 ? `${h.slice(0, 8)}…` : h);
// a two-column table of labelled values (STYLE.md: a labelled value instead of a sentence)
const kv = (pairs) => $('table', { class: 'props sunken' }, pairs.filter(Boolean).map(([k, ...v]) => $('tr', {}, $('td', {}, k), $('td', {}, ...v))));
// the terms a window uses, defined in that window (STYLE.md)
const glossed = (pairs) => $('details', { class: 'terms' }, $('summary', {}, 'What these words mean'), $('dl', {}, pairs.flatMap(([t, d]) => [$('dt', {}, t), $('dd', {}, d)])));

// ---------------------------------------------------------------- the window manager
const desk = document.getElementById('desktop'), tasks = document.getElementById('tasks');
const { wins, focus, openWindow, clear: clearWindows } = compositor({ desk, tasks, $, dispose: disposeEvents });

// ---------------------------------------------------------------- the World in this tab
const boot = document.getElementById('boot-line');
let K, nd, world, frames = [], cmdNo = 0, raceArmed = null, lie = 'honest', forging = false;
let activity = null;
const stopped = Symbol('stopped');
const yieldUI = () => new Promise(resolve => { const timer = setTimeout(resolve, 40); requestAnimationFrame(() => { clearTimeout(timer); setTimeout(resolve, 0); }); });
const t0 = performance.now();
// The kernel is fetched once, hashed, and those bytes are the module instantiated: the sha256 the World
// window shows is of the kernel this tab runs. kernel.json (build.sh) names the commit it was built from;
// deployment.json (testground/build/publish.sh) names this deployment's live World. Either may be absent
// (a local build): the page says so and runs the World in the tab.
const fetchJson = async (p) => { try { const r = await fetch(p, { cache: 'no-cache' }); return r.ok ? await r.json() : null; } catch { return null; } };
const kernelBytes = new Uint8Array(await (await fetch(new URL('./kernel.wasm', import.meta.url))).arrayBuffer());
let kernelSha = '';
try { kernelSha = hex(new Uint8Array(await crypto.subtle.digest('SHA-256', kernelBytes))); } catch { /* no WebCrypto (an insecure origin): shown as unknown */ }
const [built, deployment] = await Promise.all([fetchJson('kernel.json'), fetchJson('deployment.json')]);
// `live: "self"`: the page is served by the live World's own host (the demo box), so its relay is this
// page's origin at /ws; any other value is the relay's address
const LIVE = deployment?.live === 'self' ? `${location.protocol === 'https:' ? 'wss' : 'ws'}://${location.host}/ws` : deployment?.live ?? '';
K = await loadKernel(factory, { wasmBinary: kernelBytes });
const loadMs = performance.now() - t0;
document.getElementById('boot').remove();
// the teaching windows (teach.js): every member of every World in the tab
const allMembers = () => [...(world?.members ?? []), ...Object.values(world?.extra ?? {}).flatMap((x) => x.members)];
const T = teach({ $, readIn: (m, argv) => inMember(m, () => (m.nd ?? nd).run(m, argv)), K: () => K, nd: () => nd, openWindow, wins, runIn: (...a) => runIn(...a), members: allMembers, short,
  prefill: (...a) => prefill(...a), splitArgv: (s) => splitArgv(s),
  raceArm: (m, other, argv) => { raceArmed = { member: m.name, other, argv }; } });

// ---------------------------------------------------------------- a membership this browser keeps
// A hosted World's member is a record (hosted.mjs recordOf: the relay, the origin, the invitation and
// sponsor key it accepted, its seeds, its ids), kept in localStorage per relay so that a visitor who
// comes back is the same member. The seeds are a toy World's member keys, readable by any script on
// this page's origin; "Forget me" deletes them. Storage may be refused (a private window): then the
// membership lasts as long as the tab.
const kept = {
  key: (url) => `nd-testground/member ${url}`,
  get(url) { try { return JSON.parse(localStorage.getItem(this.key(url)) ?? 'null'); } catch { return null; } },
  put(url, rec) { try { localStorage.setItem(this.key(url), JSON.stringify(rec)); return true; } catch { return false; } },
  forget(url) { try { localStorage.removeItem(this.key(url)); } catch { /* nothing kept */ } },
};

function clearDesk() { clearWindows(); }
function newWorld() {
  if (activity) {
    activity.cancelled = true;
    activity.status.textContent = 'Stopping after the current command. Start the new World when it finishes.';
    return false;
  }
  frames = []; logSel = -1; cmdNo = 0; lie = 'honest'; raceArmed = null; setTray();
  clearDesk(); terms.clear(); tourAt = 0; T.reset();
  const t = performance.now();
  world = genesis(K, 'testground', ['alice', 'bob']);
  world.ms = performance.now() - t;
  world.height = 0; world.objects = new Map();
  nd = client(K, {
    onFrame: (f) => { frames.push({ n: frames.length, cmd: cmdNo, lie, forged: forging, ...f }); renderLog(); },
    beforeSubmit: async (m) => {
      if (!raceArmed || raceArmed.member !== m.name) return;
      const r = raceArmed; raceArmed = null;
      await runIn(r.other, r.argv, `while ${m.name}'s call waits to be sent`);
    },
  });
  refreshIcons(); openWorld(); openLog(); world.members.forEach((m, i) => openTerm(m, 700, 16 + i * 380)); openTour();
}

// ---------------------------------------------------------------- the World's properties
function openWorld() {
  if (world.hosted) return openHosted();
  const lines = world.text.trim().split('\n');
  const rows = lines.map((l) => { const w = l.split(' '); return $('tr', {}, $('td', {}, w[0] === 'founder' ? `founder ${w[1]}` : w[0]), $('td', {}, w[0] === 'founder' ? `${world.members[+w[1]].name}: member ${w[3]}  grant ${w[5]}` : w.slice(1).join(' '))); });
  const body = $('div', {},
    $('table', { class: 'props sunken' }, rows),
    kv([['kernel load', `${loadMs.toFixed(0)} ms`], ['genesis', `${world.ms.toFixed(0)} ms`], ['runs in', 'this tab: one writer, one follow per member'], ...kernelPairs()]),
    glossed([
      ['World', 'One shared ledger: a set of cells (objects) and a log of the calls that changed them.'],
      ['writer', 'The process that orders calls into the log. It is not trusted.'],
      ['follow', 'A member\'s own copy of the World. It replays the log and checks every entry.'],
      ['Turn', 'One admitted call and its effects: one entry (event) in the log.'],
      ['origin', 'Hash of the genesis input. It names the World.'],
      ['nonce', 'Random bytes in the genesis input, so two Worlds never share an origin.'],
      ['founder N', 'A member created at genesis: its member id and its grant on the World.'],
      ['member', 'A key holder. Its id is a hash of its key.'],
      ['grant', 'A cell that gives one member rights on one target (observe, mutate, invoke:N, …).'],
      ['chain', 'Hash chain over the log. Two follows with the same chain hold the same history.'],
      ['chain0, roots0', 'The chain and the state roots (hash of all cells) at genesis.'],
      ['authority', 'Certifiers of the World\'s head: count and threshold. 0 0 means none.'],
      ...kernelTerms,
    ]),
    confirmAction('New World (genesis)', 'Discard this local World and its commands?', () => newWorld()), ' ',
    LIVE ? [$('button', { class: 'btn', onclick: () => liveDoor() }, doorLabel()), ' '] : '',
    $('button', { class: 'btn', onclick: () => joinHosted() }, 'Join a hosted World…'),
    writerMenu());
  openWindow({ id: 'world', title: 'World', x: 110, y: 16, w: 570, body });
}

// The kernel this tab runs: the sha256 this tab computed of the bytes it instantiated, and kernel.json's
// commit. A visitor ties the tab to a commit by building it (build.sh: content-named objects, a sorted
// link, one sha256 per tree) and comparing.
function kernelPairs() {
  const commit = built?.commit, repo = deployment?.repo;
  return [
    ['kernel sha256', kernelSha || 'unknown (no WebCrypto on this origin)'],
    ['kernel size', `${kernelBytes.length.toLocaleString()} bytes`],
    ['built from', !built ? $('span', { class: 'warn' }, 'no kernel.json (a local build)')
      : [repo ? $('a', { class: 'cmd', href: `${repo}/commit/${commit}`, target: '_blank', rel: 'noopener' }, `nanodregg ${commit}`) : `nanodregg ${commit}`,
         built.tree === 'clean' ? '' : $('span', { class: 'warn' }, ' (with uncommitted changes)'), `; Lean ${built.lean}, emcc ${built.emcc}`]],
    built && built.sha256 !== kernelSha ? ['kernel.json sha256', $('span', { class: 'bad' }, `${built.sha256} (does not match this tab's kernel)`)] : null,
  ];
}
const kernelTerms = [['kernel sha256', 'Hash of the kernel.wasm this tab downloaded and runs. testground/build/build.sh at the commit shown makes the same hash.']];

// ---------------------------------------------------------------- (B) a hosted World
// The same page with one function swapped: the writer is a real `host serve` behind a WebSocket
// relay (deploy/testground/ws-relay.py, bytes only); this tab's member still re-derives every step
// in its own follow. It joins over the guest-book's invitation (Invite.accept under the sponsor key
// world.json names), is enrolled by the guest-book (a member like any other), and then is a member.
// The trust caveat (DESIGN-TESTGROUND §7): whoever serves this page and world.json chooses the kernel
// and the sponsor key; this is a demonstration of the check, not a trust anchor.
const hostedDefault = () => new URLSearchParams(location.search).get('hosted') ?? '';
const doorLabel = () => (kept.get(LIVE) ? 'Return to the live World' : 'Join the live World');
// The door: this deployment's live World (deployment.json's `live`, stamped at publish time), joined
// or, when this browser kept a membership of it, returned to. `?live` in the address is the door too.
function liveDoor() {
  if (!LIVE) return;
  history.replaceState(null, '', `${location.pathname}?live`);
  joinHosted(LIVE);
}
function openJoin(value = hostedDefault() || LIVE || 'ws://127.0.0.1:8787/ws', error = '') {
  const url = $('input', { type: 'url', required: true, value, 'aria-label': 'Relay address' });
  const status = $('p', { role: 'status', class: 'bad' }, error);
  const go = async () => {
    if (!/^wss?:\/\/[^/]+\/ws$/.test(url.value.trim())) { status.textContent = 'Enter ws://HOST/ws or wss://HOST/ws.'; return; }
    await joinHosted(url.value.trim());
  };
  const body = submitForm(go, $('label', {}, 'Relay address ', url), $('button', { class: 'btn', type: 'submit' }, 'Join'), status);
  const w = openWindow({ id: 'join', title: 'Hosted World', w: 480, h: 200, body, dialog: true });
  url.focus();
  return w;
}
async function joinHosted(url = null) {
  if (activity) { activity.status.textContent = 'Cancel the demo before joining another World.'; return; }
  if (url == null) return openJoin();
  if (!url) return;
  let wj;
  try { wj = await worldOf(url); } catch (e) { openJoin(url, `Cannot read the World: ${e.message}`); return; }
  // a saved membership of a World this relay no longer serves (a new genesis: a new origin) is not resumed
  let rec = kept.get(url), stale = null;
  if (rec && rec.origin !== wj.origin) { stale = rec; rec = null; kept.forget(url); }
  clearDesk();
  frames = []; logSel = -1; cmdNo = 0; lie = 'honest'; raceArmed = null; setTray();
  const onFrame = (f) => { frames.push({ n: frames.length, cmd: cmdNo, lie, ...f }); renderLog(); };
  world = { hosted: true, url, wj, origin: wj.origin, members: [], objects: new Map(), text: '' };
  const enter = (m) => { world.members = [m]; world.origin = m.origin; refreshIcons(); openHosted(); openLog(); openTerm(m, 700, 16); openTour(); };
  if (rec) {
    let me = null;
    try { me = resumeIn(K, rec, 'you', { onFrame }); } catch (e) { stale = rec; kept.forget(url); }
    if (me) {
      enter(me);
      print(me, $('div', { class: 'ok' }, `Welcome back. You are member ${short(me.id)}. Your keys were saved in this browser on ${rec.joined?.slice(0, 10) ?? 'your first visit'}. Your follow replays the log from the invitation and checks every entry.`));
      const s = await runIn(me, ['sync'], 'replay the log since the invitation');
      if (s.exit === 'ok' && !rosterOf(K, me).members.includes(me.id))
        print(me, $('div', { class: 'bad' }, `Your follow's World has no member ${short(me.id)}. This World does not hold the saved membership. Use Forget me, then join again.`));
      renderRoster(); refreshDoor();
      return;
    }
  }
  let me;
  try {
    me = await joinIn(K, url, wj, 'you', { onFrame, run: (m, argv, why) => runIn(m, argv, why), say: (m) => {
      enter(m);
      if (stale) print(m, $('div', { class: 'warn' }, `This browser saved a membership of World ${short(stale.origin)}. The relay now serves a different World (a new genesis). The old membership is deleted.`));
      print(m, $('div', { class: 'dim' }, `Joined by invitation. World origin ${short(m.origin)}. The invitation was checked against the sponsor key in world.json. Asking the guest-book (the member that enrols new members) to enrol you.`));
    } });
  } catch (e) {
    if (world.members[0]) print(world.members[0], $('div', { class: 'bad' }, e.message), explain(e.message) ? $('div', { class: 'dim' }, explain(e.message)) : ''); else openJoin(url, e.message);
    return;
  }
  const stored = kept.put(url, me.record);
  print(me, $('div', { class: 'ok' }, `Enrolled. member ${short(me.id)}, grant ${short(me.grant)}. The writer runs elsewhere. Your follow checks each of its replies.`),
    $('div', { class: 'dim' }, stored ? 'Your keys and membership are saved in this browser. Open this page again and you are the same member. Forget me deletes them.' : 'This browser does not allow storage. The membership ends when this tab closes.'));
  openHosted(); refreshDoor();
  await runIn(me, ['sync']);
}
// the roster: the members of the World as YOUR follow folded it (tg_members), refreshed after every command
function renderRoster() {
  const box = document.getElementById('roster'); if (!box || !world.hosted || !world.members[0]) return;
  const me = world.members[0], r = rosterOf(K, me);
  const label = (id) => (id === me.id ? 'you' : id === world.wj.sponsor ? 'guest-book' : 'member');
  const shown = r.members.slice(0, 60);
  box.replaceChildren(
    kv([['members', `${r.members.length}`], ['height', `${r.height ?? '—'}`], r.refused ? ['refused', $('span', { class: 'bad' }, r.refused)] : null]),
    $('div', { class: 'sunken', style: 'max-height:120px;overflow:auto' }, $('table', { class: 'props' }, shown.map((id) => $('tr', {}, $('td', {}, label(id)),
      $('td', {}, $('a', { class: 'hex', title: id, onclick: () => openObject(me, id) }, short(id))))),
      r.members.length > shown.length ? $('tr', {}, $('td', {}, ''), $('td', {}, `and ${r.members.length - shown.length} more`)) : '')),
    $('div', { class: 'dim' }, 'Read from your follow\'s copy of the World. A World knows members by key, so other members are ids. ',
      $('a', { class: 'cmd', onclick: () => runIn(me, ['sync'], 'new members since') }, 'sync'), ' to update.'));
}
function refreshIcons() {
  const a = document.getElementById('icon-m0'), b = document.getElementById('icon-m1');
  if (!a || !b) return;
  a.querySelector('.label').textContent = world.hosted ? 'you' : 'alice'; a.querySelector('.glyph').textContent = world.hosted ? 'y' : 'a';
  b.hidden = !!world.hosted;
}
function refreshDoor() { const l = document.getElementById('door-label'); if (l) l.textContent = doorLabel(); }
function forgetMe() {
  kept.forget(world.url); refreshDoor();
  history.replaceState(null, '', location.pathname);
  newWorld();
}
function openHosted() {
  const me = world.members[0];
  const body = $('div', {},
    kv([['relay', world.url === LIVE ? `${world.url} (live World)` : world.url], ['origin', world.origin], ['sponsor', `${world.wj.sponsor} (guest-book)`],
      ['you', me.id ? `member ${me.id}  grant ${me.grant}` : 'not enrolled'],
      ['saved', me.id && kept.get(world.url)?.member === me.id ? 'your keys and membership, in this browser' : 'nothing'], ...kernelPairs()]),
    $('fieldset', { class: 'writer' }, $('legend', {}, 'Members'), $('div', { id: 'roster' }, 'syncing')),
    $('p', { class: 'dim' }, 'The writer is a host serve process on another machine. This tab holds your keys and your follow. The follow checks each step before your key signs. The Frames window lists every frame you send and each reply. Another browser is another member.'),
    glossed([['relay', 'Forwards frames between this tab and the writer. It is not trusted.'], ['guest-book', 'The member that enrols new members.'],
      ['sponsor', 'The member whose key signed the invitation.'], ['follow', 'Your own copy of the World. It replays the log and checks every entry.'],
      ['saved', 'Your seeds, member id and invitation in this browser\'s storage (localStorage). Any page on this site can read them.'],
      ['members', 'The member cells in your follow\'s copy of the World. The writer does not supply this list.'], ...kernelTerms]),
    relayMenu(me), forkCheck(me),
    $('button', { class: 'btn', onclick: () => { history.replaceState(null, '', location.pathname); newWorld(); } }, 'Local World'), ' ',
    me.id && kept.get(world.url) ? confirmAction('Forget me', 'Delete the saved membership? A new join makes a new member.', () => forgetMe()) : '');
  openWindow({ id: 'world', title: world.url === LIVE ? 'Live World' : 'Hosted World', x: 110, y: 16, w: 570, body });
  renderRoster();
}

// ---------------------------------------------------------------- the Writer menu: the writer lies
// Each lie is a conformance row's own plant, switched on in the kernel (K.lie); the row and the
// outcome it expects come from the kernel's menu (K.lies), read off Protocol.Rows.rows.
const lieTitle = (n) => (lieScenes[n] ?? memberLies[n])?.title ?? (n === 'neverForward' ? 'drops the call (a loss, not a lie)' : n);
const rowOf = (n) => K.lies.find((l) => l.name === n);
function setLie(name) {
  const r = K.lie(name);
  if (r[0] !== K.table.statuses.find((x) => x.name === 'ok').code) return;
  lie = name; setTray();
  const sel = document.getElementById('writer-lie'); if (sel) sel.value = name;
  const note = document.getElementById('writer-note'); if (note) note.replaceChildren(...lieNote(name));
}
function lieNote(name) {
  if (name === 'honest') return [world?.hosted ? 'The relay forwards every frame unchanged. Your follow checks every reply in any case.' : 'The writer runs unmodified. Every follow checks what it serves in any case.'];
  const r = rowOf(name);
  return [$('b', { class: 'bad' }, `${world?.hosted ? 'Relay' : 'Writer'}: ${lieTitle(name)}.`), ' ', r?.row ? `Conformance row ${r.row} (a scripted test in Protocol.Rows), line ${r.line}, expects: ` : '', r?.row ? $('code', {}, r.expect) : '',
    '. Entries logged during the lie stay in the log after you switch back.'];
}
function writerMenu() {
  const sel = $('select', { id: 'writer-lie', 'aria-label': 'what the writer does', onchange: (e) => setLie(e.target.value) },
    $('option', { value: 'honest' }, 'is honest'),
    K.lies.filter((l) => l.kind !== 'member').map((l) => $('option', { value: l.name }, `${lieTitle(l.name)}  (${l.kind})`)));
  sel.value = lie;
  const scenes = [...Object.keys(lieScenes), ...Object.keys(memberLies)];
  return $('fieldset', { class: 'writer' }, $('legend', {}, 'Writer'),
    $('div', {}, 'The writer ', sel, ' ', $('span', { class: 'dim' }, 'reset follow (cold): '), world.members.map((m) => $('button', { class: 'btn', title: `reset ${m.name}'s follow to genesis`, onclick: () => { K.cold(m.index); print(m, $('div', { class: 'warn' }, `${m.name}'s follow is reset to genesis. Its next command replays and re-checks every Turn.`)); } }, m.name))),
    $('div', { id: 'writer-note', class: 'dim' }, ...lieNote(lie)),
    $('div', {}, 'Run a row\'s scene on a new World: ', scenes.map((n) => confirmAction(n, 'Discard this local World and its commands?', () => playLie(n)))));
}
// The fork across two tabs (PROTOCOL-74): another writer of this World's genesis (deploy/testground/
// run.sh fork) has the same origin and the same guest-book founder. Its guest-book's attestation (its
// head, signed) is checked by THIS tab's follow: cold, catching up through the attested position on
// this writer's log, and comparing chains (`sync --check`). The other tab is any tab joined there.
function forkCheck(me) {
  const url = $('input', { class: 'sunken', 'aria-label': 'another writer\'s relay', value: new URLSearchParams(location.search).get('fork') ?? '', placeholder: 'ws://…/ws (another writer, same genesis)', size: 34 });
  const go = async () => {
    const u = url.value.trim();
    if (!/^wss?:\/\/[^/]+\/ws$/.test(u)) { print(me, $('div', { class: 'warn' }, 'Enter the second server\'s address, ws://HOST/ws or wss://HOST/ws.')); return; }
    if (u === world.url) { print(me, $('div', { class: 'warn' }, 'That is your own writer. A history compared with itself always agrees. Enter another writer of this genesis (deploy/testground/run.sh fork starts one).')); return; }
    let a;
    try { a = await (await fetch(`${httpOf(u)}/attest`)).json(); } catch (e) { a = { refused: `no answer from ${httpOf(u)}/attest` }; }
    if (!a.attest) { print(me, $('div', { class: 'bad' }, `No attestation from ${url.value}: ${a.refused}`)); return; }
    K.cold(me.index);
    print(me, $('div', { class: 'warn' }, `Attestation from ${url.value}: the other writer's head, signed by its guest-book. Your follow resets, replays your writer's log up to that position, and compares the two chains.`));
    await runIn(me, ['sync', '--check', a.attest], 'attestation from another writer');
  };
  return $('fieldset', { class: 'writer' }, $('legend', {}, 'Compare histories (fork check)'),
    submitForm(go, url, ' ', $('button', { class: 'btn', type: 'submit' }, 'Compare signed history')),
    $('div', { class: 'dim' }, 'Two writers can serve the same genesis. A follow checks only its own writer. A signed head (attestation) from the other writer shows a fork: refused forkedWorld.'));
}
// A hosted tab's relay: the rows' relay lies, told by this tab's own relay around its socket
// (Web.Sim.Testground.relayPre/relayPost); the writer is the real one and stays honest. A writer lie
// needs the writer in the tab, so only the relay's are offered here.
function relayMenu(me) {
  const sel = $('select', { id: 'writer-lie', 'aria-label': 'what the relay does', onchange: (e) => setLie(e.target.value) },
    $('option', { value: 'honest' }, 'is honest'),
    K.lies.filter((l) => l.kind === 'relay').map((l) => $('option', { value: l.name }, lieTitle(l.name))));
  sel.value = lie;
  return $('fieldset', { class: 'writer' }, $('legend', {}, 'Relay'),
    $('div', {}, 'The relay ', sel, ' ', $('button', { class: 'btn', title: 'reset your follow to the World the invitation made', onclick: () => { K.cold(me.index); print(me, $('div', { class: 'warn' }, 'Your follow is reset. Its next command replays and re-checks every Turn the writer serves through this relay.')); } }, 'reset follow (cold)')),
    $('div', { id: 'writer-note', class: 'dim' }, ...lieNote(lie)),
    $('div', { class: 'dim' }, 'Example: choose "alters an event in the log", press reset follow, run nd sync. The writer logged the true Turn. Your follow checks the altered copy and refuses it (eventMismatch).'));
}
function setTray() {
  const t = document.getElementById('tray-lie'); if (!t) return;
  t.textContent = lie === 'honest' ? 'writer: honest' : `writer: LYING (${lie})`;
  t.className = lie === 'honest' ? '' : 'bad';
}
async function withActivity(name, total, action) {
  if (activity) { wins.get('activity')?.focus(); return { ok: false, busy: true }; }
  const status = $('span', { role: 'status', 'aria-live': 'polite' }, 'Starting.'),
    progress = $('progress', { max: Math.max(1, total), value: 0, 'aria-label': 'Commands completed' });
  const job = { name, total, done: 0, turns: 0, cancelled: false, status };
  const cancel = $('button', { class: 'btn', onclick: () => {
    job.cancelled = true; cancel.disabled = true; status.textContent = 'Stopping after the current command.';
  } }, 'Cancel');
  const w = openWindow({ id: 'activity', title: 'Demo: '+name, w: 420, h: 190,
    body: $('div', {}, progress, $('p', {}, status), cancel),
    onClose: () => { job.cancelled = true; } });
  activity = job;
  job.run = async (action) => {
    await yieldUI();
    if (job.cancelled) throw stopped;
    status.textContent = 'Command '+(job.done+1)+' running. '+job.turns+' Turns completed.';
    const r = await action();
    job.done++;
    job.turns += (r?.stdout?.match(/^tx /gm) ?? []).length;
    progress.value = job.done;
    status.textContent = job.done+' commands completed. '+job.turns+' Turns completed.'+(job.cancelled ? ' Stopping.' : '');
    await yieldUI();
    if (job.cancelled) throw stopped;
    return r;
  };
  try {
    const result = await action(job);
    status.textContent = (result.ok ? 'Complete. ' : 'Stopped. ')+job.done+' commands completed. '+job.turns+' Turns completed.';
    return result;
  } catch (e) {
    if (e === stopped) { status.textContent = 'Cancelled. '+job.done+' commands completed. Completed Turns remain in the World.'; return { ok: false, cancelled: true }; }
    status.textContent = 'Stopped: '+e.message;
    throw e;
  } finally {
    cancel.disabled = true;
    if (activity === job) activity = null;
    if (!w.closed) w.setTitle('Demo: '+name);
  }
}
async function playLie(name, opts = {}) {
  if (activity) { wins.get('activity')?.focus(); return { ok: false, busy: true }; }
  if (opts.fresh !== false) newWorld();
  const sc = lieScenes[name] ?? memberLies[name];
  return withActivity(name, sc.steps.length, job => playLieSequence(name, { ...opts, fresh: false }, job));
}
async function playLieSequence(name, { fresh = true, from = 0 } = {}, job) {
  const sc = lieScenes[name] ?? memberLies[name];
  if (fresh) newWorld();
  const by = (n) => world.members.find((m) => m.name === n);
  const origin = world.text.match(/^origin (\S+)/m)[1];
  const fetchText = async (p) => (p.startsWith('kernel:') ? new TextDecoder().decode(K.text(p.slice(7)).slice(1)) : (await fetch(p)).text());
  const r = await runScene({ ...sc, steps: sc.steps.slice(from) }, { fetchText, members: world.members, origin, head0: head0Of(world.text), act: async (s, v) => job.run(async () => {
    const m = s.who ? by(s.who) : null;
    if (s.say) print(m ?? world.members[0], $('div', { class: 'warn' }, s.say));
    if (s.lie) { setLie(s.lie); return null; }
    if (s.cold) { K.cold(by(s.cold).index); print(by(s.cold), $('div', { class: 'dim' }, `${s.cold}'s follow is reset to genesis.`)); return null; }
    if (s.forge) return runIn(m, s.forge(v), 'hostile client: signed without the follow\'s check', { forge: true, quiet: true });
    if (s.cancel) return runIn(m, ['cancel', hex(by(s.cancel).last)], '', { quiet: s.check });
    return runIn(m, s.argv(v), '', { quiet: s.check || s.expect });
  }) });
  const row = rowOf(name) ?? {};
  if (r.ok) caught(name, r, row, (r.r && world.members.find((x) => x.name === sc.steps.find((x) => x.check)?.who)) || world.members.find((x) => x.name === 'bob') || world.members[0]); else print(world.members[0], $('div', { class: 'bad' }, `scene ${name} stopped: ${r.r?.exit} ${r.r?.stderr ?? ''}`));
  return r;
}
// the verdict of a scene's checked line: what the member's own follow said, beside what the row expects
function caught(name, r, row, m) {
  const fs = frames.filter((f) => f.cmd === cmdNo);
  const member = row.kind === 'member';
  const liar = member ? frames.filter((f) => f.forged).at(-1)
    : fs.filter((f) => f.lied).at(-1) ?? fs.filter((f) => f.to === 'writer' && f.op === 'log').at(-1);
  const by = member ? 'a member (hostile client)' : row.kind === 'relay' ? 'the relay between the member and the writer' : 'the writer';
  const title = r.outcome === 'ok' ? 'The false reply had no effect: the follow confirmed the call itself' : 'Rejected by the follow';
  print(m, $('div', { class: `result ${r.outcome === 'ok' ? 'ok' : 'bad'}` },
    $('b', {}, `${title}: ${r.outcome}`),
    kv([['fault', `${by}: ${lieTitle(name)}`],
      member ? ['writer', 'unmodified; it admitted the call, because laws judge the new state, not the history'] : null,
      ...(r.r.stderr || '').trim().split('\n').filter((l) => l && l !== r.outcome).map((l) => ['detail', l]),
      liar ? ['frame', $('a', { class: 'cmd', onclick: () => { logSel = liar.n; openLog(); } }, `#${liar.n} ${liar.who} → ${liar.to} ${liar.op}`), member ? ' (the hostile call)' : liar.lied ? ' (altered by the relay)' : ' (from the writer)'] : null,
      row.row ? ['expected', `${row.expect} (regression test ${row.row}, line ${row.line})`, r.outcome === row.expect ? '' : $('b', { class: 'bad' }, ' — this tab said otherwise')] : null]),
    explain(r.outcome) ? $('div', {}, explain(r.outcome)) : ''));
  if (liar) { logSel = liar.n; renderLog(); }
}

// ---------------------------------------------------------------- a member's terminal
function linkify(text, m) {
  // every 64-hex id becomes a link that opens the object as a window; a line `tx …` names a
  // transaction, which is not a cell, so it stays text
  return text.split(/(\n)/).flatMap((line) => {
    // a `tx` line names a step of the log: it opens the Turn view
    if (line.startsWith('tx ') && /^tx [0-9a-f]{64}$/.test(line)) return ['tx ', $('a', { class: 'hex', title: `Turn ${line.slice(3)}`, onclick: () => T.openTurn(m, line.slice(3)) }, short(line.slice(3)))];
    if (line.startsWith('tx ') || line.startsWith('join ') || line.startsWith('invite ')) return [line];
    // an id opens the window for its kind (teach.js idLink); a hash that names no cell stays text
    return line.split(/([0-9a-f]{64})/).map((part) => (/^[0-9a-f]{64}$/.test(part) ? T.idLink(m, part) : part));
  });
}
const commandText = (argv) => argv.map(quoteArg).join(' ');
function splitArgv(s) {
  const out = []; let cur = '', q = null, any = false;
  for (const c of s) {
    if (q) { if (c === q) q = null; else cur += c; }
    else if (c === '"' || c === "'") { q = c; any = true; }
    else if (/\s/.test(c)) { if (cur || any) { out.push(cur); cur = ''; any = false; } }
    else cur += c;
  }
  if (cur || any) out.push(cur);
  return out;
}
const terms = new Map();
function openTerm(m, x, y) {
  // reopening a terminal shows the one that exists: its transcript and history are kept
  const open = wins.get(`term-${m.name}`);
  if (open && terms.has(m.name)) { focus(open); return; }
  const out = $('div', { class: 'out sunken', 'aria-live': 'polite' });
  const input = $('input', { class: 'sunken', 'aria-label': `${m.name}'s nd command`, placeholder: 'create   ·   write OBJ 0 hello   ·   read OBJ ?', autocomplete: 'off', spellcheck: 'false' });
  const hist = []; let hi = 0;
  listen(input, 'keydown', (e) => {
    if (e.key === 'ArrowUp') { hi = Math.max(0, hi - 1); input.value = hist[hi] ?? ''; e.preventDefault(); }
    if (e.key === 'ArrowDown') { hi = Math.min(hist.length, hi + 1); input.value = hist[hi] ?? ''; e.preventDefault(); }
  });
  const submit = async () => {
    if (!input.value.trim()) return;
    const line = input.value.trim(); hist.push(line); hi = hist.length; input.value = '';
    const argv = splitArgv(line.replace(/^nd\s+/, ''));
    await runIn(m, argv, '', { typed: line.replace(/^nd\s+/, '') });
  };
  const body = $('div', { class: 'term' }, out, submitForm(submit, $('div', { class: 'line' }, $('span', { class: 'prompt' }, `${m.name}$ nd`), input, $('button', { class: 'btn', type: 'submit' }, 'Run'))));
  terms.set(m.name, { out, m });
  openWindow({ onClose: () => terms.delete(m.name), id: `term-${m.name}`, title: `${m.name}${m.world ? ` (World ${m.world})` : ''}`, x, y, w: 520, body });
  const commands = 'Commands: create · write OBJ SLOT "TEXT" · read OBJ [?] · grant OBJ MEMBER RIGHTS · invoke OBJ METHOD "ARGUMENT" · sync · help lists every command. Quote an argument that holds a space.';
  if (world.hosted) print(m, $('span', { class: 'dim' }, `You are a member of a hosted World. Your keys stay in this tab. Your follow (your copy of the World) checks each command before your key signs it.\n${commands}\n`));
  else print(m, $('span', { class: 'dim' }, `You are ${m.name}, founder ${m.index}${m.world ? ` of World ${m.world}` : ''}, member ${short(m.id)}. Your keys stay in this tab. Your follow (your copy of the World) checks each command before your key signs it.\n${commands}\n`));
}
function print(m, ...nodes) {
  const t = terms.get(m.name); if (!t) return;
  const bottom = t.out.scrollHeight - t.out.scrollTop - t.out.clientHeight < 24;
  t.out.append(...nodes);
  if (bottom) t.out.scrollTop = t.out.scrollHeight;
}

// one command at a time per member, as one terminal runs one `nd` at a time: a command typed while
// another is in flight (the hosted join's first sync) waits for it, never interleaves its frames
async function inMember(m, action) {
  const session = world, prev = m.queue ?? Promise.resolve();
  let release; m.queue = new Promise(r => { release = r; });
  await prev;
  try {
    if (session !== world) return { exit: 'client', stdout: '', stderr: 'The World changed before this command ran.\n' };
    return await action();
  } finally { release(); }
}
async function runIn(m, argv, why = '', opts = {}) {
  return inMember(m, () => runOne(m, argv, why, opts));
}
async function runOne(m, argv, why, { forge = false, quiet = false, typed = null } = {}) {
  const session = world;
  cmdNo++;
  // the command as typed, or as the terminal would read it back; a long argument (a package text)
  // is shown folded, and "edit" puts the whole command in the input
  const full = typed ?? commandText(argv);
  const shown = typed ?? argv.map((a) => (a.length > 72 ? `${quoteArg(a).slice(0, 48)}… [${a.length} chars]` : quoteArg(a))).join(' ');
  print(m, $('div', {}, $('b', { class: forge ? 'bad' : '' }, `${m.name}$ ${forge ? 'forge' : 'nd'} ${shown}`),
    forge ? '' : [' ', $('a', { class: 'cmd dim', title: 'put this command in the input', onclick: () => prefill(m, full) }, 'edit')],
    why ? $('span', { class: 'dim' }, `   (${why})`) : ''));
  const n0 = frames.length, t = performance.now();
  let r;
  forging = forge;
  const via = m.nd ?? nd;
  try { r = forge ? await via.forge(m, argv) : await via.run(m, argv); } catch (e) { r = { exit: 'client', stdout: '', stderr: `${e.message}\n` }; }
  forging = false;
  if (session !== world) return r;
  const ms = performance.now() - t;
  const cls = r.exit === 'ok' ? 'ok' : r.exit === 'declined' || r.exit === 'open' || r.exit === 'uncertain' ? 'warn' : 'bad';
  print(m, $('div', {}, ...linkify(r.stdout, m)), r.stderr ? $('div', { class: cls }, r.stderr) : '',
    $('div', { class: 'dim' }, `exit ${r.exit} · ${ms.toFixed(1)} ms · ${frames.length - n0} frames · ${meterOf(m)}`));
  for (const id of (r.stdout.match(/^id ([0-9a-f]{64})/gm) || []).map((l) => l.slice(3))) world.objects.set(id, argv[0]);
  if (argv[0] === 'install' && r.exit === 'ok') { const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (id) T.remember(id, argv[1]); }
  const hm = r.stdout.match(/^height (\d+)/m); if (hm) world.height = +hm[1];
  document.getElementById('tray-height').textContent = `${frames.length} frames · ${cmdNo} commands`;
  if (r.exit !== 'ok') print(m, resultBlock(m, argv, r, frames.slice(n0)));
  flushLog();
  await yieldUI();
  if (session !== world) return r;
  for (const o of [...wins.values()]) if (o.refresh && !o.closed) o.refresh();
  renderRoster();
  tourCheck(m, argv, r);
  return r;
}

// the meter (KERNEL-68), read back from the member's OWN fold as its health receipt (tg_meter: Protocol.Health), not asked of the writer
function meterOf(m) {
  const r = (m.K ?? K).meter(m.index);
  if (r[0] !== K.table.statuses.find((x) => x.name === 'ok').code) return '';
  const kv = Object.fromEntries(new TextDecoder().decode(r.slice(1)).trim().split('\n').map((l) => l.split(' ')));
  // the member's health receipt (Protocol.Health): built from its own fold, read back from its bytes and
  // checked against its own head; the numbers shown are the checked receipt's
  const checked = kv.checked === 'ok' ? 'receipt checks' : `receipt refused: ${kv.checked}`;
  return `ticks ${(+kv.ticks).toLocaleString()} / ${(+kv.budget).toLocaleString()} this window · ${kv.refusals} refusals · ${checked}`;
}

// ---------------------------------------------------------------- refusals are dialogs, by name
// A result that is not plain ok is shown beside the command that made it, in the member's terminal:
// the exact outcome name, what it means, what the writer answered, and links to the rule and the
// object. Nothing interrupts the experiment (CLIENT-51: no result dialogs).
function resultBlock(m, argv, r, fs) {
  const lines = (r.stderr || '').trim().split('\n').filter(Boolean);
  const head = lines.find((l) => l.startsWith(r.exit + ' ')) ?? lines.at(-1) ?? r.exit;
  const kind = { declined: 'Declined', open: 'Call unresolved', uncertain: 'Outcome unknown', refused: 'Refused', client: 'Not run' }[r.exit] ?? r.exit;
  const sub = fs.filter((f) => f.to !== 'follow' && (f.op === 'submit' || f.op === 'lookup')).at(-1);
  const writerSaid = sub ? `${sub.op} → ${sub.status}${sub.status === 'ok' ? '' : ' ' + new TextDecoder().decode(sub.payload)}`
    : 'no call was submitted; the answer came from your follow';
  const hintLaw = (r.stdout.match(/^hint lawDenied ([0-9a-f]{64}): (.*)$/m) || []);
  const target = /^[0-9a-f]{64}$/.test(argv[1] ?? '') ? argv[1] : null;
  const l = fs.filter((f) => f.lied).at(-1);
  const what = r.exit === 'open' ? 'The writer has neither admitted nor refused the call yet. nd sync, or nd receipt CALL, settles it later; cancel CALL withdraws it.'
    : r.exit === 'uncertain' ? 'Your follow could not settle whether the call landed. nd sync and look again.' : explain(head);
  return $('div', { class: `result ${r.exit === 'refused' || r.exit === 'client' ? 'bad' : 'warn'}` },
    $('b', {}, `${kind}: ${head}`),
    what ? $('div', {}, what) : '',
    kv([['writer', writerSaid],
      hintLaw[1] ? ['rule', 'law in package ', T.idLink(m, hintLaw[1]), `: ${hintLaw[2]}`] : null,
      target ? ['object', T.idLink(m, target), ' (unchanged by this command)'] : null,
      lie !== 'honest' ? ['fault on', `${rowOf(lie)?.kind === 'relay' || world.hosted ? 'relay' : 'writer'}: ${lieTitle(lie)}`, l ? `; altered frame #${l.n} (${l.op})` : ''] : null]));
}
// What a refusal's NAME means, for a visitor; the name itself is the kernel's (law 7).
const glossary = {
  stale: 'stale: your call pinned a cell (named the state it expected), and the cell changed before the writer admitted the call. The writer does not apply a call signed over an older state. Run the command again; the follow plans it on the new state.',
  hasMethods: 'hasMethods: this object runs a package. Change it by calling a method (invoke OBJ METHOD "ARGUMENT"), not by writing slots.',
  grantRight: 'grantRight: the grant named with --via does not include the right this call needs (for example invoke:0 when the grant gives invoke:1).',
  usage: 'usage: the command has the wrong arguments. The hint above shows the form; quote an argument that holds a space.',
  unknownVerb: 'unknownVerb: not a command. The hint above lists every command.',
  badPackage: 'badPackage: the text does not read as a package. The hint gives the reader\'s reason and the character offset; the package editor shows the line.',
  noGrant: 'noGrant: you do not own the object and named no grant (--via GRANT) that reaches its owner.',
  missingCell: 'missingCell: no cell with this id in your follow\'s World.',
  idTaken: 'idTaken: a package id is the hash of its bytes. These bytes are already installed.',
  lawDenied: 'lawDenied: a law of the object refused the change. A law compares the old state with the new state.',
  program: 'program: a check inside the method refused. The line above names the check.',
  eventMismatch: 'eventMismatch: an event on the log page does not match the Turn the writer admitted; one byte differs from what was signed. The follow refuses the page and keeps nothing from it.',
  chainMismatch: 'chainMismatch: replaying the page does not produce the chain hash the writer reports. An event is missing, or the writer logged something other than what it served.',
  cancelForged: 'cancelForged: the page has a cancel whose signature is not its member\'s.',
  forkedPost: 'forkedPost: a member posted a head for a step of this World whose chain hash differs from your follow\'s at that step. Two histories claim one World. The page is kept; the post is refused.',
  postBeyondPage: 'postBeyondPage: a member posted a head for a step this World had not reached when the post was admitted. No member of this history held that head: the poster has a longer history of this World, or forged it. The page is kept.',
  hostContradicted: 'hostContradicted: the writer reports one outcome for your call and your follow finds another. The attempt stays open. The writer\'s reply is shown and not acted on.',
  relationFull: 'relationFull: the relation (a table of rows inside the object) is at its row limit; here, the one slot is taken.',
  forkedWorld: 'forkedWorld: the signed head names a chain hash your follow does not have at that step of your writer\'s log. The two writers serve different histories of one genesis.',
  enrollFloor: 'enrollFloor: the guest-book keeps its last enrolments for the operator. This World takes no new members until its next genesis. Enrolled members are not affected. The local World is always open.',
  enrollBudget: 'enrollBudget: the relay enrols at most a few visitors per address per hour. Try again later. A membership saved in this browser needs no enrolment.',
  ticksBudget: 'ticksBudget: this member has spent its ticks for this window. Each Turn records its member and its ticks, and every follow recomputes both, so no writer can charge one member for another. The count restarts each window.',
};
function explain(name) { const w = name.split(' ').find((x) => glossary[x]); return w ? glossary[w] : ''; }

// ---------------------------------------------------------------- objects are windows
// teach.js's inspector: `read OBJ ?` and `read OBJ` as the viewing member's follow prints them, the
// package's text, the object's grants, each law runnable on a change.
function prefill(m, text) {
  const w = wins.get(`term-${m.name}`); if (!w) return;
  focus(w); const input = w.el.querySelector('input'); input.value = text; input.focus();
}
function openObject(m, id, opts) { return T.openInspector(m, id, opts); }
// ---------------------------------------------------------------- the wire, as a scrubbable timeline
let logSel = -1, logFrame = 0;
function openLog() {
  const existing = wins.get('log');
  if (existing) { focus(existing); renderLog(); return; }
  const scrub = $('input', { type: 'range', class: 'scrub', min: 0, max: 0, value: 0, 'aria-label': 'frame' });
  const detail = $('div', {}), list = $('div', { class: 'log sunken', tabindex: '0', 'aria-label': 'Frames', style: 'max-height:240px;overflow:auto' });
  const body = $('div', {}, scrub, detail, list, glossed([
    ['frame', 'One message: member → its follow, or member → writer.'],
    ['op', 'The request kind (command, resume, submit, lookup, log, …).'],
    ['reply', 'The status the receiver answered with.']]));
  const w = openWindow({ id: 'log', title: 'Frames', ...(world?.hosted ? { x: 700, y: 340, w: 520 } : { x: 110, y: 560, w: 570 }), body,
    onClose: () => { cancelAnimationFrame(logFrame); logFrame = 0; } });
  w.view = { scrub, detail, list, shown: new Map(), selected: null };
  listen(scrub, 'input', () => { logSel = +scrub.value; flushLog(); });
  listen(list, 'click', e => {
    const row = e.target.closest('[data-frame]'); if (row) { logSel = +row.dataset.frame; flushLog(); }
  });
  listen(list, 'keydown', e => {
    if (!['ArrowUp', 'ArrowDown', 'Home', 'End'].includes(e.key) || !frames.length) return;
    e.preventDefault();
    const at = logSel < 0 ? frames.length - 1 : logSel;
    logSel = e.key === 'Home' ? Math.max(0, frames.length - 200) : e.key === 'End' ? frames.length - 1
      : Math.max(Math.max(0, frames.length - 200), Math.min(frames.length - 1, at + (e.key === 'ArrowUp' ? -1 : 1)));
    flushLog();
  });
  flushLog();
}
function renderLog() {
  if (!wins.has('log') || logFrame) return;
  logFrame = requestAnimationFrame(() => { logFrame = 0; flushLog(); });
}
function flushLog() {
  const w = wins.get('log'); if (!w?.view) return;
  const { scrub, detail, list, shown } = w.view;
  const follow = logSel < 0, start = Math.max(0, frames.length - 200), selected = follow ? frames.length - 1 : logSel;
  scrub.max = Math.max(0, frames.length - 1); scrub.value = selected;
  for (const [n, el] of shown) if (n < start || n >= frames.length) { el.remove(); shown.delete(n); }
  for (let n = start; n < frames.length; n++) {
    if (shown.has(n)) continue;
    const f = frames[n], row = $('div', { class: 'row', 'data-frame': n },
      $('span', {}, '#'+n), $('span', {}, f.who), $('span', {}, '→'+f.to),
      $('span', { class: 'x' }, f.op), $('span', { class: f.status === 'ok' ? 'ok' : 'bad' }, f.status+' '+f.bytes+'B', f.lied ? $('b', { class: 'lied' }, ' LIED') : '', f.forged ? $('b', { class: 'lied' }, ' FORGED') : ''));
    shown.set(n, row); list.append(row);
  }
  for (const [n, row] of shown) row.classList.toggle('sel', n === selected);
  const sel = frames[selected];
  if (w.view.selected !== sel) {
    w.view.selected = sel;
    detail.replaceChildren(sel ? kv([['frame', '#'+sel.n+' (command '+sel.cmd+')'], ['from → to', sel.who+' → '+sel.to], ['op', sel.op], ['bytes', sel.bytes], ['reply', sel.status],
      sel.lied ? ['lied', $('span', { class: 'bad' }, 'yes: the relay in front of the writer rewrote, answered or withheld this frame')] : null,
      sel.lie && sel.lie !== 'honest' ? ['lie on', sel.lie] : null]) : '');
  }
  if (follow) list.scrollTop = list.scrollHeight;
  else {
    const row = shown.get(selected);
    if (row && (row.offsetTop < list.scrollTop || row.offsetTop + row.offsetHeight > list.scrollTop + list.clientHeight))
      list.scrollTop = row.offsetTop - list.offsetTop;
  }
}

// ---------------------------------------------------------------- the first five minutes
// each step advances only when its command ends with the result it teaches (`want`)
const tour = [
  { say: 'alice creates a cell: an object with numbered slots and no code. She owns it.', argv: () => ['create'], who: 0, want: 'ok', done: (a) => a[0] === 'create' },
  { say: 'alice writes slot 0. Her copy of the World checks the write before her key signs it. If the check fails, nothing is signed.', argv: () => ['write', firstObj(), '0', 'hello from the testground'], who: 0, want: 'ok', done: (a) => a[0] === 'write' },
  { say: 'alice reads the description of the cell. Click any id to open the object.', argv: () => ['read', firstObj(), '?'], who: 0, want: 'ok', done: (a) => a[0] === 'read' },
  { say: 'alice grants bob the right to write the cell (mutate). The grant is a cell with its own id.', argv: () => ['grant', firstObj(), world.members[1].id, 'mutate'], who: 0, want: 'ok', done: (a) => a[0] === 'grant' },
  { say: 'bob writes slot 0 through the grant. His call names the state of the cell it expects (a pin). alice writes slot 0 while his signed call is in transit, so the writer declines his call (stale).', argv: () => ['write', firstObj(), '0', 'bob says hi', '--via', firstGrant()], who: 1, race: true, want: 'declined stale', done: (a, m) => m.name === 'bob' && a[0] === 'write' },
  { say: 'The writer lies: it changes one byte of every event it serves. bob\'s follow resets to genesis and replays the log. It checks each Turn and refuses the altered one (eventMismatch).', argv: () => ['sync'], who: 1, lie: 'flipEvent', want: 'refused eventMismatch', done: (a, m) => m.name === 'bob' && a[0] === 'sync' && lie !== 'honest' },
  // one demo per axis (DESIGN-TESTGROUND §5): each is demos.js's argv, typed into the terminals
  { say: 'A generator: a package whose method installs another package. The generated package has the law n <= 100; setting n = 101 is refused (lawDenied).', demo: 'generator' },
  { say: 'A creator: one call makes a package and an object of it. The object belongs to the member who asked. A second member at the same bound gets a new object of the same package.', demo: 'creator' },
  { say: 'A claim: a package says what it keeps (total <= 100), and install checks that its own law enforces it. A package whose law skips the test on a write is refused (claimUnproved).', demo: 'claims' },
  { say: 'The meter: each Turn records its member and its ticks (evaluator steps). bob repeats an expensive call until his ticks for the window run out (ticksBudget).', demo: 'meter' },
  { say: 'A time lock: a second World (A) runs in this tab. alice\'s lock releases only with a receipt showing that A admitted a call at or after the deadline height.', demo: 'timelock' },
  { say: 'An inbox for an agent: alice rings her Bell (a queue of questions) and names a section of a document as the place for the answer. bob\'s member runs the resident, the program a hosted World runs for a Bell; here only its model is scripted. The answer becomes a proposed text of that section (a candidate) in the same Turn. Her revoke of the Bell\'s grant suspends it (support0 dead). A ring aimed through the revoked grant is withdrawn; the next ring is answered. The Resident window shows each open choice.', demo: 'inbox' },
];
let tourAt = 0;
const firstObj = () => [...world.objects.entries()].find(([, v]) => v === 'create')?.[0] ?? '';
const firstGrant = () => [...world.objects.entries()].find(([, v]) => v === 'grant')?.[0] ?? '';
function tourCheck(m, argv, r) {
  const s = tour[tourAt];
  if (world.hosted || !s || s.demo || !s.done(argv, m)) return;
  if (outcomeOf(r) !== s.want) return;
  tourAt++; openTour(false);
}
// A hosted tab has one member, you; the lesson that needs a second member uses a second tab.
const hostedTour = { at: 0, cell: null, grant: null, wrote: null };
function openHostedTour(activate = true) {
  const me = world.members[0], ht = hostedTour;
  const others = world.hosted && me.id ? rosterOf(K, me).members.filter((id) => id !== me.id && id !== world.wj.sponsor) : [];
  const pick = $('select', { 'aria-label': 'member to grant' }, others.map((id) => $('option', { value: id }, short(id))));
  const run = async (argv, check) => { const r = await runIn(me, argv); if (check(r)) { ht.at++; } openHostedTour(); return r; };
  const steps = [
    ['Create a cell. You own it.', () => $('button', { class: 'btn', onclick: () => run(['create'], (r) => { ht.cell = (r.stdout.match(/^id (\S+)/m) || [])[1]; return !!ht.cell; }) }, 'Run: nd create')],
    ['Open this page in a private window or another browser (a tab of this browser returns as you: your membership is saved here). It joins as a second member. Then press sync here: the second member appears in the Members list of the World window.',
      () => [$('a', { class: 'cmd', href: location.href, target: '_blank' }, 'this page\'s address'), ' ', $('button', { class: 'btn', onclick: () => run(['sync'], () => rosterOf(K, me).members.filter((id) => id !== me.id && id !== world.wj.sponsor).length > 0) }, 'Run: nd sync')]],
    ['Grant the second member the right to write your cell (mutate).', () => others.length ? [pick, ' ', $('button', { class: 'btn', onclick: () => run(['grant', ht.cell, pick.value, 'mutate'], (r) => { ht.grant = (r.stdout.match(/^id (\S+)/m) || [])[1]; return !!ht.grant; }) }, 'Run: nd grant')] : 'No second member yet: open a second tab and sync.'],
    ['In the second window, type this command. Its follow checks it and its key signs it:', () => [$('code', {}, `write ${ht.cell} 0 "from the second window" --via ${ht.grant}`), ' ',
      $('button', { class: 'btn', onclick: () => navigator.clipboard?.writeText(`write ${ht.cell} 0 "from the second window" --via ${ht.grant}`) }, 'copy'), ' then here: ',
      $('button', { class: 'btn', onclick: () => run(['read', ht.cell], (r) => r.exit === 'ok' && /from the second window/.test(r.stdout)) }, 'Run: nd read')]],
  ];
  const items = steps.map(([say, ctl], i) => $('li', { class: i < ht.at ? 'done' : '' }, say, i === ht.at ? $('div', {}, ctl()) : ''));
  openWindow({ activate, id: 'tour', title: 'Tour (hosted World)', x: 110, y: 270, w: 600, body: $('div', { class: 'tour' },
    $('p', {}, 'You are one member of a World whose writer runs on a server. Other visitors are members too. This tour uses a second window as a second member.'), $('ol', {}, items),
    ht.at >= steps.length ? $('p', { class: 'ok' }, 'Done: the second member wrote your cell through your grant, and your follow checked that Turn.') : '') });
}
function openTour(activate = true) {
  if (world.hosted) return openHostedTour(activate);
  const items = tour.map((s, i) => $('li', { class: i < tourAt ? 'done' : '' }, s.say, i === tourAt ? $('div', {},
    $('code', {}, s.demo ? `Demos ▸ ${demos[s.demo].title}` : `${world.members[s.who].name}$ nd ${s.argv().map((a) => short(a)).join(' ')}`), ' ',
    $('button', { class: 'btn', onclick: async () => {
      if (s.demo) { if (lie !== 'honest') setLie('honest'); const r = await playDemo(s.demo); if (r.ok) { tourAt++; openTour(); } return; }
      const m = world.members[s.who];
      if (s.race) raceArmed = { member: m.name, other: world.members[0], argv: ['write', firstObj(), '0', 'alice was here first'] };
      if (s.lie) { const sc = lieScenes[s.lie]; await playLie(s.lie, { fresh: false, from: sc.steps.findIndex((x) => x.lie) }); return; }
      await runIn(m, s.argv());
    } }, 'Run')) : ''));
  openWindow({ activate, id: 'tour', title: 'Tour', x: 110, y: 270, w: 570,
    body: $('div', { class: 'tour' },
      LIVE ? $('p', { class: 'door sunken' }, 'This World runs only in this tab. Nothing you do here reaches anyone else. ',
        $('button', { class: 'btn', onclick: () => liveDoor() }, doorLabel()), ' to work with other visitors. Its writer runs on a public server. Your follow checks each of its replies.') : '',
      $('p', {}, 'One World, two members (alice, bob), all in this tab. Type into their terminals, or press Run on each step.'), $('ol', {}, items),
      tourAt >= tour.length ? $('p', {}, 'More: the Tutorial builds the language up step by step (cells, pins, packages, laws, grants, holes, offers). The Writer menu in the World window turns on each lie the conformance rows test. Or try: write as bob without --via; install a package twice; New World.') : '') });
}

// ---------------------------------------------------------------- demos: command sequences a member types
function openDemos() {
  if (world.hosted) {
    openWindow({ id: 'demos', title: 'Demos', x: 140, y: 300, w: 520, body: $('div', { class: 'tour' },
      $('p', {}, 'These examples need two members, alice and bob, in this tab, so they run in a World in this tab, not in the hosted World.'),
      $('button', { class: 'btn', onclick: () => { history.replaceState(null, '', location.pathname); newWorld(); openDemos(); } }, 'Start a local World')) });
    return;
  }
  const list = Object.entries(demos).map(([k, d]) => $('li', {}, $('b', {}, d.title), ' ',
    $('button', { class: 'btn', onclick: () => playDemo(k) }, 'Run here'), ' ',
    confirmAction('Run on a new World', 'Discard this local World and its commands?', () => { newWorld(); return playDemo(k); }), $('div', { class: 'dim' }, `${d.steps.length} commands`)));
  openWindow({ id: 'demos', title: 'Demos', x: 140, y: 300, w: 520, body: $('div', { class: 'tour' }, $('ol', {}, list), $('p', { class: 'dim' }, 'Run here types the commands into the terminals of the current World; a package it already installed is reused. Run on a new World starts from genesis.')) });
}
// a second World in this tab (the time-lock's clock): its own kernel instance, its own writer, its
// founders' terminals; made once per World in the tab and kept until Re-genesis
async function secondWorld(name, names) {
  world.extra ??= {};
  if (world.extra[name]) return world.extra[name];
  const KW = await loadKernel(factory, { wasmBinary: kernelBytes });
  const g = genesis(KW, name, names);
  const ndW = client(KW, { onFrame: (f) => { frames.push({ n: frames.length, cmd: cmdNo, lie: 'honest', ...f, who: `${f.who}@${name}` }); renderLog(); } });
  for (const m of g.members) { m.K = KW; m.nd = ndW; m.world = name; }
  world.extra[name] = { K: KW, members: g.members, origin: g.text.match(/^origin (\S+)/m)[1] };
  g.members.forEach((m, i) => openTerm(m, 640, 120 + i * 60));
  return world.extra[name];
}
// ---------------------------------------------------------------- the Bell's resident (Web.Sim.Resident)
// The kernel runs the deployed resident's tick and stops at each effect; resident.js performs it. This
// window lays out what each tick did: its commands, its two open choices (holes) with every candidate
// and the facts it cites, its log lines, and what it keeps between ticks.
const residentLog = { m: null, bell: null, ticks: [] };
function residentEvent(m, e) {
  if (e.start) { Object.assign(residentLog, { m, bell: e.start.split(' ').at(-1), ticks: [] }); }
  else { if (!residentLog.ticks.length || residentLog.ticks.at(-1).done) residentLog.ticks.push({ events: [] }); const t = residentLog.ticks.at(-1); t.events.push(e); if (e.end) t.done = true; }
  openResident();
}
const SUPPORT_WORDS = { pending: 'the ring is in this read of the queue', stands: 'its answer was not withdrawn', left: 'the ring is no longer in the queue', waits: 'the ring is still in the queue' };
function supportText(f) { const [k, cell] = f.split(' '); return k === 'gone' ? ['cell ', cell ? T.idLink(residentLog.m, cell) : '', ' is gone'] : SUPPORT_WORDS[k] ?? f; }
function candText(m, c) {
  if (c.ring) return [c.kind === 'ask' ? 'ask the model about ' : 'deliver the kept answer to ', `"${c.ring.text}"`, c.ring.via ? [' (aimed through grant ', T.idLink(m, c.ring.via), ')'] : ''];
  if (c.kind === 'withdraw') return ['withdraw the answer: cell ', T.idLink(m, c.cell), ' is gone'];
  return { idle: 'do nothing this tick', closed: 'forget the answer: the ring left the queue', stop: 'stop the queue (answerRefused)' }[c.kind] ?? c.kind;
}
function holeTable(m, h) {
  const title = h.hole === 'serve' ? 'Open choice serve: which ring to act on' : ['Open choice use: what follows the refused answer to "', h.ring.text, '" (', h.line, ')'];
  return [$('h4', {}, title), $('table', { class: 'props sunken holes' },
    $('tr', {}, $('td', {}, 'candidate'), $('td', {}, 'facts it cites'), $('td', {}, 'usable'), $('td', {}, '')),
    h.cands.map((c) => $('tr', { class: c.chosen ? 'chosen' : '' }, $('td', {}, candText(m, c)),
      $('td', {}, c.supports.length ? c.supports.map((x) => $('div', { class: x.holds ? 'ok' : 'bad' }, supportText(x.fact), x.holds ? ': holds' : ': dead')) : $('span', { class: 'dim' }, 'none')),
      $('td', {}, c.usable ? 'yes' : 'no'), $('td', {}, c.chosen ? $('b', {}, 'chosen') : ''))))];
}
function openResident() {
  const m = residentLog.m;
  if (!m) return;
  const tick = (t, i) => $('div', { class: 'tick' }, $('h4', {}, `Tick ${i + 1}`), t.events.map((e) => {
    if (e.hole) return holeTable(m, e);
    if (e.cmd) return $('div', {}, $('code', {}, `nd ${e.cmd.map(quoteArg).map((a) => (a.length > 40 ? `${a.slice(0, 32)}…` : a)).join(' ')}`), ' → ', e.exit === 'ok' ? 'ok' : $('span', { class: 'bad' }, e.stderr.trim().split('\n')[0] || e.exit));
    if (e.ask) return $('div', {}, `ask the model "${e.ask.text}": `, e.answer == null ? $('span', { class: 'bad' }, 'no answer') : `"${e.answer}" (scripted)`);
    if (e.keep) return $('div', { class: 'dim' }, `keep on the volume: "${e.text}"`);
    if (e.forget) return $('div', { class: 'dim' }, 'forget the kept answer');
    if (e.note) return $('div', { class: 'dim' }, `keep on the volume: ${e.note} withdrawn ring${e.note === 1 ? '' : 's'}`);
    if (e.say) return $('pre', { class: 'src sunken' }, e.say);
    if (e.end) return [$('div', { class: e.end === 'next' ? 'ok' : 'bad' }, e.end === 'next' ? 'tick ends' : `the resident ends: ${e.why}`),
      e.memory.length ? kv(e.memory.map((x) => (x.kept ? ['kept answer', `"${x.kept.text}"`] : ['withdrawn', `"${x.withdrawn.text}" `, 'because cell ', T.idLink(m, x.cell), ' is gone']))) : ''];
    return '';
  }));
  openWindow({ id: 'resident', title: 'Resident', x: 560, y: 60, w: 600, body: $('div', { class: 'inspector' },
    kv([['program', 'Hosting.Resident: the program a hosted World runs for a Bell, run here by the kernel in this tab'], ['member', `${m.name}`], ['Bell', T.idLink(m, residentLog.bell)], ['model', 'scripted: the demo gives the answer to each question']]),
    residentLog.ticks.map(tick),
    glossed([
      ['resident', 'A program that answers a Bell\'s rings. It acts as one member, through that member\'s grant on the Bell.'],
      ['tick', 'One round of the resident: one read of the queue, then at most one question to the model and one answer.'],
      ['open choice (hole)', 'A point in the program where the next step is chosen at run time from a list of candidates.'],
      ['candidate', 'One possible next step. It cites facts. It is usable only if every fact it cites holds in what the resident has just read.'],
      ['withdrawn', 'An answer the resident gave up because a cell it cites is gone (retired). The ring stays in the queue; the resident skips it.'],
    ])) });
}
async function playDemo(name) {
  if (world.hosted) return { ok: false, hosted: true };
  const d = demos[name];
  return withActivity(d.title, d.steps.reduce((n, s) => n + (s.repeat ?? 1), 0), job => playDemoSequence(name, job));
}
async function playDemoSequence(name, job) {
  const t = performance.now();
  const d = demos[name];
  const origin = { B: world.text.match(/^origin (\S+)/m)?.[1] };
  const members = [...world.members];
  for (const [w, names] of Object.entries(d.worlds ?? {})) { const x = await secondWorld(w, names); origin[w] = x.origin; members.push(...x.members); }
  const r = await runDemo(name, {
    fetchText: async (p) => (p.startsWith('kernel:') ? new TextDecoder().decode(K.text(p.slice(7)).slice(1)) : (await fetch(p)).text()),
    members, origin, idOfText: T.idOfText,
    resident: ((d) => ({
      start: (m, a, s) => job.run(async () => { if (s.say) print(m, $('div', { class: 'warn' }, s.say)); return d.start(m, a); }),
      tick: (m, answers, s) => job.run(async () => { if (s.say) print(m, $('div', { class: 'warn' }, s.say)); return d.tick(m, answers); }),
    }))(residentDriver(K, (m, argv) => runIn(m, argv, 'resident'), residentEvent)),
    run: async (m, argv, s) => job.run(async () => {
      if (s.say) print(m, $('div', { class: 'warn' }, s.say));
      const out = await runIn(m, argv, s.again ? `repeat ${s.again}` : '');
      if (s.open) { const id = (out.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (id) openObject(m, id, { activate: false }); }
      return out;
    }),
  });
  print(world.members[0], $('div', { class: r.ok ? 'ok' : 'bad' }, `demo ${name}: ${r.ok ? 'every step as expected' : 'stopped'}, ${((performance.now() - t) / 1000).toFixed(1)} s`));
  return r;
}

// ---------------------------------------------------------------- desktop icons
const icons = document.getElementById('icons');
// one click opens (a double click is the same click twice: the window is focused, not rebuilt)
const icon = (glyph, label, act, id = null) => icons.append($('button', { class: 'icon', ...(id ? { id } : {}), onclick: act }, $('span', { class: 'glyph', 'aria-hidden': 'true' }, glyph), $('span', { class: 'label' }, label)));
icon('◆', 'World', () => openWorld());
icon('a', 'alice', () => openTerm(world.members[0]), 'icon-m0');
icon('b', 'bob', () => world.members[1] && openTerm(world.members[1]), 'icon-m1');
icon('≡', 'Frames', () => openLog());
icon('?', 'Start here', () => openTour());
icon('▶', 'Demos', () => openDemos());
icon('n', 'Lesson', () => T.openLesson());
icon('1', 'Tutorial', () => T.openTutorial());
icon('{', 'Editor', () => T.openEditor());
icon('λ', 'Expressions', () => T.openRepl());
icon('#', 'Cells', () => T.openInventory(world.members[0], [...world.objects.entries()]));
if (LIVE) { icon('◎', doorLabel(), () => liveDoor()); icons.lastChild.querySelector('.label').id = 'door-label'; }
document.getElementById('start').addEventListener('click', () => openWorld());
const q = new URLSearchParams(location.search);
newWorld();
if (q.has('live') && LIVE) liveDoor();
else if (hostedDefault() && q.has('join')) joinHosted(hostedDefault());
window.testground = { desktop: { wins, openWindow, focus }, activity: () => activity && ({ name: activity.name, done: activity.done, turns: activity.turns, cancelled: activity.cancelled }), K, runIn, playDemo, world: () => world, frames: () => frames, hex, kernel: { sha256: kernelSha, built }, deployment, roster: () => (world.hosted ? rosterOf(K, world.members[0]) : null), T };
