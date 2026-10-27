// testground.js — the desktop. Pixels only: windows, a taskbar, a terminal per member, dialogs.
// Every word a window shows is printed by the member's own follow (Lean) or is a name from the
// kernel's table; this file lays it out and never decides what it means.
import factory from './kernel.mjs';
import { loadKernel, client, genesis, custody, rand32, hex, unhex } from './nd.js';
import { framed, wsOpen } from './transport.js';
import { demos, runDemo, lieScenes, memberLies, runScene, head0Of } from './demos.js';

const $ = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v; else if (k.startsWith('on')) e.addEventListener(k.slice(2), v); else e.setAttribute(k, v);
  }
  for (const k of kids.flat()) e.append(k instanceof Node ? k : document.createTextNode(String(k)));
  return e;
};
const short = (h) => (h && h.length > 12 ? `${h.slice(0, 8)}…` : h);
// a two-column table of labelled values (STYLE.md: a labelled value instead of a sentence)
const kv = (pairs) => $('table', { class: 'props sunken' }, pairs.filter(Boolean).map(([k, ...v]) => $('tr', {}, $('td', {}, k), $('td', {}, ...v))));
// the terms a window uses, defined in that window (STYLE.md)
const glossed = (pairs) => $('details', { class: 'terms' }, $('summary', {}, 'Terms'), $('dl', {}, pairs.flatMap(([t, d]) => [$('dt', {}, t), $('dd', {}, d)])));

// ---------------------------------------------------------------- the window manager
const desk = document.getElementById('desktop'), tasks = document.getElementById('tasks');
let zTop = 10, cascade = 0;
const wins = new Map();
function focus(w) {
  for (const o of wins.values()) { o.el.classList.remove('focused'); o.task.classList.remove('on'); }
  w.el.classList.add('focused'); w.task.classList.add('on'); w.el.style.zIndex = ++zTop; w.el.hidden = false;
}
function openWindow({ id, title, x, y, w = 420, body, onClose, dialog = false }) {
  if (wins.has(id)) { const o = wins.get(id); o.setBody(body); o.setTitle(title); focus(o); return o; }
  const bodyBox = $('div', { class: 'body' }, body);
  const titleEl = $('span', { class: 'title' }, title);
  const close = $('button', { title: 'close', 'aria-label': 'close' }, '×');
  const min = dialog ? '' : $('button', { title: 'minimise', 'aria-label': 'minimise' }, '_');
  const bar = $('div', { class: 'titlebar' }, titleEl, min, close);
  const el = $('div', { class: 'window' + (dialog ? ' dialog' : ''), role: dialog ? 'alertdialog' : 'dialog', 'aria-label': title }, bar, bodyBox);
  const pos = cascade++ % 8;
  el.style.left = `${x ?? 110 + pos * 26}px`; el.style.top = `${y ?? 16 + pos * 22}px`; el.style.width = `${w}px`;
  desk.append(el);
  const task = $('button', { title }, title);
  if (!dialog) tasks.append(task);
  const o = { id, el, task, setBody: (b) => bodyBox.replaceChildren(b), setTitle: (t) => { titleEl.textContent = t; task.textContent = t; } };
  wins.set(id, o);
  el.addEventListener('pointerdown', () => focus(o));
  task.addEventListener('click', () => (el.hidden || !el.classList.contains('focused') ? focus(o) : (el.hidden = true)));
  close.addEventListener('click', (e) => { e.stopPropagation(); el.remove(); task.remove(); wins.delete(id); onClose?.(); });
  if (min) min.addEventListener('click', (e) => { e.stopPropagation(); el.hidden = true; task.classList.remove('on'); });
  bar.addEventListener('pointerdown', (e) => {
    if (e.target.tagName === 'BUTTON') return;
    const sx = e.clientX - el.offsetLeft, sy = e.clientY - el.offsetTop;
    const move = (m) => { el.style.left = `${Math.max(0, m.clientX - sx)}px`; el.style.top = `${Math.max(0, m.clientY - sy)}px`; };
    const up = () => { removeEventListener('pointermove', move); removeEventListener('pointerup', up); };
    addEventListener('pointermove', move); addEventListener('pointerup', up);
  });
  focus(o);
  return o;
}

// ---------------------------------------------------------------- the World in this tab
const boot = document.getElementById('boot-line');
let K, nd, world, frames = [], cmdNo = 0, raceArmed = null, lie = 'honest', forging = false;
const t0 = performance.now();
K = await loadKernel(factory);
const loadMs = performance.now() - t0;
document.getElementById('boot').remove();

function newWorld() {
  frames = []; cmdNo = 0; lie = 'honest'; setTray();
  for (const o of [...wins.values()]) { o.el.remove(); o.task.remove(); wins.delete(o.id); }
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
  openWorld(); openLog(); world.members.forEach((m, i) => openTerm(m, 700, 16 + i * 380)); openTour();
}

// ---------------------------------------------------------------- the World's properties
function openWorld() {
  if (world.hosted) return openHosted();
  const lines = world.text.trim().split('\n');
  const rows = lines.map((l) => { const w = l.split(' '); return $('tr', {}, $('td', {}, w[0] === 'founder' ? `founder ${w[1]}` : w[0]), $('td', {}, w[0] === 'founder' ? `${world.members[+w[1]].name}: member ${w[3]}  grant ${w[5]}` : w.slice(1).join(' '))); });
  const body = $('div', {},
    $('table', { class: 'props sunken' }, rows),
    kv([['kernel load', `${loadMs.toFixed(0)} ms`], ['genesis', `${world.ms.toFixed(0)} ms`], ['runs in', 'this tab: one writer, one follow per member']]),
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
    ]),
    $('button', { class: 'btn', onclick: () => newWorld() }, 'New World (genesis)'), ' ',
    $('button', { class: 'btn', onclick: () => joinHosted() }, 'Join a hosted World…'),
    writerMenu());
  openWindow({ id: 'world', title: 'World', x: 110, y: 16, w: 570, body });
}

// ---------------------------------------------------------------- (B) a hosted World
// The same page with one function swapped: the writer is a real `host serve` behind a WebSocket
// relay (deploy/testground/ws-relay.py, bytes only); this tab's member still re-derives every step
// in its own follow. It joins over the guest-book's invitation (Invite.accept under the sponsor key
// world.json names), is enrolled by the guest-book (a member like any other), and then is a member.
// The trust caveat (DESIGN-TESTGROUND §7): whoever serves this page and world.json chooses the kernel
// and the sponsor key; this is a demonstration of the check, not a trust anchor.
const hostedDefault = () => new URLSearchParams(location.search).get('hosted') ?? '';
function httpOf(ws) { return ws.replace(/^ws/, 'http').replace(/\/ws$/, ''); }
async function joinHosted(url = null) {
  url = url ?? prompt('Relay address (wss://…/ws):', hostedDefault() || 'ws://127.0.0.1:8787/ws');
  if (!url) return;
  const say = (t) => { boot.textContent = t; };
  let wj;
  try { wj = await (await fetch(`${httpOf(url)}/world.json`)).json(); } catch (e) { alert(`cannot read ${httpOf(url)}/world.json: ${e.message}`); return; }
  const j = K.join(unhex(wj.invitation), unhex(wj.sponsorKey));
  const text = new TextDecoder().decode(j.slice(1));
  if (j[0] !== K.table.statuses.find((x) => x.name === 'ok').code) { alert(`Invitation refused: ${text}`); return; }
  const jv = Object.fromEntries(text.trim().split('\n').map((l) => l.split(' ')));
  for (const o of [...wins.values()]) { o.el.remove(); o.task.remove(); wins.delete(o.id); }
  frames = []; cmdNo = 0; lie = 'honest'; setTray();
  const host = framed(wsOpen(url), { frameMax: K.table.bounds.frameBytesMax });
  const me = { name: 'you', index: +jv.index, custody: custody(K, [rand32(), rand32(), rand32()]) };
  me.nd = client(K, { host, onFrame: (f) => { frames.push({ n: frames.length, cmd: cmdNo, lie, ...f }); renderLog(); } });
  world = { hosted: true, url, wj, origin: jv.origin, members: [me], objects: new Map(), text: '' };
  openHosted(); openLog(); openTerm(me, 700, 16);
  print(me, $('div', { class: 'dim' }, `Joined by invitation. World origin ${short(jv.origin)}. The invitation was checked against the sponsor key in world.json. Asking the guest-book (the member that enrols new members) to enrol you.`));
  const init = await runIn(me, ['init', wj.sponsor], 'join token, signed by your new key');
  const token = (init.stdout.match(/^join ([0-9a-f]+)/m) || [])[1];
  if (!token) return;
  let en;
  try { en = await (await fetch(`${httpOf(url)}/enroll`, { method: 'POST', body: token })).json(); } catch (e) { en = { refused: e.message }; }
  if (!en.member) { print(me, $('div', { class: 'bad' }, `Not enrolled: ${en.refused}`)); return; }
  K.self(me.index, en.member, en.grant); me.id = en.member; me.grant = en.grant;
  print(me, $('div', { class: 'ok' }, `Enrolled. member ${short(en.member)}, grant ${short(en.grant)}. The writer runs elsewhere. Your follow checks each of its replies.`));
  openHosted();
  await runIn(me, ['sync']);
}
function openHosted() {
  const me = world.members[0];
  const body = $('div', {},
    kv([['relay', world.url], ['origin', world.origin], ['sponsor', `${world.wj.sponsor} (guest-book)`],
      ['you', me.id ? `member ${me.id}  grant ${me.grant}` : 'not enrolled']]),
    $('p', { class: 'dim' }, 'The writer is a host serve process on another machine. This tab holds your keys and your follow. The follow checks each step before your key signs. A second tab of this page is a second member.'),
    glossed([['relay', 'Forwards frames between this tab and the writer. It is not trusted.'], ['guest-book', 'The member that enrols new members.'],
      ['sponsor', 'The member whose key signed the invitation.'], ['follow', 'Your own copy of the World. It replays the log and checks every entry.']]),
    relayMenu(me), forkCheck(me),
    $('button', { class: 'btn', onclick: () => newWorld() }, 'Local World'));
  openWindow({ id: 'world', title: 'Hosted World', x: 110, y: 16, w: 570, body });
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
    $('div', {}, 'Run a row\'s scene on a new World: ', scenes.map((n) => $('button', { class: 'btn', title: lieTitle(n), onclick: () => playLie(n) }, n))));
}
// The fork across two tabs (PROTOCOL-74): another writer of this World's genesis (deploy/testground/
// run.sh fork) has the same origin and the same guest-book founder. Its guest-book's attestation (its
// head, signed) is checked by THIS tab's follow: cold, catching up through the attested position on
// this writer's log, and comparing chains (`sync --check`). The other tab is any tab joined there.
function forkCheck(me) {
  const url = $('input', { class: 'sunken', 'aria-label': 'another writer\'s relay', value: new URLSearchParams(location.search).get('fork') ?? '', placeholder: 'ws://…/ws (another writer, same genesis)', size: 34 });
  const go = async () => {
    let a;
    try { a = await (await fetch(`${httpOf(url.value)}/attest`)).json(); } catch (e) { a = { refused: e.message }; }
    if (!a.attest) { print(me, $('div', { class: 'bad' }, `No attestation from ${url.value}: ${a.refused}`)); return; }
    K.cold(me.index);
    print(me, $('div', { class: 'warn' }, `Attestation from ${url.value}: the other writer's head, signed by its guest-book. Your follow resets, replays your writer's log up to that position, and compares the two chains.`));
    await runIn(me, ['sync', '--check', a.attest], 'attestation from another writer');
  };
  return $('fieldset', { class: 'writer' }, $('legend', {}, 'Fork check'),
    $('div', {}, url, ' ', $('button', { class: 'btn', onclick: go }, 'Check attestation')),
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
async function playLie(name, { fresh = true, from = 0 } = {}) {
  const sc = lieScenes[name] ?? memberLies[name];
  if (fresh) newWorld();
  const by = (n) => world.members.find((m) => m.name === n);
  const origin = world.text.match(/^origin (\S+)/m)[1];
  const fetchText = async (p) => (p.startsWith('kernel:') ? new TextDecoder().decode(K.text(p.slice(7)).slice(1)) : (await fetch(p)).text());
  const r = await runScene({ ...sc, steps: sc.steps.slice(from) }, { fetchText, members: world.members, origin, head0: head0Of(world.text), act: async (s, v) => {
    const m = s.who ? by(s.who) : null;
    if (s.say) print(m ?? world.members[0], $('div', { class: 'warn' }, s.say));
    if (s.lie) { setLie(s.lie); return null; }
    if (s.cold) { K.cold(by(s.cold).index); print(by(s.cold), $('div', { class: 'dim' }, `${s.cold}'s follow is reset to genesis.`)); return null; }
    if (s.forge) return runIn(m, s.forge(v), 'hostile client: signed without the follow\'s check', { forge: true, quiet: true });
    if (s.cancel) return runIn(m, ['cancel', hex(by(s.cancel).last)], '', { quiet: s.check });
    return runIn(m, s.argv(v), '', { quiet: s.check || s.expect });
  } });
  const row = rowOf(name) ?? {};
  if (r.ok) caught(name, r, row); else print(world.members[0], $('div', { class: 'bad' }, `scene ${name} stopped: ${r.r?.exit} ${r.r?.stderr ?? ''}`));
}
// the verdict of a scene's checked line: what the member's own follow said, beside what the row expects
function caught(name, r, row) {
  const fs = frames.filter((f) => f.cmd === cmdNo);
  const member = row.kind === 'member';
  const liar = member ? frames.filter((f) => f.forged).at(-1)
    : fs.filter((f) => f.lied).at(-1) ?? fs.filter((f) => f.to === 'writer' && f.op === 'log').at(-1);
  const match = r.outcome === row.expect;
  const body = $('div', {},
    $('div', { class: 'mark' + (r.outcome === 'ok' ? ' okm' : '') }, r.outcome === 'ok' ? '✓' : '×'),
    $('div', {},
      $('div', { class: 'name' }, r.outcome),
      kv([['lie', member ? `by a member: ${lieTitle(name)}` : `by the writer: ${lieTitle(name)}`],
        member ? ['writer', 'honest; it admitted the call (laws judge the new state, not the history)'] : null,
        ...(r.r.stderr || '').trim().split('\n').filter((l) => l && l !== r.outcome).map((l) => ['detail', l]),
        ['result', r.outcome === 'ok' ? 'ok: the follow decided the call from its own copy of the World, not from the writer\'s reply'
          : `refused by the member's follow: what the writer served does not match ${member ? 'the post' : 'what the writer says'}. Nothing signed depends on it.`],
        liar ? ['lying frame', $('a', { class: 'cmd', onclick: () => { logSel = liar.n; openLog(); } }, `#${liar.n} ${liar.who} → writer ${liar.op}`), member ? ' (hostile call, admitted)' : liar.lied ? ' (rewritten by the relay)' : ' (from the lying writer)'] : null,
        row.row ? ['row expects', `${row.expect} (row ${row.row}, line ${row.line})`] : null,
        row.row ? ['match', $('span', { class: match ? 'ok' : 'bad' }, match ? 'yes' : 'NO')] : null]),
      explain(r.outcome) ? $('p', {}, explain(r.outcome)) : ''),
    $('div', { class: 'actions' }, $('button', { class: 'btn', onclick: () => d.el.querySelector('.titlebar button').click() }, 'OK')));
  const d = openWindow({ id: `caught-${cmdNo}`, title: r.outcome === 'ok' ? 'Lie without effect' : 'Lie caught', x: 240, y: 160, w: 500, body, dialog: true });
  if (liar) { logSel = liar.n; renderLog(); }
}

// ---------------------------------------------------------------- a member's terminal
function linkify(text, m) {
  // every 64-hex id becomes a link that opens the object as a window; a line `tx …` names a
  // transaction, which is not a cell, so it stays text
  return text.split(/(\n)/).flatMap((line) => {
    if (line.startsWith('tx ') || line.startsWith('join ') || line.startsWith('invite ')) return [line];
    return line.split(/([0-9a-f]{64})/).map((part) => {
      if (!/^[0-9a-f]{64}$/.test(part)) return part;
      const who = world.members.find((x) => x.id === part);
      if (who) return $('span', { title: `member ${part}` }, `${who.name}:${short(part)}`);
      return $('a', { class: 'hex', title: part, onclick: () => openObject(m, part) }, short(part));
    });
  });
}
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
  const out = $('div', { class: 'out sunken', 'aria-live': 'polite' });
  const input = $('input', { class: 'sunken', 'aria-label': `${m.name}'s nd command`, placeholder: 'create   ·   write OBJ 0 hello   ·   read OBJ ?', autocomplete: 'off', spellcheck: 'false' });
  const hist = []; let hi = 0;
  input.addEventListener('keydown', async (e) => {
    if (e.key === 'ArrowUp') { hi = Math.max(0, hi - 1); input.value = hist[hi] ?? ''; e.preventDefault(); }
    if (e.key === 'ArrowDown') { hi = Math.min(hist.length, hi + 1); input.value = hist[hi] ?? ''; e.preventDefault(); }
    if (e.key !== 'Enter' || !input.value.trim()) return;
    const line = input.value.trim(); hist.push(line); hi = hist.length; input.value = '';
    const argv = splitArgv(line.replace(/^nd\s+/, ''));
    await runIn(m, argv);
  });
  const body = $('div', { class: 'term' }, out, $('div', { class: 'line' }, $('span', { class: 'prompt' }, `${m.name}$ nd`), input));
  terms.set(m.name, { out, m });
  openWindow({ id: `term-${m.name}`, title: `${m.name}${m.world ? ` (World ${m.world})` : ''}`, x, y, w: 520, body });
  print(m, $('span', { class: 'dim' }, `You are ${m.name}, founder ${m.index}${m.world ? ` of World ${m.world}` : ''}, member ${short(m.id)}. Your keys stay in this tab. Your follow (your copy of the World) checks each command before your key signs it.\nCommands: create · write OBJ SLOT TEXT · read OBJ [?] · grant OBJ MEMBER RIGHTS · invoke OBJ N ARGS · install TEXT · sync\n`));
}
function print(m, ...nodes) { const t = terms.get(m.name); if (!t) return; t.out.append(...nodes); t.out.scrollTop = t.out.scrollHeight; }

// one command at a time per member, as one terminal runs one `nd` at a time: a command typed while
// another is in flight (the hosted join's first sync) waits for it, never interleaves its frames
async function runIn(m, argv, why = '', opts = {}) {
  const prev = m.queue ?? Promise.resolve();
  let release; m.queue = new Promise((r) => { release = r; });
  await prev;
  try { return await runOne(m, argv, why, opts); } finally { release(); }
}
async function runOne(m, argv, why, { forge = false, quiet = false } = {}) {
  cmdNo++;
  const label = argv.map((a) => (a.length > 40 ? `${a.slice(0, 37)}…` : a)).join(' ');
  print(m, $('div', {}, $('b', { class: forge ? 'bad' : '' }, `${m.name}$ ${forge ? 'forge' : 'nd'} ${label}`), why ? $('span', { class: 'dim' }, `   (${why})`) : ''));
  const n0 = frames.length, t = performance.now();
  let r;
  forging = forge;
  const via = m.nd ?? nd;
  try { r = forge ? await via.forge(m, argv) : await via.run(m, argv); } catch (e) { r = { exit: 'client', stdout: '', stderr: `${e.message}\n` }; }
  forging = false;
  const ms = performance.now() - t;
  const cls = r.exit === 'ok' ? 'ok' : r.exit === 'declined' || r.exit === 'open' || r.exit === 'uncertain' ? 'warn' : 'bad';
  print(m, $('div', {}, ...linkify(r.stdout, m)), r.stderr ? $('div', { class: cls }, r.stderr) : '',
    $('div', { class: 'dim' }, `exit ${r.exit} · ${ms.toFixed(1)} ms · ${frames.length - n0} frames · ${meterOf(m)}`));
  for (const id of (r.stdout.match(/^id ([0-9a-f]{64})/gm) || []).map((l) => l.slice(3))) world.objects.set(id, argv[0]);
  const hm = r.stdout.match(/^height (\d+)/m); if (hm) world.height = +hm[1];
  document.getElementById('tray-height').textContent = `${frames.length} frames · ${cmdNo} commands`;
  if (r.exit !== 'ok' && !quiet) refusal(m, argv, r, frames.slice(n0));
  for (const o of wins.values()) if (o.refresh) o.refresh();
  tourCheck(m, argv, r);
  return r;
}

// the meter (KERNEL-68), read back from the member's OWN fold (tg_meter: World.ticksUsed), not asked of the writer
function meterOf(m) {
  const r = (m.K ?? K).meter(m.index);
  if (r[0] !== K.table.statuses.find((x) => x.name === 'ok').code) return '';
  const kv = Object.fromEntries(new TextDecoder().decode(r.slice(1)).trim().split('\n').map((l) => l.split(' ')));
  return `ticks ${(+kv.ticks).toLocaleString()} / ${(+kv.budget).toLocaleString()} this window`;
}

// ---------------------------------------------------------------- refusals are dialogs, by name
function refusal(m, argv, r, fs) {
  // follow's stderr: one line `EXIT NAME…` (the refusal by name) and any lines that explain it
  const lines = (r.stderr || '').trim().split('\n').filter(Boolean);
  const head = lines.find((l) => l.startsWith(r.exit + ' ')) ?? lines.at(-1) ?? r.exit;
  const rest = [...lines.filter((l) => l !== head), ...(r.stdout || '').trim().split('\n').filter(Boolean)];
  const sub = fs.filter((f) => f.to === 'writer' && (f.op === 'submit' || f.op === 'lookup')).at(-1);
  const writerSaid = sub ? `${sub.op} → ${sub.status}${sub.status === 'ok' ? '' : ' ' + new TextDecoder().decode(sub.payload)}` : 'nothing: your follow refused the call before signing, so nothing was sent';
  const body = $('div', {},
    $('div', { class: 'mark' + (r.exit === 'declined' ? ' warn' : '') }, r.exit === 'declined' ? '!' : '×'),
    $('div', {},
      $('div', { class: 'name' }, head),
      rest.map((l) => $('div', {}, l)),
      kv([['command', `${m.name}: nd ${argv[0]}`], ['exit', r.exit], ['writer\'s reply', writerSaid],
        lie !== 'honest' ? ['lie on', $('span', { class: 'bad' }, `${world.hosted ? 'relay' : 'writer'}: ${lieTitle(lie)}`, (() => { const l = fs.filter((f) => f.lied).at(-1); return l ? `; lying frame #${l.n} (${l.op})` : ''; })())] : null]),
      explain(head) ? $('p', {}, explain(head)) : ''),
    $('div', { class: 'actions' }, $('button', { class: 'btn', onclick: () => d.el.querySelector('.titlebar button').click() }, 'OK')));
  const d = openWindow({ id: `dlg-${cmdNo}`, title: r.exit === 'declined' ? 'Declined call' : 'Refusal', x: 260 + (cmdNo % 5) * 14, y: 180 + (cmdNo % 5) * 14, w: 460, body, dialog: true });
}
// What a refusal's NAME means, for a visitor; the name itself is the kernel's (law 7).
const glossary = {
  stale: 'stale: your call pinned a cell (named the state it expected), and the cell changed before the writer admitted the call. The writer does not apply a call signed over an older state. Run the command again; the follow plans it on the new state.',
  noGrant: 'noGrant: you do not own the object and named no grant (--via GRANT) that reaches its owner.',
  missingCell: 'missingCell: no cell with this id in your follow\'s World.',
  idTaken: 'idTaken: a package id is the hash of its bytes. These bytes are already installed.',
  lawDenied: 'lawDenied: a law of the object refused the change. A law compares the old state with the new state.',
  program: 'program: a check inside the method refused. The line above names the check.',
  eventMismatch: 'eventMismatch: an event on the log page does not match the Turn the writer admitted; one byte differs from what was signed. The follow refuses the page and keeps nothing from it.',
  chainMismatch: 'chainMismatch: replaying the page does not produce the chain hash the writer reports. An event is missing, or the writer logged something other than what it served.',
  cancelForged: 'cancelForged: the page has a cancel whose signature is not its member\'s.',
  forkedPost: 'forkedPost: a member posted a head for a step of this World whose chain hash differs from your follow\'s at that step. Two histories claim one World. The page is kept; the post is refused.',
  hostContradicted: 'hostContradicted: the writer reports one outcome for your call and your follow finds another. The attempt stays open. The writer\'s reply is shown and not acted on.',
  relationFull: 'relationFull: the relation (a table of rows inside the object) is at its row limit; here, the one slot is taken.',
  forkedWorld: 'forkedWorld: the signed head names a chain hash your follow does not have at that step of your writer\'s log. The two writers serve different histories of one genesis.',
  ticksBudget: 'ticksBudget: this member has spent its ticks for this window. Each Turn records its member and its ticks, and every follow recomputes both, so no writer can charge one member for another. The count restarts each window.',
};
function explain(name) { const w = name.split(' ').find((x) => glossary[x]); return w ? glossary[w] : ''; }

// ---------------------------------------------------------------- objects are windows
// The window is `read OBJ ?` (the object's own description, PROTOCOL-44) and `read OBJ`, as the
// viewing member's follow prints them; each line is laid out by its first word, never re-derived.
function prefill(m, text) {
  const w = wins.get(`term-${m.name}`); if (!w) return;
  focus(w); const input = w.el.querySelector('input'); input.value = text; input.focus();
}
function openObject(m, id) {
  const w = openWindow({ id: `obj-${id}`, title: `Object ${short(id)}`, w: 560, body: $('div', {}, 'reading…') });
  w.refresh = async () => {
    const d = await (m.nd ?? nd).run(m, ['read', id, '?']);
    const s = await (m.nd ?? nd).run(m, ['read', id]);
    const props = [], methods = [], laws = [], rels = [], calls = [];
    let core = null;
    for (const l of (d.exit === 'ok' ? d.stdout : '').trim().split('\n').filter(Boolean)) {
      const sp = l.indexOf(' '), k = sp < 0 ? l : l.slice(0, sp), v = sp < 0 ? '' : l.slice(sp + 1);
      if (k === 'core') core = v;
      else if (k === 'method') { const [i, label, ...ty] = v.split(' '); methods.push({ i, label, ty: ty.join(' ') }); }
      else if (k === 'call') calls.push(v);
      else if (k === 'law') laws.push(v);
      else if (k === 'rel') rels.push(v);
      else props.push([k, v]);
    }
    const row = (k, ...v) => $('tr', {}, $('td', {}, k), $('td', {}, ...v));
    const table = $('table', { class: 'props sunken' },
      props.map(([k, v]) => row(k, ...linkify(v, m))),
      core ? row('core', $('details', {}, $('summary', {}, `${core.length / 2} bytes (the package code invoke runs)`), $('code', { style: 'word-break:break-all' }, core))) : '',
      methods.map((x) => row(`method ${x.i}`, $('b', {}, x.label), ' ', $('code', {}, x.ty), ' ', $('a', { class: 'cmd', onclick: () => prefill(m, `invoke ${id} ${x.i} `) }, 'invoke…'))),
      calls.map((c) => row('call', c)), laws.map((c) => row('law', c)), rels.map((c) => row('rel', $('code', {}, c))));
    const state = $('table', { class: 'props sunken' }, (s.exit === 'ok' ? s.stdout : s.stderr).trim().split('\n').filter(Boolean).map((l) => {
      const e = l.indexOf('='); return e < 0 ? row('', ...linkify(l, m)) : row(l.slice(0, e), ...linkify(l.slice(e + 1), m));
    }));
    w.setBody($('div', {},
      kv([['source', `${m.name}'s follow: read ${short(id)} ?`], ['updated', 'after every command']]),
      d.exit === 'ok' ? table : $('div', { class: 'bad' }, d.stderr),
      $('h4', { style: 'margin:8px 0 4px' }, 'state'), state,
      methods.length ? '' : $('p', {}, $('a', { class: 'cmd', onclick: () => prefill(m, `write ${id} 0 `) }, 'write a slot…')),
      glossed([['owner', 'The member who may change the object without a grant.'], ['data', 'A cell with numbered slots and no code (create with no package).'],
        ['package', 'The id of the code the object runs.'], ['method N', 'An entry point: name and argument type. Call it with invoke OBJ N ARGS.'],
        ['call', 'A call a method may make to another object: method index, call index, type.'], ['law', 'A rule that judges every change: old state → new state.'],
        ['rel', 'A relation: a table of keyed rows inside the object, with a row limit.'], ['state', 'The current value, from read OBJ.']])));
  };
  w.refresh();
}

// ---------------------------------------------------------------- the wire, as a scrubbable timeline
let logSel = -1;
function openLog() {
  const w = openWindow({ id: 'log', title: 'Frames', x: 110, y: 560, w: 570, body: $('div', {}) });
  w.refresh = renderLog; renderLog();
}
function renderLog() {
  const w = wins.get('log'); if (!w) return;
  const scrub = $('input', { type: 'range', class: 'scrub', min: 0, max: Math.max(0, frames.length - 1), value: logSel < 0 ? frames.length - 1 : logSel, 'aria-label': 'frame' });
  const rows = frames.slice(-200).map((f) => $('div', { class: 'row' + (f.n === logSel ? ' sel' : ''), onclick: () => { logSel = f.n; renderLog(); } },
    $('span', {}, `#${f.n}`), $('span', {}, f.who), $('span', {}, `→${f.to}`), $('span', { class: 'x' }, f.op), $('span', { class: f.status === 'ok' ? 'ok' : 'bad' }, `${f.status} ${f.bytes}B`, f.lied ? $('b', { class: 'lied' }, ' LIED') : '', f.forged ? $('b', { class: 'lied' }, ' FORGED') : '')));
  const sel = frames[logSel < 0 ? frames.length - 1 : logSel];
  scrub.addEventListener('input', () => { logSel = +scrub.value; renderLog(); });
  w.setBody($('div', {}, scrub,
    sel ? kv([['frame', `#${sel.n} (command ${sel.cmd})`], ['from → to', `${sel.who} → ${sel.to}`], ['op', sel.op], ['bytes', sel.bytes], ['reply', sel.status],
      sel.lied ? ['lied', $('span', { class: 'bad' }, 'yes: the relay in front of the writer rewrote, answered or withheld this frame')] : null,
      sel.lie && sel.lie !== 'honest' ? ['lie on', sel.lie] : null]) : '',
    $('div', { class: 'log sunken', style: 'max-height:180px;overflow:auto' }, rows),
    glossed([['frame', 'One message: member → its follow, or member → writer.'], ['op', 'The request kind (command, resume, submit, lookup, log, …).'],
      ['reply', 'The status the receiver answered with.']])));
  const on = w.el.querySelector('.log .row.sel'); if (on) on.scrollIntoView({ block: 'nearest' });
  else { const l = w.el.querySelector('.log'); if (l) l.scrollTop = l.scrollHeight; }
}

// ---------------------------------------------------------------- the first five minutes
const tour = [
  { say: 'alice creates a cell: an object with numbered slots and no code. She owns it.', argv: () => ['create'], who: 0, done: (a) => a[0] === 'create' },
  { say: 'alice writes slot 0. Her copy of the World checks the write before her key signs it. If the check fails, nothing is signed.', argv: () => ['write', firstObj(), '0', 'hello from the testground'], who: 0, done: (a) => a[0] === 'write' },
  { say: 'alice reads the description of the cell. Click any id to open the object.', argv: () => ['read', firstObj(), '?'], who: 0, done: (a) => a[0] === 'read' },
  { say: 'alice grants bob the right to write the cell (mutate). The grant is a cell with its own id.', argv: () => ['grant', firstObj(), world.members[1].id, 'mutate'], who: 0, done: (a) => a[0] === 'grant' },
  { say: 'bob writes slot 0 through the grant. His call names the state of the cell it expects (a pin). alice writes slot 0 while his signed call is in transit, so the writer declines his call (stale).', argv: () => ['write', firstObj(), '0', 'bob says hi', '--via', firstGrant()], who: 1, race: true, done: (a, m) => m.name === 'bob' && a[0] === 'write' },
  { say: 'The writer lies: it changes one byte of every event it serves. bob\'s follow resets to genesis and replays the log. It checks each Turn and refuses the altered one (eventMismatch).', argv: () => ['sync'], who: 1, lie: 'flipEvent', done: (a, m) => m.name === 'bob' && a[0] === 'sync' && lie !== 'honest' },
  // one demo per axis (DESIGN-TESTGROUND §5): each is demos.js's argv, typed into the terminals
  { say: 'A generator: a package whose method installs another package. The generated package has the law n <= 100; setting n = 101 is refused (lawDenied).', demo: 'generator' },
  { say: 'The meter: each Turn records its member and its ticks (evaluator steps). bob repeats an expensive call until his ticks for the window run out (ticksBudget).', demo: 'meter' },
  { say: 'A time lock: a second World (A) runs in this tab. alice\'s lock releases only with a receipt showing that A admitted a call at or after the deadline height.', demo: 'timelock' },
];
let tourAt = 0;
const firstObj = () => [...world.objects.entries()].find(([, v]) => v === 'create')?.[0] ?? '';
const firstGrant = () => [...world.objects.entries()].find(([, v]) => v === 'grant')?.[0] ?? '';
function tourCheck(m, argv, r) { if (!world.hosted && tour[tourAt] && !tour[tourAt].demo && r.exit !== 'client' && tour[tourAt].done(argv, m)) { tourAt++; openTour(); } }
function openTour() {
  const items = tour.map((s, i) => $('li', { class: i < tourAt ? 'done' : '' }, s.say, i === tourAt ? $('div', {},
    $('code', {}, s.demo ? `Demos ▸ ${demos[s.demo].title}` : `${world.members[s.who].name}$ nd ${s.argv().map((a) => short(a)).join(' ')}`), ' ',
    $('button', { class: 'btn', onclick: async () => {
      if (s.demo) { if (lie !== 'honest') setLie('honest'); const r = await playDemo(s.demo); if (r.ok) { tourAt++; openTour(); } return; }
      const m = world.members[s.who];
      if (s.race) raceArmed = { member: m.name, other: world.members[0], argv: ['write', firstObj(), '0', 'alice was here first'] };
      if (s.lie) { const sc = lieScenes[s.lie]; await playLie(s.lie, { fresh: false, from: sc.steps.findIndex((x) => x.lie) }); return; }
      await runIn(m, s.argv());
    } }, 'Run')) : ''));
  openWindow({ id: 'tour', title: 'Tour', x: 110, y: 270, w: 570,
    body: $('div', { class: 'tour' }, $('p', {}, 'One World, two members (alice, bob), all in this tab. Type into their terminals, or press Run on each step.'), $('ol', {}, items),
      tourAt >= tour.length ? $('p', {}, 'More: the Writer menu in the World window turns on each lie the conformance rows test, and runs its scene. Or try: write as bob without --via; install a package twice; New World.') : '') });
}

// ---------------------------------------------------------------- demos: command sequences a member types
function openDemos() {
  const list = Object.entries(demos).map(([k, d]) => $('li', {}, $('b', {}, d.title), ' ',
    $('button', { class: 'btn', onclick: () => playDemo(k) }, 'Run'), $('div', { class: 'dim' }, `${d.steps.length} commands`)));
  openWindow({ id: 'demos', title: 'Demos', x: 140, y: 300, w: 520, body: $('div', { class: 'tour' }, $('ol', {}, list), $('p', { class: 'dim' }, 'Each demo types ordinary nd commands into the terminals, on the current World.')) });
}
// a second World in this tab (the time-lock's clock): its own kernel instance, its own writer, its
// founders' terminals; made once per World in the tab and kept until Re-genesis
async function secondWorld(name, names) {
  world.extra ??= {};
  if (world.extra[name]) return world.extra[name];
  const KW = await loadKernel(factory);
  const g = genesis(KW, name, names);
  const ndW = client(KW, { onFrame: (f) => { frames.push({ n: frames.length, cmd: cmdNo, lie: 'honest', ...f, who: `${f.who}@${name}` }); renderLog(); } });
  for (const m of g.members) { m.K = KW; m.nd = ndW; m.world = name; }
  world.extra[name] = { K: KW, members: g.members, origin: g.text.match(/^origin (\S+)/m)[1] };
  g.members.forEach((m, i) => openTerm(m, 640, 120 + i * 60));
  return world.extra[name];
}
async function playDemo(name) {
  const t = performance.now();
  const d = demos[name];
  const origin = { B: world.text.match(/^origin (\S+)/m)?.[1] };
  const members = [...world.members];
  for (const [w, names] of Object.entries(d.worlds ?? {})) { const x = await secondWorld(w, names); origin[w] = x.origin; members.push(...x.members); }
  const r = await runDemo(name, {
    fetchText: async (p) => (p.startsWith('kernel:') ? new TextDecoder().decode(K.text(p.slice(7)).slice(1)) : (await fetch(p)).text()),
    members, origin,
    run: async (m, argv, s) => {
      if (s.say) print(m, $('div', { class: 'warn' }, s.say));
      const out = await runIn(m, argv, s.again ? `repeat ${s.again}` : '');
      if (s.open) { const id = (out.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (id) openObject(m, id); }
      return out;
    },
  });
  print(world.members[0], $('div', { class: r.ok ? 'ok' : 'bad' }, `demo ${name}: ${r.ok ? 'every step as expected' : 'stopped'}, ${((performance.now() - t) / 1000).toFixed(1)} s`));
  return r;
}

// ---------------------------------------------------------------- desktop icons
const icons = document.getElementById('icons');
const icon = (glyph, label, act) => icons.append($('button', { class: 'icon', ondblclick: act, onkeydown: (e) => e.key === 'Enter' && act() }, $('span', { class: 'glyph' }, glyph), $('span', { class: 'label' }, label)));
icon('◆', 'World', () => openWorld());
icon('a', 'alice', () => openTerm(world.members[0]));
icon('b', 'bob', () => world.members[1] && openTerm(world.members[1]));
icon('≡', 'Frames', () => openLog());
icon('?', 'Start here', () => openTour());
icon('▶', 'Demos', () => openDemos());
document.getElementById('start').addEventListener('click', () => openWorld());
if (hostedDefault() && new URLSearchParams(location.search).has('join')) { newWorld(); joinHosted(hostedDefault()); } else newWorld();
window.testground = { K, runIn, playDemo, world: () => world, frames: () => frames, hex };
