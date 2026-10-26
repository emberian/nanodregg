// testground.js — the desktop. Pixels only: windows, a taskbar, a terminal per member, dialogs.
// Every word a window shows is printed by the member's own follow (Lean) or is a name from the
// kernel's table; this file lays it out and never decides what it means.
import factory from './kernel.mjs';
import { loadKernel, client, genesis, hex } from './nd.js';
import { demos, runDemo } from './demos.js';

const $ = (tag, attrs = {}, ...kids) => {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') e.className = v; else if (k.startsWith('on')) e.addEventListener(k.slice(2), v); else e.setAttribute(k, v);
  }
  for (const k of kids.flat()) e.append(k instanceof Node ? k : document.createTextNode(String(k)));
  return e;
};
const short = (h) => (h && h.length > 12 ? `${h.slice(0, 8)}…` : h);

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
let K, nd, world, frames = [], cmdNo = 0, raceArmed = null;
const t0 = performance.now();
K = await loadKernel(factory);
const loadMs = performance.now() - t0;
document.getElementById('boot').remove();

function newWorld() {
  frames = []; cmdNo = 0;
  for (const o of [...wins.values()]) { o.el.remove(); o.task.remove(); wins.delete(o.id); }
  const t = performance.now();
  world = genesis(K, 'testground', ['alice', 'bob']);
  world.ms = performance.now() - t;
  world.height = 0; world.objects = new Map();
  nd = client(K, {
    onFrame: (f) => { frames.push({ n: frames.length, cmd: cmdNo, ...f }); renderLog(); },
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
  const lines = world.text.trim().split('\n');
  const rows = lines.map((l) => { const w = l.split(' '); return $('tr', {}, $('td', {}, w[0] === 'founder' ? `founder ${w[1]}` : w[0]), $('td', {}, w[0] === 'founder' ? `${world.members[+w[1]].name}: member ${w[3]}  grant ${w[5]}` : w.slice(1).join(' '))); });
  const body = $('div', {},
    $('table', { class: 'props sunken' }, rows),
    $('p', { class: 'dim' }, `kernel loaded in ${loadMs.toFixed(0)} ms; genesis in ${world.ms.toFixed(0)} ms, in this tab. One writer, one follow per member, all Lean compiled to WebAssembly; this page moves bytes.`),
    $('button', { class: 'btn', onclick: () => newWorld() }, 'Re-genesis (a new World)'));
  openWindow({ id: 'world', title: 'World — testground', x: 110, y: 16, w: 570, body });
}

// ---------------------------------------------------------------- a member's terminal
function linkify(text, m) {
  // every 64-hex id becomes a link that opens the object as a window; a line `tx …` names a
  // transaction, which is not a cell, so it stays text
  return text.split(/(\n)/).flatMap((line) => {
    if (line.startsWith('tx ')) return [line];
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
  openWindow({ id: `term-${m.name}`, title: `${m.name}@testground — nd`, x, y, w: 520, body });
  print(m, $('span', { class: 'dim' }, `you are ${m.name}, founder ${m.index}: member ${short(m.id)}. Your keys are in this tab; your follow re-derives every step before it signs.\n`));
}
function print(m, ...nodes) { const t = terms.get(m.name); if (!t) return; t.out.append(...nodes); t.out.scrollTop = t.out.scrollHeight; }

async function runIn(m, argv, why = '') {
  cmdNo++;
  const label = argv.map((a) => (a.length > 40 ? `${a.slice(0, 37)}…` : a)).join(' ');
  print(m, $('div', {}, $('b', {}, `${m.name}$ nd ${label}`), why ? $('span', { class: 'dim' }, `   (${why})`) : ''));
  const n0 = frames.length, t = performance.now();
  let r;
  try { r = await nd.run(m, argv); } catch (e) { r = { exit: 'client', stdout: '', stderr: `${e.message}\n` }; }
  const ms = performance.now() - t;
  const cls = r.exit === 'ok' ? 'ok' : r.exit === 'declined' || r.exit === 'open' || r.exit === 'uncertain' ? 'warn' : 'bad';
  print(m, $('div', {}, ...linkify(r.stdout, m)), r.stderr ? $('div', { class: cls }, r.stderr) : '',
    $('div', { class: 'dim' }, `exit ${r.exit} · ${ms.toFixed(1)} ms · ${frames.length - n0} frames`));
  for (const id of (r.stdout.match(/^id ([0-9a-f]{64})/gm) || []).map((l) => l.slice(3))) world.objects.set(id, argv[0]);
  const hm = r.stdout.match(/^height (\d+)/m); if (hm) world.height = +hm[1];
  document.getElementById('tray-height').textContent = `${frames.length} frames · ${cmdNo} commands`;
  if (r.exit !== 'ok') refusal(m, argv, r, frames.slice(n0));
  for (const o of wins.values()) if (o.refresh) o.refresh();
  tourCheck(m, argv, r);
  return r;
}

// ---------------------------------------------------------------- refusals are dialogs, by name
function refusal(m, argv, r, fs) {
  // follow's stderr: one line `EXIT NAME…` (the refusal by name) and any lines that explain it
  const lines = (r.stderr || '').trim().split('\n').filter(Boolean);
  const head = lines.find((l) => l.startsWith(r.exit + ' ')) ?? lines.at(-1) ?? r.exit;
  const rest = [...lines.filter((l) => l !== head), ...(r.stdout || '').trim().split('\n').filter(Boolean)];
  const sub = fs.filter((f) => f.to === 'writer' && (f.op === 'submit' || f.op === 'lookup')).at(-1);
  const writerSaid = sub ? `${sub.op} → ${sub.status}${sub.status === 'ok' ? '' : ' ' + new TextDecoder().decode(sub.payload)}` : 'nothing — your own follow re-derived the call on its own World, refused it, and never asked custody to sign';
  const body = $('div', {},
    $('div', { class: 'mark' + (r.exit === 'declined' ? ' warn' : '') }, r.exit === 'declined' ? '!' : '×'),
    $('div', {},
      $('div', { class: 'name' }, head),
      rest.map((l) => $('div', {}, l)),
      $('div', { class: 'dim' }, `${m.name}'s nd ${argv[0]} ended ${r.exit}. The writer said: ${writerSaid}.`),
      $('div', {}, explain(head))),
    $('div', { class: 'actions' }, $('button', { class: 'btn', onclick: () => d.el.querySelector('.titlebar button').click() }, 'OK')));
  const d = openWindow({ id: `dlg-${cmdNo}`, title: r.exit === 'declined' ? 'Declined' : 'Refused', x: 260 + (cmdNo % 5) * 14, y: 180 + (cmdNo % 5) * 14, w: 460, body, dialog: true });
}
// What a refusal's NAME means, for a visitor; the name itself is the kernel's (law 7).
const glossary = {
  stale: 'A cell your call pinned changed before your call was admitted: the writer would not apply it to a World you did not sign over. Run it again; your follow re-plans on the new World.',
  noGrant: 'You are not the owner and named no grant (`--via GRANT`) that reaches the owner.',
  missingCell: 'No such cell in your follow\'s World.',
  idTaken: 'Packages are content addressed: these exact bytes are installed already.',
  lawDenied: 'A law of the object refused the act.',
  program: 'The object\'s own method refused; the line above says which check, by name.',
};
function explain(name) { const w = name.split(' ').at(-1); return glossary[w] ?? ''; }

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
    const d = await nd.run(m, ['read', id, '?']);
    const s = await nd.run(m, ['read', id]);
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
      core ? row('core', $('details', {}, $('summary', {}, `${core.length / 2} bytes: the package cell, the bytes invoke will run`), $('code', { style: 'word-break:break-all' }, core))) : '',
      methods.map((x) => row(`method ${x.i}`, $('b', {}, x.label), ' ', $('code', {}, x.ty), ' ', $('a', { class: 'cmd', onclick: () => prefill(m, `invoke ${id} ${x.i} `) }, 'invoke…'))),
      calls.map((c) => row('call', c)), laws.map((c) => row('law', c)), rels.map((c) => row('rel', $('code', {}, c))));
    const state = $('table', { class: 'props sunken' }, (s.exit === 'ok' ? s.stdout : s.stderr).trim().split('\n').filter(Boolean).map((l) => {
      const e = l.indexOf('='); return e < 0 ? row('', ...linkify(l, m)) : row(l.slice(0, e), ...linkify(l.slice(e + 1), m));
    }));
    w.setBody($('div', {},
      $('div', { class: 'dim' }, `as ${m.name}'s follow describes it (read ${short(id)} ?), re-read after every command`),
      d.exit === 'ok' ? table : $('div', { class: 'bad' }, d.stderr),
      $('h4', { style: 'margin:8px 0 4px' }, 'state'), state,
      methods.length ? '' : $('p', {}, $('a', { class: 'cmd', onclick: () => prefill(m, `write ${id} 0 `) }, 'write a slot…'))));
  };
  w.refresh();
}

// ---------------------------------------------------------------- the wire, as a scrubbable timeline
let logSel = -1;
function openLog() {
  const w = openWindow({ id: 'log', title: 'Wire — every frame', x: 110, y: 560, w: 570, body: $('div', {}) });
  w.refresh = renderLog; renderLog();
}
function renderLog() {
  const w = wins.get('log'); if (!w) return;
  const scrub = $('input', { type: 'range', class: 'scrub', min: 0, max: Math.max(0, frames.length - 1), value: logSel < 0 ? frames.length - 1 : logSel, 'aria-label': 'scrub the wire' });
  const rows = frames.slice(-200).map((f) => $('div', { class: 'row' + (f.n === logSel ? ' sel' : ''), onclick: () => { logSel = f.n; renderLog(); } },
    $('span', {}, `#${f.n}`), $('span', {}, f.who), $('span', {}, `→${f.to}`), $('span', { class: 'x' }, f.op), $('span', { class: f.status === 'ok' ? 'ok' : 'bad' }, `${f.status} ${f.bytes}B`)));
  const sel = frames[logSel < 0 ? frames.length - 1 : logSel];
  scrub.addEventListener('input', () => { logSel = +scrub.value; renderLog(); });
  w.setBody($('div', {}, scrub,
    sel ? $('div', { class: 'dim' }, `frame #${sel.n}, command ${sel.cmd}: ${sel.who} → ${sel.to} ${sel.op}, ${sel.bytes} bytes, answered ${sel.status}`) : '',
    $('div', { class: 'log sunken', style: 'max-height:180px;overflow:auto' }, rows)));
}

// ---------------------------------------------------------------- the first five minutes
const tour = [
  { say: 'alice creates a data object she owns.', argv: () => ['create'], who: 0, done: (a) => a[0] === 'create' },
  { say: 'alice writes slot 0. Her follow pins the cell, re-derives the Turn on its own World, and only then asks custody to sign.', argv: () => ['write', firstObj(), '0', 'hello from the testground'], who: 0, done: (a) => a[0] === 'write' },
  { say: 'alice asks the object to describe itself; click its id anywhere to open it as a window.', argv: () => ['read', firstObj(), '?'], who: 0, done: (a) => a[0] === 'read' },
  { say: 'alice grants bob mutate on it.', argv: () => ['grant', firstObj(), world.members[1].id, 'mutate'], who: 0, done: (a) => a[0] === 'grant' },
  { say: 'bob writes through that grant, but alice writes the same slot while bob\'s signed call is on its way. Watch the dialog: the kernel names why.', argv: () => ['write', firstObj(), '0', 'bob says hi', '--via', firstGrant()], who: 1, race: true, done: (a, m) => m.name === 'bob' && a[0] === 'write' },
];
let tourAt = 0;
const firstObj = () => [...world.objects.entries()].find(([, v]) => v === 'create')?.[0] ?? '';
const firstGrant = () => [...world.objects.entries()].find(([, v]) => v === 'grant')?.[0] ?? '';
function tourCheck(m, argv, r) { if (tour[tourAt] && r.exit !== 'client' && tour[tourAt].done(argv, m)) { tourAt++; openTour(); } }
function openTour() {
  const items = tour.map((s, i) => $('li', { class: i < tourAt ? 'done' : '' }, s.say, i === tourAt ? $('div', {},
    $('code', {}, `${world.members[s.who].name}$ nd ${s.argv().map((a) => short(a)).join(' ')}`), ' ',
    $('button', { class: 'btn', onclick: async () => {
      const m = world.members[s.who];
      if (s.race) raceArmed = { member: m.name, other: world.members[0], argv: ['write', firstObj(), '0', 'alice was here first'] };
      await runIn(m, s.argv());
    } }, 'Run')) : ''));
  openWindow({ id: 'tour', title: 'Start here', x: 110, y: 270, w: 570,
    body: $('div', { class: 'tour' }, $('p', {}, 'This is a World with two members, alice and bob, running entirely in this tab. Type into their terminals, or follow these steps.'), $('ol', {}, items),
      tourAt >= tour.length ? $('p', {}, 'Now break something: write as bob without --via, install a package twice, or press Re-genesis.') : '') });
}

// ---------------------------------------------------------------- demos: command sequences a member types
function openDemos() {
  const list = Object.entries(demos).map(([k, d]) => $('li', {}, $('b', {}, d.title), ' ',
    $('button', { class: 'btn', onclick: () => playDemo(k) }, 'Run'), $('div', { class: 'dim' }, `${d.steps.length} nd commands, typed into alice's and bob's terminals as they run`)));
  openWindow({ id: 'demos', title: 'Demos', x: 140, y: 300, w: 520, body: $('div', { class: 'tour' }, $('ol', {}, list), $('p', { class: 'dim' }, 'Every demo is the same argv a member would type; each runs on this World, so run it after the tour or on a fresh World.')) });
}
async function playDemo(name) {
  const t = performance.now();
  const r = await runDemo(name, {
    fetchText: async (p) => (await fetch(p)).text(),
    members: world.members,
    run: async (m, argv, s) => {
      if (s.say) print(m, $('div', { class: 'warn' }, `— ${s.say}`));
      const out = await runIn(m, argv);
      if (s.open) { const id = (out.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (id) openObject(m, id); }
      return out;
    },
  });
  print(world.members[0], $('div', { class: r.ok ? 'ok' : 'bad' }, `demo ${name}: ${r.ok ? 'every step answered as scripted' : 'stopped'} in ${((performance.now() - t) / 1000).toFixed(1)} s`));
}

// ---------------------------------------------------------------- desktop icons
const icons = document.getElementById('icons');
const icon = (glyph, label, act) => icons.append($('button', { class: 'icon', ondblclick: act, onkeydown: (e) => e.key === 'Enter' && act() }, $('span', { class: 'glyph' }, glyph), $('span', { class: 'label' }, label)));
icon('◆', 'World', () => openWorld());
icon('a', 'alice', () => openTerm(world.members[0]));
icon('b', 'bob', () => openTerm(world.members[1]));
icon('≡', 'Wire', () => openLog());
icon('?', 'Start here', () => openTour());
icon('▶', 'Demos', () => openDemos());
document.getElementById('start').addEventListener('click', () => openWorld());
newWorld();
window.testground = { K, runIn, world: () => world, frames: () => frames, hex };
