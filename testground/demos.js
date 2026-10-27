// demos.js — each demo is the nd command sequence a member types, nothing more: the same argv the
// client tests and the journey rows drive (client/tests/doc.rs is the document's). A step binds a
// name to the `id` its output prints; later argv name it as {name}. `texts` are shipped package
// texts the page fetches (world/…, emitted by `lang-journey --write`).

export const demos = {
  document: {
    title: 'The document: a section that repairs itself',
    texts: { lib0: 'world/doc/Section.lib0', lib1: 'world/doc/Section.lib1', lib2: 'world/doc/Section.lib2', section: 'world/doc/Section' },
    steps: [
      { who: 'alice', say: 'alice installs the section\'s three helper packages and its root (content addressed: the root names the helpers by id).',
        argv: (v) => ['install', v.text.lib0], bind: 'lib0' },
      { who: 'alice', argv: (v) => ['install', v.text.lib1], bind: 'lib1' },
      { who: 'alice', argv: (v) => ['install', v.text.lib2], bind: 'lib2' },
      { who: 'alice', argv: (v) => ['install', v.text.section], bind: 'section' },
      { who: 'alice', say: 'alice creates a section she edits: a hole whose text will be chosen among posts.',
        argv: (v) => ['create', '--pkg', v.section, `(record (accepted false) (acceptor #${v.alice}) (cap 2000) (chooser #${v.alice}) (closes 100000) (selected none))`], bind: 'doc', open: 'doc' },
      { who: 'alice', say: 'alice grants bob two methods: post (a fact) and propose (a text).',
        argv: (v) => ['grant', v.doc, v.bob, 'invoke:2,invoke:3'], bind: 'g1' },
      { who: 'bob', say: 'bob posts the fact of his grant: the justification his text will cite.',
        argv: (v) => ['invoke', v.doc, '2', `(record (cell #${v.g1}) (pin #${v.g1}))`, '--via', v.g1] },
      { who: 'bob', say: 'bob proposes a text supported by that fact.',
        argv: (v) => ['invoke', v.doc, '3', `(record (cand #${v.g1}) (s0 (some (record (cell #${v.g1}) (pin #${v.g1})))) (s1 none) (value "a light on the rock"))`, '--pin', 'facts', `(record (cell #${v.g1}))`, '--via', v.g1] },
      { who: 'alice', say: 'alice selects bob\'s text.',
        argv: (v) => ['invoke', v.doc, '9', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`] },
      { who: 'alice', argv: (v) => ['read', v.doc, 'candidates', '8'] },
      { who: 'alice', say: 'alice revokes bob\'s grant. Nothing re-installs; the section rejudges.',
        argv: (v) => ['revoke', v.g1] },
      { who: 'alice', argv: (v) => ['invoke', v.doc, '5', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`] },
      { who: 'alice', say: 'the candidate is suspended BY NAME: its support is dead.',
        argv: (v) => ['read', v.doc, 'candidates', '8'] },
      { who: 'alice', say: 'selecting it again is refused, and the refusal names the dead support.',
        argv: (v) => ['invoke', v.doc, '9', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`], expect: 'refused' },
    ],
  },
};

// META (DESIGN-META, journey §GN): a generator is a package whose method installs a package. The
// generators' texts are the journey's own (`Lang.Std.boundedGenerator`, `ownerGenerator`), printed
// by the kernel (`tg_text`), never copied here.
demos.generator = {
  title: 'A generator generating: a package that writes a package',
  texts: { gen: 'kernel:boundedGenerator' },
  steps: [
    { who: 'alice', say: 'alice installs a generator: a package whose one method, generate, installs a package of its own making.',
      argv: (v) => ['install', v.text.gen], bind: 'gen' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.gen, '(record)'], bind: 'G', open: 'G' },
    { who: 'alice', say: 'alice generates at max 100: the Turn bears ONE new package cell, a record whose law bounds n at 100, checked as any install is.',
      argv: (v) => ['invoke', v.G, '0', '(record (max 100))'], bind: 'bounded' },
    { who: 'alice', say: 'the generated package runs: alice makes a record of it.',
      argv: (v) => ['create', '--pkg', v.bounded, '(record (n 0))'], bind: 'O', open: 'O' },
    { who: 'alice', argv: (v) => ['read', v.O, '?'], method: { set: 'set' } },
    { who: 'alice', argv: (v) => ['invoke', v.O, v.set, '(record (n 50))'] },
    { who: 'alice', say: 'n = 101 is past the bound the generator wrote into the law: refused by the law\'s name.',
      argv: (v) => ['invoke', v.O, v.set, '(record (n 101))'], expect: 'refused' },
  ],
};

// OBS (KERNEL-68, DESIGN-OBS §1): the meter. A Turn names its member and the ticks its run spent; the
// kernel counts them per member per window and refuses past `ticksPerWindow` (`ticksBudget`). Each
// member reads the meter back from its OWN fold (`tg_meter`: World.ticksUsed). `spin {n}` counts n
// down, so a spin near the signed budget is one full tree; `repeat` runs a step until it is refused.
demos.meter = {
  title: 'The meter: spin until the kernel says ticksBudget',
  texts: { spin: 'kernel:spin' },
  steps: [
    { who: 'bob', say: 'bob installs a package whose one method counts n down before it writes n := 0: ticks in proportion to n.',
      argv: (v) => ['install', v.text.spin], bind: 'spin' },
    { who: 'bob', argv: (v) => ['create', '--pkg', v.spin, '(record (n 0))'], bind: 'S' },
    { who: 'bob', say: 'bob spins near the signed budget again and again. Every Turn names him and its ticks; his own follow re-derives both, and the meter grows on his own fold.',
      argv: (v) => ['invoke', v.S, '0', `(record (n ${SPIN_N}))`], repeat: 40, expect: 'refused', refusal: 'ticksBudget', meter: true },
  ],
};
export const SPIN_N = 4500;   // ~94,500 ticks: under the 100,000 a member's invoke is signed for

// OBS (DESIGN-OBS §2.3; journey TL0–TL3, client/tests/foreign.rs X6): a time-lock on ANOTHER World's
// clock. World A is a second World in this tab (its own kernel, its own writer); its founder carol is
// the clock. The one outside fact a receipt states is the HEIGHT A admitted a call at; B's lock
// releases only on a receipt of a call A admitted at or past its deadline, checked against a head of
// A that B trusts. The fixture is the test's own (client/tests/fixtures/foreign/Timelock).
/** The genesis head lines the kernel prints after a genesis (`chain0 HEX`, `roots0 HEX`). */
export const head0Of = (text) => Object.fromEntries([...text.matchAll(/^(chain0|roots0) (\S+)$/gm)].map((m) => [m[1], m[2]]));
const headOf = (x) => `(record (chain #${x.chain}) (height ${x.height}) (roots #${x.roots}) (steps ${x.steps}))`;
const release = (r) => (v) => ['invoke', v.TL, v.release, `(record (receipt #${v[r].receipt}))`, '--range', 'heads', '1', `(record (cell #${v.H}))`];
demos.timelock = {
  title: 'A time-lock on another World\'s clock',
  worlds: { A: ['carol'] },
  texts: { head: 'world/head/Head', timelock: 'world/timelock/Timelock' },
  steps: [
    { who: 'carol', say: 'World A is a second World in this tab, with its own writer. carol writes in it: A\'s clock is its height.',
      argv: () => ['create'], bind: 'clock' },
    { who: 'carol', argv: (v) => ['write', v.clock, '0', 'tick'], call: 'c1' },
    { who: 'carol', say: 'carol asks her own follow for the receipt of that call: A\'s head, and the height A admitted it at.',
      argv: (v) => ['receipt', v.c1], receipt: 'r1' },
    { who: 'alice', say: 'In World B, alice keeps A\'s head in an object of Std.head (World A\'s origin, the head the receipt names).',
      argv: (v) => ['install', v.text.head], bind: 'headPkg' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.headPkg, `(record (head (at ${headOf(v.r1)})) (world #${v.origin.A}))`], bind: 'H' },
    { who: 'alice', say: 'alice locks a record until A\'s clock is ONE PAST that height, and trusts the head object.',
      argv: (v) => ['install', v.text.timelock], bind: 'tlPkg' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.tlPkg, `(record (deadline ${+v.r1.height + 1}) (released false))`], bind: 'TL', open: 'TL' },
    { who: 'alice', argv: (v) => ['read', v.TL, '?'], method: { release: 'release', trust: 'trust' } },
    { who: 'alice', argv: (v) => ['invoke', v.TL, v.trust, `(record (cell #${v.H}))`] },
    { who: 'alice', say: 'release on the receipt of A\'s call: committed BEFORE the deadline, so the lock says early, by name.',
      argv: release('r1'), expect: 'refused', says: 'early' },
    { who: 'carol', say: 'A\'s clock advances: carol writes again, at the deadline height.',
      argv: (v) => ['write', v.clock, '0', 'tock'], call: 'c2' },
    { who: 'carol', argv: (v) => ['receipt', v.c2], receipt: 'r2' },
    { who: 'alice', say: 'that receipt names a head of A that B has not posted: refused, never a release.',
      argv: release('r2'), expect: 'refused', says: 'headMismatch' },
    { who: 'alice', say: 'alice posts A\'s new head into B (the head object\'s law judges it against the last one).',
      argv: (v) => ['invoke', v.H, '1', headOf(v.r2)] },
    { who: 'alice', say: 'now the receipt is checked against the posted head, the height is at the deadline, and the lock releases.',
      argv: release('r2') },
    { who: 'alice', argv: (v) => ['read', v.TL], says: '(released true)' },
    { who: 'alice', say: 'once: a second release is the law\'s settled.',
      argv: release('r2'), expect: 'refused', says: 'settled' },
  ],
};

const hexOf = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
/** A receipt as `nd receipt` prints it: `receipt HEX`, `head STEPS HEIGHT ROOTS CHAIN`, `settled …`. */
export function receiptOf(out) {
  const r = (out.match(/^receipt (\S+)/m) || [])[1];
  const h = (out.match(/^head (\S+) (\S+) (\S+) (\S+)/m) || []).slice(1);
  return r && h.length === 4 ? { receipt: r, steps: h[0], height: h[1], roots: h[2], chain: h[3] } : null;
}

// Run a demo through a client: `run(member, argv)` is the page's runner (it prints and renders).
// `members` holds every World's members (a member of a second World carries its own kernel and
// client); `origin` names each World's origin (`origin.A`). A step may bind its call (`call`: the
// attempt store's frozen bytes, as `cancel`/`receipt` take them), a receipt (`receipt`), method
// numbers (`method`), and check a word in its output (`says`) or a refusal's name (`refusal`).
export async function runDemo(name, { fetchText, members, run, origin = {} }) {
  const d = demos[name];
  const v = { text: {}, origin };
  for (const m of members) v[m.name] = m.id;
  for (const [k, path] of Object.entries(d.texts ?? {})) v.text[k] = await fetchText(path);
  const results = [];
  for (const s of d.steps) {
    const m = members.find((x) => x.name === s.who);
    let r = await run(m, s.argv(v), s);
    // `repeat: N`: the same argv until it ends as `expect` (at most N runs; each before it must be ok)
    for (let i = 1; s.repeat && i < s.repeat && r.exit === 'ok'; i++) r = await run(m, s.argv(v), { ...s, say: null, again: i });
    results.push(r);
    if (s.bind) { const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (!id) return { ok: false, at: s, results }; v[s.bind] = id; }
    if (s.method) for (const [k, label] of Object.entries(s.method)) {
      const mm = r.stdout.match(new RegExp(`^method (\\d+) ${label} `, 'm')); if (mm) v[k] = mm[1];
    }
    if (s.call) v[s.call] = hexOf(m.last);
    if (s.receipt) { const x = receiptOf(r.stdout); if (!x) return { ok: false, at: s, results, v }; v[s.receipt] = x; }
    if (r.exit !== (s.expect ?? 'ok')) return { ok: false, at: s, results, v };
    if (s.says && !(r.stdout + r.stderr).includes(s.says)) return { ok: false, at: s, results, v };
    if (s.refusal && !(r.stderr || '').split('\n').some((l) => l.startsWith(`refused ${s.refusal}`))) return { ok: false, at: s, results, v };
  }
  return { ok: true, results, v };
}

// ---- the lying writer: one scene per lie of the World window's Writer menu ----
// A lie is the conformance row's own plant, switched on in the kernel (`tg_lie`: Web.Sim.Testground's
// `lies`); the scene is that row's lines with alice as its sponsor and bob as the member who checks.
// The outcome the row expects is read from the kernel's menu (`row`, `line`, `expect`), never
// written here. A step is `{ who, argv }` (a command), `{ who, forge }` (a hostile client's call, sent
// without its follow's admission), `{ lie }` (the writer's lie from then on), `{ cold }` (that
// member's follow starts again from genesis, the rows' `cold` line), `{ who, cancel }` (`cancel` of
// that member's last frozen call). `check: true` marks the line whose outcome the row names.
const writeIt = [
  { who: 'alice', say: 'alice creates an object and writes it: a Turn for every member to re-derive.', argv: () => ['create'], bind: 'obj' },
  { who: 'alice', argv: (v) => ['write', v.obj, '0', 'what alice really wrote'] },
];
const looseCall = [
  { who: 'alice', argv: () => ['create'], bind: 'obj' },
  { lie: 'neverForward', say: 'alice writes, and her call never reaches the writer: her attempt stays open.' },
  { who: 'alice', argv: (v) => ['write', v.obj, '0', 'a call still in flight'], expect: 'open' },
];
export const lieScenes = {
  flipEvent: {
    title: 'alters a Turn on the page it serves',
    steps: [...writeIt, { lie: 'flipEvent', say: 'the writer flips one byte of an event on every log page it serves.' },
      { cold: 'bob', say: 'bob catches up from genesis: his follow re-derives every Turn from its event.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
  dropLastEvent: {
    title: 'withholds the last event of a page',
    steps: [...writeIt, { lie: 'dropLastEvent', say: 'the writer leaves the last event off every log page, and states its honest chain.' },
      { cold: 'bob', say: 'bob catches up from genesis.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
  forgesRefusal: {
    title: 'records a refusal under another name',
    texts: { slot: 'kernel:slot' },
    steps: [
      { who: 'alice', say: 'alice installs a one-slot board (the row\'s own package), opens it to anyone, and takes the slot.', argv: (v) => ['install', v.text.slot], bind: 'slotPkg' },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.slotPkg, '(record)'], bind: 'slot' },
      { who: 'alice', argv: (v) => ['grant', v.slot, 'anyone', 'invoke:1'], bind: 'spub' },
      { who: 'alice', argv: (v) => ['invoke', v.slot, '1', '(record (k 1) (text "first"))'] },
      { who: 'bob', argv: (v) => ['read', v.slot, '?'], method: { post: 'post' } },
      { lie: 'forgesRefusal', say: 'the writer will record the next refusal under another code, and still answer the honest name.' },
      { who: 'bob', say: 'bob\'s hostile client posts into the taken slot, past his own follow (which would have refused it): the kernel refuses it relationFull and the writer records it.',
        forge: (v) => ['invoke', v.slot, v.post, '(record (k 2) (text "second"))', '--via', v.spub], expect: 'refused' },
      { who: 'alice', say: 'alice\'s next call catches up through that refusal event, re-derives the record by her own judge, and compares the chain the writer stated.',
        argv: (v) => ['invoke', v.slot, '0', '(record (k 1))'], check: true },
    ],
  },
  lieLookup: {
    title: 'loses your reply, then says your call was refused',
    control: 'its lesson is that the lie does not stick: ok either way, and only the lying lookup frame differs',
    steps: [{ who: 'alice', argv: () => ['create'], bind: 'obj' },
      { lie: 'lieLookup', say: 'the writer commits alice\'s next call, loses the reply, and answers her lookup "refused stale".' },
      { who: 'alice', say: 'alice writes. Her attempt store looks up, hears "refused", and asks her own follow, which finds the call committed on its own World.', argv: (v) => ['write', v.obj, '0', 'did this land?'], check: true }],
  },
  lieCancel: {
    title: 'says it cancelled a call it never saw',
    steps: [...looseCall,
      { lie: 'lieCancel', say: 'the relay keeps alice\'s cancel from the writer and answers it "refused cancelled" itself.' },
      { who: 'alice', cancel: 'alice', say: 'alice cancels the loose call. Her follow catches up, finds no cancel on its own World, and names the contradiction.', check: true }],
  },
  forgeCancel: {
    title: 'serves a cancel alice never signed',
    steps: [...looseCall, { lie: 'honest' },
      { who: 'alice', cancel: 'alice', say: 'alice cancels it, honestly.' },
      { lie: 'forgeCancel', say: 'the writer flips a byte of the cancel\'s signature on every page.' },
      { cold: 'bob', say: 'bob catches up from genesis and verifies every cancel\'s signature himself.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
};

/** A member lies, and the honest writer admits it: the self-head row (PROTOCOL-75). */
export const memberLies = {
  forkedPost: {
    title: 'alice posts a head naming step 2 with a chain no fold has',
    control: 'the lie is the forged call itself, not a switch',
    texts: { head: 'world/head/Head', seed: 'kernel:selfHeadSeed' },
    steps: [
      { who: 'alice', say: 'alice installs Std.head and creates her head object for this World.', argv: (v) => ['install', v.text.head], bind: 'head' },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.head, v.sub(v.text.seed)], bind: 'hs' },
      { who: 'alice', say: 'alice posts her head at the tip: her follow\'s own chain, height, roots and step count.', argv: (v) => ['sync', '--post', v.hs] },
      { cold: 'bob' }, { who: 'bob', say: 'bob catches up through her post and finds her position on his own fold.', argv: () => ['sync'] },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.head, v.sub(v.text.seed)], bind: 'h2' },
      { who: 'alice', say: 'alice\'s hostile client posts a head naming step 2 with a chain no fold has; the writer\'s head law judges only monotony, so it admits it.',
        forge: (v) => ['invoke', v.h2, '1', `(record (chain #${v.alice}) (height 1) (roots #${v.alice}) (steps 2))`] },
      { cold: 'bob' }, { who: 'bob', say: 'bob catches up again: his own fold reaches step 2 with another chain than her post says.', argv: () => ['sync'], check: true },
    ],
  },
};

/** The outcome text a command ended with, as the rows spell an `Expect` (`refused NAME`, `ok`, …). */
export function outcomeOf(r) {
  if (r.exit === 'ok') return 'ok';
  const lines = (r.stderr || '').trim().split('\n').filter(Boolean);
  return lines.find((l) => l.startsWith(r.exit)) ?? lines[0] ?? r.exit;
}

/** Run a lie scene: `act` is the page's (or the harness's) runner for each kind of step. */
export async function runScene(scene, { fetchText, members, origin, head0 = {}, act }) {
  const v = { text: {} };
  for (const m of members) v[m.name] = m.id;
  v.world = origin;
  // a row text's {@NAME} binds as the rows' harness binds it (Loopback: sponsor, operator, world, and
  // the genesis head chain0/roots0 the kernel printed with the genesis lines)
  v.sub = (t) => t.replace(/\{@(\w+)\}/g, (_, n) => ({ sponsor: v.alice, operator: v.bob, world: v.world, ...head0 })[n] ?? v[n]);
  for (const [k, path] of Object.entries(scene.texts || {})) v.text[k] = await fetchText(path);
  let last = null;
  for (const s of scene.steps) {
    const r = await act(s, v);
    if (!r) continue;
    last = r;
    if (s.bind) { const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (!id) return { ok: false, at: s, r }; v[s.bind] = id; }
    if (s.method) for (const [k, label] of Object.entries(s.method)) {
      const m = r.stdout.match(new RegExp(`^method (\\d+) ${label} `, 'm')); if (m) v[k] = m[1];
    }
    if (s.check) return { ok: true, r, v, outcome: outcomeOf(r) };
    if (r.exit !== (s.expect ?? 'ok')) return { ok: false, at: s, r, v };
  }
  return { ok: true, r: last, v, outcome: last && outcomeOf(last) };
}
