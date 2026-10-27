// demos.js — each demo is the nd command sequence a member types, nothing more: the same argv the
// client tests and the journey rows drive (client/tests/doc.rs is the document's). A step binds a
// name to the `id` its output prints; later argv name it as {name}. `texts` are shipped package
// texts the page fetches (world/…, emitted by `lang-journey --write`).

export const demos = {
  document: {
    title: 'Document section with a hole',
    texts: { lib0: 'world/doc/Section.lib0', lib1: 'world/doc/Section.lib1', lib2: 'world/doc/Section.lib2', section: 'world/doc/Section' },
    steps: [
      { who: 'alice', say: 'alice installs three helper packages and the section package. A package id is the hash of its text. The section package names its helpers by id.',
        argv: (v) => ['install', v.text.lib0], bind: 'lib0' },
      { who: 'alice', argv: (v) => ['install', v.text.lib1], bind: 'lib1' },
      { who: 'alice', argv: (v) => ['install', v.text.lib2], bind: 'lib2' },
      { who: 'alice', argv: (v) => ['install', v.text.section], bind: 'section' },
      { who: 'alice', say: 'alice creates a section. Its text is a hole: a slot filled later by selecting one proposed text (a candidate).',
        argv: (v) => ['create', '--pkg', v.section, `(record (accepted false) (acceptor #${v.alice}) (cap 2000) (chooser #${v.alice}) (closes 100000) (selected none))`], bind: 'doc', open: 'doc' },
      { who: 'alice', say: 'alice grants bob two methods: 2 (post a fact) and 3 (propose a text).',
        argv: (v) => ['grant', v.doc, v.bob, 'invoke:2,invoke:3'], bind: 'g1' },
      { who: 'bob', say: 'bob posts a fact: his grant. His proposal cites it as support.',
        argv: (v) => ['invoke', v.doc, '2', `(record (cell #${v.g1}) (pin #${v.g1}))`, '--via', v.g1] },
      { who: 'bob', say: 'bob proposes the text "a light on the rock", supported by that fact.',
        argv: (v) => ['invoke', v.doc, '3', `(record (cand #${v.g1}) (s0 (some (record (cell #${v.g1}) (pin #${v.g1})))) (s1 none) (value "a light on the rock"))`, '--pin', 'facts', `(record (cell #${v.g1}))`, '--via', v.g1] },
      { who: 'alice', say: 'alice selects bob\'s text.',
        argv: (v) => ['invoke', v.doc, '9', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`] },
      { who: 'alice', argv: (v) => ['read', v.doc, 'candidates', '8'] },
      { who: 'alice', say: 'alice revokes bob\'s grant. The fact that supports his text is now dead. Method 5 re-checks the candidate.',
        argv: (v) => ['retire', v.g1] },
      { who: 'alice', argv: (v) => ['invoke', v.doc, '5', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`] },
      { who: 'alice', say: 'The candidate is suspended. Its row names the dead support.',
        argv: (v) => ['read', v.doc, 'candidates', '8'] },
      { who: 'alice', say: 'alice selects it again. Refused; the refusal names the dead support.',
        argv: (v) => ['invoke', v.doc, '9', `(record (cand #${v.g1}))`, '--pin', 'candidates', `(record (cand #${v.g1}))`, '--pin', 'facts', `(record (cell #${v.g1}))`], expect: 'refused' },
    ],
  },
};

// META (DESIGN-META, journey §GN): a generator is a package whose method installs a package. The
// generators' texts are the journey's own (`Lang.Std.boundedGenerator`, `ownerGenerator`), printed
// by the kernel (`tg_text`), never copied here.
demos.generator = {
  title: 'Generator: a package that installs a package',
  texts: { gen: 'kernel:boundedGenerator' },
  steps: [
    { who: 'alice', say: 'alice installs a generator. Its one method, generate, installs a new package.',
      argv: (v) => ['install', v.text.gen], bind: 'gen' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.gen, '(record)'], bind: 'G', open: 'G' },
    { who: 'alice', say: 'alice calls generate with max 100. The Turn installs one new package: a record with the law n <= 100. The kernel checks this install like any other.',
      argv: (v) => ['invoke', v.G, '0', '(record (max 100))'], bind: 'bounded' },
    { who: 'alice', say: 'alice creates an object of the generated package.',
      argv: (v) => ['create', '--pkg', v.bounded, '(record (n 0))'], bind: 'O', open: 'O' },
    { who: 'alice', argv: (v) => ['read', v.O, '?'], method: { set: 'set' } },
    { who: 'alice', argv: (v) => ['invoke', v.O, v.set, '(record (n 50))'] },
    { who: 'alice', say: 'alice sets n = 101. The law refuses it (lawDenied bounded).',
      argv: (v) => ['invoke', v.O, v.set, '(record (n 101))'], expect: 'refused' },
  ],
};

// OBS (KERNEL-68, DESIGN-OBS §1): the meter. A Turn names its member and the ticks its run spent; the
// kernel counts them per member per window and refuses past `ticksPerWindow` (`ticksBudget`). Each
// member reads the meter back from its OWN fold (`tg_meter`: World.ticksUsed). `spin {n}` counts n
// down, so a spin near the signed budget is one full tree; `repeat` runs a step until it is refused.
demos.meter = {
  title: 'Meter: ticks per member',
  texts: { spin: 'kernel:spin' },
  steps: [
    { who: 'bob', say: 'bob installs spin. Its method counts n down to 0, so a call costs ticks in proportion to n. A tick is one step of the evaluator.',
      argv: (v) => ['install', v.text.spin], bind: 'spin' },
    { who: 'bob', argv: (v) => ['create', '--pkg', v.spin, '(record (n 0))'], bind: 'S' },
    { who: 'bob', say: 'bob calls spin with n = 4500 (about 94,500 ticks) until he is refused. Each Turn records its member and its ticks. His follow recomputes both. A member may spend 2,097,152 ticks per window.',
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
  title: 'Time lock on another World\'s height',
  worlds: { A: ['carol'] },
  texts: { head: 'world/head/Head', timelock: 'world/timelock/Timelock' },
  steps: [
    { who: 'carol', say: 'World A is a second World in this tab, with its own writer. carol writes in A. The height of A is the clock.',
      argv: () => ['create'], bind: 'clock' },
    { who: 'carol', argv: (v) => ['write', v.clock, '0', 'tick'], call: 'c1' },
    { who: 'carol', say: 'carol gets the receipt of that call: the head of A, and the height at which A admitted the call.',
      argv: (v) => ['receipt', v.c1], receipt: 'r1' },
    { who: 'alice', say: 'In World B (this World), alice creates a head object (package Std.head). It holds the origin of World A and the head named in the receipt.',
      argv: (v) => ['install', v.text.head], bind: 'headPkg' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.headPkg, `(record (head (at ${headOf(v.r1)})) (world #${v.origin.A}))`], bind: 'H' },
    { who: 'alice', say: 'alice creates a lock with deadline = that height + 1. She names the head object as trusted.',
      argv: (v) => ['install', v.text.timelock], bind: 'tlPkg' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.tlPkg, `(record (deadline ${+v.r1.height + 1}) (released false))`], bind: 'TL', open: 'TL' },
    { who: 'alice', argv: (v) => ['read', v.TL, '?'], method: { release: 'release', trust: 'trust' } },
    { who: 'alice', argv: (v) => ['invoke', v.TL, v.trust, `(record (cell #${v.H}))`] },
    { who: 'alice', say: 'alice calls release with the receipt. A admitted the call before the deadline: refused (early).',
      argv: release('r1'), expect: 'refused', says: 'early' },
    { who: 'carol', say: 'carol writes again. The height of A reaches the deadline.',
      argv: (v) => ['write', v.clock, '0', 'tock'], call: 'c2' },
    { who: 'carol', argv: (v) => ['receipt', v.c2], receipt: 'r2' },
    { who: 'alice', say: 'The new receipt names a head of A that B has not recorded: refused (headMismatch).',
      argv: release('r2'), expect: 'refused', says: 'headMismatch' },
    { who: 'alice', say: 'alice records the new head of A in the head object. Its law checks the new head against the old one.',
      argv: (v) => ['invoke', v.H, '1', headOf(v.r2)] },
    { who: 'alice', say: 'alice calls release again. The receipt matches the recorded head and its height is the deadline: released.',
      argv: release('r2') },
    { who: 'alice', argv: (v) => ['read', v.TL], says: '(released true)' },
    { who: 'alice', say: 'A second release is refused (settled).',
      argv: release('r2'), expect: 'refused', says: 'settled' },
  ],
};

// AGENT (HOSTING-53, HOSTING-58; DESIGN-AGENT A1/A2): the Bell as an agent's inbox, filling a hole of
// the document. alice rings her Bell AIMED at a section; the answer is delivered to the section's
// `propose` in the same Turn, under the grant alice gave the Bell OBJECT, and the revoke withdraws
// it by name. In this tab the answerer is SCRIPTED: bob is the Bell's resident and types the answer
// the hosted resident would send (its argv: the ring's key and aim echoed, the section's fact row
// pinned with --pin OBJ/REL). The real model answers only hosted, opt-in (launcher/tests/agent_hole.rs).
const aimOf = (v) => `(some (record (cand #${v.gS}) (method 3) (target #${v.doc}) (via #${v.gS})))`;
demos.inbox = {
  title: 'An inbox for an agent: a question answered into a document (scripted answerer)',
  texts: { bell: 'world/resident/Bell', lib0: 'world/doc/Section.lib0', lib1: 'world/doc/Section.lib1', lib2: 'world/doc/Section.lib2', section: 'world/doc/Section' },
  steps: [
    { who: 'alice', say: 'alice installs the Bell (a queue of questions, rings) and creates one. Its answerer (resident) is bob. Here bob types the answers (a scripted answerer).',
      argv: (v) => ['install', v.text.bell], bind: 'bellPkg' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.bellPkg, `(record (open true) (resident #${v.bob}))`], bind: 'bell', open: 'bell' },
    { who: 'alice', argv: (v) => ['grant', v.bell, v.bob, 'observe,invoke:0'], bind: 'gA' },
    { who: 'alice', say: 'alice installs the section package and creates a section. She chooses its text.',
      argv: (v) => ['install', v.text.lib0] },
    { who: 'alice', argv: (v) => ['install', v.text.lib1] },
    { who: 'alice', argv: (v) => ['install', v.text.lib2] },
    { who: 'alice', argv: (v) => ['install', v.text.section], bind: 'section' },
    { who: 'alice', argv: (v) => ['create', '--pkg', v.section, `(record (accepted false) (acceptor #${v.alice}) (cap 2000) (chooser #${v.alice}) (closes 100000) (selected none))`], bind: 'doc', open: 'doc' },
    { who: 'alice', say: 'alice grants the Bell object, not bob, the right to propose a text (invoke:3). She posts that grant as a fact. The answer cites the fact as its support.',
      argv: (v) => ['grant', v.doc, v.bell, 'invoke:3'], bind: 'gS' },
    { who: 'alice', argv: (v) => ['invoke', v.doc, '2', `(record (cell #${v.gS}) (pin #${v.gS}))`] },
    { who: 'alice', say: 'alice rings the Bell. The ring names the section as the place for the answer (an aim).',
      argv: (v) => ['invoke', v.bell, '4', `(record (text "what should the first section say?") (to ${aimOf(v)}))`] },
    { who: 'bob', say: 'bob reads the pending ring: its key and its aim.',
      argv: (v) => ['read', v.bell, 'pending', '64'], grab: { nb: /\(notBefore (\d+)\)/ }, says: `(target #` },
    { who: 'bob', say: 'bob answers with the argv a hosted resident sends. The answer repeats the aim; the Bell refuses an answer without it (rung: text). --pin names the section\'s fact row (SECTION/facts) the support reads. One Turn answers the ring and adds the candidate.',
      argv: (v) => ['invoke', v.bell, '0', `(record (notBefore ${v.nb}) (ringText "what should the first section say?") (ringer #${v.alice}) (text "a lamp on the stair") (to ${aimOf(v)}))`,
        '--pin', `${v.doc}/facts`, `(record (cell #${v.gS}))`, '--via', v.gA] },
    { who: 'alice', say: 'The section holds the answer as a candidate. Its author (by) is bob, the signer. Its status is verified.',
      argv: (v) => ['read', v.doc, 'candidates', '8'], says: 'verified' },
    { who: 'alice', say: 'alice revokes the Bell\'s grant on the section and judges the candidate again (rejudge). It is suspended (support0 dead).',
      argv: (v) => ['retire', v.gS] },
    { who: 'alice', argv: (v) => ['invoke', v.doc, '5', `(record (cand #${v.gS}))`, '--pin', 'candidates', `(record (cand #${v.gS}))`, '--pin', 'facts', `(record (cell #${v.gS}))`] },
    { who: 'alice', argv: (v) => ['read', v.doc, 'candidates', '8'], says: 'support0 dead' },
    { who: 'alice', say: 'alice tries to choose the answer as the section\'s text. It is refused (support0 dead).',
      argv: (v) => ['invoke', v.doc, '9', `(record (cand #${v.gS}))`, '--pin', 'candidates', `(record (cand #${v.gS}))`, '--pin', 'facts', `(record (cell #${v.gS}))`], expect: 'refused', says: 'support0 dead' },
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
// numbers (`method`), a pattern's group (`grab`), and check a word in its output (`says`) or a refusal's name (`refusal`).
export async function runDemo(name, { fetchText, members, run, origin = {}, idOfText = null }) {
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
    // a package this World already holds (`refused idTaken`): the demo reuses it, by the id it was
    // installed under in this tab
    if (r.exit === 'refused' && /idTaken/.test(r.stderr) && idOfText && s.argv(v)[0] === 'install') {
      const id = idOfText(s.argv(v)[1]);
      if (id) r = { ...r, exit: 'ok', stdout: `id ${id}\n` };
    }
    results.push(r);
    if (s.bind) { const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (!id) return { ok: false, at: s, results }; v[s.bind] = id; }
    if (s.method) for (const [k, label] of Object.entries(s.method)) {
      const mm = r.stdout.match(new RegExp(`^method (\\d+) ${label} `, 'm')); if (mm) v[k] = mm[1];
    }
    // `grab`: names bound to the first group of a pattern in the output (the ring's notBefore)
    if (s.grab) for (const [k, re] of Object.entries(s.grab)) { const g = (r.stdout.match(re) || [])[1]; if (!g) return { ok: false, at: s, results, v }; v[k] = g; }
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
  { who: 'alice', say: 'alice creates a cell and writes slot 0.', argv: () => ['create'], bind: 'obj' },
  { who: 'alice', argv: (v) => ['write', v.obj, '0', 'what alice really wrote'] },
];
const looseCall = [
  { who: 'alice', argv: () => ['create'], bind: 'obj' },
  { lie: 'neverForward', say: 'alice writes. Her call never reaches the writer, so her attempt stays open.' },
  { who: 'alice', argv: (v) => ['write', v.obj, '0', 'a call still in flight'], expect: 'open' },
];
export const lieScenes = {
  flipEvent: {
    title: 'alters an event in the log',
    steps: [...writeIt, { lie: 'flipEvent', say: 'The writer changes one byte of an event on every log page it serves.' },
      { cold: 'bob', say: 'bob\'s follow resets to genesis and re-checks every event.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
  dropLastEvent: {
    title: 'drops the last event of each log page',
    steps: [...writeIt, { lie: 'dropLastEvent', say: 'The writer omits the last event of each log page and reports the true chain hash.' },
      { cold: 'bob', say: 'bob\'s follow resets to genesis.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
  forgesRefusal: {
    title: 'logs a refusal under a different name',
    texts: { slot: 'kernel:slot' },
    steps: [
      { who: 'alice', say: 'alice installs a one-slot board, grants post to anyone, and takes the slot.', argv: (v) => ['install', v.text.slot], bind: 'slotPkg' },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.slotPkg, '(record)'], bind: 'slot' },
      { who: 'alice', argv: (v) => ['grant', v.slot, 'anyone', 'invoke:1'], bind: 'spub' },
      { who: 'alice', argv: (v) => ['invoke', v.slot, '1', '(record (k 1) (text "first"))'] },
      { who: 'bob', argv: (v) => ['read', v.slot, '?'], method: { post: 'post' } },
      { lie: 'forgesRefusal', say: 'The writer will log the next refusal under a different code and reply with the true name.' },
      { who: 'bob', say: 'bob\'s hostile client posts to the taken slot without his follow\'s check. The kernel refuses it (relationFull). The writer logs the refusal under the wrong code.',
        forge: (v) => ['invoke', v.slot, v.post, '(record (k 2) (text "second"))', '--via', v.spub], expect: 'refused' },
      { who: 'alice', say: 'alice\'s next call replays the refusal event, recomputes it, and compares the chain hash with the writer\'s.',
        argv: (v) => ['invoke', v.slot, '0', '(record (k 1))'], check: true },
    ],
  },
  lieLookup: {
    title: 'loses the reply, then reports the call refused',
    control: 'its lesson is that the lie does not stick: ok either way, and only the lying lookup frame differs',
    steps: [{ who: 'alice', argv: () => ['create'], bind: 'obj' },
      { lie: 'lieLookup', say: 'The writer will commit alice\'s next call, drop the reply, and answer her lookup with "refused stale".' },
      { who: 'alice', say: 'alice writes. Her client asks the writer about the call and hears "refused". Her follow finds the call committed.', argv: (v) => ['write', v.obj, '0', 'did this land?'], check: true }],
  },
  lieCancel: {
    title: 'reports a cancel it never received',
    steps: [...looseCall,
      { lie: 'lieCancel', say: 'The relay will withhold alice\'s cancel from the writer and answer "refused cancelled" itself.' },
      { who: 'alice', cancel: 'alice', say: 'alice cancels the open call. Her follow finds no cancel in the log and reports the contradiction (hostContradicted).', check: true }],
  },
  forgeCancel: {
    title: 'serves a cancel alice did not sign',
    steps: [...looseCall, { lie: 'honest' },
      { who: 'alice', cancel: 'alice', say: 'alice cancels the open call.' },
      { lie: 'forgeCancel', say: 'The writer changes one byte of the cancel signature on every page.' },
      { cold: 'bob', say: 'bob\'s follow resets to genesis and checks every cancel signature.' },
      { who: 'bob', argv: () => ['sync'], check: true }],
  },
};

/** A member lies, and the honest writer admits it: the self-head row (PROTOCOL-75). */
export const memberLies = {
  forkedPost: {
    title: 'alice posts a false head for step 2',
    control: 'the lie is the forged call itself, not a switch',
    texts: { head: 'world/head/Head', seed: 'kernel:selfHeadSeed' },
    steps: [
      { who: 'alice', say: 'alice installs Std.head and creates a head object for this World.', argv: (v) => ['install', v.text.head], bind: 'head' },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.head, v.sub(v.text.seed)], bind: 'hs' },
      { who: 'alice', say: 'alice posts her current head: chain hash, height, state roots, step count.', argv: (v) => ['sync', '--post', v.hs] },
      { cold: 'bob' }, { who: 'bob', say: 'bob\'s follow replays the log, including her post, and finds the same head.', argv: () => ['sync'] },
      { who: 'alice', argv: (v) => ['create', '--pkg', v.head, v.sub(v.text.seed)], bind: 'h2' },
      { who: 'alice', say: 'alice\'s hostile client posts a head for step 2 with a false chain hash. The head law checks only that heads increase, so the writer admits it.',
        forge: (v) => ['invoke', v.h2, '1', `(record (chain #${v.alice}) (height 1) (roots #${v.alice}) (steps 2))`] },
      { cold: 'bob' }, { who: 'bob', say: 'bob\'s follow replays again. At step 2 his chain hash differs from the one in her post.', argv: () => ['sync'], check: true },
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
