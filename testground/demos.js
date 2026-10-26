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

// Run a demo through a client: `run(member, argv)` is the page's runner (it prints and renders).
export async function runDemo(name, { fetchText, members, run }) {
  const d = demos[name];
  const v = { text: {} };
  for (const m of members) v[m.name] = m.id;
  for (const [k, path] of Object.entries(d.texts)) v.text[k] = await fetchText(path);
  const results = [];
  for (const s of d.steps) {
    const m = members.find((x) => x.name === s.who);
    const r = await run(m, s.argv(v), s);
    results.push(r);
    if (s.bind) { const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1]; if (!id) return { ok: false, at: s, results }; v[s.bind] = id; }
    if (r.exit !== (s.expect ?? 'ok')) return { ok: false, at: s, results, v };
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
export async function runScene(scene, { fetchText, members, origin, act }) {
  const v = { text: {} };
  for (const m of members) v[m.name] = m.id;
  v.world = origin;
  v.sub = (t) => t.replace(/\{@(\w+)\}/g, (_, n) => ({ sponsor: v.alice, operator: v.bob, world: v.world })[n] ?? v[n]);
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
