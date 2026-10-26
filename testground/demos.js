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
