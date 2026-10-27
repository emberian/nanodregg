// teach.js — the windows that teach the language: the object inspector, the package editor, the term
// REPL with its grammar, the Turn view and the tutorial (CLIENT-50). Every answer is the kernel's
// (Web.Sim.Teach: tg_ob, tg_grammar, tg_source, tg_grants, tg_turn; or a member's nd command); this
// file lays answers out and never decides what they mean. Words follow testground/STYLE.md.

const dec = new TextDecoder();
const OK = 0;
// a core package text (`(package (imports …) …)`) is what install takes as it is; a surface text is
// lowered first (`(core P)`)
export const isCore = (t) => /^\s*(;[^\n]*\n\s*)*\(package\s*\(imports/.test(t);

// a balanced s-expression starting at `i` (display only: the source shown for one law)
function sexpAt(text, i) {
  let depth = 0, inStr = false;
  for (let j = i; j < text.length; j++) {
    const c = text[j];
    if (inStr) { if (c === '"') inStr = false; continue; }
    if (c === '"') inStr = true;
    else if (c === ';') { while (j < text.length && text[j] !== '\n') j++; }
    else if (c === '(') depth++;
    else if (c === ')') { depth--; if (depth === 0) return text.slice(i, j + 1); }
  }
  return text.slice(i);
}
// the declaration `(HEAD NAME …)` of a surface text, if it has one
function declOf(text, head, name) {
  const re = new RegExp(`\\(${head}\\s+${name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}[\\s)]`);
  const m = re.exec(text);
  return m ? sexpAt(text, m.index) : '';
}

export function teach(ctx) {
  const { $, K, openWindow, wins, runIn, members, short, prefill } = ctx;
  const answer = (r) => ({ ok: r[0] === OK, text: dec.decode(r.slice(1)) });
  const ob = (form) => answer(K().ob(form));
  const kv = (pairs) => $('table', { class: 'props sunken' }, pairs.filter(Boolean).map(([k, ...v]) => $('tr', {}, $('td', {}, k), $('td', {}, ...v))));
  const glossed = (pairs) => $('details', { class: 'terms' }, $('summary', {}, 'Terms'), $('dl', {}, pairs.flatMap(([t, d]) => [$('dt', {}, t), $('dd', {}, d)])));
  const pre = (t, cls = '') => $('pre', { class: `src sunken ${cls}` }, t);
  const h = (t) => $('h4', {}, t);

  // what the tab knows of a package's text: the source a member installed (surface or core) by id
  const sources = new Map();
  function remember(id, text, surface = null) {
    const o = sources.get(id) ?? {};
    sources.set(id, { ...o, text: o.text ?? text, surface: surface ?? o.surface ?? (text && !isCore(text) ? text : null) });
  }

  const idOfText = (t) => [...sources].find(([, x]) => x.text === t)?.[0];

  // a member's name, for a member id; else a short id link
  const nameOf = (hex) => members().find((m) => m.id === hex)?.name;
  function idLink(m, hex) {
    if (!hex || hex === '-') return hex ?? '';
    const n = nameOf(hex);
    if (n) return $('span', { title: `member ${hex}` }, n);
    if (hex === 'anyone') return 'anyone';
    return $('a', { class: 'hex', title: hex, onclick: () => openInspector(m, hex) }, short(hex));
  }

  // ---------------------------------------------------------------- the object inspector
  async function openInspector(m, id) {
    const w = openWindow({ id: `obj-${id}`, title: `Object ${short(id)}`, w: 640, body: $('div', {}, 'reading…') });
    w.refresh = async () => {
      const nd = m.nd ?? ctx.nd();
      const d = await nd.run(m, ['read', id, '?']);
      const s = await nd.run(m, ['read', id]);
      if (d.exit !== 'ok') { w.setBody($('div', { class: 'bad' }, (d.stderr || '').trim(), ' ', d.stdout.trim())); return; }
      const lines = d.stdout.trim().split('\n').filter(Boolean);
      const props = {}, methods = [], calls = [], laws = [], rels = [], extraLaws = [];
      for (const l of lines) {
        const sp = l.indexOf(' '), k = sp < 0 ? l : l.slice(0, sp), v = sp < 0 ? '' : l.slice(sp + 1);
        if (k === 'method') { const [i, label, ...ty] = v.split(' '); methods.push({ i, label, ty: ty.join(' ') }); }
        else if (k === 'call') { const [i, j, ...ty] = v.split(' '); calls.push({ i, j, ty: ty.join(' ') }); }
        else if (k === 'law' && /^[0-9a-f]{64}( |$)/.test(v)) extraLaws.push(v);
        else if (k === 'law') laws.push(v);
        else if (k === 'rel') rels.push(v);
        else props[k] = v;
      }
      const pkg = props.package;
      let src = pkg ? sources.get(pkg) : null;
      if (pkg && !src?.core) {
        const r = answer((m.K ?? K()).source(m.index, pkg));
        if (r.ok) { remember(pkg, r.text); sources.get(pkg).core = r.text; src = sources.get(pkg); }
      }
      const shown = src?.surface ?? src?.core ?? '';
      const grants = answer((m.K ?? K()).grants(m.index, id));
      const grantRows = grants.ok ? grants.text.trim().split('\n').filter(Boolean).map((l) => {
        const x = l.split(' '); const at = (k) => x[x.indexOf(k) + 1];
        return $('tr', {}, $('td', {}, idLink(m, x[1])), $('td', {}, idLink(m, at('grantee'))), $('td', {}, idLink(m, at('issuer'))), $('td', {}, at('rights')));
      }) : [];
      const stateText = (s.exit === 'ok' ? s.stdout : s.stderr).trim();
      const body = $('div', { class: 'inspector' },
        kv([['object', id], ['owner', idLink(m, props.owner)],
          ['package', pkg ? idLink(m, pkg) : 'none: a data object (numbered slots, no code)'],
          props.doc ? ['doc', props.doc.replace(/^"|"$/g, '')] : null,
          props.state ? ['state type', $('code', {}, props.state)] : null,
          ['viewed by', `${m.name}'s follow (read ${short(id)} ?), updated after each command`]]),
        h('State'), pre(stateText || '(empty)'),
        pkg ? '' : $('p', {}, $('a', { class: 'cmd', onclick: () => prefill(m, `write ${id} 0 `) }, 'write a slot…')),
        methods.length ? [h('Methods'), $('table', { class: 'props sunken methods' },
          $('tr', {}, $('td', {}, 'index'), $('td', {}, 'name'), $('td', {}, 'argument type'), $('td', {}, 'calls it may make'), $('td', {}, '')),
          methods.map((x) => $('tr', {}, $('td', {}, x.i), $('td', {}, $('b', {}, x.label)), $('td', {}, $('code', {}, x.ty)),
            $('td', {}, calls.filter((c) => c.i === x.i).map((c) => $('div', {}, $('code', {}, c.ty)))),
            $('td', {}, $('a', { class: 'cmd', onclick: () => prefill(m, `invoke ${id} ${x.i} `) }, 'invoke…')))))] : '',
        laws.length ? [h('Laws'), laws.map((ℓ) => lawPanel(m, id, ℓ, src, stateText))] : '',
        extraLaws.length ? [h('Extra laws (data object)'), extraLaws.map((x) => $('div', {}, $('code', {}, x)))] : '',
        rels.length ? [h('Relations'), rels.map((r) => relPanel(m, id, r))] : '',
        h('Grants on this object'),
        grantRows.length ? $('table', { class: 'props sunken' }, $('tr', {}, $('td', {}, 'grant'), $('td', {}, 'grantee'), $('td', {}, 'issuer'), $('td', {}, 'rights')), grantRows)
          : $('p', { class: 'dim' }, 'none. Only the owner may change or call it.'),
        pkg ? [h('Source'), sourcePanel(m, pkg, src)] : '',
        glossed([
          ['owner', 'The member who may change or call the object without a grant.'],
          ['package', 'The code the object runs, installed once and named by the hash of its bytes.'],
          ['state', 'The object\'s current value. A method computes a new one; the laws judge the change.'],
          ['method', 'An entry point. invoke OBJ INDEX ARGS runs it. Methods are numbered in name order. A method returns the new state, the calls to make, and the row edits.'],
          ['calls', 'The kinds of call a method may return (for example an invoke of another object). The kernel runs them in the same Turn, as this object.'],
          ['law', 'A rule over every change: it sees the old state, the new state and the request, and returns ok or a refusal with a reason.'],
          ['relation', 'A table of keyed rows inside the object, with a row limit. A method reads rows only through pins the call signed.'],
          ['grant', 'A cell that lets one member (or anyone) use rights on this object: observe, mutate, invoke:N.'],
          ['core', 'The package as the kernel reads it: the source lowered to plain terms (lam, record, case, …).'],
        ]));
      w.setBody(body);
      void shown;
    };
    await w.refresh();
    return w;
  }

  function sourcePanel(m, pkg, src) {
    const box = $('div', {});
    const show = (which) => {
      const t = which === 'surface' ? src?.surface : src?.core ?? src?.text;
      box.replaceChildren(pre(t || '(no text)'));
    };
    const tabs = $('div', { class: 'tabs' },
      src?.surface ? $('button', { onclick: () => show('surface') }, 'source (as installed)') : '',
      $('button', { onclick: () => show('core') }, 'core (as the kernel reads it)'),
      $('button', { onclick: () => openEditor(src?.surface ?? src?.core ?? '') }, 'edit a copy…'));
    show(src?.surface ? 'surface' : 'core');
    return $('div', {}, tabs, box);
  }

  // one law: its clause from the source, and a form that runs it on an old and a new state
  function lawPanel(m, obj, ℓ, src, stateText) {
    const clause = (src?.surface && declOf(src.surface, 'law', ℓ)) || '';
    const old = $('textarea', { class: 'sunken', rows: 1, cols: 60, 'aria-label': 'old state' }, /^\(record/.test(stateText) ? stateText : '(record)');
    const neu = $('textarea', { class: 'sunken', rows: 1, cols: 60, 'aria-label': 'new state' }, /^\(record/.test(stateText) ? stateText : '(record)');
    const who = m.id ?? '00'.repeat(32);
    const req = $('textarea', { class: 'sunken', rows: 2, cols: 60, 'aria-label': 'request' },
      `(record (agent #${who}) (principal #${who}) (self #${obj}) (notBefore 0) (validUntil 100) (occasion (invoke 0)))`);
    const out = $('div', {});
    const run = () => {
      const text = src?.surface ?? src?.core ?? src?.text;
      if (!text) { out.replaceChildren($('span', { class: 'bad' }, 'no package text in this tab')); return; }
      const r = ob(`(law ${text} ${ℓ} ${old.value} ${neu.value} ${req.value})`);
      out.replaceChildren(kv([['verdict', $('b', { class: r.ok ? 'ok' : 'bad' }, r.ok ? r.text : `refused ${r.text}`)]]));
    };
    return $('details', { class: 'law' }, $('summary', {}, $('b', {}, ℓ), clause ? '' : ' (clause in the core text below)'),
      clause ? pre(clause) : '',
      $('div', { class: 'dim' }, 'Run this law on one change. The occasion names the act: (birth (record)), (write (record)), (invoke N).'),
      kv([['old', old], ['new', neu], ['request', req]]),
      $('button', { class: 'btn', onclick: run }, 'Judge'), out);
  }

  function relPanel(m, obj, r) {
    const name = (r.match(/^\((\S+)/) || [])[1] ?? r;
    const out = $('div', {});
    const list = async () => {
      const x = await (m.nd ?? ctx.nd()).run(m, ['read', obj, name, '16']);
      out.replaceChildren(pre((x.exit === 'ok' ? x.stdout : x.stderr).trim() || '(no rows)'));
    };
    return $('div', {}, $('code', {}, r), ' ', $('button', { class: 'btn', onclick: list }, 'list rows'), out);
  }

  // ---------------------------------------------------------------- the package editor
  const templates = {
    record: { title: 'record with one method', text: `(package
  (doc "A record with one text field. set replaces it.")
  (state (rec (text bytes)))
  (method set (arg (rec (text (bytes 1 200))))
    (done (with state (text arg.text)))))`, seed: '(record (text "first"))' },
    counter: { title: 'counter with a law (never below floor)', text: `(package
  (doc "A counter. inc adds, dec subtracts. The law keeps n at or above floor.")
  (state (rec (floor nat) (n nat)))
  (method dec (arg (rec (by nat))) (done (with state (n (- state.n arg.by)))))
  (method inc (arg (rec (by nat))) (done (with state (n (+ state.n arg.by)))))
  (law floor
    (on (birth invoke) (if (<= new.floor new.n) ok (refuse "below floor")))
    (else ok)))`, seed: '(record (floor 0) (n 0))' },
    table: { title: 'object with a relation (a guest list)', text: `(package
  (doc "A guest list. sign adds one row per member; a row is final.")
  (state (rec (open bool)))
  (rel guests (key (who digest)) (val (rec (note bytes))) (limit 64) (guard mine))
  (method sign (arg (rec (note (bytes 1 200)))) (edits 1)
    (check (state.open "closed")
      (done state (insert guests (record (who req.agent)) (record (note arg.note))))))
  (guard mine
    (case edit
      (insert x (if (deq x.key.who req.agent) ok (refuse "not yours")))
      (upsert x (refuse "final")))))`, seed: '(record (open true))' },
    hole: { title: 'object with a hole (the document section, core text)', path: 'world/doc/Section', needs: ['world/doc/Section.lib0', 'world/doc/Section.lib1', 'world/doc/Section.lib2'],
      seed: '(record (accepted false) (acceptor #ALICE) (cap 2000) (chooser #ALICE) (closes 100000) (selected none))' },
  };
  async function templateText(t) { return t.text ?? (await (await fetch(t.path)).text()); }

  async function openEditor(text = null, opts = {}) {
    const area = $('textarea', { class: 'sunken code', rows: 18, cols: 80, spellcheck: 'false', 'aria-label': 'package source' });
    const gutter = $('pre', { class: 'gutter', 'aria-hidden': 'true' });
    const syncGutter = () => { const n = area.value.split('\n').length; gutter.textContent = Array.from({ length: n }, (_, i) => i + 1).join('\n'); gutter.scrollTop = area.scrollTop; };
    area.addEventListener('input', syncGutter); area.addEventListener('scroll', syncGutter);
    const out = $('div', {});
    const who = $('select', { 'aria-label': 'install as' }, members().map((m) => $('option', { value: m.name }, m.name)));
    const pick = $('select', { 'aria-label': 'template', onchange: async () => { const t = templates[pick.value]; if (t) { area.value = await templateText(t); syncGutter(); state.seed = t.seed; state.needs = t.needs ?? []; } } },
      $('option', { value: '' }, 'start from…'), Object.entries(templates).map(([k, t]) => $('option', { value: k }, t.title)));
    const state = { seed: '(record)', needs: [] };
    const markLine = (n) => {
      const ls = area.value.split('\n'); let a = 0; for (let i = 0; i < n - 1 && i < ls.length; i++) a += ls[i].length + 1;
      area.focus(); area.setSelectionRange(a, a + (ls[n - 1] ?? '').length);
      area.scrollTop = Math.max(0, (n - 4) * 15);
    };
    const check = () => {
      const r = ob(`(check ${area.value})`);
      const line = (r.text.match(/ line (\d+)/) || [])[1];
      out.replaceChildren(kv([['check', $('b', { class: r.ok ? 'ok' : 'bad' }, r.ok ? 'ok' : `refused ${r.text.split(' ')[0]}`)],
        r.ok ? ['package', `${r.text.split(' ')[1]} bytes, id ${short(r.text.split(' ').at(-1))}`] : ['detail', r.text],
        line ? ['line', $('a', { class: 'cmd', onclick: () => markLine(+line) }, `${line} (select it)`)] : null]));
      if (line) markLine(+line);
      return r;
    };
    const core = () => {
      const r = isCore(area.value) ? { ok: true, text: area.value } : ob(`(core ${area.value})`);
      out.replaceChildren(r.ok ? $('div', {}, $('div', { class: 'dim' }, 'The source lowered to core terms: the text install reads.'), pre(r.text)) : kv([['core', $('b', { class: 'bad' }, `refused ${r.text}`)]]));
    };
    const install = async () => {
      const c = check(); if (!c.ok) return;
      const m = members().find((x) => x.name === who.value);
      for (const p of state.needs) {
        const t = await (await fetch(p)).text();
        const r = await runIn(m, ['install', t], 'a package this one imports');
        if (r.exit !== 'ok' && !/idTaken/.test(r.stderr)) { out.append($('div', { class: 'bad' }, `import ${p}: ${r.stderr.trim()}`)); return; }
      }
      const coreText = isCore(area.value) ? { ok: true, text: area.value } : ob(`(core ${area.value})`);
      if (!coreText.ok) { out.append($('div', { class: 'bad' }, `core: ${coreText.text}`)); return; }
      const r = await runIn(m, ['install', coreText.text], 'from the package editor');
      const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1] ?? c.text.split(' ').at(-1);
      remember(id, coreText.text, isCore(area.value) ? null : area.value);
      const seed = state.seed.replace(/#ALICE/g, `#${members()[0].id}`);
      out.replaceChildren(kv([['install', $('b', { class: r.exit === 'ok' ? 'ok' : 'bad' }, r.exit === 'ok' ? 'ok' : (r.stderr || r.exit).trim())],
        ['package', idLink(m, id)],
        ['next', $('a', { class: 'cmd', onclick: () => prefill(m, `create --pkg ${id} '${seed}'`) }, `create an object of it (as ${m.name})…`)]]));
    };
    if (text != null) area.value = text; else { area.value = templates.counter.text; state.seed = templates.counter.seed; }
    syncGutter();
    const body = $('div', { class: 'editor' },
      $('div', {}, pick, ' ', $('button', { class: 'btn', onclick: () => openGrammar('surface') }, 'grammar')),
      $('div', { class: 'edit' }, gutter, area),
      $('div', {}, $('button', { class: 'btn', onclick: check }, 'Check'), ' ', $('button', { class: 'btn', onclick: core }, 'Show core'), ' ',
        'install as ', who, ' ', $('button', { class: 'btn', onclick: install }, 'Install')),
      out,
      glossed([
        ['package', '(package decl…): a state type, methods, laws, relations and guards.'],
        ['state', 'The type of the object\'s value: (rec (field type)…).'],
        ['method', '(method name (arg type) body): the body ends in (done state item…), the new state and its row edits; (with state (field value)…) changes some fields.'],
        ['law', '(law name (on occasions body)… (else body)): judges old → new; old, new and req are in scope; ok or (refuse "why").'],
        ['check', 'Reads, lowers and type-checks the source as install will. A refusal names the line.'],
        ['core', 'What the source lowers to. install takes this text; its hash is the package id.'],
        ['install', 'A call that stores the package. The same bytes twice: refused (idTaken).'],
      ]));
    openWindow({ id: `editor-${opts.id ?? 'main'}`, title: 'Package editor', x: 160, y: 40, w: 680, body });
  }

  // ---------------------------------------------------------------- the term REPL and the grammar
  function openGrammar(which = 'core') {
    const box = $('div', {});
    const show = (w) => { const r = answer(K().grammar(w)); box.replaceChildren(pre(r.text), $('p', { class: 'dim' }, w === 'core'
      ? 'Core: what a term is. A package\'s methods and laws are core terms after lowering. Names: x a variable; (. e l) a field; (lam x T e) a function; (fix e) recursion; (refuse T "why") a refusal.'
      : 'Surface: what a package source is. It lowers to the core (Show core in the package editor). ℓ a label, T a type, e a term, n a number.')); };
    show(which);
    openWindow({ id: 'grammar', title: 'Grammar', x: 220, y: 60, w: 760, body: $('div', {}, $('div', { class: 'tabs' }, $('button', { onclick: () => show('core') }, 'core (terms)'), $('button', { onclick: () => show('surface') }, 'surface (packages)')), box) });
  }

  const replExamples = [
    ['(+ 1 2)', 'addition'], ['(let x nat 4 (* x x))', 'a local name'], ['((fn (x nat) (y nat) (+ x y)) 2 3)', 'a function of two arguments'],
    ['(. (record (a 1) (b "hi")) b)', 'a field of a record'], ['(case (inj (sum (no (rec)) (yes nat)) yes 5) (no x 0) (yes y y))', 'a sum and a case'],
    ['(cat "ab" "cd")', 'bytes'], ['(- 1 2)', 'a fault: natural numbers do not go below 0'],
    ['((. (fix (lam self (rec (go (-> nat nat))) (record (go (lam n nat (if (== n 0) 0 ((. self go) (- n 1)))))))) go) 1000)', 'recursion; try 200 ticks'],
  ];
  function openRepl() {
    const input = $('textarea', { class: 'sunken code', rows: 3, cols: 72, spellcheck: 'false', 'aria-label': 'term' }, '(+ 1 2)');
    const ticks = $('input', { class: 'sunken', size: 8, value: '10000', 'aria-label': 'ticks' });
    const hist = $('div', { class: 'repl-out sunken' });
    const run = (form) => {
      const r = ob(form === 'type' ? `(type ${input.value})` : `(eval ${+ticks.value || 0} ${input.value})`);
      let row;
      if (form === 'type') row = kv([['term', $('code', {}, input.value)], ['type', $('b', { class: r.ok ? '' : 'bad' }, r.ok ? r.text : `refused ${r.text}`)]]);
      else if (r.ok) {
        const m = r.text.match(/^(.*) : (.*) used (\d+) of (\d+)$/s) || r.text.match(/^(<.*>) used (\d+) of (\d+)$/s);
        row = m && m.length === 5 ? kv([['term', $('code', {}, input.value)], ['value', $('b', {}, m[1])], ['type', $('code', {}, m[2])], ['ticks', `${m[3]} of ${m[4]}`]])
          : kv([['term', $('code', {}, input.value)], ['value', r.text]]);
      } else row = kv([['term', $('code', {}, input.value)], ['result', $('b', { class: 'bad' }, r.text)]]);
      hist.prepend(row);
    };
    input.addEventListener('keydown', (e) => { if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); run('eval'); } });
    const body = $('div', {},
      $('div', {}, input),
      $('div', {}, $('button', { class: 'btn', onclick: () => run('eval') }, 'Evaluate'), ' ', $('button', { class: 'btn', onclick: () => run('type') }, 'Type'), ' ticks ', ticks, ' ',
        $('button', { class: 'btn', onclick: () => openGrammar('core') }, 'grammar')),
      $('details', {}, $('summary', {}, 'Examples'), $('ul', {}, replExamples.map(([t, why]) => $('li', {}, $('a', { class: 'cmd', onclick: () => { input.value = t; } }, t), $('span', { class: 'dim' }, ` ${why}`))))),
      hist,
      glossed([['term', 'An expression of the core language. Ctrl+Enter evaluates.'], ['type', 'The checker\'s type for the term; the evaluator runs only a well-typed term.'],
        ['tick', 'One step of the evaluator. Every run has a tick budget; past it the run stops (fault ticks). A call pays for its ticks.'],
        ['fault', 'A run that stopped without a value: ticks, underflow, divZero, a refusal.']]));
    openWindow({ id: 'repl', title: 'Terms', x: 200, y: 80, w: 640, body });
  }

  // ---------------------------------------------------------------- the Turn view
  function openTurn(m0, tx) {
    // the first member whose follow absorbed the step (the viewer first)
    const order = [m0, ...members().filter((x) => x !== m0 && (x.K ?? null) === (m0.K ?? null))];
    let r = null, by = null;
    for (const m of order) { const x = answer((m.K ?? K()).turn(m.index, tx)); if (x.ok) { r = x; by = m; break; } if (!r) r = x; }
    let body;
    if (!by) body = kv([['tx', tx], ['turn', $('span', { class: 'bad' }, `not absorbed by any follow in this tab (${r?.text}). Run nd sync as a member, then open it again.`)]]);
    else {
      const ls = r.text.trim().split('\n');
      const rest = (l) => l.slice(l.indexOf(' ') + 1);
      const first = (k) => ls.find((l) => l.startsWith(k + ' '));
      const hexes = (s) => s.split(/([0-9a-f]{64})/).map((p) => (/^[0-9a-f]{64}$/.test(p) ? idLink(by, p) : p));
      const pins = ls.filter((l) => l.startsWith('pin ')).map((l) => { const x = l.split(' '); return $('tr', {}, $('td', {}, idLink(by, x[1])), $('td', { title: x[3] }, short(x[3])), $('td', {}, x.slice(4).join(' '))); });
      const states = ls.filter((l) => l.startsWith('state ')).map((l) => { const m = l.match(/^state (\S+) before (.*) after (.*)$/); return m ? $('tr', {}, $('td', {}, idLink(by, m[1])), $('td', {}, $('code', {}, m[2] || '(empty)')), $('td', {}, $('code', {}, m[3]))) : ''; });
      const tree = ls.filter((l) => /^(run|call) \d+ /.test(l)).map((l) => { const d = +l.split(' ')[1]; return $('div', { style: `padding-left:${d * 18}px` }, ...hexes(l)); });
      const refusal = first('refusal');
      body = $('div', { class: 'turn' },
        kv([['step', rest(first('step'))], ['tx', rest(first('tx'))], ['height', rest(first('height'))], ['member', idLink(by, rest(first('member')))],
          first('ticks') ? ['ticks', rest(first('ticks'))] : null, first('charge') ? ['charge', rest(first('charge'))] : null,
          first('code') ? ['code', rest(first('code'))] : null, ['window', rest(first('window'))], ['seen by', `${by.name}'s follow`]]),
        h('Call'), kv([['call', ...hexes(rest(first('call') ?? 'call -'))], first('args') ? ['arguments', $('code', {}, rest(first('args')))] : null]),
        tree.length ? [h('Runs and the calls they returned'), $('div', { class: 'sunken tree' }, tree)] : '',
        pins.length ? [h('Cells read, with their pins'), $('table', { class: 'props sunken' }, $('tr', {}, $('td', {}, 'cell'), $('td', {}, 'pin (version seen)'), $('td', {}, 'what the Turn does')), pins)] : '',
        states.length ? [h('State written'), $('table', { class: 'props sunken' }, $('tr', {}, $('td', {}, 'cell'), $('td', {}, 'before'), $('td', {}, 'after')), states)] : '',
        ls.some((l) => l.startsWith('create ')) ? [h('Cells created'), ls.filter((l) => l.startsWith('create ')).map((l) => $('div', {}, ...hexes(l)))] : '',
        ls.some((l) => /^(row|range) /.test(l)) ? [h('Rows and ranges'), ls.filter((l) => /^(row|range) /.test(l)).map((l) => $('div', {}, ...hexes(l)))] : '',
        refusal ? [h('Refusal'), kv([['rule', $('b', { class: 'bad' }, ...hexes(rest(refusal)))]])] : '',
        glossed([['Turn', 'One admitted call: its pins, its writes, the cells it creates, its ticks. The log is a list of Turns and recorded refusals.'],
          ['pin', 'The version of a cell the call was planned on. If the cell changed since, the call is declined (stale).'],
          ['keep / write / retire', 'What the Turn does to a pinned cell: read it only, change slots, or delete it.'],
          ['run', 'One method run: its arguments and ticks. Its calls are run in the same Turn, as the calling object.'],
          ['charge', 'Storage the Turn pays for, in bytes.'], ['window', 'The heights at which the signed call may land.'],
          ['refusal', 'A call the writer recorded as refused, with the rule that refused it, re-derived by this follow.']]));
    }
    openWindow({ id: `turn-${tx}`, title: `Turn ${short(tx)}`, x: 180, y: 60, w: 680, body });
  }

  // ---------------------------------------------------------------- the tutorial
  // A step: words, an optional package source (editable), commands (editable, one per line:
  // `WHO: nd ARGV… [-> NAME]`, `{NAME}` substitutes an id bound earlier, `{source}` the source's core
  // text; `race A: … | B: …` runs B's command while A's signed call waits to be sent).
  const steps = [
    { title: 'A cell', text: [
      'A cell is the unit of state. A data cell has numbered slots and no code.',
      'alice creates one. She is its owner: only she may write it.'],
      cmds: 'alice: create -> cell\nalice: read {cell} ?' },
    { title: 'A write', text: [
      'alice writes slot 0. Her copy of the World (her follow) checks the write before her key signs it. If the check fails, nothing is signed.',
      'The writer puts the call in the log as a Turn. Click its tx to see the Turn: the pin on the cell and the slot it set.'],
      cmds: 'alice: write {cell} 0 hello\nalice: read {cell}' },
    { title: 'A pin and a stale write', text: [
      'A call names the version of every cell it reads (a pin). alice grants bob the right to write the cell (mutate).',
      'bob writes slot 0. While his signed call is in transit, alice writes slot 0 first. bob\'s pin no longer matches: the writer declines his call (stale). Run again, his follow plans on the new version.'],
      expect: ['ok', 'ok', 'declined stale', 'ok', 'ok'],
      cmds: 'alice: grant {cell} {bob} mutate -> g\nbob: sync\nrace bob: write {cell} 0 "from bob" --via {g} | alice: write {cell} 0 "from alice"\nbob: write {cell} 0 "from bob, again" --via {g}\nbob: read {cell}' },
    { title: 'An object with a method', text: [
      'A package is code: a state type and methods. An object runs one package.',
      'A method returns the new state. invoke OBJ N ARGS runs method N; methods are numbered in name order. Change the source and run again: the kernel checks it at install.'],
      source: `(package
  (doc "A counter. inc adds by to n.")
  (state (rec (n nat)))
  (method inc (arg (rec (by nat)))
    (done (with state (n (+ state.n arg.by))))))`,
      cmds: 'alice: install {source} -> counterPkg\nalice: create --pkg {counterPkg} "(record (n 0))" -> counter\nalice: invoke {counter} 0 "(record (by 5))"\nalice: read {counter}' },
    { title: 'A law that refuses', text: [
      'A law judges every change. It sees the old state, the new state and the request, and answers ok or a refusal.',
      'The method computes; the law decides whether the result may stand. Here dec by 3 takes n from 7 to 4, below the floor 5: refused (lawDenied). Open the object to run the law on states you choose.'],
      source: templates.counter.text,
      expect: ['ok', 'ok', 'ok', 'refused lawDenied', 'ok'],
      cmds: 'alice: install {source} -> floorPkg\nalice: create --pkg {floorPkg} "(record (floor 5) (n 6))" -> floored\nalice: invoke {floored} 1 "(record (by 1))"\nalice: invoke {floored} 0 "(record (by 3))"\nalice: read {floored}' },
    { title: 'A grant to another member', text: [
      'Only the owner may call an object directly. A grant gives one member rights on one object; here invoke:1, the method inc.',
      'bob names the grant with --via. A call outside the grant is refused (grantRight). A call with no grant is refused (noGrant).'],
      expect: ['ok', 'ok', 'refused grantRight', 'refused noGrant'],
      cmds: 'alice: grant {floored} {bob} invoke:1 -> g2\nbob: invoke {floored} 1 "(record (by 2))" --via {g2}\nbob: invoke {floored} 0 "(record (by 1))" --via {g2}\nbob: invoke {floored} 1 "(record (by 2))"' },
    { title: 'A hole and a candidate', text: [
      'A hole is a slot whose value is chosen among proposed values (candidates). A candidate cites facts as support; a fact is a pinned cell.',
      'bob posts a fact (his grant) and proposes a text supported by it; alice selects it. alice revokes the grant: the fact dies, method 5 re-checks the candidate, and it is suspended. Selecting it again is refused, and the refusal names the dead support.',
      'The source is the section package as generated (core text); it imports three helper packages.'],
      sourcePath: 'world/doc/Section', texts: { lib0: 'world/doc/Section.lib0', lib1: 'world/doc/Section.lib1', lib2: 'world/doc/Section.lib2' },
      expect: [...Array(13).fill('ok'), 'refused program'],
      cmds: `alice: install {lib0}\nalice: install {lib1}\nalice: install {lib2}\nalice: install {source} -> section\nalice: create --pkg {section} "(record (accepted false) (acceptor #{alice}) (cap 2000) (chooser #{alice}) (closes 100000) (selected none))" -> doc\nalice: grant {doc} {bob} invoke:2,invoke:3 -> g3\nbob: invoke {doc} 2 "(record (cell #{g3}) (pin #{g3}))" --via {g3}\nbob: invoke {doc} 3 '(record (cand #{g3}) (s0 (some (record (cell #{g3}) (pin #{g3})))) (s1 none) (value "a light on the rock"))' --pin facts "(record (cell #{g3}))" --via {g3}\nalice: invoke {doc} 9 "(record (cand #{g3}))" --pin candidates "(record (cand #{g3}))" --pin facts "(record (cell #{g3}))"\nalice: read {doc} candidates 8\nalice: revoke {g3}\nalice: invoke {doc} 5 "(record (cand #{g3}))" --pin candidates "(record (cand #{g3}))" --pin facts "(record (cell #{g3}))"\nalice: read {doc} candidates 8\nalice: invoke {doc} 9 "(record (cand #{g3}))" --pin candidates "(record (cand #{g3}))" --pin facts "(record (cell #{g3}))"` },
    { title: 'An offer and a fuse', text: [
      'An offer is a standing row: a role and a range of terms. Two objects of one offer package, alice\'s X and bob\'s Y, each post one.',
      'bob grants X the right to call Y\'s take. alice fuses: X checks that the two offers agree on a price, removes its offer, and calls Y.take with the same deal; Y checks and removes its offer. One Turn, two objects.',
      'The source is the offer package as generated (core text).'],
      sourceKernel: 'offer',
      cmds: 'alice: install {source} -> offerPkg\nalice: create --pkg {offerPkg} "(record)" -> X\nbob: create --pkg {offerPkg} "(record)" -> Y\nalice: invoke {X} 1 "(record (n 0) (role buyer) (terms (record (price (record (hi 10) (lo 5))))))"\nbob: invoke {Y} 1 "(record (n 0) (role seller) (terms (record (price (record (hi 12) (lo 8))))))"\nbob: grant {Y} {X} invoke:3 -> take\nalice: sync\nalice: invoke {X} 0 "(record (keys (record (a 0) (b 0))) (pair (record (a #{X}) (b #{Y}))) (theta (record (price 9))) (via (some #{take})))" --pin offer "(record (n 0))" --pin {Y}/offer "(record (n 0))"\nalice: read {X} offer 8\nbob: read {Y} offer 8' },
  ];

  const tut = { at: 0, v: {}, done: new Set() };
  function parseLine(l) {
    const race = l.match(/^race\s+(\w+):\s*(.*?)\s*\|\s*(\w+):\s*(.*)$/);
    if (race) return { race: true, who: race[1], cmd: race[2], other: race[3], otherCmd: race[4] };
    const m = l.match(/^(\w+):\s*(?:nd\s+)?(.*?)(?:\s*->\s*(\w+))?\s*$/);
    return m ? { who: m[1], cmd: m[2], bind: m[3] } : null;
  }
  async function stepSource(s) {
    if (s.source) return s.source;
    if (s.sourcePath) return (await fetch(s.sourcePath)).text();
    if (s.sourceKernel) return dec.decode(K().text(s.sourceKernel).slice(1));
    return null;
  }
  async function runStep(i, srcArea, cmdArea, out) {
    const s = steps[i], v = tut.v;
    for (const m of members()) v[m.name] = m.id;
    out.replaceChildren();
    let coreText = null;
    if (srcArea && !isCore(srcArea.value)) {
      const c = ob(`(check ${srcArea.value})`);
      if (!c.ok) {
        const line = (c.text.match(/ line (\d+)/) || [])[1];
        out.append(kv([['source', $('b', { class: 'bad' }, `refused ${c.text}`)], line ? ['line', line] : null]));
        return;
      }
      const k = ob(`(core ${srcArea.value})`); coreText = k.ok ? k.text : srcArea.value;
    } else if (srcArea) coreText = srcArea.value;
    for (const [k, p] of Object.entries(s.texts ?? {})) v[k] = await (await fetch(p)).text();
    // split first, then substitute: a {NAME} that holds a package text stays one argument
    const argvOf = (cmd) => ctx.splitArgv(cmd).map((a) => a.replace(/\{(\w+)\}/g, (_, n) => (n === 'source' ? coreText ?? '' : v[n] ?? `{${n}}`)));
    const rows = [];
    const table = $('table', { class: 'props sunken steps' });
    out.append(table);
    for (const line of cmdArea.value.split('\n').map((x) => x.trim()).filter(Boolean)) {
      const p = parseLine(line);
      if (!p) { table.append($('tr', {}, $('td', {}, line), $('td', { class: 'bad' }, 'not WHO: COMMAND'))); return; }
      const m = members().find((x) => x.name === p.who);
      if (!m) { table.append($('tr', {}, $('td', {}, line), $('td', { class: 'bad' }, `no member ${p.who}`))); return; }
      const argv = argvOf(p.cmd);
      if (p.race) {
        const o = members().find((x) => x.name === p.other);
        ctx.raceArm(m, o, argvOf(p.otherCmd));
      }
      const r = await runIn(m, argv, p.race ? `${p.other} writes first while this call is in transit` : 'tutorial', { quiet: true });
      // a package this World already holds (idTaken) is bound by the id this tab installed it under
      const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1] ?? (argv[0] === 'install' && /idTaken/.test(r.stderr) ? idOfText(argv[1]) : undefined);
      if (p.bind && id) v[p.bind] = id;
      if (argv[0] === 'install' && id) remember(id, argv[1], srcArea && argv[1] === coreText && !isCore(srcArea.value) ? srcArea.value : null);
      const tx = (r.stdout.match(/^tx ([0-9a-f]{64})/m) || [])[1];
      const name = (r.stderr || '').trim().split('\n').find((l) => l.startsWith(r.exit + ' ')) ?? '';
      const shownCmd = `${p.who}$ nd ${argv.map((a) => (a.length > 48 ? `${a.slice(0, 45)}…` : a)).join(' ')}`;
      const outText = r.stdout.trim().split('\n').filter((l) => !/^(tx|id) /.test(l)).join('\n');
      table.append($('tr', {},
        $('td', {}, $('code', {}, shownCmd)),
        $('td', {}, $('b', { class: r.exit === 'ok' ? 'ok' : r.exit === 'declined' ? 'warn' : 'bad' }, r.exit === 'ok' ? 'ok' : name || r.exit),
          id ? [' ', p.bind ? `${p.bind} = ` : 'id ', idLink(m, id)] : '',
          tx ? [' ', $('a', { class: 'cmd', onclick: () => openTurn(m, tx) }, 'Turn')] : '',
          outText ? pre(outText.length > 600 ? `${outText.slice(0, 600)}…` : outText) : '',
          (r.stdout.match(/^hint .*/m) || [])[0] ? $('div', { class: 'dim' }, r.stdout.match(/^hint .*/m)[0]) : '')));
      rows.push(r);
      if (r.exit === 'client') break;
    }
    tut.done.add(i);
  }
  async function openTutorial(at = tut.at) {
    tut.at = at;
    const s = steps[at];
    const src = await stepSource(s);
    const srcArea = src != null ? $('textarea', { class: 'sunken code', rows: Math.min(14, src.split('\n').length + 1), cols: 82, spellcheck: 'false', 'aria-label': 'package source' }, src) : null;
    const cmdArea = $('textarea', { class: 'sunken code', rows: s.cmds.split('\n').length + 1, cols: 82, spellcheck: 'false', 'aria-label': 'commands' }, s.cmds);
    const out = $('div', {});
    const nav = $('ol', { class: 'tut-nav' }, steps.map((x, i) => $('li', { class: (i === at ? 'on ' : '') + (tut.done.has(i) ? 'done' : '') }, $('a', { class: 'cmd', onclick: () => openTutorial(i) }, `${i + 1}. ${x.title}`))));
    const body = $('div', { class: 'tutorial' }, nav,
      $('h3', {}, `${at + 1}. ${s.title}`), s.text.map((t) => $('p', {}, t)),
      srcArea ? [$('div', { class: 'label' }, 'Package source ', $('button', { class: 'btn', onclick: () => openEditor(srcArea.value, { id: 'tut' }) }, 'open in editor'), ' ', $('button', { class: 'btn', onclick: () => openGrammar(s.source ? 'surface' : 'core') }, 'grammar')), srcArea] : '',
      $('div', { class: 'label' }, 'Commands (WHO: COMMAND, -> NAME binds the printed id, {NAME} uses it)'), cmdArea,
      $('div', {}, $('button', { class: 'btn', onclick: () => runStep(at, srcArea, cmdArea, out) }, 'Run'), ' ',
        at + 1 < steps.length ? $('button', { class: 'btn', onclick: () => openTutorial(at + 1) }, 'Next step') : ''),
      out);
    openWindow({ id: 'tutorial', title: 'Tutorial', x: 130, y: 20, w: 760, body });
  }

  return { openInspector, openEditor, openRepl, openGrammar, openTurn, openTutorial, remember, steps, templates, parseLine };
}
