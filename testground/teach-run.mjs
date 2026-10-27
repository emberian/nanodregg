// teach-run.mjs — the tutorial's steps (teach.js) under node, in order on one fresh World, against the
// kernel the page loads: every command must end as its step's `expect` says, in order.
//   node teach-run.mjs [--harness-control] [-v]
// The gate (testground/build/gate.sh) runs it beside lies-run and axes-run, so a step whose words
// teach one thing while the kernel now answers another is red. --harness-control adds an expectation
// no command meets (GATES-15).
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
import { teach, isCore } from './teach.js';
const argv = process.argv.slice(2);
const verbose = argv.includes('-v'), control = argv.includes('--harness-control');
const dec = new TextDecoder();
const K = await loadKernel(factory);
let race = null;
const nd = client(K, { beforeSubmit: async (m) => { if (race && race.member === m.name) { const r = race; race = null; r.result = await nd.run(r.other, r.argv); } } });
const g = genesis(K, 'testground', ['alice', 'bob']);
const members = g.members.map((m) => ({ ...m, K, nd }));
global.fetch = async (p) => ({ text: async () => readFileSync(new URL(p, import.meta.url), 'utf8') });
const splitArgv = (s) => { const out = []; let cur = '', q = null, any = false;
  for (const c of s) { if (q) { if (c === q) q = null; else cur += c; } else if (c === '"' || c === "'") { q = c; any = true; } else if (/\s/.test(c)) { if (cur || any) { out.push(cur); cur = ''; any = false; } } else cur += c; }
  if (cur || any) out.push(cur); return out; };
const T = teach({ $: () => ({}), K: () => K, nd: () => nd, openWindow: () => ({}), wins: new Map(), runIn: async () => null, members: () => members,
  short: (h) => h, prefill: () => {}, splitArgv, raceArm: () => {} });
const outcome = (r) => (r.exit === 'ok' ? 'ok' : ((r.stderr || '').trim().split('\n').find((l) => l.startsWith(r.exit + ' ')) ?? r.exit));
const v = {};
for (const m of members) v[m.name] = m.id;
let bad = 0, n = 0;
const steps = control ? [...T.steps, { title: 'harness-control', cmds: 'alice: create', expect: ['refused harness-control'] }] : T.steps;
for (const [i, s] of steps.entries()) {
  let src = s.source ?? (s.sourcePath ? readFileSync(new URL(s.sourcePath, import.meta.url), 'utf8') : s.sourceKernel ? dec.decode(K.text(s.sourceKernel).slice(1)) : null);
  let core = null;
  if (src != null) {
    // a core text is what install takes (its install is its check); a surface text is lowered first
    const k = isCore(src) ? null : K.ob(`(core ${src})`);
    if (k && k[0] !== 0) { bad++; console.log(`FAIL ${i + 1} ${s.title}: the source does not lower: ${dec.decode(k.slice(1))}`); continue; }
    core = k ? dec.decode(k.slice(1)) : src;
  }
  for (const [k, p] of Object.entries(s.texts ?? {})) v[k] = readFileSync(new URL(p, import.meta.url), 'utf8');
  const argvOf = (c) => splitArgv(c).map((a) => a.replace(/\{(\w+)\}/g, (_, x) => (x === 'source' ? core : v[x] ?? `{${x}}`)));
  const lines = s.cmds.split('\n').map((x) => x.trim()).filter(Boolean);
  const got = [];
  for (const line of lines) {
    const p = T.parseLine(line);
    const m = members.find((x) => x.name === p.who);
    if (p.race) race = { member: m.name, other: members.find((x) => x.name === p.other), argv: argvOf(p.otherCmd) };
    const r = await nd.run(m, argvOf(p.cmd));
    n++;
    const id = (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
    if (p.bind && id) v[p.bind] = id;
    got.push(outcome(r));
    if (verbose) console.log(`  ${p.who}$ ${p.cmd.slice(0, 90)} -> ${outcome(r)} ${r.stdout.trim().split('\n').filter((l) => !/^(tx|id) /.test(l)).join(' | ').slice(0, 160)}`);
  }
  const want = s.expect ?? lines.map(() => 'ok');
  const same = want.length === got.length && want.every((w, j) => got[j] === w || (w.endsWith('*') && got[j].startsWith(w.slice(0, -1))));
  if (!same) bad++;
  console.log(`${same ? 'OK  ' : 'FAIL'} ${i + 1} ${s.title.padEnd(26)} ${got.join(' · ')}${same ? '' : `\n     expected ${want.join(' · ')}`}`);
}
console.log(bad ? `TESTGROUND TUTORIAL RED: ${bad} step(s)` : `TESTGROUND TUTORIAL GREEN: ${steps.length} steps, ${n} commands`);
process.exit(bad ? 1 : 0);
