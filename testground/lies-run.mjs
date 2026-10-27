// lies-run.mjs — every Writer-menu lie's scene under node, on a fresh World each, against the kernel
// the page loads; prints the outcome alice's or bob's follow ended with beside the one the row expects.
//
//   node lies-run.mjs [--honest] [--harness-control] [SCENE]
//   node lies-run.mjs --hosted ws://…/ws [--honest] [SCENE]     the relay lies in two hosted tabs
//
// The expectation is the row's own (K.lies: Web.Sim.Testground reads it off Protocol.rows), so a row
// that moves its line or changes its outcome moves the scene's verdict with it: this run is RED until
// the scene follows (gates/runs.tsv `script:testground/build/gate.sh`). --honest is the control
// (lies off: the checked line must then NOT end as the row expects, except where the row's lesson is
// that the lie does not stick). --harness-control adds one expectation nothing meets (GATES-15).
// --hosted: alice and bob are two kernels, each joined over the guest-book's invitation; a relay lie
// is told by each tab's own relay around its socket (tg_relay_pre/post), the writer is the real one.
// A writer lie has no writer in a hosted tab to tell it (`refused noWriter`), and a member's lie would
// stay in the shared World for every later joiner, so those scenes are n/a there.
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { loadKernel, client, genesis, hex } from './nd.js';
import { lieScenes, memberLies, runScene, head0Of } from './demos.js';
import { joinMember, worldOf } from './hosted.mjs';
const argv = process.argv.slice(2);
const flag = (f) => argv.includes(f);
const hostedAt = argv.indexOf('--hosted'), hostedUrl = hostedAt >= 0 ? argv[hostedAt + 1] : null;
const honest = flag('--honest'), control = flag('--harness-control');
const only = control ? 'harness-control' : argv.find((a, i) => !a.startsWith('--') && !(hostedAt >= 0 && i === hostedAt + 1));
const dec = new TextDecoder();
const K0 = await loadKernel(factory);
const fetchText = async (p) => (p.startsWith('kernel:') ? dec.decode(K0.text(p.slice(7)).slice(1)) : readFileSync(new URL(p, import.meta.url), 'utf8'));
const wj = hostedUrl ? await worldOf(hostedUrl) : null;

// one World per scene: two founders in one kernel, or two hosted tabs (two kernels, one real writer)
async function world() {
  if (!hostedUrl) {
    const g = genesis(K0, 'testground', ['alice', 'bob']);
    const nd = client(K0, {});
    for (const m of g.members) { m.K = K0; m.nd = nd; }
    return { members: g.members, origin: g.text.match(/^origin (\S+)/m)[1], head0: head0Of(g.text), everyK: [K0] };
  }
  const ms = [await joinMember(factory, hostedUrl, wj, 'alice'), await joinMember(factory, hostedUrl, wj, 'bob')];
  return { members: ms, origin: ms[0].origin, everyK: ms.map((m) => m.K) };
}

const scenes = [...Object.entries(lieScenes), ...Object.entries(memberLies)];
if (control) scenes.push(['harness-control', { ...lieScenes.flipEvent, expect: 'harness-control: an outcome no follow ends with' }]);
let bad = 0, ran = 0;
for (const [name, sc] of scenes) {
  if (only && name !== only) continue;
  const row = sc.expect ? { name, row: 'harness-control', expect: sc.expect } : (K0.lies.find((l) => l.name === name) ?? {});
  if (!row.expect) { bad++; console.log(`FAIL   ${name.padEnd(14)} the kernel's menu has no row for this scene (a row renamed or removed its plant)`); continue; }
  if (honest && sc.control) { console.log(`n/a    ${name.padEnd(14)} ${sc.control}`); continue; }
  if (hostedUrl && (memberLies[name] || K0.lies.find((l) => l.name === name)?.kind === 'writer')) {
    console.log(`n/a    ${name.padEnd(14)} hosted: ${memberLies[name] ? 'a member\'s lie would stay in the shared World' : 'a writer lie needs the writer in the tab (refused noWriter)'}`);
    continue;
  }
  const w = await world();
  const by = (n) => w.members.find((m) => m.name === n);
  const t = performance.now();
  const act = async (s, v) => {
    if (s.lie) { if (!honest || s.lie === 'neverForward' || s.lie === 'honest') for (const K of w.everyK) K.lie(s.lie); return null; }
    if (s.cold) { const m = by(s.cold); m.K.cold(m.index); return null; }
    const m = by(s.who);
    const r = s.forge ? await m.nd.forge(m, s.forge(v)) : s.cancel ? await m.nd.run(m, ['cancel', hex(by(s.cancel).last)]) : await m.nd.run(m, s.argv(v));
    if (process.env.V) console.log(`  ${m.name}$ ${s.forge ? 'forge' : 'nd'} … -> ${r.exit} ${r.stderr.trim()}`);
    return r;
  };
  const r = await runScene(sc, { fetchText, members: w.members, origin: w.origin, head0: w.head0, act });
  for (const K of w.everyK) K.lie('honest');
  for (const m of w.members) m.host?.close();
  ran++;
  const hit = r.ok && (r.outcome === row.expect) !== honest;
  if (!hit) bad++;
  console.log(`${hit ? (honest ? 'CLEAN ' : 'CAUGHT') : 'FAIL  '} ${name.padEnd(14)} got "${r.outcome ?? '-'}"  row ${row.row}:${row.line ?? '-'} expects "${row.expect}"  ${(performance.now() - t).toFixed(0)} ms${r.ok ? '' : `  STOPPED at ${JSON.stringify(r.at?.argv ? 'argv' : r.at)} with ${r.r?.exit} ${r.r?.stderr}`}`);
}
const mode = `${hostedUrl ? 'hosted ' : ''}${honest ? 'honest' : 'lies'}`;
if (!ran) { console.log(`FAIL no scene ran (${only ?? 'all'})`); bad++; }
console.log(bad ? `TESTGROUND LIES (${mode}) RED: ${bad} scene(s)` : `TESTGROUND LIES (${mode}) GREEN: ${ran} scene(s)`);
process.exit(bad ? 1 : 0);
