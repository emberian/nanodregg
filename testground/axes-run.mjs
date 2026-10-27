// axes-run.mjs — each axis's demo (demos.js) under node, on a fresh World each, against the kernel the
// page loads: every step must answer as scripted (its exit, the refusal it names, the word it says).
//   node axes-run.mjs [--harness-control] [DEMO]
// A demo with `worlds` gets each extra World as its own kernel instance (as the page does). The
// gate (testground/build/gate.sh) runs it beside lies-run.mjs, so a demo whose argv no longer
// reaches its outcome is red, never a silent scene. --harness-control runs one step no member's
// command can pass (GATES-15).
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
import { demos, runDemo } from './demos.js';
const argv = process.argv.slice(2);
const control = argv.includes('--harness-control');
const only = argv.find((a) => !a.startsWith('--'));
const dec = new TextDecoder();
if (control) demos['harness-control'] = { title: 'harness-control', steps: [{ who: 'alice', argv: () => ['create'], says: 'harness-control: a word no command prints' }] };
const axes = control ? ['harness-control'] : only ? [only] : ['generator', 'creator', 'meter', 'timelock', 'document', 'inbox'];
let bad = 0;
for (const name of axes) {
  const d = demos[name];
  if (!d) { bad++; console.log(`FAIL ${name}: no such demo`); continue; }
  const K = await loadKernel(factory);
  const g = genesis(K, 'testground', ['alice', 'bob']);
  const members = g.members.map((m) => ({ ...m, K, nd: client(K) }));
  const origin = { B: g.text.match(/^origin (\S+)/m)[1] };
  for (const [w, names] of Object.entries(d.worlds ?? {})) {
    const KW = await loadKernel(factory);
    const gw = genesis(KW, w, names);
    origin[w] = gw.text.match(/^origin (\S+)/m)[1];
    for (const m of gw.members) members.push({ ...m, K: KW, nd: client(KW) });
  }
  const t = performance.now();
  let n = 0;
  const r = await runDemo(name, {
    fetchText: async (p) => (p.startsWith('kernel:') ? dec.decode(K.text(p.slice(7)).slice(1)) : readFileSync(new URL(p, import.meta.url), 'utf8')),
    members, origin,
    run: async (m, a) => { n++; const o = await m.nd.run(m, a); if (process.env.V) console.log(`  ${m.name}$ nd ${a.join(' ').slice(0, 90)} -> ${o.exit} ${o.stderr.trim()}`); return o; },
  });
  const last = r.results.at(-1);
  if (!r.ok) bad++;
  console.log(`${r.ok ? 'OK  ' : 'FAIL'} ${name.padEnd(10)} ${n} commands, ${((performance.now() - t) / 1000).toFixed(1)} s; last: ${last?.exit} ${(last?.stderr ?? '').trim().split('\n').pop()}${r.ok ? '' : `  STOPPED at ${(r.at?.say ?? r.at?.argv?.toString() ?? '').slice(0, 90)}`}`);
  const meter = members.find((m) => m.name === 'bob');
  if (name === 'meter') {
    // bob's health receipt (Protocol.Health), built from his own fold and checked against his own head:
    // a receipt that does not check, or that states no ticks after the spins, is red
    const kv = Object.fromEntries(dec.decode(K.meter(meter.index).slice(1)).trim().split('\n').map((l) => l.split(' ')));
    const ok = kv.checked === 'ok' && +kv.ticks > 0;
    if (!ok) bad++;
    console.log(`${ok ? '    ' : 'FAIL'} bob's health receipt (${(kv.health ?? '').length / 2} bytes, checked ${kv.checked}): ticks ${kv.ticks} of ${kv.budget} · refusals ${kv.refusals} · total ${kv.total} · height ${kv.height}`);
  }
}
console.log(bad ? `TESTGROUND AXES RED: ${bad} demo(s)` : `TESTGROUND AXES GREEN: ${axes.length} demo(s)`);
process.exit(bad ? 1 : 0);
