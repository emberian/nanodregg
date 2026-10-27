// demo-run.mjs — run a demo under node against the page's kernel (the same module, the same client)
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
import { runDemo } from './demos.js';
import { readFileSync } from 'node:fs';
const K = await loadKernel(factory);
const nd = client(K);
const g = genesis(K, 'testground', ['alice', 'bob']);
const r = await runDemo(process.argv[2] || 'document', {
  fetchText: async (p) => (p.startsWith('kernel:') ? new TextDecoder().decode(K.text(p.slice(7)).slice(1)) : readFileSync(new URL(p, import.meta.url), 'utf8')),
  members: g.members,
  run: async (m, argv, s) => { const t = performance.now(); const r = await nd.run(m, argv); console.log(`${m.name}$ nd ${argv.map((a) => a.length > 50 ? a.slice(0, 47) + '…' : a).join(' ')} -> ${r.exit} ${(performance.now() - t).toFixed(0)} ms\n${(r.stdout + r.stderr).split('\n').slice(0, 14).join('\n')}`); return r; },
});
if (process.env.METER) for (const m of g.members) console.log(`${m.name} meter:`, new TextDecoder().decode(K.meter(m.index).slice(1)).trim().replace(/\n/g, ' · '));
console.log(r.ok ? 'DEMO OK' : `DEMO STOPPED at ${r.at.argv.toString().slice(0, 60)}`);
