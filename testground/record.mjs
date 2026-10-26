// record.mjs — run the document demo and the scenario's writes, recording every kernel call and its
// reply as a trace a native build of the same kernel replays (differential: bytes must agree).
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
import { runDemo } from './demos.js';
import { readFileSync, writeFileSync } from 'node:fs';
const K0 = await loadKernel(factory);
const rec = [];
const wrap = (kind, f) => (...a) => { const r = f(...a); rec.push({ kind, a, r }); return r; };
const K = { ...K0, genesis: wrap(0, K0.genesis), host: wrap(1, K0.host), follow: wrap(2, K0.follow) };
const nd = client(K);
const g = genesis(K, 'testground', ['alice', 'bob']);
const t = performance.now();
const r = await runDemo('document', { fetchText: async (p) => readFileSync(new URL(p, import.meta.url), 'utf8'), members: g.members, run: (m, argv) => nd.run(m, argv) });
const c = await nd.run(g.members[0], ['create']); const obj = c.stdout.match(/^id ([0-9a-f]{64})/m)[1];
for (let i = 0; i < 20; i++) await nd.run(g.members[0], ['write', obj, '0', `w${i}`]);
const ms = performance.now() - t;
// trace: per call  u8 kind | u32 i | u8 op | u32 len | bytes | u32 rlen | rbytes
const parts = [];
const u32 = (n) => { const b = Buffer.alloc(4); b.writeUInt32LE(n); return b; };
for (const e of rec) {
  let i = 0, op = 0, p;
  if (e.kind === 0) p = e.a[0]; else if (e.kind === 1) { op = e.a[0]; p = e.a[1]; } else { i = e.a[0]; op = e.a[1]; p = e.a[2]; }
  parts.push(Buffer.from([e.kind]), u32(i), Buffer.from([op]), u32(p.length), Buffer.from(p), u32(e.r.length), Buffer.from(e.r));
}
writeFileSync('trace.bin', Buffer.concat(parts));
const kernelMs = rec.length;
console.log(`demo ${r.ok ? 'ok' : 'STOPPED'}; ${rec.length} kernel calls; wall ${ms.toFixed(0)} ms (wasm, node, incl. the JS client)`);
