// hosted-run.mjs — two members of a HOSTED World under node, each its own kernel instance as two
// tabs would be: each joins over the guest-book's invitation, is enrolled, and they run the
// document demo against the real `host serve` behind the relay (deploy/testground/run.sh).
//   node hosted-run.mjs ws://127.0.0.1:8787/ws [document|basic]
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { loadKernel, client, custody, rand32, unhex } from './nd.js';
import { framed, wsOpen } from './transport.js';
import { runDemo } from './demos.js';
const [url, what = 'document'] = process.argv.slice(2);
const http = url.replace(/^ws/, 'http').replace(/\/ws$/, '');
const wj = await (await fetch(`${http}/world.json`)).json();
const dec = new TextDecoder();
async function member(name) {
  const K = await loadKernel(factory);   // a tab: its own kernel, its own follow
  const ok = K.table.statuses.find((s) => s.name === 'ok').code;
  const j = K.join(unhex(wj.invitation), unhex(wj.sponsorKey));
  if (j[0] !== ok) throw new Error(`join: ${dec.decode(j.slice(1))}`);
  const kv = Object.fromEntries(dec.decode(j.slice(1)).trim().split('\n').map((l) => l.split(' ')));
  const host = framed(wsOpen(url), { closedStatus: K.table.statuses.find((s) => s.name === 'closed').code, frameMax: K.table.bounds.frameBytesMax });
  const m = { name, index: +kv.index, custody: custody(K, [rand32(), rand32(), rand32()]), K };
  m.nd = client(K, { host });
  const t0 = performance.now();
  const init = await m.nd.run(m, ['init', wj.sponsor]);
  const token = (init.stdout.match(/^join ([0-9a-f]+)/m) || [])[1];
  if (!token) throw new Error(`init: ${init.exit} ${init.stderr}`);
  const en = await (await fetch(`${http}/enroll`, { method: 'POST', body: token })).json();
  if (!en.member) throw new Error(`enroll: ${JSON.stringify(en)}`);
  K.self(m.index, en.member, en.grant); m.id = en.member; m.grant = en.grant;
  const s = await m.nd.run(m, ['sync']);
  console.log(`${name}: joined origin ${kv.origin.slice(0, 12)}…, enrolled member ${m.id.slice(0, 12)}… in ${(performance.now() - t0).toFixed(0)} ms; sync ${s.exit}`);
  return m;
}
const alice = await member('alice'), bob = await member('bob');
const show = async (m, argv) => { const t = performance.now(); const r = await m.nd.run(m, argv); console.log(`${m.name}$ nd ${argv.map((a) => a.length > 30 ? a.slice(0, 27) + '…' : a).join(' ')} -> ${r.exit} (${(performance.now() - t).toFixed(0)} ms) ${r.stderr.trim()}`); return r; };
if (what === 'basic') {
  const c = await show(alice, ['create']);
  const obj = (c.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
  await show(alice, ['write', obj, '0', 'hello from a hosted World']);
  const g = await show(alice, ['grant', obj, bob.id, 'mutate']);
  const grant = (g.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
  await show(bob, ['write', obj, '0', 'bob, from another tab', '--via', grant]);
  await show(alice, ['read', obj]);
} else {
  const r = await runDemo('document', { fetchText: async (p) => readFileSync(new URL(p, import.meta.url), 'utf8'), members: [alice, bob],
    run: async (m, argv) => show(m, argv) });
  console.log(r.ok ? 'DEMO OK (two members, two kernels, one real writer)' : `DEMO STOPPED at ${JSON.stringify(r.at?.say ?? '')}`);
}
process.exit(0);
