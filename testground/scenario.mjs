// scenario.mjs — the prototype's script, run under node against the same kernel the page loads:
// genesis (alice, bob), alice creates an object and writes it, describes it, grants bob mutate,
// then bob and alice race one slot: bob's write was signed over a pin alice's write moves.
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
const ms = () => performance.now();
let t = ms();
const K = await loadKernel(factory);
console.log(`kernel loaded+initialised ${(ms() - t).toFixed(0)} ms`);
const frames = [];
let raced = false;
const nd = client(K, {
  onFrame: (f) => frames.push(f),
  beforeSubmit: async (m, argv) => {
    if (m.name === 'bob' && !raced) { raced = true; const r = await nd.run(A, ['write', obj, '0', 'alice was here first']); console.log('  [race] alice writes first:', r.exit, r.stdout.trim()); }
  },
});
t = ms();
const g = genesis(K, 'testground', ['alice', 'bob']);
console.log(`genesis ${(ms() - t).toFixed(0)} ms\n${g.text}`);
const [A, B] = g.members;
const step = async (m, argv) => { const t0 = ms(); const n0 = frames.length; const r = await nd.run(m, argv); console.log(`${m.name}$ nd ${argv.join(' ')}  -> ${r.exit} (${(ms() - t0).toFixed(0)} ms, ${frames.length - n0} frames)\n${r.stdout}${r.stderr}`); return r; };
const c = await step(A, ['create']);
const obj = (c.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
await step(A, ['write', obj, '0', 'hello from the testground']);
await step(A, ['read', obj, '?']);
await step(A, ['read', obj]);
const gr = await step(A, ['grant', obj, B.id, 'mutate']);
const grant = (gr.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
await step(B, ['sync']);
await step(B, ['write', obj, '0', 'bob says hi', '--via', grant]);
await step(B, ['write', obj, '0', 'bob, after the race', '--via', grant]);
await step(A, ['grant', '77'.repeat(32), B.id, 'mutate']);
await step(B, ['read', obj]);
import { readFileSync } from 'node:fs';
const bell = readFileSync(new URL('./world/resident/Bell', import.meta.url), 'utf8');
for (let i = 0; i < 3; i++) await step(A, ['install', bell]);
const t9 = ms(); let n = 0; for (; n < 20; n++) await nd.run(A, ['write', obj, '0', `w${n}`]); console.log(`20 writes: ${((ms() - t9) / 20).toFixed(1)} ms each`);
