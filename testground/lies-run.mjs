// lies-run.mjs — every Writer-menu lie's scene under node, on a fresh World each, against the kernel
// the page loads; prints the outcome alice's or bob's follow ended with beside the one the row expects.
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { loadKernel, client, genesis } from './nd.js';
import { lieScenes, memberLies, runScene } from './demos.js';
const K = await loadKernel(factory);
const dec = new TextDecoder();
const fetchText = async (p) => (p.startsWith('kernel:') ? dec.decode(K.text(p.slice(7)).slice(1)) : readFileSync(new URL(p, import.meta.url), 'utf8'));
// --honest: every lie step but the loss (`neverForward`) skipped — the control: the checked line must
// then NOT end as the row expects (except where the row's lesson is that the lie does not stick)
const honest = process.argv.includes('--honest');
const only = process.argv.slice(2).find((a) => !a.startsWith('--'));
let bad = 0;
for (const [name, sc] of [...Object.entries(lieScenes), ...Object.entries(memberLies)]) {
  if (only && name !== only) continue;
  if (honest && sc.control) { console.log(`n/a    ${name.padEnd(14)} ${sc.control}`); continue; }
  const g = genesis(K, 'testground', ['alice', 'bob']);
  const origin = g.text.match(/^origin (\S+)/m)[1];
  const nd = client(K, {});
  const by = (n) => g.members.find((m) => m.name === n);
  const t = performance.now();
  const act = async (s, v) => {
    if (s.lie) { if (!honest || s.lie === 'neverForward' || s.lie === 'honest') K.lie(s.lie); return null; }
    if (s.cold) { K.cold(by(s.cold).index); return null; }
    const m = by(s.who);
    const r = s.forge ? nd.forge(m, s.forge(v)) : s.cancel ? await nd.run(m, ['cancel', Buffer.from(by(s.cancel).last).toString('hex')]) : await nd.run(m, s.argv(v));
    if (process.env.V) console.log(`  ${m.name}$ ${s.forge ? 'forge' : 'nd'} … -> ${r.exit} ${r.stderr.trim()}`);
    return r;
  };
  const r = await runScene(sc, { fetchText, members: g.members, origin, act });
  K.lie('honest');
  const row = K.lies.find((l) => l.name === name) ?? {};
  const hit = r.ok && (r.outcome === row.expect) !== honest;
  if (!hit) bad++;
  console.log(`${hit ? (honest ? 'CLEAN ' : 'CAUGHT') : 'MISS  '} ${name.padEnd(14)} got "${r.outcome ?? '-'}"  row ${row.row}:${row.line ?? '-'} expects "${row.expect}"  ${(performance.now() - t).toFixed(0)} ms${r.ok ? '' : `  STOPPED at ${JSON.stringify(r.at?.argv ? 'argv' : r.at)} with ${r.r?.exit} ${r.r?.stderr}`}`);
}
console.log(K.lies);
process.exit(bad ? 1 : 0);
