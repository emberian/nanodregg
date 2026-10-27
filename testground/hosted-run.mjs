// hosted-run.mjs — two members of a HOSTED World under node, each its own kernel instance as two
// tabs would be: each joins over the guest-book's invitation, is enrolled, and they run the
// document demo against the real `host serve` behind the relay (deploy/testground/run.sh).
//   node hosted-run.mjs ws://127.0.0.1:8787/ws [document|basic] [--harness-control]
// Every command must answer as scripted (its exit; `basic`: ok, then the read shows bob's text), the
// joins and first syncs included; the last line is `HOSTED <what> OK` or `HOSTED <what> RED: …`, exit
// 1 on red (testground/build/gate.sh runs both scenes on a fresh World). --harness-control adds one
// expectation no command meets (GATES-15).
import { readFileSync } from 'node:fs';
import factory from './kernel.mjs';
import { runDemo } from './demos.js';
import { joinMember, worldOf } from './hosted.mjs';
const args = process.argv.slice(2).filter((a) => !a.startsWith('--'));
const [url, what = 'document'] = args;
const control = process.argv.includes('--harness-control');
const red = (why) => { console.log(`FAIL ${why}`); console.log(`HOSTED ${what} RED: ${why}`); process.exit(1); };
const wj = await worldOf(url);
async function member(name) {
  const m = await joinMember(factory, url, wj, name);
  console.log(`${name}: joined origin ${m.origin.slice(0, 12)}…, enrolled member ${m.id.slice(0, 12)}… in ${m.joinMs.toFixed(0)} ms; sync ${m.syncExit}`);
  if (m.syncExit !== 'ok') red(`${name}'s first sync after enrolment: ${m.syncExit} ${m.syncErr}`);
  return m;
}
const alice = await member('alice'), bob = await member('bob');
const show = async (m, argv) => { const t = performance.now(); const r = await m.nd.run(m, argv); console.log(`${m.name}$ nd ${argv.map((a) => a.length > 30 ? a.slice(0, 27) + '…' : a).join(' ')} -> ${r.exit} (${(performance.now() - t).toFixed(0)} ms) ${r.stderr.trim()}`); return r; };
const must = async (m, argv, want = 'ok') => { const r = await show(m, argv); if (r.exit !== want) red(`${m.name}$ nd ${argv[0]}: ${r.exit} ${r.stderr.trim()}`); return r; };
if (control) await must(alice, ['create'], 'harness-control: an exit no command ends with');
if (what === 'basic') {
  const c = await must(alice, ['create']);
  const obj = (c.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
  await must(alice, ['write', obj, '0', 'hello from a hosted World']);
  const g = await must(alice, ['grant', obj, bob.id, 'mutate']);
  const grant = (g.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
  await must(bob, ['write', obj, '0', 'bob, from another tab', '--via', grant]);
  const r = await must(alice, ['read', obj]);
  if (!r.stdout.includes('bob, from another tab')) red('alice does not read bob\'s write');
} else {
  const r = await runDemo('document', { fetchText: async (p) => readFileSync(new URL(p, import.meta.url), 'utf8'), members: [alice, bob],
    run: async (m, argv) => show(m, argv) });
  if (!r.ok) red(`the document demo stopped at ${JSON.stringify(r.at?.say ?? r.at?.argv?.toString() ?? '')}`);
}
console.log(`HOSTED ${what} OK (two members, two kernels, one real writer)`);
process.exit(0);
