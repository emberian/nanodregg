// hosted-run.mjs — two members of a HOSTED World under node, each its own kernel instance as two
// tabs would be: each joins over the guest-book's invitation, is enrolled, and they run the
// document demo against the real `host serve` behind the relay (deploy/testground/run.sh).
//   node hosted-run.mjs ws://127.0.0.1:8787/ws [document|basic|door|inbox] [--harness-control]
// Every command must answer as scripted (its exit; `basic`: ok, then the read shows bob's text), the
// joins and first syncs included; the last line is `HOSTED <what> OK` or `HOSTED <what> RED: …`, exit
// 1 on red (testground/build/gate.sh runs every scene on a fresh World). --harness-control adds one
// expectation no command meets (GATES-15).
// `door` is the page's door to a live World (CLIENT-49): each joined member's roster, read off its
// own fold, holds itself, the guest-book and the other member; alice's membership RECORD (what the
// page keeps in localStorage) resumed in a fresh kernel (a reloaded tab) syncs, finds itself in its
// roster, and writes the object alice made before the reload; the same record with its seeds
// forgotten does not write (the keys are what came back); kernel.json's sha256 is kernel.wasm's.
// `inbox` is the page's "Ask the resident" (HOSTING-62, CLIENT-59) on a World with a resident
// (`run.sh resident`, `keys`, `resident-serve`): alice rings the public Bell aimed at her own section
// and the resident's answer arrives as its verified candidate; she retires her grant and the
// candidate is suspended `support0 dead`. The answer must be words, not a named text such as
// `(refused askCap)`, unless --named-ok.
import { readFileSync, existsSync } from 'node:fs';
import { createHash } from 'node:crypto';
import factory from './kernel.mjs';
import { runDemo } from './demos.js';
import { joinMember, resumeMember, rosterOf, worldOf, httpOf } from './hosted.mjs';
import { hex, rand32 } from './nd.js';
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
} else if (what === 'door') {
  const rosterHas = (m, ids, when) => {
    const r = rosterOf(m.K, m);
    console.log(`${m.name}'s roster ${when}: ${r.members.length} members at height ${r.height}${r.refused ? ` (refused ${r.refused})` : ''}`);
    for (const [who, id] of ids) if (!r.members.includes(id)) red(`${m.name}'s own fold has no member ${who} (${id.slice(0, 12)}…) ${when}`);
    return r;
  };
  const c = await must(alice, ['create']);
  const obj = (c.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];
  await must(alice, ['write', obj, '0', 'before the reload']);
  await must(bob, ['sync']); await must(alice, ['sync']);
  rosterHas(alice, [['alice', alice.id], ['bob', bob.id], ['the guest-book', wj.sponsor]], 'after both joined');
  rosterHas(bob, [['alice', alice.id], ['bob', bob.id], ['the guest-book', wj.sponsor]], 'after both joined');
  const rec = JSON.parse(JSON.stringify(alice.record));   // as localStorage hands it back
  const back = await resumeMember(factory, rec, 'alice-back');
  console.log(`alice-back: resumed member ${back.id.slice(0, 12)}… in a fresh kernel in ${back.joinMs.toFixed(0)} ms; sync ${back.syncExit}`);
  if (back.syncExit !== 'ok') red(`the resumed member's first sync: ${back.syncExit} ${back.syncErr}`);
  rosterHas(back, [['alice', alice.id], ['bob', bob.id]], 'after the reload');
  await must(back, ['write', obj, '0', 'after the reload']);
  const rd = await must(bob, ['read', obj]);
  if (!rd.stdout.includes('after the reload')) red('bob does not read the resumed alice\'s write');
  // the control: the same membership with its keys forgotten is not alice
  const forgot = await resumeMember(factory, { ...rec, seeds: [rand32(), rand32(), rand32()].map(hex) }, 'alice-forgot');
  const w = await show(forgot, ['write', obj, '0', 'a stranger with alice\'s ids']);
  if (w.exit === 'ok') red('a record with forgotten seeds wrote as alice');
  const kj = new URL('./kernel.json', import.meta.url);
  if (!existsSync(kj)) red('no kernel.json beside kernel.wasm (build.sh writes it)');
  const stamped = JSON.parse(readFileSync(kj, 'utf8')).sha256;
  const actual = createHash('sha256').update(readFileSync(new URL('./kernel.wasm', import.meta.url))).digest('hex');
  if (stamped !== actual) red(`kernel.json says sha256 ${stamped}, kernel.wasm is ${actual}`);
  console.log(`kernel ${actual.slice(0, 16)}… = kernel.json's`);
  // the abuse bounds the door needs: the guest-book's floor of its enrolment grant (gate.sh runs this
  // World with ND_TESTGROUND_ENROLL_FLOOR=250, so a join past the scenes' own is refused), then the
  // relay's per-address enrolment budget (429, Retry-After, enrollBudget)
  if (process.env.ND_TESTGROUND_ENROLL_FLOOR) {
    let floor = null;
    for (let n = 0; n < 8 && !floor; n++) {
      try { await joinMember(factory, url, wj, `probe${n}`); } catch (e) { floor = e.message; }
    }
    console.log(`a join at the floor: ${floor}`);
    if (!/enrollFloor/.test(floor ?? '')) red(`no join was refused enrollFloor: ${floor}`);
  }
  const at = await (await fetch(`${httpOf(url)}/attest`)).text();
  console.log(`GET /attest answers ${at.length} bytes (${JSON.parse(at).attest ? 'an attestation' : at.trim()})`);
  let budget = null;
  for (let n = 0; n < 12 && !budget; n++) {
    const r = await fetch(`${httpOf(url)}/enroll`, { method: 'POST', body: 'zz' });
    if (r.status === 429) budget = { after: n, retry: r.headers.get('retry-after'), body: await r.text() };
  }
  console.log(`the relay's enrolment budget: ${JSON.stringify(budget)}`);
  if (!budget || !/enrollBudget/.test(budget.body) || !(+budget.retry > 0)) red('the relay never refused an address its enrolment budget');
} else if (what === 'inbox') {
  if (!wj.inbox) red('world.json names no inbox (run.sh resident)');
  if (!alice.bellGrant) red('the guest-book gave alice no grant on the Bell');
  const you = Object.assign(Object.create(Object.getPrototypeOf(alice)), alice, { name: 'you' });
  const t0 = performance.now();
  const r = await runDemo('inboxHosted', { fetchText: async (p) => readFileSync(new URL(p, import.meta.url), 'utf8'), members: [you],
    vars: { bell: wj.inbox.bell, section: wj.inbox.section, bellGrant: alice.bellGrant, q: '"Write one short sentence for the first section of a document about lighthouses."' },
    run: async (m, argv) => show(m, argv) });
  if (!r.ok) red(`the inbox demo stopped at ${JSON.stringify(r.at?.say ?? r.at?.argv?.toString() ?? '')}`);
  const row = r.results.map((x) => x.stdout).find((o) => /verified/.test(o)) ?? '';
  const value = (row.match(/\(value "((?:[^"\\]|\\.)*)"\)/) || [])[1];
  console.log(`the resident's answer, as the section's candidate (${((performance.now() - t0) / 1000).toFixed(1)} s): ${JSON.stringify(value)}`);
  if (!row.includes(`(by #${wj.inbox.resident})`)) red(`the candidate is not by the resident's member: ${row}`);
  if (!value) red(`no candidate value in ${row}`);
  if (value.startsWith('(') && !process.argv.includes('--named-ok')) red(`the answer is a named text, not a model's words: ${value}`);
} else {
  const r = await runDemo('document', { fetchText: async (p) => readFileSync(new URL(p, import.meta.url), 'utf8'), members: [alice, bob],
    run: async (m, argv) => show(m, argv) });
  if (!r.ok) red(`the document demo stopped at ${JSON.stringify(r.at?.say ?? r.at?.argv?.toString() ?? '')}`);
}
console.log(`HOSTED ${what} OK (two members, two kernels, one real writer)`);
process.exit(0);
