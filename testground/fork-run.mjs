// fork-run.mjs — the fork across two tabs (PROTOCOL-74, DESIGN-TRUST T1), under node: two writers of
// ONE genesis (deploy/testground/run.sh fork), two members, one per writer, each in its own kernel.
//   node fork-run.mjs ws://…A/ws ws://…B/ws
// Both writers' guest-books are the same founder (the same seeds), so both Worlds have one origin and
// each tab's invitation is the same; they diverge at their first different Turn. Tab two writes in B;
// tab one, in A, checks B's guest-book attestation (`sync --check`, its follow cold, catching up
// THROUGH the attested position on its own writer's log) and is refused forkedWorld by name. The
// control: the same check of A's own guest-book attestation is not refused.
import factory from './kernel.mjs';
import { joinMember, worldOf, httpOf } from './hosted.mjs';
const [urlA, urlB] = process.argv.slice(2);
const [wa, wb] = [await worldOf(urlA), await worldOf(urlB)];
console.log(`A ${urlA}: origin ${wa.origin.slice(0, 16)}…  B ${urlB}: origin ${wb.origin.slice(0, 16)}…  ${wa.origin === wb.origin ? 'one origin' : 'TWO ORIGINS (not a fork)'}`);
const one = await joinMember(factory, urlA, wa, 'one'), two = await joinMember(factory, urlB, wb, 'two');
const show = async (m, argv) => { const t = performance.now(); const r = await m.nd.run(m, argv); console.log(`${m.name}$ nd ${argv.map((a) => (a.length > 24 ? a.slice(0, 21) + '…' : a)).join(' ')} -> ${r.exit} (${(performance.now() - t).toFixed(0)} ms) ${(r.stdout + r.stderr).trim().split('\n').filter((l) => !l.startsWith('tx ')).join(' | ').slice(0, 140)}`); return r; };
const c = await show(two, ['create']);
await show(two, ['write', c.stdout.match(/^id (\S+)/m)[1], '0', 'written at writer B']);
const attest = async (url) => (await (await fetch(`${httpOf(url)}/attest`)).json());
const check = async (m, url) => { const a = await attest(url); if (!a.attest) return { exit: 'none', stderr: JSON.stringify(a) }; m.K.cold(m.index); return show(m, ['sync', '--check', a.attest]); };
console.log('one checks A\'s own guest-book attestation (the control):');
const ctl = await check(one, urlA);
console.log('one checks B\'s guest-book attestation:');
const fk = await check(one, urlB);
const forked = fk.exit === 'refused' && /refused forkedWorld/.test(fk.stderr);
const ok = ctl.exit === 'ok' && forked;
console.log(ok ? 'FORK CAUGHT: one origin, two writers, forkedWorld by name' : `FORK NOT CAUGHT (control ${ctl.exit} ${ctl.stderr?.trim()}; check ${fk.exit} ${fk.stderr?.trim()})`);
process.exit(ok ? 0 : 1);
