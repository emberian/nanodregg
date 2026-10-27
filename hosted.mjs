// hosted.mjs — a member of a HOSTED World, in a tab (testground.js) or under node (hosted-run.mjs,
// lies-run.mjs --hosted, fork-run.mjs): it joins over the guest-book's invitation (tg_join:
// Invite.accept under the sponsor key world.json names), asks the guest-book to enrol its `init`
// token, and takes the ids it was enrolled under. A member that joined is a RECORD (its relay, the
// World's origin, the invitation and sponsor key it accepted, its seeds, its ids); a visitor who comes
// back resumes from it: the same invitation accepted again in a fresh kernel, the same keys, the same
// ids, and a `sync` that re-derives every Turn since the invitation. Nothing in the record is taken
// on the writer's word: the origin is the invitation's, the ids are checked against the member's own
// fold (`rosterOf`) once it has caught up.
import { loadKernel, client, custody, rand32, hex, unhex } from './nd.js';
import { framed, wsOpen } from './transport.js';
const dec = new TextDecoder();
export const httpOf = (ws) => ws.replace(/^ws/, 'http').replace(/\/ws$/, '');
export const worldOf = async (url) => (await fetch(`${httpOf(url)}/world.json`)).json();
const okOf = (K) => K.table.statuses.find((s) => s.name === 'ok').code;
const kvOf = (b) => Object.fromEntries(dec.decode(b).trim().split('\n').map((l) => l.split(' ')));

/** Accept an invitation under a sponsor key in kernel K: a follow whose World the invitation's signed inputs make. */
export function accept(K, invitation, sponsorKey) {
  const j = K.join(unhex(invitation), unhex(sponsorKey));
  if (j[0] !== okOf(K)) throw new Error(`the invitation is refused: ${dec.decode(j.slice(1))}`);
  const kv = kvOf(j.slice(1));
  return { index: +kv.index, origin: kv.origin };
}

/** A member of the World at `url` in kernel K, its writer frames over the relay's WebSocket. */
function memberIn(K, url, { name, index, origin, seeds, onFrame }) {
  const host = framed(wsOpen(url), { frameMax: K.table.bounds.frameBytesMax });
  const m = { name, index, origin, custody: custody(K, seeds), K, host };
  m.nd = client(K, { host, onFrame });
  return m;
}

/** Join: accept world.json's invitation, `init` a join token signed by fresh keys, ask the guest-book
 * to enrol it, take the ids it answers. `run(m, argv, why)` runs a command (the page prints it). */
export async function joinIn(K, url, wj, name, { onFrame, run = (m, argv) => m.nd.run(m, argv), say = () => {} } = {}) {
  const a = accept(K, wj.invitation, wj.sponsorKey);
  const m = memberIn(K, url, { name, ...a, seeds: [rand32(), rand32(), rand32()], onFrame });
  say(m, 'joined');
  const init = await run(m, ['init', wj.sponsor], 'join token, signed by your new key');
  const token = (init.stdout.match(/^join ([0-9a-f]+)/m) || [])[1];
  if (!token) throw new Error(`init: ${init.exit} ${init.stderr.trim()}`);
  let en;
  try { en = await (await fetch(`${httpOf(url)}/enroll`, { method: 'POST', body: token })).json(); } catch (e) { en = { refused: e.message }; }
  if (!en.member) throw new Error(`Not enrolled: ${en.refused ?? JSON.stringify(en)}`);
  K.self(m.index, en.member, en.grant); m.id = en.member; m.grant = en.grant;
  m.record = recordOf(m, url, wj);
  return m;
}

/** What a tab keeps of a member so that its visitor can come back (JSON; the page's localStorage). */
export function recordOf(m, url, wj) {
  return { v: 1, relay: url, origin: m.origin, invitation: wj.invitation, sponsorKey: wj.sponsorKey, sponsor: wj.sponsor,
           seeds: m.custody.seeds.map(hex), member: m.id, grant: m.grant, joined: new Date().toISOString() };
}

/** Come back: the record's invitation accepted again in K (the origin it makes must be the record's),
 * its keys and ids. The caller then syncs: the follow re-derives every Turn since the invitation. */
export function resumeIn(K, rec, name, { onFrame } = {}) {
  if (rec?.v !== 1) throw new Error('not a membership record this page can read');
  const a = accept(K, rec.invitation, rec.sponsorKey);
  if (a.origin !== rec.origin) throw new Error(`the record's invitation makes World ${a.origin}, not ${rec.origin}`);
  const m = memberIn(K, rec.relay, { name, ...a, seeds: rec.seeds.map(unhex), onFrame });
  const s = K.self(m.index, rec.member, rec.grant);
  if (s[0] !== okOf(K)) throw new Error(`self: ${dec.decode(s.slice(1))}`);
  m.id = rec.member; m.grant = rec.grant; m.record = rec;
  return m;
}

/** The members of m's World as m's own fold holds them (tg_members), and the height it has folded to. */
export function rosterOf(K, m) {
  const r = K.members(m.index);
  if (r[0] !== okOf(K)) return { members: [], height: null, refused: dec.decode(r.slice(1)) };
  const lines = dec.decode(r.slice(1)).trim().split('\n');
  return { members: lines.filter((l) => l.startsWith('member ')).map((l) => l.slice(7)),
           height: +((lines.find((l) => l.startsWith('height ')) ?? 'height 0').slice(7)),
           enrollLeft: lines.find((l) => l.startsWith('enrollLeft ')) ? +lines.find((l) => l.startsWith('enrollLeft ')).slice(11) : null };
}

/** Under node: a member in its own kernel instance, as a second tab would be; joined, then synced. */
export async function joinMember(factory, url, wj, name) {
  const K = await loadKernel(factory);
  const t0 = performance.now();
  const m = await joinIn(K, url, wj, name);
  const s = await m.nd.run(m, ['sync']);
  m.joinMs = performance.now() - t0; m.syncExit = s.exit; m.syncErr = s.stderr.trim();
  return m;
}

/** Under node: a returning visitor, a FRESH kernel instance (a reloaded tab) resumed from a record. */
export async function resumeMember(factory, rec, name) {
  const K = await loadKernel(factory);
  const t0 = performance.now();
  const m = resumeIn(K, rec, name);
  const s = await m.nd.run(m, ['sync']);
  m.joinMs = performance.now() - t0; m.syncExit = s.exit; m.syncErr = s.stderr.trim();
  return m;
}
