// hosted.mjs — a member of a HOSTED World under node, its own kernel instance as a tab would be: it
// joins over the guest-book's invitation (tg_join: Invite.accept under the sponsor key world.json
// names), asks the guest-book to enrol its `init` token, and takes the ids it was enrolled under.
// hosted-run.mjs and lies-run.mjs --hosted run their members through it.
import { loadKernel, client, custody, rand32, unhex } from './nd.js';
import { framed, wsOpen } from './transport.js';
const dec = new TextDecoder();
export const httpOf = (ws) => ws.replace(/^ws/, 'http').replace(/\/ws$/, '');
export const worldOf = async (url) => (await fetch(`${httpOf(url)}/world.json`)).json();
export async function joinMember(factory, url, wj, name) {
  const K = await loadKernel(factory);
  const ok = K.table.statuses.find((s) => s.name === 'ok').code;
  const j = K.join(unhex(wj.invitation), unhex(wj.sponsorKey));
  if (j[0] !== ok) throw new Error(`join: ${dec.decode(j.slice(1))}`);
  const kv = Object.fromEntries(dec.decode(j.slice(1)).trim().split('\n').map((l) => l.split(' ')));
  const host = framed(wsOpen(url), { frameMax: K.table.bounds.frameBytesMax });
  const m = { name, index: +kv.index, origin: kv.origin, custody: custody(K, [rand32(), rand32(), rand32()]), K, host };
  m.nd = client(K, { host });
  const t0 = performance.now();
  const init = await m.nd.run(m, ['init', wj.sponsor]);
  const token = (init.stdout.match(/^join ([0-9a-f]+)/m) || [])[1];
  if (!token) throw new Error(`init: ${init.exit} ${init.stderr}`);
  const en = await (await fetch(`${httpOf(url)}/enroll`, { method: 'POST', body: token })).json();
  if (!en.member) throw new Error(`enroll: ${JSON.stringify(en)}`);
  K.self(m.index, en.member, en.grant); m.id = en.member; m.grant = en.grant;
  const s = await m.nd.run(m, ['sync']);
  m.joinMs = performance.now() - t0; m.syncExit = s.exit; m.syncErr = s.stderr.trim();
  return m;
}
