// guestbook.mjs — the hosted World's sponsor, a member like any other: the page's own client
// (nd.js + the kernel's follow) under node, on the writer's box, holding its own seeds.
//
//   node guestbook.mjs init DIR                 seeds into DIR/seeds (0600); prints `key HEX next HEX`
//                                               for `host genesis` (this member is founder 0)
//   node guestbook.mjs keys DIR                 the same two lines from seeds DIR already holds (a
//                                               second writer of the same genesis: run.sh fork)
//   node guestbook.mjs serve DIR HOST_SOCK      DIR/input holds `host genesis`'s `input HEX`
//
// `serve` follows the World from its genesis inputs (tg_found), signs an invitation to it (`invite
// INPUT`, the follow command) and writes DIR/world.json: the invitation, the sponsor's key and member
// id, which the page joins over (tg_join: Invite.accept under that key). Then, on DIR/guestbook.sock,
// one line `join HEX` (a visitor's `init` token) is answered with one JSON line: `enroll HEX` and
// `grant world MEMBER observe --via GRANT`, each this member's own nd command, its follow re-deriving
// and refusing by name like any member's; `{"member","grant"}` or `{"refused": NAME}`. One line
// `attest` is answered with this member's own `sync --attest` (`{"attest": HEX}`): its head, signed,
// which a member of another writer of the same genesis checks with `sync --check` (PROTOCOL-74). How many it
// enrolls is the kernel's to bound (the founder grant's enroll:N, its meter), not this file's.
import { readFileSync, writeFileSync, existsSync, unlinkSync, chmodSync } from 'node:fs';
import net from 'node:net';
import { webcrypto } from 'node:crypto';
import factory from './kernel.mjs';
import { loadKernel, client, custody, hex, unhex } from './nd.js';
import { framed, unixOpen } from './transport.js';

if (!globalThis.crypto) globalThis.crypto = webcrypto;
const [cmd, dir, hostSock] = process.argv.slice(2);
const K = await loadKernel(factory);
const rand = () => { const b = new Uint8Array(32); crypto.getRandomValues(b); return b; };

if (cmd === 'init') {
  if (existsSync(`${dir}/seeds`)) { console.error('seeds: exists'); process.exit(17); }
  const seeds = [rand(), rand(), rand()];
  writeFileSync(`${dir}/seeds`, seeds.map(hex).join('\n') + '\n', { mode: 0o600 });
  console.log(`key ${hex(K.pub(seeds[0]))} next ${hex(K.pub(seeds[1]))}`);
  process.exit(0);
}
if (cmd === 'keys') {
  const seeds = readFileSync(`${dir}/seeds`, 'utf8').trim().split('\n').map(unhex);
  console.log(`key ${hex(K.pub(seeds[0]))} next ${hex(K.pub(seeds[1]))}`);
  process.exit(0);
}
if (cmd !== 'serve') { console.error('usage: guestbook.mjs init DIR | keys DIR | serve DIR HOST_SOCK'); process.exit(2); }

writeFileSync(`${dir}/guestbook.pid`, `${process.pid}\n`);
const seeds = readFileSync(`${dir}/seeds`, 'utf8').trim().split('\n').map(unhex);
const input = readFileSync(`${dir}/input`, 'utf8').trim().replace(/^input /, '');
const T = K.table, okCode = T.statuses.find((s) => s.name === 'ok').code;
const f = K.found(unhex(input), 0);
if (f[0] !== okCode) { console.error(`found: ${new TextDecoder().decode(f.slice(1))}`); process.exit(1); }
const lines = Object.fromEntries(new TextDecoder().decode(f.slice(1)).trim().split('\n').map((l) => l.split(' ')));
const me = { name: 'guestbook', index: +lines.index, id: lines.member, grant: lines.grant, custody: custody(K, seeds) };
const host = framed(unixOpen(net, hostSock), { frameMax: T.bounds.frameBytesMax });
const nd = client(K, { host });
const run = async (argv) => { const r = await nd.run(me, argv); console.error(`guestbook$ nd ${argv[0]} … → ${r.exit} ${r.stderr.trim()}`); return r; };
const idOf = (r) => (r.stdout.match(/^id ([0-9a-f]{64})/m) || [])[1];

const s = await run(['sync']);
if (s.exit !== 'ok') process.exit(1);
const inv = await run(['invite', input]);
const invitation = (inv.stdout.match(/^invite ([0-9a-f]+)/m) || [])[1];
if (!invitation) process.exit(1);
writeFileSync(`${dir}/world.json`, JSON.stringify({ origin: lines.origin, invitation, sponsorKey: hex(K.pub(seeds[0])), sponsor: me.id }) + '\n');

let queue = Promise.resolve();
const enroll = async (token) => {
  const e = await run(['enroll', token]);
  const member = idOf(e);
  if (!member) return { refused: e.stderr.trim() || e.exit };
  const g = await run(['grant', 'world', member, 'observe', '--via', me.grant]);
  const grant = idOf(g);
  return grant ? { member, grant } : { refused: g.stderr.trim() || g.exit };
};
const sock = `${dir}/guestbook.sock`;
if (existsSync(sock)) unlinkSync(sock);
net.createServer((c) => {
  let buf = '';
  c.on('data', (d) => {
    buf += d; if (buf.length > 512) return c.destroy();
    const nl = buf.indexOf('\n'); if (nl < 0) return;
    if (buf.slice(0, nl) === 'attest') {
      queue = queue.then(async () => {
        const a = await run(['sync', '--attest']);
        const h = (a.stdout.match(/^attest ([0-9a-f]+)/m) || [])[1];
        c.end(JSON.stringify(h ? { attest: h } : { refused: a.stderr.trim() || a.exit }) + '\n');
      }).catch(() => c.end('{"refused":"guestbook"}\n'));
      return;
    }
    const m = buf.slice(0, nl).match(/^join ([0-9a-f]{1,400})$/);
    if (!m) return c.end('{"refused":"usage"}\n');
    queue = queue.then(async () => c.end(JSON.stringify(await enroll(m[1])) + '\n')).catch(() => c.end('{"refused":"guestbook"}\n'));
  });
  c.on('error', () => {});
}).listen(sock, () => { chmodSync(sock, 0o660); console.error(`guestbook: member ${me.id}, serving ${sock}`); });
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, () => { try { unlinkSync(`${dir}/guestbook.pid`); } catch {} process.exit(0); });
