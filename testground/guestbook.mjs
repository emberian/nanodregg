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
// enrolls is the kernel's to bound (the founder grant's enroll:N, its meter), not this file's; this file
// keeps a FLOOR of that count (ND_TESTGROUND_ENROLL_FLOOR, default 16): a `join` line is refused
// `enrollFloor` once its own fold's `enrollLeft` (tg_members) is at the floor, and the floor is spent
// only by a `reserve HEX` line, which the relay never sends (it forwards `join` only): the operator's,
// on the box, to enrol a member for a check after the public has used the rest. A member enrolled
// once needs no enrolment again (the page keeps its keys); the floor is for the World's operator.
//
// THE HOSTED RESIDENT (HOSTING-62). One line `resident HEX MODEL CAP WINDOW_MS PRICE` (the operator's,
// once, from `run.sh resident`; the relay never sends it) makes the World's inbox: it enrols the
// resident's join token HEX (`grant world … observe`), installs `world/grain/Lifecycle` and creates
// the resident grain (installed, never started: keybroker binds a socket for each resident grain the
// World holds), installs `world/hosting/Allowance` and creates the resident's allowance on MODEL (cap
// CAP micro-units per WINDOW_MS, PRICE micro-units per 1000 tokens, key slot 7, 300 tokens an ask),
// installs `world/resident/Bell` and creates the public Bell, its resident the resident's member,
// granted `observe,invoke:0` on it, and installs the document section's four texts (`world/doc`), so
// that a visitor creates a section without installing 80 KB of package. It keeps the ids in
// DIR/resident.json and adds `inbox` (the Bell, the resident's member and the section package) to
// world.json. From then on every `join` also grants the new member
// `invoke:3,invoke:4` on the Bell (ring, and withdraw its own ring) and answers that grant as `bellGrant`.
// This member is the allowance's OPERATOR: keybroker's decider reads only allowances it owns.
import { readFileSync, writeFileSync, existsSync, unlinkSync, chmodSync, renameSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
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
const FLOOR = +(process.env.ND_TESTGROUND_ENROLL_FLOOR ?? 16);
// the count this member's grant has left to enrol, read off its own fold (tg_members `enrollLeft`)
const enrollLeft = () => { const r = K.members(me.index); const m = new TextDecoder().decode(r.slice(1)).match(/^enrollLeft (\d+)$/m); return r[0] === okCode && m ? +m[1] : null; };

const s = await run(['sync']);
if (s.exit !== 'ok') process.exit(1);
const inv = await run(['invite', input]);
const invitation = (inv.stdout.match(/^invite ([0-9a-f]+)/m) || [])[1];
if (!invitation) process.exit(1);
// the hosted resident's ids, once `resident` made them
let inbox = existsSync(`${dir}/resident.json`) ? JSON.parse(readFileSync(`${dir}/resident.json`, 'utf8')) : null;
const writeWorld = () => {
  const w = { origin: lines.origin, invitation, sponsorKey: hex(K.pub(seeds[0])), sponsor: me.id };
  if (inbox) w.inbox = { bell: inbox.bell, resident: inbox.member, section: inbox.section };
  writeFileSync(`${dir}/world.json.tmp`, JSON.stringify(w) + '\n');
  renameSync(`${dir}/world.json.tmp`, `${dir}/world.json`);
};
writeWorld();
const text = (rel) => readFileSync(fileURLToPath(new URL(`./world/${rel}`, import.meta.url)), 'utf8');
// the inbox, made once (HOSTING-62): every act is this member's own nd command
const makeInbox = async (token, model, cap, windowMs, price) => {
  if (inbox) return { refused: 'exists' };
  const e = await run(['enroll', token]);
  const member = idOf(e);
  if (!member) return { refused: e.stderr.trim() || e.exit };
  const step = async (argv) => { const r = await run(argv); const id = idOf(r); if (!id) throw new Error(`${argv[0]}: ${r.stderr.trim() || r.exit}`); return id; };
  try {
    const grant = await step(['grant', 'world', member, 'observe', '--via', me.grant]);
    const life = await step(['install', text('grain/Lifecycle')]);
    const grain = await step(['create', '--pkg', life, '(record (entry "resident") (kind resident) (phase installed))']);
    const apkg = await step(['install', text('hosting/Allowance')]);
    const allowance = await step(['create', '--pkg', apkg,
      `(record (cap ${cap}) (keySlot 7) (maxTokens 300) (microPerKTok ${price}) (model "${model}") (resident #${grain}) (revoked false) (windowMs ${windowMs}))`]);
    const bpkg = await step(['install', text('resident/Bell')]);
    const bell = await step(['create', '--pkg', bpkg, `(record (open true) (resident #${member}))`]);
    const bellGrant = await step(['grant', bell, member, 'observe,invoke:0']);
    let section = null;
    for (const t of ['doc/Section.lib0', 'doc/Section.lib1', 'doc/Section.lib2', 'doc/Section']) section = await step(['install', text(t)]);
    inbox = { member, grant, grain, allowance, bell, bellGrant, model, section };
    writeFileSync(`${dir}/resident.json`, JSON.stringify(inbox) + '\n', { mode: 0o600 });
    writeWorld();
    return inbox;
  } catch (err) { return { refused: err.message }; }
};

let queue = Promise.resolve();
const enroll = async (token, reserve = false) => {
  const left = enrollLeft();
  if (!reserve && left !== null && left <= FLOOR) return { refused: 'enrollFloor', left };
  const e = await run(['enroll', token]);
  const member = idOf(e);
  if (!member) return { refused: e.stderr.trim() || e.exit };
  const g = await run(['grant', 'world', member, 'observe', '--via', me.grant]);
  const grant = idOf(g);
  if (!grant) return { refused: g.stderr.trim() || g.exit };
  if (!inbox) return { member, grant };
  // the inbox: ring the public Bell (4) and withdraw its own ring (3)
  const b = await run(['grant', inbox.bell, member, 'invoke:3,invoke:4']);
  const bellGrant = idOf(b);
  return bellGrant ? { member, grant, bellGrant } : { refused: b.stderr.trim() || b.exit };
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
    const r = buf.slice(0, nl).match(/^resident ([0-9a-f]{1,400}) (claude-[a-z0-9.-]{1,60}) ([1-9][0-9]{0,15}) ([1-9][0-9]{0,12}) ([1-9][0-9]{0,9})$/);
    if (r) {
      queue = queue.then(async () => c.end(JSON.stringify(await makeInbox(r[1], r[2], r[3], r[4], r[5])) + '\n')).catch(() => c.end('{"refused":"guestbook"}\n'));
      return;
    }
    const m = buf.slice(0, nl).match(/^(join|reserve) ([0-9a-f]{1,400})$/);
    if (!m) return c.end('{"refused":"usage"}\n');
    queue = queue.then(async () => c.end(JSON.stringify(await enroll(m[2], m[1] === 'reserve')) + '\n')).catch(() => c.end('{"refused":"guestbook"}\n'));
  });
  c.on('error', () => {});
}).listen(sock, () => { chmodSync(sock, 0o660); console.error(`guestbook: member ${me.id}, serving ${sock}`); });
for (const sig of ['SIGTERM', 'SIGINT']) process.on(sig, () => { try { unlinkSync(`${dir}/guestbook.pid`); } catch {} process.exit(0); });
