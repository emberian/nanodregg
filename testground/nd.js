// nd.js — the member's side in a browser tab: framing, custody, the attempt store, nothing else.
//
// This is the part client/src/run.rs plays (and Protocol.Rows.Loopback plays in process): it
// performs the steps the member's own follow asks for and hands each result back with the
// continuation. It decides nothing. Every layout, op, status, step tag, bound and word it uses is
// read from the kernel's table (`tg_table`, Lean's Protocol.Table); every decision — what to sign,
// what to send, what a reply means, what the attempt store does next — is a Lean export.

const enc = new TextEncoder(), dec = new TextDecoder();
export const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
export const unhex = (s) => Uint8Array.from(s.match(/../g) || [], (h) => parseInt(h, 16));
const cat = (...bs) => { const n = bs.reduce((a, b) => a + b.length, 0); const o = new Uint8Array(n); let i = 0; for (const b of bs) { o.set(b, i); i += b.length; } return o; };
const u32 = (n) => { const o = new Uint8Array(4); new DataView(o.buffer).setUint32(0, n, true); return o; };

// ---- the kernel module: bytes in, bytes out ----
// `opts` reach emscripten's factory: the page hands `wasmBinary`, the bytes it fetched and hashed, so the
// module it shows the sha256 of is the module it runs
export async function loadKernel(factory, opts = {}) {
  const K = await factory(opts);
  if (K._w_init() !== 0) throw new Error('kernel init refused');
  const out = (n) => { if (n < 0) throw new Error('kernel IO error'); return K.HEAPU8.slice(K._w_out(), K._w_out() + n); };
  const put = (b) => { const p = K._malloc(b.length || 1); K.HEAPU8.set(b, p); return p; };
  const call = (f, ...args) => {
    const ptrs = []; const flat = [];
    for (const a of args) { if (a instanceof Uint8Array) { const p = put(a); ptrs.push(p); flat.push(p, a.length); } else flat.push(a); }
    try { return out(f(...flat)); } finally { ptrs.forEach((p) => K._free(p)); }
  };
  const table = JSON.parse(dec.decode(out(K._w_table())));
  const lies = JSON.parse(dec.decode(out(K._w_lies())));
  return {
    table, lies,
    // the lying writer (Web.Sim.Testground: the rows' own plants), a cold follow, a hostile client
    lie: (name) => call(K._w_lie, enc.encode(name)),
    lied: () => K._w_lied() === 1,
    cold: (i) => call(K._w_cold, i),
    forge: (i, argv, seed, next) => call(K._w_forge, i, argv, seed, next),
    text: (name) => call(K._w_text, enc.encode(name)),
    // a hosted World: follows here, the writer elsewhere
    found: (input, i) => call(K._w_found, input, i),
    join: (invitation, key) => call(K._w_join, invitation, key),
    self: (i, member, grant) => call(K._w_self, i, enc.encode(member), enc.encode(grant)),
    // the rows' relay around a hosted tab's socket: before it (an answer of its own, or forward) and after
    // the meter, read back from member i's own fold (World.ticksUsed)
    meter: (i) => call(K._w_meter, i),
    // the members of member i's World, read off its own fold (a hosted tab's roster)
    members: (i) => call(K._w_members, i),
    relayPre: (op) => call(K._w_relay_pre, op),
    relayPost: (op, p, r) => call(K._w_relay_post, op, p, r),
    genesis: (b) => call(K._w_genesis, b),
    host: (op, p) => call(K._w_host, op, p),
    follow: (i, op, p) => call(K._w_follow, i, op, p),
    pub: (seed) => call(K._w_pub, seed),
    sign: (seed, msg) => call(K._w_sign, seed, msg),
    attempt: (left, req, seen) => K._w_attempt(left, req, seen),
  };
}

// ---- the codec: a reader and a writer for any layout the table carries (Codec.Layout's bytes) ----
export class Refusal extends Error {}
export function codec(table) {
  const max = table.bounds.frameBytesMax;
  function write(layout, v, bound = max) {
    const parts = [];
    for (const f of layout) {
      const x = v[f.name];
      switch (f.kind) {
        case 'byte': case 'oneOf': parts.push(Uint8Array.of(x)); break;
        case 'u32': parts.push(u32(x)); break;
        case 'u64': { const o = new Uint8Array(8); new DataView(o.buffer).setBigUint64(0, BigInt(x), true); parts.push(o); break; }
        case 'bytes': case 'path': if (x.length > bound) throw new Refusal(`pastBound ${f.name}`); parts.push(u32(x.length), x); break;
        case 'list': case 'paths': if (x.length > bound) throw new Refusal(`pastBound ${f.name}`);
          parts.push(u32(x.length)); for (const e of x) { if (e.length > bound) throw new Refusal(`pastBound ${f.name}`); parts.push(u32(e.length), e); } break;
        default: throw new Refusal(`unknown field kind ${f.kind}`);
      }
    }
    return cat(...parts);
  }
  function read(layout, b, at = 0, bound = max) {
    const dv = new DataView(b.buffer, b.byteOffset, b.byteLength); let i = at; const v = {};
    const need = (n) => { if (i + n > b.length) throw new Refusal(`truncated at ${i}`); };
    const bytes = () => { need(4); const n = dv.getUint32(i, true); if (n > bound) throw new Refusal(`pastBound at ${i}`); i += 4; need(n); const s = b.slice(i, i + n); i += n; return s; };
    for (const f of layout) {
      switch (f.kind) {
        case 'byte': need(1); v[f.name] = b[i++]; break;
        case 'oneOf': { need(1); const t = b[i]; if (!f.cases.some((c) => c.code === t)) throw new Refusal(`badTag ${t} at ${i}`); i++; v[f.name] = t; break; }
        case 'u32': need(4); v[f.name] = dv.getUint32(i, true); i += 4; break;
        case 'u64': need(8); v[f.name] = dv.getBigUint64(i, true); i += 8; break;
        case 'bytes': case 'path': v[f.name] = bytes(); break;
        case 'list': case 'paths': { need(4); const n = dv.getUint32(i, true); if (n > bound) throw new Refusal(`pastBound at ${i}`); i += 4; v[f.name] = Array.from({ length: n }, bytes); break; }
        default: throw new Refusal(`unknown field kind ${f.kind}`);
      }
    }
    return [v, i];
  }
  const readAll = (layout, b, bound) => { const [v, i] = read(layout, b, 0, bound); if (i !== b.length) throw new Refusal(`trailing at ${i}`); return v; };
  const stepByCode = new Map(table.steps.map((s) => [s.code, s]));
  return {
    write, readAll,
    step(b) { const s = stepByCode.get(b[0]); if (!s) throw new Refusal(`badTag ${b[0]} at 0`); const [v, i] = read(s.layout, b, 1); if (i !== b.length) throw new Refusal(`trailing at ${i}`); return { tag: s.name, ...v }; },
  };
}

// ---- the table's names, by code and by name ----
export function names(table) {
  const by = (xs) => Object.fromEntries(xs.map((x) => [x.name, x.code]));
  const of = (xs) => Object.fromEntries(xs.map((x) => [x.code, x.name]));
  return { op: by(table.ops), opName: of(table.ops), status: by(table.statuses), statusName: of(table.statuses),
           exitName: of(table.commandExits), exit: by(table.commandExits), action: by(table.attemptActions), actionName: of(table.attemptActions) };
}

// ---- custody: a member's current, next and pending seeds, held by the page, never by follow ----
export function custody(K, seeds) {
  // seeds: [current, next, pending] 32-byte Uint8Arrays (fresh randomness each, never derived)
  return { seeds, pub: (i) => K.pub(seeds[i]), sign: (i, m) => K.sign(seeds[i], m) };
}

// ---- one command, run as nd runs it (client/src/run.rs): follow's steps until done ----
// `host` is the transport to the writer: the kernel's own writer in this tab (K.host) unless a
// hosted World's socket is given (transport.js: the same frames to a real `host serve`)
export function client(K, { onFrame = () => {}, beforeSubmit = null, host = null } = {}) {
  const C = codec(K.table), N = names(K.table), T = K.table;
  const ok = N.status.ok;
  const reply = (b) => ({ status: b[0], payload: b.slice(1) });
  const local = !host;
  // a hosted World's frames pass the tab's relay (the rows' relay lies, Web.Sim.Testground.relayPre/
  // relayPost) on their way to the socket and back, as the tab's own writer's do inside K.host
  const viaRelay = (send) => async (op, p) => {
    const pre = K.relayPre(op);
    if (pre[0] !== ok) return pre;            // no World in the kernel: its refusal is the reply
    if (pre.length > 1) return pre.slice(1);  // the relay answered the frame itself
    return K.relayPost(op, p, await send(op, p));
  };
  const toWriter = host ? viaRelay(host) : (async (op, p) => K.host(op, p));
  // a writer the transport cannot reach is the transport's error (transport.js TransportError, nd's
  // RunError::Host), never a reply: `null` here, and the caller ends the command or loses the reply
  const sendHost = async (who, op, p) => {
    let r;
    try { r = await toWriter(op, p); } catch (e) {
      onFrame({ who, to: local ? 'writer' : 'host', op: N.opName[op], bytes: p.length, status: 'unreachable', payload: new Uint8Array(0), lied: false });
      lostWhy = e.message; return null;
    }
    onFrame({ who, to: local ? 'writer' : 'host', op: N.opName[op], bytes: p.length, status: N.statusName[r[0]], payload: r.slice(1), lied: K.lied() });
    return r;
  };
  const sendFollow = (who, i, op, p) => { const r = K.follow(i, op, p); onFrame({ who, to: 'follow', op: N.opName[op], bytes: p.length, status: N.statusName[r[0]] }); return r; };
  let lostWhy = '';
  const signResult = (cu, keyI, nextI, msg) => cat(Uint8Array.of(ok), C.write(T.signResult, { key: cu.pub(keyI), next: cu.pub(nextI), signature: cu.sign(keyI, msg) }));

  function stepOf(b) {
    const r = reply(b);
    if (r.status !== ok) return { tag: 'refusedByFollow', name: dec.decode(r.payload) };
    return C.step(r.payload);
  }
  async function run(m, argv, depth = 0) {
    const argvB = argv.map((a) => (a instanceof Uint8Array ? a : enc.encode(a)));
    const first = sendFollow(m.name, m.index, N.op.command, C.write(T.command, { argv: argvB }, T.bounds.argvBytesMax));
    return steps(m, argv, stepOf(first), depth);
  }
  async function resume(m, k, result) {
    return stepOf(sendFollow(m.name, m.index, N.op.resume, C.write(T.resume, { k, result })));
  }
  async function steps(m, argv, st, depth) {
    for (let n = 0; n < T.bounds.stepsPerCommandMax; n++) {
      switch (st.tag) {
        case 'refusedByFollow': return { exit: 'refused', stdout: '', stderr: `refused ${st.name}\n` };
        case 'done': return { exit: N.exitName[st.exit] ?? `exit${st.exit}`, stdout: dec.decode(st.stdout), stderr: dec.decode(st.stderr) };
        case 'sign': st = await resume(m, st.k, signResult(m.custody, 0, 1, st.message)); break;
        case 'precommit': st = await resume(m, st.k, cat(Uint8Array.of(ok), C.write(T.precommitResult, { next: m.custody.pub(1), pending: m.custody.pub(2) }))); break;
        case 'signNext': m.arming = true; st = await resume(m, st.k, signResult(m.custody, 1, 2, st.message)); break;
        case 'signIncoming': st = await resume(m, st.k, signResult(m.custody, 1, 2, st.message)); break;
        case 'host': {
          const r = await sendHost(m.name, st.op, st.payload);
          if (!r) return { exit: 'client', stdout: '', stderr: `host: ${lostWhy}\n` };
          st = await resume(m, st.k, r); break;
        }
        case 'submit': {
          m.last = st.call;   // the attempt store's frozen bytes: what `cancel CALL` names
          if (beforeSubmit) await beforeSubmit(m, argv, st.call);
          st = await resume(m, st.k, await drive(m, st.call, depth));
          break;
        }
        default: return { exit: 'client', stdout: '', stderr: `unknown step ${st.tag}\n` };
      }
    }
    return { exit: 'client', stdout: '', stderr: 'stepsPerCommandMax\n' };
  }
  // the attempt store (CLIENT-3): Protocol.Attempt.next decides every request; the page only sends
  async function drive(m, call, depth) {
    const req = (w) => T.attemptRequests.indexOf(w), seenI = (w) => T.attemptSeen.indexOf(w);
    const statusSeen = { ok: 'committed', refused: 'refused', declined: 'declined', uncertain: 'unknown', absent: 'absent' };
    let sends = 0, last = [255, 0], hostReply = null, hostSeen = 'lost', said = '';
    for (let fuel = 3 * T.bounds.sendsMax + 3; fuel > 0; fuel--) {
      const a = N.actionName[K.attempt(sends < T.bounds.sendsMax ? 1 : 0, last[0], last[1])];
      const ended = (payload) => cat(Uint8Array.of(N.action[a]), enc.encode(payload));
      switch (a) {
        case 'submit': case 'lookup': {
          const r = await sendHost(m.name, a === 'submit' ? N.op.submit : N.op.lookup, call);
          if (a === 'submit') sends++;
          hostReply = r ?? new Uint8Array(1); hostSeen = r ? statusSeen[N.statusName[r[0]]] ?? 'lost' : 'lost';
          last = [req(a), seenI(hostSeen)]; break;
        }
        case 'confirm': case 'probe': {
          const o = depth < 2 ? await run(m, ['receipt', hex(call)], depth + 1) : null;
          const seen = o && o.exit === 'ok' ? settleOf(o.stdout) : null;
          if (seen) { said = seen.text; last = [req(a), seenI(seen.seen)]; } else last = [req(a), seenI('lost')];
          break;
        }
        case 'committed': case 'refused': case 'open': case 'badReply': return ended(a === 'committed' || a === 'refused' ? said : '');
        case 'declined': return ended(dec.decode(hostReply.slice(1)));
        case 'contradicted': return ended(`${hostSeen} ${T.attemptSeen[last[1]]}`);
        case 'uncertain': return ended('');
        default: return ended('');
      }
    }
    return cat(Uint8Array.of(N.action.uncertain));
  }
  function settleOf(out) {
    const [rw, hw, sw] = T.receiptWords;
    const lines = out.replace(/\n$/, '').split('\n');
    if (lines.length !== 3 || !lines[0].startsWith(rw + ' ') || !lines[1].startsWith(hw + ' ') || !lines[2].startsWith(sw + ' ')) return null;
    const text = lines[2].slice(sw.length + 1);
    const hit = T.settleSeen.find(([w]) => w === text.split(' ')[0]);
    return hit ? { seen: hit[1], text } : null;
  }
  // a hostile client (Protocol.Rows.Loopback.forgedCall in the kernel): the argv planned on the
  // member's World WITHOUT its follow's admission, signed with its own seed, sent once; the writer's
  // word is the outcome
  async function forge(m, argv) {
    const argvB = argv.map((a) => (a instanceof Uint8Array ? a : enc.encode(a)));
    const r = K.forge(m.index, C.write(T.command, { argv: argvB }, T.bounds.argvBytesMax), m.custody.seeds[0], m.custody.seeds[1]);
    if (r[0] !== ok) return { exit: 'refused', stdout: '', stderr: `refused ${dec.decode(r.slice(1))}\n` };
    m.last = r.slice(1);
    const h = await sendHost(m.name, N.op.submit, m.last);
    if (!h) return { exit: 'client', stdout: '', stderr: `host: ${lostWhy}\n`, forged: true };
    const said = N.statusName[h[0]];
    return { exit: said === 'ok' ? 'ok' : said, stdout: '', stderr: said === 'ok' ? '' : `${said} ${dec.decode(h.slice(1))}\n`, forged: true };
  }
  return { run, forge };
}

// ---- a World in the tab: genesis with fresh founders ----
export function rand32() { const b = new Uint8Array(32); crypto.getRandomValues(b); return b; }
export function genesis(K, name, founderNames) {
  const C = codec(K.table);
  const members = founderNames.map((n, index) => ({ name: n, index, custody: custody(K, [rand32(), rand32(), rand32()]) }));
  const argv = [enc.encode(name), rand32(), ...members.flatMap((m) => [m.custody.pub(0), m.custody.pub(1)])];
  const r = K.genesis(C.write(K.table.command, { argv }, K.table.bounds.argvBytesMax));
  const text = dec.decode(r.slice(1));
  if (r[0] !== names(K.table).status.ok) throw new Error(text);
  for (const line of text.split('\n')) {
    const w = line.split(' ');
    if (w[0] === 'founder') { const m = members[+w[1]]; m.id = w[3]; m.grant = w[5]; }
  }
  return { text, members };
}
