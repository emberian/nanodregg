// transport.js — a hosted World's writer, reached over a byte stream: the WebSocket relay in a tab
// (deploy/testground/ws-relay.py: bytes only, onto the supervisor's host.sock) or the socket itself
// under node. The frames are host.sock's own (client/src/frame.rs): `u32le len ‖ op ‖ version ‖ payload`
// out (the version is the kernel's `table.wireVersion`, PROTOCOL-87: a writer at another wire answers
// `refused wireVersion N expected M`), `u32le len ‖ status ‖ payload` back; one request in flight per connection, as nd sends them. This
// file decides nothing, and it invents no reply: a writer it cannot reach, or a connection that drops
// before the reply, is a TransportError the caller sees, as nd's `RunError::Host` (client/src/run.rs):
// at a follow step the command ends `client` naming it; in the attempt loop it is a lost reply. (A
// `closed` reply fabricated here was handed to follow as the writer's word, and follow named it
// `badResult` on every command of a tab whose runtime had no WebSocket: TENANT, 10-27.)
export class TransportError extends Error {}
const u32 = (n) => { const o = new Uint8Array(4); new DataView(o.buffer).setUint32(0, n, true); return o; };

/** A transport over a duplex that delivers byte chunks: `open(onData, onClose)` → `{ send, close }`;
 * `wire` is the kernel's version (`table.wireVersion`, hex), sent after every request's op. */
export function framed(open, { frameMax, wire }) {
  if (!/^[0-9a-f]{8}$/.test(wire ?? '')) throw new TransportError(`no wire version: ${wire}`);
  const version = Uint8Array.from(wire.match(/../g).map((h) => parseInt(h, 16)));
  let conn = null, buf = new Uint8Array(0), waiting = null, chain = Promise.resolve();
  const lost = (why) => new TransportError(why);
  const onData = (chunk) => {
    const b = new Uint8Array(buf.length + chunk.length); b.set(buf); b.set(chunk, buf.length); buf = b;
    if (buf.length < 4) return;
    const n = new DataView(buf.buffer, buf.byteOffset).getUint32(0, true);
    if (n > frameMax + 1) { conn?.close(); return; }
    if (buf.length < 4 + n) return;
    const reply = buf.slice(4, 4 + n); buf = buf.slice(4 + n);
    const w = waiting; waiting = null; w?.resolve(reply);
  };
  const onClose = () => { conn = null; buf = new Uint8Array(0); const w = waiting; waiting = null; w?.reject(lost('the writer closed the connection before its reply')); };
  async function ask(op, payload) {
    if (!conn) { try { conn = await open(onData, onClose); } catch (e) { throw lost(`unreachable: ${e.message}`); } }
    return new Promise((resolve, reject) => {
      waiting = { resolve, reject };
      const f = new Uint8Array(4 + 1 + version.length + payload.length);
      f.set(u32(1 + version.length + payload.length)); f[4] = op; f.set(version, 5); f.set(payload, 5 + version.length);
      try { conn.send(f); } catch { onClose(); }
    });
  }
  // one request at a time, in order
  const host = (op, payload) => { const p = chain.then(() => ask(op, payload)); chain = p.catch(() => {}); return p; };
  host.close = () => conn?.close();
  return host;
}

/** A WebSocket (a browser's, or node's global one) as a duplex. */
export const wsOpen = (url) => (onData, onClose) => new Promise((resolve, reject) => {
  if (typeof WebSocket === 'undefined') throw new Error('this runtime has no WebSocket (node 20: run with --experimental-websocket; node 22+ has it)');
  const ws = new WebSocket(url); ws.binaryType = 'arraybuffer';
  ws.onmessage = (e) => onData(new Uint8Array(e.data));
  ws.onclose = () => onClose();
  ws.onerror = () => reject(new Error(`cannot reach ${url}`));
  ws.onopen = () => resolve({ send: (b) => ws.send(b), close: () => ws.close() });
});

/** A Unix socket under node (the guest-book on the writer's box) as a duplex. */
export const unixOpen = (net, path) => (onData, onClose) => new Promise((resolve, reject) => {
  const s = net.connect(path);
  s.on('data', (d) => onData(new Uint8Array(d.buffer, d.byteOffset, d.length)));
  s.on('close', () => onClose());
  s.once('error', reject);
  s.once('connect', () => resolve({ send: (b) => s.write(b), close: () => s.destroy() }));
});
