// transport.js — a hosted World's writer, reached over a byte stream: the WebSocket relay in a tab
// (deploy/testground/ws-relay.py: bytes only, onto the supervisor's host.sock) or the socket itself
// under node. The frames are host.sock's own (client/src/frame.rs): `u32le len ‖ op ‖ payload` out,
// `u32le len ‖ status ‖ payload` back; one request in flight per connection, as nd sends them. This
// file decides nothing: a closed connection is answered as the mux answers it, `closed ‖ reason`,
// and the attempt loop (Protocol.Attempt.next) decides what that means.
const u32 = (n) => { const o = new Uint8Array(4); new DataView(o.buffer).setUint32(0, n, true); return o; };

/** A transport over a duplex that delivers byte chunks: `open(onData, onClose)` → `{ send, close }`. */
export function framed(open, { closedStatus, frameMax }) {
  let conn = null, buf = new Uint8Array(0), waiting = null, chain = Promise.resolve();
  const closed = (why) => Uint8Array.of(closedStatus, ...new TextEncoder().encode(why));
  const onData = (chunk) => {
    const b = new Uint8Array(buf.length + chunk.length); b.set(buf); b.set(chunk, buf.length); buf = b;
    if (buf.length < 4) return;
    const n = new DataView(buf.buffer, buf.byteOffset).getUint32(0, true);
    if (n > frameMax + 1) { conn?.close(); return; }
    if (buf.length < 4 + n) return;
    const reply = buf.slice(4, 4 + n); buf = buf.slice(4 + n);
    const w = waiting; waiting = null; w?.(reply);
  };
  const onClose = () => { conn = null; buf = new Uint8Array(0); const w = waiting; waiting = null; w?.(closed('unreachable')); };
  async function ask(op, payload) {
    if (!conn) { try { conn = await open(onData, onClose); } catch { return closed('unreachable'); } }
    return new Promise((resolve) => {
      waiting = resolve;
      const f = new Uint8Array(4 + 1 + payload.length);
      f.set(u32(1 + payload.length)); f[4] = op; f.set(payload, 5);
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
