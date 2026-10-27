#!/usr/bin/env python3
"""ws-relay.py — the testground's hosted World on the network: WebSocket <-> host.sock, bytes only.

    ws-relay.py --listen 127.0.0.1:8787 --host-sock /run/nd-testground/host.sock \
                --world /srv/nd-testground/guestbook/world.json \
                --guestbook /srv/nd-testground/guestbook/guestbook.sock [--max-conns 64]

Each WebSocket connection is one connection to the supervisor's host.sock (nd-supervise: its mux
bounds connections, idles, deadlines and names every close): binary messages from the tab are
written to the socket as they are, and whatever the socket answers is sent back as binary
messages. The relay parses no frame and no op: the tab speaks host.sock's own frames
(testground/transport.js) and the writer refuses what it does not serve. A member's follow runs in
the tab, so nothing this relay passes is trusted by anyone: a lie here is caught there by name.

Besides the socket: `GET /world.json` (the guest-book's invitation and its sponsor key; the
testground's trust caveat is that whoever serves this file and the page chooses both, DESIGN-
TESTGROUND §7) and `POST /enroll` (a join token, one line to the guest-book's socket, its one-line
JSON answer back). Python's standard library only. Listens where it is told; exposing it to the
internet (TLS, a reverse proxy) is the operator's act, not this file's.
"""
import argparse, asyncio, base64, hashlib, os, signal, struct, sys

GUID = b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
MSG_MAX = 1 << 21          # a tab's message: one host.sock frame at most (frameBytesMax + header)
HEAD_MAX = 8192
ENROLL_MAX = 512

def http(status, body=b"", ctype=b"text/plain; charset=utf-8"):
    return (b"HTTP/1.1 " + status + b"\r\nContent-Type: " + ctype + b"\r\nContent-Length: " +
            str(len(body)).encode() + b"\r\nAccess-Control-Allow-Origin: *\r\n"
            b"Access-Control-Allow-Headers: content-type\r\nConnection: close\r\n\r\n" + body)

async def read_frame(r):
    """One WebSocket frame from the tab: (fin, opcode, payload). Client frames are masked."""
    b0, b1 = await r.readexactly(2)
    n = b1 & 0x7F
    if n == 126: n = struct.unpack(">H", await r.readexactly(2))[0]
    elif n == 127: n = struct.unpack(">Q", await r.readexactly(8))[0]
    if not b1 & 0x80 or n > MSG_MAX: raise ValueError("unmasked or oversized frame")
    mask = await r.readexactly(4)
    p = await r.readexactly(n)
    m = (mask * (n // 4 + 1))[:n]
    return bool(b0 & 0x80), b0 & 0x0F, (int.from_bytes(p, "big") ^ int.from_bytes(m, "big")).to_bytes(n, "big")

def frame(opcode, payload):
    n = len(payload)
    head = bytes([0x80 | opcode])
    if n < 126: head += bytes([n])
    elif n < 1 << 16: head += bytes([126]) + struct.pack(">H", n)
    else: head += bytes([127]) + struct.pack(">Q", n)
    return head + payload

class Relay:
    def __init__(self, a):
        self.a, self.live = a, 0

    async def handle(self, r, w):
        try:
            head = await r.readuntil(b"\r\n\r\n")
        except Exception:
            w.close(); return
        if len(head) > HEAD_MAX: w.close(); return
        lines = head.decode("latin-1").split("\r\n")
        method, path = (lines[0].split(" ") + ["", ""])[:2]
        hdr = {l.split(":", 1)[0].strip().lower(): l.split(":", 1)[1].strip() for l in lines[1:] if ":" in l}
        try:
            if method == "GET" and path == "/ws" and hdr.get("upgrade", "").lower() == "websocket":
                await self.ws(r, w, hdr)
            elif method == "GET" and path == "/world.json":
                try: body = open(self.a.world, "rb").read()
                except OSError: w.write(http(b"404 Not Found", b"no world yet\n"))
                else: w.write(http(b"200 OK", body, b"application/json"))
            elif method == "POST" and path == "/enroll":
                n = int(hdr.get("content-length", "0"))
                if n > ENROLL_MAX: w.write(http(b"413 Payload Too Large"))
                else: w.write(http(b"200 OK", await self.enroll(await r.readexactly(n)), b"application/json"))
            elif method == "OPTIONS":
                w.write(http(b"204 No Content"))
            else:
                w.write(http(b"404 Not Found"))
            await w.drain()
        except Exception as e:
            print(f"relay: {path}: {e!r}", file=sys.stderr)
        finally:
            w.close()

    async def enroll(self, token):
        """One join token to the guest-book's socket; its one-line answer back."""
        tok = token.strip()
        if not tok or any(c not in b"0123456789abcdef" for c in tok):
            return b'{"refused":"badToken"}'
        try:
            gr, gw = await asyncio.open_unix_connection(self.a.guestbook)
            gw.write(b"join " + tok + b"\n"); await gw.drain()
            line = await asyncio.wait_for(gr.readline(), 120)
            gw.close()
            return line.strip() or b'{"refused":"guestbookSilent"}'
        except Exception as e:
            return b'{"refused":"guestbookUnreachable"}'

    async def ws(self, r, w, hdr):
        if self.live >= self.a.max_conns:
            w.write(http(b"503 Service Unavailable", b"full\n")); return
        key = hdr.get("sec-websocket-key", "").encode()
        acc = base64.b64encode(hashlib.sha1(key + GUID).digest())
        w.write(b"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                b"Sec-WebSocket-Accept: " + acc + b"\r\n\r\n")
        await w.drain()
        self.live += 1
        try:
            hr, hw = await asyncio.open_unix_connection(self.a.host_sock)
        except OSError:
            self.live -= 1
            w.write(frame(8, struct.pack(">H", 1011) + b"host.sock unreachable")); return
        async def up():                     # tab -> host.sock
            msg = b""
            while True:
                fin, op, p = await read_frame(r)
                if op == 8: return
                if op == 9: w.write(frame(10, p)); continue
                if op in (0, 2): msg += p
                if len(msg) > MSG_MAX: return
                if fin and op in (0, 2): hw.write(msg); await hw.drain(); msg = b""
        async def down():                   # host.sock -> tab
            while True:
                b = await hr.read(65536)
                if not b: return
                w.write(frame(2, b)); await w.drain()
        tasks = [asyncio.create_task(up()), asyncio.create_task(down())]
        try:
            await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
        finally:
            for t in tasks: t.cancel()
            hw.close(); self.live -= 1
            try: w.write(frame(8, struct.pack(">H", 1000))); await w.drain()
            except Exception: pass

async def main():
    p = argparse.ArgumentParser()
    p.add_argument("--listen", default="127.0.0.1:8787")
    p.add_argument("--host-sock", required=True)
    p.add_argument("--world", required=True)
    p.add_argument("--guestbook", required=True)
    p.add_argument("--max-conns", type=int, default=64)
    p.add_argument("--pid-file")
    a = p.parse_args()
    host, port = a.listen.rsplit(":", 1)
    if a.pid_file:
        with open(a.pid_file, "w") as f: f.write(f"{os.getpid()}\n")
    srv = await asyncio.start_server(Relay(a).handle, host, int(port), limit=HEAD_MAX)
    stop = asyncio.Event()
    for s in (signal.SIGTERM, signal.SIGINT): asyncio.get_running_loop().add_signal_handler(s, stop.set)
    print(f"relay: listening on {a.listen}, host.sock {a.host_sock}", file=sys.stderr)
    async with srv:
        await stop.wait()

if __name__ == "__main__":
    asyncio.run(main())
