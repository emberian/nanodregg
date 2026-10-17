#!/usr/bin/env python3
"""deploy/live/feed.py SOCKET CALLDIR FROM TO — send calls FROM..TO-1 (live-calls payloads) to a
unit's client socket, one at a time, and print each reply's status byte.

A client frame is `u32le len ‖ op ‖ payload` with len counting the op byte (client/src/frame.rs);
a reply is `u32le len ‖ status ‖ payload`. Each reply has a deadline; a closed socket or a missed
deadline is printed by name and ends the feed with exit 1. Decides nothing: the harness judges.
"""
import os
import socket
import struct
import sys

REPLY_SECONDS = 30


def read_exact(s, n):
    buf = b""
    while len(buf) < n:
        chunk = s.recv(n - len(buf))
        if not chunk:
            raise EOFError("closed")
        buf += chunk
    return buf


def main():
    if len(sys.argv) != 5:
        print("usage: feed.py SOCKET CALLDIR FROM TO", file=sys.stderr)
        return 2
    sock, calls, lo, hi = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    with open(os.path.join(calls, "op")) as f:
        op = int(f.read().strip())
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(REPLY_SECONDS)
    s.connect(sock)
    for i in range(lo, hi):
        with open(os.path.join(calls, "call-%03d.bin" % i), "rb") as f:
            payload = f.read()
        s.sendall(struct.pack("<I", 1 + len(payload)) + bytes([op]) + payload)
        try:
            (n,) = struct.unpack("<I", read_exact(s, 4))
            body = read_exact(s, n)
        except (EOFError, socket.timeout, ConnectionError) as e:
            print("reply %d none (%s)" % (i, type(e).__name__ if not isinstance(e, EOFError) else "closed"))
            return 1
        print("reply %d status=%d bytes=%d" % (i, body[0], len(body) - 1))
    s.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
