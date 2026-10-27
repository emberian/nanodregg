#!/usr/bin/env bash
# deploy/testground/run.sh — the testground's hosted World (DESIGN-TESTGROUND §3.2), by hand, every
# process with a PID file. The systemd units beside this file run the same three commands.
#
#   run.sh genesis STATE      seeds for the guest-book (founder 0), `host genesis`, its inputs kept
#   run.sh start   STATE      host serve under nd-supervise, the guest-book, the relay (127.0.0.1:PORT)
#   run.sh serve   STATE      the same three in the FOREGROUND, for a service manager (systemd
#                             Type=simple): it waits; when any of the three exits it stops the other
#                             two by their PIDs and exits non-zero (Restart= restarts); SIGTERM stops all
#   run.sh stop    STATE      each process by its PID file, and nothing else
#   run.sh fork    STATE FORK a SECOND writer of STATE's genesis in FORK: the same label, nonce and
#                             founder (the guest-book's seeds), so the same origin; start it with
#                             PORT=… run.sh start FORK. Two writers of one genesis are a fork; a
#                             member of one checks the other's guest-book attestation and is refused
#                             forkedWorld by name (PROTOCOL-74).
#
# Environment: ND_BIN (host, nd-supervise; default the tree's build outputs), TG (the testground
# directory holding kernel.{mjs,wasm} from build.sh, nd.js, transport.js, guestbook.mjs),
# PORT (8787). The relay listens on 127.0.0.1 only: putting it on the internet (TLS, a proxy, a
# tunnel) is the operator's act. STATE holds the Store, the guest-book's seeds (0600) and sockets.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
cmd=${1:?usage: run.sh genesis|start|stop STATE}; st=$(mkdir -p "${2:?STATE}" && cd "$2" && pwd)
HOST=${ND_HOST:-$root/.lake/build/bin/host}; SUP=${ND_SUPERVISE:-$root/target/release/nd-supervise}
TG=${TG:-$root/testground}; PORT=${PORT:-8787}
mkdir -p "$st/gb" "$st/run"; chmod 700 "$st/gb"

# the three processes, each in the background with its PID file (start's and serve's)
launch() {
  # hidden from the writer: the guest-book's seeds and every home (CLIENT-8 refuses a child with nothing
  # hidden). nd-supervise links itself to its parent's death (CLIENT-38), so its parent is a shell
  # that waits for it (the PID file's): stopping that shell stops the supervisor, which stops host.
  nohup bash -c '"$0" "$@"; exit $?' "$SUP" "$st/run/host.sock" --hide "$st/gb" --hide /home --write "$st/store" \
    --exec "$HOST" -- "$HOST" serve "$st/store" > "$st/run/host.log" 2>&1 < /dev/null & echo $! > "$st/run/host.pid"
  for _ in $(seq 50); do [ -S "$st/run/host.sock" ] && break; sleep 0.1; done
  nohup node "$TG/guestbook.mjs" serve "$st/gb" "$st/run/host.sock" > "$st/run/guestbook.log" 2>&1 < /dev/null &
  echo $! > "$st/run/guestbook.pid"
  for _ in $(seq 300); do [ -S "$st/gb/guestbook.sock" ] && break; sleep 0.1; done
  nohup python3 "$here/ws-relay.py" --listen "127.0.0.1:$PORT" --host-sock "$st/run/host.sock" \
    --world "$st/gb/world.json" --guestbook "$st/gb/guestbook.sock" > "$st/run/relay.log" 2>&1 < /dev/null &
  echo $! > "$st/run/relay.pid"
}
stop_all() {
  for p in relay guestbook host; do
    f=$st/run/$p.pid; [ -f "$f" ] || continue
    kill "$(cat "$f")" 2>/dev/null && echo "stopped $p ($(cat "$f"))"; rm -f "$f"
  done
}

case $cmd in
genesis)
  [ -e "$st/store" ] && { echo "store: exists" >&2; exit 17; }
  read -r _ key _ next < <(node "$TG/guestbook.mjs" init "$st/gb")
  "$HOST" genesis "$st/store" testground "$key" "$next" | tee "$st/genesis.txt"
  grep '^input ' "$st/genesis.txt" > "$st/gb/input" ;;
start)
  [ -e "$st/run/host.pid" ] && kill -0 "$(cat "$st/run/host.pid")" 2>/dev/null && { echo "host: running" >&2; exit 1; }
  launch
  echo "hosted World: relay ws://127.0.0.1:$PORT/ws (PIDs in $st/run/*.pid)" ;;
serve)
  [ -e "$st/run/host.pid" ] && kill -0 "$(cat "$st/run/host.pid")" 2>/dev/null && { echo "host: running" >&2; exit 1; }
  launch
  trap 'stop_all; exit 0' TERM INT
  echo "hosted World: relay ws://127.0.0.1:$PORT/ws (serving in the foreground; PIDs in $st/run/*.pid)"
  rc=0; wait -n "$(cat "$st/run/host.pid")" "$(cat "$st/run/guestbook.pid")" "$(cat "$st/run/relay.pid")" || rc=$?
  echo "a process of the hosted World exited ($rc): stopping the others" >&2
  stop_all >&2; exit $(( rc == 0 ? 1 : rc )) ;;
fork)
  fk=$(mkdir -p "${3:?FORK}" && cd "$3" && pwd)
  [ -e "$fk/store" ] && { echo "fork store: exists" >&2; exit 17; }
  mkdir -p "$fk/gb" "$fk/run"; chmod 700 "$fk/gb"; cp -p "$st/gb/seeds" "$fk/gb/seeds"
  read -r _ key _ next < <(node "$TG/guestbook.mjs" keys "$fk/gb")
  "$HOST" genesis "$fk/store" testground --nonce "$(sed -n 's/^nonce //p' "$st/genesis.txt")" "$key" "$next" | tee "$fk/genesis.txt"
  grep '^input ' "$fk/genesis.txt" > "$fk/gb/input"
  cmp -s "$fk/gb/input" "$st/gb/input" || { echo "fork: the genesis input differs from STATE's" >&2; exit 1; } ;;
stop)
  stop_all ;;
*) echo "usage: run.sh genesis|start|serve|stop STATE | fork STATE FORK" >&2; exit 2 ;;
esac
