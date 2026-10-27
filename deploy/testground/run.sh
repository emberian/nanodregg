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
#
# The hosted RESIDENT (HOSTING-62): an agent answering the World's public Bell with a model's words.
#   run.sh resident STATE     once, with the World up: the resident's member (its custody, its follow
#                             Store joined from the invitation), and through the guest-book the
#                             World's inbox: the resident grain, its allowance, the public Bell
#   run.sh keys STATE         keybroker in the FOREGROUND: the provider key's holder, the only process
#                             of the World that reaches the network (KEYDIR/provider.key, the
#                             operator's; anchors and pins from this tree). Its decider reads STATE's Store
#   run.sh resident-serve STATE  the resident in the FOREGROUND: its follower, its member (`nd --stdio`)
#                             and the resident itself, each under nd-supervise; ends when one does
#   run.sh fork    STATE FORK a SECOND writer of STATE's genesis in FORK: the same label, nonce and
#                             founder (the guest-book's seeds), so the same origin; start it with
#                             PORT=… run.sh start FORK. Two writers of one genesis are a fork; a
#                             member of one checks the other's guest-book attestation and is refused
#                             forkedWorld by name (PROTOCOL-74).
#
# Environment: ND_HOST, ND_SUPERVISE, ND_ND, ND_KEYBROKER, ND_DECIDER, ND_RESIDENT (the programs;
# default the tree's build outputs), TG (the testground directory holding kernel.{mjs,wasm} from
# build.sh, nd.js, transport.js, guestbook.mjs), PORT (8787); for the resident ND_KEYDIR (default
# STATE/keys: anchors, pins, the decider's PID file) and ND_KEYS (the key file, default
# KEYDIR/provider.key), ND_UPSTREAM (keybroker's dial address, default api.anthropic.com:443), ND_TLS (the
# anchors.pem and pins to install, default the tree's deploy/tls), and the allowance's ND_MODEL,
# ND_CAP, ND_WINDOW_MS, ND_PRICE (README "The resident"). The relay listens on 127.0.0.1 only: putting it on the internet (TLS, a proxy, a
# tunnel) is the operator's act. STATE holds the Store, the guest-book's seeds (0600) and sockets.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
cmd=${1:?usage: run.sh genesis|start|stop STATE}; st=$(mkdir -p "${2:?STATE}" && cd "$2" && pwd)
HOST=${ND_HOST:-$root/.lake/build/bin/host}; SUP=${ND_SUPERVISE:-$root/target/release/nd-supervise}
TG=${TG:-$root/testground}; PORT=${PORT:-8787}
ND=${ND_ND:-$root/target/release/nd}; KB=${ND_KEYBROKER:-$root/target/release/keybroker}
DECIDER=${ND_DECIDER:-$root/.lake/build/bin/hosting-broker}; RES=${ND_RESIDENT:-$root/.lake/build/bin/resident}
KEYDIR=${ND_KEYDIR:-$st/keys}; KEYS=${ND_KEYS:-$KEYDIR/provider.key}; TLS=${ND_TLS:-$root/deploy/tls}
# the resident's places: its own state, the hosted tree its plan names (label `testground`, the
# genesis label), keybroker's socket directory and the member socket root
R=$st/resident; HROOT=$st/hosted; KBDIR=$st/kb; MROOT=$st/rm
jsonget() { python3 -c 'import json,sys; v=json.load(open(sys.argv[1])); [v:=v[k] for k in sys.argv[2:]]; print(v)' "$@"; }
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
resident)
  [ -S "$st/gb/guestbook.sock" ] && [ -S "$st/run/host.sock" ] || { echo "resident: the World is not up (start it first)" >&2; exit 1; }
  [ -e "$st/gb/resident.json" ] && { echo "resident: exists ($st/gb/resident.json)" >&2; exit 17; }
  rm -rf "$R"; mkdir -p "$R/ws" "$R/holding" "$R/run"; chmod 700 "$R" "$R/ws" "$R/holding"
  # its follow Store, joined from the guest-book's invitation under the sponsor key (PROTOCOL-42)
  "$HOST" join "$R/store" "$(jsonget "$st/gb/world.json" invitation)" "$(jsonget "$st/gb/world.json" sponsorKey)" > "$R/join.txt"
  # a follower with no member yet, for `init` alone; stopped by its PID file
  nohup "$SUP" "$R/run/follow.sock" --hide "$st/gb" --hide /home --write "$R/store" --exec "$HOST" -- \
    "$HOST" follow "$R/store" "$(printf '0%.0s' $(seq 64))" "$(printf '0%.0s' $(seq 64))" > "$R/run/init-follow.log" 2>&1 < /dev/null &
  echo $! > "$R/run/init-follow.pid"
  for _ in $(seq 100); do [ -S "$R/run/follow.sock" ] && break; sleep 0.1; done
  export ND_WORKSPACE=$R/ws ND_HOLDING=$R/holding ND_FOLLOW_SOCK=$R/run/follow.sock ND_HOST_SOCK=$st/run/host.sock
  "$ND" --init-hosted > /dev/null
  token=$("$ND" init "$(jsonget "$st/gb/world.json" sponsor)" | sed -n 's/^join //p')
  kill "$(cat "$R/run/init-follow.pid")"; rm -f "$R/run/init-follow.pid" "$R/run/follow.sock"
  [ -n "$token" ] || { echo "resident: nd init gave no join token" >&2; exit 1; }
  # the inbox, by the guest-book: the resident's member, grain, allowance and the public Bell
  ans=$(printf 'resident %s %s %s %s %s\n' "$token" "${ND_MODEL:-claude-haiku-5-5}" "${ND_CAP:-25000}" \
    "${ND_WINDOW_MS:-300000}" "${ND_PRICE:-500}" | python3 -c '
import socket, sys
s = socket.socket(socket.AF_UNIX); s.connect(sys.argv[1]); s.sendall(sys.stdin.buffer.read())
print(s.makefile("rb").readline().decode().strip())' "$st/gb/guestbook.sock")
  python3 -c 'import json,sys; j=json.loads(sys.argv[1]); sys.exit(0 if "bell" in j else 1)' "$ans" || { echo "resident: refused $ans" >&2; exit 1; }
  printf '%s %s\n' "$(jsonget "$st/gb/resident.json" member)" "$(jsonget "$st/gb/resident.json" grant)" > "$R/follow"
  g=$(jsonget "$st/gb/resident.json" grain); P=$HROOT/worlds/testground/grains/$g
  mkdir -p "$P/pkg" "$P/vol" "$HROOT/worlds/testground/store"
  printf '(record (bell #%s) (grant #%s) (maxTokens 300) (model "%s") (system "%s"))\n' \
    "$(jsonget "$st/gb/resident.json" bell)" "$(jsonget "$st/gb/resident.json" bellGrant)" "${ND_MODEL:-claude-haiku-5-5}" \
    "${ND_SYSTEM:-Answer in one or two plain sentences. The question comes from a visitor of a public demo page.}" > "$P/pkg/resident.conf"
  chmod 600 "$R/follow"
  echo "$ans" ;;
keys)
  [ -s "$KEYS" ] || { echo "keys: no $KEYS (the operator's; README: The resident)" >&2; exit 78; }
  [ -e "$st/gb/resident.json" ] || { echo "keys: no inbox yet (run.sh resident)" >&2; exit 78; }
  mkdir -p -m 0700 "$KEYDIR"
  install -m 0644 "$TLS/anchors.pem" "$KEYDIR/anchors.pem"           # the build's, each start
  [ -e "$KEYDIR/pins" ] || install -m 0644 "$TLS/pins" "$KEYDIR/pins"   # the operator may re-pin
  mkdir -p -m 0700 "$KEYDIR/run"; mkdir -p "$KBDIR"; chmod 2710 "$KBDIR"
  # each resident's directory under the setgid KBDIR must come out 02710 (RUNBOOK §2a: UMask 0027)
  umask 027
  exec "$KB" "$KEYS" "$KEYDIR/anchors.pem" "$KEYDIR/pins" "$KBDIR" "$KEYDIR/run" \
    "${ND_UPSTREAM:-api.anthropic.com:443}" "$st/store" "$(jsonget "$st/gb/world.json" sponsor)" "$(id -u)" "$DECIDER" ;;
resident-serve)
  [ -s "$R/follow" ] || { echo "resident-serve: no resident (run.sh resident)" >&2; exit 78; }
  read -r member grant < "$R/follow"; g=$(jsonget "$st/gb/resident.json" grain)
  P=$HROOT/worlds/testground/grains/$g
  install -m 0755 "$RES" "$P/pkg/resident"     # the build's, each start
  mkdir -p -m 0700 "$MROOT/$g"
  rm -f "$R/run/follow.sock" "$MROOT/$g/nd.sock" "$R/run/resident.sock"
  pids=()
  stop_r() { for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done; }
  trap 'stop_r; exit 0' TERM INT
  "$SUP" "$R/run/follow.sock" --hide "$st/gb" --hide "$KEYDIR" --write "$R/store" --exec "$HOST" -- \
    "$HOST" follow "$R/store" "$member" "$grant" < /dev/null & pids+=($!)
  for _ in $(seq 300); do [ -S "$R/run/follow.sock" ] && break; sleep 0.1; done
  "$SUP" "$MROOT/$g/nd.sock" --hide "$st/gb" --hide "$KEYDIR" --write "$R/ws" --exec "$ND" \
    --connect "$st/run/host.sock" --connect "$R/run/follow.sock" -- "$ND" --stdio "$R/ws" "$R/run/follow.sock" "$st/run/host.sock" < /dev/null & pids+=($!)
  # keybroker binds the resident's socket within a tick of seeing its grain
  for _ in $(seq 600); do [ -S "$KBDIR/$g/broker.sock" ] && [ -S "$MROOT/$g/nd.sock" ] && break; sleep 0.1; done
  [ -S "$KBDIR/$g/broker.sock" ] || { echo "resident-serve: no broker socket $KBDIR/$g/broker.sock (is keybroker up?)" >&2; stop_r; exit 1; }
  # the resident, its argv exactly its plan joined onto the three roots (Hosting.Resident.place):
  # after argv[0], the program again, then each field's count and paths (launcher::plan_argv)
  "$SUP" "$R/run/resident.sock" --hide "$st/gb" --hide "$KEYDIR" --hide "$HROOT/worlds/testground/store" \
    --read "$P/pkg" --write "$P/vol" --exec "$P/pkg/resident" \
    --connect "$KBDIR/$g/broker.sock" --connect "$MROOT/$g/nd.sock" -- \
    "$P/pkg/resident" "$P/pkg/resident" 1 "$P/pkg" 1 "$P/vol" 0 1 "$KBDIR/$g/broker.sock" 1 "$MROOT/$g/nd.sock" < /dev/null & pids+=($!)
  echo "resident: grain $g, member $member, serving (PIDs ${pids[*]})"
  rc=0; wait -n "${pids[@]}" || rc=$?
  echo "a process of the resident exited ($rc): stopping the others" >&2
  stop_r; exit $(( rc == 0 ? 1 : rc )) ;;
*) echo "usage: run.sh genesis|start|serve|stop|resident|keys|resident-serve STATE | fork STATE FORK" >&2; exit 2 ;;
esac
