#!/usr/bin/env bash
# deploy/live/broker.sh SRC ROOT — the rendered keybroker unit under a real systemd user manager (OPS-3).
#
# SRC holds bin/{host,live-calls,emit-units,keybroker,hosting-broker,emit-anchors}, anchors.pem
# (deploy/tls/anchors.pem) and EXITS.md (deploy/units/EXITS.md: codes are read from it by name, never
# typed here). ROOT must not exist; everything is written under it except the unit link
# (`systemctl --user link`). The unit is started and stopped BY NAME; the only process signalled by
# hand is the decider, by the PID in keybroker's own PID file (ROOT/pids/decider.pid). Every wait is
# bounded. One line per row, then `ALL PASS` or `FAIL k`:
#   ROW NAME PASS|FAIL|INFO :: detail
# One uid runs it all (a user unit): PEER is this uid and SOCKDIR's group its primary group, the
# deployment's two-uid branch is the broker test's. The upstream is an unreachable local port: the
# rows are the unit's, not a call's. The mechanism (/usr/local/libexec/nd-bwrap) is a deploy-time
# install (README.md).
set -uo pipefail
SRC=${1:?usage: broker.sh SRC ROOT} ROOT=${2:?usage: broker.sh SRC ROOT}
[ -e "$ROOT" ] && { echo "$ROOT exists: every run gets a fresh ROOT"; exit 2; }
umask 022
mkdir -p "$ROOT/bin" && chmod 0755 "$ROOT" || exit 2
cp "$SRC"/bin/{host,live-calls,emit-units,keybroker,hosting-broker,emit-anchors} "$ROOT/bin/" || exit 2
B=$ROOT/bin U=$ROOT/units R=$ROOT
UNIT=nd-ops-live-keybroker
code() { awk -F'|' -v n=" $1 " '$3 == n {gsub(/ /, "", $2); print $2; exit}' "$SRC/EXITS.md"; }
fail=0
row() { echo "ROW $1 $2 :: $3"; [ "$2" = FAIL ] && fail=$((fail+1)); return 0; }
prop() { systemctl --user show "$UNIT" -p "$1" --value; }
wait_for() { local end=$((SECONDS+$1)); shift
  until "$@"; do [ $SECONDS -ge $end ] && return 1; sleep 0.2; done; }
active() { [ "$(prop ActiveState)" = active ]; }
settled() { local s; s=$(prop ActiveState); [ "$s" = failed ] || [ "$s" = inactive ]; }
restarted_past() { [ "$(prop NRestarts)" -gt "$1" ] && active; }
exits() { journalctl --user -u "$UNIT" -o cat --no-pager 2>/dev/null | grep -o 'Main process exited, code=[a-z]*, status=[0-9A-Z]*' | tail -n 1; }
fresh() { systemctl --user stop "$UNIT" 2>/dev/null; systemctl --user reset-failed "$UNIT" 2>/dev/null; return 0; }
for n in deciderSignaled keyFileMode sockDir; do [ -n "$(code $n)" ] || { echo "no code for $n in EXITS.md"; exit 2; }; done
[ -x /usr/local/libexec/nd-bwrap ] || { echo "no mechanism at /usr/local/libexec/nd-bwrap (README.md)"; exit 2; }

# the fixture: a genesis Store, the provider key (a canary, never a real key), the pinned anchors,
# SOCKDIR 02710, the environment file
mkdir -p "$R/etc" "$R/pids" "$R/broker" "$R/calls" "$R/report" "$U" && chmod 0700 "$R/etc" && chmod 2710 "$R/broker" || exit 2
"$B/live-calls" "$R/calls" 1 >/dev/null || exit 2
mapfile -t g < "$R/calls/genesis.args"
"$B/host" genesis "$R/store" "${g[@]}" > "$R/report/genesis.txt" || exit 2
op=$(awk '/^founder 0 /{print $4}' "$R/report/genesis.txt")
printf '7 CANARY-ops3-live-not-a-key\n' > "$R/etc/provider.key" && chmod 0600 "$R/etc/provider.key"
cp "$SRC/anchors.pem" "$R/etc/anchors.pem" && chmod 0644 "$R/etc/anchors.pem"
printf 'ND_OPERATOR=%s\nND_RESIDENTS=01\nND_PEER=%s\n' "$op" "$(id -u)" > "$R/etc/keybroker.env"
"$B/emit-units" --live "$ROOT" "$U" || exit 2
l=$HOME/.config/systemd/user/$UNIT.service
if [ -L "$l" ]; then case $(readlink "$l") in */units/$UNIT.service) rm "$l";; *) echo "$l is not ours"; exit 2;; esac
elif [ -e "$l" ]; then echo "$l is not ours"; exit 2; fi
systemctl --user link "$U/$UNIT.service" >/dev/null || exit 2
systemctl --user daemon-reload
fresh
sock=$R/broker/01/broker.sock

# G. the rendered unit starts: ExecStartPre passes on the pinned anchors, keybroker binds the
# resident's socket 0660 in its 02710 directory and its decider runs confined, under NoNewPrivileges
systemctl --user start "$UNIT"
up() { [ -S "$sock" ] && [ -s "$R/pids/decider.pid" ] && active; }
if wait_for 30 up; then
  dp=$(cat "$R/pids/decider.pid")
  m=$(stat -c '%a %g' "$sock") dm=$(stat -c '%a' "$R/broker/01")
  nnp=$(prop NoNewPrivileges) dexe=$(readlink "/proc/$dp/exe" 2>/dev/null)
  if [ "$m" = "660 $(id -g)" ] && [ "$dm" = 2710 ] && [ "$nnp" = yes ] && [ -n "$dexe" ]; then
    row keybroker-unit-starts PASS "active; socket $m dir $dm; decider pid $dp exe $dexe; NoNewPrivileges=$nnp"
  else row keybroker-unit-starts FAIL "socket '$m' dir '$dm' NoNewPrivileges=$nnp decider exe '$dexe'"; fi
else row keybroker-unit-starts FAIL "$(prop ActiveState)/$(prop Result) $(exits) :: $(journalctl --user -u "$UNIT" -o cat --no-pager 2>/dev/null | tail -n 4 | tr '\n' ';')"; fi

# H. a signalled decider: keybroker ends deciderSignaled (restart class), systemd restarts it
n0=$(prop NRestarts)
if active && [ -s "$R/pids/decider.pid" ]; then
  dp=$(cat "$R/pids/decider.pid")
  kill -KILL "$dp"
  if wait_for 30 restarted_past "$n0" && wait_for 30 up; then
    case $(exits) in
      *status=$(code deciderSignaled)) row decider-killed-is-restarted PASS "SIGKILL decider pid $dp; $(exits) (deciderSignaled $(code deciderSignaled)); NRestarts $n0 -> $(prop NRestarts); new decider $(cat "$R/pids/decider.pid")";;
      *) row decider-killed-is-restarted FAIL "restarted, but $(exits) (want status=$(code deciderSignaled))";;
    esac
  else row decider-killed-is-restarted FAIL "$(prop ActiveState) $(exits) NRestarts $(prop NRestarts)"; fi
else row decider-killed-is-restarted FAIL "keybroker not up with a decider PID file"; fi

# I. an installed anchors copy edited by one byte: ExecStartPre refuses every start, the unit
# stops at the start limit, keybroker never runs
fresh
cp "$R/etc/anchors.pem" "$R/report/anchors.good"
python3 -I -c 'import sys; p=sys.argv[1]; b=bytearray(open(p,"rb").read()); i=len(b)//2; b[i]^=1; open(p,"wb").write(b)' "$R/etc/anchors.pem"
if cmp -s "$R/etc/anchors.pem" "$R/report/anchors.good"; then row anchors-edited-refused-at-start FAIL "the edit is a no-op"; else
  rm -f "$sock"
  systemctl --user start "$UNIT"
  wait_for 60 settled
  lim=$(journalctl --user -u "$UNIT" -o cat --no-pager 2>/dev/null | grep -c 'Start request repeated too quickly')
  pre=$(journalctl --user -u "$UNIT" -o cat --no-pager 2>/dev/null | grep -m1 -i 'emit-anchors' | cut -c1-160)
  if settled && [ "$lim" -ge 1 ] && [ ! -S "$sock" ]; then
    row anchors-edited-refused-at-start PASS "Result=$(prop Result); start limit hit; journal: $pre"
  else row anchors-edited-refused-at-start FAIL "$(prop ActiveState)/$(prop Result) limit=$lim :: $pre"; fi
fi
cp "$R/report/anchors.good" "$R/etc/anchors.pem"

# J. a custody refusal: the provider key at mode 0644 stops the unit by name, never restarted
fresh
chmod 0644 "$R/etc/provider.key"
systemctl --user start "$UNIT"
wait_for 30 settled
st=$(prop ExecMainStatus) nr=$(prop NRestarts)
if settled && [ "$st" = "$(code keyFileMode)" ] && [ "$nr" = 0 ]; then
  row key-mode-0644-stops PASS "ExecMainStatus=$st (keyFileMode) NRestarts=0 $(prop Result)"
else row key-mode-0644-stops FAIL "status=$st (want $(code keyFileMode)) NRestarts=$nr $(prop ActiveState)"; fi
chmod 0600 "$R/etc/provider.key"

# K. SOCKDIR of the wrong mode: sockDir, stopped before any socket opens
fresh
rm -f "$sock"; chmod 0755 "$R/broker"
systemctl --user start "$UNIT"
wait_for 30 settled
st=$(prop ExecMainStatus) nr=$(prop NRestarts)
if settled && [ "$st" = "$(code sockDir)" ] && [ "$nr" = 0 ] && [ ! -S "$sock" ]; then
  row sockdir-mode-stops PASS "ExecMainStatus=$st (sockDir) NRestarts=0, no socket"
else row sockdir-mode-stops FAIL "status=$st (want $(code sockDir)) NRestarts=$nr socket $( [ -S "$sock" ] && echo present || echo absent)"; fi
chmod 2710 "$R/broker"

fresh
if [ $fail = 0 ]; then echo "ALL PASS"; exit 0; fi
echo "FAIL $fail"; exit 1
