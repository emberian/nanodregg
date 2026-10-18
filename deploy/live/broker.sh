#!/usr/bin/env bash
# deploy/live/broker.sh SRC ROOT — the rendered keybroker, hosted-follower and grain-launch units under a
# real systemd user manager (OPS-3).
#
# SRC holds bin/{host,live-calls,emit-units,keybroker,hosting-broker,emit-anchors,nd-supervise,
# grain-launch,hosting-controller}, anchors.pem
# (deploy/tls/anchors.pem), pins (deploy/tls/pins, empty) and EXITS.md (deploy/units/EXITS.md: codes are read from it by name, never
# typed here). ROOT must not exist; everything is written under it except the unit link
# (`systemctl --user link`: four, nd-ops-live-keybroker, the writer nd-ops-live-serve that admits the
# resident grain's two calls, and the two templates nd-ops-live-hfollow@ and nd-ops-live-grain@). Units are started and stopped BY NAME; the only process signalled by
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
. "$SRC/journal.sh" || exit 2
umask 022
mkdir -p "$ROOT/bin" && chmod 0755 "$ROOT" || exit 2
cp "$SRC"/bin/{host,live-calls,emit-units,keybroker,hosting-broker,emit-anchors,nd-supervise,grain-launch,hosting-controller} "$ROOT/bin/" && cp "$SRC/feed.py" "$ROOT/" || exit 2
B=$ROOT/bin U=$ROOT/units R=$ROOT
UNIT=nd-ops-live-keybroker
LINKS="nd-ops-live-keybroker nd-ops-live-hfollow@ nd-ops-live-grain@ nd-ops-live-serve"
code() { # NAME TABLE: the code of NAME in EXITS.md's table whose heading starts `## TABLE`
  awk -F'|' -v n=" $1 " -v t="## $2" 'index($0, t) == 1 {in_t=1; next} /^## / {in_t=0}
    in_t && $3 == n {gsub(/ /, "", $2); print $2; exit}' "$SRC/EXITS.md"; }
fail=0
row() { echo "ROW $1 $2 :: $3"; [ "$2" = FAIL ] && fail=$((fail+1)); return 0; }
prop() { systemctl --user show "${2:-$UNIT}" -p "$1" --value; }
wait_for() { local end=$((SECONDS+$1)); shift
  until "$@"; do [ $SECONDS -ge $end ] && return 1; sleep 0.2; done; }
active() { [ "$(prop ActiveState)" = active ]; }
settled() { local s; s=$(prop ActiveState); [ "$s" = failed ] || [ "$s" = inactive ]; }
restarted_past() { [ "$(prop NRestarts)" -gt "$1" ] && active; }
# journal reads are this run's, after the cursor journal.sh records (a link kept across runs keeps
# one journal: run 2's first draft read run 1's lines; `--since` had one-second granularity)
ju() { jr -u "${1:-$UNIT}"; }
exits() { ju | grep -o 'Main process exited, code=[a-z]*, status=[0-9A-Z]*' | tail -n 1; }
fresh() { systemctl --user stop "$UNIT" 2>/dev/null; systemctl --user reset-failed "$UNIT" 2>/dev/null; return 0; }
for nt in deciderSignaled:keybroker keyFileMode:keybroker sockDir:keybroker store:hosting-controller layoutMissing:grain-launch inviteRefused:host missing:host; do
  [ -n "$(code "${nt%%:*}" "${nt#*:}")" ] || { echo "no code for $nt in EXITS.md"; exit 2; }; done
[ -x /usr/local/libexec/nd-bwrap ] || { echo "no mechanism at /usr/local/libexec/nd-bwrap (README.md)"; exit 2; }

# the fixture: a genesis Store, the provider key (a canary, never a real key), the pinned anchors,
# SOCKDIR 02710, the environment file
mkdir -p "$R/etc" "$R/pids" "$R/broker" "$R/calls" "$R/report" "$U" && chmod 0700 "$R/etc" && chmod 2710 "$R/broker" || exit 2
journal_mark "$R/report"
"$B/live-calls" "$R/calls" 1 >/dev/null || exit 2
mapfile -t g < "$R/calls/genesis.args"
"$B/host" genesis "$R/store" "${g[@]}" > "$R/report/genesis.txt" || exit 2
op=$(awk '/^founder 0 /{print $4}' "$R/report/genesis.txt")
printf '7 CANARY-ops3-live-not-a-key\n' > "$R/etc/provider.key" && chmod 0600 "$R/etc/provider.key"
cp "$SRC/anchors.pem" "$R/etc/anchors.pem" && chmod 0644 "$R/etc/anchors.pem"
cp "$SRC/pins" "$R/etc/pins" && chmod 0644 "$R/etc/pins" || exit 2   # the shipped, EMPTY pins: the fixture never calls upstream
printf 'ND_OPERATOR=%s\nND_PEER=%s\n' "$op" "$(id -u)" > "$R/etc/keybroker.env"
"$B/emit-units" --live "$ROOT" "$U" || exit 2
for u in $LINKS; do
  l=$HOME/.config/systemd/user/$u.service
  if [ -L "$l" ]; then case $(readlink "$l") in */units/$u.service) rm "$l";; *) echo "$l is not ours"; exit 2;; esac
  elif [ -e "$l" ]; then echo "$l is not ours"; exit 2; fi
  systemctl --user link "$U/$u.service" >/dev/null || exit 2
done
systemctl --user daemon-reload
# the World's resident grain (HOSTING-26): keybroker binds a socket only for a resident grain the Store
# holds, so the rendered writer admits live-calls' two grain calls (install the lifecycle package,
# create the grain) before any keybroker row; the socket's directory is the grain's name
mkdir -p "$R/ws"
S=nd-ops-live-serve
systemctl --user start "$S"
wait_for 30 test -S "$R/ws/serve.sock" || { echo "the writer for the grain calls did not bind"; exit 2; }
gout=$(python3 -I "$R/feed.py" "$R/ws/serve.sock" "$R/calls" 0 2 grain | tr '\n' ';')
systemctl --user stop "$S"
gchk=$("$B/host" check "$R/store" | grep -o ' height=[0-9]*' | tr -d ' ')
[ "$gchk" = height=2 ] && [ "$(echo "$gout" | grep -o 'status=0' | wc -l)" = 2 ] || { echo "the grain calls were not admitted: $gout check $gchk"; exit 2; }
gdir=$(cat "$R/calls/grain.dir")
fresh
sock=$R/broker/$gdir/broker.sock

# G. the rendered unit starts: ExecStartPre passes on the pinned anchors, keybroker binds the
# resident's socket in its 02710 directory (0600: PEER is this uid, keybroker's one-uid mode, HOSTING-21;
# the deployment's two-uid socket is 0660) and its decider runs confined, under NoNewPrivileges
systemctl --user start "$UNIT"
up() { [ -S "$sock" ] && [ -s "$R/pids/decider.pid" ] && active; }
if wait_for 30 up; then
  dp=$(cat "$R/pids/decider.pid")
  m=$(stat -c '%a %g' "$sock") dm=$(stat -c '%a' "$R/broker/$gdir")
  nnp=$(prop NoNewPrivileges) dexe=$(readlink "/proc/$dp/exe" 2>/dev/null)
  ghost=$(ls -A "$R/broker" | grep -vx "$gdir" | tr '\n' ' ')
  if [ "$m" = "600 $(id -g)" ] && [ "$dm" = 2710 ] && [ -z "$ghost" ] && [ "$nnp" = yes ] && [ -n "$dexe" ]; then
    row keybroker-unit-starts PASS "active; the World's resident grain $gdir has socket $m dir $dm and nothing else is listed; decider pid $dp exe $dexe; NoNewPrivileges=$nnp"
  else row keybroker-unit-starts FAIL "socket '$m' dir '$dm' unlisted names '$ghost' NoNewPrivileges=$nnp decider exe '$dexe'"; fi
else row keybroker-unit-starts FAIL "$(prop ActiveState)/$(prop Result) $(exits) :: $(ju | tail -n 4 | tr '\n' ';')"; fi

# H. a signalled decider: keybroker ends deciderSignaled (restart class), systemd restarts it
n0=$(prop NRestarts)
if active && [ -s "$R/pids/decider.pid" ]; then
  dp=$(cat "$R/pids/decider.pid")
  kill -KILL "$dp"
  if wait_for 30 restarted_past "$n0" && wait_for 30 up; then
    case $(exits) in
      *status=$(code deciderSignaled keybroker)) row decider-killed-is-restarted PASS "SIGKILL decider pid $dp; $(exits) (deciderSignaled $(code deciderSignaled keybroker)); NRestarts $n0 -> $(prop NRestarts); new decider $(cat "$R/pids/decider.pid")";;
      *) row decider-killed-is-restarted FAIL "restarted, but $(exits) (want status=$(code deciderSignaled keybroker))";;
    esac
  else row decider-killed-is-restarted FAIL "$(prop ActiveState) $(exits) NRestarts $(prop NRestarts)"; fi
else row decider-killed-is-restarted FAIL "keybroker not up with a decider PID file"; fi

# I. an installed anchors copy edited by one byte: ExecStartPre refuses every start, the unit
# stops at the start limit, keybroker never runs
fresh
CUR=$(journalctl --user --show-cursor -n 0 --no-pager 2>/dev/null | sed -n 's/^-- cursor: //p'); [ -n "$CUR" ] || exit 2  # row I reads only its own lines
cp "$R/etc/anchors.pem" "$R/report/anchors.good"
python3 -I -c 'import sys; p=sys.argv[1]; b=bytearray(open(p,"rb").read()); i=len(b)//2; b[i]^=1; open(p,"wb").write(b)' "$R/etc/anchors.pem"
if cmp -s "$R/etc/anchors.pem" "$R/report/anchors.good"; then row anchors-edited-refused-at-start FAIL "the edit is a no-op"; else
  rm -f "$sock"
  systemctl --user start "$UNIT"
  wait_for 60 settled
  lim=$(ju | grep -c 'Start request repeated too quickly')
  pre=$(ju | grep -m1 -i 'emit-anchors' | cut -c1-160)
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
if settled && [ "$st" = "$(code keyFileMode keybroker)" ] && [ "$nr" = 0 ]; then
  row key-mode-0644-stops PASS "ExecMainStatus=$st (keyFileMode) NRestarts=0 $(prop Result)"
else row key-mode-0644-stops FAIL "status=$st (want $(code keyFileMode keybroker)) NRestarts=$nr $(prop ActiveState)"; fi
chmod 0600 "$R/etc/provider.key"

# K. SOCKDIR of the wrong mode: sockDir, stopped before any socket opens
fresh
rm -f "$sock"; chmod 0755 "$R/broker"
systemctl --user start "$UNIT"
wait_for 30 settled
st=$(prop ExecMainStatus) nr=$(prop NRestarts)
if settled && [ "$st" = "$(code sockDir keybroker)" ] && [ "$nr" = 0 ] && [ ! -S "$sock" ]; then
  row sockdir-mode-stops PASS "ExecMainStatus=$st (sockDir) NRestarts=0, no socket"
else row sockdir-mode-stops FAIL "status=$st (want $(code sockDir keybroker)) NRestarts=$nr socket $( [ -S "$sock" ] && echo present || echo absent)"; fi
chmod 2710 "$R/broker"

fresh

# L. the hosted follower (template, instance w) under nd-supervise --group: its Store JOINED from
# founder 0's invitation with RUNBOOK §2b's argv (`host join STORE INVITATION KEY_HEX`, OPS-15),
# its origin the writer's; its socket 0660 of the shared directory's group
F=nd-ops-live-hfollow@w G=nd-ops-live-grain@w
mkdir -p "$R/hosted/worlds/w/store" "$R/nd-follow" "$R/member" "$R/ws" "$R/env" "$R/pids/w" && chmod 0700 "$R/hosted" "$R/hosted/worlds" "$R/hosted/worlds/w" "$R/hosted/worlds/w/store" && chmod 2710 "$R/nd-follow" "$R/member" || exit 2
inv=$(cat "$R/calls/invitation") key=$(cat "$R/calls/sponsor.key")
"$B/host" join "$R/hosted/worlds/w/store" "$inv" "$key" > "$R/report/join-hosted.txt" || exit 2
[ "$(awk '/^origin /{print $2}' "$R/report/join-hosted.txt")" = "$(awk '/^origin /{print $2}' "$R/report/genesis.txt")" ] || { echo "the joined World is not the writer's"; exit 2; }
gr=$(awk '/^founder 0 /{print $6}' "$R/report/genesis.txt")
printf 'ND_MEMBER=%s\nND_GRANT=%s\nND_GID=%s\n' "$op" "$gr" "$(id -g)" > "$R/env/w.env"
fsock=$R/nd-follow/w.sock
systemctl --user start "$F"
fup() { [ -S "$fsock" ] && [ "$(prop ActiveState "$F")" = active ]; }
if wait_for 30 fup; then
  m=$(stat -c '%a %g' "$fsock")
  if [ "$m" = "660 $(id -g)" ]; then row hosted-follower-starts PASS "active; socket $m (--group)"
  else row hosted-follower-starts FAIL "socket '$m'"; fi
else row hosted-follower-starts FAIL "$(prop ActiveState "$F")/$(prop Result "$F") :: $(ju "$F" | tail -n 3 | tr '\n' ';')"; fi

# M. grain-launch (template, instance w) starts its confined controller over the follow Store and
# keeps running (the World has no grain: nothing is launched)
systemctl --user start "$G"
sleep 10
if [ "$(prop ActiveState "$G")" = active ] && [ "$(prop NRestarts "$G")" = 0 ]; then
  row grain-launch-starts PASS "active after 10 s, NRestarts=0, MainPID $(prop MainPID "$G")"
else row grain-launch-starts FAIL "$(prop ActiveState "$G")/$(prop Result "$G") status=$(prop ExecMainStatus "$G") :: $(ju "$G" | tail -n 3 | tr '\n' ';')"; fi
systemctl --user stop "$G"

# N. a controller Store refusal stops the launcher by name: instance x over an empty store directory
X=nd-ops-live-grain@x
mkdir -p "$R/hosted/worlds/x/store" "$R/pids/x" && chmod 0700 "$R/hosted/worlds/x"
systemctl --user start "$X"
xs() { local s; s=$(prop ActiveState "$X"); [ "$s" = failed ] || [ "$s" = inactive ]; }
wait_for 30 xs
st=$(prop ExecMainStatus "$X") nr=$(prop NRestarts "$X")
if xs && [ "$st" = "$(code store hosting-controller)" ] && [ "$nr" = 0 ]; then
  row controller-store-refusal-stops PASS "ExecMainStatus=$st (controller store, passed through) NRestarts=0"
else row controller-store-refusal-stops FAIL "status=$st (want $(code store hosting-controller)) NRestarts=$nr $(prop ActiveState "$X")"; fi

# O. a layout directory missing (instance y has no worlds/y/store; LAYOUT_HIDDEN is just `store` since
# HOSTING-32): grain-launch refuses layoutMissing at start, by name, before the controller runs; never restarted
systemctl --user stop "$X" 2>/dev/null
G=nd-ops-live-grain@y
mkdir -p "$R/hosted/worlds/y" "$R/pids/y" && chmod 0700 "$R/hosted/worlds/y" || exit 2
systemctl --user reset-failed "$G" 2>/dev/null
systemctl --user start "$G"
gs() { local s; s=$(prop ActiveState "$G"); [ "$s" = failed ] || [ "$s" = inactive ]; }
wait_for 30 gs
st=$(prop ExecMainStatus "$G") nr=$(prop NRestarts "$G")
if gs && [ "$st" = "$(code layoutMissing grain-launch)" ] && [ "$nr" = 0 ]; then
  row layout-missing-stops PASS "ExecMainStatus=$st (layoutMissing) NRestarts=0 :: $(ju "$G" | grep -m1 -i layoutMissing | cut -c1-120)"
else row layout-missing-stops FAIL "status=$st (want $(code layoutMissing grain-launch)) NRestarts=$nr $(prop ActiveState "$G")"; fi

# P. a forged invitation: `host join` refuses inviteRefused and writes nothing; the follower unit
# started over that empty Store directory ends `missing` (fatal) and is NOT restarted: a refused
# join never becomes a follower (OPS-15)
P=nd-ops-live-hfollow@p
mkdir -p "$R/hosted/worlds/p/store" && chmod 0700 "$R/hosted/worlds/p" "$R/hosted/worlds/p/store"
cp "$R/env/w.env" "$R/env/p.env"
forged=$(python3 -I -c 'import sys; h=sys.argv[1]; print(h[:-1] + ("1" if h[-1] == "0" else "0"))' "$inv")
"$B/host" join "$R/hosted/worlds/p/store" "$forged" "$key" 2> "$R/report/join-forged.err"; jc=$?
if [ "$forged" = "$inv" ] || [ "$jc" != "$(code inviteRefused host)" ] || [ -n "$(ls -A "$R/hosted/worlds/p/store")" ]; then
  row forged-join-follower-stops FAIL "join exit $jc (want $(code inviteRefused host)) store $(ls -A "$R/hosted/worlds/p/store" | wc -l) files :: $(cat "$R/report/join-forged.err")"
else
  systemctl --user start "$P"
  ps_() { local s; s=$(prop ActiveState "$P"); [ "$s" = failed ] || [ "$s" = inactive ]; }
  wait_for 30 ps_
  st=$(prop ExecMainStatus "$P") nr=$(prop NRestarts "$P")
  if ps_ && [ "$st" = "$(code missing host)" ] && [ "$nr" = 0 ]; then
    row forged-join-follower-stops PASS "join $(cat "$R/report/join-forged.err"); follower ExecMainStatus=$st (missing) NRestarts=0"
  else row forged-join-follower-stops FAIL "follower status=$st (want $(code missing host)) NRestarts=$nr $(prop ActiveState "$P")"; fi
fi

for u in "$F" "$G" nd-ops-live-grain@w "$X" "$P" nd-ops-live-hfollow@x; do systemctl --user stop "$u" 2>/dev/null; systemctl --user reset-failed "$u" 2>/dev/null; done
if [ $fail = 0 ]; then echo "ALL PASS"; exit 0; fi
echo "FAIL $fail"; exit 1
