#!/usr/bin/env bash
# deploy/live/harness.sh SRC ROOT — the rendered units under a real systemd user manager (OPS-2).
#
# SRC holds bin/{host,nd-supervise,emit-units,live-calls}, feed.py and journal.sh (every journal read
# is this run's, after a cursor; OPS-16); ROOT must not exist (one run,
# one fresh ROOT: its Stores are new geneses). Everything is written under ROOT except the unit links (`systemctl --user link`, in ~/.config/systemd/user). Units are
# started and stopped BY NAME; the only process signalled by hand is the host child of a unit,
# found from the unit's own MainPID by walking /proc/PID/task/*/children to the process whose exe
# is ROOT/bin/host (never a pattern). Every wait is bounded. One line per row:
#   ROW NAME PASS|FAIL|INFO :: detail
# then `ALL PASS` or `FAIL k`. The mechanism (/usr/local/libexec/nd-bwrap) is a deploy-time
# install (README.md), not something this script or the units create.
set -uo pipefail
SRC=${1:?usage: harness.sh SRC ROOT} ROOT=${2:?usage: harness.sh SRC ROOT}
[ -e "$ROOT" ] && { echo "$ROOT exists: every run gets a fresh ROOT"; exit 2; }
mkdir -p "$ROOT/bin" && cp "$SRC"/bin/{host,nd-supervise,emit-units,live-calls} "$ROOT/bin/" && cp "$SRC/feed.py" "$ROOT/" || exit 2
. "$SRC/journal.sh" || exit 2
B=$ROOT/bin C=$ROOT/calls U=$ROOT/units
UNITS="nd-ops-live-serve nd-ops-live-serve2 nd-ops-live-follow nd-ops-live-fsize"
fail=0
row() { echo "ROW $1 $2 :: $3"; [ "$2" = FAIL ] && fail=$((fail+1)); return 0; }
prop() { systemctl --user show "$1" -p "$2" --value; }
wait_for() { # SECONDS CMD... : poll every 0.2 s until CMD succeeds; 1 at the deadline
  local end=$((SECONDS+$1)); shift
  until "$@"; do [ $SECONDS -ge $end ] && return 1; sleep 0.2; done; }
active() { [ "$(prop "$1" ActiveState)" = active ]; }
settled() { local s; s=$(prop "$1" ActiveState); [ "$s" = failed ] || [ "$s" = inactive ]; }
restarted_past() { [ "$(prop "$1" NRestarts)" -gt "$2" ] && active "$1"; }
exits() { jr -u "$1" | grep -o 'Main process exited, code=[a-z]*, status=[0-9A-Z]*' | tail -n "${2:-1}" | tr '\n' ';'; }
host_child() { # the host process under unit $1, by its MainPID's descendants
  local p q; p=$(prop "$1" MainPID); [ "$p" -gt 0 ] || return 1
  for _ in 1 2 3 4 5 6; do
    [ "$(readlink "/proc/$p/exe" 2>/dev/null)" = "$B/host" ] && { echo "$p"; return 0; }
    q=$(cat /proc/"$p"/task/*/children 2>/dev/null | tr ' ' '\n' | grep -m1 .) || return 1
    p=$q
  done; return 1; }
for u in $UNITS; do systemctl --user stop "$u" 2>/dev/null; systemctl --user reset-failed "$u" 2>/dev/null; done

mkdir -p "$ROOT/ws" "$ROOT/env" "$U" "$ROOT/report"
journal_mark "$ROOT/report"
[ -x /usr/local/libexec/nd-bwrap ] || { echo "no mechanism at /usr/local/libexec/nd-bwrap (README.md)"; exit 2; }
"$B/live-calls" "$C" 12 >/dev/null || exit 2
# the member's follow Store is the writer's genesis reproduced with the writer's nonce (KERNEL-24,
# RUNBOOK §2): genesis.args carries the nonce, so all three are one World
for s in store fsize-store follow-store; do
  mapfile -t g < "$C/genesis.args"
  "$B/host" genesis "$ROOT/$s" "${g[@]}" > "$ROOT/report/genesis-$s.txt" || exit 2
done
m=$(awk '/^founder 0 /{print $4}' "$ROOT/report/genesis-store.txt")
gr=$(awk '/^founder 0 /{print $6}' "$ROOT/report/genesis-store.txt")
printf 'ND_MEMBER=%s\nND_GRANT=%s\n' "$m" "$gr" > "$ROOT/env/nd-ops-live-follow.env"
"$B/emit-units" --live "$ROOT" "$U" || exit 2
seg=$(stat -c %s "$ROOT/fsize-store/seg.log")
# fault injection, by hand and named: a file-size limit just above the fresh segment
sed -i "s/^\[Service\]$/[Service]\nLimitFSIZE=$((seg + 4096))/" "$U/nd-ops-live-fsize.service"
for u in $UNITS; do
  # a previous run's link (to its own ROOT/units) is replaced; any other file of that name stops us
  l=$HOME/.config/systemd/user/$u.service
  if [ -L "$l" ]; then case $(readlink "$l") in */units/$u.service) rm "$l";; *) echo "$l is not ours"; exit 2;; esac
  elif [ -e "$l" ]; then echo "$l is not ours"; exit 2; fi
  systemctl --user link "$U/$u.service" >/dev/null || exit 2
done
systemctl --user daemon-reload

# A. the confined Lean resident starts under the rendered unit and admits calls
systemctl --user start nd-ops-live-serve
wait_for 30 test -S "$ROOT/ws/serve.sock" && wait_for 10 active nd-ops-live-serve
out=$(python3 -I "$ROOT/feed.py" "$ROOT/ws/serve.sock" "$C" 0 4 | tr '\n' ';')
chk=$("$B/host" check "$ROOT/store" | grep -o ' height=[0-9]*' | tr -d ' ')
if active nd-ops-live-serve && [ "$chk" = height=4 ] && [ "$(echo "$out" | grep -o 'status=0' | wc -l)" = 4 ]; then
  row floor-suffices-for-lean-resident PASS "confined serve active; replies $out check $chk"
else row floor-suffices-for-lean-resident FAIL "state=$(prop nd-ops-live-serve ActiveState) replies=$out check=$chk"; fi

# B. a restart-class death is restarted
n0=$(prop nd-ops-live-serve NRestarts)
if hp=$(host_child nd-ops-live-serve); then
  kill -KILL "$hp"
  if wait_for 30 restarted_past nd-ops-live-serve "$n0" && wait_for 30 test -S "$ROOT/ws/serve.sock"; then
    # judged, not only printed (GATES-5): the restarted writer admits the next call and reaches height 5
    out=$(python3 -I "$ROOT/feed.py" "$ROOT/ws/serve.sock" "$C" 4 5 | tr '\n' ';')
    chk=$("$B/host" check "$ROOT/store" | grep -o ' height=[0-9]*' | tr -d ' ')
    if [ "$(echo "$out" | grep -o 'status=0' | wc -l)" = 1 ] && [ "$chk" = height=5 ]; then
      row host-killed-is-restarted PASS "SIGKILL host pid $hp; $(exits nd-ops-live-serve) NRestarts $n0 -> $(prop nd-ops-live-serve NRestarts); after: $out check $chk"
    else row host-killed-is-restarted FAIL "restarted, but the next call: $out check $chk (want one status=0, height=5)"; fi
  else row host-killed-is-restarted FAIL "state=$(prop nd-ops-live-serve ActiveState) $(exits nd-ops-live-serve)"; fi
else row host-killed-is-restarted FAIL "no host process under the unit"; fi

# C. a fatal exit stops: a second writer on the same Store is `locked` (16), never restarted
systemctl --user start nd-ops-live-serve2
wait_for 30 settled nd-ops-live-serve2
st=$(prop nd-ops-live-serve2 ExecMainStatus) nr=$(prop nd-ops-live-serve2 NRestarts)
if settled nd-ops-live-serve2 && [ "$st" = 16 ] && [ "$nr" = 0 ]; then
  row second-writer-locked-is-stopped PASS "ExecMainStatus=16 NRestarts=0 $(prop nd-ops-live-serve2 ActiveState)/$(prop nd-ops-live-serve2 Result)"
else row second-writer-locked-is-stopped FAIL "status=$st NRestarts=$nr state=$(prop nd-ops-live-serve2 ActiveState)"; fi

# D. a crash on every start stops at the start limit
for _ in 1 2 3 4 5 6 7; do
  n=$(prop nd-ops-live-serve NRestarts)
  hp=$(host_child nd-ops-live-serve) || break
  kill -KILL "$hp"
  wait_for 30 restarted_past nd-ops-live-serve "$n" || break
done
wait_for 20 settled nd-ops-live-serve
r=$(prop nd-ops-live-serve Result)
# systemd 255 reports the refused restart as Result=exit-code; the journal names the start limit
lim=$(jr -u nd-ops-live-serve | grep -c 'Start request repeated too quickly')
if settled nd-ops-live-serve && { [ "$r" = start-limit-hit ] || [ "$lim" -ge 1 ]; }; then
  row crash-loop-hits-start-limit PASS "Start request repeated too quickly; Result=$r after NRestarts=$(prop nd-ops-live-serve NRestarts)"
else row crash-loop-hits-start-limit FAIL "Result=$r state=$(prop nd-ops-live-serve ActiveState) NRestarts=$(prop nd-ops-live-serve NRestarts)"; fi
chk=$("$B/host" check "$ROOT/store"); row store-sound-after-the-kills INFO "$chk"

# E. an append that fails (LimitFSIZE): `uncertain` (3) restarted is the table's claim
systemctl --user start nd-ops-live-fsize
wait_for 30 test -S "$ROOT/ws/fsize.sock" && wait_for 10 active nd-ops-live-fsize
n0=$(prop nd-ops-live-fsize NRestarts)
out=$(python3 -I "$ROOT/feed.py" "$ROOT/ws/fsize.sock" "$C" 0 1 | tr '\n' ';')
wait_for 30 restarted_past nd-ops-live-fsize "$n0"
ex=$(exits nd-ops-live-fsize)
case $ex in
  *status=3\;) row append-failure-is-uncertain-restarted PASS "$ex reply $out NRestarts $(prop nd-ops-live-fsize NRestarts)";;
  *) row append-failure-is-uncertain-restarted FAIL "$ex (want status=3) reply $out NRestarts $(prop nd-ops-live-fsize NRestarts)";;
esac
systemctl --user stop nd-ops-live-fsize

# F. the follower unit under its rendered EnvironmentFile: the confined follower opens its Store
systemctl --user start nd-ops-live-follow
fl() { jr -u nd-ops-live-follow | grep -q '^STATUS follow'; }
if wait_for 30 fl && active nd-ops-live-follow; then
  row follower-unit-starts PASS "active; $(jr -u nd-ops-live-follow | grep -m1 '^STATUS follow' | cut -c1-160)"
else row follower-unit-starts FAIL "$(prop nd-ops-live-follow ActiveState)/$(prop nd-ops-live-follow Result) $(exits nd-ops-live-follow) :: $(jr -u nd-ops-live-follow | tail -n 3 | tr '\n' ';')"; fi

for u in $UNITS; do systemctl --user stop "$u"; systemctl --user reset-failed "$u" 2>/dev/null; done
if [ $fail = 0 ]; then echo "ALL PASS"; exit 0; fi
echo "FAIL $fail"; exit 1
