#!/bin/bash
# deploy/live/confined-unit.sh ROOT BIN [FILTER] [TAG] — the confinement under the service manager's own
# sandbox (CLIENT-48, CLIENT-52): `host serve` and a member's `host follow`, each under nd-supervise in a
# transient system unit carrying the PRODUCTION PROFILE read out of the rendered writer unit
# (deploy/units/linux/nd-host-serve.service, Ops.Units.Node.profile: every line between
# `NoNewPrivileges=yes` and `TimeoutStopSec=`, its paths moved under ROOT: ReadWritePaths=ROOT,
# NoExecPaths=ROOT/u/stores), nd-supervise given the unit's `--landlock-abi`; then `nd create`, `write`,
# `read` as the member. Each unit's state and the member's verdicts are printed.
#
# PROBE=1: instead of the writer, run BIN/sandbox-probe as nd-supervise's confined child under the same
# unit lines (the real writer launch path: nd-supervise's policy, the unit's profile) on a script of
# the operations it must refuse, and print each verdict (sandbox/tests/probe.rs is the standalone half).
#
# ROOT: a fresh directory with a clean custody chain (root-owned parents, no group or other write), e.g.
# `sudo install -d -o $USER -m 0755 /srv/nd-sbx`; it is emptied and refilled. BIN: host, nd,
# nd-supervise (and sandbox-probe), outside /home (ProtectHome=yes). FILTER: overrides the unit's
# SystemCallFilter (`@system-service` alone shows the refusal by name, `confine: landlock is missing`).
# ABI: overrides the unit's `--landlock-abi` (a kernel below it refuses every launch `landlockAbi`, by
# name, in the unit's journal). UNIT: the rendered unit to read (default: this tree's). Needs
# `sudo -n systemd-run`. Units stop at the end.
set -u
S=${1:?ROOT}; B=${2:?BIN}; FILTER=${3:-}; TAG=${4:-a}; U=$S/u
UNIT=${UNIT:-$(dirname "$0")/../units/linux/nd-host-serve.service}
ABI=${ABI:-$(sed -n 's/.*--landlock-abi \([0-9][0-9]*\).*/\1/p' "$UNIT")}
rm -rf "$U"; mkdir -p "$U/holding" "$U/stores" "$U/hide"; chmod 700 "$U" "$U/holding"
PROPS=(-p Type=exec --uid="$(id -u)" --gid="$(id -g)")
while IFS= read -r l; do
  case $l in
    '') ;;
    ReadWritePaths=*) PROPS+=(-p "ReadWritePaths=$U") ;;
    NoExecPaths=*) PROPS+=(-p "NoExecPaths=$U/stores") ;;
    SystemCallFilter=*) PROPS+=(-p "SystemCallFilter=${FILTER:-${l#*=}}") ;;
    *) PROPS+=(-p "$l") ;;
  esac
done < <(sed -n '/^NoNewPrivileges=yes$/,/^TimeoutStopSec=/p' "$UNIT" | grep -v '^TimeoutStopSec=')
[ "${#PROPS[@]}" -gt 40 ] || { echo "confined-unit: no profile lines in $UNIT"; exit 2; }
echo "profile: $UNIT (${#PROPS[@]} args), --landlock-abi $ABI"
sup() { # NAME SOCK STORE PROGRAM ARGS...
  local n=$1 sock=$2 st=$3 prog=$4; shift 4
  sudo -n systemd-run --unit="nd-confined-$TAG-$n" --collect "${PROPS[@]}" \
    "$B/nd-supervise" "$sock" --landlock-abi "$ABI" --hide "$U/hide" --hide /home --write "$st" \
    --exec "$prog" -- "$prog" "$@"
}
journal() { sudo -n journalctl -q -u "nd-confined-$TAG-$1" --no-pager | grep -E 'nd-supervise|confine|ld-linux|error' | tail -"${2:-3}"; }

if [ "${PROBE:-}" = 1 ]; then
  # The targets: a same-uid file outside the write grant (inside the unit's ReadWritePaths, so only
  # the inner sandbox can refuse), the probe's parent (nd-supervise), the write grant itself.
  P=$U/stores/P; mkdir -p "$P" "$U/sib" "$U/ws"; echo x > "$U/sib/f"; echo x > "$P/own"
  cat > "$P/script" <<SCRIPT
chmod-sibling fchmodat $U/sib/f
chmod2-sibling fchmodat2 $U/sib/f
times-sibling utimensat $U/sib/f
chown-sibling chown $U/sib/f
xattr-sibling setxattr $U/sib/f
fchmod-own fchmod $P/own
read-sibling open $U/sib/f
fifo-in-grant mkfifo $P/fifo
signal-parent kill-parent
signal-all kill-all
tgkill-parent tgkill-parent
sigqueue-parent sigqueue-parent
pidfd-parent pidfd-parent
setown-parent setown-parent
setown-ex-parent setown-ex-parent
setsig setsig
async async
pdeathsig-clear pdeathsig-clear
socket socket
socketpair socketpair
memfd memfd
clone-process clone-process
io-uring io-uring
exec-written exec-written $P
loader-written loader-written $P
SCRIPT
  sup probe "$U/ws/probe.sock" "$P" "$B/sandbox-probe" script "$P/script" "$P/out"
  for _ in $(seq 100); do [ "$(grep -c . "$P/out" 2>/dev/null)" -ge 25 ] && break; sleep 0.1; done
  sleep 1
  echo "unit probe: $(systemctl show -p ActiveState -p ExecMainStatus "nd-confined-$TAG-probe.service" | tr '\n' ' ')"
  cat "$P/out"; echo
  # the loader's own refusal, when NoExecPaths stops it mapping the written file
  journal probe 6
  sudo -n systemctl stop "nd-confined-$TAG-probe.service" 2>/dev/null
  exit 0
fi

export ND_WORKSPACE=$U/ws ND_HOLDING=$U/holding
"$B/nd" --init || exit 1
keys=$("$B/nd" --keys); key=$(sed -n 's/^key //p' <<<"$keys"); next=$(sed -n 's/^next //p' <<<"$keys")
g=$("$B/host" genesis "$U/stores/W" nano "$key" "$next") || exit 1
nonce=$(sed -n 's/^nonce //p' <<<"$g")
"$B/host" genesis "$U/stores/F" nano --nonce "$nonce" "$key" "$next" >/dev/null || exit 1
founder=$(sed -n 's/^founder 0 member //p' <<<"$g"); member=${founder%% grant *}; grant=${founder##* grant }
sup writer "$U/ws/host.sock" "$U/stores/W" "$B/host" serve "$U/stores/W"
sup follow "$U/ws/follow.sock" "$U/stores/F" "$B/host" follow "$U/stores/F" "$member" "$grant"
for _ in $(seq 100); do [ -S "$U/ws/host.sock" ] && [ -S "$U/ws/follow.sock" ] && break; sleep 0.1; done
for n in writer follow; do
  echo "unit $n: $(systemctl show -p ActiveState -p RestrictNamespaces -p ProtectKernelTunables -p ProcSubset \
    -p RestrictSUIDSGID -p MemoryDenyWriteExecute -p RestrictAddressFamilies -p MemoryMax -p LimitFSIZE \
    -p LimitNOFILE "nd-confined-$TAG-$n.service" | tr '\n' ' ')"
done
obj=$("$B/nd" create | sed -n 's/^id //p'); echo "create: $obj"
"$B/nd" write "$obj" 1 hello-from-the-unit >/dev/null && echo "write: ok"
echo "read: $("$B/nd" read "$obj")"
journal writer
for n in writer follow; do sudo -n systemctl stop "nd-confined-$TAG-$n.service" 2>/dev/null; done
