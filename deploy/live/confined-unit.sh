#!/bin/bash
# deploy/live/confined-unit.sh ROOT BIN [FILTER] [TAG] — the confinement under a service manager's own
# sandbox (CLIENT-48): `host serve` and a member's `host follow`, each under nd-supervise in a transient
# system unit carrying the demo box's FULL tenant hardening (RestrictNamespaces=yes,
# ProtectKernelTunables=yes, ProcSubset=pid, RestrictSUIDSGID=yes, MemoryDenyWriteExecute=yes, no
# network, the syscall filter), then `nd create`, `write`, `read` as the member. Each unit's state and
# the member's verdicts are printed. ROOT: a fresh directory with a clean custody chain (root-owned
# parents, no group or other write), e.g. `sudo install -d -o $USER -m 0755 /srv/nd-sbx`; it is
# emptied and refilled. BIN: host, nd and nd-supervise, outside /home (ProtectHome=yes). FILTER: the
# unit's SystemCallFilter (default `@system-service @sandbox`; `@system-service` alone shows the
# refusal by name, `confine: landlock is missing`). Needs `sudo -n systemd-run`. Units stop at the end.
set -u
S=${1:?ROOT}; B=${2:?BIN}; FILTER=${3:-"@system-service @sandbox"}; TAG=${4:-a}; U=$S/u
rm -rf "$U"; mkdir -p "$U/holding" "$U/stores" "$U/hide"; chmod 700 "$U" "$U/holding"
export ND_WORKSPACE=$U/ws ND_HOLDING=$U/holding
"$B/nd" --init || exit 1
keys=$("$B/nd" --keys); key=$(sed -n 's/^key //p' <<<"$keys"); next=$(sed -n 's/^next //p' <<<"$keys")
g=$("$B/host" genesis "$U/stores/W" nano "$key" "$next") || exit 1
nonce=$(sed -n 's/^nonce //p' <<<"$g")
"$B/host" genesis "$U/stores/F" nano --nonce "$nonce" "$key" "$next" >/dev/null || exit 1
founder=$(sed -n 's/^founder 0 member //p' <<<"$g"); member=${founder%% grant *}; grant=${founder##* grant }
PROPS=(-p Type=exec -p ProtectSystem=strict -p ReadWritePaths=$U -p ProtectHome=yes -p PrivateTmp=yes
  -p PrivateDevices=yes -p PrivateIPC=yes -p ProtectProc=invisible -p ProcSubset=pid
  -p ProtectKernelTunables=yes -p ProtectKernelModules=yes -p ProtectKernelLogs=yes
  -p ProtectControlGroups=yes -p ProtectClock=yes -p ProtectHostname=yes -p RestrictRealtime=yes
  -p RestrictSUIDSGID=yes -p LockPersonality=yes -p MemoryDenyWriteExecute=yes -p RemoveIPC=yes
  -p SystemCallArchitectures=native -p "SystemCallFilter=$FILTER" -p SystemCallErrorNumber=EPERM
  -p NoNewPrivileges=yes -p CapabilityBoundingSet= -p RestrictNamespaces=yes
  -p IPAddressDeny=any -p IPAddressAllow=localhost -p RestrictAddressFamilies=AF_UNIX
  -p UMask=0077 -p MemoryMax=256M -p TasksMax=64 --uid="$(id -u)" --gid="$(id -g)")
run() { # NAME SOCK STORE ARGS...
  local n=$1 sock=$2 st=$3; shift 3
  sudo -n systemd-run --unit="nd-confined-$TAG-$n" --collect "${PROPS[@]}" \
    "$B/nd-supervise" "$sock" --hide "$U/hide" --hide /home --write "$st" --exec "$B/host" -- "$B/host" "$@"
}
run writer "$U/ws/host.sock" "$U/stores/W" serve "$U/stores/W"
run follow "$U/ws/follow.sock" "$U/stores/F" follow "$U/stores/F" "$member" "$grant"
for _ in $(seq 100); do [ -S "$U/ws/host.sock" ] && [ -S "$U/ws/follow.sock" ] && break; sleep 0.1; done
for n in writer follow; do
  echo "unit $n: $(systemctl show -p ActiveState -p RestrictNamespaces -p ProtectKernelTunables -p ProcSubset \
    -p RestrictSUIDSGID -p MemoryDenyWriteExecute -p RestrictAddressFamilies "nd-confined-$TAG-$n.service" | tr '\n' ' ')"
done
obj=$("$B/nd" create | sed -n 's/^id //p'); echo "create: $obj"
"$B/nd" write "$obj" 1 hello-from-the-unit >/dev/null && echo "write: ok"
echo "read: $("$B/nd" read "$obj")"
sudo -n journalctl -q -u "nd-confined-$TAG-writer" --no-pager | grep -E 'nd-supervise|confine' | tail -3
for n in writer follow; do sudo -n systemctl stop "nd-confined-$TAG-$n.service" 2>/dev/null; done
