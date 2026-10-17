
### broker.sh on burst5-a (OPS-3, 2026-10-17 18:04–18:07Z, systemd 255, bundle bf1839b, taskset 0-1)

Run 1: FAIL 2. keybroker-unit-starts and decider-killed-is-restarted failed: the journal said
`bwrap: loopback: Failed to create NETLINK_ROUTE socket: Address family not supported by protocol`,
then `keybroker: deciderEnded 1`, a restart-class status 1 at every start until the start limit. The
unit's `RestrictAddressFamilies=AF_UNIX AF_INET AF_INET6` forbade the netlink socket that
`bwrap --unshare-net` needs to bring the decider sandbox's loopback up. Fixed in the renderer
(AF_NETLINK added; deploy/units/linux/nd-keybroker.service re-rendered). Not predicted: the decider's
mechanism failure surfaces as `deciderEnded 1`, a code no table names (sent to HOSTING).
Run 2 (the fixed renderer): ALL PASS.

```
ROW keybroker-unit-starts PASS :: active; socket 660 1001 dir 2710; decider pid 3100907 exe /usr/local/libexec/nd-bwrap; NoNewPrivileges=yes
ROW decider-killed-is-restarted PASS :: SIGKILL decider pid 3100907; Main process exited, code=exited, status=102 (deciderSignaled 102); NRestarts 0 -> 1; new decider 3100952
ROW anchors-edited-refused-at-start PASS :: Result=exit-code; start limit hit; journal: emit-anchors: /srv/scratch/ops3-live/run1/etc/anchors.pem differs from webpki-root-certs' pinned roots; regenerate it
ROW key-mode-0644-stops PASS :: ExecMainStatus=84 (keyFileMode) NRestarts=0 exit-code
ROW sockdir-mode-stops PASS :: ExecMainStatus=105 (sockDir) NRestarts=0, no socket
ROW hosted-follower-starts PASS :: active; socket 660 1001 (--group)
ROW grain-launch-starts PASS :: active after 10 s, NRestarts=0, MainPID 3101211
ROW controller-store-refusal-stops PASS :: ExecMainStatus=109 (controller store, passed through) NRestarts=0
```

The anchors row's journal check was re-verified against run 2's own lines (five
`run2/etc/anchors.pem differs` refusals, then the start limit); broker.sh now reads the journal
`--since` its own start. Undone at 18:07:40Z (BURST5-UP-LOG §8).
