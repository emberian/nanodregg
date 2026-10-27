# Operating a World

The [RUNBOOK](../deploy/RUNBOOK.md) contains installation/recovery detail. [Host.Cli](../Host/Cli.lean) defines the grammar; [units](../deploy/units/linux) and [exit tables](../deploy/units/EXITS.md) are generated from [Ops.Units](../Ops/Units.lean). Uppercase arguments below stand for operator-supplied values.

| Operation | Form and responsibility |
|---|---|
| Genesis | host genesis STORE NAME [--nonce HEX32] [--certifier HEX32]... [--threshold N] [KEY_HEX NEXT_HEX]... checks founders, authority and budget before creation. Founders independently check the inputs. |
| Writer | host serve STORE [--retain N] serves framed requests. The key-file handle holds the writer lock. Default retention keeps history; an explicit count must meet the floor. |
| Follower | host follow STORE MEMBER_HEX GRANT_HEX owns a separate writable Store and executes member commands. |
| Join | host join STORE INVITE_HEX KEY_HEX [IN] authenticates the invitation under the trusted sponsor key. IN is for a carried invitation. |
| Inspect | host check STORE [--anchor STEPS:CHAIN_HEX] checks history against a held position. The anchor counts steps, not heights. |
| Seal | host seal STORE [--retain N] seals a stopped Store. |
| Carry | host export STORE OUT exports a stopped Store and prints its authority. Host import takes STORE NAME IN with either --digest HEX and optional --nonce HEX32, or --origin HEX with --nonce HEX32, and states the authority: --certifier HEX32... --threshold N, or --uncertified. Stating none under a certifying World is refused authorityUnstated. Preserve the checked export pin. RUNBOOK §6. |

nd-supervise confines the child and multiplexes bounded socket connections onto framed stdio. Policy grants Store writes and executable access while hiding custody roots. Linux needs the fixed sandbox mechanism and its installation permissions; absence has no permissive fallback.

| Unit | Role |
|---|---|
| nd-host-serve.service | Writer under nd. |
| nd-host-follow.service | Personal follower; its own Store and hidden workspace/holding directories. |
| nd-hosted-follow@.service | Hosted follower under nd-hosted; shared socket group for its driver. |
| nd-follow-drive@.service | nd sync under nd; Restart=always, forty-second interval, except its fatal refusal class. |
| nd-keybroker.service | Provider keys, anchors and pins under nd; confined Lean decider. |
| nd-members@.service | World resident decider and managed follower/member children. |
| nd-grain-launch@.service | Controller and confined grains under nd-hosted. |

nd-members separates member sockets, custody, follower state and follower sockets. Launcher roots must also be disjoint. Ownership, modes and directory chains are checked; a matching path is insufficient. Rendered tmpfiles/sysusers definitions supply identities and modes.

A resident sees its package, writable volume and own member/broker sockets. It reads the Bell, keeps intent before asking, persists the answer before submitting and settles delivery through its member. The broker checks provider policy and custody; the provider secret does not enter the resident volume.

Uncertain is an unknown outcome: use member settlement. Do not invent missing Store files or start a second writer. The [Store layout](../deploy/units/STORE.md) gives backup order: key, atomic base, index, segments. Preserve the backup together and check the restored Store against a held steps/chain anchor. Retention can make older anchors unavailable.

The optional base.cert sidecar is self-authenticating to its consumer, not a replacement for the base/log. [TRUST](TRUST.md) explains the producer boundary.

## Durability and recovery

One host serve process holds the Store. Requests queue while a sync runs and become the next batch, so a batch is one frame and there is no batching timer. Each batch frame is appended and synced before any of its replies leave. No reply reports a state a crash can take back.

A failed append or sync is never retried, because the kernel may have dropped the dirty pages. Every reply of that batch is uncertain, the process exits with a restart-class status, and the next open decides what is on disk.

Open reads the base, then the segment frame by frame. The first incomplete frame or frame that fails its tag ends the log. Only the last frame can be torn, because each batch is synced before the next is written. Bytes after the last good frame are truncated as a torn tail only if they are no longer than one frame and no frame verifies anywhere after them. A verifying frame after bad bytes means acknowledged data follows, and open refuses with storeCorrupt instead of truncating. A corruption inside the last frame reads as torn: the height goes back for the client holding that receipt.

The supervisor owns the socket and parses no payload. It routes each reply to its connection by number and drops a reply it cannot route. The client recovers with lookup.
