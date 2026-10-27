# The system

Nanodregg is a shared World with one writer and members who check its history themselves. A member signs a call planned against its own view. The writer derives and judges the call, records an admitted turn or a recordable refusal, and serves the history. Followers re-derive each event before accepting the resulting World. The operator can read every byte in a World.

| Layer | Contract |
|---|---|
| [Kernel](../Kernel/World.lean) | Cells, accounts, grants, relations, authenticated roots, budgets and the transition for turns and recorded refusals. [Receive](../Kernel/Receive/Rederive.lean) connects signed calls to those transitions. |
| [Lang](../Lang/Program.lean) | Checked packages supply methods and laws. Imports and external reads use the caller's pinned view; evaluation spends a bounded tick allowance. |
| [Codec](../Codec/Stream.lean) | Canonical encodings, bounded decoders, digests and signatures give the other layers their bytes. |
| [Protocol](../Protocol/Command/Machine.lean) | Commands catch up, plan, request signatures and settle against the follower's own World. Invitations, receipts and heads describe what another party can check. |
| [Host](../Host/Store.lean) | One locked Store persists authenticated records and atomic bases. Bounded pages serve a base or log; a follower persists its own checked history. |
| [Client](../client/src/bin/nd.rs) | Rust holds member secrets, freezes signed attempts, transports frames and performs the steps Lean requests. |
| [Hosting](../Hosting/Resident/Run.lean) | World objects describe resident grains. Confined processes use member and broker sockets; the keybroker holds provider credentials. |
| [Ops and judge](JUDGE.md) | Rendered units operate the processes. A landing builds what it changed and runs what it touched; the periodic convergence report checks the whole. |

Objects run installed packages. Laws judge changes; relations hold bounded keyed rows. Activities, offers, escrow and generators are package constructions over these mechanisms. [OBJECTS](OBJECTS.md) connects them to executable journeys.

An accepted command is more than a writer reply: settlement is checked against the member's own journal and refusal roots. A thin joiner begins with a sponsor-pinned base; [TRUST](TRUST.md) explains that boundary, certificates and foreign receipts.

[Spec](../Spec/README.md) names the composed theorem claims, their premises and their floors. They do not imply secrecy from the operator, multiwriter consensus or an unconditional end-to-end durability or at-most-once guarantee.

Use [MEMBER](MEMBER.md) for commands, [OPERATING](OPERATING.md) for processes and recovery, and [TESTGROUND](TESTGROUND.md) for the browser system.
