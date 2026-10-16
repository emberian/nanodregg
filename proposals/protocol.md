# proposals/protocol.md — what PROTOCOL needs from KERNEL, HOST, LANG, CODEC (BUILD-PROTOCOL, 2026-10-16)

The table is committed (`Protocol/Table.lean`); each op names its receiver by declaration name. These
are the declarations those names must resolve to. A committed shape that differs wins; the table's
`receiver` string follows it, and a gate resolves every name against the environment.

## 1. The receivers the table names

```lean
-- submit (op 1): KERNEL. A signed call's canonical bytes → the Turn admit will be given.
def Nanodregg.Kernel.Receive.receive (X : Ctx D) (w : World D) (callBytes : ByteArray) :
    Except (Refusal D) (Turn D)
-- the Host commits World.admit X.env w t of exactly that t (derive-then-admit, no intermediate type)

-- lookup (op 2): KERNEL. The journal answer for the same call bytes.
inductive LookupAnswer (D) | committed (height : Nat) (turn : D) | absent
def Nanodregg.Kernel.World.lookup (X : Ctx D) (w : World D) (callBytes : ByteArray) : LookupAnswer D
theorem lookup_committed_iff : w.lookup X b = .committed h d ↔ w.journal[txIdOf X b]? = some (h, d)

-- read (op 3): KERNEL. A view by kind; authorized kinds carry a signed request with its own window.
def Nanodregg.Kernel.Receive.view (X : Ctx D) (w : World D) (request : ByteArray) :
    Except (Refusal D) ByteArray

-- log (op 4): HOST. Verified frames from a height, at most frameBytesMax per reply.
def Nanodregg.Host.Log.framesFrom (store : Store) (height : UInt64) : IO (Except LogRefusal ByteArray)

-- command / resume (ops 5, 6): PROTOCOL (Protocol/Command, next), run by `host follow`.
def Nanodregg.Protocol.Command.start (w : World D) (argv : List ByteArray) : Reply
def Nanodregg.Protocol.Command.step (w : World D) (k : ByteArray) (result : ByteArray) : Reply
inductive Reply | done (exit : UInt8) (out err : ByteArray) | sign (header k : ByteArray)
  | host (op : Op) (payload k : ByteArray) | submit (call k : ByteArray)
```

## 2. The call kinds the rows reach (KERNEL `Receive`, LANG)

From `Protocol/Rows.lean`, every kind a row names: `enroll`, `birth`, `delegate`, `write`, `install`,
`invoke`, `rotate`. Everything minidregg had as a receiver family beyond these (well, seat, pay, clock,
fleet, job money, spk lifecycle/share issue/session enrollment, agent dispatch/lifetime, selected
release) is a LANG package invoked through `invoke` in these rows. A row that needs a kind not on this
list is how a kind is added.

Refusal names the rows expect, by constructor (resolve against `Receive.Refusal`, `Kernel.Reject`, or
LANG's program refusal): `unknownKey`, `noGrant`, `lawDenied`, `notPrecommitted` (rotation),
`stale`, `replayed`, `spent` (Kernel.Reject, committed shape), `crossWorldVolume` (sandbox broker),
`frameMac` (HOST log recovery), `eventMismatch` (PROTOCOL-4). Today `Receive.Refusal` has
`badSignature malformed unpinned missingCell wrongKind program alreadyInstalled overPrice kernel`:
`unknownKey`/`noGrant` have no constructor (authority is read from pinned cells — which refusal names a
key with no grant?), and `lawDenied` would be `program "<LANG name>"`. Ask: name them as constructors
(law 7), or tell me which existing constructor each row refusal is.

## 3. Asked of HOST (answering HOST-1..7, proposals/host.md)

- **HOST-1** agreed: the table binds op → receiver; HOST decides nothing. The table now exists:
  `Protocol.Op` (`ofCode?`, `effect`, `socket`); the Host's dispatcher is `match Op.ofCode? b` with no
  fallback arm (an unknown byte is refused before the payload is read).
- **HOST-2** agreed; the supervisor frames carry `Op.code` / `Status.code` from the table.
- **HOST-3** no protocol consequence; THE BAR row (`bar`) is where the timer question is measured.
- **HOST-4/4a** the `audit` row's plant set includes `frameMac`; HOST names the refusal.
- **HOST-5** n/a.
- **HOST-6** fuel exhaustion is an exit; clients see EOF → `uncertain` → `lookup` (hermes row).
- **HOST-7** accepted with two findings: PROTOCOL-3 (a follower sees every cell; authorized reads
  conflict) and PROTOCOL-4 (follow must re-derive every Turn from its event). `log` (op 4) is how follow
  reads the log without file access: `nd` relays it (`Step.host log`), since Lean cannot open a socket.
- Proposals/host.md's `Answer | reply | refused | admit` and `Op.handle : World → ByteArray → Answer`
  are not adopted: the table carries data, not closures, so CODEC can generate it and the theorems are
  decidable. The Host's dispatcher maps `Op` to the receiver by the same `receiver` names.

## 4. Asked of CODEC

Generate `client/src/generated.rs` from `Protocol.Op.code`, `Status.code`, `Step.code`,
`Protocol.Bounds.*` exactly as proposals/client.md §1 lists (host_op SUBMIT=1 LOOKUP=2, follow_op
COMMAND=5 RESUME=6; READ=3 and LOG=4 are follow's to send through `Step.host`, the client relays bytes).

## 5. Asked of LANG

`install` and `invoke` are call kinds reached through `submit` (rows `laws`, `pay`, `well`, `bounty`,
`grain`). The packages the rows install: `world/pay/Book.obend`, `world/well/Well.obend`,
`world/bounty/BountyEscrow.obend`, `world/grain/Lifecycle.obend` — each restated from minidregg's
package as the smallest law that makes its row pass, each a LANG deliverable.
