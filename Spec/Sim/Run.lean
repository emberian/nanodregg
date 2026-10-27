/-
# Spec.Sim.Run — the inputs of the deployed runs the floors and the inhabited facts compute

Keys from Ed25519 seeds, a genesis World with one founder, and the founder's signed calls against it
(a `rotate`, a `create`, an `issue`/`account`/`transfer`, a planned call, an envelope), each staged by
the writer's own `submit` at the deployed `Ctx`. Tooling (a `Sim` module, closure C9: no deployed
module imports it): what is computed of these is stated in `Spec.Proofs.Floor` (`native_decide`
facts) and everything else is kernel-checked from them.
-/
import Spec.Trivial
import Kernel.Sim.Deployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

abbrev Xd : Ctx Digest := Host.Deployed.X

def wSeed (t : String) : ByteArray := Kernel.Sim.Deployed.seed t.toUTF8

def wKey : ByteArray := Ed25519.publicKey (wSeed "f0")
def wNext : ByteArray := Ed25519.publicKey (wSeed "f0-next")

/-- One founder, its key and its precommitted next key. -/
def wGenesis : World Digest :=
  genesisWorld Xd "spec".toUTF8 "spec-0".toUTF8 100000000 [(wKey, nextKeyDigest Xd wNext)]
    Authority.none

def wMember : Digest := founderId Xd wGenesis.origin 0

/-- The founder rotates to its precommitted key, signed by that key (a rotate is signed by the key it moves to, `receiveWith_key`). -/
def wCall : Call Digest :=
  let u : Unsigned Digest :=
    { world := wGenesis.origin, member := wMember, key := wNext, notBefore := 0, validUntil := 101,
      pins := [(wMember, pinOf Xd.env (wGenesis.entry Xd.env wMember))], maxCharge := 1000000,
      body := .rotate wNext (nextKeyDigest Xd (Ed25519.publicKey (wSeed "f0-next-next"))) }
  ⟨u, Ed25519.sign (wSeed "f0-next") (Xd.callMessage u)⟩

/-- The log the writer stages for that call. -/
def wLog : List (Step Digest) :=
  match submit Xd wGenesis wCall with
  | .ok (t, _) => [.turn t]
  | .error _ => []

/-- A digest other than the zero one. -/
def oneDigest : Digest := ⟨⟨Array.replicate 32 1⟩, by simp [ByteArray.size]⟩

/-- The run's call with another next-key digest: the founder could have rotated either way. -/
def wCall2 : Call Digest :=
  let u : Unsigned Digest :=
    { wCall.unsigned with body := .rotate wNext (nextKeyDigest Xd (Ed25519.publicKey (wSeed "f0-other"))) }
  ⟨u, Ed25519.sign (wSeed "f0-next") (Xd.callMessage u)⟩

def wLog2 : List (Step Digest) :=
  match submit Xd wGenesis wCall2 with
  | .ok (t, _) => [.turn t]
  | .error _ => []

/-- No two distinct preimages in the list hash alike: `CollidesAmong`'s negation, as a computation. -/
def collisionFree (hash : String → ByteArray → Digest) (S : List (String × ByteArray)) : Bool :=
  S.all fun p => S.all fun q => decide (p = q ∨ hash p.1 p.2 ≠ hash q.1 q.2)

def wCb : ByteArray := Xd.callBytes wCall

/-- A settle-phase continuation carrying the run's call. -/
def wKb : ByteArray := (Command.State.bytes ⟨[], 4, [wCb]⟩).getD .empty

def mintDenom : ByteArray := "spec-mint".toUTF8

/-- A value cell of 10 units and no floor: a balance from nowhere. -/
def mintCell : Cell :=
  { kind := 0, discipline := .value,
    slots := [(Value.denomKey, mintDenom), (Value.balanceKey, Value.balanceBytes 10),
      (Value.floorKey, Value.floorBytes 0)] }

def tMint0 : Turn Digest :=
  { txId := oneDigest, notBefore := 0, validUntil := 10, touches := [], creates := [(oneDigest, mintCell)],
    nullifiers := [], charge := 0, event := .empty, member := oneDigest }

/-- The Turn that bears it, paying exactly its weight. -/
def tMint : Turn Digest := { tMint0 with charge := tMint0.weight }

/-- The founder creates a data object (no package, no laws) holding one state slot. -/
def oCreate : Call Digest :=
  let u : Unsigned Digest :=
    { world := wGenesis.origin, member := wMember, key := wKey, notBefore := 0, validUntil := 101,
      pins := [(wMember, pinOf Xd.env (wGenesis.entry Xd.env wMember))], maxCharge := 1000000,
      body := .create none [] [(stateBase, "x".toUTF8)] }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

/-- The World after the create, as the writer stages it. -/
def oLog : List (Step Digest) :=
  match submit Xd wGenesis oCreate with
  | .ok (t, _) => [.turn t]
  | .error _ => []

/-- The World the writer stages on that log. -/
def oWorld : World Digest :=
  match submit Xd wGenesis oCreate with
  | .ok (_, w) => w
  | .error _ => wGenesis

/-- The object it bore. -/
def oId : Digest := cellIdOf Xd.env (txIdOf Xd oCreate) 0

/-- The owner writes 32 bytes at edit key 0: under the kernel, state slot `stateBase`; under the raw
writer, the package slot. -/
def oWrite : Call Digest :=
  let u : Unsigned Digest :=
    { world := oWorld.origin, member := wMember, key := wKey, notBefore := 0, validUntil := 101,
      pins := [(wMember, pinOf Xd.env (oWorld.entry Xd.env wMember)), (oId, pinOf Xd.env (oWorld.entry Xd.env oId))],
      maxCharge := 1000000, body := .write oId [(slotPackage, some oneDigest.bytes)] none }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

/-- A law term and a package holding it: the claim's law premises, inhabited. -/
def law0 : Lang.Term := .lam .nat (.lam .nat (.lam .nat (.bool true)))

def pkg0 : Lang.Package :=
  { imports := [], state := .nat, iface := .nat, body := .record [("law", law0)], methods := [],
    laws := ["law"] }

def wMe : Command.Self Digest := ⟨oneDigest, oneDigest, oneDigest, 0⟩

/-- A `rotate` command at its settle phase, carrying the run's call. -/
def wKbS : ByteArray := (Command.State.bytes ⟨["rotate".toUTF8], 4, ["out".toUTF8, wCb]⟩).getD .empty

/-- The writer's word: `committed`. -/
def wRes : ByteArray := ⟨#[Attempt.Action.committed.code]⟩

/-- A reply that ends its command `ok`. -/
def okDone : Command.Reply → Bool
  | .done code _ _ => decide (code = CommandExit.ok.code.toUInt8)
  | _ => false

/-- The founder's other rotation with a one-height window: admissible at the genesis World. -/
def cExp : Call Digest :=
  let u : Unsigned Digest := { wCall2.unsigned with validUntil := 1 }
  ⟨u, Ed25519.sign (wSeed "f0-next") (Xd.callMessage u)⟩

/-- A `cancel CALL` command of the run's call. -/
def wKbC : ByteArray :=
  (Command.State.bytes ⟨["cancel".toUTF8, (Text.toHex wCb).toUTF8], 10, []⟩).getD .empty

/-- The founder's envelope for the log from height 0, under its own root grant, signed by its key. -/
def wEnvelope : Envelope Digest :=
  let grant := founderGrantId Xd wGenesis.origin 0
  { world := wGenesis.origin, member := wMember, grant, start := 0, notBefore := 0, validUntil := 10,
    key := wKey,
    signature := Ed25519.sign (wSeed "f0") (Envelope.message Xd wGenesis.origin wMember grant 0 0 10) }

def wFrame : Host.Frame := ⟨0, Protocol.Op.log.code, (Envelope.bytes Xd wEnvelope).getD .empty⟩

/-- A call of the founder (current key) against `w`, pinning `pins`. -/
def fCall (w : World Digest) (pins : List Digest) (b : Body Digest) : Call Digest :=
  let u : Unsigned Digest :=
    { world := w.origin, member := wMember, key := wKey, notBefore := 0, validUntil := 101,
      pins := (wMember :: pins).map fun c => (c, pinOf Xd.env (w.entry Xd.env c)), maxCharge := 1000000,
      body := b }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

/-- The World and Turn the writer stages for a call (the World unchanged if it refuses). -/
def staged (w : World Digest) (c : Call Digest) : World Digest × List (Step Digest) :=
  match submit Xd w c with
  | .ok (t, w') => (w', [.turn t])
  | .error _ => (w, [])

/-- The founder issues a well of 1000. -/
def vIssue : Call Digest := fCall wGenesis [] (.issue 1000)
def vWell : Digest := cellIdOf Xd.env (txIdOf Xd vIssue) 0
def vW1 : World Digest := (staged wGenesis vIssue).1

/-- The founder opens its own account of the well's denomination. -/
def vAccount : Call Digest := fCall vW1 [] (.account vWell wMember)
def vAcct : Digest := accountId Xd wMember vWell
def vW2 : World Digest := (staged vW1 vAccount).1

/-- The founder transfers 10 out of the well into the account. -/
def vTransfer : Call Digest := fCall vW2 [vWell, vAcct] (.transfer (.well vWell) (.of wMember vWell) 10 none none)

def vLog : List (Step Digest) :=
  (staged wGenesis vIssue).2 ++ (staged vW1 vAccount).2 ++ (staged vW2 vTransfer).2

/-- The founder as a member of the genesis World. -/
def sMe : Command.Self Digest := ⟨wGenesis.origin, wMember, founderGrantId Xd wGenesis.origin 0, 10⟩

/-- What follow plans at the genesis World for the founder's `issue 1000` (no signed reads). -/
def sU : Unsigned Digest :=
  match Command.plan Xd sMe wGenesis wKey {} (.issue 1000) with
  | .ok u => u
  | .error _ => wCall.unsigned

end Nanodregg.Spec
