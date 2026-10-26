/-
# Spec.Trivial — the trivial systems the claims refuse

Each is `deployed d` with ONE field replaced by what a lazy implementation would do. They are the
other half of each claim's meaning: `Spec.Proofs.Floor` proves the claim false of each, so a claim
that held of every system would hold of these. (A def-module: the floors live in `Floor`.)
-/
import Spec.System

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-- The World a trusting follower is told: one admitted Turn more than it has steps, of another
World. -/
def told (w : World Digest) : World Digest :=
  { w with height := w.steps + 1, origin := Digest.zero }

/-- **The trusting follower**: it takes the World the Host's reply tells it, re-deriving nothing. -/
def trustingFollower (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f _ _ => ({ f with world := told f.world }, .steps [], .done 0 .empty .empty) }

/-- **The Host's-word follower**: every step ends its command `done ok` (the pre-PROTOCOL-64
machine's reading of a `committed` reply, without a settlement on follow's own World). -/
def hostWord (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    follow := fun _ f _ _ => (f, .steps [], .done CommandExit.ok.code.toUInt8 .empty .empty) }

/-- **The always-final settlement**: every call is `expired`. -/
def alwaysFinal (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with settle := fun _ _ _ => .expired }

/-- **The open host**: it answers every frame with a page of the log. -/
def openHost (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with handle := fun _ _ => .defer (.log 0) }

/-- **The chainless kernel**: it admits as the kernel does but never extends the log chain, so the
chain binds nothing that was folded. -/
def chainless (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    admit := fun w t => (World.admit Host.Deployed.X.env w t).map fun w' => { w' with chain := w.chain } }

/-- Every check `checkWith` runs but conservation (`checkValue`), in its order. -/
def checkMinting (E : Env Digest) (w : World Digest) (t : Turn Digest) :
    Except (Reject Digest) (List (Post Digest) × (Rows Digest × Nat)) := do
  checkBounds t
  checkWindow w t
  checkJournal E w t
  checkShape t
  let posts := (← mapEx (touchCheck E w) t.touches).reduceOption
  checkNullifiers E w t
  checkRowsRemain E w t
  checkRanges E w t
  let rr ← rowsRun E w t
  checkCharge w t (credit posts + rr.2)
  checkCreates E w t
  checkTicks E w t
  checkSteps w
  pure (posts, rr)

/-- **The minting kernel**: `World.admitImpl` without `checkValue`, so a Turn may bear or write value
its flows do not balance. -/
def minting (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    admit := fun w t => match checkMinting Host.Deployed.X.env w t with
      | .ok (posts, rr) => .ok (commitWith Host.Deployed.X.env w t posts rr)
      | .error r => .error r }

/-- Edits at the cell's raw slot keys (`applyEdits` without the `stateBase` offset). -/
def rawEdits (s : Slots) (edits : List (Nat × Option ByteArray)) : Slots :=
  edits.foldl (fun s e => match e.2 with
    | some v => s.set e.1 v
    | none => s.erase e.1) s

/-- A signed `write` derived by a receiver that treats the whole cell as state: the owner's authority
is checked, but the edits land at raw slot keys (the package, owner and law slots among them) and
no law judges them. -/
def rawWrite (X : Ctx Digest) (w : World Digest) (c : Call Digest) (obj : Digest)
    (edits : List (Nat × Option ByteArray)) (via : Option Digest) : Except (Refusal Digest) (Turn Digest) := do
  req (c.unsigned.world = w.origin) .wrongWorld
  let look := pinned X.env w c.unsigned.pins
  checkSignature X c
  checkKey look c.unsigned
  let cell ← readKind look obj kindObject
  let _ ← ownerAuthority X look c.unsigned.member obj cell .mutate via
  sealTurn X c [] (writeOf obj (diffOps cell.slots (rawEdits cell.slots edits))) []

/-- The kernel's receivers, except that a signed `write` is `rawWrite`. -/
def rawReceive (w : World Digest) (c : Call Digest) : Except (Refusal Digest) (Turn Digest) :=
  match c.unsigned.body with
  | .write obj edits via => rawWrite Host.Deployed.X w c obj edits via
  | _ => receive Host.Deployed.X w c

/-- **The raw writer**: a kernel whose `write` lets the owner rewrite every slot of its object. -/
def rawWriter (d : ByteArray → ByteArray) : System Digest := { deployed d with receive := rawReceive }

end Nanodregg.Spec
