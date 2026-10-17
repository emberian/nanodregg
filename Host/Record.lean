/-
# Host.Record — a batch record: what one segment frame holds

    record = CODEC's `batch batchMax dc`: the batch's Turns, each with the World's ROOT after it

The writer encodes each Turn it staged with the root its World reached right after it (HOST-29:
`chainNext` commits the root, so a `log` page advances the chain from these pairs without
admitting anything). Open decodes the record and runs it with `runRooted`: each Turn is admitted
with the transition it trusts (the writer's and the follower's reopen: `World.admit`), and the
root it states is compared with the root of the World admission reached (a pair assertion, law 4).
So a record whose Turns and roots disagree is refused `rootMismatch` by name at its index, and no
root is ever taken on the writer's word. The chain after a record is then `chainOf` over its pairs
(`Kernel.RootedFold.chain`), so the record does not state it a second time.
-/
import Codec.World
import Host.Bounds

namespace Nanodregg.Host.Record

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- Why a record does not fold (law 7). -/
inductive Fault (F : Type) where
  | undecodable (r : Codec.Refusal)
  /-- the `index`-th Turn of the record is refused by the open's transition -/
  | turn (index : Nat) (f : F)
  /-- the `index`-th Turn admits, but the root the record states beside it is not the root the
  World reached (HOST-29) -/
  | rootMismatch (index : Nat)

def Fault.name {F : Type} : Fault F → String
  | .undecodable _ => "undecodable"
  | .turn _ _ => "turn"
  | .rootMismatch _ => "rootMismatch"

def codec (dc : Stream D) : Stream (List (Turn D × D)) := Nanodregg.Codec.Kernel.batch recordTurnsMax dc

/-- The record of `staged`: each admitted Turn with the root after it (`Machine.note`). -/
def encode (dc : Stream D) (staged : Array (Turn D × D)) : ByteArray :=
  (codec dc).bytes staged.toList

/-- Run a record's pairs from `w`: admit each Turn, and require the root stated beside it to be
`root` of the World admission reached. `i` is the index of the first pair. -/
def runRooted {F : Type} (admit : World D → Turn D → Except F (World D)) (root : World D → D) :
    Nat → World D → List (Turn D × D) → Except (Fault F) (World D)
  | _, w, [] => .ok w
  | i, w, (t, r) :: rest =>
    match admit w t with
    | .error f => .error (.turn i f)
    | .ok w' => if root w' = r then runRooted admit root (i + 1) w' rest else .error (.rootMismatch i)

/-- Decode one record, run it (`runRooted`), and return its pairs beside the World (what a tail
reports per batch, `Host.Tail`). -/
def stepTurns {F : Type} (dc : Stream D) (admit : World D → Turn D → Except F (World D))
    (root : World D → D) (w : World D) (r : ByteArray) : Except (Fault F) (World D × List (Turn D × D)) :=
  match (codec dc).decode r with
  | .error e => .error (.undecodable e)
  | .ok ps =>
    match runRooted admit root 0 w ps with
    | .error f => .error f
    | .ok w' => .ok (w', ps)

/-- One record run from `w`: `stepTurns`'s World. -/
def step {F : Type} (dc : Stream D) (admit : World D → Turn D → Except F (World D)) (root : World D → D)
    (w : World D) (r : ByteArray) : Except (Fault F) (World D) :=
  (stepTurns dc admit root w r).map Prod.fst

end Nanodregg.Host.Record
