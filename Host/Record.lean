/-
# Host.Record — a batch record: what one segment frame holds

    record = CODEC's `batch batchMax dc`: the batch's steps, each with the World's roots digest after it

A step is an admitted Turn or a recorded refusal (`Kernel.Step`, KERNEL-47). The writer encodes each
step it staged with the roots digest its World reached right after it (`World.roots`: one digest of
the cells', the journal's and the refusals' roots; HOST-29, KERNEL-41, KERNEL-47 amendment 3:
`stepLink` commits it, so a `log` page advances the chain from these pairs without admitting
anything). Open decodes the record and runs it with `runRooted`: each step is taken with the
transition it trusts (the writer's and the follower's reopen: `World.step`), and the digest it states
is compared with the roots of the World the step reached (a pair assertion, law 4). So a record
whose steps and roots disagree is refused `rootMismatch` by name at its index, and no root is ever
taken on the writer's word. The chain after a record is then `chainOf` over its pairs
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
  /-- the `index`-th step of the record (a Turn or a recorded refusal) is refused by the open's
  transition -/
  | step (index : Nat) (f : F)
  /-- the `index`-th step is taken, but the roots digest the record states beside it is not the one
  the World reached (HOST-29) -/
  | rootMismatch (index : Nat)

def Fault.name {F : Type} : Fault F → String
  | .undecodable _ => "undecodable"
  | .step _ _ => "step"
  | .rootMismatch _ => "rootMismatch"

def codec (dc : Stream D) : Stream (List (Step D × D)) := Nanodregg.Codec.Kernel.batch recordTurnsMax dc

/-- The record of `staged`: each step with the roots digest after it (`Machine.note`). -/
def encode (dc : Stream D) (staged : Array (Step D × D)) : ByteArray :=
  (codec dc).bytes staged.toList

/-- A World's position in its log: its STEP count and its chain (`Env.bytes`). The one `mark` every
Store's index, pages and restarts read (`Loop.Recorder.mark`), deployed and simulated alike: a
position in steps, not height, since a recorded refusal is a step at an unchanged height
(KERNEL-47 amendment 1, HOST-42). -/
def mark (E : Env D) (w : World D) : Nat × ByteArray := (w.steps, E.bytes w.chain)

/-- Run a record's pairs from `w`: take each step, and require the digest stated beside it to be
`root` (the deployed `World.roots`) of the World the step reached. `i` is the index of the first
pair. -/
def runRooted {F : Type} (step : World D → Step D → Except F (World D)) (root : World D → D) :
    Nat → World D → List (Step D × D) → Except (Fault F) (World D)
  | _, w, [] => .ok w
  | i, w, (t, r) :: rest =>
    match step w t with
    | .error f => .error (.step i f)
    | .ok w' => if root w' = r then runRooted step root (i + 1) w' rest else .error (.rootMismatch i)

/-- Decode one record, run it (`runRooted`), and return its pairs beside the World (what a tail
reports per batch, `Host.Tail`). -/
def stepTurns {F : Type} (dc : Stream D) (step : World D → Step D → Except F (World D))
    (root : World D → D) (w : World D) (r : ByteArray) : Except (Fault F) (World D × List (Step D × D)) :=
  match (codec dc).decode r with
  | .error e => .error (.undecodable e)
  | .ok ps =>
    match runRooted step root 0 w ps with
    | .error f => .error f
    | .ok w' => .ok (w', ps)

/-- One record run from `w`: `stepTurns`'s World. -/
def step {F : Type} (dc : Stream D) (step : World D → Step D → Except F (World D)) (root : World D → D)
    (w : World D) (r : ByteArray) : Except (Fault F) (World D) :=
  (stepTurns dc step root w r).map Prod.fst

end Nanodregg.Host.Record
