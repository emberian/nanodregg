/-
# Host.Record — a batch record: what one segment frame holds

    record = CODEC's `batch batchMax dc` of (the batch's Turns, the World's chain after them)

The writer encodes the Turns it staged and the chain its World reached. Open decodes the record,
advances its World through the Turns with the fold it trusts (the writer reopening:
`World.fold`; a follower: `Receive.audit`, which re-derives every Turn), and then checks the
stated chain against the one its own fold reached (a pair assertion, law 4). So a record whose
Turns and chain disagree is refused by name, and the chain is never taken on the writer's word.
-/
import Codec.World

namespace Nanodregg.Host.Record

open Nanodregg.Kernel Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- The most Turns one record holds: the loop's batch bound. -/
def turnsMax : Nat := 64

/-- Why a record does not fold (law 7). -/
inductive Fault (F : Type) where
  | undecodable (r : Codec.Refusal)
  /-- the `index`-th Turn of the record is refused by the open's fold -/
  | turn (index : Nat) (f : F)
  /-- the Turns fold, but not to the chain the record states -/
  | chainMismatch

def Fault.name {F : Type} : Fault F → String
  | .undecodable _ => "undecodable"
  | .turn _ _ => "turn"
  | .chainMismatch => "chainMismatch"

def codec (dc : Stream D) : Stream (List (Turn D) × D) := Nanodregg.Codec.Kernel.batch turnsMax dc

/-- The record of `staged`, admitted to reach `after`. -/
def encode (dc : Stream D) (after : World D) (staged : Array (Turn D)) : ByteArray :=
  (codec dc).bytes (staged.toList, after.chain)

/-- Fold one record with `advance` and check the chain it states. -/
def step {F : Type} (dc : Stream D) (advance : World D → List (Turn D) → Except (Nat × F) (World D))
    (w : World D) (r : ByteArray) : Except (Fault F) (World D) :=
  match (codec dc).decode r with
  | .error e => .error (.undecodable e)
  | .ok (ts, chain) =>
    match advance w ts with
    | .error (i, f) => .error (.turn i f)
    | .ok w' => if w'.chain = chain then .ok w' else .error .chainMismatch

end Nanodregg.Host.Record
