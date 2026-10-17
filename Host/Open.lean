/-
# Host.Open — what a Store opens to

    openLog s recordMax step w₀ initial log

reads the segment bytes after a base (`initial` is the tag they chain from, `w₀` the base's World)
with `Log.recover`, and folds every verifying record with `step` (for the Host: decode the batch
record and `World.admit` each Turn, then check the chain the record states). Nothing else
advances a World on open (HOST-14: there are no deltas).

* `corrupt off` — a frame verifies after bad bytes: acknowledged data follows, so the Store does
  not open and nothing is truncated (HOST-12);
* `record i f` — the `i`-th verifying record does not fold: written by a different build or a
  different kernel, refused by name, never skipped;
* otherwise the World, the frame count, where the valid bytes end, the tag to chain the next
  frame from, and `torn`: the bytes past `validLen` that are the one unsynced frame. The writer
  truncates them; a follower never does (it reads them as "not yet written").

The follower and the reopening writer run this same function: one open, one fold.

Theorems (`Host.Proofs.Open`): `open_encodeAll` (a clean segment opens to the fold of exactly the
records written), `open_torn` (a segment whose last frame was cut opens to the fold of the frames
before it, `torn` = the cut), and `open_sound` (for ANY bytes, the World opened is the fold of
records that are literally the bytes before `validLen`).
-/
import Host.Log

namespace Nanodregg.Host

/-- Why a Store does not open (law 7). -/
inductive OpenFault (F : Type) where
  /-- bad bytes at `offset` with a verifying frame after them -/
  | corrupt (offset : Nat)
  /-- the `index`-th verifying record does not fold -/
  | record (index : Nat) (fault : F)
  deriving Repr

structure Opened (W : Type) where
  world : W
  records : Nat
  validLen : Nat
  lastTag : ByteArray
  /-- the torn tail's length past `validLen` (0 when the segment ends clean) -/
  torn : Nat

variable {W F : Type}

/-- Fold the records in order; a refusal names the record's index. -/
def foldRecords (step : W → ByteArray → Except F W) : W → Nat → List ByteArray → Except (OpenFault F) W
  | w, _, [] => .ok w
  | w, i, r :: rs =>
    match step w r with
    | .ok w' => foldRecords step w' (i + 1) rs
    | .error f => .error (.record i f)

def tornOf : Log.Tail → Nat
  | .torn n => n
  | _ => 0

def openLog (s : Log.Sealer) (recordMax : Nat) (step : W → ByteArray → Except F W) (w₀ : W)
    (initial log : ByteArray) : Except (OpenFault F) (Opened W) :=
  let rv := Log.recover s recordMax initial log
  match rv.tail with
  | .corrupt off => .error (.corrupt off)
  | tail =>
    match foldRecords step w₀ 0 rv.records with
    | .ok w => .ok ⟨w, rv.records.length, rv.validLen, rv.lastTag, tornOf tail⟩
    | .error e => .error e

end Nanodregg.Host
