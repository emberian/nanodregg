/-
# Protocol.Receipt — a receipt as proof: what happened to a call, shown against a head (PROTOCOL-45)

The head a member holds is its World's height and ROOTS digest (`World.roots`: the cells', the
journal's, the refusals' and the rows' roots, which every head link commits, KERNEL-47, KERNEL-48).
A RECEIPT for a transaction id carries the four roots and the trie paths that answer the id:

* `committed h td`: the journal holds `(h, td)` at the id (an inclusion path, KERNEL-41);
* `refused h code member`: the refusals hold the recorded refusal at `.tx id`, charged to `member`
  (KERNEL-44, KERNEL-50, PROTOCOL-41);
* `absent`: neither does (two exclusion paths). That is an answer only while `journalForgets` is
  false at the head's height for the call's `notBefore`; past it absence says nothing (`forgotten`).

`check` decides it against the head, trusting nothing the receipt states:
`Proofs.Receipt.check_committed` / `check_absent` / `check_refused_uncommitted` say a receipt that
checks against a World's roots tells the truth about that World's JOURNAL (the entry, its absence),
or the hash collides: a relay cannot turn a committed call into `absent` or `refused`, nor change
its entry. A `refused` receipt is the World's recorded refusal, its height, code and charged member, and an `absent`
one shows no refusal recorded either (`check_refused_sound`, `check_absent_unrefused`, through
KERNEL's refusals soundness, `Kernel.Proofs.RefusalsHead`). The head is the member's own folded World (its
height and roots together); a relayed head would need its height bound to the roots.

`build` is how a member's follow makes one from the World it folded (`receipt CALL`), and
`Protocol.Settle.ofReceipt` is how it settles the call from it (PROTOCOL-46; `check_build`: the
built receipt checks against the member's own head).
-/
import Kernel.World
import Codec.World
import Protocol.Command.Text
import Protocol.Table

namespace Nanodregg.Protocol.Receipt

open Nanodregg.Codec Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- What a receipt says happened to the call. -/
inductive Answer (D : Type)
  | committed (height : Nat) (turn : D)
  | refused (height code : Nat) (member : D)
  | absent
  deriving DecidableEq

structure Receipt (D : Type) where
  txId : D
  root : D
  jroot : D
  rroot : D
  rowsroot : D
  answer : Answer D
  jpath : Trie.Proof D D
  rpath : Trie.Proof (WindowSlot D) D

/-- Why a receipt does not answer (law 7). -/
inductive Refusal
  | badReceipt
  /-- the receipt is about another transaction id -/
  | otherTx
  /-- its roots are not the head's -/
  | headMismatch
  /-- a path does not verify for the answer it states -/
  | pathMismatch
  /-- `absent` past `journalForgets`: absence no longer says the call did not land -/
  | forgotten
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badReceipt => "badReceipt" | .otherTx => "otherTx" | .headMismatch => "headMismatch"
  | .pathMismatch => "pathMismatch" | .forgotten => "forgotten"

def Answer.text (dbytes : D → ByteArray) : Answer D → String
  | .committed h td => s!"committed {h} {Text.toHex (dbytes td)}"
  | .refused h code m => s!"refused {h} {code} {Text.toHex (dbytes m)}"
  | .absent => "absent"

/-- The answer's own check: its path verifies for what it states, and `absent` is not forgotten. -/
def answerOf (E : Env D) (height : Nat) (txId : D) (notBefore : Nat) (r : Receipt D) :
    Except Refusal (Answer D) :=
  match r.answer with
  | .committed h td =>
      if h < 2 ^ 64 ∧ Trie.verifyInclusion (journalSpec E) r.jroot txId (journalDigest E (h, td)) r.jpath = true
      then .ok (.committed h td) else .error .pathMismatch
  | .refused h code m =>
      -- recorded refused AND not committed: the journal path must show the id absent
      if h < 2 ^ 64 ∧ code < 2 ^ 64 ∧
          Trie.verifyInclusion (refusalSpec E) r.rroot (.refusal (.tx txId)) (refusalDigest E (.refused h code m)) r.rpath = true ∧
          Trie.verifyExclusion (journalSpec E) r.jroot txId r.jpath = true
      then .ok (.refused h code m) else .error .pathMismatch
  | .absent =>
      if journalForgets height notBefore = true then .error .forgotten
      else if Trie.verifyExclusion (journalSpec E) r.jroot txId r.jpath = true ∧
          Trie.verifyExclusion (refusalSpec E) r.rroot (.refusal (.tx txId)) r.rpath = true
      then .ok .absent else .error .pathMismatch

/-- THE decision: the receipt against the head (`height`, `roots`) for the call (`txId`,
`notBefore`). -/
def check (E : Env D) (height : Nat) (roots txId : D) (notBefore : Nat) (r : Receipt D) :
    Except Refusal (Answer D) :=
  if r.txId ≠ txId then .error .otherTx
  else if rootsDigest E r.root r.jroot r.rroot r.rowsroot ≠ roots then .error .headMismatch
  else answerOf E height txId notBefore r

/-- A receipt from a World: its roots, what it holds at the id, and both paths. -/
def build (E : Env D) (w : World D) (txId : D) : Receipt D :=
  let answer : Answer D := match w.journalAt E txId with
    | some (h, td) => .committed h td
    | none => match w.refusalAt E (.tx txId) with
      | some (.refused h code m) => .refused h code m
      | _ => .absent
  { txId, root := w.root E, jroot := w.journalRoot E, rroot := w.refusalsRoot E,
    rowsroot := w.rowsRoot E, answer,
    jpath := w.journal.prove (journalSpec E) txId, rpath := w.refusals.prove (refusalSpec E) (.refusal (.tx txId)) }

/-! ## Wire form

The two paths are CODEC's trie proof (`Codec.Kernel.proof`, KERNEL-49 (a)): each sibling with the bit
its node branches on, read back only when the bits ascend below the trie's depth. Every digest is
the digest codec's `dc` (deployed: `Codec.Deployed.digestCodec`). -/

def layout : Layout :=
  [.byte "answer", .u64 "a", .u64 "b", .bytes "turn", .bytes "txId", .bytes "root", .bytes "jroot",
   .bytes "rroot", .bytes "rowsroot", .bytes "jpath", .bytes "rpath"]

def frame : Stream (Layout.Ty Protocol.Bounds.frameBytesMax layout) :=
  Layout.codec Protocol.Bounds.frameBytesMax (by decide) layout

/-- The journal path's codec: keys and digests are transaction ids and digests. -/
def jproof (E : Env D) (dc : Stream D) : Stream (Trie.Proof D D) :=
  Codec.Kernel.proof (journalSpec E) dc dc

/-- The refusals path's codec: keys are refusals slots (`Codec.Kernel.refusalSlot`). -/
def rproof (E : Env D) (dc : Stream D) : Stream (Trie.Proof (WindowSlot D) D) :=
  Codec.Kernel.proof (refusalSpec E) (Codec.Kernel.refusalSlot dc) dc

def bytes (E : Env D) (dc : Stream D) (r : Receipt D) : Option ByteArray := do
  let f := Text.fit Protocol.Bounds.frameBytesMax
  let (tag, a, b, turn) : UInt8 × Nat × Nat × ByteArray := match r.answer with
    | .committed h td => (0, h, 0, dc.bytes td)
    | .refused h code m => (1, h, code, dc.bytes m)
    | .absent => (2, 0, 0, ByteArray.empty)
  pure (frame.bytes (tag, a.toUInt64, b.toUInt64, ← f turn, ← f (dc.bytes r.txId), ← f (dc.bytes r.root),
    ← f (dc.bytes r.jroot), ← f (dc.bytes r.rroot), ← f (dc.bytes r.rowsroot),
    ← f ((jproof E dc).bytes r.jpath), ← f ((rproof E dc).bytes r.rpath), ()))

def ofBytes (E : Env D) (dc : Stream D) (b : ByteArray) : Option (Receipt D) :=
  let dig (x : ByteArray) : Option D := (dc.decode x).toOption
  match frame.decode b with
  | .error _ => none
  | .ok (tag, a, bb, turn, tx, root, jroot, rroot, rowsroot, jp, rp, ()) => do
    let answer ← if tag = 0 then (dig turn.1).map (.committed a.toNat)
      else if tag = 1 then (dig turn.1).map (.refused a.toNat bb.toNat)
      else if tag = 2 then some .absent else none
    pure { txId := ← dig tx.1, root := ← dig root.1, jroot := ← dig jroot.1,
           rroot := ← dig rroot.1, rowsroot := ← dig rowsroot.1, answer,
           jpath := ← ((jproof E dc).decode jp.1).toOption,
           rpath := ← ((rproof E dc).decode rp.1).toOption }

end Nanodregg.Protocol.Receipt
