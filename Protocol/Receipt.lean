/-
# Protocol.Receipt — a receipt as proof: what happened to a call, shown against a head (PROTOCOL-45)

The head a member holds is its World's height and ROOTS digest (`World.roots`: the cells', the
journal's, the refusals' and the rows' roots, which every head link commits, KERNEL-47, KERNEL-48).
A RECEIPT for a transaction id carries the four roots and the trie paths that answer the id:

* `committed h td`: the journal holds `(h, td)` at the id (an inclusion path, KERNEL-41);
* `refused h code`: the refusals hold the recorded refusal at `.tx id` (KERNEL-44, PROTOCOL-41);
* `absent`: neither does (two exclusion paths). That is an answer only while `journalForgets` is
  false at the head's height for the call's `notBefore`; past it absence says nothing (`forgotten`).

`check` decides it against the head, trusting nothing the receipt states:
`Proofs.Receipt.check_committed` / `check_absent` / `check_refused_uncommitted` say a receipt that
checks against a World's roots tells the truth about that World's JOURNAL (the entry, its absence),
or the hash collides: a relay cannot turn a committed call into `absent` or `refused`, nor change
its entry. What a `refused` receipt says about the REFUSALS trie (the recorded height and code) is
only that its path verifies against the head's refusals root (`check_refused`): KERNEL states no
refusals-trie soundness yet (cv 01a14dfa-200a). The head is the member's own folded World (its
height and roots together); a relayed head would need its height bound to the roots.

`build` is how a member's follow makes one from the World it folded (`receipt CALL`), and
`Protocol.Settle.ofReceipt` is how it settles the call from it (PROTOCOL-46; `check_build`: the
built receipt checks against the member's own head).
-/
import Kernel.World
import Protocol.Command.Text
import Protocol.Table

namespace Nanodregg.Protocol.Receipt

open Nanodregg.Codec Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- What a receipt says happened to the call. -/
inductive Answer (D : Type)
  | committed (height : Nat) (turn : D)
  | refused (height code : Nat)
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
  rpath : Trie.Proof (RefusalSlot D) D

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
  | .refused h code => s!"refused {h} {code}"
  | .absent => "absent"

/-- The answer's own check: its path verifies for what it states, and `absent` is not forgotten. -/
def answerOf (E : Env D) (height : Nat) (txId : D) (notBefore : Nat) (r : Receipt D) :
    Except Refusal (Answer D) :=
  match r.answer with
  | .committed h td =>
      if h < 2 ^ 64 ∧ Trie.verifyInclusion (journalSpec E) r.jroot txId (journalDigest E (h, td)) r.jpath = true
      then .ok (.committed h td) else .error .pathMismatch
  | .refused h code =>
      -- recorded refused AND not committed: the journal path must show the id absent
      if Trie.verifyInclusion (refusalSpec E) r.rroot (.tx txId) (refusalDigest E (.refused h code)) r.rpath = true ∧
          Trie.verifyExclusion (journalSpec E) r.jroot txId r.jpath = true
      then .ok (.refused h code) else .error .pathMismatch
  | .absent =>
      if journalForgets height notBefore = true then .error .forgotten
      else if Trie.verifyExclusion (journalSpec E) r.jroot txId r.jpath = true ∧
          Trie.verifyExclusion (refusalSpec E) r.rroot (.tx txId) r.rpath = true
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
      | some (.refused h code) => .refused h code
      | _ => .absent
  { txId, root := w.root E, jroot := w.journalRoot E, rroot := w.refusalsRoot E,
    rowsroot := w.rowsRoot E, answer,
    jpath := w.journal.prove (journalSpec E) txId, rpath := w.refusals.prove (refusalSpec E) (.tx txId) }

/-! ## Wire form -/

def layout : Layout :=
  [.byte "answer", .u64 "a", .u64 "b", .bytes "turn", .bytes "txId", .bytes "root", .bytes "jroot",
   .bytes "rroot", .bytes "rowsroot", .byte "jterm", .list "jkeys", .list "jdigests", .list "jsibs",
   .byte "rterm", .list "rkeys", .list "rdigests", .list "rsibs"]

def frame : Stream (Layout.Ty Protocol.Bounds.frameBytesMax layout) :=
  Layout.codec Protocol.Bounds.frameBytesMax (by decide) layout

/-- A refusals key from its bytes (`refusalKeyBytes`'s inverse on its image). -/
def refusalKeyOf (digestOf : ByteArray → Option D) (b : ByteArray) : Option (RefusalSlot D) :=
  if h : 9 ≤ b.size then
    let mid := b.extract 1 (b.size - 8)
    let tail := b.extract (b.size - 8) b.size
    if b[0] = 0 then
      if tail = Stream.nat64.bytes 0 then (digestOf mid).map .tx else none
    else if b[0] = 1 then
      match Stream.u64.decode tail with
      | .ok win => (digestOf mid).map (.count · win)
      | .error _ => none
    else none
  else none

def proofParts {K : Type} (kb : K → ByteArray) (db : D → ByteArray) (p : Trie.Proof K D) :
    UInt8 × List ByteArray × List ByteArray × List ByteArray :=
  match p.term with
  | none => (0, [], [], p.sibs.map db)
  | some kds => (1, kds.map (kb ·.1), kds.map (db ·.2), p.sibs.map db)

def proofOf {K : Type} (ko : ByteArray → Option K) (digestOf : ByteArray → Option D)
    (t : UInt8) (ks ds ss : List ByteArray) : Option (Trie.Proof K D) := do
  let sibs ← ss.mapM digestOf
  if t = 0 then
    if ks.isEmpty && ds.isEmpty then pure ⟨none, sibs⟩ else none
  else if t = 1 then
    if ks.length = ds.length then pure ⟨some (← (ks.zip ds).mapM fun (k, d) => do pure (← ko k, ← digestOf d)), sibs⟩
    else none
  else none

def bytes (E : Env D) (r : Receipt D) : Option ByteArray := do
  let f := Text.fit Protocol.Bounds.frameBytesMax
  let fl := Text.fitList Protocol.Bounds.frameBytesMax
  let (tag, a, b, turn) : UInt8 × Nat × Nat × ByteArray := match r.answer with
    | .committed h td => (0, h, 0, E.bytes td)
    | .refused h code => (1, h, code, ByteArray.empty)
    | .absent => (2, 0, 0, ByteArray.empty)
  let (jt, jk, jd, js) := proofParts E.bytes E.bytes r.jpath
  let (rt, rk, rd, rs) := proofParts (refusalKeyBytes E) E.bytes r.rpath
  pure (frame.bytes (tag, a.toUInt64, b.toUInt64, ← f turn, ← f (E.bytes r.txId), ← f (E.bytes r.root),
    ← f (E.bytes r.jroot), ← f (E.bytes r.rroot), ← f (E.bytes r.rowsroot), jt, ← fl jk, ← fl jd, ← fl js, rt, ← fl rk, ← fl rd,
    ← fl rs, ()))

def ofBytes (digestOf : ByteArray → Option D) (b : ByteArray) : Option (Receipt D) :=
  match frame.decode b with
  | .error _ => none
  | .ok (tag, a, bb, turn, tx, root, jroot, rroot, rowsroot, jt, jk, jd, js, rt, rk, rd, rs, ()) => do
    let answer ← if tag = 0 then (digestOf turn.1).map (.committed a.toNat)
      else if tag = 1 then some (.refused a.toNat bb.toNat)
      else if tag = 2 then some .absent else none
    pure { txId := ← digestOf tx.1, root := ← digestOf root.1, jroot := ← digestOf jroot.1,
           rroot := ← digestOf rroot.1, rowsroot := ← digestOf rowsroot.1, answer,
           jpath := ← proofOf digestOf digestOf jt (Text.unlist jk) (Text.unlist jd) (Text.unlist js),
           rpath := ← proofOf (refusalKeyOf digestOf) digestOf rt (Text.unlist rk) (Text.unlist rd)
             (Text.unlist rs) }

end Nanodregg.Protocol.Receipt
