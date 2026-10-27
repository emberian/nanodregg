/-
# Protocol.Health — the World's own measure of a member, as a receipt (DESIGN-OBS §1.5)

A member asks its World "how much of this window have I spent" and gets an answer it can hand to
anyone who holds the World's head. The answer is three counters of the window trie (KERNEL-50,
KERNEL-68), each read as the kernel's check of the member's NEXT act reads it:

* `ticks`: the ticks the member's admitted Turns spent in the window its next Turn lands in
  (`World.ticksUsed`: the key at `refusalWindow (height + 1)`, checked against `Bounds.ticksPerWindow`);
* `refusals`: the refusals recorded against the member in the window a refusal now lands in
  (`World.refusalCount`: the key at `refusalWindow height`, against `Bounds.refusalsPerWindow`);
* `total`: the World's recorded refusals in that window, all members together (`World.refusalTotal`,
  against `Bounds.refusalsPerWindowMax`).

A HEALTH RECEIPT carries the four roots the head's roots digest commits (as `Protocol.Receipt` does) and
one window-trie path per counter: an inclusion of the `count` leaf when the counter is positive, an
exclusion of its key when it is zero (the World holds no zero counter: `refusalFits` asks `1 ≤ n`).
`check` decides it against a `Protocol.Head` and the member asked about, trusting nothing the receipt
states: the windows are the HEAD's (its height), never the receipt's, so a relay cannot answer for a
window the head is not in. `Proofs.Health.check_sound`: a receipt that checks against a World's own head
states that World's three counters, or a listed input collides.

There is no signer. A member's own `receipt --health` reads its own fold, which IS the measurement (every
Turn's member and ticks re-derived by its follow); a party without the World checks the receipt against a
head whose provenance it already trusts — the member's own fold, a member's attestation
(`Head.Attestation`, T1), a certified head (`Head.Certificate`, T3) — and the receipt adds no authority
of its own (DESIGN-OBS §1.5: a "health signer" would be a fourth).
-/
import Protocol.Receipt
import Protocol.Head

namespace Nanodregg.Protocol.Health

open Nanodregg.Codec Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A counter of the window trie as the kernel's checks read it: the `count` leaf at `k`, or zero. -/
def countAt (E : Env D) (w : World D) (k : WindowSlot D) : Nat :=
  match w.refusals.get (refusalSpec E) k with
  | some (.count n) => n
  | _ => 0

/-- The member's meter key a World at `height` charges its next Turn to. -/
def ticksKey (m : D) (height : Nat) : WindowSlot D := .meter (.ticks m (refusalWindow (height + 1)))

/-- The member's refusal-count key a World at `height` records its next refusal under. -/
def countKey (m : D) (height : Nat) : WindowSlot D := .refusal (.count m (refusalWindow height))

/-- The World's refusal-total key at `height`. -/
def totalKey (origin : D) (height : Nat) : WindowSlot D := .refusal (.total origin (refusalWindow height))

/-- What a health receipt says: the member's three counters. -/
structure Answer where
  ticks : Nat
  refusals : Nat
  total : Nat
  deriving DecidableEq, Repr

structure Health (D : Type) where
  member : D
  root : D
  jroot : D
  rroot : D
  rowsroot : D
  answer : Answer
  tpath : Trie.Proof (WindowSlot D) D
  cpath : Trie.Proof (WindowSlot D) D
  opath : Trie.Proof (WindowSlot D) D

/-- Why a health receipt does not answer (law 7). -/
inductive Refusal
  /-- the bytes are not a health receipt -/
  | badHealth
  /-- it is about another member than the one asked about -/
  | otherMember
  /-- its roots are not the head's -/
  | headMismatch
  /-- a path does not verify for the counter it states, at the head's window -/
  | pathMismatch
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badHealth => "badHealth" | .otherMember => "otherMember" | .headMismatch => "headMismatch"
  | .pathMismatch => "pathMismatch"

/-- One counter's path: the `count n` leaf at `k` when `n` is positive, `k`'s absence when it is zero. -/
def counted (E : Env D) (rroot : D) (k : WindowSlot D) (n : Nat) (p : Trie.Proof (WindowSlot D) D) : Bool :=
  if n = 0 then Trie.verifyExclusion (refusalSpec E) rroot k p
  else decide (n < 2 ^ 64) && Trie.verifyInclusion (refusalSpec E) rroot k (refusalDigest E (.count n)) p

/-- THE decision: the receipt against the head, for member `m`. -/
def check (E : Env D) (h : Head.Head D) (m : D) (r : Health D) : Except Refusal Answer :=
  if r.member ≠ m then .error .otherMember
  else if rootsDigest E r.root r.jroot r.rroot r.rowsroot ≠ h.roots then .error .headMismatch
  else if counted E r.rroot (ticksKey m h.height) r.answer.ticks r.tpath = true ∧
      counted E r.rroot (countKey m h.height) r.answer.refusals r.cpath = true ∧
      counted E r.rroot (totalKey h.origin h.height) r.answer.total r.opath = true
  then .ok r.answer else .error .pathMismatch

/-- The member's three counters on a World, as its own fold holds them. -/
def answerOf (E : Env D) (w : World D) (m : D) : Answer :=
  ⟨countAt E w (ticksKey m w.height), countAt E w (countKey m w.height),
   countAt E w (totalKey w.origin w.height)⟩

/-- A health receipt from a World: its roots, the member's counters and their three paths. -/
def build (E : Env D) (w : World D) (m : D) : Health D :=
  { member := m, root := w.root E, jroot := w.journalRoot E, rroot := w.refusalsRoot E,
    rowsroot := w.rowsRoot E, answer := answerOf E w m,
    tpath := w.refusals.prove (refusalSpec E) (ticksKey m w.height),
    cpath := w.refusals.prove (refusalSpec E) (countKey m w.height),
    opath := w.refusals.prove (refusalSpec E) (totalKey w.origin w.height) }

/-- The word `receipt --health` prints the receipt's bytes under. -/
def word : String := "health"

/-- The three counters' text form, each with its bound and the window its key names. -/
def Answer.text (a : Answer) (height : Nat) : String :=
  s!"ticks {a.ticks} of {Bounds.ticksPerWindow} in window {(refusalWindow (height + 1)).toNat}\n" ++
  s!"refusals {a.refusals} of {Bounds.refusalsPerWindow} in window {(refusalWindow height).toNat}\n" ++
  s!"total {a.total} of {Bounds.refusalsPerWindowMax} in window {(refusalWindow height).toNat}\n"

/-! ## Wire form: the receipt's frame (`Protocol.Receipt`'s digest and path codecs) -/

def layout : Layout :=
  [.u64 "ticks", .u64 "refusals", .u64 "total", .bytes "member", .bytes "root", .bytes "jroot",
   .bytes "rroot", .bytes "rowsroot", .bytes "tpath", .bytes "cpath", .bytes "opath"]

def frame : Stream (Layout.Ty Protocol.Bounds.frameBytesMax layout) :=
  Layout.codec Protocol.Bounds.frameBytesMax (by decide) layout

def bytes (E : Env D) (dc : Stream D) (r : Health D) : Option ByteArray := do
  let f := Text.fit Protocol.Bounds.frameBytesMax
  let p := Receipt.rproof E dc
  if r.answer.ticks < 2 ^ 64 ∧ r.answer.refusals < 2 ^ 64 ∧ r.answer.total < 2 ^ 64 then
    pure (frame.bytes (r.answer.ticks.toUInt64, r.answer.refusals.toUInt64, r.answer.total.toUInt64,
      ← f (dc.bytes r.member), ← f (dc.bytes r.root), ← f (dc.bytes r.jroot), ← f (dc.bytes r.rroot),
      ← f (dc.bytes r.rowsroot), ← f (p.bytes r.tpath), ← f (p.bytes r.cpath), ← f (p.bytes r.opath), ()))
  else none

def ofBytes (E : Env D) (dc : Stream D) (b : ByteArray) : Option (Health D) :=
  let dig (x : ByteArray) : Option D := (dc.decode x).toOption
  let p := Receipt.rproof E dc
  match frame.decode b with
  | .error _ => none
  | .ok (t, c, o, m, root, jroot, rroot, rowsroot, tp, cp, op, ()) => do
    pure { member := ← dig m.1, root := ← dig root.1, jroot := ← dig jroot.1, rroot := ← dig rroot.1,
           rowsroot := ← dig rowsroot.1, answer := ⟨t.toNat, c.toNat, o.toNat⟩,
           tpath := ← (p.decode tp.1).toOption, cpath := ← (p.decode cp.1).toOption,
           opath := ← (p.decode op.1).toOption }

/-- Decode, then check: what a party holding head `h` does with a health receipt's bytes. -/
def checkBytes (E : Env D) (dc : Stream D) (h : Head.Head D) (m : D) (b : ByteArray) : Except Refusal Answer :=
  match ofBytes E dc b with
  | none => .error .badHealth
  | some r => check E h m r

end Nanodregg.Protocol.Health
