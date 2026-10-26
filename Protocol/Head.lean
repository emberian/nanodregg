/-
# Protocol.Head — a World's position, and a member's attestation of its own (PROTOCOL-74; DESIGN-TRUST T1)

A HEAD is one World's position as every party states it: the World (its origin, KERNEL-24), its step
count (the chain's index, KERNEL-47), its height, its roots digest (what a receipt is checked
against, PROTOCOL-45) and its chain (what `fold_head_binds` binds: one `(steps, chain)` is one log).
Four spellings of it were in the tree (`logPage`'s pair, `receipt CALL`'s `head` line, `Std.head`'s
record, `host check`'s anchor); this is the one.

An ATTESTATION is a member's signed statement that its OWN follow's fold sits at a head: the head,
the member and its key, signed under `domHead` (the seventh signing domain, pairwise disjoint from
the six of `Protocol.Proofs.Domains`). It is not an authority: it says what one member holds, never
what the World is. Follow makes one at the tip of a catch-up (`nd sync --attest`: the message it
hands custody is its own World's head, `Command.attestTip`) and checks another member's
(`nd sync --check ATTEST`): the signature under the key it names, the World, and, on the World it
caught up to, that the key is the signer's CURRENT one (a rotated-away key is `staleKey`: an
attestation is checked under the signer's current key; rotate, then attest again).

The ANCHOR CHECK is the comparison (`anchorCheck`): as follow absorbs a page it advances the chain
over the page's steps, each with the roots digest after it (the record's shape, `Persist.steps`),
exactly as the kernel's `chainOf` does, and when the fold reaches the anchor's step count the chain
there must be the anchor's. Reaching it with another chain is `forked`: this member and the member
whose head that is hold two histories of one World (`Proofs.Head.forked_not_on_fold`); reaching it
with the same chain is `shared`: their logs agree up to that step, or two listed inputs collide
(`Proofs.Head.anchor_binds`, through `fold_head_binds`). The member that is BEHIND does the check: it
passes through the other's position on its way to the tip. One already past it answers `ahead` (its
World holds only the current chain; `host check STORE --anchor` on its own Store compares a past
position), and one whose writer's tip is below the anchor answers `unreached`.
-/
import Protocol.Envelope
import Protocol.Command.Text

namespace Nanodregg.Protocol.Head

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- One World's position. -/
structure Head (D : Type) where
  origin : D
  steps : Nat
  height : Nat
  roots : D
  chain : D
  deriving DecidableEq

/-- A World's own head. -/
def headOf (E : Env D) (w : World D) : Head D :=
  ⟨w.origin, w.steps, w.height, w.roots E, w.chain⟩

/-- The domain every attestation message begins with. -/
def domHead : ByteArray := "nanodregg/protocol/head/v1".toUTF8

/-- The signed part: the head's five fields, the member's id bytes and its key. -/
def unsignedLayout : Layout :=
  [.bytes "origin", .u64 "steps", .u64 "height", .bytes "roots", .bytes "chain", .bytes "member", .bytes "key"]

/-- An attestation on the wire: the signed bytes as carried, then the signature over them. -/
def attestationLayout : Layout := [.bytes "unsigned", .bytes "signature"]

def unsignedFrame : Stream (Layout.Ty Bounds.frameBytesMax unsignedLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) unsignedLayout

def attestationFrame : Stream (Layout.Ty Bounds.frameBytesMax attestationLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) attestationLayout

/-- The unsigned bytes of an attestation's fields, or `none` past the frame bound. -/
def unsignedBytes (E : Env D) (h : Head D) (member : D) (key : ByteArray) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (unsignedFrame.bytes (← f (E.bytes h.origin), h.steps.toUInt64, h.height.toUInt64,
    ← f (E.bytes h.roots), ← f (E.bytes h.chain), ← f (E.bytes member), ← f key, ()))

/-- What the member signs. -/
def message (unsigned : ByteArray) : ByteArray := domHead ++ unsigned

/-- An attestation's wire bytes, or `none` past the frame bound. -/
def bytes (unsigned signature : ByteArray) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (attestationFrame.bytes (← f unsigned, ← f signature, ()))

/-- A decoded attestation. -/
structure Attestation (D : Type) where
  head : Head D
  member : D
  key : ByteArray
  /-- the signed bytes exactly as carried (`unsignedFrame`) -/
  unsigned : ByteArray
  signature : ByteArray

/-- Why an attestation is not taken (law 7). -/
inductive Refusal
  /-- the bytes are not an attestation (either frame, or a digest field) -/
  | badAttestation
  /-- it names another World than the member's own -/
  | otherWorld
  /-- the signature does not verify over the bytes carried under the key they name -/
  | badHeadSignature
  /-- the member it names is not a live member of the World follow caught up to -/
  | notMember
  /-- the key it names is not that member's current key on the World follow caught up to -/
  | staleKey
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badAttestation => "badAttestation" | .otherWorld => "otherWorld"
  | .badHeadSignature => "badHeadSignature" | .notMember => "notMember" | .staleKey => "staleKey"

/-- The constructor's index, the thing a name must determine (`Proofs.Head.Refusal.name_injective`). -/
def Refusal.tag : Refusal → Nat
  | .badAttestation => 0 | .otherWorld => 1 | .badHeadSignature => 2 | .notMember => 3 | .staleKey => 4

def Refusal.all : List Refusal := [.badAttestation, .otherWorld, .badHeadSignature, .notMember, .staleKey]

/-- Decode the signed bytes, checking nothing they state. -/
def said (X : Ctx D) (u : ByteArray) : Option (Head D × D × ByteArray) :=
  match unsignedFrame.decode u with
  | .error _ => none
  | .ok (o, s, h, r, c, m, k, ()) => do
      pure (⟨← X.digestOf o.1, s.toNat, h.toNat, ← X.digestOf r.1, ← X.digestOf c.1⟩, ← X.digestOf m.1, k.1)

/-- Decode an attestation, checking nothing it states. -/
def ofBytes (X : Ctx D) (b : ByteArray) : Option (Attestation D) :=
  match attestationFrame.decode b with
  | .error _ => none
  | .ok (u, s, ()) => do
      let (h, m, k) ← said X u.1
      pure { head := h, member := m, key := k, unsigned := u.1, signature := s.1 }

/-- Decode and verify: the attestation is for `origin` and its signature verifies under the key it
names. Whether that key is the member's is `signer`'s question, asked on a caught-up World. -/
def verified (X : Ctx D) (origin : D) (b : ByteArray) : Except Refusal (Attestation D) :=
  match ofBytes X b with
  | none => .error .badAttestation
  | some a =>
    if a.head.origin ≠ origin then .error .otherWorld
    else if !X.verify a.key (message a.unsigned) a.signature then .error .badHeadSignature
    else .ok a

/-- On `w`, the attestation's member is live and the key it names is that member's current one. -/
def signer (X : Ctx D) (w : World D) (a : Attestation D) : Except Refusal Unit :=
  match currentKey X.env w a.member with
  | none => .error .notMember
  | some k => if k = a.key then .ok () else .error .staleKey

/-! ## The anchor check -/

/-- What walking a page's steps against an anchor finds. -/
inductive Anchored
  /-- the fold reached the anchor's step count with the anchor's chain -/
  | shared
  /-- the page ends before the anchor's step count (or began past it) -/
  | unreached
  /-- the fold reached the anchor's step count with ANOTHER chain -/
  | forked
  deriving DecidableEq, Repr

/-- From position `(s, c)`, advance the chain over the steps (each with the roots digest after it,
as `World.fold` stamps them: `stepLink`, `chainOf`) and compare at the anchor's step count. -/
def anchorCheck (E : Env D) (steps : Nat) (chain : ByteArray) : Nat → D → List (Kernel.Step D × D) → Anchored
  | _, _, [] => .unreached
  | s, c, (t, r) :: rest =>
      let c' := stepLink E c t r
      if s + 1 = steps then (if E.bytes c' = chain then .shared else .forked)
      else anchorCheck E steps chain (s + 1) c' rest

end Nanodregg.Protocol.Head
