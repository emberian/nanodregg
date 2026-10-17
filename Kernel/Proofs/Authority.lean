/-
# Kernel.Proofs.Authority — who may do what, as theorems about `receive`

* A grant chain: `principalOf … (some g) = .ok p` means a chain of live, pinned grant links from
  `g`, each aimed at the object, held by the next agent and carrying the right, ending at a root
  whose issuer is `p` (`Chain`).
* `write` and `law` are admitted only for the object's owner, directly or through such a chain
  rooted at the owner (the row plant "receiver skips the grant check on write" breaks this).
* Every call but `rotate` is signed by its member's CURRENT key; `rotate` only to the
  PRECOMMITTED key.
-/
import Kernel.Proofs.Receive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A grant chain from `g` for `agent` reaching principal `p`. -/
inductive Chain (X : Ctx D) (look : Pinned D) (obj : D) (right : Right) : D → D → D → Prop
  | root {g agent issuer : D} {cell : Cell} :
      readKind look g kindGrant = .ok cell →
      slotDigest X g cell grantTarget = .ok obj →
      slotDigest X g cell grantGrantee = .ok agent →
      (cell.slots.get (rightKey right)).isSome = true →
      slotDigest X g cell grantIssuer = .ok issuer →
      cell.slots.get grantParent = none →
      Chain X look obj right g agent issuer
  | link {g agent issuer parent p : D} {cell : Cell} {pb : ByteArray} :
      readKind look g kindGrant = .ok cell →
      slotDigest X g cell grantTarget = .ok obj →
      slotDigest X g cell grantGrantee = .ok agent →
      (cell.slots.get (rightKey right)).isSome = true →
      slotDigest X g cell grantIssuer = .ok issuer →
      cell.slots.get grantParent = some pb →
      X.digestOf pb = some parent →
      Chain X look obj right parent issuer p →
      Chain X look obj right g agent p

omit [Ord D] in
theorem walk_chain {X : Ctx D} {look : Pinned D} {obj : D} {right : Right} :
    ∀ {fuel : Nat} {g agent p : D}, walk X look obj right fuel g agent = .ok p →
      Chain X look obj right g agent p
  | 0, _, _, _, h => by simp [walk] at h
  | fuel + 1, g, agent, p, h => by
      unfold walk at h
      simp only [except_bind_ok] at h
      obtain ⟨cell, hc, target, ht, ⟨⟩, hteq, grantee, hg, ⟨⟩, hgeq, ⟨⟩, hr, issuer, hi, h⟩ := h
      rw [req_ok, decide_eq_true_eq] at hteq hgeq
      rw [req_ok] at hr
      subst hteq; subst hgeq
      split at h
      · rename_i hp
        simp only [Except.ok.injEq] at h
        subst h
        exact .root hc ht hg hr hi hp
      · rename_i pb hp
        split at h
        · simp at h
        · rename_i parent hd
          exact .link hc ht hg hr hi hp hd (walk_chain h)

omit [Ord D] in
/-- **Write authority.** A derived `write` comes from the object's owner, or from an agent holding a
grant chain for `mutate` whose root issuer is the owner. -/
theorem write_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {obj : D}
    {edits : List (Nat × Option ByteArray)} {via : Option D} {t : Turn D}
    (h : write X look c obj edits via = .ok t) :
    ∃ cell owner, readKind look obj kindObject = .ok cell ∧
      slotDigest X obj cell slotOwner = .ok owner ∧
      (via = none ∧ c.unsigned.member = owner ∨
        ∃ g, via = some g ∧ Chain X look obj .mutate g c.unsigned.member owner) := by
  unfold write at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, _, _, ⟨⟩, _, principal, ha, _⟩ := h
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨cell, p, hc, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- **Law authority.** Replacing a data object's laws needs the same owner authority. -/
theorem law_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {obj : D} {laws : List D}
    {via : Option D} {t : Turn D} (h : law X look c obj laws via = .ok t) :
    ∃ cell owner, readKind look obj kindObject = .ok cell ∧
      slotDigest X obj cell slotOwner = .ok owner ∧
      (via = none ∧ c.unsigned.member = owner ∨
        ∃ g, via = some g ∧ Chain X look obj .mutate g c.unsigned.member owner) := by
  unfold law at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, _, _, ⟨⟩, _, principal, ha, _⟩ := h
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨cell, p, hc, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- **Current key.** Every derived call that is not a rotation is signed by a key its member cell
holds as current. -/
theorem key_current {X : Ctx D} {look : Pinned D} {c : Call D} {t : Turn D}
    (h : receiveWith X look c = .ok t) (hnr : ∀ k n, c.unsigned.body ≠ .rotate k n) :
    ∃ m, readKind look c.unsigned.member kindMember = .ok m ∧
      m.slots.get slotKey = some c.unsigned.key := by
  have hk := receiveWith_key h
  unfold keyRule at hk
  split at hk
  · rename_i k n hb; exact absurd hb (hnr k n)
  · unfold checkKey at hk
    split at hk
    · simp at hk
    · simp at hk
    · rename_i m hm
      exact ⟨m, hm, by simpa [req_ok] using hk⟩

omit [Ord D] in
/-- **Pre-rotation.** A derived rotation moves the member to a key whose digest it had
precommitted, and is signed by that key. -/
theorem rotate_precommitted {X : Ctx D} {look : Pinned D} {c : Call D} {key : ByteArray} {next : D}
    {t : Turn D} (h : rotate X look c key next = .ok t) :
    c.unsigned.key = key ∧ ∃ m, readKind look c.unsigned.member kindMember = .ok m ∧
      slotDigest X c.unsigned.member m slotNext = .ok (nextKeyDigest X key) := by
  unfold rotate at h
  simp only [except_bind_ok] at h
  obtain ⟨m, hm, ⟨⟩, hkey, committed, hc, ⟨⟩, heq, _⟩ := h
  rw [req_ok, decide_eq_true_eq] at hkey heq
  exact ⟨hkey, m, hm, heq ▸ hc⟩

end Nanodregg.Kernel.Receive
