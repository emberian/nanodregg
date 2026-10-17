/-
# Kernel.Proofs.Fold — what a log means, and why a follower can trust a head

`World.fold` is the follower and the reopening Host. The headline theorem, `chain_binds`: two
logs of the same length that reach the same chain from the same genesis are the same log, or
the hash has a collision — so a follower that checks one signed `(height, chain)` knows every
turn before it.
-/
import Kernel.Proofs.Admit

namespace Nanodregg.Kernel

section Chain
variable {D : Type}

/-- Two different inputs with one digest. -/
def Collision (hash : String → ByteArray → D) : Prop :=
  ∃ dom a b, a ≠ b ∧ hash dom a = hash dom b

theorem chainOf_concat {E : Env D} :
    ∀ {c : D} {l : List (Turn D)} {t : Turn D},
      chainOf E c (l ++ [t]) = chainNext E (chainOf E c l) t
  | c, [], t => rfl
  | c, x :: rest, t => by
      show chainOf E (chainNext E c x) (rest ++ [t]) = _
      rw [chainOf_concat]; rfl

theorem bytes_append_inj {x y x' y' : ByteArray} (h : x ++ y = x' ++ y') (hs : x.size = x'.size) :
    x = x' ∧ y = y' := by
  have hd : x.data ++ y.data = x'.data ++ y'.data := by
    rw [← ByteArray.data_append, ← ByteArray.data_append, h]
  obtain ⟨h₁, h₂⟩ := Array.append_inj hd hs
  exact ⟨ByteArray.ext h₁, ByteArray.ext h₂⟩

/-- One chain step determines its predecessor and its turn, or exhibits a collision. -/
theorem chainNext_inj {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : Function.Injective E.turnBytes)
    {c₁ c₂ : D} {t₁ t₂ : Turn D} (h : chainNext E c₁ t₁ = chainNext E c₂ t₂) :
    (c₁ = c₂ ∧ t₁ = t₂) ∨ Collision E.hash := by
  unfold chainNext at h
  by_cases hin : E.bytes c₁ ++ E.bytes (turnDigest E t₁) =
      E.bytes c₂ ++ E.bytes (turnDigest E t₂)
  · obtain ⟨hc, hd⟩ := bytes_append_inj hin (by simp [hsz])
    have hc' := hb hc
    have hd' := hb hd
    unfold turnDigest at hd'
    by_cases hti : E.turnBytes t₁ = E.turnBytes t₂
    · exact Or.inl ⟨hc', ht hti⟩
    · exact Or.inr ⟨_, _, _, hti, hd'⟩
  · exact Or.inr ⟨_, _, _, hin, h⟩

/-- **Follower soundness.** Two logs of one length that reach one chain from one start are one
log, or the hash collides. With `fold_chain` and `fold_height`: a follower holding a trusted
`(height, chain)` holds the only log that produces it. -/
theorem chain_binds {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : Function.Injective E.turnBytes) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Turn D)), l₁.length = k → l₂.length = k →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ Collision E.hash
  | 0, l₁, l₂, h₁, h₂, _ => by
      rw [List.length_eq_zero_iff] at h₁ h₂; subst h₁; subst h₂; exact Or.inl rfl
  | k + 1, l₁, l₂, h₁, h₂, h => by
      rcases List.eq_nil_or_concat l₁ with rfl | ⟨a₁, t₁, rfl⟩
      · simp at h₁
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨a₂, t₂, rfl⟩
      · simp at h₂
      simp only [List.concat_eq_append] at h h₁ h₂ ⊢
      rw [chainOf_concat, chainOf_concat] at h
      rcases chainNext_inj hsz hb ht h with ⟨hc, rfl⟩ | hcol
      · simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h₁ h₂
        rcases chain_binds hsz hb ht k a₁ a₂ h₁ h₂ hc with rfl | hcol
        · exact Or.inl rfl
        · exact Or.inr hcol
      · exact Or.inr hcol

end Chain

variable {D : Type} [Ord D] [DecidableEq D]

theorem fold_cons_ok {E : Env D} {w w'' : World D} {t : Turn D} {rest : List (Turn D)} :
    World.fold E w (t :: rest) = .ok w'' ↔
      ∃ w', World.admit E w t = .ok w' ∧ World.fold E w' rest = .ok w'' := by
  conv => lhs; unfold World.fold
  cases ha : World.admit E w t with
  | error r => simp
  | ok w' =>
      cases hf : World.fold E w' rest with
      | error e => obtain ⟨i, r⟩ := e; simp [hf]
      | ok v => simp [hf]

/-- A log's fold is the fold of its pieces: restart from any admitted prefix is sound. -/
theorem fold_append {E : Env D} :
    ∀ {w w'' : World D} {l₁ l₂ : List (Turn D)},
      World.fold E w (l₁ ++ l₂) = .ok w'' ↔
        ∃ w', World.fold E w l₁ = .ok w' ∧ World.fold E w' l₂ = .ok w''
  | w, w'', [], l₂ => by simp [World.fold]
  | w, w'', t :: rest, l₂ => by
      rw [List.cons_append, fold_cons_ok]
      constructor
      · rintro ⟨w₁, h₁, h₂⟩
        obtain ⟨w', h₃, h₄⟩ := (fold_append (l₁ := rest)).mp h₂
        exact ⟨w', fold_cons_ok.mpr ⟨w₁, h₁, h₃⟩, h₄⟩
      · rintro ⟨w', h₁, h₂⟩
        obtain ⟨w₁, h₃, h₄⟩ := fold_cons_ok.mp h₁
        exact ⟨w₁, h₃, (fold_append (l₁ := rest)).mpr ⟨w', h₄, h₂⟩⟩

theorem fold_height {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w'.height = w.height + l.length
  | w, w', [], h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_height h₂, admit_height h₁]; simp; omega

theorem fold_chain {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w'.chain = chainOf E w.chain l
  | w, w', [], h => by simp [World.fold] at h; subst h; rfl
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      rw [fold_chain h₂, admit_chain h₁]; rfl

/-- **Charge exactness over a log.** The budget falls by exactly the sum of the charges, and
each charge is its turn's weight. -/
theorem fold_charge {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w'.allowance + (l.map Turn.charge).sum = w.allowance ∧ ∀ t ∈ l, t.charge = t.weight
  | w, w', [], h => by simp [World.fold] at h; subst h; simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨ih₁, ih₂⟩ := fold_charge h₂
      obtain ⟨c₁, _, c₃⟩ := admit_charge h₁
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]; omega
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact c₁
        · exact ih₂ x hx

/-- The follower's theorem in its usable form: same start, same head after folding, same log
(or a collision). -/
theorem fold_head_binds {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : Function.Injective E.turnBytes)
    {g w₁ w₂ : World D} {l₁ l₂ : List (Turn D)}
    (h₁ : World.fold E g l₁ = .ok w₁) (h₂ : World.fold E g l₂ = .ok w₂)
    (hh : w₁.height = w₂.height) (hc : w₁.chain = w₂.chain) :
    l₁ = l₂ ∨ Collision E.hash := by
  have hl : l₁.length = l₂.length := by
    have := fold_height h₁; have := fold_height h₂; omega
  rw [fold_chain h₁, fold_chain h₂] at hc
  exact chain_binds hsz hb ht l₁.length l₁ l₂ rfl hl.symm hc

/-- `World.fold` is the monadic left fold of `World.admit` (HOST's `staged_foldlM` carries over). -/
theorem fold_foldlM {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)},
      World.fold E w l = .ok w' ↔ l.foldlM (World.admit E) w = .ok w'
  | w, w', [] => by simp [World.fold, List.foldlM, pure, Except.pure]
  | w, w', t :: rest => by
      rw [fold_cons_ok, List.foldlM_cons]
      cases ha : World.admit E w t with
      | error r => simp [bind, Except.bind]
      | ok w₁ => simp [bind, Except.bind, fold_foldlM]

/-- An admitted turn lands inside its window. -/
theorem admit_window {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : t.notBefore ≤ w.height + 1 ∧ w.height + 1 ≤ t.validUntil := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have hw := hc.window
  unfold checkWindow at hw
  rw [req_ok] at hw
  simpa using hw

/-- **`absent` becomes final by expiry (HOST-8).** If the journal of `w` lacks `k` and some later
World of an admitted log has it, a turn of that log carries `k` and a window still open after
`w`: its `validUntil` exceeds `w.height`. So once `w.height ≥ v`, a transaction whose signed window
ends at `v` and is absent stays absent, unless another call with a LATER window has the same
transaction id — two different signed calls with one digest (`txIdOf`), a collision. -/
theorem absent_final [Std.TransOrd D] [Std.LawfulEqOrd D] {E : Env D} {k : D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w.journal[k]? = none → w'.journal[k]? ≠ none →
        ∃ t ∈ l, t.txId = k ∧ w.height < t.validUntil
  | w, w', [], h, ha, hj => by simp [World.fold] at h; subst h; exact absurd ha hj
  | w, w', t :: rest, h, ha, hj => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hwin := (admit_window h₁).2
      by_cases hk : t.txId = k
      · exact ⟨t, by simp, hk, by omega⟩
      · have ha₁ : w₁.journal[k]? = none := by
          obtain ⟨_, _, rfl⟩ := admit_ok h₁
          show (w.journal.insert t.txId _)[k]? = none
          rw [Std.TreeMap.getElem?_insert]
          have : compare t.txId k ≠ .eq := fun he => hk (Std.LawfulEqCmp.eq_of_compare he)
          simp [this, ha]
        obtain ⟨u, hu, huk, hlt⟩ := absent_final h₂ ha₁ hj
        exact ⟨u, by simp [hu], huk, by rw [admit_height h₁] at hlt; omega⟩

end Nanodregg.Kernel
