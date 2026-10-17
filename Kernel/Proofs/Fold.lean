/-
# Kernel.Proofs.Fold — what a log means, and why a follower can trust a head

`World.fold` is the follower and the reopening Host. The headline theorem, `chain_binds`: two
logs of the same length that reach the same chain from the same genesis are the same log, or
the hash has a collision — so a follower that checks one signed `(height, chain)` knows every
turn before it.
-/
import Kernel.Proofs.Admit
import Kernel.Proofs.Bytes

namespace Nanodregg.Kernel

section Chain
variable {D : Type}

/-- Two different inputs with one digest. -/
def Collision (hash : String → ByteArray → D) : Prop :=
  ∃ dom a b, a ≠ b ∧ hash dom a = hash dom b

/-- `E.turnBytes` is injective on the turns `checkBounds` passes. That is what the deployed codec
proves (`Codec.Proofs.Deployed.turnBytes_injective`). Over ALL turns it is false there: `nat64`
truncates a counter past 2^64, so two turns that differ only in such a counter share their bytes.
No theorem here assumes the unrestricted form. -/
def TurnBytesInjOn [Ord D] (E : Env D) : Prop :=
  ∀ {t t' : Turn D}, checkBounds t = .ok () → checkBounds t' = .ok () →
    E.turnBytes t = E.turnBytes t' → t = t'

theorem chainOf_concat {E : Env D} :
    ∀ {c : D} {l : List (Turn D × D)} {t : Turn D} {r : D},
      chainOf E c (l ++ [(t, r)]) = chainNext E (chainOf E c l) t r
  | c, [], t, r => rfl
  | c, (x, rx) :: rest, t, r => by
      show chainOf E (chainNext E c x rx) (rest ++ [(t, r)]) = _
      rw [chainOf_concat]; rfl

/-- One chain step between bounded turns determines its predecessor, its turn and the root after
it, or exhibits a collision. -/
theorem chainNext_inj [Ord D] {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : TurnBytesInjOn E)
    {c₁ c₂ r₁ r₂ : D} {t₁ t₂ : Turn D} (hb₁ : checkBounds t₁ = .ok ()) (hb₂ : checkBounds t₂ = .ok ())
    (h : chainNext E c₁ t₁ r₁ = chainNext E c₂ t₂ r₂) :
    (c₁ = c₂ ∧ t₁ = t₂ ∧ r₁ = r₂) ∨ Collision E.hash := by
  unfold chainNext at h
  by_cases hin : E.bytes c₁ ++ E.bytes (turnDigest E t₁) ++ E.bytes r₁ =
      E.bytes c₂ ++ E.bytes (turnDigest E t₂) ++ E.bytes r₂
  · obtain ⟨hct, hr⟩ := bytes_append_inj hin (by simp [hsz])
    obtain ⟨hc, hd⟩ := bytes_append_inj hct (by simp [hsz])
    have hc' := hb hc
    have hd' := hb hd
    unfold turnDigest at hd'
    by_cases hti : E.turnBytes t₁ = E.turnBytes t₂
    · exact Or.inl ⟨hc', ht hb₁ hb₂ hti, hb hr⟩
    · exact Or.inr ⟨_, _, _, hti, hd'⟩
  · exact Or.inr ⟨_, _, _, hin, h⟩

/-- **Follower soundness.** Two logs of one length that reach one chain from one start are one
log with one root after every turn, or the hash collides, provided every turn of both logs is
bounded (an admitted turn always is: `fold_bounded`). With `fold_chain` and `fold_height`: a
follower holding a trusted `(height, chain)` holds the only log that produces it. -/
theorem chain_binds [Ord D] {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : TurnBytesInjOn E) {c : D} :
    ∀ (k : Nat) (l₁ l₂ : List (Turn D × D)), l₁.length = k → l₂.length = k →
      (∀ p ∈ l₁, checkBounds p.1 = .ok ()) → (∀ p ∈ l₂, checkBounds p.1 = .ok ()) →
      chainOf E c l₁ = chainOf E c l₂ → l₁ = l₂ ∨ Collision E.hash
  | 0, l₁, l₂, h₁, h₂, _, _, _ => by
      rw [List.length_eq_zero_iff] at h₁ h₂; subst h₁; subst h₂; exact Or.inl rfl
  | k + 1, l₁, l₂, h₁, h₂, hl₁, hl₂, h => by
      rcases List.eq_nil_or_concat l₁ with rfl | ⟨a₁, ⟨t₁, r₁⟩, rfl⟩
      · simp at h₁
      rcases List.eq_nil_or_concat l₂ with rfl | ⟨a₂, ⟨t₂, r₂⟩, rfl⟩
      · simp at h₂
      simp only [List.concat_eq_append] at h h₁ h₂ hl₁ hl₂ ⊢
      rw [chainOf_concat, chainOf_concat] at h
      rcases chainNext_inj hsz hb ht (hl₁ _ (List.mem_append_right _ (List.mem_singleton_self _)))
          (hl₂ _ (List.mem_append_right _ (List.mem_singleton_self _))) h with ⟨hc, rfl, rfl⟩ | hcol
      · simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at h₁ h₂
        rcases chain_binds hsz hb ht k a₁ a₂ h₁ h₂ (fun p hp => hl₁ p (List.mem_append_left _ hp))
            (fun p hp => hl₂ p (List.mem_append_left _ hp)) hc with rfl | hcol
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

/-- The chain a fold stamps: the log's turns, each with the root its admission left. -/
theorem fold_chain {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      ∃ rs : List D, rs.length = l.length ∧ w'.chain = chainOf E w.chain (l.zip rs) ∧
        (l ≠ [] → rs.getLast? = some (w'.root E))
  | w, w', [], h => by simp [World.fold] at h; subst h; exact ⟨[], rfl, rfl, fun h => absurd rfl h⟩
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨rs, hl, hc, hr⟩ := fold_chain h₂
      refine ⟨w₁.root E :: rs, by simp [hl], ?_, fun _ => ?_⟩
      · rw [hc, admit_chain h₁]; rfl
      · cases rest with
        | nil =>
            simp at hl; subst hl
            simp [World.fold] at h₂; subst h₂; rfl
        | cons u us =>
            simp [List.getLast?_cons, hr (by simp)]

/-- **Charge exactness over a log.** Each turn of an admitted log paid exactly its weight (where
the budget went is `Kernel.Proofs.Weight.fold_conserves`). -/
theorem fold_charge {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' → ∀ t ∈ l, t.charge = t.weight
  | w, w', [], _ => by simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact (admit_charge h₁).1
      · exact fold_charge h₂ x hx

/-- An admitted turn is bounded. -/
theorem admit_bounded {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : checkBounds t = .ok () := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  exact hc.bounds

/-- Every turn of an admitted log is bounded: the premise `chain_binds` needs, met by every fold. -/
theorem fold_bounded {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' → ∀ t ∈ l, checkBounds t = .ok ()
  | w, w', [], _ => by simp
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact admit_bounded h₁
      · exact fold_bounded h₂ x hx

/-- The follower's theorem in its usable form: same start, same head after folding, same log
(or a collision). -/
theorem fold_head_binds {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : TurnBytesInjOn E)
    {g w₁ w₂ : World D} {l₁ l₂ : List (Turn D)}
    (h₁ : World.fold E g l₁ = .ok w₁) (h₂ : World.fold E g l₂ = .ok w₂)
    (hh : w₁.height = w₂.height) (hc : w₁.chain = w₂.chain) :
    l₁ = l₂ ∨ Collision E.hash := by
  have hl : l₁.length = l₂.length := by
    have := fold_height h₁; have := fold_height h₂; omega
  obtain ⟨rs₁, hr₁, hc₁, _⟩ := fold_chain h₁
  obtain ⟨rs₂, hr₂, hc₂, _⟩ := fold_chain h₂
  rw [hc₁, hc₂] at hc
  rcases chain_binds hsz hb ht l₁.length (l₁.zip rs₁) (l₂.zip rs₂) (by simp [hr₁])
      (by simp [hr₂, hl]) (fun p hp => fold_bounded h₁ p.1 (List.of_mem_zip hp).1)
      (fun p hp => fold_bounded h₂ p.1 (List.of_mem_zip hp).1) hc with he | hcol
  · left
    have := congrArg (List.map Prod.fst) he
    rwa [List.map_fst_zip (by omega), List.map_fst_zip (by omega)] at this
  · exact .inr hcol

/-- `World.fold` is a function of its log. -/
theorem fold_det {E : Env D} {g w₁ w₂ : World D} {l : List (Turn D)}
    (h₁ : World.fold E g l = .ok w₁) (h₂ : World.fold E g l = .ok w₂) : w₁ = w₂ := by
  rw [h₁] at h₂; exact Except.ok.inj h₂

/-- **The fold reaches the host's World.** A follower that folds a log from the host's genesis and
reaches the host's `(height, chain)` holds the host's World — every cell, nullifier, journal entry,
the budget and the root — or the hash has a collision. -/
theorem fold_reaches_host {E : Env D} {n : Nat} (hsz : ∀ d, (E.bytes d).size = n)
    (hb : Function.Injective E.bytes) (ht : TurnBytesInjOn E)
    {g host follower : World D} {lh lf : List (Turn D)}
    (hh : World.fold E g lh = .ok host) (hf : World.fold E g lf = .ok follower)
    (hht : follower.height = host.height) (hc : follower.chain = host.chain) :
    follower = host ∨ Collision E.hash := by
  rcases fold_head_binds hsz hb ht hf hh hht hc with rfl | hcol
  · exact .inl (fold_det hf hh)
  · exact .inr hcol

/-- `World.fold` is the monadic left fold of `World.admit` (HOST's `staged_rooted` builds on it). -/
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
