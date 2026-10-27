/-
# Kernel.Proofs.Causal — an admitted causal pin is a head of the log (KERNEL-79)

A signed call may carry the head its signer planned at (`Unsigned.causal`, recorded as `Turn.causal`).
`World.admit` judges it against the World's own chain there (`checkCausal`, `World.chainAt`: the current
chain, or the ring of the last `Bounds.pinWindow` heads in the window trie). Three facts:

* `admit_pin_holds` — an admitted Turn's pin is the World's chain at the pin's step;
* `fold_chainAt_passes` — the ring tells the truth: along a fold from a World whose ring is empty, every
  head `chainAt` answers is a head some prefix of the log reaches;
* `pinned_no_join` — two folds from one start that both admit a Turn pinned at `(s, c)` are one log up
  to step `s`, or two of the listed inputs collide. A pinned call is never shared by two histories that
  disagree before its pin (SUNDR's no-join, for pinned calls; CRIT-TRUST, PROTOCOL-82).
  `pinned_no_join_genesis` is its instance from a genesis World.

What is not claimed: a pin older than the ring is `pinExpired` (refused, never admitted unchecked); a
writer that withholds is not detected here; laws do not see the pin yet (LANG-107, landing 1b).
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.RefusalsHead

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A passing pin check names the World's chain at the pin's step. -/
theorem checkCausal_ok {E : Env D} {w : World D} {p : CausalPin D}
    (h : checkCausal E w (some p) = .ok ()) : w.chainAt E p.steps = some p.chain :=
  (checkCausal_some_ok.mp h).2

/-- **An admitted pin holds** (KERNEL-79): the World an admitted Turn was admitted on had, at the
pin's step, exactly the pin's chain. -/
theorem admit_pin_holds {E : Env D} {w w' : World D} {t : Turn D} {p : CausalPin D}
    (h : World.admit E w t = .ok w') (hp : t.causal = some p) : w.chainAt E p.steps = some p.chain := by
  obtain ⟨posts, hk, -⟩ := admit_ok h
  have := hk.causal
  rw [hp] at this
  exact checkCausal_ok this

/-- `l` passes chain `c` at step `s`: some prefix of `l` folds from `g` to a World at step count `s`
whose chain is `c`. -/
def Passes (E : Env D) (g : World D) (l : List (Step D)) (s : Nat) (c : D) : Prop :=
  ∃ l₁ l₂ v, l = l₁ ++ l₂ ∧ World.fold E g l₁ = .ok v ∧ v.steps = s ∧ v.chain = c

/-- A World whose ring holds nothing: `chainAt` answers only its own head (every genesis World and every
carried World: their window trie starts empty). -/
def RingEmpty (E : Env D) (g : World D) : Prop :=
  ∀ k, g.refusals.get (refusalSpec E) (.chain k) = none

theorem genesis_ringEmpty (E : Env D) (o : D) (a : Nat) : RingEmpty E (World.genesis E o a) :=
  fun _ => by simp [World.genesis, Trie.get_empty]

/-- **The ring tells the truth** (KERNEL-79): along a fold from a World with an empty ring and a
canonical window trie, every head `chainAt` answers is a head a prefix of the log reaches. -/
theorem fold_chainAt_passes {E : Env D} {g : World D} (hg : RingEmpty E g) (hgc : g.RefusalsCanon E) :
    ∀ (l : List (Step D)) {w : World D}, World.fold E g l = .ok w →
      ∀ s c, w.chainAt E s = some c → Passes E g l s c := by
  suffices H : ∀ (n : Nat) (l : List (Step D)), l.length = n → ∀ {w : World D}, World.fold E g l = .ok w →
      ∀ s c, w.chainAt E s = some c → Passes E g l s c from fun l => H l.length l rfl
  intro n
  induction n with
  | zero =>
    intro l hl w hw s c hs
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero hl
    subst hl0
    simp [World.fold] at hw
    subst hw
    unfold World.chainAt at hs
    split at hs
    · rename_i he
      cases hs
      exact ⟨[], [], _, rfl, rfl, he.symm, rfl⟩
    · rw [hg _] at hs
      simp at hs
  | succ n ih =>
    intro l' hl' w' hw' s c hs
    obtain ⟨l, st, rfl⟩ : ∃ l st, l' = l ++ [st] := by
      cases hr : l'.reverse with
      | nil => simp at hr; subst hr; simp at hl'
      | cons b L => exact ⟨L.reverse, b, by rw [← List.reverse_reverse l', hr]; simp⟩
    have hl : l.length = n := by simp at hl'; omega
    obtain ⟨w, hw, hst⟩ := fold_append.mp hw'
    have hst' : World.step E w st = .ok w' := by
      obtain ⟨v, hv, hf⟩ := fold_cons_ok.mp hst
      simp [World.fold] at hf
      subst hf
      exact hv
    have hc : w.RefusalsCanon E := fold_refusalsCanon hgc hw
    unfold World.chainAt at hs
    split at hs
    · rename_i he
      cases hs
      exact ⟨l ++ [st], [], w', by simp, hw', he.symm, rfl⟩
    · rw [step_ring hc hst', step_origin hst'] at hs
      by_cases hk : (ChainSlot.ring w.origin (ringSlot s) = .ring w.origin (ringSlot w.steps))
      · rw [if_pos hk] at hs
        dsimp only at hs
        split at hs
        · rename_i he
          cases hs
          subst he
          exact ⟨l, [st], w, rfl, hw, rfl, rfl⟩
        · cases hs
      · rw [if_neg hk] at hs
        have hw_ne : s ≠ w.steps := by
          intro he; apply hk; rw [he]
        have hwc : w.chainAt E s = some c := by
          unfold World.chainAt; rw [if_neg hw_ne]; exact hs
        obtain ⟨l₁, l₂, v, hl₁, hv, hvs, hvc⟩ := ih l hl hw s c hwc
        exact ⟨l₁, l₂ ++ [st], v, by rw [hl₁]; simp, hv, hvs, hvc⟩

/-- The prefix a log passes at a step is the prefix of that length: a fold from `g` reaches step count
`g.steps + l₁.length`. -/
theorem Passes.prefix {E : Env D} {g : World D} {l : List (Step D)} {s : Nat} {c : D}
    (h : Passes E g l s c) : ∃ v, World.fold E g (l.take (s - g.steps)) = .ok v ∧ v.steps = s ∧ v.chain = c := by
  obtain ⟨l₁, l₂, v, rfl, hv, hs, hc⟩ := h
  have := fold_steps hv
  have hlen : s - g.steps = l₁.length := by omega
  have ht : (l₁ ++ l₂).take l₁.length = l₁ := by simp
  refine ⟨v, ?_, hs, hc⟩
  rw [hlen, ht]
  exact hv

/-- **No join for pinned calls** (KERNEL-79; SUNDR's no-join, CRIT-TRUST): two folds from one start
`g` (empty ring, canonical window trie) that each admit, at some step, a Turn pinned at `(s, c)` agree
on their first `s - g.steps` steps — one log — or two of the listed inputs collide. -/
theorem pinned_no_join {E : Env D} {n : Nat} (hE : E.Lawful n) {g : World D} (hg : RingEmpty E g)
    (hgc : g.RefusalsCanon E) {p : CausalPin D}
    {la lb : List (Step D)} {ta tb : Turn D} {wa wb wa' wb' : World D}
    (ha : World.fold E g la = .ok wa) (hta : World.admit E wa ta = .ok wa') (hpa : ta.causal = some p)
    (hb : World.fold E g lb = .ok wb) (htb : World.admit E wb tb = .ok wb') (hpb : tb.causal = some p) :
    la.take (p.steps - g.steps) = lb.take (p.steps - g.steps) ∨
      CollidesAmong E.hash (foldPres E g (la.take (p.steps - g.steps)) ++
        foldPres E g (lb.take (p.steps - g.steps))) := by
  obtain ⟨va, hva, hvas, hvac⟩ := (fold_chainAt_passes hg hgc la ha _ _ (admit_pin_holds hta hpa)).prefix
  obtain ⟨vb, hvb, hvbs, hvbc⟩ := (fold_chainAt_passes hg hgc lb hb _ _ (admit_pin_holds htb hpb)).prefix
  exact fold_head_binds hE hva hvb (by rw [hvas, hvbs]) (by rw [hvac, hvbc])

/-- **`pinned_no_join` from a genesis World**: two logs of one genesis that each admit a Turn pinned at
`(s, c)` are one log for their first `s` steps, or two of the listed inputs collide. -/
theorem pinned_no_join_genesis {E : Env D} {n : Nat} (hE : E.Lawful n) (o : D) (a : Nat) {p : CausalPin D}
    {la lb : List (Step D)} {ta tb : Turn D} {wa wb wa' wb' : World D}
    (ha : World.fold E (World.genesis E o a) la = .ok wa) (hta : World.admit E wa ta = .ok wa')
    (hpa : ta.causal = some p)
    (hb : World.fold E (World.genesis E o a) lb = .ok wb) (htb : World.admit E wb tb = .ok wb')
    (hpb : tb.causal = some p) :
    la.take p.steps = lb.take p.steps ∨
      CollidesAmong E.hash (foldPres E (World.genesis E o a) (la.take p.steps) ++
        foldPres E (World.genesis E o a) (lb.take p.steps)) := by
  have h := pinned_no_join hE (genesis_ringEmpty E o a) (Trie.canon_empty _ 0) ha hta hpa hb htb hpb
  have h0 : (World.genesis E o a).steps = 0 := rfl
  rw [h0, Nat.sub_zero] at h
  exact h

end Nanodregg.Kernel
