/-
# Hosting.Proofs.Certify — the certify key signs heads of the decider's own fold, one per step count

`decide_ok`: a grant is the bytes the writer sent, they are the certified bytes of a head the
decider's fold holds, the decider was anchored, and the head follows the last certified one
(`Follows`: not below it, and at its step count it IS it). `granted_one_head`: over any run of
grants in which each decision is made by a certifier holding the previous grant as `last` (one
decider life, or several, each restarted with keybroker's persisted head and whatever fold the
Store's files gave it), two heads granted at one step count are one head. So the seed never signs
the two certificates `Protocol.Proofs.Head.certified_equivocation` needs. `anchoredBy_chain`: an
anchor is the kernel's chain link from the certified head to the opened World.

One head per step count is not enough: a key could sign one branch at step 10 and another at step 11
without signing twice at either (CRIT-TRUST). `granted_extends` closes that: over any run of grants
whose certifiers keep `Line` (one line of linked heads, and the last certified head on it), every
head granted EXTENDS every head granted before it (`Extends`: one World, and step pairs whose
kernel chain link runs from the earlier head's chain to the later one's). `Line` holds of a decider
at its open (`opened_line`; `restart_extends`: an anchored restart's World extends the last certified
head) and is kept by every record it absorbs (`absorb_line`: the decider checks each link itself)
and by every grant (`decide_line`).
-/
import Hosting.Certify

namespace Nanodregg.Hosting.Proofs.Certify

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol.Head Nanodregg.Hosting.Certify

variable {D : Type} [DecidableEq D]

/-- `h` may be this key's next certified head after `l`: not below it, and at its step count it is
`l` itself. -/
def Follows : Option (Head D) → Head D → Prop
  | none, _ => True
  | some l, h => l.steps ≤ h.steps ∧ (l.steps = h.steps → l = h)

/-- What a grant is. -/
theorem decide_ok {X : Ctx D} {c c' : Certifier D} {b s : ByteArray}
    (h : Certify.decide X c b = .ok (c', s)) :
    s = b ∧ c.anchored = true ∧
      ∃ hd ∈ c.heads, certifiedBytes X.env hd = some b ∧ hd.origin = c.origin ∧
        c' = { c with last := some hd } ∧ Follows c.last hd := by
  unfold Certify.decide at h
  cases hs : certifiedSaid X b with
  | none => simp [hs] at h
  | some hd =>
    simp only [hs] at h
    by_cases hb : certifiedBytes X.env hd = some b
    · by_cases ho : hd.origin = c.origin
      · by_cases ha : c.anchored = true
        · simp only [hb, ho, ha, bind, Except.bind, pure, Except.pure] at h
          cases hl : c.last with
          | none =>
            simp only [hl, if_true, ne_eq, not_true_eq_false, if_false] at h
            cases hg : c.heads.getLast? with
            | none => simp [hg] at h
            | some t =>
              simp only [hg] at h
              split at h
              · cases h
              · split at h
                · rename_i hc
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ⟨rfl, ha, hd, by simpa using hc, hb, ho, by rw [ha], trivial⟩
                · cases h
          | some l =>
            simp only [hl, if_true, ne_eq, not_true_eq_false, if_false] at h
            split at h
            · cases h
            · rename_i hr
              have hf : Follows (some l) hd := by
                refine ⟨by omega, fun he => ?_⟩
                by_cases hq : hd = l
                · exact hq.symm
                · exact absurd (Or.inr ⟨he.symm, hq⟩) hr
              cases hg : c.heads.getLast? with
              | none => simp [hg] at h
              | some t =>
                simp only [hg] at h
                split at h
                · cases h
                · split at h
                  · rename_i hc
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨rfl, ha, hd, by simpa using hc, hb, ho, by rw [ha], hf⟩
                  · cases h
        · simp [hb, ho, ha, bind, Except.bind, pure, Except.pure] at h
      · simp [hb, ho, bind, Except.bind, pure, Except.pure] at h
    · simp [hb, bind, Except.bind] at h

/-- A grant names a head the decider's own fold holds, by its certified bytes. -/
theorem certify_on_fold {X : Ctx D} {c c' : Certifier D} {b s : ByteArray}
    (h : Certify.decide X c b = .ok (c', s)) :
    ∃ hd ∈ c.heads, certifiedBytes X.env hd = some s := by
  obtain ⟨rfl, -, hd, hm, hb, -⟩ := decide_ok h
  exact ⟨hd, hm, hb⟩

/-- A run of grants of one key, over any number of decider lives: each decision is made by SOME
certifier (its fold, its window and its anchor are whatever that life holds) whose `last` is the
previous grant's head (one life carries it in memory; a restart reads keybroker's persisted copy).
`Granted X l hs`: starting from last certified head `l`, the heads `hs` were granted in order. -/
inductive Granted (X : Ctx D) : Option (Head D) → List (Head D) → Prop
  | nil (l : Option (Head D)) : Granted X l []
  | cons {l : Option (Head D)} {c c' : Certifier D} {b : ByteArray} {hd : Head D} {rest : List (Head D)} :
      c.last = l → Certify.decide X c b = .ok (c', b) → c'.last = some hd → Granted X (some hd) rest →
      Granted X l (hd :: rest)

omit [DecidableEq D] in
private theorem follows_trans {a b c : Head D} (h₁ : Follows (some a) b) (h₂ : Follows (some b) c) :
    Follows (some a) c := by
  obtain ⟨h₁s, h₁e⟩ := h₁
  obtain ⟨h₂s, h₂e⟩ := h₂
  refine ⟨Nat.le_trans h₁s h₂s, fun he => ?_⟩
  have hab : a.steps = b.steps := by omega
  have hbc : b.steps = c.steps := by omega
  rw [h₁e hab, h₂e hbc]

/-- Every head of a run follows the run's starting head and every head granted before it. -/
private theorem granted_pairwise {X : Ctx D} :
    ∀ {l : Option (Head D)} {hs : List (Head D)}, Granted X l hs →
      (∀ h ∈ hs, Follows l h) ∧ hs.Pairwise (fun a b => Follows (some a) b)
  | _, _, .nil _ => ⟨by simp, List.Pairwise.nil⟩
  | l, _, .cons (c := c) (hd := hd) (rest := rest) hl hdec hlast hrest => by
    obtain ⟨-, -, hd', -, -, -, hc', hf⟩ := decide_ok hdec
    have hdd : hd' = hd := by
      rw [hc'] at hlast
      exact Option.some.inj hlast
    subst hdd
    rw [hl] at hf
    obtain ⟨ihf, ihp⟩ := granted_pairwise hrest
    refine ⟨?_, List.Pairwise.cons ihf ihp⟩
    intro h hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hf
    · cases l with
      | none => trivial
      | some l₀ => exact follows_trans hf (ihf h hm)

private theorem pairwise_either {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb => by
    rcases List.pairwise_cons.mp hp with ⟨hx, hxs⟩
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact Or.inl (ha'.trans hb'.symm)
    · subst ha'; exact Or.inr (Or.inl (hx b hb'))
    · subst hb'; exact Or.inr (Or.inr (hx a ha'))
    · exact pairwise_either hxs ha' hb'

/-- **One head per step count.** Over any run of grants (any number of decider lives, each with
whatever fold its Store gave it, carrying only the last certified head), two heads granted at one
step count are one head: the certify key never signs two certificates at one step. -/
theorem granted_one_head {X : Ctx D} {l : Option (Head D)} {hs : List (Head D)} (h : Granted X l hs)
    {a b : Head D} (ha : a ∈ hs) (hb : b ∈ hs) (he : a.steps = b.steps) : a = b := by
  rcases pairwise_either (granted_pairwise h).2 ha hb with e | ⟨-, f⟩ | ⟨-, f⟩
  · exact e
  · exact f he
  · exact (f he.symm).symm

/-- An anchor is the kernel's chain link: the pairs advance the certified head's chain, from its
step count, to exactly the opened World's chain and step count. -/
theorem anchoredBy_chain [Ord D] {E : Env D} {l : Head D} {w : World D} {ps : List (Step D × D)}
    (h : anchoredBy E l w ps = true) :
    l.origin = w.origin ∧ l.steps + ps.length = w.steps ∧ chainOf E l.chain ps = w.chain := by
  simpa [anchoredBy] using h

/-! ## Extension across step counts (TRUST-4; CRIT-TRUST's recovery finding) -/

section Extension

omit [DecidableEq D] in
theorem chainOf_append (E : Env D) : ∀ (c : D) (ps qs : List (Step D × D)),
    chainOf E c (ps ++ qs) = chainOf E (chainOf E c ps) qs
  | _, [], _ => rfl
  | c, (t, r) :: ps, qs => chainOf_append E (stepLink E c t r) ps qs

/-- `h` extends `l`: one World, and step pairs from `l`, as many as the step counts differ by, whose
kernel chain link (`chainOf`) runs from `l`'s chain to `h`'s. -/
def Extends (E : Env D) (l h : Head D) : Prop :=
  ∃ ps : List (Step D × D), l.origin = h.origin ∧ l.steps + ps.length = h.steps ∧ chainOf E l.chain ps = h.chain

omit [DecidableEq D] in
theorem Extends.refl (E : Env D) (h : Head D) : Extends E h h := ⟨[], rfl, by simp, rfl⟩

omit [DecidableEq D] in
theorem Extends.trans {E : Env D} {a b c : Head D} (h₁ : Extends E a b) (h₂ : Extends E b c) : Extends E a c := by
  obtain ⟨ps, ho, hs, hc⟩ := h₁
  obtain ⟨qs, ho', hs', hc'⟩ := h₂
  exact ⟨ps ++ qs, ho.trans ho', by rw [List.length_append]; omega, by rw [chainOf_append, hc, hc']⟩

omit [DecidableEq D] in
theorem Extends.steps_le {E : Env D} {a b : Head D} (h : Extends E a b) : a.steps ≤ b.steps := by
  obtain ⟨ps, -, hs, -⟩ := h; omega

theorem linked_extends {E : Env D} {t h : Head D} {ps : List (Step D × D)} (hl : linked E t h ps = true) :
    Extends E t h := by
  simp only [linked, decide_eq_true_eq] at hl
  exact ⟨ps, hl.1, hl.2.1, hl.2.2⟩

/-- **The certifier's window is one line, with the last certified head on it.** Its heads are pairwise
`Extends` in order; and when it is anchored, the last certified head is extended by the window's tip
and comparable with every head in the window. -/
structure Line (E : Env D) (c : Certifier D) : Prop where
  chain : c.heads.Pairwise (Extends E)
  last : c.anchored = true → ∀ l, c.last = some l →
    ∃ t, c.heads.getLast? = some t ∧ Extends E l t ∧ ∀ h ∈ c.heads, Extends E l h ∨ Extends E h l

omit [DecidableEq D] in
private theorem mem_getLast {α : Type} {R : α → α → Prop} {l : List α} {t x : α}
    (hp : l.Pairwise R) (ht : l.getLast? = some t) (hx : x ∈ l) : x = t ∨ R x t := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp ht
  rcases List.mem_append.mp hx with hx | hx
  · exact .inr ((List.pairwise_append.mp hp).2.2 x hx t (List.mem_singleton_self t))
  · exact .inl (List.mem_singleton.mp hx)

/-- **At the open**: a decider's certifier satisfies `Line`. -/
theorem opened_line [Ord D] {E : Env D} {w : World D} {last : Option (Head D)} {pairs : Option (List (Step D × D))} :
    Line E (Certifier.opened E w last pairs) := by
  refine ⟨List.pairwise_singleton _ _, ?_⟩
  intro ha l hl
  simp only [Certifier.opened] at ha hl
  subst hl
  have hx : Extends E l (headOf E w) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at ha
    rcases ha with he | ha
    · rw [he]; exact Extends.refl E _
    · cases pairs with
      | none => cases ha
      | some ps =>
        obtain ⟨ho, hs, hc⟩ := anchoredBy_chain ha
        exact ⟨ps, ho, hs, hc⟩
  refine ⟨headOf E w, by simp [Certifier.opened], hx, ?_⟩
  intro h hm
  simp only [Certifier.opened, List.mem_singleton] at hm
  subst hm
  exact .inl hx

/-- **The restart path proves extension**: a decider restarted with the last certified head `l` that
comes up anchored holds a World whose head extends `l` (the opened World IS `l`'s head, or the
Store's kept step pairs run the kernel's chain link from `l` to it). -/
theorem restart_extends [Ord D] {E : Env D} {w : World D} {l : Head D} {pairs : Option (List (Step D × D))}
    (ha : (Certifier.opened E w (some l) pairs).anchored = true) : Extends E l (headOf E w) := by
  obtain ⟨t, ht, hx, -⟩ := opened_line.last ha l rfl
  simp only [Certifier.opened, List.getLast?_singleton, Option.some.injEq] at ht
  rw [ht]; exact hx

/-- **Every record the decider absorbs keeps `Line`**: it checks the head's link from the window's
tip itself, and an unlinked head unanchors it. -/
theorem absorb_line {E : Env D} {c : Certifier D} (hc : Line E c) (p : List (Step D × D) × Head D) :
    Line E (c.absorb E p) := by
  obtain ⟨ps, h⟩ := p
  unfold Certifier.absorb
  cases ht : c.heads.getLast? with
  | none => exact ⟨List.pairwise_singleton _ _, fun ha => by simp at ha⟩
  | some t =>
    simp only
    split
    · rename_i hl
      have hth := linked_extends hl
      have hk : c.heads.length + 1 - headsMax ≤ c.heads.length := by unfold headsMax; omega
      have hd : (c.heads ++ [h]).drop (c.heads.length + 1 - headsMax) =
          c.heads.drop (c.heads.length + 1 - headsMax) ++ [h] := List.drop_append_of_le_length hk
      have hto : ∀ x ∈ c.heads, Extends E x h := fun x hx =>
        (mem_getLast hc.chain ht hx).elim (fun e => e ▸ hth) (fun e => e.trans hth)
      refine ⟨?_, ?_⟩
      · simp only
        rw [hd]
        refine List.pairwise_append.mpr ⟨hc.chain.sublist (List.drop_sublist _ _), List.pairwise_singleton _ _, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton.mp hy]
        exact hto x (List.mem_of_mem_drop hx)
      · intro ha l hl
        simp only at ha hl ⊢
        rw [hd]
        refine ⟨h, by simp, ?_⟩
        by_cases hca : c.anchored = true
        · obtain ⟨t', ht', hlt, hall⟩ := hc.last hca l hl
          rw [ht] at ht'
          obtain rfl := Option.some.inj ht'
          have hlh : Extends E l h := hlt.trans hth
          refine ⟨hlh, fun y hy => ?_⟩
          rcases List.mem_append.mp hy with hy | hy
          · exact hall y (List.mem_of_mem_drop hy)
          · rw [List.mem_singleton.mp hy]; exact .inl hlh
        · simp only [hca, Bool.false_or, hl, decide_eq_true_eq] at ha
          subst ha
          refine ⟨Extends.refl E _, fun y hy => ?_⟩
          rcases List.mem_append.mp hy with hy | hy
          · exact .inr (hto y (List.mem_of_mem_drop hy))
          · rw [List.mem_singleton.mp hy]; exact .inl (Extends.refl E _)
    · exact ⟨List.pairwise_singleton _ _, fun ha => by simp at ha⟩

omit [DecidableEq D] in
private theorem pairwise_either' {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha (List.not_mem_nil)
  | x :: xs, hp, a, b, ha, hb => by
    rcases List.pairwise_cons.mp hp with ⟨hx, hxs⟩
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact Or.inl (ha'.trans hb'.symm)
    · subst ha'; exact Or.inr (Or.inl (hx b hb'))
    · subst hb'; exact Or.inr (Or.inr (hx a ha'))
    · exact pairwise_either' hxs ha' hb'

/-- **Every grant keeps `Line`**: the granted head is in the window, so it is on the line. -/
theorem decide_line {X : Ctx D} {c c' : Certifier D} {b s : ByteArray} (hc : Line X.env c)
    (h : Certify.decide X c b = .ok (c', s)) : Line X.env c' := by
  obtain ⟨-, ha, hd, hm, -, -, rfl, -⟩ := decide_ok h
  refine ⟨hc.chain, fun _ l hl => ?_⟩
  simp only [Option.some.injEq] at hl
  subst hl
  obtain ⟨t, ht⟩ : ∃ t, c.heads.getLast? = some t := by
    cases hg : c.heads.getLast? with
    | none => simp [List.getLast?_eq_none_iff.mp hg] at hm
    | some t => exact ⟨t, rfl⟩
  refine ⟨t, ht, (mem_getLast hc.chain ht hm).elim (fun e => e ▸ Extends.refl _ _) id, fun y hy => ?_⟩
  rcases pairwise_either' hc.chain hm hy with e | r | r
  · rw [← e]; exact .inl (Extends.refl _ _)
  · exact .inl r
  · exact .inr r

/-- **A grant extends the last certified head.** -/
theorem grant_extends {X : Ctx D} {c c' : Certifier D} {b s : ByteArray} {l : Head D} (hc : Line X.env c)
    (h : Certify.decide X c b = .ok (c', s)) (hl : c.last = some l) :
    ∃ hd, c'.last = some hd ∧ Extends X.env l hd := by
  obtain ⟨-, ha, hd, hm, -, -, rfl, hf⟩ := decide_ok h
  refine ⟨hd, rfl, ?_⟩
  obtain ⟨-, -, -, hall⟩ := hc.last ha l hl
  rw [hl] at hf
  rcases hall hd hm with r | r
  · exact r
  · obtain ⟨hle, heq⟩ := hf
    rw [heq (Nat.le_antisymm hle r.steps_le)]
    exact Extends.refl _ _

/-- A run of grants whose every certifier keeps `Line` (what `opened_line`, `absorb_line` and
`decide_line` give every certifier the decider builds). -/
inductive GrantedLined (X : Ctx D) : Option (Head D) → List (Head D) → Prop
  | nil (l : Option (Head D)) : GrantedLined X l []
  | cons {l : Option (Head D)} {c c' : Certifier D} {b : ByteArray} {hd : Head D} {rest : List (Head D)} :
      c.last = l → Line X.env c → Certify.decide X c b = .ok (c', b) → c'.last = some hd →
      GrantedLined X (some hd) rest → GrantedLined X l (hd :: rest)

theorem GrantedLined.granted {X : Ctx D} :
    ∀ {l : Option (Head D)} {hs : List (Head D)}, GrantedLined X l hs → Granted X l hs
  | _, _, .nil l => .nil l
  | _, _, .cons hl _ hd hc hr => .cons hl hd hc hr.granted

/-- **Every head the key grants extends every head it granted before**, across any number of decider
lives: what sign-once per step count (`granted_one_head`) does not give. With the run's starting
head `l₀` (the persisted last certified head), every granted head extends it too. -/
theorem granted_extends {X : Ctx D} :
    ∀ {l : Option (Head D)} {hs : List (Head D)}, GrantedLined X l hs →
      (∀ l₀, l = some l₀ → ∀ h ∈ hs, Extends X.env l₀ h) ∧ hs.Pairwise (Extends X.env)
  | _, _, .nil _ => ⟨by simp, List.Pairwise.nil⟩
  | l, _, .cons (c := c) (hd := hd) (rest := rest) hl hline hdec hlast hrest => by
    obtain ⟨ihf, ihp⟩ := granted_extends hrest
    have hhd : ∀ h ∈ rest, Extends X.env hd h := ihf hd rfl
    refine ⟨fun l₀ hl₀ h hm => ?_, List.Pairwise.cons hhd ihp⟩
    obtain ⟨hd', hl', hx⟩ := grant_extends hline hdec (hl.trans hl₀)
    rw [hlast] at hl'
    obtain rfl := Option.some.inj hl'
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hx
    · exact hx.trans (hhd h hm)

end Extension

end Nanodregg.Hosting.Proofs.Certify
