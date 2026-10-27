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

end Nanodregg.Hosting.Proofs.Certify
