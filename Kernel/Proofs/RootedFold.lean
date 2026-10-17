/-
# Kernel.Proofs.RootedFold — a rooted run (HOST-29)

* `Rooted.snoc` — a rooted run extended by one accepted step, noted with the state after it, is a
  rooted run (what the Host's batch machine does per admitted Turn);
* `RootedFold.fold` — a rooted fold IS a fold of its Turns: the roots are stated by the definition,
  and stripping them leaves `World.fold`;
* `RootedFold.chain` — the chain a rooted fold reaches is `chainOf` over its (Turn, root) pairs: the
  stated roots are exactly what a reader needs to advance the chain without admitting.
-/
import Kernel.Proofs.Admit

namespace Nanodregg.Kernel

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- A run of steps, each paired with a note of the state right after it, from `w` to `w'`: every
step is accepted and every note is the one the run reached (HOST-29). A Store's batch record is a
`RootedFold`: its Turns with the root after each; so are the loop's staged batch and the Turns follow
absorbs. Generic so the Host's batch machine states the same fact over its own parameters. -/
def Rooted {W T R N : Type} (admit : W → T → Except R W) (note : W → N) : W → List (T × N) → W → Prop
  | w, [], w' => w' = w
  | w, (t, n) :: rest, w' => ∃ w₁, admit w t = .ok w₁ ∧ n = note w₁ ∧ Rooted admit note w₁ rest w'

/-- `Rooted` over the kernel's transition and root: Turns admitted in order, each with the root of
the World after it. -/
abbrev World.RootedFold (E : Env D) : World D → List (Turn D × D) → World D → Prop :=
  Rooted (World.admit E) (World.root E)

end

theorem Rooted.snoc {W T R N : Type} {admit : W → T → Except R W} {note : W → N} :
    ∀ {w w₁ w' : W} {l : List (T × N)} {t : T}, Rooted admit note w l w₁ → admit w₁ t = .ok w' →
      Rooted admit note w (l ++ [(t, note w')]) w'
  | w, w₁, w', [], t, h, ha => by
      simp only [Rooted] at h; subst h
      exact ⟨w', ha, rfl, rfl⟩
  | w, w₁, w', (s, n) :: rest, t, h, ha => by
      obtain ⟨w₂, h2, hn, hr⟩ := h
      exact ⟨w₂, h2, hn, Rooted.snoc hr ha⟩

variable {D : Type} [Ord D] [DecidableEq D]

theorem RootedFold.fold {E : Env D} : ∀ {w w' : World D} {l : List (Turn D × D)},
    World.RootedFold E w l w' → World.fold E w (l.map Prod.fst) = .ok w'
  | w, w', [], h => by simp only [World.RootedFold, Rooted] at h; subst h; rfl
  | w, w', (t, r) :: rest, h => by
      obtain ⟨w₁, ha, -, hr⟩ := h
      simp only [List.map_cons, World.fold, ha, RootedFold.fold hr]

theorem RootedFold.chain {E : Env D} : ∀ {w w' : World D} {l : List (Turn D × D)},
    World.RootedFold E w l w' → w'.chain = chainOf E w.chain l
  | w, w', [], h => by simp only [World.RootedFold, Rooted] at h; subst h; rfl
  | w, w', (t, r) :: rest, h => by
      obtain ⟨w₁, ha, hr0, hr⟩ := h
      rw [RootedFold.chain hr, admit_chain ha, ← hr0]
      rfl

end Nanodregg.Kernel
