/-
# Hosting.Proofs.Frame — deciding only a batch's touched ids misses nothing

`fold_frame`: KERNEL's per-Turn `admit_frame` lifted to a batch — a cell id that no Turn of the batch
touches or creates keeps its entry. `decide_frame`: so its controller decision is the same after the
batch as before, which is what lets `Loop.step` decide `touchedIds` only (HOSTING-10's owed
batch-level frame property).
-/
import Hosting.Controller
import Kernel.Proofs.Frame

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Controller

variable {D : Type} [Ord D] [DecidableEq D]

theorem fold_frame {E : Env D} : ∀ {w w' : World D} {ts : List (Step D)} {c : D},
    World.fold E w ts = .ok w' → c ∉ touchedIds (Step.turns ts) → w'.entry E c = w.entry E c
  | w, w', [], c, h, _ => by simp [World.fold] at h; subst h; rfl
  | w, w', .refusal r :: rest, c, h, hc => by
    obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
    rw [fold_frame h₂ hc]
    exact refuse_entry h₁ c
  | w, w', .turn t :: rest, c, h, hc => by
    obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
    simp only [Step.turns, touchedIds, List.flatMap_cons, List.mem_append, not_or] at hc
    obtain ⟨⟨hct, hcc⟩, hr⟩ := hc
    rw [fold_frame h₂ (by simpa [touchedIds] using hr)]
    exact admit_frame h₁ (fun x hx he => absurd (he ▸ List.mem_map_of_mem hx) hct) hcc

theorem decide_frame {E : Env D} {w w' : World D} {ts : List (Step D)} {c : D}
    (label pkgId : ByteArray) (now : Nat) (live : List Live) (g : ByteArray)
    (h : World.fold E w ts = .ok w') (hc : c ∉ touchedIds (Step.turns ts)) :
    decideCell label pkgId now live g (w'.live E c) = decideCell label pkgId now live g (w.live E c) := by
  unfold World.live
  rw [fold_frame h hc]

end Nanodregg.Hosting.Proofs
