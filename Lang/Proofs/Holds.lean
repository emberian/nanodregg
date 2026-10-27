/-
# Lang.Proofs.Holds — a returned run backs every held leg (LANG-90; DESIGN-TYPES §3.1)

`runMeasuredWith_legs`: a run that returned had `checkLegs` admit its edits against its calls, so for
EVERY asset `a`, what the `holds` rows it writes need is at most what its calls move into the object's
account of `a` (`needIn a ls ≤ movedIn self a calls`), and what the rows it replaces or retracts held
is at most what they move out (`needOut a ls ≤ movedOut self a calls`), where `ls` are the run's held
legs read off its edits and their old rows (`legsOf`). This is the per-RUN fact; the history theorem
(the legs a `holds` relation holds never exceed the object's balance of their asset) is the next
landing's, from `admit_value` plus this.

Plant: `checkLegs := fun … => .ok ()` reds `checkLegs_backed` and the journey's HV2, HV3, HV6, HV7.
-/
import Lang.Proofs.Effect

namespace Nanodregg.Lang

open Nanodregg.Kernel.Receive

section
variable {D : Type} [DecidableEq D]

theorem needIn_pos_mem {a : D} : ∀ {ls : List (Leg D)}, 0 < needIn a ls → ∃ l ∈ ls, l.2.1 = a
  | [], h => by simp [needIn] at h
  | (ℓ, b, i, o) :: ls, h => by
    simp only [needIn] at h
    by_cases hb : b = a
    · exact ⟨(ℓ, b, i, o), by simp, hb⟩
    · simp only [hb, if_false, Nat.zero_add] at h
      obtain ⟨l, hl, e⟩ := needIn_pos_mem h
      exact ⟨l, by simp [hl], e⟩

theorem needOut_pos_mem {a : D} : ∀ {ls : List (Leg D)}, 0 < needOut a ls → ∃ l ∈ ls, l.2.1 = a
  | [], h => by simp [needOut] at h
  | (ℓ, b, i, o) :: ls, h => by
    simp only [needOut] at h
    by_cases hb : b = a
    · exact ⟨(ℓ, b, i, o), by simp, hb⟩
    · simp only [hb, if_false, Nat.zero_add] at h
      obtain ⟨l, hl, e⟩ := needOut_pos_mem h
      exact ⟨l, by simp [hl], e⟩

/-- `checkLegsGo` admits a list only when every leg's asset is backed in both directions. -/
theorem checkLegsGo_ok {self : D} {calls : List (Body D)} {all : List (Leg D)} :
    ∀ {ls : List (Leg D)}, checkLegsGo self calls all ls = .ok () →
      ∀ l ∈ ls, needIn l.2.1 all ≤ movedIn self l.2.1 calls ∧ needOut l.2.1 all ≤ movedOut self l.2.1 calls
  | [], _, l, hl => by simp at hl
  | (ℓ, a, i, o) :: ls, h, l, hl => by
    simp only [checkLegsGo] at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨Nat.le_of_not_lt h1, Nat.le_of_not_lt h2⟩
    · exact checkLegsGo_ok h l hl

/-- **`checkLegs` admits exactly backed runs**: for every asset, the legs the edits need in and out are
moved in and out by the calls. -/
theorem checkLegs_backed {digestOf : ByteArray → Option D} {rv : RowView D} {self : D}
    {calls : List (Body D)} {es : List (Edit D)} (h : checkLegs digestOf rv self calls es = .ok ()) :
    ∃ ls, legsOf digestOf rv self es = .ok ls ∧
      ∀ a, needIn a ls ≤ movedIn self a calls ∧ needOut a ls ≤ movedOut self a calls := by
  unfold checkLegs at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i ls hls
  refine ⟨ls, hls, fun a => ⟨?_, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos (needIn a ls) with h0 | h0
    · omega
    · obtain ⟨l, hl, rfl⟩ := needIn_pos_mem h0
      exact (checkLegsGo_ok h l hl).1
  · rcases Nat.eq_zero_or_pos (needOut a ls) with h0 | h0
    · omega
    · obtain ⟨l, hl, rfl⟩ := needOut_pos_mem h0
      exact (checkLegsGo_ok h l hl).2

/-- **A returned run backs every held leg** (LANG-90's theorem): the row acts it returns are its edits'
(`es`), and for every asset the held legs of those edits (`legsOf`, read off the new values and the old
rows) are moved in and out by the calls it returns. -/
theorem runMeasuredWith_legs {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {setup : Pinned D → RowView D → D → Kernel.Slots → Nat → ByteArray → Req D → Except (Refusal D) RunSetup}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Kernel.Slots} {calls : List (Body D)}
    {rows : List (Kernel.RowSlot D × Kernel.RowAct)} {t n : Nat}
    (h : runMeasuredWith bytesOf digestOf setup look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S es ls, setup look rv pkg state method args r = .ok S ∧ rows = es.map (fun x : Edit D => (x.slot, x.act)) ∧
      legsOf digestOf rv r.self es = .ok ls ∧
      ∀ a, needIn a ls ≤ movedIn r.self a calls ∧ needOut a ls ≤ movedOut r.self a calls := by
  unfold runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  all_goals first | (simp at h; done) | skip
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl, -, -⟩ := h
  obtain ⟨ls, hls, hb⟩ := checkLegs_backed ‹checkLegs _ _ _ _ _ = .ok _›
  exact ⟨S, _, ls, hS, rfl, hls, hb⟩

end

end Nanodregg.Lang
