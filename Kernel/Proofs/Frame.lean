/-
# Kernel.Proofs.Frame — what an admitted turn leaves alone, and what it can never undo

Frame: a cell the turn neither writes, retires nor bears is unchanged. ROM: a live ROM cell
is live and identical after every admitted turn, hence forever. Nullifiers: an admitted turn
spends each of its nullifiers exactly once — none was spent before, all are after — and the
spent set only grows, so across a log no nullifier is spent twice.
-/
import Kernel.Proofs.Fold

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

omit [DecidableEq D] in
theorem insertAll_get_of_not_mem {c : D} :
    ∀ {m : Std.TreeMap D Entry compare} {ps : List (D × Entry)},
      c ∉ ps.map Prod.fst → (insertAll m ps)[c]? = m[c]?
  | m, [], _ => rfl
  | m, p :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      show (insertAll (m.insert p.1 p.2) rest)[c]? = m[c]?
      rw [insertAll_get_of_not_mem h.2, Std.TreeMap.getElem?_insert]
      have : compare p.1 c ≠ .eq := fun he => h.1 (Std.LawfulEqCmp.eq_of_compare he).symm
      simp [this]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A touch that leaves something behind leaves it at its own cell, and is not a `keep`. -/
theorem touchCheck_some {E : Env D} {w : World D} {x : Touch D} {p : D × Entry}
    (h : touchCheck E w x = .ok (some p)) : p.1 = x.cell ∧ x.act ≠ .keep := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp
  | retire =>
      rw [ha] at h
      cases hc : w.live x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- What a checked turn changes is exactly at its non-`keep` touches. -/
theorem posts_touched {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Entry)}
    (hk : Checked E w t posts) : ∀ p ∈ posts, ∃ x ∈ t.touches, p.1 = x.cell ∧ x.act ≠ .keep := by
  obtain ⟨raw, hm, rfl⟩ := hk.touches
  intro p hp
  have hp : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hp
  obtain ⟨x, hx, hr⟩ := mapEx_mem hm (some p) hp
  exact ⟨x, hx, touchCheck_some hr⟩

/-- **Frame.** A cell the turn neither writes, retires nor bears is unchanged. -/
theorem admit_frame {E : Env D} {w w' : World D} {t : Turn D} {c : D}
    (h : World.admit E w t = .ok w') (hl : ∀ x ∈ t.touches, x.cell = c → x.act = .keep)
    (hc : c ∉ createdIds E t) : w'.cells[c]? = w.cells[c]? := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hcp : c ∉ (bornEntries E t).map Prod.fst := by
    intro hm
    apply hc
    unfold bornEntries createdPairs at hm
    rw [List.map_map] at hm
    have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2)) = Prod.fst := rfl
    rw [this, List.map_fst_zip (by simp [createdIds])] at hm
    exact hm
  have hpc : c ∉ posts.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨x, hx, he, hne⟩ := posts_touched hk p hp
    exact hne (hl x hx he.symm)
  show (insertAll (insertAll w.cells posts) (bornEntries E t))[c]? = _
  rw [insertAll_get_of_not_mem hcp, insertAll_get_of_not_mem hpc]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A live ROM cell is only ever kept: a write refuses `romWrite`, a retirement `romRetire`. -/
theorem rom_keep {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Entry)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live c = some cell)
    (hrom : cell.discipline = .rom) : ∀ x ∈ t.touches, x.cell = c → x.act = .keep := by
  intro x hx hxc
  obtain ⟨r, hr⟩ := hk.touch x hx
  unfold touchCheck at hr
  rw [hxc, hlive] at hr
  simp only [except_bind_ok] at hr
  obtain ⟨⟨⟩, _, hr⟩ := hr
  cases ha : x.act with
  | keep => rfl
  | write ops =>
      rw [ha] at hr
      simp only [except_bind_ok] at hr
      obtain ⟨_, hp, _⟩ := hr
      simp [postWrite, hrom] at hp
  | retire =>
      rw [ha] at hr
      simp only [except_bind_ok] at hr
      obtain ⟨⟨⟩, hp, _⟩ := hr
      simp [req, hrom] at hp

omit [Std.LawfulEqOrd D] [DecidableEq D] in
theorem live_contains {w : World D} {c : D} {cell : Cell} (h : w.live c = some cell) :
    w.cells.contains c = true := by
  unfold World.live at h
  rw [Std.TreeMap.contains_eq_isSome_getElem?]
  cases hc : w.cells[c]? with
  | none => rw [hc] at h; simp at h
  | some e => simp

omit [Std.LawfulEqOrd D] in
/-- A live cell's id is never born again (`idTaken`). -/
theorem live_not_created {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Entry)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live c = some cell) :
    c ∉ createdIds E t := by
  intro hm
  have hc := hk.creates
  unfold checkCreates at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, _, ⟨⟩, _, hf⟩ := hc
  have := (forEx_ok.mp hf) c hm
  simp [req, live_contains hlive] at this

/-- **ROM is forever, one step.** A live ROM cell is live and identical after an admitted turn. -/
theorem admit_rom {E : Env D} {w w' : World D} {t : Turn D} {c : D} {cell : Cell}
    (h : World.admit E w t = .ok w') (hlive : w.live c = some cell) (hrom : cell.discipline = .rom) :
    w'.live c = some cell := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  have hf := admit_frame h (rom_keep hk hlive hrom) (live_not_created hk hlive)
  unfold World.live at hlive ⊢
  rw [hf]; exact hlive

/-- **ROM is forever.** A live ROM cell survives, unchanged, every admitted log. -/
theorem fold_rom {E : Env D} {c : D} {cell : Cell} (hrom : cell.discipline = .rom) :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w.live c = some cell → w'.live c = some cell
  | w, w', [], h, hl => by simp [World.fold] at h; subst h; exact hl
  | w, w', t :: rest, h, hl => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_rom hrom h₂ (admit_rom h₁ hl hrom)

omit [Std.LawfulEqOrd D] [DecidableEq D] in
theorem spendAll_contains_of_contains {n : D} :
    ∀ {s : Std.TreeSet D compare} {ns : List D}, s.contains n = true →
      (spendAll s ns).contains n = true
  | s, [], h => h
  | s, x :: rest, h => by
      show (spendAll (s.insert x) rest).contains n = true
      apply spendAll_contains_of_contains
      rw [Std.TreeSet.contains_insert]; simp [h]

omit [DecidableEq D] in
theorem spendAll_contains_of_mem {n : D} :
    ∀ {s : Std.TreeSet D compare} {ns : List D}, n ∈ ns → (spendAll s ns).contains n = true
  | s, [], h => by simp at h
  | s, x :: rest, h => by
      show (spendAll (s.insert x) rest).contains n = true
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · apply spendAll_contains_of_contains
        rw [Std.TreeSet.contains_insert]
        simp
      · exact spendAll_contains_of_mem h

/-- **Nullifiers spend once.** Each nullifier of an admitted turn was unspent and is spent; the
spent set only grows. -/
theorem admit_nullifiers {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    (∀ n ∈ t.nullifiers, w.spent.contains n = false ∧ w'.spent.contains n = true) ∧
      ∀ n, w.spent.contains n = true → w'.spent.contains n = true := by
  obtain ⟨_, hk, rfl⟩ := admit_ok h
  refine ⟨fun n hn => ⟨?_, spendAll_contains_of_mem hn⟩, fun n hn => spendAll_contains_of_contains hn⟩
  have := (forEx_ok.mp hk.nullifiers) n hn
  rw [req_ok] at this
  simpa using this

/-- Across a log no nullifier is spent twice, and none was spent at the start. -/
theorem fold_nullifiers {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      ∀ i j (hi : i < l.length) (hj : j < l.length) n, i < j →
        n ∈ (l[i]'hi).nullifiers → n ∉ (l[j]'hj).nullifiers
  | w, w', [], _ => by intro i _ hi; simp at hi
  | w, w', t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro i j hi hj n hij hni hnj
      cases j with
      | zero => omega
      | succ j =>
          cases i with
          | zero =>
              -- n is spent after t; every later turn needs it unspent
              have spent₁ := ((admit_nullifiers h₁).1 n hni).2
              have later : ∀ {v v' : World D} {ls : List (Turn D)}, World.fold E v ls = .ok v' →
                  v.spent.contains n = true → ∀ (k : Nat) (hk : k < ls.length),
                    n ∉ (ls[k]'hk).nullifiers := by
                intro v v' ls
                induction ls generalizing v with
                | nil => intro _ _ k hk; simp at hk
                | cons u us ih =>
                    intro hf hs k hk hm
                    obtain ⟨v₁, hv₁, hv₂⟩ := fold_cons_ok.mp hf
                    cases k with
                    | zero =>
                        have := ((admit_nullifiers hv₁).1 n hm).1
                        simp [hs] at this
                    | succ k =>
                        exact ih hv₂ ((admit_nullifiers hv₁).2 n hs) k
                          (by simpa using hk) hm
              exact later h₂ spent₁ j (by simpa using hj) hnj
          | succ i =>
              exact fold_nullifiers h₂ i j (by simpa using hi) (by simpa using hj) n
                (by omega) hni hnj

end Nanodregg.Kernel
