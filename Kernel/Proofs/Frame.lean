/-
# Kernel.Proofs.Frame — what an admitted turn leaves alone, and what it can never undo

Frame: a cell no leg, retirement or birth of the turn names is unchanged. ROM: a live ROM cell
is live and identical after every admitted turn, hence forever. Nullifiers: an admitted turn
spends each of its nullifiers exactly once — none was spent before, all are after — and the
spent set only grows, so across a log no nullifier is spent twice.
-/
import Kernel.Proofs.Fold

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

omit [DecidableEq D] in
theorem insertAll_get_of_not_mem {c : D} :
    ∀ {m : Std.TreeMap D Entry compare} {ps : List (D × Cell)},
      c ∉ ps.map Prod.fst → (insertAll m ps)[c]? = m[c]?
  | m, [], _ => rfl
  | m, p :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      show (insertAll (m.insert p.1 (.live p.2)) rest)[c]? = m[c]?
      rw [insertAll_get_of_not_mem h.2, Std.TreeMap.getElem?_insert]
      have : compare p.1 c ≠ .eq := fun he => h.1 (Std.LawfulEqCmp.eq_of_compare he).symm
      simp [this]

omit [DecidableEq D] in
theorem tombAll_get_of_not_mem {c : D} :
    ∀ {m : Std.TreeMap D Entry compare} {cs : List D}, c ∉ cs → (tombAll m cs)[c]? = m[c]?
  | m, [], _ => rfl
  | m, x :: rest, h => by
      simp only [List.mem_cons, not_or] at h
      show (tombAll (m.insert x .tomb) rest)[c]? = m[c]?
      rw [tombAll_get_of_not_mem h.2, Std.TreeMap.getElem?_insert]
      have : compare x c ≠ .eq := fun he => h.1 (Std.LawfulEqCmp.eq_of_compare he).symm
      simp [this]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D] in
theorem postLeg_cell {w : World D} {l : Leg D} {p : D × Cell} (h : postLeg w l = .ok p) :
    p.1 = l.cell := by
  unfold postLeg at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, _, ⟨⟩, _, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
    · simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, _, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      rw [← h]

/-- **Frame.** A cell the turn neither writes, retires nor bears is unchanged. -/
theorem admit_frame {E : Env D} {w w' : World D} {t : Turn D} {c : D}
    (h : World.admit E w t = .ok w') (hl : c ∉ t.legs.map Leg.cell) (hr : c ∉ t.retires)
    (hc : c ∉ createdIds E t) : w'.cells[c]? = w.cells[c]? := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hkeys : posts.map Prod.fst = t.legs.map Leg.cell :=
    mapEx_map (fun _ _ hp => postLeg_cell hp) hk.legs
  have hcp : c ∉ (createdPairs E t).map Prod.fst := by
    intro hm
    apply hc
    unfold createdPairs at hm
    rw [List.map_fst_zip (by simp [createdIds])] at hm
    exact hm
  show (insertAll (tombAll (insertAll w.cells posts) t.retires) (createdPairs E t))[c]? = _
  rw [insertAll_get_of_not_mem hcp, tombAll_get_of_not_mem hr,
    insertAll_get_of_not_mem (by rw [hkeys]; exact hl)]

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A live ROM cell has no leg in an admitted turn (`postLeg` refuses `romWrite`). -/
theorem rom_no_leg {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Cell)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live c = some cell)
    (hrom : cell.discipline = .rom) : c ∉ t.legs.map Leg.cell := by
  intro hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  -- every leg's `postLeg` succeeded
  have : ∃ p, postLeg w l = .ok p := by
    clear hm
    have key : ∀ {ls : List (Leg D)} {ps : List (D × Cell)}, mapEx (postLeg w) ls = .ok ps →
        ∀ x ∈ ls, ∃ p, postLeg w x = .ok p := by
      intro ls
      induction ls with
      | nil => intro _ _ x hx; simp at hx
      | cons a rest ih =>
          intro ps hps x hx
          unfold mapEx at hps
          cases ha : postLeg w a with
          | error e => simp [ha] at hps
          | ok b =>
              cases hr : mapEx (postLeg w) rest with
              | error e => simp [ha, hr] at hps
              | ok bs =>
                  simp only [List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · exact ⟨b, ha⟩
                  · exact ih hr x hx
    exact key hk.legs l hl
  obtain ⟨p, hp⟩ := this
  unfold postLeg at hp
  rw [hlive] at hp
  simp [hrom] at hp

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- A live ROM cell is never retired by an admitted turn (`romRetire`). -/
theorem rom_no_retire {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Cell)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live c = some cell)
    (hrom : cell.discipline = .rom) : c ∉ t.retires := by
  intro hm
  have := (forEx_ok.mp hk.retires) c hm
  unfold checkRetire at this
  rw [hlive] at this
  simp [hrom, req] at this

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
theorem live_not_created {E : Env D} {w : World D} {t : Turn D} {posts : List (D × Cell)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live c = some cell) :
    c ∉ createdIds E t := by
  intro hm
  have hc := hk.creates
  unfold checkCreates at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, _, hf⟩ := hc
  have := (forEx_ok.mp hf) c hm
  simp [req, live_contains hlive] at this

/-- **ROM is forever, one step.** A live ROM cell is live and identical after an admitted turn. -/
theorem admit_rom {E : Env D} {w w' : World D} {t : Turn D} {c : D} {cell : Cell}
    (h : World.admit E w t = .ok w') (hlive : w.live c = some cell) (hrom : cell.discipline = .rom) :
    w'.live c = some cell := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  have hf := admit_frame h (rom_no_leg hk hlive hrom) (rom_no_retire hk hlive hrom)
    (live_not_created hk hlive)
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
