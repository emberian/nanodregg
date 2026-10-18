/-
# Kernel.Proofs.Frame — what an admitted turn leaves alone, and what it can never undo

Frame: a cell the turn neither writes, retires nor bears is unchanged. ROM: a live ROM cell
is live and identical after every admitted turn, hence forever. Nullifiers: an admitted turn
spends each of its nullifiers exactly once — none was spent before, all are after — and the
spent set only grows, so across a log no nullifier is spent twice.
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.TrieMap
import Kernel.Proofs.Logic.Frame

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Frame.** A cell the turn neither writes, retires nor bears is unchanged. -/
theorem admit_frame {E : Env D} {w w' : World D} {t : Turn D} {c : D}
    (h : World.admit E w t = .ok w') (hl : ∀ x ∈ t.touches, x.cell = c → x.act = .keep)
    (hc : c ∉ createdIds t) : w'.entry E c = w.entry E c := by
  unfold World.entry
  rw [(admit_Frame h).cells (.cell c) (not_cellFoot_iff.mpr ⟨hl, hc⟩)]


/-- A live ROM cell is only ever kept: a write refuses `romWrite`, a retirement `romRetire`. -/
theorem rom_keep {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live E c = some cell)
    (hrom : cell.discipline = .rom) : ∀ x ∈ t.touches, x.cell = c → x.act = .keep := by
  intro x hx hxc
  obtain ⟨r, hr⟩ := hk.touch x hx
  obtain ⟨v, hv⟩ : ∃ v, w.entry E c = some (.live cell v) := by
    unfold World.live at hlive
    split at hlive
    · rename_i v he; simp only [Option.some.injEq] at hlive; exact ⟨v, hlive ▸ he⟩
    · simp at hlive
  unfold touchCheck at hr
  rw [hxc, hv] at hr
  simp only [except_bind_ok] at hr
  obtain ⟨⟨⟩, _, hr⟩ := hr
  cases ha : x.act with
  | keep => rfl
  | write ops =>
      rw [ha] at hr
      simp only [except_bind_ok] at hr
      obtain ⟨⟨⟩, _, _, hp, _⟩ := hr
      simp [postWrite, hrom] at hp
  | retire =>
      rw [ha] at hr
      simp only [except_bind_ok] at hr
      obtain ⟨⟨⟩, hp, _⟩ := hr
      simp [req, hrom] at hp

theorem live_taken {E : Env D} {w : World D} {c : D} {cell : Cell} (h : w.live E c = some cell) :
    w.taken E c = true := by
  unfold World.live at h; unfold World.taken
  cases hc : w.entry E c with
  | none => rw [hc] at h; simp at h
  | some e => simp

/-- A live cell's id is never born again (`idTaken`). -/
theorem live_not_created {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live E c = some cell) :
    c ∉ createdIds t := by
  intro hm
  have hc := hk.creates
  unfold checkCreates at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hf⟩ := hc
  have := (forEx_ok.mp hf) c hm
  simp [req, live_taken hlive] at this

/-- **ROM is forever, one step.** A live ROM cell is live and identical after an admitted turn. -/
theorem admit_rom {E : Env D} {w w' : World D} {t : Turn D} {c : D} {cell : Cell}
    (h : World.admit E w t = .ok w') (hlive : w.live E c = some cell) (hrom : cell.discipline = .rom) :
    w'.live E c = some cell := by
  obtain ⟨posts, hk, _⟩ := admit_ok h
  have hf := admit_frame h (rom_keep hk hlive hrom) (live_not_created hk hlive)
  unfold World.live at hlive ⊢
  rw [hf]; exact hlive

/-- **ROM is forever.** A live ROM cell survives, unchanged, every admitted log. -/
theorem fold_rom {E : Env D} {c : D} {cell : Cell} (hrom : cell.discipline = .rom)
    {w w' : World D} {l : List (Step D)} (h : World.fold E w l = .ok w')
    (hl : w.live E c = some cell) : w'.live E c = some cell :=
  fold_keeps (P := fun v => v.live E c = some cell) (fun hp ha => admit_rom ha hp hrom)
    (fun hp hr => (refuse_live hr c).trans hp) hl h

/-- **Nullifiers spend once.** Each nullifier of an admitted turn was unspent and is spent; the
spent set only grows. -/
theorem admit_nullifiers {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    (∀ n ∈ t.nullifiers, w.isSpent E n = false ∧ w'.isSpent E n = true) ∧
      ∀ n, w.isSpent E n = true → w'.isSpent E n = true := by
  obtain ⟨_, hk, rfl⟩ := admit_ok h
  refine ⟨fun n hn => ⟨?_, spendAll_spent_of_mem hn⟩, fun n hn => ?_⟩
  · have := (forEx_ok.mp hk.nullifiers) n hn
    rw [req_ok] at this
    simpa using this
  · by_cases hm : n ∈ t.nullifiers
    · exact spendAll_spent_of_mem hm
    · unfold World.isSpent
      rw [(admit_Frame h).cells (.nullifier n) fun f => by cases f with | spent hn' => exact hm hn']
      exact hn

/-- Across a log no nullifier is spent twice, and none was spent at the start. -/
theorem fold_nullifiers {E : Env D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold E w l = .ok w' →
      ∀ i j (hi : i < (Step.turns l).length) (hj : j < (Step.turns l).length) n, i < j →
        n ∈ ((Step.turns l)[i]'hi).nullifiers → n ∉ ((Step.turns l)[j]'hj).nullifiers
  | w, w', [], _ => by intro i _ hi; simp [Step.turns] at hi
  | w, w', .refusal r :: rest, h => by
      obtain ⟨w₁, _, h₂⟩ := fold_cons_ok.mp h
      exact fold_nullifiers (l := rest) h₂
  | w, w', .turn t :: rest, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      intro i j hi hj n hij hni hnj
      cases j with
      | zero => omega
      | succ j =>
          cases i with
          | zero =>
              -- n is spent after t; every later turn needs it unspent
              have spent₁ := ((admit_nullifiers h₁).1 n hni).2
              have later : ∀ {v v' : World D} {ls : List (Step D)}, World.fold E v ls = .ok v' →
                  v.isSpent E n = true → ∀ (k : Nat) (hk : k < (Step.turns ls).length),
                    n ∉ ((Step.turns ls)[k]'hk).nullifiers := by
                intro v v' ls
                induction ls generalizing v with
                | nil => intro _ _ k hk; simp [Step.turns] at hk
                | cons u us ih =>
                    intro hf hs k hk hm
                    obtain ⟨v₁, hv₁, hv₂⟩ := fold_cons_ok.mp hf
                    cases u with
                    | refusal q =>
                        exact ih hv₂ ((refuse_isSpent hv₁ n).trans hs) k hk hm
                    | turn u =>
                        cases k with
                        | zero =>
                            have := ((admit_nullifiers hv₁).1 n hm).1
                            simp [hs] at this
                        | succ k =>
                            exact ih hv₂ ((admit_nullifiers hv₁).2 n hs) k
                              (by simpa [Step.turns] using hk) hm
              exact later h₂ spent₁ j (by simpa [Step.turns] using hj) hnj
          | succ i =>
              exact fold_nullifiers h₂ i j (by simpa [Step.turns] using hi) (by simpa [Step.turns] using hj) n
                (by omega) hni hnj

/-! ## Reading a slot back, and every slot holds the leaf of its kind -/

theorem entry_get {E : Env D} {w : World D} {c : D} {e : Entry} (h : w.entry E c = some e) :
    w.trie.get (trieSpec E) (.cell c) = some (.entry e) := by
  unfold World.entry at h
  cases hg : w.trie.get (trieSpec E) (.cell c) with
  | none => rw [hg] at h; simp at h
  | some l =>
      rw [hg] at h
      cases l with
      | entry e' => simp only [Option.some.injEq] at h; rw [h]
      | spent => simp at h

theorem live_entry {E : Env D} {w : World D} {c : D} {cell : Cell} (h : w.live E c = some cell) :
    ∃ v, w.entry E c = some (.live cell v) := by
  unfold World.live at h
  cases he : w.entry E c with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h
      cases e with
      | live cell' v => simp only [Option.some.injEq] at h; exact ⟨v, by rw [h]⟩
      | tomb => simp at h

theorem get_live {E : Env D} {w : World D} {c : D} {cell : Cell} {v : Nat}
    (h : w.trie.get (trieSpec E) (.cell c) = some (.entry (.live cell v))) : w.live E c = some cell := by
  unfold World.live World.entry; rw [h]

theorem live_get {E : Env D} {w : World D} {c : D} {cell : Cell} (h : w.live E c = some cell) :
    ∃ v, w.trie.get (trieSpec E) (.cell c) = some (.entry (.live cell v)) := by
  obtain ⟨v, hv⟩ := live_entry h
  exact ⟨v, entry_get hv⟩

/-- Every slot of the World's map holds the leaf of its kind (`Leaf.fits`): a cell slot an entry,
a nullifier slot `spent`. Genesis does (`genesis_slotted`), and every admitted turn keeps it
(`admit_slotted`), since `commit` only writes those two pairings. -/
def World.Slotted (E : Env D) (w : World D) : Prop :=
  ∀ s l, w.trie.get (trieSpec E) s = some l → Leaf.fits s l = true

omit [Ord D] in
theorem insertAll_fits {E : Env D} :
    ∀ {m : Cells D} (ps : List (D × Entry)),
      (∀ s l, m.get (trieSpec E) s = some l → Leaf.fits s l = true) →
      ∀ s l, (insertAll E m ps).get (trieSpec E) s = some l → Leaf.fits s l = true
  | _, [], h => h
  | m, p :: rest, h => by
      apply insertAll_fits (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest
      intro s l hg
      rw [Trie.get_insert] at hg
      split at hg
      · rename_i hs; subst hs; simp only [Option.some.injEq] at hg; subst hg; rfl
      · exact h s l hg

omit [Ord D] in
theorem spendAll_fits {E : Env D} :
    ∀ {m : Cells D} (ns : List D),
      (∀ s l, m.get (trieSpec E) s = some l → Leaf.fits s l = true) →
      ∀ s l, (spendAll E m ns).get (trieSpec E) s = some l → Leaf.fits s l = true
  | _, [], h => h
  | m, n :: rest, h => by
      apply spendAll_fits (m := m.insert (trieSpec E) (.nullifier n) .spent) rest
      intro s l hg
      rw [Trie.get_insert] at hg
      split at hg
      · rename_i hs; subst hs; simp only [Option.some.injEq] at hg; subst hg; rfl
      · exact h s l hg

theorem genesis_slotted (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).Slotted E := by
  intro s l hg; simp [World.genesis, Trie.get_empty] at hg

theorem admit_slotted {E : Env D} {w w' : World D} {t : Turn D} (hf : w.Slotted E)
    (h : World.admit E w t = .ok w') : w'.Slotted E := by
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  exact spendAll_fits _ (insertAll_fits _ (insertAll_fits _ hf))

theorem fold_slotted {E : Env D} {w w' : World D} {l : List (Step D)} (hf : w.Slotted E)
    (h : World.fold E w l = .ok w') : w'.Slotted E :=
  fold_keeps (P := fun v => v.Slotted E) (fun hp ha => admit_slotted hp ha)
    (fun hp hr => fun s l hg => hp s l (by rw [← refuse_trie hr]; exact hg)) hf h

/-- In a World whose slots fit, a cell id with no entry has an empty slot. -/
theorem get_cell_none {E : Env D} {w : World D} (hf : w.Slotted E) {c : D} (h : w.entry E c = none) :
    w.trie.get (trieSpec E) (.cell c) = none := by
  cases hg : w.trie.get (trieSpec E) (.cell c) with
  | none => rfl
  | some l =>
      have hl := hf _ _ hg
      cases l with
      | entry e => unfold World.entry at h; rw [hg] at h; simp at h
      | spent => simp [Leaf.fits] at hl

end Nanodregg.Kernel
