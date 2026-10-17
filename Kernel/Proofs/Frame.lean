/-
# Kernel.Proofs.Frame — what an admitted turn leaves alone, and what it can never undo

Frame: a cell the turn neither writes, retires nor bears is unchanged. ROM: a live ROM cell
is live and identical after every admitted turn, hence forever. Nullifiers: an admitted turn
spends each of its nullifiers exactly once — none was spent before, all are after — and the
spent set only grows, so across a log no nullifier is spent twice.
-/
import Kernel.Proofs.Fold
import Kernel.Proofs.TrieMap

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The map under a turn's writes -/

omit [Ord D] in
theorem insertAll_get_of_not_mem {E : Env D} {c : D} :
    ∀ {m : Cells D} {ps : List (D × Entry)},
      c ∉ ps.map Prod.fst → (insertAll E m ps).get (trieSpec E) (.cell c) = m.get (trieSpec E) (.cell c)
  | m, [], _ => rfl
  | m, p :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ = _
      rw [insertAll_get_of_not_mem h.2, Trie.get_insert, if_neg]
      intro he; injection he with he; exact h.1 he

omit [Ord D] in
/-- Writing cell entries leaves every nullifier slot alone. -/
theorem insertAll_get_nullifier {E : Env D} {n : D} :
    ∀ {m : Cells D} {ps : List (D × Entry)},
      (insertAll E m ps).get (trieSpec E) (.nullifier n) = m.get (trieSpec E) (.nullifier n)
  | m, [] => rfl
  | m, p :: rest => by
      show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ = _
      rw [insertAll_get_nullifier, Trie.get_insert, if_neg]; intro he; cases he

omit [Ord D] in
/-- Spending nullifiers leaves every cell slot alone. -/
theorem spendAll_get_cell {E : Env D} {c : D} :
    ∀ {m : Cells D} {ns : List D},
      (spendAll E m ns).get (trieSpec E) (.cell c) = m.get (trieSpec E) (.cell c)
  | m, [] => rfl
  | m, x :: rest => by
      show (spendAll E (m.insert (trieSpec E) (.nullifier x) .spent) rest).get _ _ = _
      rw [spendAll_get_cell, Trie.get_insert, if_neg]; intro he; cases he

/-- A turn's map, read at a cell: its touches' and births' entries over the pre-state's. -/
theorem commitTrie_cell {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} {c : D} :
    (commitTrie E w t posts).get (trieSpec E) (.cell c) =
      (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)).get (trieSpec E) (.cell c) :=
  spendAll_get_cell

theorem commitTrie_entry {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} {c : D}
    (hp : c ∉ (posts.map Post.pair).map Prod.fst) (hb : c ∉ (bornEntries t).map Prod.fst) :
    (commitTrie E w t posts).get (trieSpec E) (.cell c) = w.trie.get (trieSpec E) (.cell c) := by
  rw [commitTrie_cell, insertAll_get_of_not_mem hb, insertAll_get_of_not_mem hp]


/-- A touch that leaves something behind leaves it at its own cell, and is not a `keep`. -/
theorem touchCheck_some {E : Env D} {w : World D} {x : Touch D} {p : Post D}
    (h : touchCheck E w x = .ok (some p)) : p.cell = x.cell ∧ x.act ≠ .keep := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, h⟩ := h
  cases ha : x.act with
  | keep => rw [ha] at h; simp [pure, Except.pure] at h
  | write ops =>
      rw [ha] at h
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp
  | retire =>
      rw [ha] at h
      cases hc : w.live E x.cell with
      | none => rw [hc] at h; simp at h
      | some cell =>
          rw [hc] at h
          simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp


/-- What a checked turn changes is exactly at its non-`keep` touches. -/
theorem posts_touched {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) : ∀ p ∈ posts, ∃ x ∈ t.touches, p.cell = x.cell ∧ x.act ≠ .keep := by
  obtain ⟨raw, hm, rfl⟩ := hk.touches
  intro p hp
  have hp : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hp
  obtain ⟨x, hx, hr⟩ := mapEx_mem hm (some p) hp
  exact ⟨x, hx, touchCheck_some hr⟩

/-- **Frame.** A cell the turn neither writes, retires nor bears is unchanged. -/
theorem admit_frame {E : Env D} {w w' : World D} {t : Turn D} {c : D}
    (h : World.admit E w t = .ok w') (hl : ∀ x ∈ t.touches, x.cell = c → x.act = .keep)
    (hc : c ∉ createdIds t) : w'.entry E c = w.entry E c := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  have hcp : c ∉ (bornEntries t).map Prod.fst := by
    intro hm
    apply hc
    unfold bornEntries at hm
    rw [List.map_map] at hm
    have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2)) = Prod.fst := rfl
    rw [this] at hm
    exact hm
  have hpc : c ∉ (posts.map Post.pair).map Prod.fst := by
    intro hm
    rw [List.map_map] at hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨x, hx, he, hne⟩ := posts_touched hk p hp
    exact hne (hl x hx he.symm)
  unfold World.entry
  rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_entry hpc hcp]


/-- A live ROM cell is only ever kept: a write refuses `romWrite`, a retirement `romRetire`. -/
theorem rom_keep {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) {c : D} {cell : Cell} (hlive : w.live E c = some cell)
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
theorem fold_rom {E : Env D} {c : D} {cell : Cell} (hrom : cell.discipline = .rom) :
    ∀ {w w' : World D} {l : List (Turn D)}, World.fold E w l = .ok w' →
      w.live E c = some cell → w'.live E c = some cell
  | w, w', [], h, hl => by simp [World.fold] at h; subst h; exact hl
  | w, w', t :: rest, h, hl => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_rom hrom h₂ (admit_rom h₁ hl hrom)

omit [Ord D] in
theorem spendAll_spent_of_spent {E : Env D} {n : D} :
    ∀ {m : Cells D} {ns : List D}, (m.get (trieSpec E) (.nullifier n)).isSome = true →
      ((spendAll E m ns).get (trieSpec E) (.nullifier n)).isSome = true
  | m, [], h => h
  | m, x :: rest, h => by
      show ((spendAll E (m.insert (trieSpec E) (.nullifier x) .spent) rest).get _ _).isSome = true
      apply spendAll_spent_of_spent
      rw [Trie.get_insert]; split <;> simp_all

omit [Ord D] in
theorem spendAll_spent_of_mem {E : Env D} {n : D} :
    ∀ {m : Cells D} {ns : List D}, n ∈ ns →
      ((spendAll E m ns).get (trieSpec E) (.nullifier n)).isSome = true
  | m, [], h => by simp at h
  | m, x :: rest, h => by
      show ((spendAll E (m.insert (trieSpec E) (.nullifier x) .spent) rest).get _ _).isSome = true
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · apply spendAll_spent_of_spent; rw [Trie.get_insert_self]; rfl
      · exact spendAll_spent_of_mem h

theorem commitTrie_spent {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} {n : D}
    (h : (w.trie.get (trieSpec E) (.nullifier n)).isSome = true) :
    ((commitTrie E w t posts).get (trieSpec E) (.nullifier n)).isSome = true := by
  unfold commitTrie; apply spendAll_spent_of_spent; rw [insertAll_get_nullifier, insertAll_get_nullifier]; exact h

/-- **Nullifiers spend once.** Each nullifier of an admitted turn was unspent and is spent; the
spent set only grows. -/
theorem admit_nullifiers {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    (∀ n ∈ t.nullifiers, w.isSpent E n = false ∧ w'.isSpent E n = true) ∧
      ∀ n, w.isSpent E n = true → w'.isSpent E n = true := by
  obtain ⟨_, hk, rfl⟩ := admit_ok h
  refine ⟨fun n hn => ⟨?_, spendAll_spent_of_mem hn⟩, fun n hn => commitTrie_spent hn⟩
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
                  v.isSpent E n = true → ∀ (k : Nat) (hk : k < ls.length),
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
    w.entry E c = some (.live cell) := by
  unfold World.live at h
  cases he : w.entry E c with
  | none => rw [he] at h; simp at h
  | some e =>
      rw [he] at h
      cases e with
      | live cell' => simp only [Option.some.injEq] at h; rw [h]
      | tomb => simp at h

theorem get_live {E : Env D} {w : World D} {c : D} {cell : Cell}
    (h : w.trie.get (trieSpec E) (.cell c) = some (.entry (.live cell))) : w.live E c = some cell := by
  unfold World.live World.entry; rw [h]

theorem live_get {E : Env D} {w : World D} {c : D} {cell : Cell} (h : w.live E c = some cell) :
    w.trie.get (trieSpec E) (.cell c) = some (.entry (.live cell)) := entry_get (live_entry h)

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

theorem fold_slotted {E : Env D} :
    ∀ {w w' : World D} {l : List (Turn D)}, w.Slotted E → World.fold E w l = .ok w' → w'.Slotted E
  | w, w', [], hf, h => by simp [World.fold] at h; subst h; exact hf
  | w, w', t :: rest, hf, h => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      exact fold_slotted (admit_slotted hf h₁) h₂

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
