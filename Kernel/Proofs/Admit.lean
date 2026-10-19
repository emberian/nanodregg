/-
# Kernel.Proofs.Admit — what an admitted turn guarantees

Every theorem here is about `World.admit` itself (the receive path), not about a model of it.
-/
import Kernel.World
import Kernel.Proofs.Check
import Kernel.Proofs.TrieRetain

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
/-- Distinct constructors have distinct wire names (law 7): equal names, same constructor. -/
theorem Reject.name_injective (a b : Reject D) (h : a.name = b.name) : a.ctorIdx = b.ctorIdx := by
  cases a <;> cases b <;> simp_all [Reject.name] <;> rfl

omit [Ord D] [DecidableEq D] in
/-- A passing `noDup` found no duplicate. -/
theorem noDup_none {α : Type} [Ord α] {l : List α} {e : α → Reject D}
    (h : noDup l e = .ok ()) : firstDup l = none := by
  unfold noDup at h
  cases hf : firstDup l with
  | none => rfl
  | some a => rw [hf] at h; cases h

/-- Every check `admit` runs, as facts; `raw` is what each touch leaves (`none`: unchanged). -/
structure Checked (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Prop where
  bounds : checkBounds t = .ok ()
  journal : checkJournal E w t = .ok ()
  shape : checkShape t = .ok ()
  window : checkWindow w t = .ok ()
  steps : checkSteps w = .ok ()
  touches : ∃ raw, mapEx (touchCheck E w) t.touches = .ok raw ∧ posts = raw.reduceOption
  value : checkValue E t posts = .ok ()
  nullifiers : checkNullifiers E w t = .ok ()
  charge : checkCharge w t (credit posts + (rowsAfter E w t).2) = .ok ()
  creates : checkCreates E w t = .ok ()
  rowsRemain : checkRowsRemain E w t = .ok ()
  ranges : checkRanges E w t = .ok ()
  rows : rowsRun E w t = .ok (rowsAfter E w t)

theorem check_ok {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (h : check E w t = .ok posts) : Checked E w t posts := by
  obtain ⟨rr₀, h⟩ : ∃ rr₀, checkWith E w t = .ok (posts, rr₀) := by
    unfold check at h
    cases hc : checkWith E w t with
    | error r => rw [hc] at h; cases h
    | ok pr => rw [hc] at h; cases h; exact ⟨pr.2, rfl⟩
  unfold checkWith at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, ⟨⟩, h3, ⟨⟩, h4, raw, h5, ⟨⟩, hv, ⟨⟩, h6, ⟨⟩, hrr, ⟨⟩, hrg, rr, hrw, ⟨⟩, h7,
    ⟨⟩, h8, ⟨⟩, hs, h9⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h9
  obtain ⟨h9, -⟩ := h9
  subst h9
  have ha : rowsAfter E w t = rr := by unfold rowsAfter; rw [hrw]
  rw [← ha] at hrw h7
  exact ⟨h1, h3, h4, h2, hs, ⟨raw, h5, rfl⟩, hv, h6, h7, h8, hrr, hrg, hrw⟩

/-- Every touch of a checked turn passed `touchCheck`. -/
theorem Checked.touch {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) : ∀ x ∈ t.touches, ∃ r, touchCheck E w x = .ok r := by
  obtain ⟨raw, hm, _⟩ := hk.touches
  exact mapEx_each hm

/-- A touch that passes saw what the signer saw. -/
theorem touchCheck_pin {E : Env D} {w : World D} {x : Touch D} {r : Option (Post D)}
    (h : touchCheck E w x = .ok r) : pinOf E (w.entry E x.cell) = x.seen := by
  unfold touchCheck at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hp, _⟩ := h
  exact of_decide_eq_true (req_ok.mp hp)

theorem admit_ok {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    ∃ posts, Checked E w t posts ∧ w' = commit E w t posts := by
  unfold World.admit at h
  cases hc : check E w t with
  | error r => simp [hc] at h
  | ok posts =>
      simp [hc] at h
      exact ⟨posts, check_ok hc, h.symm⟩

theorem admit_height {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : w'.height = w.height + 1 := by
  obtain ⟨_, _, rfl⟩ := admit_ok h; rfl

/-- The chain commits to the root AFTER the turn (KERNEL-23 (d)). -/
theorem admit_chain {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : w'.chain = chainNext E w.chain t (w'.roots E) := by
  obtain ⟨_, _, rfl⟩ := admit_ok h
  rfl

omit [DecidableEq D] in
/-- **The roots a read recomputes are the roots' own digests** (cv 01a15107-2272): `World.roots`
takes the four roots through ONE shared lazy empty digest (`rootsOf`), and that is the digest of
the four roots' `hashOf`, each empty trie's being the empty digest. So sharing the empty digest
changed no roots value: no head, record or proof digest moves. -/
theorem World.roots_eq (E : Env D) (w : World D) :
    w.roots E = rootsDigest E (w.root E) (w.journalRoot E) (w.refusalsRoot E) (w.rowsRoot E) := by
  unfold World.roots rootsOf World.root World.journalRoot World.refusalsRoot World.rowsRoot
  dsimp only
  rw [Trie.rootWith_eq (trieSpec E) _ _ rfl, Trie.rootWith_eq (journalSpec E) _ _ rfl,
    Trie.rootWith_eq (refusalSpec E) _ _ rfl, Trie.rootWith_eq (rowSpec E) _ _ rfl]

/-- **Charge exactness.** An admitted turn paid exactly its weight, could afford it with what
its touches and its row touches give back, and the budget moved by exactly the charge less that
credit (KERNEL-15, KERNEL-48). -/
theorem admit_charge {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    t.charge = t.weight ∧ ∃ posts, Checked E w t posts ∧
      t.charge ≤ w.allowance + credit posts + (rowsAfter E w t).2 ∧
      w'.allowance + t.charge = w.allowance + credit posts + (rowsAfter E w t).2 := by
  obtain ⟨posts, hc, rfl⟩ := admit_ok h
  have hch := hc.charge
  unfold checkCharge at hch
  simp only [except_bind_ok] at hch
  obtain ⟨⟨⟩, h1, h2⟩ := hch
  rw [req_ok, decide_eq_true_eq] at h1 h2
  refine ⟨h1, posts, hc, by omega, ?_⟩
  show w.allowance + credit posts + (rowsAfter E w t).2 - t.charge + t.charge =
    w.allowance + credit posts + (rowsAfter E w t).2
  omega

/-- **The weight bound.** An admitted turn costs at most `Bounds.weightMax`, its log record
included: the static budget HOST sizes a turn record and a batch by. A batch of `n` admitted
turns appends at most `n * Bounds.weightMax` record bytes, by CODEC's equality
`Codec.Deployed.turnBytes_size : (env.turnBytes t).size = t.logWeight` (generic:
`Codec.Kernel.turn_size_logWeight` at any 32-byte digest codec). -/
theorem admit_weight {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    t.charge = t.weight ∧ t.logWeight ≤ t.weight ∧ t.weight ≤ Bounds.weightMax := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have hb := hc.bounds
  unfold checkBounds at hb
  simp only [except_bind_ok] at hb
  obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hw, _⟩ := hb
  rw [req_ok, decide_eq_true_eq] at hw
  exact ⟨(admit_charge h).1, Nat.le_add_right _ _, hw⟩

/-- **Guards from the intent.** Every cell the turn touches is, in the pre-state, exactly what
the signer saw. -/
theorem admit_pins {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') : ∀ x ∈ t.touches, pinOf E (w.entry E x.cell) = x.seen := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  intro x hx
  obtain ⟨_, hr⟩ := hc.touch x hx
  exact touchCheck_pin hr

/-- **The staleness refusal.** A turn whose pin disagrees with the World is admitted by no
World transition. -/
theorem stale_refused {E : Env D} {w : World D} {t : Turn D} {x : Touch D}
    (hmem : x ∈ t.touches) (hstale : pinOf E (w.entry E x.cell) ≠ x.seen) :
    ∀ w', World.admit E w t ≠ .ok w' :=
  fun _ h => hstale (admit_pins h x hmem)

/-- A stale touch is refused `stale` before anything about its write or retirement is judged. -/
theorem touchCheck_stale {E : Env D} {w : World D} {x : Touch D}
    (hstale : pinOf E (w.entry E x.cell) ≠ x.seen) : touchCheck E w x = .error (.stale x.cell) := by
  unfold touchCheck
  simp [req, hstale, bind, Except.bind]

/-- **Stale BY NAME.** If the checks before the touches pass and the first touch that fails is
stale, the turn is refused `stale` naming that cell. -/
theorem stale_named {E : Env D} {w : World D} {t : Turn D} {pre post : List (Touch D)}
    {x : Touch D} (hb : checkBounds t = .ok ()) (hj : checkJournal E w t = .ok ())
    (hs : checkShape t = .ok ()) (hw : checkWindow w t = .ok ())
    (ht : t.touches = pre ++ x :: post) (hpre : ∀ y ∈ pre, ∃ r, touchCheck E w y = .ok r)
    (hstale : pinOf E (w.entry E x.cell) ≠ x.seen) :
    World.admit E w t = .error (.stale x.cell) := by
  have hm : mapEx (touchCheck E w) t.touches = .error (.stale x.cell) := by
    rw [ht]; exact mapEx_error_at (touchCheck_stale hstale) post hpre
  unfold World.admit check checkWith
  simp [hb, hj, hs, hw, hm, bind, Except.bind, Except.map]

/-- A retry of an admitted transaction inside its window is answered `replayed` with its
height, whatever else is true of the World now (only the static bounds and the window are
checked first: an expired retry is `outsideWindow` whether or not its entry was pruned,
KERNEL-33). -/
theorem replay_named {E : Env D} {w : World D} {t : Turn D} {h : Nat} {d : D}
    (hb : checkBounds t = .ok ()) (hw : checkWindow w t = .ok ())
    (hj : w.journalAt E t.txId = some (h, d)) :
    World.admit E w t = .error (.replayed h) := by
  have : checkJournal E w t = .error (.replayed h) := by simp [checkJournal, hj]
  unfold World.admit check checkWith
  simp [hb, hw, this, bind, Except.bind, Except.map]

/-- The World's journal trie is canonical (`Trie.Canon` at the root, KERNEL-41): what a lookup
after a prune rests on. Genesis gives it, every insert and prune keeps it (`admit_journalCanon`). -/
def World.JournalCanon (E : Env D) (w : World D) : Prop := Trie.Canon (journalSpec E) 0 w.journal

/-- The journal after a commit IS the default-form insert then prune (the shared empty-digest thunk
reduced). -/
theorem commit_journal {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} :
    (commit E w t posts).journal =
      pruneJournal E (w.height + 1) (w.journal.insert (journalSpec E) t.txId (w.height + 1, turnDigest E t)) := rfl

omit [Ord D] in
/-- A lookup in the pruned journal: at a multiple of `windowMax`, the entry if it is `kept`;
otherwise the entry. Exact on a canonical trie (`Trie.get_retainAt` at the root). -/
theorem pruneJournal_get {E : Env D} {H : Nat} {j : Journal D} (hj : Trie.Canon (journalSpec E) 0 j)
    (k : D) :
    (pruneJournal E H j).get (journalSpec E) k =
      if H % Bounds.windowMax = 0 then (j.get (journalSpec E) k).filter (kept H) else j.get (journalSpec E) k := by
  unfold pruneJournal
  split
  · exact Trie.get_retainAt (journalSpec E) _ [] hj (fun _ _ _ _ _ _ h => by simp at h) k
  · rfl

omit [Ord D] [DecidableEq D] in
/-- A prune keeps the journal trie canonical (`Trie.canon_retainAt` at the root). -/
theorem pruneJournal_canon {E : Env D} {H : Nat} {j : Journal D} (hj : Trie.Canon (journalSpec E) 0 j) :
    Trie.Canon (journalSpec E) 0 (pruneJournal E H j) := by
  unfold pruneJournal
  split
  · exact Trie.canon_retainAt (journalSpec E) _ [] 0 j hj (fun _ _ _ _ _ _ h => by simp at h)
  · exact hj

/-- **Every admission keeps the journal trie canonical.** -/
theorem admit_journalCanon {E : Env D} {w w' : World D} {t : Turn D} (hc : w.JournalCanon E)
    (h : World.admit E w t = .ok w') : w'.JournalCanon E := by
  obtain ⟨_, _, rfl⟩ := admit_ok h
  unfold World.JournalCanon
  rw [commit_journal]
  exact pruneJournal_canon (Trie.canon_insert _ _ _ hc)

omit [DecidableEq D] in
theorem genesis_journalCanon (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).JournalCanon E :=
  Trie.canon_empty _ 0

/-- An admitted transaction was new. -/
theorem admit_new {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w.journalAt E t.txId = none := by
  obtain ⟨_, hc, rfl⟩ := admit_ok h
  have hj := hc.journal
  unfold checkJournal at hj
  cases hjt : w.journalAt E t.txId with
  | none => rfl
  | some e =>
      obtain ⟨hh, d⟩ := e
      simp [hjt] at hj

/-- The committed journal read at any id, on a canonical journal: the turn's own entry at its id
(pruning never drops it: it was admitted at this height), else the old entry, filtered if this
height prunes. -/
theorem commit_journalAt {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hc : w.JournalCanon E) (k : D) :
    (commit E w t posts).journalAt E k =
      if k = t.txId then some (w.height + 1, turnDigest E t)
      else if (w.height + 1) % Bounds.windowMax = 0 then (w.journalAt E k).filter (kept (w.height + 1))
      else w.journalAt E k := by
  unfold World.journalAt
  rw [commit_journal, pruneJournal_get (Trie.canon_insert _ _ _ hc), Trie.get_insert]
  by_cases hk : k = t.txId
  · subst hk
    simp only [if_true]
    split
    · simp [Option.filter, kept, Bounds.windowMax]
    · rfl
  · simp only [hk, if_false]

/-- **An admitted transaction is journalled** at the new height with its digest (on a canonical
journal: every reached World's, `JournalOk`). -/
theorem admit_journaled {E : Env D} {w w' : World D} {t : Turn D} (hc : w.JournalCanon E)
    (h : World.admit E w t = .ok w') :
    w'.journalAt E t.txId = some (w.height + 1, turnDigest E t) := by
  obtain ⟨posts, _, rfl⟩ := admit_ok h
  rw [commit_journalAt hc]; simp

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
/-- Writing entries leaves at a written id one of the entries written there. -/
theorem insertAll_get_mem {E : Env D} {c : D} :
    ∀ {m : Cells D} {ps : List (D × Entry)}, c ∈ ps.map Prod.fst →
      ∃ e, (c, e) ∈ ps ∧ (insertAll E m ps).get (trieSpec E) (.cell c) = some (.entry e)
  | m, [], h => by simp at h
  | m, p :: rest, h => by
      by_cases hr : c ∈ rest.map Prod.fst
      · obtain ⟨e, he, hg⟩ := insertAll_get_mem (m := m.insert (trieSpec E) (.cell p.1) (.entry p.2)) hr
        exact ⟨e, List.mem_cons_of_mem _ he, hg⟩
      · have hc : p.1 = c := by
          simp only [List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact h.symm
          · exact absurd h hr
        refine ⟨p.2, by rw [← hc]; exact List.mem_cons_self, ?_⟩
        show (insertAll E (m.insert (trieSpec E) (.cell p.1) (.entry p.2)) rest).get _ _ = _
        rw [insertAll_get_of_not_mem hr, hc, Trie.get_insert_self]

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

/-- **The batch is the sequential trie** (cv 01a15107-2281): `commitTrie`'s one pass on the dirty
overlay is `spendAll` over `insertAll` over `insertAll`, each key in turn, as a `T` value (cached
digests included). No premise. Every proof about the map after a turn reads this shape. -/
theorem commitTrie_eq {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} :
    commitTrie E w t posts =
      spendAll E (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) t.nullifiers := by
  unfold commitTrie insertAll spendAll
  simp only [Trie.insertAll_eq_foldl, List.map_append, List.foldl_append, List.foldl_map]

/-- `commit`'s trie, in the proofs' shape. -/
theorem commit_trie_eq {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} :
    (commit E w t posts).trie =
      spendAll E (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)) t.nullifiers :=
  commitTrie_eq

/-- A turn's map, read at a cell: its touches' and births' entries over the pre-state's. -/
theorem commitTrie_cell {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} {c : D} :
    (commitTrie E w t posts).get (trieSpec E) (.cell c) =
      (insertAll E (insertAll E w.trie (posts.map Post.pair)) (bornEntries t)).get (trieSpec E) (.cell c) := by
  rw [commitTrie_eq]; exact spendAll_get_cell

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
      rcases hc : w.entry E x.cell with _ | ⟨_ | _⟩
      · rw [hc] at h; simp at h
      · rw [hc] at h
        simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        obtain ⟨⟨⟩, _, _, _, rfl⟩ := h
        simp
      · rw [hc] at h; simp at h
  | retire =>
      rw [ha] at h
      rcases hc : w.entry E x.cell with _ | ⟨_ | _⟩
      · rw [hc] at h; simp at h
      · rw [hc] at h
        simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        obtain ⟨⟨⟩, _, rfl⟩ := h
        simp
      · rw [hc] at h; simp at h


/-- What a checked turn changes is exactly at its non-`keep` touches. -/
theorem posts_touched {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) : ∀ p ∈ posts, ∃ x ∈ t.touches, p.cell = x.cell ∧ x.act ≠ .keep := by
  obtain ⟨raw, hm, rfl⟩ := hk.touches
  intro p hp
  have hp : some p ∈ raw := by simpa [List.reduceOption, List.mem_filterMap] using hp
  obtain ⟨x, hx, hr⟩ := mapEx_mem hm (some p) hp
  exact ⟨x, hx, touchCheck_some hr⟩

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

omit [Ord D] in
theorem spendAll_get_nul {E : Env D} {n : D} :
    ∀ {m : Cells D} {ns : List D},
      (spendAll E m ns).get (trieSpec E) (.nullifier n) =
        if n ∈ ns then some .spent else m.get (trieSpec E) (.nullifier n)
  | m, [] => by simp [spendAll]
  | m, x :: rest => by
      show (spendAll E (m.insert (trieSpec E) (.nullifier x) .spent) rest).get _ _ = _
      rw [spendAll_get_nul, Trie.get_insert]
      by_cases hr : n ∈ rest
      · simp [hr]
      · by_cases hx : n = x
        · subst hx; simp
        · have : (Slot.nullifier n : Slot D) ≠ .nullifier x := by intro e; injection e with e; exact hx e
          simp [hr, hx, this]

/-- The map after a turn, at a nullifier: spent if the turn spends it, else as before. -/
theorem commitTrie_nul {E : Env D} {w' : World D} {t : Turn D} {posts : List (Post D)} {n : D} :
    (commitTrie E w' t posts).get (trieSpec E) (.nullifier n) =
      if n ∈ t.nullifiers then some .spent else w'.trie.get (trieSpec E) (.nullifier n) := by
  rw [commitTrie_eq, spendAll_get_nul, insertAll_get_nullifier, insertAll_get_nullifier]

end Nanodregg.Kernel
