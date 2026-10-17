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

/-- Every check `admit` runs, as facts; `raw` is what each touch leaves (`none`: unchanged). -/
structure Checked (E : Env D) (w : World D) (t : Turn D) (posts : List (Post D)) : Prop where
  bounds : checkBounds t = .ok ()
  journal : checkJournal E w t = .ok ()
  shape : checkShape t = .ok ()
  window : checkWindow w t = .ok ()
  touches : ∃ raw, mapEx (touchCheck E w) t.touches = .ok raw ∧ posts = raw.reduceOption
  value : checkValue E t posts = .ok ()
  nullifiers : checkNullifiers E w t = .ok ()
  charge : checkCharge w t (credit posts) = .ok ()
  creates : checkCreates E w t = .ok ()

theorem check_ok {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (h : check E w t = .ok posts) : Checked E w t posts := by
  unfold check at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, ⟨⟩, h2, ⟨⟩, h3, ⟨⟩, h4, raw, h5, ⟨⟩, hv, ⟨⟩, h6, ⟨⟩, h7, ⟨⟩, h8, h9⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h9
  subst h9
  exact ⟨h1, h3, h4, h2, ⟨raw, h5, rfl⟩, hv, h6, h7, h8⟩

/-- Every touch of a checked turn passed `touchCheck`. -/
theorem Checked.touch {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hk : Checked E w t posts) : ∀ x ∈ t.touches, ∃ r, touchCheck E w x = .ok r := by
  obtain ⟨raw, hm, _⟩ := hk.touches
  exact mapEx_each hm

/-- A touch that passes saw what the signer saw. -/
theorem touchCheck_pin {E : Env D} {w : World D} {x : Touch D} {r : Option (Post D)}
    (h : touchCheck E w x = .ok r) : pinOf E (w.live E x.cell) = x.seen := by
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
  obtain ⟨_, _, rfl⟩ := admit_ok h; rfl

/-- **Charge exactness.** An admitted turn paid exactly its weight, could afford it with what
its touches give back, and the budget moved by exactly the charge less that credit (KERNEL-15). -/
theorem admit_charge {E : Env D} {w w' : World D} {t : Turn D}
    (h : World.admit E w t = .ok w') :
    t.charge = t.weight ∧ ∃ posts, Checked E w t posts ∧ t.charge ≤ w.allowance + credit posts ∧
      w'.allowance + t.charge = w.allowance + credit posts := by
  obtain ⟨posts, hc, rfl⟩ := admit_ok h
  have hch := hc.charge
  unfold checkCharge at hch
  simp only [except_bind_ok] at hch
  obtain ⟨⟨⟩, h1, h2⟩ := hch
  rw [req_ok, decide_eq_true_eq] at h1 h2
  refine ⟨h1, posts, hc, h2, ?_⟩
  show w.allowance + credit posts - t.charge + t.charge = w.allowance + credit posts
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
    (h : World.admit E w t = .ok w') : ∀ x ∈ t.touches, pinOf E (w.live E x.cell) = x.seen := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  intro x hx
  obtain ⟨_, hr⟩ := hc.touch x hx
  exact touchCheck_pin hr

/-- **The staleness refusal.** A turn whose pin disagrees with the World is admitted by no
World transition. -/
theorem stale_refused {E : Env D} {w : World D} {t : Turn D} {x : Touch D}
    (hmem : x ∈ t.touches) (hstale : pinOf E (w.live E x.cell) ≠ x.seen) :
    ∀ w', World.admit E w t ≠ .ok w' :=
  fun _ h => hstale (admit_pins h x hmem)

/-- A stale touch is refused `stale` before anything about its write or retirement is judged. -/
theorem touchCheck_stale {E : Env D} {w : World D} {x : Touch D}
    (hstale : pinOf E (w.live E x.cell) ≠ x.seen) : touchCheck E w x = .error (.stale x.cell) := by
  unfold touchCheck
  simp [req, hstale, bind, Except.bind]

/-- **Stale BY NAME.** If the checks before the touches pass and the first touch that fails is
stale, the turn is refused `stale` naming that cell. -/
theorem stale_named {E : Env D} {w : World D} {t : Turn D} {pre post : List (Touch D)}
    {x : Touch D} (hb : checkBounds t = .ok ()) (hj : checkJournal E w t = .ok ())
    (hs : checkShape t = .ok ()) (hw : checkWindow w t = .ok ())
    (ht : t.touches = pre ++ x :: post) (hpre : ∀ y ∈ pre, ∃ r, touchCheck E w y = .ok r)
    (hstale : pinOf E (w.live E x.cell) ≠ x.seen) :
    World.admit E w t = .error (.stale x.cell) := by
  have hm : mapEx (touchCheck E w) t.touches = .error (.stale x.cell) := by
    rw [ht]; exact mapEx_error_at (touchCheck_stale hstale) post hpre
  unfold World.admit check
  simp [hb, hj, hs, hw, hm, bind, Except.bind]

/-- A retry of an admitted transaction inside its window is answered `replayed` with its
height, whatever else is true of the World now (only the static bounds and the window are
checked first: an expired retry is `outsideWindow` whether or not its entry was pruned,
KERNEL-33). -/
theorem replay_named {E : Env D} {w : World D} {t : Turn D} {h : Nat} {d : D}
    (hb : checkBounds t = .ok ()) (hw : checkWindow w t = .ok ())
    (hj : w.journalAt E t.txId = some (h, d)) :
    World.admit E w t = .error (.replayed h) := by
  have : checkJournal E w t = .error (.replayed h) := by simp [checkJournal, hj]
  unfold World.admit check
  simp [hb, hw, this, bind, Except.bind]

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
  · exact Trie.get_retainAt (journalSpec E) _ [] hj (fun _ _ _ => trivial) k
  · rfl

omit [Ord D] [DecidableEq D] in
/-- A prune keeps the journal trie canonical (`Trie.canon_retainAt` at the root). -/
theorem pruneJournal_canon {E : Env D} {H : Nat} {j : Journal D} (hj : Trie.Canon (journalSpec E) 0 j) :
    Trie.Canon (journalSpec E) 0 (pruneJournal E H j) := by
  unfold pruneJournal
  split
  · exact Trie.canon_retainAt (journalSpec E) _ [] 0 j hj (fun _ _ _ => trivial)
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

end Nanodregg.Kernel
