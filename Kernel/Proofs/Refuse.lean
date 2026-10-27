/-
# Kernel.Proofs.Refuse — what a recorded refusal does to a World, and the one step of a log

KERNEL-44 / KERNEL-47. `World.refuse` moves the refusals trie, the step counter and the chain, and
nothing else (`refuse_frame`): no cell, journal entry, height or budget. `World.step` is the one
transition of a log; the facts every fold theorem inducts over are here, one per field, for both
arms.
-/
import Kernel.Proofs.Admit

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

theorem refuse_ok {E : Env D} {w w' : World D} {r : Refused D}
    (h : World.refuse E w r = .ok w') : checkRefusal E w r = .ok () ∧ w' = commitRefusal E w r := by
  unfold World.refuse at h
  cases hc : checkRefusal E w r with
  | error e => simp [hc] at h
  | ok u => simp [hc] at h; exact ⟨rfl, h.symm⟩

/-- **A refusal touches no cell, no journal entry, no height, no budget, no origin.** -/
theorem refuse_frame {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.trie = w.trie ∧ w'.journal = w.journal ∧ w'.height = w.height ∧ w'.allowance = w.allowance ∧
      w'.origin = w.origin := by
  obtain ⟨_, rfl⟩ := refuse_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem refuse_trie {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.trie = w.trie := (refuse_frame h).1

/-- No cell reader sees a refusal: every read of the cells' trie is the same after it. -/
theorem refuse_entry {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') (c : D) :
    w'.entry E c = w.entry E c := by
  unfold World.entry; rw [refuse_trie h]

theorem refuse_live {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') (c : D) :
    w'.live E c = w.live E c := by
  unfold World.live; rw [refuse_entry h]

theorem refuse_isSpent {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') (n : D) :
    w'.isSpent E n = w.isSpent E n := by
  unfold World.isSpent; rw [refuse_trie h]

theorem refuse_journalAt {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') (k : D) :
    w'.journalAt E k = w.journalAt E k := by
  unfold World.journalAt; rw [(refuse_frame h).2.1]

theorem refuse_steps {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.steps = w.steps + 1 := by
  obtain ⟨_, rfl⟩ := refuse_ok h; rfl

/-- The chain commits the roots AFTER the refusal, by the refusal's own link (kind byte 1). -/
theorem refuse_chain {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.chain = refusalLink E w.chain r (w'.roots E) := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  rfl

theorem admit_steps {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w'.steps = w.steps + 1 := by
  obtain ⟨_, _, rfl⟩ := admit_ok h; rfl

/-! ## The step counter stays below `2^64` -/

omit [DecidableEq D] in
theorem checkSteps_lt {w : World D} (h : checkSteps w = .ok ()) : w.steps + 1 < 2 ^ 64 := by
  unfold checkSteps at h
  have := req_ok.mp h
  simp only [decide_eq_true_eq] at this
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  omega

theorem admit_steps_lt {E : Env D} {w w' : World D} {t : Turn D} (h : World.admit E w t = .ok w') :
    w'.steps < 2 ^ 64 := by
  obtain ⟨_, hc, _⟩ := admit_ok h
  have := checkSteps_lt hc.steps
  rw [admit_steps h]; exact this

theorem refuse_steps_lt {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.steps < 2 ^ 64 := by
  obtain ⟨hc, _⟩ := refuse_ok h
  unfold checkRefusal at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, -, ⟨⟩, hs, -⟩ := hc
  rw [refuse_steps h]; exact checkSteps_lt hs

omit [DecidableEq D] in
/-- **The step check bites (the tooth of `checkSteps_lt`).** At the ceiling it refuses
`overBound .counter`, by that name. -/
theorem checkSteps_refuses {w : World D} (h : 2 ^ 64 ≤ w.steps + 1) :
    checkSteps w = .error (.overBound .counter) := by
  have hc : Bounds.counterLimit = 2 ^ 64 := by decide
  have hn : ¬ (w.steps + 1 < Bounds.counterLimit) := by rw [hc]; omega
  unfold checkSteps req
  simp [hn]

/-- No Turn is admitted from a World at the step ceiling. -/
theorem admit_refused_at_step_ceiling {E : Env D} {w w' : World D} {t : Turn D}
    (h : 2 ^ 64 ≤ w.steps + 1) : World.admit E w t ≠ .ok w' := by
  intro ha
  have := admit_steps_lt ha
  rw [admit_steps ha] at this; omega

/-- No refusal is recorded from a World at the step ceiling. -/
theorem refuse_refused_at_step_ceiling {E : Env D} {w w' : World D} {r : Refused D}
    (h : 2 ^ 64 ≤ w.steps + 1) : World.refuse E w r ≠ .ok w' := by
  intro hr
  have := refuse_steps_lt hr
  rw [refuse_steps hr] at this; omega

/-! ## The one step -/

/-- A step's numbers are within `Bounds`: what makes its chain link injective. -/
def Step.Bounded : Step D → Prop
  | .turn t => checkBounds t = .ok ()
  | .refusal r => checkRefusedBounds r = .ok ()

theorem refuse_bounded {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    checkRefusedBounds r = .ok () := by
  obtain ⟨hc, _⟩ := refuse_ok h
  unfold checkRefusal at hc
  simp only [except_bind_ok] at hc
  obtain ⟨⟨⟩, hb, _⟩ := hc
  exact hb

theorem step_bounded {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    s.Bounded := by
  cases s with
  | turn t => obtain ⟨_, hc, _⟩ := admit_ok h; exact hc.bounds
  | refusal r => exact refuse_bounded h

theorem step_height {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    w'.height = w.height + s.dheight := by
  cases s with
  | turn t => exact admit_height h
  | refusal r => simp [Step.dheight, (refuse_frame h).2.2.1]

theorem step_steps {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    w'.steps = w.steps + 1 := by
  cases s with
  | turn t => exact admit_steps h
  | refusal r => exact refuse_steps h

/-- **Every step leaves the counter below `2^64`** (CODEC's `CodecFits.stepsLt`, HOST's re-seal). -/
theorem step_steps_lt {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    w'.steps < 2 ^ 64 := by
  cases s with
  | turn t => exact admit_steps_lt h
  | refusal r => exact refuse_steps_lt h

theorem step_chain {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    w'.chain = stepLink E w.chain s (w'.roots E) := by
  cases s with
  | turn t => exact admit_chain h
  | refusal r => exact refuse_chain h

theorem step_origin {E : Env D} {w w' : World D} {s : Step D} (h : World.step E w s = .ok w') :
    w'.origin = w.origin := by
  cases s with
  | turn t => obtain ⟨_, _, rfl⟩ := admit_ok h; rfl
  | refusal r => exact (refuse_frame h).2.2.2.2

/-- A property of Worlds kept by every admission and every recorded refusal is kept by the fold
(`World.fold` unfolded: the same one-step induction every fold theorem was). -/
theorem fold_keeps {E : Env D} {P : World D → Prop}
    (ha : ∀ {w w' : World D} {t : Turn D}, P w → World.admit E w t = .ok w' → P w')
    (hr : ∀ {w w' : World D} {r : Refused D}, P w → World.refuse E w r = .ok w' → P w') :
    ∀ {w w' : World D} {l : List (Step D)}, P w → World.fold E w l = .ok w' → P w'
  | w, w', [], hp, h => by
      unfold World.fold at h; simp only [Except.ok.injEq] at h; subst h; exact hp
  | w, w', s :: rest, hp, h => by
      unfold World.fold at h
      cases hs : World.step E w s with
      | error e => simp [hs] at h
      | ok w₁ =>
          rw [hs] at h
          cases hf : World.fold E w₁ rest with
          | error e => obtain ⟨i, r⟩ := e; simp [hf] at h
          | ok v =>
              simp only [hf, Except.ok.injEq] at h
              subst h
              have hp₁ : P w₁ := by
                cases s with
                | turn t => exact ha hp hs
                | refusal r => exact hr hp hs
              exact fold_keeps ha hr hp₁ hf

/-- A property that reads only the cells' trie is kept by every recorded refusal. -/
theorem refuse_keeps_trie {E : Env D} {P : World D → Prop} (hP : ∀ {w w' : World D}, w'.trie = w.trie → P w → P w')
    {w w' : World D} {r : Refused D} (hp : P w) (h : World.refuse E w r = .ok w') : P w' :=
  hP (refuse_trie h) hp

/-- Every World a fold reaches from one whose counter fits has a counter that fits. -/
theorem fold_steps_lt {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.steps < 2 ^ 64)
    (h : World.fold E w l = .ok w') : w'.steps < 2 ^ 64 :=
  fold_keeps (P := fun v => v.steps < 2 ^ 64) (fun _ ha => admit_steps_lt ha) (fun _ hr => refuse_steps_lt hr) hw h

/-! ## The refusals trie stays canonical -/

/-- The World's refusals trie is canonical (`Trie.Canon` at the root): what every refusals read
rests on, as `JournalCanon` for the journal. A premise of refusal readers only. -/
def World.RefusalsCanon (E : Env D) (w : World D) : Prop := Trie.Canon (refusalSpec E) 0 w.refusals

omit [Ord D] [DecidableEq D] in
theorem pruneRefusals_canon {E : Env D} {H : Nat} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r) :
    Trie.Canon (refusalSpec E) 0 (pruneRefusals E H r) := by
  unfold pruneRefusals
  split
  · exact Trie.canon_retainAt (refusalSpec E) _ [] 0 r hr (fun _ _ _ _ _ _ h => by simp at h)
  · exact hr

omit [Ord D] in
/-- A lookup in the pruned refusals: at a multiple of `windowMax`, the leaf if it is kept. -/
theorem pruneRefusals_get {E : Env D} {H : Nat} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r)
    (k : WindowSlot D) :
    (pruneRefusals E H r).get (refusalSpec E) k =
      if H % Bounds.windowMax = 0 then (r.get (refusalSpec E) k).filter (keptRefusal H k)
      else r.get (refusalSpec E) k := by
  unfold pruneRefusals
  split
  · exact Trie.get_retainAt (refusalSpec E) _ [] hr (fun _ _ _ _ _ _ h => by simp at h) k
  · rfl

/-! ### The ring of recent chain heads (KERNEL-79): the window trie's third kind -/

/-- The ring's write touches no refusal-window key: the kinds are disjoint by constructor. -/
theorem ringPush_get_refusal {E : Env D} {w : World D} {r : Refusals D} (k : RefusalSlot D) :
    (ringPush E w r).get (refusalSpec E) (.refusal k) = r.get (refusalSpec E) (.refusal k) :=
  Trie.get_insert_ne _ _ _ (by intro h; cases h)

/-- The ring's write touches no meter key. -/
theorem ringPush_get_meter {E : Env D} {w : World D} {r : Refusals D} (k : MeterSlot D) :
    (ringPush E w r).get (refusalSpec E) (.meter k) = r.get (refusalSpec E) (.meter k) :=
  Trie.get_insert_ne _ _ _ (by intro h; cases h)

/-- The ring's write: the World's step and chain at its step's ring position, nothing else. -/
theorem ringPush_get_chain {E : Env D} {w : World D} {r : Refusals D} (k : ChainSlot D) :
    (ringPush E w r).get (refusalSpec E) (.chain k) =
      if k = .ring w.origin (ringSlot w.steps) then some (.head w.steps w.chain)
      else r.get (refusalSpec E) (.chain k) := by
  unfold ringPush; rw [Trie.get_insert]
  by_cases h : k = .ring w.origin (ringSlot w.steps)
  · subst h; simp
  · rw [if_neg (fun he => h (WindowSlot.chain.inj he)), if_neg h]

theorem ringPush_canon {E : Env D} {w : World D} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r) :
    Trie.Canon (refusalSpec E) 0 (ringPush E w r) := Trie.canon_insert _ _ _ hr

/-- A Turn's commit prunes the refusals at the new height, over the meter leaf it bumped
(`commitMeter`: unchanged for a Turn with no ticks, KERNEL-68), then writes the ring (KERNEL-79). -/
theorem commit_refusals {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} :
    (commit E w t posts).refusals = ringPush E w (pruneRefusals E (w.height + 1) (commitMeter E w t)) := rfl

/-- A Turn with no ticks leaves the refusals as before, but for the prune and the ring. -/
theorem commit_refusals_of_ticks_zero {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (h : t.ticks = 0) : (commit E w t posts).refusals = ringPush E w (pruneRefusals E (w.height + 1) w.refusals) := by
  rw [commit_refusals]; unfold commitMeter; simp [h]

theorem commitRefusal_refusals {E : Env D} {w : World D} {r : Refused D} :
    (commitRefusal E w r).refusals = ringPush E w
      (((w.refusals.insert (refusalSpec E) (.refusal (.tx r.txId)) (.refused (w.height + 1) r.code r.member)).insert
        (refusalSpec E) (.refusal (.count r.member (refusalWindow w.height))) (.count (refusalCount E w r.member + 1))).insert
        (refusalSpec E) (.refusal (.total w.origin (refusalWindow w.height))) (.count (refusalTotal E w + 1))) := by
  show ringPush E w (commitRefusals E w r) = _
  unfold commitRefusals
  rw [Trie.insertAll_eq_foldl]; rfl

/-- The meter's write keeps the refusals canonical (one insert, or nothing: KERNEL-68). -/
theorem commitMeter_canon {E : Env D} {w : World D} {t : Turn D} (hc : w.RefusalsCanon E) :
    Trie.Canon (refusalSpec E) 0 (commitMeter E w t) := by
  unfold commitMeter
  split
  · exact hc
  · exact Trie.canon_insert _ _ _ hc

/-- The meter's write touches no refusal-window key (KERNEL-68): the two kinds of the window trie
are disjoint by constructor, so no hypothesis. -/
theorem commitMeter_get_refusal {E : Env D} {w : World D} {t : Turn D} (k : RefusalSlot D) :
    (commitMeter E w t).get (refusalSpec E) (.refusal k) = w.refusals.get (refusalSpec E) (.refusal k) := by
  unfold commitMeter
  split
  · rfl
  · exact Trie.get_insert_ne _ _ _ (by intro h; cases h)

/-- The meter's write touches no other meter key (KERNEL-68). -/
theorem commitMeter_get_meter_ne {E : Env D} {w : World D} {t : Turn D} {k : MeterSlot D}
    (hk : k ≠ .ticks t.member (refusalWindow (w.height + 1))) :
    (commitMeter E w t).get (refusalSpec E) (.meter k) = w.refusals.get (refusalSpec E) (.meter k) := by
  unfold commitMeter
  split
  · rfl
  · exact Trie.get_insert_ne _ _ _ (fun h => hk (WindowSlot.meter.inj h))

/-- **The turn's own meter leaf after a Turn** (KERNEL-68): untouched for a Turn with no ticks, else the
member's ticks this window bumped by the Turn's. The prune never drops it: it is keyed by the window
the Turn lands in, which is the window the prune keeps. -/
theorem commit_meterAt_self {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hc : w.RefusalsCanon E) :
    (commit E w t posts).meterAt E (.ticks t.member (refusalWindow (w.height + 1))) =
      if t.ticks = 0 then w.meterAt E (.ticks t.member (refusalWindow (w.height + 1)))
      else some (ticksUsed E w t.member + t.ticks) := by
  unfold World.meterAt
  rw [commit_refusals, ringPush_get_meter, pruneRefusals_get (commitMeter_canon hc)]
  unfold commitMeter
  by_cases ht : t.ticks = 0
  · simp only [ht, ↓reduceIte]
    by_cases hz : (w.height + 1) % Bounds.windowMax = 0
    · simp only [hz, ↓reduceIte]
      cases hg : w.refusals.get (refusalSpec E) (.meter (.ticks t.member (refusalWindow (w.height + 1)))) with
      | none => rfl
      | some v => cases v <;> simp [Option.filter, keptRefusal]
    · simp only [hz, ↓reduceIte]
  · simp only [ht, ↓reduceIte, Trie.get_insert_self]
    by_cases hz : (w.height + 1) % Bounds.windowMax = 0
    · simp [hz, Option.filter, keptRefusal]
    · simp [hz]

/-- **Every other meter leaf after a Turn** (KERNEL-68): as before, up to the prune — at a multiple of
`windowMax` a leaf of any other window is gone. The meter's twin of `admit_refusalAt`, over its own
kind. -/
theorem commit_meterAt_ne {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)}
    (hc : w.RefusalsCanon E) (m : D) (win : UInt64)
    (hk : MeterSlot.ticks m win ≠ .ticks t.member (refusalWindow (w.height + 1))) :
    (commit E w t posts).meterAt E (.ticks m win) =
      if (w.height + 1) % Bounds.windowMax = 0 ∧ win ≠ refusalWindow (w.height + 1) then none
      else w.meterAt E (.ticks m win) := by
  unfold World.meterAt
  rw [commit_refusals, ringPush_get_meter, pruneRefusals_get (commitMeter_canon hc), commitMeter_get_meter_ne hk]
  by_cases hz : (w.height + 1) % Bounds.windowMax = 0
  · simp only [hz, true_and, ↓reduceIte]
    by_cases hw : win = refusalWindow (w.height + 1)
    · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte]
      cases hg : w.refusals.get (refusalSpec E) (.meter (.ticks m (refusalWindow (w.height + 1)))) with
      | none => rfl
      | some v => cases v <;> simp [Option.filter, keptRefusal]
    · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte]
      cases hg : w.refusals.get (refusalSpec E) (.meter (.ticks m win)) with
      | none => rfl
      | some v => cases v <;> simp [Option.filter, keptRefusal, hw]
  · simp only [hz, false_and, ↓reduceIte]

theorem admit_refusalsCanon {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (h : World.admit E w t = .ok w') : w'.RefusalsCanon E := by
  obtain ⟨_, _, rfl⟩ := admit_ok h
  unfold World.RefusalsCanon
  rw [commit_refusals]
  exact ringPush_canon (pruneRefusals_canon (commitMeter_canon hc))

theorem refuse_refusalsCanon {E : Env D} {w w' : World D} {r : Refused D} (hc : w.RefusalsCanon E)
    (h : World.refuse E w r = .ok w') : w'.RefusalsCanon E := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  unfold World.RefusalsCanon
  rw [commitRefusal_refusals]
  exact ringPush_canon (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ hc)))

theorem step_refusalsCanon {E : Env D} {w w' : World D} {s : Step D} (hc : w.RefusalsCanon E)
    (h : World.step E w s = .ok w') : w'.RefusalsCanon E := by
  cases s with
  | turn t => exact admit_refusalsCanon hc h
  | refusal r => exact refuse_refusalsCanon hc h

omit [DecidableEq D] in
theorem genesis_refusalsCanon (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).RefusalsCanon E :=
  Trie.canon_empty _ 0

/-! ## Finality: a recorded refusal is never admitted -/

/-- **A transaction id that holds a recorded refusal is refused `refusedFinal`, never admitted**
(KERNEL-44, KERNEL-47 amendment 6): whatever its pins now see (a pin that returned A→B→A included). -/
theorem admit_refusedFinal {E : Env D} {w : World D} {t : Turn D} {h code : Nat} {mb : D}
    (hr : w.refusalAt E (.tx t.txId) = some (.refused h code mb)) :
    ∀ w', World.admit E w t ≠ .ok w' := by
  intro w' ha
  obtain ⟨_, hc, _⟩ := admit_ok ha
  have hj := hc.journal
  unfold checkJournal at hj
  cases hjt : w.journalAt E t.txId with
  | some e => simp [hjt] at hj
  | none => simp [hjt, hr] at hj

/-- An admitted transaction id held no recorded refusal. -/
theorem admit_not_refused {E : Env D} {w w' : World D} {t : Turn D} (ha : World.admit E w t = .ok w') :
    ∀ h code mb, w.refusalAt E (.tx t.txId) ≠ some (.refused h code mb) :=
  fun _ _ _ hr => admit_refusedFinal hr w' ha

/-- A recorded refusal is recorded: after `refuse`, its transaction id holds `refused (H + 1) code`
(on any refusals trie: the two inserts are at different keys). -/
theorem refuse_recorded {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.refusalAt E (.tx r.txId) = some (.refused (w.height + 1) r.code r.member) := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  unfold World.refusalAt
  rw [commitRefusal_refusals, ringPush_get_refusal]
  simp [Trie.get_insert]

/-- The meter's write touches no ring key. -/
theorem commitMeter_get_chain {E : Env D} {w : World D} {t : Turn D} (k : ChainSlot D) :
    (commitMeter E w t).get (refusalSpec E) (.chain k) = w.refusals.get (refusalSpec E) (.chain k) := by
  unfold commitMeter
  split
  · rfl
  · exact Trie.get_insert_ne _ _ _ (by intro h; cases h)

/-- **A step writes the ring at its own position and nothing else of it** (KERNEL-79): the leaf
`(w.steps, w.chain)` at `ringSlot w.steps`; every other ring leaf is as before (the prune keeps every
ring leaf; the meter and the refusal records are other kinds). -/
theorem step_ring {E : Env D} {w w' : World D} {st : Step D} (hc : w.RefusalsCanon E)
    (h : World.step E w st = .ok w') (k : ChainSlot D) :
    w'.refusals.get (refusalSpec E) (.chain k) =
      if k = .ring w.origin (ringSlot w.steps) then some (.head w.steps w.chain)
      else w.refusals.get (refusalSpec E) (.chain k) := by
  cases st with
  | turn t =>
    obtain ⟨posts, _, rfl⟩ := admit_ok h
    rw [commit_refusals, ringPush_get_chain]
    split
    · rfl
    · rw [pruneRefusals_get (commitMeter_canon hc), commitMeter_get_chain]
      split
      · cases w.refusals.get (refusalSpec E) (.chain k) <;> simp [Option.filter, keptRefusal]
      · rfl
  | refusal r =>
    obtain ⟨_, rfl⟩ := refuse_ok h
    rw [commitRefusal_refusals, ringPush_get_chain]
    split
    · rfl
    · rw [Trie.get_insert_ne _ _ _ (by intro he; cases he), Trie.get_insert_ne _ _ _ (by intro he; cases he),
        Trie.get_insert_ne _ _ _ (by intro he; cases he)]

/-- **A pin passes exactly when it is not ahead and the World's chain at its step is the pin's**
(KERNEL-79, `checkCausal`). -/
theorem checkCausal_some_ok {E : Env D} {w : World D} {p : CausalPin D} :
    checkCausal E w (some p) = .ok () ↔ p.steps ≤ w.steps ∧ w.chainAt E p.steps = some p.chain := by
  constructor
  · intro h
    simp only [checkCausal] at h
    split at h
    · cases h
    · rename_i hlt
      refine ⟨Nat.le_of_not_lt hlt, ?_⟩
      split at h
      · rename_i c hc
        unfold req at h
        split at h
        · rename_i he
          rw [hc]
          simpa using he
        · cases h
      · cases h
  · rintro ⟨hle, hc⟩
    simp only [checkCausal]
    rw [if_neg (Nat.not_lt.mpr hle), hc]
    simp [req]

/-- A Turn's causal pin survives one more step on `w`: it names `w`'s own head, or a ring position the
step does not overwrite (KERNEL-79). A pin `Bounds.pinWindow` steps behind the head is the one the next
step's ring leaf replaces. -/
def PinSurvives (w : World D) (t : Turn D) : Prop :=
  ∀ p, t.causal = some p → p.steps = w.steps ∨ ringSlot p.steps ≠ ringSlot w.steps

/-- **The ring across an admission** (KERNEL-79): at every step the World has passed, the admitted World
answers the chain the World answered, but at the one ring position the step overwrites. -/
theorem chainAt_admit {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (h : World.admit E w t = .ok w') {s : Nat} (hs : s ≤ w.steps)
    (hr : s = w.steps ∨ ringSlot s ≠ ringSlot w.steps) : w'.chainAt E s = w.chainAt E s := by
  have hst := admit_steps h
  have ho : w'.origin = w.origin := step_origin (s := .turn t) h
  unfold World.chainAt
  rw [if_neg (show ¬ s = w'.steps by omega), ho, step_ring (st := .turn t) hc h]
  rcases hr with rfl | hne
  · simp
  · rw [if_neg (fun he => hne (ChainSlot.ring.inj he).2), if_neg (fun he => hne (by rw [he]))]

end Nanodregg.Kernel
