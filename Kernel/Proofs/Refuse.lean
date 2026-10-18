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
  obtain ⟨_, rfl⟩ := refuse_ok h; rfl

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
  · exact Trie.canon_retainAt (refusalSpec E) _ [] 0 r hr (fun _ _ _ => trivial)
  · exact hr

omit [Ord D] in
/-- A lookup in the pruned refusals: at a multiple of `windowMax`, the leaf if it is kept. -/
theorem pruneRefusals_get {E : Env D} {H : Nat} {r : Refusals D} (hr : Trie.Canon (refusalSpec E) 0 r)
    (k : RefusalSlot D) :
    (pruneRefusals E H r).get (refusalSpec E) k =
      if H % Bounds.windowMax = 0 then (r.get (refusalSpec E) k).filter (keptRefusal H k)
      else r.get (refusalSpec E) k := by
  unfold pruneRefusals
  split
  · exact Trie.get_retainAt (refusalSpec E) _ [] hr (fun _ _ _ => trivial) k
  · rfl

theorem commit_refusals {E : Env D} {w : World D} {t : Turn D} {posts : List (Post D)} :
    (commit E w t posts).refusals = pruneRefusals E (w.height + 1) w.refusals := rfl

theorem commitRefusal_refusals {E : Env D} {w : World D} {r : Refused D} :
    (commitRefusal E w r).refusals =
      (w.refusals.insert (refusalSpec E) (.tx r.txId) (.refused (w.height + 1) r.code)).insert (refusalSpec E)
        (.count r.member (refusalWindow w.height)) (.count (refusalCount E w r.member + 1)) := rfl

theorem admit_refusalsCanon {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (h : World.admit E w t = .ok w') : w'.RefusalsCanon E := by
  obtain ⟨_, _, rfl⟩ := admit_ok h
  unfold World.RefusalsCanon
  rw [commit_refusals]
  exact pruneRefusals_canon hc

theorem refuse_refusalsCanon {E : Env D} {w w' : World D} {r : Refused D} (hc : w.RefusalsCanon E)
    (h : World.refuse E w r = .ok w') : w'.RefusalsCanon E := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  unfold World.RefusalsCanon
  rw [commitRefusal_refusals]
  exact Trie.canon_insert _ _ _ (Trie.canon_insert _ _ _ hc)

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
theorem admit_refusedFinal {E : Env D} {w : World D} {t : Turn D} {h code : Nat}
    (hr : w.refusalAt E (.tx t.txId) = some (.refused h code)) :
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
    ∀ h code, w.refusalAt E (.tx t.txId) ≠ some (.refused h code) :=
  fun _ _ hr => admit_refusedFinal hr w' ha

/-- A recorded refusal is recorded: after `refuse`, its transaction id holds `refused (H + 1) code`
(on any refusals trie: the two inserts are at different keys). -/
theorem refuse_recorded {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    w'.refusalAt E (.tx r.txId) = some (.refused (w.height + 1) r.code) := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  unfold World.refusalAt
  rw [commitRefusal_refusals]
  simp [Trie.get_insert]

end Nanodregg.Kernel
