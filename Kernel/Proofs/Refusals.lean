/-
# Kernel.Proofs.Refusals — recorded refusals are bounded, final within their window, and read back

KERNEL-44 / KERNEL-47. The refusals trie is the third instance of the one trie type. What a reached
World's refusals hold (`World.RefusalsOk`, CODEC's `kernel/refusals` refusal: `refusalsOk_of_fits`,
`refusalsFits_of_ok`) is kept by every admission and every recorded refusal (`fold_refusalsOk`), so
a member never holds more than `Bounds.refusalsPerWindow` in a window (`refusalCount_le`). A
recorded refusal is never admitted afterwards (`admit_refusedFinal`), and is answered by name
(`submit_refused_final`) at every height the call could still be admitted, and every height below
`journalForgets` (`refused_answers`): the A→B→A defect KERNEL-44 names is closed. The keys separate
with no premise but a lawful `Env` (`refusals_separate`); a key without its kind byte does not
(`plant_refusals_unseparated`).
-/
import Kernel.Proofs.Journal
import Kernel.Proofs.Cells
import Kernel.Proofs.Audit

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## What `World.refuse` checked -/

/-- Every check of a recorded refusal, as facts. -/
theorem checkRefusal_facts {E : Env D} {w : World D} {r : Refused D} (h : checkRefusal E w r = .ok ()) :
    checkRefusedBounds r = .ok () ∧ r.notBefore ≤ w.height + 1 ∧ w.height + 1 ≤ r.validUntil ∧
      w.journalAt E r.txId = none ∧ (∀ hh code, w.refusalAt E (.tx r.txId) ≠ some (.refused hh code)) ∧
      refusalCount E w r.member < Bounds.refusalsPerWindow := by
  unfold checkRefusal at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hb, ⟨⟩, -, ⟨⟩, hw, h⟩ := h
  have hw' := req_ok.mp hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
  refine ⟨hb, hw'.1, hw'.2, ?_⟩
  cases hj : w.journalAt E r.txId with
  | some e => rw [hj] at h; obtain ⟨_, _⟩ := e; simp at h
  | none =>
      rw [hj] at h
      cases hr : w.refusalAt E (.tx r.txId) with
      | none =>
          rw [hr] at h
          refine ⟨rfl, fun hh code he => ?_, by simpa using req_ok.mp h⟩
          simp at he
      | some l =>
          rw [hr] at h
          cases l with
          | refused hh code => simp at h
          | count n =>
              refine ⟨rfl, fun hh code he => ?_, by simpa using req_ok.mp h⟩
              simp at he

theorem refuse_facts {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w') :
    checkRefusedBounds r = .ok () ∧ r.notBefore ≤ w.height + 1 ∧ w.height + 1 ≤ r.validUntil ∧
      w.journalAt E r.txId = none ∧ (∀ hh code, w.refusalAt E (.tx r.txId) ≠ some (.refused hh code)) ∧
      refusalCount E w r.member < Bounds.refusalsPerWindow :=
  checkRefusal_facts (refuse_ok h).1

omit [Ord D] [DecidableEq D] in
/-- A recorded refusal's counters are below `2^64`. -/
theorem refusedBounds_lt {r : Refused D} (h : checkRefusedBounds r = .ok ()) :
    r.notBefore < 2 ^ 64 ∧ r.validUntil < 2 ^ 64 ∧ r.code < 2 ^ 64 := by
  unfold checkRefusedBounds at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, hc⟩ := h
  have := req_ok.mp hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, counterLimit_eq] at this
  omega

/-- The refusals after a refusal, read at any key: the call's leaf, the member's bumped count, else
what was there. -/
theorem refuse_refusalAt {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w')
    (k : RefusalSlot D) :
    w'.refusalAt E k =
      if k = .count r.member (refusalWindow w.height) then some (.count (refusalCount E w r.member + 1))
      else if k = .tx r.txId then some (.refused (w.height + 1) r.code)
      else w.refusalAt E k := by
  obtain ⟨_, rfl⟩ := refuse_ok h
  unfold World.refusalAt
  rw [commitRefusal_refusals, Trie.get_insert, Trie.get_insert]

/-- The refusals after an admission, read at any key: at a multiple of `windowMax`, the leaf if it is
kept; otherwise the leaf (on a canonical trie). -/
theorem admit_refusalAt {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (h : World.admit E w t = .ok w') (k : RefusalSlot D) :
    w'.refusalAt E k =
      if (w.height + 1) % Bounds.windowMax = 0 then (w.refusalAt E k).filter (keptRefusal (w.height + 1) k)
      else w.refusalAt E k := by
  obtain ⟨_, _, rfl⟩ := admit_ok h
  unfold World.refusalAt
  rw [commit_refusals, pruneRefusals_get hc]

/-! ## The invariant -/

/-- The refusals trie is canonical, and every leaf it holds fits the World's height
(`refusalFits`). -/
def World.RefusalsOk (E : Env D) (w : World D) : Prop :=
  w.RefusalsCanon E ∧ ∀ k l, w.refusalAt E k = some l → refusalFits w.height k l = true

theorem refusalsOk_of_empty {E : Env D} {w : World D} (h : w.refusals = .empty) : w.RefusalsOk E := by
  refine ⟨by unfold World.RefusalsCanon; rw [h]; exact Trie.canon_empty _ 0, fun k l hk => ?_⟩
  unfold World.refusalAt at hk; rw [h] at hk; cases hk

theorem genesis_refusalsOk (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).RefusalsOk E :=
  refusalsOk_of_empty rfl

/-- **A canonical listing that `refusalsFits` is a `RefusalsOk` trie**: what CODEC's `kernel/refusals`
refusal gives every decoded base (whose refusals trie the decoder builds, so it is canonical). -/
theorem refusalsOk_of_fits {E : Env D} {w : World D} (hc : Trie.Canon (refusalSpec E) 0 w.refusals)
    (h : refusalsFits w.height w.refusals.toList = true) : w.RefusalsOk E := by
  unfold refusalsFits at h
  rw [List.all_eq_true] at h
  refine ⟨hc, fun k l hk => h (k, l) ?_⟩
  exact (Trie.mem_toList (refusalSpec E) 0 w.refusals hc.1 k l).mpr hk

/-- **Every `RefusalsOk` trie fits**, so the refusal never refuses a base a fold wrote. -/
theorem refusalsFits_of_ok {E : Env D} {w : World D} (hw : w.RefusalsOk E) :
    refusalsFits w.height w.refusals.toList = true := by
  unfold refusalsFits
  rw [List.all_eq_true]
  intro p hp
  exact hw.2 p.1 p.2 ((Trie.mem_toList (refusalSpec E) 0 w.refusals hw.1.1 p.1 p.2).mp hp)

theorem windowMax_pos : 0 < Bounds.windowMax := by decide

omit [Ord D] [DecidableEq D] in
/-- One height on, a leaf that fits still fits, unless this height prunes it. -/
theorem refusalFits_succ {H : Nat} {k : RefusalSlot D} {l : RefusalLeaf} (hf : refusalFits H k l = true)
    (hk : (H + 1) % Bounds.windowMax = 0 → keptRefusal (H + 1) k l = true) :
    refusalFits (H + 1) k l = true := by
  cases k <;> cases l <;> simp only [refusalFits, decide_eq_true_eq, Bool.false_eq_true] at hf ⊢
  · rename_i id hh code
    refine ⟨hf.1, by omega, ?_, hf.2.2.2.1, hf.2.2.2.2⟩
    by_cases hz : (H + 1) % Bounds.windowMax = 0
    · have := hk hz
      simp only [keptRefusal, decide_eq_true_eq] at this
      omega
    · have : (H + 1) % Bounds.windowMax = H % Bounds.windowMax + 1 := by
        rw [windowMax_eq] at hz ⊢; omega
      omega
  · rename_i m win n
    refine ⟨?_, hf.2.1, hf.2.2⟩
    by_cases hz : (H + 1) % Bounds.windowMax = 0
    · have := hk hz
      simpa [keptRefusal] using this
    · rw [hf.1]
      unfold refusalWindow
      congr 1
      rw [windowMax_eq] at hz ⊢; omega

/-- **The invariant holds after every admission.** -/
theorem admit_refusalsOk {E : Env D} {w w' : World D} {t : Turn D} (hw : w.RefusalsOk E)
    (h : World.admit E w t = .ok w') : w'.RefusalsOk E := by
  refine ⟨admit_refusalsCanon hw.1 h, fun k l hk => ?_⟩
  rw [admit_height h]
  rw [admit_refusalAt hw.1 h k] at hk
  split at hk
  · rw [Option.filter_eq_some_iff] at hk
    exact refusalFits_succ (hw.2 k l hk.1) (fun _ => hk.2)
  · rename_i hz
    exact refusalFits_succ (hw.2 k l hk) (fun h' => absurd h' hz)

/-- **The invariant holds after every recorded refusal**: the new leaf fits (refused at the next
height, below `2^64` because its window is), the member's count stays within the budget. -/
theorem refuse_refusalsOk {E : Env D} {w w' : World D} {r : Refused D} (hw : w.RefusalsOk E)
    (h : World.refuse E w r = .ok w') : w'.RefusalsOk E := by
  obtain ⟨hb, -, hvu, -, -, hcnt⟩ := refuse_facts h
  obtain ⟨-, -, hlt⟩ := refusedBounds_lt hb
  have hvlt := (refusedBounds_lt hb).2.1
  refine ⟨refuse_refusalsCanon hw.1 h, fun k l hk => ?_⟩
  rw [(refuse_frame h).2.2.1]
  rw [refuse_refusalAt h k] at hk
  split at hk
  · rename_i he
    cases hk; subst he
    simp only [refusalFits, decide_eq_true_eq]
    unfold Bounds.refusalsPerWindow at hcnt ⊢
    refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial | omega
  · split at hk
    · rename_i _ he
      cases hk; subst he
      simp only [refusalFits, decide_eq_true_eq, counterLimit_eq]
      have := windowMax_pos
      omega
    · exact hw.2 k l hk

theorem step_refusalsOk {E : Env D} {w w' : World D} {s : Step D} (hw : w.RefusalsOk E)
    (h : World.step E w s = .ok w') : w'.RefusalsOk E := by
  cases s with
  | turn t => exact admit_refusalsOk hw h
  | refusal r => exact refuse_refusalsOk hw h

theorem fold_refusalsOk {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.RefusalsOk E)
    (h : World.fold E w l = .ok w') : w'.RefusalsOk E :=
  fold_keeps (P := fun v => v.RefusalsOk E) admit_refusalsOk refuse_refusalsOk hw h

/-- A member's window COUNT is at most `Bounds.refusalsPerWindow` on every `RefusalsOk` World. This
bounds the counter; that the counter counts the records is `fold_member_refusals`, and the bound over
the log is `fold_member_refusals_le`. -/
theorem refusalCount_le {E : Env D} {w : World D} (hw : w.RefusalsOk E) (m : D) :
    refusalCount E w m ≤ Bounds.refusalsPerWindow := by
  unfold refusalCount
  split
  · rename_i n hg
    have := hw.2 _ _ hg
    simp only [refusalFits, decide_eq_true_eq] at this
    exact this.2.2
  · exact Nat.zero_le _

/-! ## The counter counts the records (the DoS bound is about the log, not a number) -/

/-- A recorded refusal bumps its member's count for the window by one and no other member's. -/
theorem refuse_refusalCount {E : Env D} {w w' : World D} {r : Refused D} (h : World.refuse E w r = .ok w')
    (m : D) : refusalCount E w' m = refusalCount E w m + (if m = r.member then 1 else 0) := by
  have hh := (refuse_frame h).2.2.1
  unfold refusalCount
  rw [hh, refuse_refusalAt h]
  by_cases hm : m = r.member
  · subst hm; simp [refusalCount]
  · rw [if_neg (by simp [hm]), if_neg (by simp)]
    simp [hm]

/-- An admission inside one window (no prune at the new height) moves no count. -/
theorem admit_refusalCount {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (h : World.admit E w t = .ok w') (hz : (w.height + 1) % Bounds.windowMax ≠ 0) (m : D) :
    refusalCount E w' m = refusalCount E w m := by
  have hw : refusalWindow w'.height = refusalWindow w.height := by
    rw [admit_height h]; unfold refusalWindow; congr 1
    rw [windowMax_eq] at hz ⊢; omega
  unfold refusalCount
  rw [hw, admit_refusalAt hc h, if_neg hz]

/-- **A member's recorded refusals in one window are its count's growth**: over a log that stays in
one window (`w` and `w'` at heights with one quotient by `windowMax`), the member's count grows by
exactly the log's recorded refusals of that member. The count is not a number the kernel trusts: it
counts the records (the vacuity read's F1). -/
theorem fold_member_refusals {E : Env D} {m : D} :
    ∀ {w w' : World D} {l : List (Step D)}, w.RefusalsCanon E → World.fold E w l = .ok w' →
      w'.height / Bounds.windowMax = w.height / Bounds.windowMax →
      refusalCount E w' m = refusalCount E w m + ((Step.refusals l).filter fun r => decide (r.member = m)).length
  | w, w', [], _, h, _ => by simp [World.fold] at h; subst h; simp [Step.refusals]
  | w, w', .turn t :: rest, hc, h, hwin => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hh₁ := admit_height h₁
      have hh₂ := fold_height h₂
      have hz : (w.height + 1) % Bounds.windowMax ≠ 0 := by
        rw [windowMax_eq] at hwin ⊢; omega
      have hwin₁ : w'.height / Bounds.windowMax = w₁.height / Bounds.windowMax := by
        rw [windowMax_eq] at hwin ⊢; omega
      rw [fold_member_refusals (admit_refusalsCanon hc h₁) h₂ hwin₁, admit_refusalCount hc h₁ hz m]
      simp [Step.refusals]
  | w, w', .refusal r :: rest, hc, h, hwin => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hh₁ := (refuse_frame h₁).2.2.1
      rw [fold_member_refusals (refuse_refusalsCanon hc h₁) h₂ (by rw [hh₁]; exact hwin),
        refuse_refusalCount h₁ m]
      by_cases hm : r.member = m
      · subst hm; simp [Step.refusals]; omega
      · simp [Step.refusals, hm, Ne.symm hm]

/-- **The DoS bound, over the log** (KERNEL-44): within one window, a log records at most
`Bounds.refusalsPerWindow` refusals of any one member, from any `RefusalsOk` World. -/
theorem fold_member_refusals_le {E : Env D} {w w' : World D} {l : List (Step D)} (hw : w.RefusalsOk E)
    (h : World.fold E w l = .ok w') (hwin : w'.height / Bounds.windowMax = w.height / Bounds.windowMax)
    (m : D) : ((Step.refusals l).filter fun r => decide (r.member = m)).length ≤ Bounds.refusalsPerWindow := by
  have := fold_member_refusals (m := m) hw.1 h hwin
  have := refusalCount_le (fold_refusalsOk hw h) m
  omega

/-! ## No transaction id is both refused and journaled -/

/-- Every recorded refusal's transaction id is unjournaled. -/
def World.RefusalsDisjoint (E : Env D) (w : World D) : Prop :=
  ∀ id hh code, w.refusalAt E (.tx id) = some (.refused hh code) → w.journalAt E id = none

theorem refusalsDisjoint_iff {E : Env D} {w : World D} (hc : w.RefusalsCanon E) :
    refusalsDisjoint E w = true ↔ w.RefusalsDisjoint E := by
  unfold refusalsDisjoint World.RefusalsDisjoint
  rw [List.all_eq_true]
  constructor
  · intro h id hh code hr
    have := h (.tx id, .refused hh code) ((Trie.mem_toList (refusalSpec E) 0 w.refusals hc.1 _ _).mpr hr)
    simpa using this
  · intro h p hp
    obtain ⟨k, l⟩ := p
    cases k with
    | count m win => cases l <;> rfl
    | tx id =>
        cases l with
        | refused hh code =>
            have hg := (Trie.mem_toList (refusalSpec E) 0 w.refusals hc.1 _ _).mp hp
            simp [h id hh code hg]
        | count n => rfl

theorem genesis_refusalsDisjoint (E : Env D) (o : D) (a : Nat) : (World.genesis E o a).RefusalsDisjoint E :=
  fun _ _ _ h => by simp [World.refusalAt, World.genesis, Trie.get_empty] at h

theorem admit_refusalsDisjoint {E : Env D} {w w' : World D} {t : Turn D} (hc : w.RefusalsCanon E)
    (hjc : w.JournalCanon E) (hd : w.RefusalsDisjoint E) (h : World.admit E w t = .ok w') :
    w'.RefusalsDisjoint E := by
  intro id hh code hr
  have hr₀ : w.refusalAt E (.tx id) = some (.refused hh code) := by
    rw [admit_refusalAt hc h] at hr
    split at hr
    · exact (Option.filter_eq_some_iff.mp hr).1
    · exact hr
  have hne : id ≠ t.txId := fun he => by subst he; exact admit_not_refused h hh code hr₀
  obtain ⟨_, _, rfl⟩ := admit_ok h
  rw [commit_journalAt hjc, if_neg hne, hd id hh code hr₀]
  split <;> rfl

theorem refuse_refusalsDisjoint {E : Env D} {w w' : World D} {r : Refused D} (hd : w.RefusalsDisjoint E)
    (h : World.refuse E w r = .ok w') : w'.RefusalsDisjoint E := by
  intro id hh code hr
  obtain ⟨-, -, -, hj, -, -⟩ := refuse_facts h
  rw [refuse_journalAt h]
  rw [refuse_refusalAt h, if_neg (by simp)] at hr
  split at hr
  · rename_i he; cases he; exact hj
  · exact hd id hh code hr

/-- **A fold never reaches a World holding one transaction id both refused and journaled.** -/
theorem fold_refusalsDisjoint {E : Env D} {w w' : World D} {l : List (Step D)} (hc : w.RefusalsCanon E)
    (hjc : w.JournalCanon E) (hd : w.RefusalsDisjoint E) (h : World.fold E w l = .ok w') :
    w'.RefusalsDisjoint E :=
  (fold_keeps (P := fun v => v.RefusalsCanon E ∧ v.JournalCanon E ∧ v.RefusalsDisjoint E)
    (fun hp ha => ⟨admit_refusalsCanon hp.1 ha, admit_journalCanon hp.2.1 ha,
      admit_refusalsDisjoint hp.1 hp.2.1 hp.2.2 ha⟩)
    (fun hp hr => ⟨refuse_refusalsCanon hp.1 hr,
      by show Trie.Canon _ 0 _; rw [(refuse_frame hr).2.1]; exact hp.2.1,
      refuse_refusalsDisjoint hp.2.2 hr⟩) ⟨hc, hjc, hd⟩ h).2.2

/-! ## The kind byte is what separates the keys -/

/-- PLANT (`refusals_separate`'s tooth): the key bytes without the kind byte. A refused id and the
count of the member whose id has the same bytes, for window 0, route identically. -/
private def plantRefusalKeyBytes (E : Env D) : RefusalSlot D → ByteArray
  | .tx id => E.bytes id ++ Nanodregg.Codec.Stream.nat64.bytes 0
  | .count m win => E.bytes m ++ Nanodregg.Codec.Stream.u64.bytes win

private def plantRefusalSpec (E : Env D) : Trie.Spec (RefusalSlot D) RefusalLeaf D :=
  { refusalSpec E with bit := fun k => byteBit (plantRefusalKeyBytes E k), kbytes := plantRefusalKeyBytes E }

omit [Ord D] [DecidableEq D] in
/-- **The plant does not separate**: with no kind byte, `tx d` and `count d 0` have the same bits at
every depth, for any digest `d` and any `Env`; so `refusals_separate` rests on the kind byte. -/
theorem plant_refusals_unseparated (E : Env D) (d : D) : ¬ Trie.Separates (plantRefusalSpec E) := by
  intro h
  obtain ⟨i, -, hi⟩ := h (.tx d) (.count d 0) (by simp)
  exact hi rfl

/-! ## Finality: a recorded refusal answers its transaction id while the call could be admitted -/

/-- A recorded refusal stays, and its transaction id stays unjournaled, across a fold that stays
below the refusal's prune height. -/
theorem fold_refused_retains {E : Env D} {k : D} {hh code : Nat} :
    ∀ {w w' : World D} {l : List (Step D)}, w.RefusalsCanon E → w.JournalCanon E →
      World.fold E w l = .ok w' → w.refusalAt E (.tx k) = some (.refused hh code) →
      w.journalAt E k = none → w'.height < hh + 2 * Bounds.windowMax →
      w'.refusalAt E (.tx k) = some (.refused hh code) ∧ w'.journalAt E k = none
  | w, w', [], _, _, h, hr, hj, _ => by simp [World.fold] at h; subst h; exact ⟨hr, hj⟩
  | w, w', .turn t :: rest, hc, hjc, h, hr, hj, hlt => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      have hne : t.txId ≠ k := fun he => by
        subst he; exact admit_not_refused h₁ hh code hr
      have hh₂ := fold_height h₂
      have hh₁ := admit_height h₁
      have hr₁ : w₁.refusalAt E (.tx k) = some (.refused hh code) := by
        rw [admit_refusalAt hc h₁, hr]
        split
        · simp only [Option.filter, keptRefusal, decide_eq_true_eq]
          rw [if_pos (by omega)]
        · rfl
      have hj₁ : w₁.journalAt E k = none := by
        obtain ⟨_, _, rfl⟩ := admit_ok h₁
        rw [commit_journalAt hjc, if_neg (Ne.symm hne), hj]
        split <;> rfl
      exact fold_refused_retains (admit_refusalsCanon hc h₁) (admit_journalCanon hjc h₁) h₂ hr₁ hj₁ hlt
  | w, w', .refusal r :: rest, hc, hjc, h, hr, hj, hlt => by
      obtain ⟨w₁, h₁, h₂⟩ := fold_cons_ok.mp h
      obtain ⟨-, -, -, -, hnot, -⟩ := refuse_facts h₁
      have hne : r.txId ≠ k := fun he => by subst he; exact hnot hh code hr
      have hr₁ : w₁.refusalAt E (.tx k) = some (.refused hh code) := by
        rw [refuse_refusalAt h₁, if_neg (by simp), if_neg (by simp [Ne.symm hne]), hr]
      have hjc₁ : w₁.JournalCanon E := by
        unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
      exact fold_refused_retains (refuse_refusalsCanon hc h₁) hjc₁ h₂ hr₁
        ((refuse_journalAt h₁ k).trans hj) hlt

end Nanodregg.Kernel

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **Height and steps on every reached World** (CODEC's `kernel/steps`): from a genesis, `height ≤
steps`, and the difference is the log's recorded refusals (`fold_steps_height`). (A carry sets
`steps` to the carried height, `carryWorld`, so a fold from it keeps the same.) -/
theorem reach_height_le_steps {X : Ctx D} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w : World D} {l : List (Step D)}
    (h : World.fold X.env (genesisWorld X name nonce allowance founders) l = .ok w) : w.height ≤ w.steps :=
  fold_height_le_steps (Nat.le_refl _) h

theorem genesisWorld_refusalsOk (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) : (genesisWorld X name nonce allowance founders).RefusalsOk X.env :=
  refusalsOk_of_empty rfl

/-- **A recorded refusal is final** (KERNEL-44, the A→B→A defect closed). After `World.refuse`
recorded call `c`'s refusal from `w₀`, every World a later log reaches below the refusal's prune
height answers `submit` of the very same call `refusedFinal` with the recorded code, without
re-deriving it: whatever its pins now see. -/
theorem submit_refused_final {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {r : Refused D}
    {l : List (Step D)} (hc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (h₁ : World.refuse X.env w₀ r = .ok w₁) (hid : r.txId = txIdOf X c) (hf : World.fold X.env w₁ l = .ok w₂)
    (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax) :
    submit X w₂ c = .error (.rejected (.refusedFinal r.code)) := by
  obtain ⟨-, -, -, hj, -, -⟩ := refuse_facts h₁
  have hjc₁ : w₁.JournalCanon X.env := by
    unfold World.JournalCanon; rw [(refuse_frame h₁).2.1]; exact hjc
  obtain ⟨hr₂, hj₂⟩ := fold_refused_retains (refuse_refusalsCanon hc h₁) hjc₁ hf (refuse_recorded h₁)
    ((refuse_journalAt h₁ _).trans hj) hlt
  rw [hid] at hr₂ hj₂
  unfold submit refusedAnswer
  rw [hj₂, hr₂]

/-- **A recorded call is never admitted, ever** (the twin of `submit_once`): below the prune height
`submit` answers `refusedFinal`; at and past it the call's own window has ended (its width is at most
`windowMax`, `checkBounds`, and it opened by the refusal's height), so no admission can follow. -/
theorem submit_refused_never {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {r : Refused D}
    {l : List (Step D)} (hc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (h₁ : World.refuse X.env w₀ r = .ok w₁) (hid : r.txId = txIdOf X c)
    (hnbc : r.notBefore = c.unsigned.notBefore)
    (hf : World.fold X.env w₁ l = .ok w₂) : ∀ out, submit X w₂ c ≠ .ok out := by
  intro ⟨t, w₃⟩ hs
  have hrid : r.txId = txIdOf X c ∧ r.notBefore = c.unsigned.notBefore := ⟨hid, hnbc⟩
  by_cases hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax
  · rw [submit_refused_final hc hjc h₁ hrid.1 hf hlt] at hs; cases hs
  · obtain ⟨-, hr, ha⟩ := submit_ok hs
    obtain ⟨_, _, _, _, _, _, hnb, hvu⟩ := receive_ok hr
    have hw := admit_window ha
    have hb := admit_bounded ha
    unfold checkBounds at hb
    simp only [except_bind_ok] at hb
    obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, hwm, _⟩ := hb
    rw [req_ok, decide_eq_true_eq] at hwm
    obtain ⟨-, hnb₀, -, -, -, -⟩ := refuse_facts h₁
    have hh₁ := (refuse_frame h₁).2.2.1
    have := fold_height hf
    rw [windowMax_eq] at *
    omega

/-- **`lookup`'s rule (PROTOCOL-33's shape) for a refused call**: below `journalForgets` of the call's
window, a recorded refusal is still answered by name. The record is pruned only after every height
the call could have been admitted at. -/
theorem refused_answers {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {r : Refused D}
    {l : List (Step D)} (hc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (h₁ : World.refuse X.env w₀ r = .ok w₁) (hid : r.txId = txIdOf X c) (hf : World.fold X.env w₁ l = .ok w₂)
    (hnf : journalForgets w₂.height r.notBefore = false) :
    submit X w₂ c = .error (.rejected (.refusedFinal r.code)) := by
  obtain ⟨-, hnb, -, -, -, -⟩ := refuse_facts h₁
  simp only [journalForgets, decide_eq_false_iff_not, Nat.not_le] at hnf
  exact submit_refused_final hc hjc h₁ hid hf (by omega)

/-- What `judge` recorded is final: the call it recorded is answered `refusedFinal` with the code of
the verdict it was refused with, on every later World below the prune height. -/
theorem judge_recorded_final {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    {l : List (Step D)} (hc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (hj : judge X w₀ c = .recorded v r w₁) (hf : World.fold X.env w₁ l = .ok w₂)
    (hlt : w₂.height < w₀.height + 1 + 2 * Bounds.windowMax) :
    submit X w₂ c = .error (.rejected (.refusedFinal v.code)) := by
  obtain ⟨-, -, rfl, hr⟩ := judge_recorded hj
  exact submit_refused_final hc hjc hr rfl hf hlt

/-- **What `judge` recorded is never admitted, ever** (`submit_refused_never` for the record `judge`
made). -/
theorem judge_recorded_never {X : Ctx D} {w₀ w₁ w₂ : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    {l : List (Step D)} (hc : w₀.RefusalsCanon X.env) (hjc : w₀.JournalCanon X.env)
    (hj : judge X w₀ c = .recorded v r w₁) (hf : World.fold X.env w₁ l = .ok w₂) :
    ∀ out, submit X w₂ c ≠ .ok out := by
  obtain ⟨-, -, rfl, hr⟩ := judge_recorded hj
  exact submit_refused_never hc hjc hr rfl rfl hf

/-- **Only an authenticated call is recorded**: `judge` records nothing for a call that is not
signed, for this World, by a key its member holds (KERNEL-47 amendment 7). -/
theorem judge_recorded_authenticated {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D}
    {r : Refused D} (hj : judge X w c = .recorded v r w') : authenticated X w c = true :=
  (judge_recorded hj).2.1

omit [Ord D] [DecidableEq D] in
/-- A recorded refusal's code names the verdict: `codeName` reads it back (`lookup`'s `refused NAME`). -/
theorem codeName_code (v : Verdict D) : codeName v.code = some v.name := by
  cases v with
  | refused r => cases r <;> rfl
  | rejected r => cases r <;> rfl

end Nanodregg.Kernel.Receive
