/- Guarded contextual closure: Repair. Moved without statement changes from Closure. -/
import Lang.Proofs.Contextual.Judge

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## Repair, candidate by candidate -/

theorem judge_restatus {I : Iface D E} {w : World E} {c : Candidate D} {st : Status} :
    judge I w { c with status := st } = judge I w c := rfl

theorem restatus_self (c : Candidate D) : { c with status := c.status } = c := by cases c; rfl

theorem repairPass_fst (w' : World E) (e : Edit E) (I : Iface D E) :
    ∀ (cs : List (Candidate D)) (n : Nat), (repairPass w' e I cs n).1 =
      cs.map fun c => if touches e I c then { c with status := judge I w' c } else c
  | [], _ => rfl
  | c :: cs, n => by
    unfold repairPass
    cases ht : touches e I c <;> simp [ht, repairPass_fst w' e I cs (n + 1)]

theorem repairCands_map (w' : World E) (e : Edit E) (I : Iface D E) (cs : List (Candidate D)) :
    repairCands w' e I cs =
      cs.map fun c => if touches e I c then { c with status := judge I w' c } else c :=
  repairPass_fst w' e I cs 0

/-- The pass's log is exactly the touched indices (offset `n`). -/
theorem repairPass_snd (w' : World E) (e : Edit E) (I : Iface D E) :
    ∀ (cs : List (Candidate D)) (n k : Nat), k ∈ (repairPass w' e I cs n).2 ↔
      n ≤ k ∧ ∃ c, cs[k - n]? = some c ∧ touches e I c = true
  | [], n, k => by simp [repairPass]
  | c :: cs, n, k => by
    have ih := repairPass_snd w' e I cs (n + 1) k
    unfold repairPass
    by_cases hkn : k = n
    · subst hkn
      cases ht : touches e I c
      · simp only [Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨h, -⟩; omega
        · rintro ⟨-, c', hc', ht'⟩
          simp at hc'; subst hc'; rw [ht] at ht'; cases ht'
      · simp [ht]
    · have hsh : ∀ (P : Prop), (n ≤ k ∧ P) ↔ (n + 1 ≤ k ∧ P) := by
        intro P; constructor <;> rintro ⟨h, hp⟩ <;> exact ⟨by omega, hp⟩
      cases ht : touches e I c
      · simp only [Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨h, c', hc', ht'⟩
          refine ⟨by omega, c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this]; simpa using hc'
        · rintro ⟨h, c', hc', ht'⟩
          have h' : n + 1 ≤ k := by omega
          refine ⟨h', c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this] at hc'; simpa using hc'
      · simp only [if_true, List.mem_cons, ih]
        constructor
        · rintro (h | ⟨h, c', hc', ht'⟩)
          · exact absurd h hkn
          · refine ⟨by omega, c', ?_, ht'⟩
            have : k - n = (k - (n + 1)) + 1 := by omega
            rw [this]; simpa using hc'
        · rintro ⟨h, c', hc', ht'⟩
          refine Or.inr ⟨by omega, c', ?_, ht'⟩
          have : k - n = (k - (n + 1)) + 1 := by omega
          rw [this] at hc'; simpa using hc'

/-- **Incremental = from scratch, at the candidate list.** On a coherent hole, re-judging only the
touched candidates gives exactly the list with EVERY candidate re-judged at the new world. -/
theorem repairCands_eq {I : Iface D E} {w : World E} {e : Edit E} {cs : List (Candidate D)}
    (hs : ∀ c ∈ cs, c.status = judge I w c) :
    repairCands (e.apply w) e I cs = cs.map fun c => { c with status := judge I (e.apply w) c } := by
  rw [repairCands_map]
  apply List.map_congr_left
  intro c hc
  cases ht : touches e I c
  · simp only [Bool.false_eq_true, if_false]
    rw [judge_frame ht, ← hs c hc]
  · rfl

theorem repairHole_cands (w' : World E) (e : Edit E) (I : Iface D E) (s : Slot D) :
    (repairHole w' e I s).1.cands = repairCands w' e I s.cands := by
  unfold repairHole
  cases hT : holeTouched e I s
  · simp only [if_true]
    have hno : ∀ c ∈ s.cands, touches e I c = false := by
      intro c hc
      cases ht : touches e I c
      · rfl
      · simp only [holeTouched, Bool.or_eq_false_iff, List.any_eq_false] at hT
        exact absurd ht (hT.2 c hc)
    rw [repairCands_map]
    conv => lhs; rw [← List.map_id s.cands]
    apply List.map_congr_left
    intro c hc; simp [hno c hc]
  · simp only [Bool.true_eq_false, if_false]
    split <;> rfl

theorem repair_slot {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) :
    (repair w e cl).1.slot I.name = (repairHole (e.apply w) e I (cl.slot I.name)).1 := by
  simp [repair, find_self hI]

/-- **REPAIR CORRECTNESS.** On a coherent closure, the observable after `repair e` (every retained
candidate's status, hole by hole, in order) equals the from-scratch analysis of the template and
the same retained candidates at the new world. -/
theorem repair_agrees_from_scratch {w : World E} {e : Edit E} {cl : Closure D E}
    (hc : Coherent w cl) :
    observe (repair w e cl).1 =
      observe (fromScratch (e.apply w) cl.tpl fun u => (cl.slot u).cands) := by
  unfold observe
  apply List.map_congr_left
  intro I hI
  have hI' : I ∈ cl.tpl.Ω := hI
  rw [repair_slot (w := w) (e := e) hI', repairHole_cands, repairCands_eq (hc I hI')]
  simp [fromScratch, find_name_self cl.tpl.names hI']

/-- Repair re-establishes coherence at the new world. -/
theorem repair_coherent {w : World E} {e : Edit E} {cl : Closure D E} (hc : Coherent w cl) :
    Coherent (e.apply w) (repair w e cl).1 := by
  intro I hI c hc'
  have hI' : I ∈ cl.tpl.Ω := hI
  rw [repair_slot (w := w) (e := e) hI', repairHole_cands, repairCands_eq (hc I hI')] at hc'
  obtain ⟨c0, _, rfl⟩ := List.mem_map.1 hc'
  rfl

theorem fromScratch_coherent (w : World E) (tpl : Template D E) (cands : Nat → List (Candidate D)) :
    Coherent w (fromScratch w tpl cands) := by
  intro I hI c hc
  simp only [fromScratch, find_name_self tpl.names hI] at hc
  obtain ⟨c0, _, rfl⟩ := List.mem_map.1 hc
  rfl

/-- **LOCALITY, candidate by candidate.** Repair carries an untouched candidate unchanged (the same
record, status included): it is not re-judged. -/
theorem repair_carries_untouched {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) {i : Nat} {c : Candidate D} (hci : (cl.slot I.name).cands[i]? = some c)
    (ht : touches e I c = false) : ((repair w e cl).1.slot I.name).cands[i]? = some c := by
  rw [repair_slot hI, repairHole_cands]
  simp [repairCands_map, List.getElem?_map, hci, ht]

/-- **LOCALITY, the boundary theorem.** A token edit whose token is no dependency of any retained
candidate and backs no hole hypothesis leaves the closure exactly as it was, with no outcome and an
empty repair log (the log is emitted by the same branch of `repairPass` that re-judges). -/
theorem locality {w : World E} {t : Token} {e : Edit E} (he : e = .withdraw t ∨ e = .assert t)
    {cl : Closure D E}
    (hfree : ∀ I ∈ cl.tpl.Ω, (∀ h ∈ I.hyps, h.2 ≠ t) ∧ ∀ c ∈ (cl.slot I.name).cands, t ∉ deps I c) :
    (repair w e cl).1 = cl ∧ (repair w e cl).2.1 = [] ∧ (repair w e cl).2.2 = [] := by
  have hT : ∀ I ∈ cl.tpl.Ω, holeTouched e I (cl.slot I.name) = false := by
    intro I hI
    obtain ⟨hh, hd⟩ := hfree I hI
    simp only [holeTouched, Bool.or_eq_false_iff, List.any_eq_false]
    refine ⟨?_, ?_⟩
    · rcases he with rfl | rfl
      · simp only [hypOf, Option.isSome_map, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
          List.find?_eq_none, decide_eq_true_eq]
        exact fun h hm => hh h hm
      · rfl
    · intro c hc
      rcases he with rfl | rfl <;> simp [touches, hd c hc]
  have hR : ∀ I ∈ cl.tpl.Ω, repairHole (e.apply w) e I (cl.slot I.name) = (cl.slot I.name, none) := by
    intro I hI; simp [repairHole, hT I hI]
  have houts : (repair w e cl).2.1 = [] := by
    simp only [repair, List.filterMap_eq_nil_iff]
    intro I hI; simp [hR I hI]
  have hlog : (repair w e cl).2.2 = [] := by
    simp only [repair, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
    intro I hI; simp [rejudgedIn, hT I hI]
  refine ⟨?_, houts, hlog⟩
  have hslot : (repair w e cl).1.slot = cl.slot := by
    funext u
    simp only [repair]
    split
    · rename_i I hf
      obtain ⟨hI, rfl⟩ := find_some hf
      rw [hR I hI]
    · rfl
  have hhist : (repair w e cl).1.hist = cl.hist := by
    have : (repair w e cl).1.hist = cl.hist ++ (repair w e cl).2.1.filterMap Outcome.event := rfl
    rw [this, houts]; simp
  cases cl
  simp only [repair] at hslot hhist ⊢
  simp only [hslot] at *
  congr

/-- Withdrawal, at the closure: after a withdrawal and repair, a `conflict` in a coherent closure
was already a `conflict`, with the same evidence, at the same index. -/
theorem withdraw_never_refutes_closure {w : World E} {t : Token} {cl : Closure D E}
    (hc : Coherent w cl) {I : Iface D E} (hI : I ∈ cl.tpl.Ω) {i : Nat} {c' : Candidate D}
    {ev : Evidence} (h : ((withdraw w t cl).1.slot I.name).cands[i]? = some c')
    (hev : c'.status = .conflict ev) :
    ∃ c, (cl.slot I.name).cands[i]? = some c ∧ c.status = .conflict ev := by
  unfold withdraw at h
  rw [repair_slot hI, repairHole_cands, repairCands_eq (hc I hI), List.getElem?_map] at h
  cases hci : (cl.slot I.name).cands[i]? with
  | none => simp [hci] at h
  | some c =>
    simp only [hci, Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨c, rfl, ?_⟩
    rw [hc I hI c (List.mem_of_getElem? hci)]
    exact withdraw_never_refutes.1 hev

/-! ## The repair log -/

theorem iface_eq_of_name {cl : Closure D E} {I J : Iface D E} (hI : I ∈ cl.tpl.Ω)
    (hJ : J ∈ cl.tpl.Ω) (hn : J.name = I.name) : J = I := by
  have h1 := find_self (cl := cl) hI
  have h2 := find_self (cl := cl) hJ
  rw [hn, h1] at h2
  exact (Option.some.inj h2).symm

/-- **LOCALITY, as work done.** The repair log names exactly the touched candidates of the closure:
`(I.name, k)` is logged iff candidate `k` of hole `I` is touched by the edit. An untouched candidate
is never re-judged (a recompute-all repair logs every candidate and fails this). -/
theorem repair_rejudged_eq_touched {w : World E} {e : Edit E} {cl : Closure D E} {I : Iface D E}
    (hI : I ∈ cl.tpl.Ω) (k : Nat) :
    (I.name, k) ∈ (repair w e cl).2.2 ↔
      ∃ c, (cl.slot I.name).cands[k]? = some c ∧ touches e I c = true := by
  simp only [repair, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨J, hJ, k', hk', hn, rfl⟩
    obtain rfl := iface_eq_of_name hI hJ hn
    unfold rejudgedIn at hk'
    split at hk'
    · cases hk'
    · simpa using (repairPass_snd _ e J _ 0 k').1 hk'
  · rintro ⟨c, hc, ht⟩
    refine ⟨I, hI, k, ?_, rfl, rfl⟩
    unfold rejudgedIn
    have hT : holeTouched e I (cl.slot I.name) = true := by
      simp only [holeTouched, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨c, List.mem_of_getElem? hc, ht⟩
    simp only [hT, Bool.true_eq_false, if_false]
    exact (repairPass_snd _ e I _ 0 k).2 ⟨Nat.zero_le _, c, by simpa using hc, ht⟩


end Nanodregg.Lang.Contextual

/-- From-scratch consistency: on a coherent closure, repairing an edit produces exactly the
candidate-status observation of full recomputation on the same retained problem.
Stein–Chang–Sridharan, Demanded Abstract Interpretation (2021), Thm.6.1, PDF p.10 names this
property; Mokhov–Mitchell–Peyton Jones, Build Systems à la Carte (2018), Def.3.1 p.79:11
gives its build-system analogue. Selection and accepted history are not this observable.
This is correctness, not Def.2.1 minimality; Trace.repair_minimal supplies the latter for
declared finite reads. The landed name and coherence premise are unchanged. -/
add_decl_doc Nanodregg.Lang.Contextual.repair_agrees_from_scratch
