/- Verifying traces: complete observations, exact work, and from-scratch consistency. -/
import Lang.Contextual.Trace

namespace Nanodregg.Lang.Contextual.Trace
variable {D : CalculusData} {K V : Type}

/-- Factoring the guard and all signed token reads preserves the entire old verdict.
Mokhov et al. 2018, Def.3.1 p.79:11 and §4.2.2 pp.79:14–15. -/
theorem evaluate_observe (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Candidate D) :
    evaluate g I c (observe g I w c) = judge (g.install I) w c := rfl

/-- Guard completeness by construction, rather than an unproved ReadsOnly assumption.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
theorem guard_reads_only (g : Guard D K V) (I : Iface D (K → V))
    (a b : K → V) (t : D.Tm) (h : ∀ k ∈ g.reads t, a k = b k) :
    (g.install I).guard a t = (g.install I).guard b t := by
  change g.run t _ = g.run t _
  rw [List.map_congr_left h]

/-- Complete observations determine judgments, with no ambient-world equality premise.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
theorem observation_complete (g : Guard D K V) (I : Iface D (K → V))
    (a b : World (K → V)) (c : Candidate D)
    (h : observe g I a c = observe g I b c) :
    judge (g.install I) a c = judge (g.install I) b c := by
  rw [← evaluate_observe, ← evaluate_observe, h]

/-- Successful collection establishes coverage and exact values, assuming only that PROVIDED
observations are authentic. Completeness is the conclusion. Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_sound {A B R : Type} (missing : A → R) (read : A → Option B)
    (f : A → B) (agree : ∀ k v, read k = some v → v = f k)
    (ks : List A) (vs : List B) (h : collect missing read ks = .ok vs) :
    vs = ks.map f ∧ ∀ k ∈ ks, read k = some (f k) := by
  induction ks generalizing vs with
  | nil => simp [collect] at h; subst vs; simp
  | cons k ks ih =>
    cases hk : read k with
    | none => simp [collect, hk] at h
    | some v =>
      cases hr : collect missing read ks with
      | error e => simp [collect, hk, hr] at h
      | ok rest =>
        simp [collect, hk, hr] at h
        subst vs
        obtain ⟨rfl, hrest⟩ := ih _ hr
        have hv := agree k v hk
        subst v
        exact ⟨rfl, by simpa [hk] using hrest⟩

/-- Honest total observations always collect; this supplies the success-side inhabitant.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_total {A B R : Type} (missing : A → R) (f : A → B) (ks : List A) :
    collect missing (fun k => some (f k)) ks = .ok (ks.map f) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [collect, ih]

/-- An omitted declared key prevents success, including negative/blocker reads.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem collect_missing {A B R : Type} (missing : A → R) (read : A → Option B)
    (ks : List A) (k : A) (hk : k ∈ ks) (hn : read k = none) :
    ∀ vs, collect missing read ks ≠ .ok vs := by
  induction ks with
  | nil => cases hk
  | cons a ks ih =>
    intro vs h
    cases ha : read a with
    | none => simp [collect, ha] at h
    | some v =>
      rcases List.mem_cons.1 hk with rfl | hk
      · rw [ha] at hn; cases hn
      · cases hr : collect missing read ks with
        | error e => simp [collect, ha, hr] at h
        | ok rest => exact ih hk rest hr

/-- Cache coherence is an independently checkable relation, not a constructor proof field.
Mokhov et al. 2018, Def.3.1 p.79:11, §4.2.2 pp.79:14–15. -/
def Valid (g : Guard D K V) (I : Iface D (K → V)) (c : Cached D V) : Prop :=
  c.candidate.status = evaluate g I c.candidate c.trace

/-- Initialization establishes cache coherence. Mokhov et al. 2018, §4.2.2 p.79:15. -/
theorem seed_valid (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Candidate D) : Valid g I (seed g I w c) := rfl

/-- Refresh preserves coherence, including the reused branch.
Mokhov et al. 2018, §4.2.2 p.79:15. -/
theorem refresh_valid [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Cached D V) (h : Valid g I c) :
    Valid g I (refresh g I w c) := by
  unfold refresh
  split
  · exact seed_valid g I w c.candidate
  · exact h

/-- From-scratch consistency of one candidate; the unchanged branch uses the complete trace.
Mokhov et al. 2018, Def.3.1 p.79:11; Stein et al. 2021, Thm.6.1 PDF p.10. -/
theorem refresh_consistent [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (c : Cached D V) (h : Valid g I c) :
    (refresh g I w c).candidate.status = judge (g.install I) w c.candidate := by
  unfold refresh
  split
  · exact evaluate_observe g I w c.candidate
  · rename_i hn
    have he : c.trace = observe g I w c.candidate := by simpa [meets] using hn
    rw [h, he, evaluate_observe]

/-- The pass preserves candidate order and reuses exactly the chosen branch.
Mokhov et al. 2018, Def.2.1 p.79:3. -/
theorem repair_entries [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (cs : List (Cached D V)) (n : Nat) :
    (repair g I w cs n).entries = cs.map (refresh g I w) := by
  induction cs generalizing n with
  | nil => rfl
  | cons c cs ih => simp [repair, ih]

/-- From-scratch consistency of every retained status, in order.
Mokhov et al. 2018, Def.3.1 p.79:11; Stein et al. 2021, Thm.6.1 PDF p.10. -/
theorem from_scratch_consistency [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (cs : List (Cached D V)) (n : Nat)
    (h : ∀ c ∈ cs, Valid g I c) :
    ((repair g I w cs n).entries.map fun c => c.candidate.status) =
      cs.map (fun c => judge (g.install I) w c.candidate) := by
  rw [repair_entries, List.map_map]
  exact List.map_congr_left fun c hc => refresh_consistent g I w c (h c hc)

/-- Exact work: a logged index is precisely a retained candidate with a changed trace.
This is minimality relative to declared finite reads, not a globally smallest read-set.
Mokhov et al. 2018, Def.2.1 p.79:3 and §4.2.2 pp.79:14–15. -/
theorem repair_minimal [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) :
    ∀ (cs : List (Cached D V)) (n k : Nat),
      k ∈ (repair g I w cs n).rejudged ↔
      n ≤ k ∧ ∃ c, cs[k - n]? = some c ∧ meets g I w c = true
  | [], n, k => by simp [repair]
  | c :: cs, n, k => by
    have ih := repair_minimal g I w cs (n + 1) k
    by_cases hkn : k = n
    · subst k
      cases ht : meets g I w c
      · simp only [repair, ht, Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨h, _⟩; omega
        · rintro ⟨_, c', hc', ht'⟩
          simp at hc'; subst c'; rw [ht] at ht'; cases ht'
      · simp [repair, ht]
    · by_cases hlt : k < n
      · have hn : ¬ n ≤ k := by omega
        have hn' : ¬ n + 1 ≤ k := by omega
        cases ht : meets g I w c <;> simp [repair, ht, ih, hn, hn', hkn]
      have shift : k - n = (k - (n + 1)) + 1 := by omega
      cases ht : meets g I w c <;>
        simp only [repair, ht, Bool.false_eq_true, if_false, if_true,
          List.mem_cons, ih, hkn, false_or, shift, List.getElem?_cons_succ]
      all_goals constructor <;> rintro ⟨h, c', hc', ht'⟩ <;> exact ⟨by omega, c', hc', ht'⟩

/-- A candidate executes at most once per pass, even with duplicate fillings.
Mokhov et al. 2018, Def.2.1 p.79:3. -/
theorem repair_once [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (cs : List (Cached D V)) (n : Nat) :
    (repair g I w cs n).rejudged.Nodup := by
  induction cs generalizing n with
  | nil => simp [repair]
  | cons c cs ih =>
    have hn : n ∉ (repair g I w cs (n + 1)).rejudged := by
      intro h
      have := (repair_minimal g I w cs (n + 1) n).1 h
      omega
    cases ht : meets g I w c <;> simp [repair, ht, hn, ih]

/-- Filtering tagged observations recovers exactly the signed token projection.
Mokhov et al. 2018, §4.2.2 p.79:14. -/
theorem tagged_filter {A : Type} (p : A → Bool) (xs : List A) :
    (((xs.map fun x => (x, p x)).filter Prod.snd).map Prod.fst) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx, ih]

/-- Honest provided pins plus successful capture establish the COMPLETE observation. No
coverage premise is imposed on the caller. Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
theorem capture_sound (g : Guard D K V) (I : Iface D (K → V)) (c : Candidate D)
    (w : World (K → V)) (env : K → Option V) (live : Token → Option Bool)
    (he : ∀ k v, env k = some v → v = w.env k)
    (hl : ∀ t b, live t = some b → b = w.live t)
    (s : Snapshot V) (h : capture g I c env live = .ok s) :
    s = observe g I w c := by
  cases es : collect Missing.environment env (g.reads c.filling) with
  | error e => simp [capture, es, bind, Except.bind] at h
  | ok ev =>
    cases ms : collect (Missing.token (K := K))
        (fun t => (live t).map fun b => (t, !b)) (effSupports I c) with
    | error e => simp [capture, es, ms, bind, Except.bind] at h
    | ok mv =>
      cases bs : collect (Missing.token (K := K))
          (fun t => (live t).map fun b => (t, b)) c.blockers with
      | error e => simp [capture, es, ms, bs, bind, Except.bind] at h
      | ok bv =>
        simp [capture, es, ms, bs, bind, Except.bind, pure, Except.pure] at h
        subst s
        have hev := (collect_sound Missing.environment env w.env he _ _ es).1
        have hmv := (collect_sound (Missing.token (K := K))
          (fun t => (live t).map fun b => (t, !b)) (fun t => (t, !w.live t))
          (by
            intro t v hv
            cases ht : live t with
            | none => simp [ht] at hv
            | some b =>
              simp [ht] at hv
              subst v
              rw [hl t b ht]) _ _ ms).1
        have hbv := (collect_sound (Missing.token (K := K))
          (fun t => (live t).map fun b => (t, b)) (fun t => (t, w.live t))
          (by
            intro t v hv
            cases ht : live t with
            | none => simp [ht] at hv
            | some b =>
              simp [ht] at hv
              subst v
              rw [hl t b ht]) _ _ bs).1
        rw [hev, hmv, hbv, tagged_filter, tagged_filter]
        rfl

/-- Successful checked judgment equals the existing world judgment, without assuming a
complete pin set. Authentication of each PROVIDED value remains the receiver's obligation.
Mokhov et al. 2018, Def.3.1 p.79:11, §4.2.2 pp.79:14–15. -/
theorem checkedJudge_sound (g : Guard D K V) (I : Iface D (K → V)) (c : Candidate D)
    (w : World (K → V)) (env : K → Option V) (live : Token → Option Bool)
    (he : ∀ k v, env k = some v → v = w.env k)
    (hl : ∀ t b, live t = some b → b = w.live t)
    (st : Status) (h : checkedJudge g I c env live = .ok st) :
    st = judge (g.install I) w c := by
  cases hc : capture g I c env live with
  | error e => simp [checkedJudge, hc, Except.map] at h
  | ok s =>
    simp [checkedJudge, hc, Except.map] at h
    rw [← h, capture_sound g I c w env live he hl s hc, evaluate_observe]

/-- Total authenticated observations inhabit the checked judgment's successful branch.
Mokhov et al. 2018, §4.2.2 pp.79:14–15. -/
theorem checkedJudge_total (g : Guard D K V) (I : Iface D (K → V))
    (c : Candidate D) (w : World (K → V)) :
    checkedJudge g I c (fun k => some (w.env k)) (fun t => some (w.live t)) =
      .ok (judge (g.install I) w c) := by
  simp only [checkedJudge, capture, Option.map_some, collect_total]
  simp only [bind, Except.bind, pure, Except.pure, tagged_filter, Except.map]
  rfl

/-- Changed-output indices are exact, independently of whether an input was dirty.
Mokhov et al. 2018, early cutoff §2.3 p.79:5, §4.2.2 p.79:15. -/
theorem changed_iff [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) :
    ∀ (cs : List (Cached D V)) (n k : Nat),
      k ∈ (repair g I w cs n).changed ↔
      n ≤ k ∧ ∃ c, cs[k - n]? = some c ∧
        (refresh g I w c).candidate.status ≠ c.candidate.status
  | [], n, k => by simp [repair]
  | c :: cs, n, k => by
    have ih := changed_iff g I w cs (n + 1) k
    by_cases hkn : k = n
    · subst k
      by_cases ht : (refresh g I w c).candidate.status ≠ c.candidate.status
      · simp [repair, ht]
      · simp only [repair, ht, if_false, ih]
        constructor
        · rintro ⟨h, _⟩; omega
        · rintro ⟨_, c', hc', ht'⟩
          simp at hc'; subst c'; exact False.elim (ht ht')
    · by_cases hlt : k < n
      · have hn : ¬ n ≤ k := by omega
        have hn' : ¬ n + 1 ≤ k := by omega
        by_cases ht : (refresh g I w c).candidate.status ≠ c.candidate.status <;>
          simp [repair, ht, ih, hn, hn', hkn]
      have shift : k - n = (k - (n + 1)) + 1 := by omega
      by_cases ht : (refresh g I w c).candidate.status ≠ c.candidate.status <;>
        simp [repair, ht, ih, hkn, shift]
      all_goals intro x hx hs; omega

/-- A rejudged candidate with unchanged status does not dirty holes reading that selection's
status. The premise compares a fresh judgment, not the implementation's dirty flag.
Mokhov et al. 2018, early cutoff §2.3 p.79:5, §4.2.2 p.79:15. -/
theorem early_cutoff [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (cs : List (Cached D V)) (k u : Nat) (c : Cached D V)
    (hc : cs[k]? = some c) (hv : Valid g I c)
    (hs : judge (g.install I) w c.candidate = c.candidate.status) :
    dirtyReaders (repair g I w cs 0) [(u, k)] = [] := by
  have hn : k ∉ (repair g I w cs 0).changed := by
    intro h
    obtain ⟨_, c', hc', hne⟩ := (changed_iff g I w cs 0 k).1 h
    simp only [Nat.sub_zero, hc, Option.some.injEq] at hc'
    subst c'
    exact hne ((refresh_consistent g I w c hv).trans hs)
  simp [dirtyReaders, hn]

/-- Repeated repairs remain coherent, so consistency is usable beyond one edit.
Mokhov et al. 2018, Def.3.1 p.79:11, §4.2.2 p.79:15. -/
theorem repair_valid [DecidableEq V] (g : Guard D K V) (I : Iface D (K → V))
    (w : World (K → V)) (cs : List (Cached D V)) (n : Nat)
    (h : ∀ c ∈ cs, Valid g I c) :
    ∀ c ∈ (repair g I w cs n).entries, Valid g I c := by
  rw [repair_entries]
  intro c hc
  obtain ⟨old, ho, rfl⟩ := List.mem_map.1 hc
  exact refresh_valid g I w old (h old ho)

end Nanodregg.Lang.Contextual.Trace
