/-
# Hosting.Proofs.Loop — a round launches only qualifying grains and decides every id it was given

`step_launch_sound`: every launch a round emits is for an id of the round, names that id's
directory, and is `Controller.launch_sound`'s situation on the World's own cell (a lifecycle object
whose state decodes and desires `running`, no running child, a plan). `step_decides`: every id of
the round whose decision is a verdict gets exactly that action, so `step_kill_complete` (a running
child whose touched cell is gone or is not a lifecycle object is killed) and `step_launch_complete`
follow. `step_launch_marks`: after the round a launched grain's child counts as running, so the next
round does not launch it again before a report. `exited_not_running`: an exit report clears it.
`absorb_stranger`: a report for a grain the process never launched changes nothing the decisions
read. `returning_complete`: an exit of a launched grain sends its id back through the round.
`step_kept`: the memory is bounded by running children and qualifying cells. `step_one_per_grain`:
one action per grain per round.
-/
import Hosting.Loop
import Hosting.Proofs.Controller

namespace Nanodregg.Hosting.Proofs

open Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Controller Nanodregg.Hosting.Loop

/-! ## Pages -/

theorem pages_flatten {α : Type} {n : Nat} (hn : 0 < n) :
    ∀ (fuel : Nat) (l : List α), l.length ≤ fuel → (pages n fuel l).flatten = l
  | 0, [], _ => rfl
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => rfl
  | k + 1, x :: xs, h => by
    simp only [pages, List.flatten_cons]
    rw [pages_flatten hn k _ (by simp at h ⊢; omega), List.take_append_drop]

theorem pages_sublist {α : Type} {n : Nat} :
    ∀ (fuel : Nat) (l : List α), ∀ p ∈ pages n fuel l, p.Sublist l
  | 0, _, _, h => by simp [pages] at h
  | _ + 1, [], _, h => by simp [pages] at h
  | k + 1, x :: xs, p, h => by
    simp only [pages, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.take_sublist _ _
    · exact (pages_sublist k _ p h).trans (List.drop_sublist _ _)

theorem pages_length {α : Type} {n : Nat} :
    ∀ (fuel : Nat) (l : List α), ∀ p ∈ pages n fuel l, p.length ≤ n
  | 0, _, _, h => by simp [pages] at h
  | _ + 1, [], _, h => by simp [pages] at h
  | k + 1, x :: xs, p, h => by
    simp only [pages, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.length_take_le _ _
    · exact pages_length k _ p h

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] in
private theorem eraseDups_nodup_le' : ∀ (n : Nat) (l : List D), l.length ≤ n → l.eraseDups.Nodup
  | 0, [], _ => by simp
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => by simp
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, eraseDups_nodup_le' n _ ?_⟩
    · have := List.mem_eraseDups.mp hm
      simp at this
    · exact Nat.le_trans (List.length_filter_le _ _) (by simp at h; omega)

omit [Ord D] in
/-- A list without duplicates is its own `eraseDups`. -/
theorem eraseDups_of_nodup : ∀ {l : List D}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: as, h => by
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons]
    have hf : (as.filter fun b => !b == a) = as := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun e => h.1 (e ▸ hb)
      simpa using this
    rw [hf, eraseDups_of_nodup h.2]

/-- Over a page (no duplicates, at most `grainsMax` ids), `reconcile` decides every id of the
page: the paging and deduplication inside it drop nothing. -/
theorem reconcile_page {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {now : Nat}
    {live : List Live} {w : World D} {p : List D} (hnd : p.Nodup) (hlen : p.length ≤ Bounds.grainsMax)
    {i : D} (hi : i ∈ p) {v : Verdict}
    (hv : decideCell label pkgId now live (dirOf (bytesOf i)) (w.live E i) = some v) :
    { grain := dirOf (bytesOf i), verdict := v } ∈ reconcile E bytesOf label pkgId now live w p := by
  unfold reconcile
  rw [eraseDups_of_nodup hnd, List.take_of_length_le hlen]
  exact List.mem_filterMap.mpr ⟨i, hi, by simp [hv]⟩

/-! ## A round -/

omit [Ord D] in
theorem roundIds_nodup (st : State D) (touched : List D) (rs : List Report) :
    (roundIds st touched rs).Nodup := eraseDups_nodup_le' _ _ (Nat.le_refl _)

/-- Every id of the round whose decision is a verdict gets exactly that action. -/
theorem step_decides {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} {i : D} (hi : i ∈ roundIds st touched rs)
    {v : Verdict}
    (hv : decideCell label pkgId (rs.foldl (fun n r => max n r.atMs) st.now) (st.absorb rs)
      (dirOf (bytesOf i)) (w.live E i) = some v) :
    { grain := dirOf (bytesOf i), verdict := v } ∈ (Loop.step E bytesOf label pkgId w st touched rs).2 := by
  simp only [Loop.step]
  have hall := pages_flatten (n := Bounds.grainsMax) (by decide) _ (roundIds st touched rs) (Nat.le_refl _)
  have : i ∈ (pages Bounds.grainsMax (roundIds st touched rs).length (roundIds st touched rs)).flatten := by
    rw [hall]; exact hi
  obtain ⟨p, hp, hip⟩ := List.mem_flatten.mp this
  refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
  exact reconcile_page ((roundIds_nodup st touched rs).sublist (pages_sublist _ _ p hp))
    (pages_length _ _ p hp) hip hv

/-- Every launch a round emits is for one of its ids, names that id's directory, and is decided on
the World's own cell as `launch_sound` requires. -/
theorem step_launch_sound {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} {a : Action} {p : Plan}
    (ha : a ∈ (Loop.step E bytesOf label pkgId w st touched rs).2) (hl : a.verdict = .launch p) :
    ∃ i ∈ roundIds st touched rs, a.grain = dirOf (bytesOf i) ∧
      ∃ c gr, w.live E i = some c ∧ isGrain pkgId c = true ∧ grainOf a.grain c = some (gr, .running) ∧
        runningIn (st.absorb rs) a.grain = false ∧ plan label gr = .ok p := by
  simp only [Loop.step] at ha
  obtain ⟨pg, hpg, hapg⟩ := List.mem_flatMap.mp ha
  obtain ⟨i, hi, hg, hd⟩ := reconcile_names hapg
  refine ⟨i, (pages_sublist _ _ pg hpg).subset hi, hg, ?_⟩
  rw [hl] at hd
  rw [← hg] at hd
  obtain ⟨c, gr, h1, h2, h3, h4, -, h6⟩ := launch_sound hd
  exact ⟨c, gr, h1, h2, h3, h4, h6⟩

/-- A running child whose cell at an id of the round no longer qualifies — gone, not a lifecycle
object, undecodable, or not desiring `running` — is killed (`kill_sound`'s cases, all of them). -/
theorem step_kill_complete {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} {i : D} (hi : i ∈ roundIds st touched rs)
    (hu : runningIn (st.absorb rs) (dirOf (bytesOf i)) = true)
    (hc : w.live E i = none ∨ ∃ c, w.live E i = some c ∧
      (isGrain pkgId c = false ∨ grainOf (dirOf (bytesOf i)) c = none ∨
        ∃ gr ph, grainOf (dirOf (bytesOf i)) c = some (gr, ph) ∧ ph ≠ .running)) :
    { grain := dirOf (bytesOf i), verdict := .kill } ∈ (Loop.step E bytesOf label pkgId w st touched rs).2 := by
  apply step_decides hi
  rcases hc with h | ⟨c, h, hg | hd | ⟨gr, ph, hgr, hph⟩⟩
  · simp [decideCell, h, hu]
  · simp [decideCell, h, hu, hg]
  · rw [h]
    by_cases hg : isGrain pkgId c = true
    · exact malformed_running_killed hg hd hu
    · simp [decideCell, hu, hg]
  · by_cases hg : isGrain pkgId c = true
    · simp [decideCell, h, hu, hg, hgr, hph]
    · simp [decideCell, h, hu, hg]

omit [Ord D] in
/-- The touched ids are ids of the round. -/
theorem touched_mem_roundIds {st : State D} {touched : List D} {rs : List Report} {i : D}
    (hi : i ∈ touched) : i ∈ roundIds st touched rs :=
  List.mem_eraseDups.mpr (List.mem_append_left _ hi)

/-- A touched lifecycle grain that desires `running`, has no child, is not crash-looping and has a
plan is launched with it. -/
theorem step_launch_complete {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} {i : D} (hi : i ∈ touched) {c : Cell}
    {gr : Grain} {p : Plan} (hcell : w.live E i = some c) (hg : isGrain pkgId c = true)
    (hgr : grainOf (dirOf (bytesOf i)) c = some (gr, .running))
    (hu : runningIn (st.absorb rs) (dirOf (bytesOf i)) = false)
    (hcl : crashLooping (rs.foldl (fun n r => max n r.atMs) st.now) (st.absorb rs)
      (dirOf (bytesOf i)) = false) (hp : plan label gr = .ok p) :
    { grain := dirOf (bytesOf i), verdict := .launch p } ∈
      (Loop.step E bytesOf label pkgId w st touched rs).2 := by
  apply step_decides (touched_mem_roundIds hi)
  rw [hcell]; exact launch_complete hg hgr hu hcl hp

/-! ## Memory -/

private theorem ba_beq (a b : ByteArray) : (a == b) = decide (a = b) := by
  cases a with | mk x => cases b with | mk y =>
  show (x == y) = _
  by_cases h : x = y
  · subst h; simp
  · simp [h]

private theorem upsert_running_of {live : List Live} {g h : ByteArray} {f : Live → Live}
    (hf : ∀ l, l.grain = h → (f l).grain = h ∧ (f l).running = true) (hr : runningIn live g = true) :
    runningIn (upsert live h f) g = true := by
  unfold upsert runningIn at *
  simp only [ba_beq] at *
  split
  · obtain ⟨l, hl, hlr⟩ := List.any_eq_true.mp hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlr
    refine List.any_eq_true.mpr ⟨if decide (l.grain = h) = true then f l else l, List.mem_map_of_mem hl, ?_⟩
    by_cases e : l.grain = h
    · obtain ⟨h1, h2⟩ := hf l e
      have hg : h = g := e ▸ hlr.1
      simp [e, h1, h2, hg]
    · have ne : ¬ g = h := hlr.1 ▸ e
      simp [ne, hlr.1, hlr.2]
  · simp [List.any_append, hr]

private theorem upsert_running_self {live : List Live} {h : ByteArray} {f : Live → Live}
    (hf : ∀ l, l.grain = h → (f l).grain = h ∧ (f l).running = true) :
    runningIn (upsert live h f) h = true := by
  unfold upsert runningIn
  simp only [ba_beq]
  split
  · rename_i hany
    obtain ⟨l, hl, hlg⟩ := List.any_eq_true.mp hany
    have e : l.grain = h := by simpa using hlg
    refine List.any_eq_true.mpr ⟨f l, List.mem_map.mpr ⟨l, hl, by simp [e]⟩, ?_⟩
    have := hf l e; simp [this]
  · have := hf { grain := h, running := false, exits := [] } rfl
    simp [List.any_append, this]

private theorem afterOne_running {live : List Live} {g : ByteArray} (a : Action)
    (hr : runningIn live g = true) : runningIn (afterOne live a) g = true := by
  unfold afterOne
  split
  · exact upsert_running_of (fun l e => ⟨e, rfl⟩) hr
  · exact hr

private theorem foldl_afterOne_running : ∀ {acts : List Action} {live : List Live} {g : ByteArray},
    runningIn live g = true → runningIn (acts.foldl afterOne live) g = true
  | [], _, _, h => h
  | a :: _, _, _, h => by
    simp only [List.foldl_cons]
    exact foldl_afterOne_running (afterOne_running a h)

private theorem foldl_afterOne_launch : ∀ {acts : List Action} {live : List Live} {a : Action} {p : Plan},
    a ∈ acts → a.verdict = .launch p → runningIn (acts.foldl afterOne live) a.grain = true
  | [], _, _, _, h, _ => by simp at h
  | b :: bs, live, a, p, h, hl => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · apply foldl_afterOne_running
      unfold afterOne; rw [hl]
      exact upsert_running_self (fun l e => ⟨e, rfl⟩)
    · exact foldl_afterOne_launch h hl

omit [Ord D] [DecidableEq D] in
private theorem rememberOne_mono {bytesOf : D → ByteArray} {ids : List D} {g : ByteArray}
    {acc : List (ByteArray × D)} (a : Action) (h : acc.any (·.1 == g) = true) :
    (rememberOne bytesOf ids acc a).any (·.1 == g) = true := by
  unfold rememberOne
  split
  · split
    · exact h
    · split <;> simp [List.any_append, h]
  · exact h

omit [Ord D] [DecidableEq D] in
private theorem remember_mono {bytesOf : D → ByteArray} {ids : List D} {g : ByteArray} :
    ∀ {acts : List Action} {acc : List (ByteArray × D)}, acc.any (·.1 == g) = true →
      (acts.foldl (rememberOne bytesOf ids) acc).any (·.1 == g) = true
  | [], _, h => h
  | a :: _, _, h => by
    simp only [List.foldl_cons]
    exact remember_mono (rememberOne_mono a h)

omit [Ord D] [DecidableEq D] in
/-- A grain launched in a round whose id is among the round's ids is remembered. -/
theorem remember_has {bytesOf : D → ByteArray} {ids : List D} :
    ∀ {acts : List Action} {launched : List (ByteArray × D)} {a : Action} {p : Plan},
      a ∈ acts → a.verdict = .launch p → (∃ i ∈ ids, dirOf (bytesOf i) = a.grain) →
      (remember bytesOf ids launched acts).any (·.1 == a.grain) = true
  | [], _, _, _, h, _, _ => by simp at h
  | b :: bs, launched, a, p, h, hl, hex => by
    unfold remember
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · apply remember_mono
      unfold rememberOne
      rw [hl]
      simp only
      split
      · assumption
      · obtain ⟨i, hi, hgi⟩ := hex
        rcases hf : ids.find? (fun j => dirOf (bytesOf j) == a.grain) with _ | j
        · exfalso
          have := List.find?_eq_none.mp hf i hi
          simp [ba_beq, hgi] at this
        · simp [List.any_append, ba_beq]
    · exact remember_has h hl hex

/-- After a round, every grain it launched counts as running (and is kept in the memory): the next
round does not launch it again before the launcher reports. -/
theorem step_launch_marks {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} {a : Action} {p : Plan}
    (ha : a ∈ (Loop.step E bytesOf label pkgId w st touched rs).2) (hl : a.verdict = .launch p) :
    runningIn (Loop.step E bytesOf label pkgId w st touched rs).1.live a.grain = true := by
  obtain ⟨i, hi, hgi, -⟩ := step_launch_sound ha hl
  simp only [Loop.step] at ha ⊢
  generalize hacts : List.flatMap _ _ = acts at ha ⊢
  have hr := foldl_afterOne_launch (live := st.absorb rs) ha hl
  have hrem := remember_has (bytesOf := bytesOf) (ids := roundIds st touched rs)
    (launched := st.launched) ha hl ⟨i, hi, hgi.symm⟩
  simp only [prune]
  unfold runningIn at hr ⊢
  obtain ⟨l, hlm, hlr⟩ := List.any_eq_true.mp hr
  have hg : l.grain = a.grain := by
    simp only [Bool.and_eq_true, ba_beq, decide_eq_true_eq] at hlr; exact hlr.1
  obtain ⟨x, hx, hx1⟩ := List.any_eq_true.mp hrem
  have hx1' : x.1 = a.grain := by simpa [ba_beq] using hx1
  refine List.any_eq_true.mpr ⟨l, List.mem_filter.mpr ⟨hlm, ?_⟩, hlr⟩
  refine List.any_eq_true.mpr ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
  · have : runningIn (acts.foldl afterOne (st.absorb rs)) x.1 = true := by
      rw [hx1']; exact foldl_afterOne_launch ha hl
    unfold runningIn at this
    obtain ⟨m, hm, hmr⟩ := List.any_eq_true.mp this
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inl ⟨m, hm, hmr⟩
  · simp [ba_beq, hx1', hg]

/-- An exit report for `g` leaves no running child of `g`. -/
theorem exited_not_running (live : List Live) (g : ByteArray) (s : UInt32) (t : UInt64) :
    runningIn (absorbOne live (.exited g s t)) g = false := by
  simp only [absorbOne, upsert, runningIn, ba_beq]
  split
  · rw [List.any_eq_false]
    intro l hl
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hl
    by_cases e : m.grain = g <;> simp [e, exitAt]
  · next hn =>
    rw [List.any_eq_false]
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · have : ¬ l.grain = g := fun e => hn (List.any_eq_true.mpr ⟨l, hl, by simp [e]⟩)
      simp [this]
    · simp at hl; subst hl; simp [exitAt]

/-- A failed launch, likewise, and it counts as an exit. -/
theorem failed_not_running (live : List Live) (g : ByteArray) (why : LaunchFailure) (t : UInt64) :
    runningIn (absorbOne live (.failed g why t)) g = false := by
  have := exited_not_running live g 0 t
  simpa [absorbOne] using this

/-! ## Strangers, returns, bounds, one action per grain -/

omit [Ord D] [DecidableEq D] in
private theorem upsert_other {live : List Live} {g h : ByteArray} {f : Live → Live}
    (hf : ∀ l, (f l).grain = l.grain) (hne : h ≠ g) :
    runningIn (upsert live h f) g = runningIn live g := by
  unfold upsert runningIn
  simp only [ba_beq]
  split
  · rw [List.any_map]
    congr 1
    funext l
    by_cases e : l.grain = h
    · have : ¬ l.grain = g := fun e' => hne (e ▸ e')
      simp [e, hf, hne]
    · simp [e]
  · simp [List.any_append, hf, hne]

omit [Ord D] [DecidableEq D] in
private theorem absorbOne_other {live : List Live} {g : ByteArray} {r : Report} (hne : r.grain ≠ g) :
    runningIn (absorbOne live r) g = runningIn live g := by
  cases r <;> simp only [absorbOne, Report.grain] at hne ⊢ <;>
    exact upsert_other (fun l => rfl) hne

omit [Ord D] [DecidableEq D] in
private theorem foldl_absorb_other {g : ByteArray} :
    ∀ {rs : List Report} {live : List Live}, (∀ r ∈ rs, r.grain ≠ g) →
      runningIn (rs.foldl absorbOne live) g = runningIn live g
  | [], _, _ => rfl
  | r :: rs, live, h => by
    simp only [List.foldl_cons]
    rw [foldl_absorb_other (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      absorbOne_other (h r List.mem_cons_self)]

omit [Ord D] [DecidableEq D] in
/-- A report for a grain this process never launched changes nothing the decisions read: a
launcher cannot mark a stranger's child running, so no decision rests on a child the controller
did not start. -/
theorem absorb_stranger {st : State D} {rs : List Report} {g : ByteArray} (hg : st.knows g = false) :
    runningIn (st.absorb rs) g = runningIn st.live g := by
  unfold State.absorb
  apply foldl_absorb_other
  intro r hr e
  have := (List.mem_filter.mp hr).2
  rw [e, hg] at this
  exact Bool.noConfusion this

omit [Ord D] in
/-- An exit (or failed launch) report for a grain this process launched sends that grain's id back
through the round: a crashed child of a grain that still desires `running` is decided again. -/
theorem returning_complete {st : State D} {touched : List D} {rs : List Report} {g : ByteArray}
    {i : D} (hgi : (g, i) ∈ st.launched) {r : Report} (hr : r ∈ rs) (hg : r.grain = g)
    (hx : ∀ t, r ≠ .started g t) :
    ∃ j, (g, j) ∈ st.launched ∧ j ∈ roundIds st touched rs := by
  rcases hf : st.launched.find? (·.1 == g) with _ | x
  · have := List.find?_eq_none.mp hf (g, i) hgi
    simp [ba_beq] at this
  · have hx1 : x.1 = g := by simpa [ba_beq] using List.find?_some hf
    have hxm := List.mem_of_find?_eq_some hf
    refine ⟨x.2, by rw [← hx1]; exact hxm, List.mem_eraseDups.mpr (List.mem_append_right _ ?_)⟩
    unfold returning
    refine List.mem_filterMap.mpr ⟨r, hr, ?_⟩
    cases r with
    | started g' t => simp [Report.grain] at hg; subst hg; exact absurd rfl (hx t)
    | exited g' s t =>
      simp [Report.grain] at hg; subst hg
      simp [Report.grain, hf]
    | failed g' f t =>
      simp [Report.grain] at hg; subst hg
      simp [Report.grain, hf]

/-- The memory a round keeps is bounded by the World and the running children: every grain it
remembers has a running child or a cell that still qualifies, and every report it keeps is of a
remembered grain. -/
theorem step_kept {E : Env D} {bytesOf : D → ByteArray} {label pkgId : ByteArray} {w : World D}
    {st : State D} {touched : List D} {rs : List Report} :
    let r := Loop.step E bytesOf label pkgId w st touched rs
    (∀ x ∈ r.1.launched, runningIn (r.2.foldl afterOne (st.absorb rs)) x.1 = true ∨
      qualifies E pkgId w x.2 = true) ∧
    (∀ l ∈ r.1.live, ∃ x ∈ r.1.launched, x.1 = l.grain) := by
  simp only [Loop.step, prune]
  refine ⟨fun x hx => ?_, fun l hl => ?_⟩
  · have := (List.mem_filter.mp hx).2
    simpa [Bool.or_eq_true] using this
  · obtain ⟨-, h⟩ := List.mem_filter.mp hl
    obtain ⟨x, hx, hx1⟩ := List.any_eq_true.mp h
    exact ⟨x, hx, by simpa [ba_beq] using hx1⟩

private theorem flatMap_sublist {α β γ : Type} {ps : List (List α)} {R : List α → List β}
    {f : β → γ} {g : α → γ} (h : ∀ p ∈ ps, ((R p).map f).Sublist (p.map g)) :
    ((ps.flatMap R).map f).Sublist (ps.flatten.map g) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_append, List.flatten_cons]
    exact (h p List.mem_cons_self).append (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- One action per grain per round, whenever distinct ids have distinct bytes (on the deployed
digests: always, `digest_bytes_injective`). -/
theorem step_one_per_grain {E : Env D} {bytesOf : D → ByteArray} (hb : Function.Injective bytesOf)
    {label pkgId : ByteArray} {w : World D} {st : State D} {touched : List D} {rs : List Report} :
    ((Loop.step E bytesOf label pkgId w st touched rs).2.map (·.grain)).Nodup := by
  simp only [Loop.step]
  have hnd := roundIds_nodup st touched rs
  have hsub := flatMap_sublist (g := fun i => dirOf (bytesOf i))
    (ps := pages Bounds.grainsMax (roundIds st touched rs).length (roundIds st touched rs))
    (R := reconcile E bytesOf label pkgId (rs.foldl (fun n r => max n r.atMs) st.now) (st.absorb rs) w)
    (f := (·.grain)) (fun p hp => by
      have hpn := hnd.sublist (pages_sublist _ _ p hp)
      unfold reconcile
      rw [eraseDups_of_nodup hpn, List.take_of_length_le (pages_length _ _ p hp), List.map_filterMap]
      refine filterMap_sublist_map _ _ _ ?_
      intro i b hb'
      rcases hv : decideCell label pkgId (rs.foldl (fun n r => max n r.atMs) st.now) (st.absorb rs)
        (dirOf (bytesOf i)) (w.live E i) with _ | v <;> simp [hv] at hb'
      exact hb'.symm)
  rw [pages_flatten (by decide) _ _ (Nat.le_refl _)] at hsub
  exact (List.Pairwise.map (fun i => dirOf (bytesOf i))
    (fun _ _ hne heq => hne (hb (dirOf_injective heq))) hnd).sublist hsub

/-- On the deployed ids (32-byte digests), one action per grain per round. -/
theorem step_one_per_grain_deployed {E : Env Codec.Digest} {label pkgId : ByteArray} {w : World Codec.Digest}
    {st : State Codec.Digest} {touched : List Codec.Digest} {rs : List Report} :
    ((Loop.step E Codec.Digest.bytes label pkgId w st touched rs).2.map (·.grain)).Nodup :=
  step_one_per_grain digest_bytes_injective

end Nanodregg.Hosting.Proofs
