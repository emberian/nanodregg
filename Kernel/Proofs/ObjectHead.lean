/-
# Kernel.Proofs.ObjectHead — an object's head is fixed under the follower's fold (KERNEL-64)

An object cell's slots below `stateBase` are its HEAD: `slotPackage` (0, the package; absent for a
data object), `slotOwner` (1), and the extra laws at `lawBase ≤ k < stateBase`. Its state is
everything from `stateBase` on.

* `turn_object_head`: a signed call derived from `w` (`receive`) and admitted to `w'`, at an object
  live in `w`: the object is live in `w'`, still an object, and its slots below `lawBase` (package and
  owner) read what they read; when it has a package (a PROGRAMMED object), every slot below
  `stateBase` does (its laws too). Over every Body: the turn either keeps the object, or is its signed
  `write` (state keys only) or `law` (law keys only, and refused `hasMethods` on a programmed object),
  or an invoke of it some walk dispatched (state keys only: `checkState` of the run's result), and no
  other receiver at any depth has an effect at an object (`effect_at_object`).
* `submit_object_head`: the same of the Host's `submit`.
* `honest_object_head`: THE FOLD. Along any honest folded log (every log the follower takes:
  `Kernel.Proofs.Rederive.rederiveLog_sound`; each Turn derived from its own event, each refusal
  re-judged), an object live at its start is live at its end, an object, with its package and owner
  as they were, and a programmed object's whole head as it was.
* `fold_package_fixed`: the corollary HOSTING's member socket names (HOSTING-42 trigger (ii)): the
  package slot, and `packageOf`, of a live object are the same at every World an honest log folds
  to from it.

Not over a bare `World.fold`: the writer's fold admits any Turn the kernel's own checks pass, and
`touchCheck` checks a write's pin and `postWrite` of a RAM cell only its size, so a hand-made Turn may
write slot 0 of an object (or retire it). The fact is the receivers', so it holds where every Turn is
a derivation (`receive`): what the follower checks, and what `Honest` says. Not "at birth": an object
born inside a log is live at the World after its creating turn, and the theorem starts there.
-/
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.Rederive
import Kernel.Proofs.WriteNext

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Keys a receiver's write can reach -/

omit [Ord D] [DecidableEq D] in
private theorem checkStateFrom_keys {lo : Nat} :
    ∀ {s : Slots}, checkStateFrom (D := D) lo s = .ok () → ∀ p ∈ s, lo ≤ p.1
  | [], _, _, hp => by cases hp
  | q :: rest, h, p, hp => by
      unfold checkStateFrom at h
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, hq, h⟩ := h
      rw [req_ok, decide_eq_true_eq] at hq
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · have := checkStateFrom_keys h p hp
        omega

private theorem stateOf_keys {cell : Cell} {p : Nat × ByteArray} (h : p ∈ stateOf cell) : stateBase ≤ p.1 := by
  simp only [stateOf, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

private theorem lawSlotsOf_keys {cell : Cell} {p : Nat × ByteArray} (h : p ∈ lawSlotsOf cell) : lawBase ≤ p.1 := by
  simp only [lawSlotsOf, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

omit [Ord D] [DecidableEq D] in
private theorem lawSlots_keys {X : Ctx D} {laws : List D} {p : Nat × ByteArray} (h : p ∈ lawSlots X laws) :
    lawBase ≤ p.1 := by
  simp only [lawSlots, List.mem_map] at h
  obtain ⟨⟨l, i⟩, -, rfl⟩ := h
  exact Nat.le_add_right _ _

private theorem mem_erase {k : Nat} : ∀ {s : Slots} {q : Nat × ByteArray}, q ∈ Slots.erase k s → q ∈ s
  | [], _, h => by simp [Slots.erase] at h
  | (k', v') :: rest, q, h => by
      simp only [Slots.erase] at h
      split at h
      · exact List.mem_cons_of_mem _ h
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_erase h)

private theorem applyEdits_keys :
    ∀ (edits : List (Nat × Option ByteArray)) {s : Slots}, (∀ p ∈ s, stateBase ≤ p.1) →
      ∀ p ∈ applyEdits s edits, stateBase ≤ p.1
  | [], _, h => h
  | e :: rest, s, h => by
      have step : ∀ p ∈ (match e.2 with
          | some v => s.set (stateBase + e.1) v
          | none => s.erase (stateBase + e.1)), stateBase ≤ p.1 := by
        intro p hp
        cases he : e.2 with
        | some v =>
            rw [he] at hp
            rcases mem_set hp with rfl | hp
            · exact Nat.le_add_right _ _
            · exact h p hp
        | none =>
            rw [he] at hp
            exact h p (mem_erase hp)
      exact applyEdits_keys rest step

private theorem diffOps_lower {lo : Nat} {old new : Slots} (ho : ∀ p ∈ old, lo ≤ p.1)
    (hn : ∀ p ∈ new, lo ≤ p.1) : ∀ o ∈ diffOps old new, lo ≤ o.key := by
  intro o h
  rcases diffOps_keys h with ⟨p, hp, hk⟩ | ⟨p, hp, hk⟩
  · rw [hk]; exact hn p hp
  · rw [hk]; exact ho p hp

omit [Ord D] [DecidableEq D] in
/-- A cell `packageOf` reads as a data object holds nothing at `slotPackage`. -/
private theorem packageOf_none {X : Ctx D} {obj : D} {cell : Cell} (h : packageOf X obj cell = .ok none) :
    cell.slots.get slotPackage = none := by
  cases hg : cell.slots.get slotPackage with
  | none => rfl
  | some b =>
      unfold packageOf at h
      rw [hg] at h
      cases hd : X.digestOf b <;> simp [hd] at h

/-! ## One turn -/

/-- What a receiver's own write of a cell (`writeOf`'s act, every touch of the cell carrying it)
leaves there: the cell, live, of its kind, reading what it read at every key no op names. -/
private theorem admit_writeOf_slots {E : Env D} {w w' : World D} {t : Turn D} {obj : D} {cell : Cell}
    {ops : List Op} (ha : World.admit E w t = .ok w') (hl : w.live E obj = some cell)
    (hall : ∀ x ∈ t.touches, x.cell = obj → x.act = if ops.isEmpty then .keep else .write ops)
    (hex : ∃ x ∈ t.touches, x.cell = obj) :
    ∃ cell', w'.live E obj = some cell' ∧ cell'.kind = cell.kind ∧
      ∀ k, (∀ o ∈ ops, o.key ≠ k) → cell'.slots.get k = cell.slots.get k := by
  by_cases he : ops.isEmpty = true
  · obtain ⟨posts, hk, -⟩ := admit_ok ha
    have hframe := admit_frame ha (fun x hx hxc => by rw [hall x hx hxc, if_pos he]) (live_not_created hk hl)
    refine ⟨cell, ?_, rfl, fun _ _ => rfl⟩
    unfold World.live; rw [hframe]; exact hl
  · obtain ⟨hl', -⟩ := admit_live_write ha hl hex (fun x hx hxc => by rw [hall x hx hxc, if_neg he])
    exact ⟨_, hl', rfl, fun k hk => get_applyOps_ne ops cell.slots hk⟩

/-- **One derived turn keeps an object's head.** A signed call derived from `w` and admitted to `w'`,
and an object live in `w`: the object is live in `w'`, an object, its package and owner slots (below
`lawBase`) read what they read, and when it has a package every slot below `stateBase` (its laws
too) does. -/
theorem turn_object_head [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {obj : D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hl : w.live X.env obj = some cell)
    (hk : cell.kind = kindObject) :
    ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
      (∀ k, k < lawBase → cell'.slots.get k = cell.slots.get k) ∧
      (cell.slots.get slotPackage ≠ none → ∀ k, k < stateBase → cell'.slots.get k = cell.slots.get k) := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, _k, hd, hs⟩ := receiveWith_sealed hw
  replace hd := derive_of_withTicks hd
  rw [derive_eq] at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok R =>
  rw [hR] at hd
  simp only [Except.map, Except.ok.injEq] at hd
  subst hd
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  by_cases hex : ∃ e ∈ R.1.effects, e.1 = obj
  · obtain ⟨e, he, rfl⟩ := hex
    have hrk : readKind (pinned X.env w c.unsigned.pins) e.1 kindObject = .ok cell := by
      obtain ⟨q, hq, hqe⟩ := hpins e he
      have hany : (c.unsigned.pins.any fun p => decide (p.1 = e.1)) = true :=
        List.any_eq_true.mpr ⟨q, hq, by simpa using hqe⟩
      simp [readKind, pinned, hany, hl, hk]
    -- the act the turn's derivation leaves at the object, and the keys it can reach
    obtain ⟨ops, hmem, hlaw, hprog⟩ : ∃ ops : List Op,
        (e.1, if ops.isEmpty then Act.keep else .write ops) ∈ R.1.effects ∧ (∀ o ∈ ops, lawBase ≤ o.key) ∧
          (cell.slots.get slotPackage ≠ none → ∀ o ∈ ops, stateBase ≤ o.key) := by
      have hsl : lawBase ≤ stateBase := by simp [lawBase, stateBase]
      rcases effect_at_object hR he hrk with ⟨edits, via, hb⟩ | ⟨laws', via, hb⟩ |
          ⟨n, wk, a, method, args, budget, via, hd⟩
      · rw [hb] at hR
        obtain ⟨cell₀, -, -, hko, -, -, -, -, hdeq⟩ := write_judged (stepped_draft hR)
        rw [hrk] at hko; cases hko
        have hst : ∀ o ∈ diffOps (stateOf cell) (applyEdits (stateOf cell) edits), stateBase ≤ o.key :=
          diffOps_lower (fun p hp => stateOf_keys (cell := cell) hp)
            (applyEdits_keys edits (fun p hp => stateOf_keys (cell := cell) hp))
        refine ⟨diffOps (stateOf cell) (applyEdits (stateOf cell) edits), by rw [hdeq]; simp [writeOf],
          fun o ho => Nat.le_trans hsl (hst o ho), fun _ => hst⟩
      · rw [hb] at hR
        obtain ⟨cell₀, -, -, hko, hp, -, -, -, -, -, hef⟩ := law_judged (stepped_draft hR)
        rw [hrk] at hko; cases hko
        refine ⟨diffOps (lawSlotsOf cell) (lawSlots X laws'), by rw [hef]; simp [writeOf],
          diffOps_lower (fun p hp => lawSlotsOf_keys hp) (fun p hp => lawSlots_keys hp),
          fun hne => absurd (packageOf_none hp) hne⟩
      · obtain ⟨r', hr', l₁, l₂, hl₁⟩ := dispatched_ok hR hd
        simp only [dispatch] at hr'
        obtain ⟨-, cell₀, p, rq, s, calls, rows, used, hir, -, -, -, -, hst, -, hdc⟩ := invoke_ok hr'
        have hl₀ := invokeRun_live hir
        rw [hl] at hl₀; cases hl₀
        unfold deriveCalls at hdc
        obtain ⟨l, hl'⟩ := foldCalls_effects _ _ hdc
        have hkeys := diffOps_lower (fun p hp => stateOf_keys (cell := cell) hp)
          (checkStateFrom_keys (lo := stateBase) hst)
        refine ⟨diffOps (stateOf cell) s, ?_, fun o ho => Nat.le_trans hsl (hkeys o ho), fun _ => hkeys⟩
        rw [hl₁, hl']
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_append_left
        exact List.mem_cons_self ..
    have hnd : (R.1.effects.map Prod.fst).Nodup := firstDup_none (sealTurn_firstDup hs)
    have hall : ∀ x ∈ t.touches, x.cell = e.1 → x.act = if ops.isEmpty then .keep else .write ops := by
      intro x hx hxc
      rw [htouch] at hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc]
      exact actFor_of_nodup hnd hmem
    have hex : ∃ x ∈ t.touches, x.cell = e.1 := by
      obtain ⟨q, hq, hqc⟩ := hpins _ hmem
      rw [htouch]
      exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, hqc⟩
    obtain ⟨cell', hl', hk', hget⟩ := admit_writeOf_slots ha hl hall hex
    refine ⟨cell', hl', hk'.trans hk, fun k hlt => hget k (fun o ho he => ?_),
      fun hne k hlt => hget k (fun o ho he => ?_)⟩
    · have := hlaw o ho; omega
    · have := hprog hne o ho; omega
  · have hkeep : ∀ x ∈ t.touches, x.cell = obj → x.act = .keep := by
      intro x hx hxc
      rw [htouch] at hx
      obtain ⟨q', -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc]
      exact actFor_none (fun e he he' => hex ⟨e, he, he'⟩)
    obtain ⟨posts, hk', -⟩ := admit_ok ha
    have hframe := admit_frame ha hkeep (live_not_created hk' hl)
    refine ⟨cell, ?_, hk, fun _ _ => rfl, fun _ _ _ => rfl⟩
    unfold World.live; rw [hframe]; exact hl

/-- **`submit` keeps an object's head**: `turn_object_head` of the Host's decision. -/
theorem submit_object_head [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {obj : D} {cell : Cell}
    (h : submit X w c = .ok (t, w')) (hl : w.live X.env obj = some cell) (hk : cell.kind = kindObject) :
    ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
      (∀ k, k < lawBase → cell'.slots.get k = cell.slots.get k) ∧
      (cell.slots.get slotPackage ≠ none → ∀ k, k < stateBase → cell'.slots.get k = cell.slots.get k) :=
  have hs := submit_ok h
  turn_object_head hs.2.1 hs.2.2 hl hk

/-! ## The follower's fold -/

/-- One honest step (a Turn `receive` derives from its own event, or a re-judged refusal) keeps an
object's head. -/
theorem step_object_head [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D}
    {s : Step D} {obj : D} {cell : Cell}
    (hs : World.step X.env w s = .ok w') (hh : Honest X w [s]) (hl : w.live X.env obj = some cell)
    (hk : cell.kind = kindObject) :
    ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
      (∀ k, k < lawBase → cell'.slots.get k = cell.slots.get k) ∧
      (cell.slots.get slotPackage ≠ none → ∀ k, k < stateBase → cell'.slots.get k = cell.slots.get k) := by
  cases s with
  | refusal r =>
      have hrf : World.refuse X.env w r = .ok w' := hs
      exact ⟨cell, (refuse_live hrf obj).trans hl, hk, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | turn t =>
      obtain ⟨c, -, hc, -⟩ := hh
      exact turn_object_head hc hs hl hk

/-- **THE FOLD: an object's head is fixed along every honest folded log.** For any log the follower
takes from `w` to `w'` (every Turn what `receive` derives from its own event, every refusal
re-judged: `Honest`), an object live in `w` is live in `w'`, an object, with the package and owner
slots it had in `w`; and an object that had a package in `w` has, in `w'`, every slot below
`stateBase` (package, owner, laws) it had. -/
theorem honest_object_head [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {obj : D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold X.env w l = .ok w' → Honest X w l →
      ∀ {cell : Cell}, w.live X.env obj = some cell → cell.kind = kindObject →
        ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
          (∀ k, k < lawBase → cell'.slots.get k = cell.slots.get k) ∧
          (cell.slots.get slotPackage ≠ none → ∀ k, k < stateBase → cell'.slots.get k = cell.slots.get k)
  | w, w', [], hf, _, cell, hl, hk => by
      simp only [World.fold, Except.ok.injEq] at hf
      subst hf
      exact ⟨cell, hl, hk, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | w, w', s :: rest, hf, hh, cell, hl, hk => by
      obtain ⟨w₁, hs, h1, hfr, hhr⟩ := fold_honest_cons hf hh
      obtain ⟨cell₁, hl₁, hk₁, hlo₁, hst₁⟩ := step_object_head hs h1 hl hk
      obtain ⟨cell₂, hl₂, hk₂, hlo₂, hst₂⟩ := honest_object_head hfr hhr hl₁ hk₁
      refine ⟨cell₂, hl₂, hk₂, fun k hlt => (hlo₂ k hlt).trans (hlo₁ k hlt), fun hne k hlt => ?_⟩
      have hne₁ : cell₁.slots.get slotPackage ≠ none := by
        rw [hlo₁ slotPackage (by simp [slotPackage, lawBase])]; exact hne
      exact (hst₂ hne₁ k hlt).trans (hst₁ hne k hlt)

/-- **A live object's package is fixed under the follower's fold** (HOSTING-42's trigger (ii)): at
every World an honest log folds to from `w` (every log the follower takes), an object live in `w` is
live, with the same `slotPackage` bytes and so the same `packageOf` (the same package id, or the same
data object, or the same malformed-slot refusal). Over a log that is not `Honest` the fact is not
claimed. -/
theorem fold_package_fixed [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {obj : D} {w w' : World D}
    {l : List (Step D)} {cell : Cell}
    (h : World.fold X.env w l = .ok w') (hh : Honest X w l) (hl : w.live X.env obj = some cell)
    (hk : cell.kind = kindObject) :
    ∃ cell', w'.live X.env obj = some cell' ∧ cell'.kind = kindObject ∧
      cell'.slots.get slotPackage = cell.slots.get slotPackage ∧ packageOf X obj cell' = packageOf X obj cell := by
  obtain ⟨cell', hl', hk', hlo, -⟩ := honest_object_head h hh hl hk
  have hp := hlo slotPackage (by simp [slotPackage, lawBase])
  refine ⟨cell', hl', hk', hp, ?_⟩
  unfold packageOf
  rw [hp]


end Nanodregg.Kernel.Receive
