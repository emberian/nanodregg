/-
# Kernel.Proofs.InvokeTree — the next run of an object invoked anywhere in a call's tree

`Kernel.Proofs.InvokeNext` links the runs of an object a SIGNED call invokes. An object may also be
invoked by another object's run (KERNEL-28: a run's calls are derived as the object, through `tree`),
and LEDGER's escrows are (`Ledger.Proofs.EscrowRun`'s `Runs` over an object another object calls).
Proved here, of the same definitions:

* `Invoked X w c obj`: `obj` is invoked somewhere in `c`'s tree on `w`: the walk `derive` runs
  (`dispatch` of the signed Body under `tree`, from the empty walk) succeeds and visits it. The signed
  invoke's own object is one case (`visit_distinct`).
* `invoke_tree_slots`: a signed call derived from `w` and admitted to `w'`, whose tree invoked `obj`:
  there is a judged run of `obj`'s program on its pre-state (an `invokeRun` through the caller's pins,
  an `X.program.run`, the laws in force by `lawsOf` and their judgement) whose result the committed
  state of `obj` in `w'` reads at every key. The proof takes the tree's own run, but the actor,
  method, arguments, fuel and returned calls are existentials, NOT pinned to the invoke the walk made
  (cv 01a15554-cffd: the walk-record form). `invoke_tree_run`: so every next invoke of `obj` on `w'` runs on them.

Where the top-level proof reads the act at `obj` off the Draft's first effect, a nested run's write
sits after its caller's. This proof takes the act at `obj` to be this run's through `sealTurn`'s
`duplicateEffect` check: `firstDup` over the effects' cells found none, and `firstDup` walks a
`TreeSet compare`, so it is the lawful order (`Std.TransOrd`, `Std.LawfulEqOrd`) that makes the
CHECK's "found none" mean "none there" (`firstDup_none`). The order laws are the price of this route,
not shown necessary for the statement: a second invoke of the same object is refused `revisited`
independently (`List.contains`, no order), and a counterexample to the theorem would need a non-invoke
effect at an object cell, which no callable receiver emits (not proved here). The deployed `Digest`
has both laws (`Codec.Proofs.Digest`); a consumer at a generic `D` (LEDGER) carries them. The
top-level theorems keep their order-free form. Tooth: `effectsPinned_unlawful_ord` (the check, under
an order that says `lt` of everything, passes two effects at one cell; the real order refuses them).
-/
import Kernel.Proofs.InvokeNext

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **`obj` is invoked in `c`'s tree on `w`**: the walk `derive` runs visits it. -/
def Invoked (X : Ctx D) (w : World D) (c : Call D) (obj : D) : Prop :=
  ∃ r, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok r ∧ obj ∈ r.2.visited

/-! ## A visited object was run, and its write is among the effects -/

/-- The run of `obj` a derivation made: what `invoke` checked of it, and its own act among `efs`. -/
private def Ran (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (obj : D) (efs : List (D × Act)) :
    Prop :=
  ∃ (actor : D) (method : Nat) (args : ByteArray) (fuel : Nat) (via : Option D) (cell : Cell) (p : D)
    (rq : Req D) (s : Slots) (calls : List (Body D)) (rows : List (RowSlot D × RowAct)) (used : Nat)
    (laws : List D),
    invokeRun X look c actor obj method via = .ok (cell, p, rq) ∧
    X.program.run look rv p (stateOf cell) method args rq fuel = .ok (s, calls, rows, used) ∧
    checkState (D := D) s = .ok () ∧
    lawsOf X obj cell = .ok laws ∧
    X.program.judge look (some p) laws (stateOf cell) s rq = .ok () ∧
    (obj, if (diffOps (stateOf cell) s).isEmpty then Act.keep else .write (diffOps (stateOf cell) s)) ∈ efs

omit [Ord D] in
private theorem Ran.append_right {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {obj : D}
    {efs l : List (D × Act)} (h : Ran X look rv c obj efs) : Ran X look rv c obj (efs ++ l) := by
  obtain ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, h1, h2, h3, h4, h4', h5⟩ := h
  exact ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, h1, h2, h3, h4, h4',
    List.mem_append_left _ h5⟩

omit [Ord D] in
private theorem Ran.append_left {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {obj : D}
    {efs l : List (D × Act)} (h : Ran X look rv c obj efs) : Ran X look rv c obj (l ++ efs) := by
  obtain ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, h1, h2, h3, h4, h4', h5⟩ := h
  exact ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, h1, h2, h3, h4, h4',
    List.mem_append_right _ h5⟩

omit [Ord D] [DecidableEq D] in
private theorem foldCalls_effects {sub : Sub D} {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D},
      calls.foldlM (callStep sub obj) acc = .ok r → ∃ l, r.1.effects = acc.1.effects ++ l
  | [], acc, r, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨[], by simp⟩
  | b :: rest, acc, r, h => by
      rw [List.foldlM_cons] at h
      simp only [except_bind_ok] at h
      obtain ⟨s, hs1, h⟩ := h
      unfold callStep at hs1
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hs1
      obtain ⟨q, -, rfl⟩ := hs1
      obtain ⟨l, hl⟩ := foldCalls_effects rest _ h
      exact ⟨q.1.effects ++ l, by rw [hl]; simp [Draft.append]⟩

/-- What a derivation says of the objects its walk visits: each was visited before, or was run
here and its act is among the effects. -/
private def Visits (X : Ctx D) (look : Pinned D) (rv : RowView D) (c : Call D) (wk : Walk D)
    (r : Draft D × Walk D) : Prop :=
  ∀ o ∈ r.2.visited, o ∈ wk.visited ∨ Ran X look rv c o r.1.effects

omit [Ord D] in
private theorem foldCalls_visits {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → Visits X look rv c wk r) {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D},
      calls.foldlM (callStep sub obj) acc = .ok r → Visits X look rv c acc.2 r
  | [], acc, r, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact fun o ho => .inl ho
  | b :: rest, acc, r, h => by
      rw [List.foldlM_cons] at h
      simp only [except_bind_ok] at h
      obtain ⟨s, hs1, h⟩ := h
      unfold callStep at hs1
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hs1
      obtain ⟨q, hq, rfl⟩ := hs1
      obtain ⟨l, hl⟩ := foldCalls_effects rest _ h
      intro o ho
      rcases foldCalls_visits hs rest _ h o ho with ho' | hr
      · rcases hs _ _ _ _ hq o ho' with ho'' | hr
        · exact .inl ho''
        · right
          rw [hl]
          exact (Ran.append_left (l := acc.1.effects) hr).append_right
      · exact .inr hr

omit [Ord D] in
private theorem invoke_visits {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → Visits X look rv c wk r) {wk : Walk D} {actor obj : D}
    {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D} {r : Draft D × Walk D}
    (h : invoke X look rv c sub wk actor obj method args budget via = .ok r) : Visits X look rv c wk r := by
  obtain ⟨-, cell, p, rq, new, calls, rows, used, hir, hrun, -, -, -, hst, ⟨laws, hlw, hj⟩, hd⟩ := invoke_ok h
  unfold deriveCalls at hd
  obtain ⟨l, hl⟩ := foldCalls_effects _ _ hd
  intro o ho
  rcases foldCalls_visits hs _ _ hd o ho with ho' | hr
  · simp only [List.mem_cons] at ho'
    rcases ho' with rfl | ho'
    · right
      refine ⟨actor, method, args, min budget wk.pool, via, cell, p, rq, new, calls, rows, used, laws, hir, hrun,
        hst, hlw, hj, ?_⟩
      rw [hl]
      simp [writeOf]
    · exact .inl ho'
  · exact .inr hr

omit [Ord D] in
private theorem dispatch_visits {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → Visits X look rv c wk r) {wk : Walk D} {actor : D} {b : Body D}
    {r : Draft D × Walk D} (h : dispatch X look rv c sub wk actor b = .ok r) : Visits X look rv c wk r := by
  cases b with
  | invoke obj method args budget via => exact invoke_visits hs h
  | _ =>
      simp only [dispatch] at h
      obtain ⟨hv, -⟩ := stepped_walk h
      intro o ho
      rw [hv] at ho
      exact .inl ho

omit [Ord D] in
private theorem tree_visits {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} :
    ∀ n wk a b r, tree X look rv c n wk a b = .ok r → Visits X look rv c wk r
  | 0, _, _, _, _, h => by simp [tree] at h
  | n + 1, wk, a, b, r, h => by
      obtain ⟨m, hm, -, hd⟩ := effect_as_signed h
      have : m = n := by omega
      subst this
      exact dispatch_visits (tree_visits m) hd

/-! ## The one effect at a cell -/

/-- A sealed Turn's effects name distinct cells, as `firstDup` saw it (`duplicateEffect`). -/
private theorem sealTurn_firstDup {X : Ctx D} {c : Call D} {cr : List (D × Cell)} {efs : List (D × Act)}
    {ns : List D} {rs : List (RowSlot D × RowAct)} {t : Turn D} (h : sealTurn X c cr efs ns rs = .ok t) :
    firstDup (efs.map Prod.fst) = none := by
  unfold sealTurn at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hp, -⟩ := h
  unfold effectsPinned at hp
  simp only [except_bind_ok] at hp
  obtain ⟨⟨⟩, -, hp⟩ := hp
  split at hp
  · assumption
  · cases hp

omit [Ord D] in
/-- Over effects at distinct cells, the act `actFor` finds at a cell is the one effect there. -/
private theorem actFor_of_nodup {obj : D} {a : Act} :
    ∀ {l : List (D × Act)}, (l.map Prod.fst).Nodup → (obj, a) ∈ l → actFor l obj = a
  | [], _, h => by simp at h
  | q :: rest, hn, h => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with rfl | h
      · simp [actFor, List.find?]
      · have hne : ¬ q.1 = obj := fun he => hn.1 (by rw [he]; exact List.mem_map_of_mem h)
        have hf : (q :: rest).find? (fun e => decide (e.1 = obj)) = rest.find? (fun e => decide (e.1 = obj)) :=
          List.find?_cons_of_neg (by simpa using hne)
        have ih := actFor_of_nodup hn.2 h
        unfold actFor at ih ⊢
        rw [hf]
        exact ih

/-! ## The theorems -/

/-- **An object invoked anywhere in an admitted call's tree is handed what a judged run returned.**
A signed call derived from `w` and admitted to `w'`, whose tree invoked `obj` (`Invoked`): there is a
judged run of `obj`'s program on its pre-state (an `invokeRun` through the caller's pins, an
`X.program.run`, the laws in force by `lawsOf`, their judgement) whose result the committed state
reads: `obj` is live in `w'`, and its state holds at every key what that run returned. The proof
takes the tree's own run of `obj`, but the actor, method, arguments, fuel and returned calls are
existentials, not pinned to the invoke the walk made. The order laws are the price of the proof's
route through `sealTurn`'s `duplicateEffect` check. -/
theorem invoke_tree_slots [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {obj : D}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hi : Invoked X w c obj) :
    ∃ (actor : D) (method : Nat) (args : ByteArray) (fuel : Nat) (via : Option D) (cell : Cell) (p : D)
      (r : Req D) (s : Slots) (calls : List (Body D)) (rows : List (RowSlot D × RowAct)) (used : Nat)
      (laws : List D),
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r fuel = .ok (s, calls, rows, used) ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) (some p) laws (stateOf cell) s r = .ok () ∧
      ∃ cell', w'.live X.env obj = some cell' ∧ ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, hs⟩ := receiveWith_sealed hw
  obtain ⟨r, hr, hmem⟩ := hi
  rw [derive_eq, hr] at hd
  simp only [Except.map, Except.ok.injEq] at hd
  subst hd
  have hran : Ran X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c obj r.1.effects := by
    rcases dispatch_visits (tree_visits _) hr obj hmem with h | h
    · simp at h
    · exact h
  obtain ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, hir, hrun, hst, hl, hj, hin⟩ := hran
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  have hnd : (r.1.effects.map Prod.fst).Nodup := firstDup_none (sealTurn_firstDup hs)
  have hact : ∀ x ∈ t.touches, x.cell = obj →
      x.act = if (diffOps (stateOf cell) s).isEmpty then .keep else .write (diffOps (stateOf cell) s) := by
    intro x hx hxc
    rw [htouch] at hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
    simp only at hxc ⊢
    rw [hxc]
    exact actFor_of_nodup hnd hin
  have hex : ∃ x ∈ t.touches, x.cell = obj := by
    obtain ⟨q, hq, hqc⟩ := hpins _ hin
    rw [htouch]
    exact ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, hqc⟩
  have hlive := invokeRun_live hir
  refine ⟨actor, method, args, fuel, via, cell, p, rq, s, calls, rows, used, laws, hir, hrun, hl, hj, ?_⟩
  by_cases he : (diffOps (stateOf cell) s).isEmpty = true
  · have hnil : diffOps (stateOf cell) s = [] := List.isEmpty_iff.mp he
    refine ⟨cell, ?_, fun k => ?_⟩
    · obtain ⟨posts, hk, -⟩ := admit_ok ha
      have hframe := admit_frame (c := obj) ha
        (fun x hx hxc => by rw [hact x hx hxc, if_pos he])
        (live_not_created hk hlive)
      unfold World.live; rw [hframe]; exact hlive
    · have := diffOps_next (D := D) hst (by rw [hnil]; exact List.nodup_nil) k
      rwa [hnil] at this
  · obtain ⟨hlive', hn⟩ := admit_live_write ha hlive hex
      (fun x hx hxc => by rw [hact x hx hxc, if_neg he])
    exact ⟨_, hlive', diffOps_next hst hn⟩

/-- **The state the next invoke of a tree-invoked object is handed** (`Runs`' link for an object
another object calls, LEDGER-14): after the admission of `invoke_tree_slots`, every invoke of `obj`
derived on `w'` (any call, signer, method and pins) runs on a state that holds, at every key, what
the tree's run of `obj` returned. -/
theorem invoke_tree_run [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {obj : D}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hi : Invoked X w c obj)
    {pins' : List (D × D)} {c' : Call D} {actor' : D} {method' : Nat} {via' : Option D}
    {cell' : Cell} {p' : D} {r' : Req D}
    (hr' : invokeRun X (pinned X.env w' pins') c' actor' obj method' via' = .ok (cell', p', r')) :
    ∃ (actor : D) (method : Nat) (args : ByteArray) (fuel : Nat) (via : Option D) (cell : Cell) (p : D)
      (r : Req D) (s : Slots) (calls : List (Body D)) (rows : List (RowSlot D × RowAct)) (used : Nat)
      (laws : List D),
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r fuel = .ok (s, calls, rows, used) ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) (some p) laws (stateOf cell) s r = .ok () ∧
      ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨actor, method, args, fuel, via, cell, p, r, s, calls, rows, used, laws, hir, hrun, hlw, hj, cell'', hl, hk⟩ :=
    invoke_tree_slots hc ha hi
  have hl' := invokeRun_live hr'
  rw [hl] at hl'
  cases hl'
  exact ⟨actor, method, args, fuel, via, cell, p, r, s, calls, rows, used, laws, hir, hrun, hlw, hj, hk⟩

/-- The signed invoke's object is `Invoked`: the top-level case is one instance of the tree form. -/
theorem invoked_of_signed {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {obj : D} {method : Nat}
    {args : ByteArray} {budget : Nat} {via : Option D}
    (hc : receive X w c = .ok t) (hb : c.unsigned.body = .invoke obj method args budget via) :
    Invoked X w c obj := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, -⟩ := receiveWith_sealed hw
  rw [derive_eq] at hd
  cases hr : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hr] at hd; cases hd
  | ok r => exact ⟨r, hr, (visit_distinct hr).2 obj method args budget via hb⟩

/-! ## Tooth: the order laws are load-bearing -/

/-- An order under which everything is `lt` of everything: `compare` never answers `eq`, so a
`TreeSet` under it never finds what it holds. -/
@[reducible] private def allLt : Ord Nat := ⟨fun _ _ => .lt⟩

private def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- Two writes at cell 5. -/
private def twoAt5 : List (Nat × Act) := [(5, .write [.set 16 ⟨#[1]⟩]), (5, .write [.set 16 ⟨#[2]⟩])]

/-- **The `duplicateEffect` check needs a lawful order.** Under `allLt`, `effectsPinned` accepts
`twoAt5` (`firstDup` found no duplicate in a `TreeSet` that cannot find anything), and the act a
Turn sealed from it carries at 5 is the FIRST write; under the real order the same effects are
refused `duplicateEffect`. This refutes the check `invoke_tree_slots`' proof leans on, not the
theorem: a second invoke of one object is refused `revisited` with no order, and no callable receiver
emits a non-invoke effect at an object cell (not proved here), so the order laws are the price of
the route through `duplicateEffect`. -/
theorem effectsPinned_unlawful_ord :
    isOk (@effectsPinned Nat allLt _ [(5, 5)] twoAt5) = true ∧
      actFor twoAt5 5 = .write [.set 16 ⟨#[1]⟩] ∧
      Act.write [.set 16 ⟨#[1]⟩] ≠ .write [.set 16 ⟨#[2]⟩] ∧
      effectsPinned [(5, 5)] twoAt5 = .error (.duplicateEffect 5) :=
  ⟨by decide +kernel, by decide, by decide, rfl⟩

end Nanodregg.Kernel.Receive
