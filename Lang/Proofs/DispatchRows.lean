/-
# Lang.Proofs.DispatchRows — the row acts of a dispatched invoke are touches of the sealed Turn

Facts about the kernel's definitions, proved from outside it (PROT-6's `fuse_atomic` rests on them):

* `dispatched_ok_rows`: the ROWS analogue of `Kernel.Receive.dispatched_ok`: every receiver the walk
  dispatched succeeded, and its Draft's rows sit inside the signed derivation's Draft rows
  (`callStep` concatenates them by `Draft.append`).
* `rowTouchesOf_covers`: every row effect `rowTouchesOf` seals is a row touch carrying its act: a
  pinned slot's touch carries `rowActFor`, which is the effect's act because `dupBy` found no second
  effect at the slot; an unpinned effect is carried as it is.
* `dispatched_invoke_rows`: so every row act a dispatched invoke's run returned is a touch of the
  Turn `receive` sealed, and each is under the invoked object.
* `dispatched_invoke_children`: each call the run of a dispatched invoke at level `m + 1` returned
  was dispatched, as the invoked object, at level `m`; `dispatched_signed_children`: the signed
  invoke's children live at `Bounds.callDepthMax - 1`.
* `invokeRun_ok`, `invokeRun_req`, `invokeRun_pkg`: what `invokeRun` hands the run: the cell it read
  as an object, the package its package slot names (the live cell's, `invokeRun_pkg`), and a request
  whose `self` is the invoked object.
-/
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.Rows

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

-- as in `Kernel.Proofs.Rows`: whnf of a statement about `rowPath` would build its whole list
attribute [local irreducible] rowPath

/-! ## The calls' fold concatenates rows -/

omit [Ord D] [DecidableEq D] in
private theorem foldCalls_rows {sub : Receive.Sub D} {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D},
      calls.foldlM (callStep sub obj) acc = .ok r → ∃ l, r.1.rows = acc.1.rows ++ l
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
      obtain ⟨l, hl⟩ := foldCalls_rows rest _ h
      exact ⟨q.1.rows ++ l, by rw [hl]; simp [Draft.append]⟩

omit [Ord D] [DecidableEq D] in
/-- The whole fold, split at the `i`-th call: its derivation succeeded, and its rows sit inside. -/
private theorem foldCalls_split_rows {sub : Receive.Sub D} {obj : D} {calls : List (Body D)} {i : Nat}
    (hi : i < calls.length) {a0 acc r : Draft D × Walk D}
    (hall : calls.foldlM (callStep sub obj) a0 = .ok r)
    (hpre : (calls.take i).foldlM (callStep sub obj) a0 = .ok acc) :
    ∃ q, sub acc.2 obj calls[i] = .ok q ∧ ∃ l, r.1.rows = acc.1.rows ++ q.1.rows ++ l := by
  have hsplit : calls = calls.take i ++ calls[i] :: calls.drop (i + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  rw [hsplit, List.foldlM_append, hpre] at hall
  simp only [bind, Except.bind, List.foldlM_cons] at hall
  cases hq' : callStep sub obj acc calls[i] with
  | error e => rw [hq'] at hall; cases hall
  | ok q' =>
      rw [hq'] at hall
      obtain ⟨q, hq, rfl⟩ := callStep_ok hq'
      obtain ⟨l, hl⟩ := foldCalls_rows _ _ hall
      exact ⟨q, hq, l, by rw [hl]; simp [Draft.append]⟩

omit [Ord D] [DecidableEq D] in
/-- A fold that succeeded succeeded on every prefix. -/
private theorem foldCalls_take_ok {sub : Receive.Sub D} {obj : D} {calls : List (Body D)} (i : Nat)
    {a0 r : Draft D × Walk D} (h : calls.foldlM (callStep sub obj) a0 = .ok r) :
    ∃ acc, (calls.take i).foldlM (callStep sub obj) a0 = .ok acc := by
  rw [← List.take_append_drop i calls, List.foldlM_append] at h
  obtain ⟨acc, ha, -⟩ := except_bind_ok.mp h
  exact ⟨acc, ha⟩

/-! ## A dispatched receiver's rows sit inside the signed call's -/

/-- **The rows analogue of `dispatched_ok`.** Every receiver the walk dispatched succeeded, and its
Draft's rows sit inside the signed call's Draft's rows. -/
theorem dispatched_ok_rows {X : Ctx D} {w : World D} {c : Call D} {R : Draft D × Walk D}
    (hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok R)
    {n : Nat} {wk : Walk D} {a : D} {b : Body D} (hd : Dispatched X w c n wk a b) :
    ∃ r, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r ∧
      ∃ l₁ l₂, R.1.rows = l₁ ++ r.1.rows ++ l₂ := by
  induction hd with
  | root => exact ⟨R, hR, [], [], by simp⟩
  | @call m wk actor obj method args budget via r cell p rq new calls rows used acc i hi _ hok hir hrun hpre ih =>
      obtain ⟨rp, hp, l₁, l₂, hl⟩ := ih
      have hp' := hp
      simp only [dispatch] at hp'
      rw [hok] at hp'
      cases hp'
      obtain ⟨-, cell', p', rq', new', calls', rows', used', hir', hrun', -, -, -, -, -, hd'⟩ := invoke_ok hok
      rw [hir] at hir'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hir'
      obtain ⟨rfl, rfl, rfl⟩ := hir'
      rw [hrun] at hrun'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hrun'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hrun'
      unfold deriveCalls at hd'
      obtain ⟨q, hq, l, hl'⟩ := foldCalls_split_rows hi hd' hpre
      obtain ⟨m', hm, -, hq'⟩ := effect_as_signed hq
      obtain rfl := Nat.succ.inj hm.symm
      refine ⟨q, hq', l₁ ++ acc.1.rows, l ++ l₂, ?_⟩
      rw [hl, hl']
      simp

/-! ## The seal carries every row effect -/

/-- The sealed Turn's rows are `rowTouchesOf` the caller's row pins and the Draft's rows. -/
theorem sealTurn_rows {X : Ctx D} {c : Call D} {cr : List (D × Cell)} {efs : List (D × Act)}
    {ns : List D} {rs : List (RowSlot D × RowAct)} {t : Turn D} {k : Nat} (h : sealTurn X c cr efs ns rs k = .ok t) :
    rowTouchesOf c.unsigned.rowPins rs = .ok t.rows := by
  unfold sealTurn at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, rts, hr, h⟩ := h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hr
  · simp at h

omit [Ord D] [DecidableEq D] in
/-- `dupBy` finding nothing means no element occurs twice. -/
theorem dupBy_none {α : Type} [DecidableEq α] : ∀ {l : List α}, dupBy l = none → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
      unfold dupBy at h
      split at h
      · cases h
      · rename_i hx
        exact List.nodup_cons.mpr ⟨fun hm => hx (by simpa using hm), dupBy_none h⟩

omit [Ord D] in
/-- Over row effects at distinct slots, the act `rowActFor` finds at a slot is the one effect there. -/
theorem rowActFor_of_nodup {s : RowSlot D} {a : RowAct} :
    ∀ {l : List (RowSlot D × RowAct)}, (l.map Prod.fst).Nodup → (s, a) ∈ l → rowActFor l s = a
  | [], _, h => by simp at h
  | q :: rest, hn, h => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with rfl | h
      · simp [rowActFor, List.find?]
      · have hne : ¬ q.1 = s := fun he => hn.1 (by rw [he]; exact List.mem_map_of_mem h)
        have hf : (q :: rest).find? (fun e => decide (e.1 = s)) = rest.find? (fun e => decide (e.1 = s)) :=
          List.find?_cons_of_neg (by simpa using hne)
        have ih := rowActFor_of_nodup hn.2 h
        unfold rowActFor at ih ⊢
        rw [hf]
        exact ih

/-- **Every row effect is a row touch with its act.** A pinned slot's touch carries `rowActFor`,
the effect's own act since `dupBy` found no second effect at the slot; an unpinned effect is
carried as it is. -/
theorem rowTouchesOf_covers {pins : List (RowSlot D × D)} {rows : List (RowSlot D × RowAct)}
    {rts : List (RowTouch D)} (h : rowTouchesOf pins rows = .ok rts) :
    ∀ e ∈ rows, ∃ τ ∈ rts, τ.slot = e.1 ∧ τ.act = e.2 := by
  unfold rowTouchesOf at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, -, h⟩ := h
  cases hd : dupBy (rows.map Prod.fst) with
  | some s => rw [hd] at h; cases h
  | none =>
  have hnd := dupBy_none hd
  rw [hd] at h
  simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
  subst h
  rintro ⟨s, a⟩ he
  by_cases hp : (pins.any fun p => decide (p.1 = s)) = true
  · obtain ⟨p, hpm, hpe⟩ := List.any_eq_true.mp hp
    have hps : p.1 = s := of_decide_eq_true hpe
    refine ⟨{ slot := p.1, seen := some p.2, act := rowActFor rows p.1 },
      List.mem_append_left _ (List.mem_map.mpr ⟨p, hpm, rfl⟩), hps, ?_⟩
    show rowActFor rows p.1 = a
    rw [hps]
    exact rowActFor_of_nodup hnd he
  · refine ⟨{ slot := s, seen := none, act := a }, List.mem_append_right _ (List.mem_map.mpr ⟨(s, a),
      List.mem_filter.mpr ⟨he, ?_⟩, rfl⟩), rfl, rfl⟩
    show (!(pins.any fun p => decide (p.1 = s))) = true
    cases hb : pins.any (fun p => decide (p.1 = s)) with
    | false => rfl
    | true => exact absurd hb hp

/-! ## The theorems -/

/-- **The row acts of a dispatched invoke are touches of the sealed Turn.** A signed call `receive`
turned into `t`, and an invoke of `obj` its walk dispatched (at any level; the signed invoke itself
is `dispatched_of_signed`): that invoke's `invokeRun`, its run at the fuel the walk gave it, every
row effect the run returned is a touch of `t.rows` with the same slot and act, and is under `obj`. -/
theorem dispatched_invoke_rows {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {n : Nat}
    {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    (hc : receive X w c = .ok t) (hd : Dispatched X w c n wk actor (.invoke obj method args budget via)) :
    ∃ (cell : Cell) (p : D) (rq : Req D) (new : Slots) (calls : List (Body D))
      (rows : List (RowSlot D × RowAct)) (used : Nat),
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, rq) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args rq (min budget wk.pool) = .ok (new, calls, rows, used) ∧
      (∀ e ∈ rows, e.1.under.1 = obj) ∧
      ∀ e ∈ rows, ∃ τ ∈ t.rows, τ.slot = e.1 ∧ τ.act = e.2 := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, _k, hd', hs⟩ := receiveWith_sealed hw
  replace hd' := derive_of_withTicks hd'
  rw [derive_eq] at hd'
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd'; cases hd'
  | ok R =>
  rw [hR] at hd'
  simp only [Except.map, Except.ok.injEq] at hd'
  subst hd'
  obtain ⟨r', hr', l₁, l₂, hl⟩ := dispatched_ok_rows hR hd
  simp only [dispatch] at hr'
  obtain ⟨-, cell, p, rq, new, calls, rows, used, hir, hrun, -, hunder, -, -, -, hdc⟩ := invoke_ok hr'
  unfold deriveCalls at hdc
  obtain ⟨l, hl'⟩ := foldCalls_rows calls (⟨[], writeOf obj (diffOps (stateOf cell) new), [], rows⟩,
    { wk with visited := obj :: wk.visited, pool := wk.pool - used }) hdc
  refine ⟨cell, p, rq, new, calls, rows, used, hir, hrun, hunder,
    fun e he => rowTouchesOf_covers (sealTurn_rows hs) e ?_⟩
  rw [hl, hl']
  simp [he]

/-- **Each call a dispatched invoke's run returned was dispatched**, as the invoked object, one
level down. The invoke at level `m + 1` (at level 0 its deriver refuses every call, `callTooDeep`). -/
theorem dispatched_invoke_children {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {m : Nat}
    {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    (hc : receive X w c = .ok t)
    (hd : Dispatched X w c (m + 1) wk actor (.invoke obj method args budget via))
    {cell : Cell} {p : D} {rq : Req D} {new : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hir : invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, rq))
    (hrun : X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args rq (min budget wk.pool) = .ok (new, calls, rows, used)) :
    ∀ i (hi : i < calls.length), ∃ wk', Dispatched X w c m wk' obj calls[i] := by
  intro i hi
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, _k, hd', -⟩ := receiveWith_sealed hw
  replace hd' := derive_of_withTicks hd'
  rw [derive_eq] at hd'
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd'; cases hd'
  | ok R =>
  obtain ⟨r, hr, -⟩ := dispatched_ok_rows hR hd
  simp only [dispatch] at hr
  obtain ⟨-, cell', p', rq', new', calls', rows', used', hir', hrun', -, -, -, -, -, hdc⟩ := invoke_ok hr
  rw [hir] at hir'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hir'
  obtain ⟨rfl, rfl, rfl⟩ := hir'
  rw [hrun] at hrun'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hrun'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hrun'
  unfold deriveCalls at hdc
  obtain ⟨acc, hpre⟩ := foldCalls_take_ok i hdc
  exact ⟨acc.2, Dispatched.call i hi hd hr hir hrun hpre⟩

/-- **The signed invoke's children** live at `Bounds.callDepthMax - 1`: each call its run returned
was dispatched there, as the signed invoke's object. -/
theorem dispatched_signed_children {X : Ctx D} {w : World D} {c : Call D} {t : Turn D} {obj : D}
    {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    (hc : receive X w c = .ok t) (hb : c.unsigned.body = .invoke obj method args budget via)
    {cell : Cell} {p : D} {rq : Req D} {new : Slots} {calls : List (Body D)}
    {rows : List (RowSlot D × RowAct)} {used : Nat}
    (hir : invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, rq))
    (hrun : X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args rq (min budget (poolOf c.unsigned.body)) = .ok (new, calls, rows, used)) :
    ∀ i (hi : i < calls.length), ∃ wk', Dispatched X w c (Bounds.callDepthMax - 1) wk' obj calls[i] :=
  dispatched_invoke_children (m := Bounds.callDepthMax - 1) hc (dispatched_of_signed hb) hir hrun

omit [Ord D] in
/-- **What `invokeRun` hands the run**: the cell it read as an object, the package its package
slot names, and the request of the owner authority's principal, with the invoked object as `self`
and the invoke of `method` as its occasion. -/
theorem invokeRun_ok {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {rq : Req D}
    (h : invokeRun X look c actor obj method via = .ok (cell, p, rq)) :
    readKind look obj kindObject = .ok cell ∧ packageOf X obj cell = .ok (some p) ∧
      ∃ principal, ownerAuthority X look actor obj cell (.invoke method) via = .ok principal ∧
        rq = reqOf c.unsigned obj principal (.invoke method) := by
  unfold invokeRun at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', hk, pkg, hpk, p', hp, pr, hpr, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases pkg with
  | none => simp [requireMethods] at hp
  | some q =>
      simp only [requireMethods, Except.ok.injEq] at hp
      subst hp
      exact ⟨hk, hpk, pr, hpr, rfl⟩

omit [Ord D] in
/-- **The run's `self` is the invoked object**, its occasion the invoke of `method`, its agent the
signer. -/
theorem invokeRun_req {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {rq : Req D}
    (h : invokeRun X look c actor obj method via = .ok (cell, p, rq)) :
    rq.self = obj ∧ rq.occasion = .invoke method ∧ rq.agent = c.unsigned.member := by
  obtain ⟨-, -, pr, -, rfl⟩ := invokeRun_ok h
  exact ⟨rfl, rfl, rfl⟩

/-- **An invoke of an object whose live cell names package `pkg` runs `pkg`.** -/
theorem invokeRun_pkg {X : Ctx D} {w : World D} {pins : List (D × D)} {c : Call D} {actor obj : D}
    {method : Nat} {via : Option D} {cell : Cell} {p : D} {rq : Req D} {pkg : D}
    (h : invokeRun X (pinned X.env w pins) c actor obj method via = .ok (cell, p, rq))
    (ho : ∃ cl, w.live X.env obj = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hk : X.digestOf (X.env.bytes pkg) = some pkg) : p = pkg := by
  obtain ⟨hrk, hpk, -⟩ := invokeRun_ok h
  have hl := (readKind_pinned hrk).1
  obtain ⟨cl, hcl, hsl⟩ := ho
  rw [hl] at hcl
  cases hcl
  unfold packageOf at hpk
  rw [hsl] at hpk
  simp only [hk, Except.ok.injEq, Option.some.injEq] at hpk
  exact hpk.symm

end Nanodregg.Lang
