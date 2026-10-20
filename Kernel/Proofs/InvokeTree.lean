/-
# Kernel.Proofs.InvokeTree — the next run of an object invoked anywhere in a call's tree

`Kernel.Proofs.InvokeNext` links the runs of an object a SIGNED call invokes. An object may also be
invoked by another object's run (KERNEL-28: a run's calls are derived as the object, through `tree`),
and LEDGER's escrows are (`Ledger.Proofs.EscrowRun`'s `Runs` over an object another object calls).
Proved here, of the same definitions:

* `Dispatched X w c n wk actor b`: the walk `derive` runs for `c` on `w` dispatched `b` as `actor`,
  from walk `wk`, with `n` levels of `tree` left (cv 01a15554-cffd). The signed Body is the root
  (`dispatched_of_signed` for a signed invoke), dispatched whether or not its derivation succeeds;
  each call an invoke's run returned is dispatched at the walk the calls before it left, one level
  down, and only when that invoke succeeded, so every non-root fact implies `derive` succeeded. It is the walk's own record: an invoke it holds
  names the actor, method, arguments and budget the walk ran with, so its run's returned calls are
  the ones derived.
* `Invoked X w c obj`: the walk succeeded and its visited list holds `obj`; `dispatched_of_invoked`: some dispatched
  invoke ran it.
* `invoke_tree_slots`: a signed call derived from `w` and admitted to `w'`, and an invoke of `obj`
  its walk dispatched: that invoke's `invokeRun`, its `X.program.run` at the fuel the walk gave it
  (`min budget wk.pool`), the laws in force by `lawsOf` and their judgement, and the committed state
  of `obj` in `w'` reads what the run returned at every key. `invoke_tree_run`: so every next invoke
  of `obj` on `w'` runs on it.
* THE TOTALITY (KERNEL-28): `effect_at_object`: an effect of a signed call's derivation at a cell its
  pins read as an object is the signed `write` or `law` of it, or the own write of an invoke of it the
  walk dispatched; every other receiver (enroll, rotate, grant, revoke, transfer, credit; install,
  create, issue, account have no effect) writes a cell it read as a grant, a member or an account,
  by its own `readKind` (a cell has one kind). `object_turn_cases`: so a derived and admitted turn
  keeps a live object, or is its signed write or law, or dispatched an invoke of it. Tooth
  `effect_at_object_needs_kind`: `revoke` without its kind check retires an object.

Where the top-level proof reads the act at `obj` off the Draft's first effect, a nested run's write
sits after its caller's. This proof takes the act at `obj` to be this run's through `sealTurn`'s
`duplicateEffect` check: `firstDup` over the effects' cells found none, and `firstDup` walks a
`TreeSet compare`, so it is the lawful order (`Std.TransOrd`, `Std.LawfulEqOrd`) that makes the
CHECK's "found none" mean "none there" (`firstDup_none`). The order laws are the price of this route,
not shown necessary for the statement: a second invoke of the same object is refused `revisited`
independently (`List.contains`, no order), and a counterexample to the theorem would need a non-invoke
effect at an object cell, which no callable receiver emits (`effect_at_object`). The deployed `Digest`
has both laws (`Codec.Proofs.Digest`); a consumer at a generic `D` (LEDGER) carries them. The
top-level theorems keep their order-free form. Tooth: `effectsPinned_unlawful_ord` (the check, under
an order that says `lt` of everything, passes two effects at one cell; the real order refuses them).
-/
import Kernel.Proofs.InvokeNext
import Kernel.Proofs.Authority

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **A receiver `derive`'s walk dispatched** for `c` on `w`: with `n` levels of `tree` left as its
deriver, from walk `wk`, as `actor`, the Body `b`. The signed Body at the signer, from the walk
with nothing visited, the pool `poolOf` of the signed Body and no births, at `Bounds.callDepthMax`
(`derive`; whether or not it succeeds); then, of an invoke the walk dispatched whose `invoke`
succeeded, the `i`-th call its run returned, as the invoked object, one level down, at the walk the
calls before it left (`deriveCalls`' fold over the first `i`, from the object's own Draft and the
walk past it). -/
inductive Dispatched (X : Ctx D) (w : World D) (c : Call D) : Nat → Walk D → D → Body D → Prop
  | root : Dispatched X w c Bounds.callDepthMax ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member
      c.unsigned.body
  | call {m : Nat} {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat}
      {via : Option D} {r : Draft D × Walk D} {cell : Cell} {p : D} {rq : Req D} {new : Slots}
      {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat} {acc : Draft D × Walk D}
      (i : Nat) (hi : i < calls.length) :
      Dispatched X w c (m + 1) wk actor (.invoke obj method args budget via) →
      invoke X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
          (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c (m + 1))
          wk actor obj method args budget via = .ok r →
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, rq) →
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell) method
          args rq (min budget wk.pool) = .ok (new, calls, rows, used) →
      (calls.take i).foldlM
          (callStep (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c (m + 1)) obj)
          (⟨[], writeOf obj (diffOps (stateOf cell) new), [], rows⟩,
            { wk with visited := obj :: wk.visited, pool := wk.pool - used }) = .ok acc →
      Dispatched X w c m acc.2 obj calls[i]

/-- **`obj` is invoked in `c`'s tree on `w`**: the walk `derive` runs visits it. -/
def Invoked (X : Ctx D) (w : World D) (c : Call D) (obj : D) : Prop :=
  ∃ r, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok r ∧ obj ∈ r.2.visited

/-! ## The calls a run returned, one at a time -/

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

omit [Ord D] [DecidableEq D] in
/-- One step of the calls' fold: from where the first `i` left it, the `i`-th call's derivation. -/
private theorem callStep_ok {sub : Sub D} {obj : D} {acc q : Draft D × Walk D} {b : Body D}
    (h : callStep sub obj acc b = .ok q) : ∃ q', sub acc.2 obj b = .ok q' ∧ q = (acc.1.append q'.1, q'.2) := by
  unfold callStep at h
  simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨q', h1, rfl⟩ := h
  exact ⟨q', h1, rfl⟩

omit [Ord D] [DecidableEq D] in
/-- The fold over the first `i + 1` calls is the fold over the first `i`, then the `i`-th. -/
private theorem foldCalls_succ {sub : Sub D} {obj : D} {calls : List (Body D)} {i : Nat}
    (hi : i < calls.length) {a0 acc q : Draft D × Walk D}
    (hpre : (calls.take i).foldlM (callStep sub obj) a0 = .ok acc) (hq : callStep sub obj acc calls[i] = .ok q) :
    (calls.take (i + 1)).foldlM (callStep sub obj) a0 = .ok q := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.foldlM_append, hpre]
  simp [bind, Except.bind, hq, pure, Except.pure]

omit [Ord D] [DecidableEq D] in
/-- The whole fold, split at the `i`-th call: its derivation succeeded, and its effects sit inside. -/
private theorem foldCalls_split {sub : Sub D} {obj : D} {calls : List (Body D)} {i : Nat}
    (hi : i < calls.length) {a0 acc r : Draft D × Walk D}
    (hall : calls.foldlM (callStep sub obj) a0 = .ok r)
    (hpre : (calls.take i).foldlM (callStep sub obj) a0 = .ok acc) :
    ∃ q, sub acc.2 obj calls[i] = .ok q ∧ ∃ l, r.1.effects = acc.1.effects ++ q.1.effects ++ l := by
  have hsplit : calls = calls.take i ++ calls[i] :: calls.drop (i + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  rw [hsplit, List.foldlM_append, hpre] at hall
  simp only [bind, Except.bind, List.foldlM_cons] at hall
  cases hq' : callStep sub obj acc calls[i] with
  | error e => rw [hq'] at hall; cases hall
  | ok q' =>
      rw [hq'] at hall
      obtain ⟨q, hq, rfl⟩ := callStep_ok hq'
      obtain ⟨l, hl⟩ := foldCalls_effects _ _ hall
      exact ⟨q, hq, l, by rw [hl]; simp [Draft.append]⟩

/-! ## A dispatched receiver was derived, inside the signed call's derivation -/

/-- Every receiver the walk dispatched succeeded, and its effects sit inside the signed call's. -/
private theorem dispatched_ok {X : Ctx D} {w : World D} {c : Call D} {R : Draft D × Walk D}
    (hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok R)
    {n : Nat} {wk : Walk D} {a : D} {b : Body D} (hd : Dispatched X w c n wk a b) :
    ∃ r, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r ∧
      ∃ l₁ l₂, R.1.effects = l₁ ++ r.1.effects ++ l₂ := by
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
      obtain ⟨q, hq, l, hl'⟩ := foldCalls_split hi hd' hpre
      obtain ⟨m', hm, -, hq'⟩ := effect_as_signed hq
      obtain rfl := Nat.succ.inj hm.symm
      refine ⟨q, hq', l₁ ++ acc.1.effects, l ++ l₂, ?_⟩
      rw [hl, hl']
      simp

/-! ## A visited object was dispatched -/

/-- What the walk visited from a dispatched receiver on: visited before, or a dispatched invoke's. -/
private def VisitsFrom (X : Ctx D) (w : World D) (c : Call D) (wk : Walk D) (r : Draft D × Walk D) : Prop :=
  ∀ o ∈ r.2.visited, o ∈ wk.visited ∨
    ∃ n wk' a method args budget via, Dispatched X w c n wk' a (.invoke o method args budget via)

/-- One level of `dispatched_visits`: given it one level down, at this level. -/
private theorem dispatched_visits_step {X : Ctx D} {w : World D} {c : Call D} (n : Nat)
    (ihP : ∀ m, n = m + 1 → ∀ {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D},
      Dispatched X w c m wk a b →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c m) wk a b = .ok r →
      VisitsFrom X w c wk r)
    {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D} (hd : Dispatched X w c n wk a b)
    (h : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r) :
    VisitsFrom X w c wk r := by
  cases b with
  | invoke obj method args budget via =>
      have hok := h
      simp only [dispatch] at hok
      obtain ⟨-, cell, p, rq, new, calls, rows, used, hir, hrun, -, -, -, -, -, hdc⟩ := invoke_ok hok
      unfold deriveCalls at hdc
      have key : ∀ (suf : List (Body D)) (i : Nat) (acc r' : Draft D × Walk D),
          suf = calls.drop i →
          (calls.take i).foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj)
            (⟨[], writeOf obj (diffOps (stateOf cell) new), [], rows⟩,
              { wk with visited := obj :: wk.visited, pool := wk.pool - used }) = .ok acc →
          suf.foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj) acc = .ok r' →
          VisitsFrom X w c acc.2 r' := by
        intro suf
        induction suf with
        | nil =>
            intro i acc r' _ _ hf
            simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            exact fun o ho => .inl ho
        | cons b rest ihs =>
            intro i acc r' hsuf hpre hf
            have hi : i < calls.length := by
              rcases Nat.lt_or_ge i calls.length with h | h
              · exact h
              · rw [List.drop_eq_nil_of_le h] at hsuf
                cases hsuf
            have hsuf' := hsuf
            rw [← List.getElem_cons_drop hi] at hsuf'
            have hb : calls[i] = b := (List.cons.inj hsuf').1.symm
            have hrest : rest = calls.drop (i + 1) := (List.cons.inj hsuf').2
            rw [List.foldlM_cons, except_bind_ok] at hf
            obtain ⟨q', hq', hf⟩ := hf
            have hpre' := foldCalls_succ hi hpre (by rw [hb]; exact hq')
            obtain ⟨q, hq, rfl⟩ := callStep_ok hq'
            obtain ⟨m', hm, -, hq2⟩ := effect_as_signed hq
            have ih2 := ihs (i + 1) _ r' hrest hpre' hf
            intro o ho
            rcases ih2 o ho with ho' | hdisp
            · have hchild : Dispatched X w c m' acc.2 obj b := by
                subst hm
                rw [← hb]
                exact Dispatched.call i hi hd hok hir hrun hpre
              exact ihP m' hm hchild hq2 o ho'
            · exact .inr hdisp
      intro o ho
      rcases key calls 0 _ r rfl rfl hdc o ho with ho' | hdisp
      · simp only [List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · exact .inr ⟨n, wk, a, method, args, budget, via, hd⟩
        · exact .inl ho'
      · exact .inr hdisp
  | _ =>
      simp only [dispatch] at h
      obtain ⟨hv, -⟩ := stepped_walk h
      intro o ho
      rw [hv] at ho
      exact .inl ho

private theorem dispatched_visits {X : Ctx D} {w : World D} {c : Call D} :
    ∀ n {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D}, Dispatched X w c n wk a b →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r →
      VisitsFrom X w c wk r := by
  intro n
  induction n with
  | zero => exact dispatched_visits_step 0 (fun _ h => absurd h (by omega))
  | succ m ih =>
      exact dispatched_visits_step (m + 1) (fun m' h => by
        obtain rfl : m' = m := by omega
        exact ih)

/-- **A visited object was run by an invoke the walk dispatched.** -/
theorem dispatched_of_invoked {X : Ctx D} {w : World D} {c : Call D} {obj : D} (hi : Invoked X w c obj) :
    ∃ n wk actor method args budget via, Dispatched X w c n wk actor (.invoke obj method args budget via) := by
  obtain ⟨r, hr, hmem⟩ := hi
  rcases dispatched_visits _ .root hr obj hmem with h | h
  · simp at h
  · exact h

/-- **The signed invoke is the walk's root.** -/
theorem dispatched_of_signed {X : Ctx D} {w : World D} {c : Call D} {obj : D} {method : Nat}
    {args : ByteArray} {budget : Nat} {via : Option D} (hb : c.unsigned.body = .invoke obj method args budget via) :
    Dispatched X w c Bounds.callDepthMax ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member
      (.invoke obj method args budget via) := by
  have h := Dispatched.root (X := X) (w := w) (c := c)
  rw [hb] at h
  rw [hb]
  exact h

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

/-- **An invoke the walk of an admitted call dispatched is handed what its judged run returned.** A
signed call derived from `w` and admitted to `w'`, and an invoke of `obj` its walk dispatched
(`Dispatched`, at any depth: the signed invoke itself is `dispatched_of_signed`): THAT invoke's
`invokeRun` (its actor, method, `via`), its `X.program.run` with its arguments at the fuel the walk
gave it (`min budget wk.pool`), the laws in force by `lawsOf` and their judgement; and the committed
state reads its result: `obj` is live in `w'`, and its state holds at every key what that run
returned. The run is a function, so the calls it returned are the calls the walk derived. The order
laws are the price of the proof's route through `sealTurn`'s `duplicateEffect` check. -/
theorem invoke_tree_slots [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {n : Nat} {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat}
    {via : Option D}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hd : Dispatched X w c n wk actor (.invoke obj method args budget via)) :
    ∃ (cell : Cell) (p : D) (r : Req D) (s : Slots) (calls : List (Body D)) (rows : List (RowSlot D × RowAct))
      (used : Nat) (laws : List D),
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget wk.pool) = .ok (s, calls, rows, used) ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) (some p) laws (stateOf cell) s r = .ok () ∧
      ∃ cell', w'.live X.env obj = some cell' ∧ ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd', hs⟩ := receiveWith_sealed hw
  rw [derive_eq] at hd'
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hR] at hd'; cases hd'
  | ok R =>
  rw [hR] at hd'
  simp only [Except.map, Except.ok.injEq] at hd'
  subst hd'
  obtain ⟨r', hr', l₁, l₂, hl⟩ := dispatched_ok hR hd
  simp only [dispatch] at hr'
  obtain ⟨-, cell, p, rq, s, calls, rows, used, hir, hrun, -, -, -, hst, ⟨laws, hlw, hj⟩, hdc⟩ := invoke_ok hr'
  unfold deriveCalls at hdc
  obtain ⟨l, hl'⟩ := foldCalls_effects _ _ hdc
  have hin : (obj, if (diffOps (stateOf cell) s).isEmpty then Act.keep else .write (diffOps (stateOf cell) s)) ∈
      R.1.effects := by
    rw [hl, hl']
    simp [writeOf]
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  have hnd : (R.1.effects.map Prod.fst).Nodup := firstDup_none (sealTurn_firstDup hs)
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
  refine ⟨cell, p, rq, s, calls, rows, used, laws, hir, hrun, hlw, hj, ?_⟩
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
the dispatched invoke's run returned. -/
theorem invoke_tree_run [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {w w' : World D} {c : Call D}
    {t : Turn D} {n : Nat} {wk : Walk D} {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat}
    {via : Option D}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hd : Dispatched X w c n wk actor (.invoke obj method args budget via))
    {pins' : List (D × D)} {c' : Call D} {actor' : D} {method' : Nat} {via' : Option D}
    {cell' : Cell} {p' : D} {r' : Req D}
    (hr' : invokeRun X (pinned X.env w' pins') c' actor' obj method' via' = .ok (cell', p', r')) :
    ∃ (cell : Cell) (p : D) (r : Req D) (s : Slots) (calls : List (Body D)) (rows : List (RowSlot D × RowAct))
      (used : Nat) (laws : List D),
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, r) ∧
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget wk.pool) = .ok (s, calls, rows, used) ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge (pinned X.env w c.unsigned.pins) (some p) laws (stateOf cell) s r = .ok () ∧
      ∀ k, (stateOf cell').get k = s.get k := by
  obtain ⟨cell, p, r, s, calls, rows, used, laws, hir, hrun, hlw, hj, cell'', hl, hk⟩ := invoke_tree_slots hc ha hd
  have hl' := invokeRun_live hr'
  rw [hl] at hl'
  cases hl'
  exact ⟨cell, p, r, s, calls, rows, used, laws, hir, hrun, hlw, hj, hk⟩

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


/-! ## No receiver but write, law and invoke writes an object (the totality) -/

omit [Ord D] [DecidableEq D] in
private theorem readKind_look {look : Pinned D} {g : D} {k : Nat} {cell : Cell}
    (h : readKind look g k = .ok cell) : look g = .ok (some cell) ∧ cell.kind = k := by
  unfold readKind at h
  split at h
  · cases h
  · cases h
  · rename_i cl hl
    split at h
    · cases h; exact ⟨hl, by assumption⟩
    · cases h

/-- `x` is read through `look` as a cell of a kind other than an object's. -/
private def ReadOther (look : Pinned D) (x : D) : Prop :=
  ∃ k cl, k ≠ kindObject ∧ readKind look x k = .ok cl

omit [Ord D] [DecidableEq D] in
private theorem spendEnroll_at {g : D} {cell : Cell} {units : Nat} {short : Refusal D} {ef : Option (D × Act)}
    (h : spendEnroll g cell units short = .ok ef) : ∀ e ∈ ef.toList, e.1 = g := by
  obtain ⟨i, left, -, -, rfl⟩ := spendEnroll_ok h
  split <;> simp

omit [Ord D] [DecidableEq D] in
private theorem readAccount_kind {look : Pinned D} {x : D} {cell : Cell} {v : Value}
    (h : readAccount look x = .ok (cell, v)) : readKind look x kindAccount = .ok cell := by
  unfold readAccount at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', hk, h⟩ := h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hk
  · cases h

omit [Ord D] [DecidableEq D] in
private theorem readRef_kind {X : Ctx D} {look : Pinned D} {r : AcctRef D} {x : D} {cell : Cell} {v : Value}
    (h : readRef X look r = .ok (x, cell, v)) : readKind look x kindAccount = .ok cell := by
  unfold readRef at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨cell', v'⟩, ha, h⟩ := h
  cases r with
  | well a =>
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact readAccount_kind ha
  | of o a =>
      simp only [except_bind_ok] at h
      obtain ⟨⟨⟩, -, h⟩ := h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact readAccount_kind ha

omit [Ord D] in
private theorem checkParent_at {X : Ctx D} {look : Pinned D} {actor target : D} {rights : List Right}
    {parent : Option D} {ef : Option (D × Act)} (h : checkParent X look actor target rights parent = .ok ef) :
    ∀ e ∈ ef.toList, ReadOther look e.1 := by
  cases parent with
  | none =>
      simp only [checkParent, except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨⟨⟩, -, rfl⟩ := h
      simp
  | some p =>
      simp only [checkParent, except_bind_ok] at h
      obtain ⟨pc, hpc, pt, -, ⟨⟩, -, pg, -, ⟨⟩, -, ⟨⟩, -, h⟩ := h
      intro e he
      split at h
      · rw [spendEnroll_at h e he]; exact ⟨kindGrant, pc, by decide, hpc⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; simp at he

omit [Ord D] in
/-- **Every receiver but `write`, `law` and `invoke` writes only cells it read as another kind**: a
grant (an enrolment spend, a carve, a revocation), a member (a rotation) or an account (a transfer,
a credit line); births are not effects. -/
private theorem dispatch_other {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    {wk : Walk D} {actor : D} {b : Body D} {r : Draft D × Walk D}
    (hi : b.isInvoke = false) (hw : ∀ o e v, b ≠ .write o e v) (hl : ∀ o ls v, b ≠ .law o ls v)
    (h : dispatch X look rv c sub wk actor b = .ok r) : ∀ e ∈ r.1.effects, ReadOther look e.1 := by
  cases b with
  | invoke => simp [Body.isInvoke] at hi
  | write o e v => exact absurd rfl (hw o e v)
  | law o ls v => exact absurd rfl (hl o ls v)
  | enroll key next possession via =>
      have hd := stepped_draft h
      unfold enroll at hd
      simp only [except_bind_ok] at hd
      obtain ⟨_, -, g, hg, spend, hs, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      rw [spendEnroll_at hs e he]
      exact ⟨kindGrant, g, by decide, hg⟩
  | rotate key next =>
      have hd := stepped_draft h
      unfold rotate at hd
      simp only [except_bind_ok] at hd
      obtain ⟨m, hm, ⟨⟩, -, cm, -, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨kindMember, m, by decide, hm⟩
  | install pkg =>
      have hd := stepped_draft h
      unfold install at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | create pkg laws state =>
      have hd := stepped_draft h
      unfold create at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hd⟩ := hd
      intro e he
      cases pkg with
      | none =>
          simp only [bind, Except.bind, pure, Except.pure] at hd
          injection hd with hd
          rw [← hd] at he; simp at he
      | some p =>
          simp only [except_bind_ok] at hd
          obtain ⟨_, -, hd⟩ := hd
          simp only [pure, Except.pure] at hd
          injection hd with hd
          rw [← hd] at he; simp at he
  | grant target grantee rights parent =>
      have hd := stepped_draft h
      unfold grant at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, carve, hcv, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      exact checkParent_at hcv e he
  | revoke g =>
      have hd := stepped_draft h
      unfold revoke at hd
      simp only [except_bind_ok] at hd
      obtain ⟨cell, hc, issuer, -, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨kindGrant, cell, by decide, hc⟩
  | issue cap =>
      have hd := stepped_draft h
      unfold issue at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | account asset owner =>
      have hd := stepped_draft h
      simp only [account, pure, Except.pure, Except.ok.injEq] at hd
      intro e he; rw [← hd] at he; simp at he
  | transfer src dst amount via once =>
      have hd := stepped_draft h
      unfold transfer at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨s, scell, sv⟩, hs, ⟨d, dcell, dv⟩, hdr, _, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨kindAccount, scell, by decide, readRef_kind hs⟩
      · exact ⟨kindAccount, dcell, by decide, readRef_kind hdr⟩
  | credit well acct amount via =>
      have hd := stepped_draft h
      unfold credit at hd
      simp only [except_bind_ok] at hd
      obtain ⟨⟨wcell, wv⟩, hwl, ⟨a, acell, av⟩, har, _, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, ⟨⟩, -, hd⟩ := hd
      simp only [pure, Except.pure, Except.ok.injEq] at hd
      intro e he
      rw [← hd] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨kindAccount, wcell, by decide, readAccount_kind hwl⟩
      · exact ⟨kindAccount, acell, by decide, readRef_kind har⟩

/-- What a Draft's effects are, for the totality: at a cell read as another kind, or at an object
an invoke the walk dispatched ran. -/
private def EffectsAt (X : Ctx D) (w : World D) (c : Call D) (efs : List (D × Act)) : Prop :=
  ∀ e ∈ efs, ReadOther (pinned X.env w c.unsigned.pins) e.1 ∨
    ∃ n wk a method args budget via, Dispatched X w c n wk a (.invoke e.1 method args budget via)

/-- One level of `dispatched_effects`: given it one level down, at this level. -/
private theorem dispatched_effects_step {X : Ctx D} {w : World D} {c : Call D} (n : Nat)
    (ihP : ∀ m, n = m + 1 → ∀ {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D},
      Dispatched X w c m wk a b → b.callable = true →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c m) wk a b = .ok r →
      EffectsAt X w c r.1.effects)
    {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D} (hd : Dispatched X w c n wk a b)
    (hw : ∀ o e v, b ≠ .write o e v) (hl : ∀ o ls v, b ≠ .law o ls v)
    (h : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r) :
    EffectsAt X w c r.1.effects := by
  cases hb : b.isInvoke with
  | false => exact fun e he => .inl (dispatch_other hb hw hl h e he)
  | true =>
  cases b with
  | invoke obj method args budget via =>
      have hok := h
      simp only [dispatch] at hok
      obtain ⟨-, cell, p, rq, new, calls, rows, used, hir, hrun, -, -, -, -, -, hdc⟩ := invoke_ok hok
      unfold deriveCalls at hdc
      have key : ∀ (suf : List (Body D)) (i : Nat) (acc r' : Draft D × Walk D),
          suf = calls.drop i →
          (calls.take i).foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj)
            (⟨[], writeOf obj (diffOps (stateOf cell) new), [], rows⟩,
              { wk with visited := obj :: wk.visited, pool := wk.pool - used }) = .ok acc →
          suf.foldlM (callStep (tree X (pinned X.env w c.unsigned.pins)
            (rowView X.env w c.unsigned) c n) obj) acc = .ok r' →
          EffectsAt X w c acc.1.effects → EffectsAt X w c r'.1.effects := by
        intro suf
        induction suf with
        | nil =>
            intro i acc r' _ _ hf ha
            simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            exact ha
        | cons b rest ihs =>
            intro i acc r' hsuf hpre hf ha
            have hi : i < calls.length := by
              rcases Nat.lt_or_ge i calls.length with h | h
              · exact h
              · rw [List.drop_eq_nil_of_le h] at hsuf
                cases hsuf
            have hsuf' := hsuf
            rw [← List.getElem_cons_drop hi] at hsuf'
            have hb : calls[i] = b := (List.cons.inj hsuf').1.symm
            have hrest : rest = calls.drop (i + 1) := (List.cons.inj hsuf').2
            rw [List.foldlM_cons, except_bind_ok] at hf
            obtain ⟨q', hq', hf⟩ := hf
            have hpre' := foldCalls_succ hi hpre (by rw [hb]; exact hq')
            obtain ⟨q, hq, rfl⟩ := callStep_ok hq'
            obtain ⟨m', hm, hcall, hq2⟩ := effect_as_signed hq
            have hchild : Dispatched X w c m' acc.2 obj b := by
              subst hm
              rw [← hb]
              exact Dispatched.call i hi hd hok hir hrun hpre
            have hq3 := ihP m' hm hchild hcall hq2
            refine ihs (i + 1) _ r' hrest hpre' hf (fun e he => ?_)
            simp only [Draft.append, List.mem_append] at he
            rcases he with he | he
            · exact ha e he
            · exact hq3 e he
      refine key calls 0 _ r rfl rfl hdc (fun e he => ?_)
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact .inr ⟨n, wk, a, method, args, budget, via, hd⟩
  | _ => simp [Body.isInvoke] at hb

private theorem dispatched_effects {X : Ctx D} {w : World D} {c : Call D} :
    ∀ n {wk : Walk D} {a : D} {b : Body D} {r : Draft D × Walk D}, Dispatched X w c n wk a b →
      (∀ o e v, b ≠ .write o e v) → (∀ o ls v, b ≠ .law o ls v) →
      dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c n) wk a b = .ok r →
      EffectsAt X w c r.1.effects := by
  intro n
  induction n with
  | zero => exact fun hd hw hl h => dispatched_effects_step 0 (fun _ h => absurd h (by omega)) hd hw hl h
  | succ m ih =>
      exact fun hd hw hl h => dispatched_effects_step (m + 1) (fun m' hm => by
        obtain rfl : m' = m := by omega
        intro wk' a' b' r' hd' hc h'
        exact ih hd' (fun o e v he => by subst he; simp [Body.callable] at hc)
          (fun o ls v he => by subst he; simp [Body.callable] at hc) h') hd hw hl h

/-- **The totality: no receiver but `write`, `law` and `invoke` writes an object.** An effect of a
signed call's derivation on `w` at a cell that `w`'s pinned view reads as an object (`kindObject`) is
the signed call's own `write` or `law` of that object, or the own state write of an invoke of it
that the call's walk dispatched (at any depth). Every other receiver writes a cell it read as a
grant, a member or an account, and a cell has one kind. -/
theorem effect_at_object {X : Ctx D} {w : World D} {c : Call D} {R : Draft D × Walk D}
    (hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body = .ok R)
    {e : D × Act} (he : e ∈ R.1.effects) {cell : Cell}
    (hk : readKind (pinned X.env w c.unsigned.pins) e.1 kindObject = .ok cell) :
    (∃ edits via, c.unsigned.body = .write e.1 edits via) ∨
      (∃ laws via, c.unsigned.body = .law e.1 laws via) ∨
      ∃ n wk a method args budget via, Dispatched X w c n wk a (.invoke e.1 method args budget via) := by
  have hother : ¬ ReadOther (pinned X.env w c.unsigned.pins) e.1 := by
    rintro ⟨k, cl, hne, hcl⟩
    obtain ⟨h1, h1k⟩ := readKind_look hcl
    obtain ⟨h2, h2k⟩ := readKind_look hk
    rw [h1] at h2
    injection h2 with h2
    injection h2 with h2
    subst h2
    exact hne (h1k.symm.trans h2k)
  cases hb : c.unsigned.body with
  | write o edits via =>
      rw [hb] at hR
      have hd := stepped_draft hR
      obtain ⟨_, _, _, -, -, -, -, -, hdeq⟩ := write_judged hd
      rw [hdeq] at he
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact .inl ⟨edits, via, rfl⟩
  | law o laws via =>
      rw [hb] at hR
      have hd := stepped_draft hR
      obtain ⟨_, _, _, -, -, -, -, -, -, -, hef⟩ := law_judged hd
      rw [hef] at he
      simp only [writeOf, List.mem_singleton] at he
      subst he
      exact .inr (.inl ⟨laws, via, rfl⟩)
  | _ =>
      have hroot := Dispatched.root (X := X) (w := w) (c := c)
      rw [hb] at hroot hR
      rcases dispatched_effects _ hroot (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hR e he with
        h | h
      · exact absurd h hother
      · exact .inr (.inr h)

omit [Ord D] in
private theorem actFor_none {obj : D} {l : List (D × Act)} (h : ∀ e ∈ l, e.1 ≠ obj) : actFor l obj = .keep := by
  unfold actFor
  rw [List.find?_eq_none.mpr (fun e he => by simpa using h e he)]

/-- **The totality, at the World.** A signed call derived from `w` and admitted to `w'`, and an
object live in `w`: either the turn kept it (every touch of it keeps, it is not born, and the call
neither writes nor changes the laws of it nor dispatched any invoke of it), or the signed call is a
`write` or a `law` of it, or the call's walk dispatched an invoke of it. No receiver of any other
kind, at any depth, writes or retires an object; and the first case is exact: a call that invoked
the object, even one whose run left the state as it was, is never filed as a keep. -/
theorem object_turn_cases {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {obj : D} {cell : Cell}
    (hc : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hl : w.live X.env obj = some cell)
    (hk : cell.kind = kindObject) :
    ((∀ x ∈ t.touches, x.cell = obj → x.act = .keep) ∧ obj ∉ createdIds t ∧
        (∀ edits via, c.unsigned.body ≠ .write obj edits via) ∧ (∀ laws via, c.unsigned.body ≠ .law obj laws via) ∧
        ∀ n wk a method args budget via, ¬ Dispatched X w c n wk a (.invoke obj method args budget via)) ∨
      (∃ edits via, c.unsigned.body = .write obj edits via) ∨
      (∃ laws via, c.unsigned.body = .law obj laws via) ∨
      ∃ n wk a method args budget via, Dispatched X w c n wk a (.invoke obj method args budget via) := by
  obtain ⟨-, hw⟩ := receive_ok_with hc
  obtain ⟨-, d, hd, hs⟩ := receiveWith_sealed hw
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
    obtain ⟨q, hq, hqe⟩ := hpins e he
    have hrk : readKind (pinned X.env w c.unsigned.pins) e.1 kindObject = .ok cell := by
      have hany : (c.unsigned.pins.any fun p => decide (p.1 = e.1)) = true :=
        List.any_eq_true.mpr ⟨q, hq, by simpa using hqe⟩
      simp [readKind, pinned, hany, hl, hk]
    exact .inr (effect_at_object hR he hrk)
  · refine .inl ⟨fun x hx hxc => ?_, ?_, fun edits via hb => ?_, fun laws via hb => ?_,
      fun n wk a method args budget via hd => ?_⟩
    · rw [htouch] at hx
      obtain ⟨q', -, rfl⟩ := List.mem_map.mp hx
      simp only at hxc ⊢
      rw [hxc]
      exact actFor_none (fun e he he' => hex ⟨e, he, he'⟩)
    · obtain ⟨posts, hk', -⟩ := admit_ok ha
      exact live_not_created hk' hl
    · rw [hb] at hR
      obtain ⟨_, _, _, -, -, -, -, -, hdeq⟩ := write_judged (stepped_draft hR)
      have hm : ∃ a, (obj, a) ∈ R.1.effects := by rw [hdeq]; simp [writeOf]
      obtain ⟨a, ham⟩ := hm
      exact hex ⟨(obj, a), ham, rfl⟩
    · rw [hb] at hR
      obtain ⟨_, _, _, -, -, -, -, -, -, -, hef⟩ := law_judged (stepped_draft hR)
      have hm : ∃ a, (obj, a) ∈ R.1.effects := by rw [hef]; simp [writeOf]
      obtain ⟨a, ham⟩ := hm
      exact hex ⟨(obj, a), ham, rfl⟩
    · obtain ⟨r, hr, l₁, l₂, hl₁⟩ := dispatched_ok hR hd
      simp only [dispatch] at hr
      obtain ⟨-, cell₀, p₀, rq₀, new₀, calls₀, rows₀, used₀, -, -, -, -, -, -, -, hdc⟩ := invoke_ok hr
      unfold deriveCalls at hdc
      obtain ⟨l, hl'⟩ := foldCalls_effects _ _ hdc
      have hm : ∃ a, (obj, a) ∈ R.1.effects := by
        refine ⟨if (diffOps (stateOf cell₀) new₀).isEmpty then .keep else .write (diffOps (stateOf cell₀) new₀), ?_⟩
        rw [hl₁, hl']
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_append_left
        exact List.mem_cons_self ..
      obtain ⟨a, ham⟩ := hm
      exact hex ⟨(obj, a), ham, rfl⟩

/-! ## Tooth: the totality rests on each receiver's kind check -/

/-- `revoke` with its kind check deleted: it retires whatever cell the pins hold at `g`. -/
private def revokeAnyKind (look : Pinned D) (g : D) : Except (Refusal D) (Draft D) :=
  match look g with
  | .ok (some _) => .ok ⟨[], [(g, .retire)], [], []⟩
  | _ => .error (.missingCell g)

omit [Ord D] in
/-- **Tooth: a receiver that wrote an object cell would break the totality.** Over a view reading
`g` as an object, `revoke` refuses `wrongKind` (its `readKind … kindGrant`), while the same receiver
without that check derives the retirement of the object: an effect at a cell read as an object that
is no `write`, `law` or invoke of it. Every receiver `effect_at_object` admits carries such a check. -/
theorem effect_at_object_needs_kind (X : Ctx D) (a : At D) {look : Pinned D} {g : D} {cell : Cell}
    (hg : look g = .ok (some cell)) (hk : cell.kind = kindObject) :
    readKind look g kindObject = .ok cell ∧
      revoke X look a g = .error (.wrongKind g kindGrant) ∧
      ∃ d, revokeAnyKind look g = .ok d ∧ (g, Act.retire) ∈ d.effects := by
  have hne : cell.kind ≠ kindGrant := by rw [hk]; decide
  refine ⟨by simp [readKind, hg, hk], by simp [revoke, readKind, hg, hne, bind, Except.bind],
    ⟨⟨[], [(g, .retire)], [], []⟩, by simp [revokeAnyKind, hg], by simp⟩⟩

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
emits a non-invoke effect at an object cell (`effect_at_object`), so the order laws are the price of
the route through `duplicateEffect`. -/
theorem effectsPinned_unlawful_ord :
    isOk (@effectsPinned Nat allLt _ [(5, 5)] twoAt5) = true ∧
      actFor twoAt5 5 = .write [.set 16 ⟨#[1]⟩] ∧
      Act.write [.set 16 ⟨#[1]⟩] ≠ .write [.set 16 ⟨#[2]⟩] ∧
      effectsPinned [(5, 5)] twoAt5 = .error (.duplicateEffect 5) :=
  ⟨by decide +kernel, by decide, by decide, rfl⟩

end Nanodregg.Kernel.Receive
