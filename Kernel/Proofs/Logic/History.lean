/-
# Kernel.Proofs.Logic.History — a World's history around one object, lifted once to every law (KERNEL-28, Q3)

`Lang.Proofs.Chain` lifts ONE law's admitted steps to a history (`Std.Chain`, its schemes). This
module is the kernel's half: what the World does around one object is a chain of steps each law in
force admitted, for every body kind, proved once.

* `ObjectStep X obj w w' e`: one step of the World from `w` to `w'`, as `obj` sees it. Steps that
  leave `obj` alone record nothing (`e = none`): a recorded refusal (`refusal`), an admitted turn
  that touches it nowhere and does not bear it (`other`, any turn), a call-derived turn whose
  footprint does not hold it (`frame`, by `CallFoot`), a call-derived turn that pins it, keeps it,
  and neither writes it, changes its laws, nor dispatched any invoke of it (`keep`). So a step that
  invoked the object is never filed as one that left it alone, even when its run kept the state:
  an invoke's own effect is a touch of the object (`other`, `frame` exclude it) and `keep` says
  "no invoke" outright; a history counts every invoke it holds. Steps that judge it record what the judge saw (`e = some (look, pkg,
  laws, req, old, new, calls)`): the signed `write` of it (over a canonical cell), the signed `law`
  of it (the `relaw` judgement, over the unchanged state), the signed `invoke` of it, and an invoke
  of it NESTED in another call's tree (`Dispatched`; the order laws are its route's price).
* `ObjectHistory X obj w w' tr`: the Kleene star; `tr` is the judged steps, in order.
* `object_step_none`, `object_step_some`: a step that records nothing keeps `obj`'s entry; a
  judged step's `old` is the live state, the laws in force passed `old → new` (`write_judged`,
  `law_judged`, `invoke_next_judged`, `invoke_tree_slots`), and the next live state reads `new` at
  every key (`write_next_slots`, `law_next_slots`, `invoke_next_slots`, `invoke_tree_slots`).
* `object_history_of_honest`: THE TOTALITY at the log: an honest folded log from a canonical World
  (`CellsCanon`, from genesis by `genesis_cellsCanon`/`fold_cellsCanon`) is an `ObjectHistory` of
  every object live at its start (`object_turn_cases` per turn: no receiver but write, law and
  invoke writes an object). For an object born inside the log, split the log at its birth (the
  object must be live at the history's start).
* `object_history_chain`: THE LIFT: for a `NoRef` law `t` (field `ℓ` of the package `p` that the law
  id reads as in every judged step's view) in force at every judged step, the history projects to
  `Std.Chain (Std.Step [] t)` from the object's state, step for step (`judgeOne_admits_relib`; a
  `relaw` keeps the state, so each step is a `Step`, not only an `Admits`).

The polarity (PROOF-ENGINEERING Q3): wp over the fold (a step is "if it committed then"), sp over
the law (`Std.Admits` stays existential; a faulting law has no derivation, so no step).
Teeth (`Kernel.Proofs.Logic.HistoryWitness`): `object_history_chain_witnessed` (every premise of
the lift holds together, through `Lang.program`, on a signed invoke whose run moves the state, with
the counter's `NoRef` law in force); `write_history_witnessed` (a write step, at a data object);
`object_history_needs_inForce` (on that write history, whose step no law judged, a law that admits
nothing has no chain: drop the in-force premise and the conclusion is false); the steps' own: `write_needs_canon` (`write`'s canonicity),
`law_slots_need_bound`, `effect_at_object_needs_kind` (the totality), `effectsPinned_unlawful_ord`
(`nested`'s order laws). `object_history_runs`: each judged step's calls are its run's;
`object_history_start`: a history with a judged step starts at a live object whose state reads.
-/
import Kernel.Proofs.WriteNext
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.Logic.Triple
import Lang.Proofs.Chain
import Lang.Proofs.Extract
import Lang.Proofs.Invoke
import Lang.Proofs.LawReceiver

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **One step of the World around `obj`.** `none`: the step leaves `obj` alone; `some (look, pkg,
laws, req, old, new, calls)`: the step judged `obj`'s state `old → new` under `req`, in the view
`look`, by the package `pkg` (an invoke's) and the laws `laws` (the cell's), and returned `calls`
(an invoke's; `[]` for a write or a law). -/
inductive ObjectStep (X : Ctx D) (obj : D) :
    World D → World D → Option (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)) → Prop
  | refusal {w w' : World D} {r : Refused D} : World.refuse X.env w r = .ok w' → ObjectStep X obj w w' none
  | other {w w' : World D} {t : Turn D} :
      World.admit X.env w t = .ok w' → (∀ x ∈ t.touches, x.cell ≠ obj) → obj ∉ createdIds t →
      ObjectStep X obj w w' none
  | keep {w w' : World D} {c : Call D} {t : Turn D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' →
      (∀ x ∈ t.touches, x.cell = obj → x.act = .keep) → obj ∉ createdIds t →
      (∀ edits via, c.unsigned.body ≠ .write obj edits via) → (∀ laws via, c.unsigned.body ≠ .law obj laws via) →
      (∀ n wk actor method args budget via, ¬ Dispatched X w c n wk actor (.invoke obj method args budget via)) →
      ObjectStep X obj w w' none
  | frame {w w' : World D} {c : Call D} {t : Turn D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' → ¬ CallFoot X c w (.cell obj) →
      ObjectStep X obj w w' none
  | write {w w' : World D} {c : Call D} {t : Turn D} {edits : List (Nat × Option ByteArray)} {via : Option D}
      {cell : Cell} {principal : D} {laws : List D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' → c.unsigned.body = .write obj edits via →
      w.live X.env obj = some cell → Slots.ascending cell.slots = true →
      ownerAuthority X (pinned X.env w c.unsigned.pins) c.unsigned.member obj cell .mutate via = .ok principal →
      lawsOf X obj cell = .ok laws →
      ObjectStep X obj w w' (some (pinned X.env w c.unsigned.pins, none, laws,
        reqOf c.unsigned obj principal .write, stateOf cell, applyEdits (stateOf cell) edits, []))
  | law {w w' : World D} {c : Call D} {t : Turn D} {laws' : List D} {via : Option D}
      {cell : Cell} {principal : D} {laws : List D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' → c.unsigned.body = .law obj laws' via →
      w.live X.env obj = some cell →
      ownerAuthority X (pinned X.env w c.unsigned.pins) c.unsigned.member obj cell .mutate via = .ok principal →
      lawsOf X obj cell = .ok laws →
      ObjectStep X obj w w' (some (pinned X.env w c.unsigned.pins, none, laws,
        reqOf c.unsigned obj principal (.relaw laws'), stateOf cell, stateOf cell, []))
  | invoke {w w' : World D} {c : Call D} {t : Turn D} {method : Nat} {args : ByteArray} {budget : Nat}
      {via : Option D} {cell : Cell} {p : D} {r : Req D} {s : Slots} {calls : List (Body D)}
      {rows : List (RowSlot D × RowAct)} {used : Nat} {laws : List D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' →
      c.unsigned.body = .invoke obj method args budget via →
      invokeRun X (pinned X.env w c.unsigned.pins) c c.unsigned.member obj method via = .ok (cell, p, r) →
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget (poolOf c.unsigned.body)) = .ok (s, calls, rows, used) →
      lawsOf X obj cell = .ok laws →
      ObjectStep X obj w w' (some (pinned X.env w c.unsigned.pins, some p, laws, r, stateOf cell, s, calls))
  | nested [Std.TransOrd D] [Std.LawfulEqOrd D] {w w' : World D} {c : Call D} {t : Turn D} {n : Nat}
      {wk : Walk D} {actor : D} {method : Nat} {args : ByteArray} {budget : Nat}
      {via : Option D} {cell : Cell} {p : D} {r : Req D} {s : Slots} {calls : List (Body D)}
      {rows : List (RowSlot D × RowAct)} {used : Nat} {laws : List D} :
      receive X w c = .ok t → World.admit X.env w t = .ok w' →
      Dispatched X w c n wk actor (.invoke obj method args budget via) →
      invokeRun X (pinned X.env w c.unsigned.pins) c actor obj method via = .ok (cell, p, r) →
      X.program.run (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) p (stateOf cell)
        method args r (min budget wk.pool) = .ok (s, calls, rows, used) →
      lawsOf X obj cell = .ok laws →
      ObjectStep X obj w w' (some (pinned X.env w c.unsigned.pins, some p, laws, r, stateOf cell, s, calls))

/-- **A history of the World around `obj`**, from `w` to `w'`: the judged steps, in order. -/
inductive ObjectHistory (X : Ctx D) (obj : D) :
    World D → World D → List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)) → Prop
  | nil (w : World D) : ObjectHistory X obj w w []
  | cons {w w₁ w' : World D} {e : Option (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))}
      {rest : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))} :
      ObjectStep X obj w w₁ e → ObjectHistory X obj w₁ w' rest → ObjectHistory X obj w w' (e.toList ++ rest)

/-! ## One step -/

/-- **A step that records nothing keeps the object's entry**, live or not. -/
theorem object_step_none {X : Ctx D} {obj : D} {w w' : World D} (h : ObjectStep X obj w w' none) :
    w'.live X.env obj = w.live X.env obj := by
  cases h with
  | refusal hr => exact refuse_live hr obj
  | other ha hk hc =>
      have he := admit_frame ha (fun x hx hxc => absurd hxc (hk x hx)) hc
      unfold World.live; rw [he]
  | keep _ ha hk hc _ _ _ =>
      have he := admit_frame ha hk hc
      unfold World.live; rw [he]
  | frame hc ha hf =>
      have he := call_frame hc ha (.cell obj) hf
      unfold World.live World.entry
      rw [he]

omit [Ord D] in
private theorem invokeRun_occasion {X : Ctx D} {look : Pinned D} {c : Call D} {actor obj : D} {method : Nat}
    {via : Option D} {cell : Cell} {p : D} {r : Req D}
    (h : invokeRun X look c actor obj method via = .ok (cell, p, r)) : r.occasion = .invoke method := by
  unfold invokeRun at h
  simp only [except_bind_ok] at h
  obtain ⟨cell', -, pkg, -, p', -, pr, -, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2.2]; rfl

/-- **A judged step.** Its `old` is the object's live state; the laws in force (the package's and the
cell's) admitted `old → new` under its request, in its view; a law change or adoption keeps the
state; an invoke's package ran `old → new` on the method its request names, returning its calls (a
write or a law returns none); the object is live after it, with a state that reads `new` at every
key. -/
theorem object_step_some {X : Ctx D} {obj : D} {w w' : World D} {look : Pinned D} {pkg : Option D}
    {laws : List D} {r : Req D} {old new : Slots} {calls : List (Body D)}
    (h : ObjectStep X obj w w' (some (look, pkg, laws, r, old, new, calls)))
    {cell : Cell} (hl : w.live X.env obj = some cell) :
    old = stateOf cell ∧ X.program.judge look pkg laws old new r = .ok () ∧
      (∀ ls, r.occasion = .relaw ls ∨ r.occasion = .adopt ls → new = old) ∧
      (pkg = none → calls = []) ∧
      (∀ q, pkg = some q → ∃ rv method args fuel rows used, r.occasion = .invoke method ∧
        X.program.run look rv q old method args r fuel = .ok (new, calls, rows, used)) ∧
      ∃ cell', w'.live X.env obj = some cell' ∧ ∀ k, (stateOf cell').get k = new.get k := by
  cases h with
  | @write _ _ c t edits via cell₀ principal laws hc ha hb hl₀ hcan hau hlw =>
      rw [hl] at hl₀; cases hl₀
      obtain ⟨principal', laws', -, hau', hlw', hj, cell', hl', -, hk⟩ := write_next_slots hc ha hb hl hcan
      rw [hau] at hau'; cases hau'
      rw [hlw] at hlw'; cases hlw'
      refine ⟨rfl, hj, fun ls hls => ?_, fun _ => rfl, fun q hq => by simp at hq, cell', hl', hk⟩
      rcases hls with h | h <;> cases h
  | @law _ _ c t laws' via cell₀ principal laws hc ha hb hl₀ hau hlw =>
      rw [hl] at hl₀; cases hl₀
      obtain ⟨principal', laws'', -, hau', hlw', hrel, -, cell', hl', hk⟩ := law_next_slots hc ha hb hl
      rw [hau] at hau'; cases hau'
      rw [hlw] at hlw'; cases hlw'
      exact ⟨rfl, hrel, fun _ _ => rfl, fun _ => rfl, fun q hq => by simp at hq, cell', hl', hk⟩
  | @invoke _ _ c t method args budget via cell₀ p r s calls rows used laws hc ha hb hr hp hlw =>
      have hl₀ := invokeRun_live hr
      rw [hl] at hl₀; cases hl₀
      obtain ⟨laws', hlw', hj⟩ := invoke_next_judged hc ha hb hr hp
      rw [hlw] at hlw'; cases hlw'
      obtain ⟨cell', hl', hk⟩ := invoke_next_slots hc ha hb hr hp
      have ho := invokeRun_occasion hr
      refine ⟨rfl, hj, fun ls hls => ?_, fun h => by simp at h, fun q hq => ?_, cell', hl', hk⟩
      · rw [ho] at hls; rcases hls with h | h <;> cases h
      · cases hq; exact ⟨_, method, args, _, rows, used, ho, hp⟩
  | nested hc ha hd hr hp hlw =>
      have hl₀ := invokeRun_live hr
      rw [hl] at hl₀; cases hl₀
      obtain ⟨cell₁, p₁, r₁, s₁, calls₁, rows₁, used₁, laws₁, hr₁, hp₁, hlw₁, hj, cell', hl', hk⟩ :=
        invoke_tree_slots hc ha hd
      rw [hr] at hr₁
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr₁
      obtain ⟨rfl, rfl, rfl⟩ := hr₁
      rw [hp] at hp₁
      simp only [Except.ok.injEq, Prod.mk.injEq] at hp₁
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp₁
      rw [hlw] at hlw₁; cases hlw₁
      have ho := invokeRun_occasion hr
      refine ⟨rfl, hj, fun ls hls => ?_, fun h => by simp at h, fun q hq => ?_, cell', hl', hk⟩
      · rw [ho] at hls; rcases hls with h | h <;> cases h
      · cases hq; exact ⟨_, _, _, _, _, _, ho, hp⟩

/-- A judged step happened at a World holding the object live. -/
theorem object_step_live {X : Ctx D} {obj : D} {w w' : World D}
    {e : Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D)}
    (h : ObjectStep X obj w w' (some e)) : ∃ cell, w.live X.env obj = some cell := by
  cases h with
  | write _ _ _ hl => exact ⟨_, hl⟩
  | law _ _ _ hl => exact ⟨_, hl⟩
  | invoke _ _ _ hr => exact ⟨_, invokeRun_live hr⟩
  | nested _ _ _ hr => exact ⟨_, invokeRun_live hr⟩

/-! ## The totality, at the log -/

private theorem admit_kind {E : Env D} {w w' : World D} {t : Turn D} {obj : D} {cell cell' : Cell}
    (ha : World.admit E w t = .ok w') (hl : w.live E obj = some cell) (hl' : w'.live E obj = some cell') :
    cell'.kind = cell.kind := by
  rcases admit_live ha hl' with hb | ⟨c0, h0, rfl | ⟨ops, hp⟩⟩
  · obtain ⟨posts, hk, -⟩ := admit_ok ha
    exact absurd (List.mem_map.mpr ⟨_, hb, rfl⟩) (live_not_created hk hl)
  · rw [hl] at h0; cases h0; rfl
  · rw [hl] at h0; cases h0; exact (postWrite_keeps hp).1

/-- **Every honest folded log is a history of every object live at its start** (the totality at
the log). From a World whose cells are canonical (`CellsCanon`: genesis has it,
`genesis_cellsCanon`, and every fold keeps it, `fold_cellsCanon`), each logged turn keeps the
object, or is the signed `write` or `law` of it, or dispatched an invoke of it
(`object_turn_cases`); each logged refusal keeps it. So the log is an `ObjectHistory`: no step of it
moves the object outside one of `ObjectStep`'s constructors. -/
theorem object_history_of_honest [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {obj : D} :
    ∀ {w w' : World D} {l : List (Step D)}, World.fold X.env w l = .ok w' → Honest X w l →
      CellsCanon X.env w →
      ∀ {cell : Cell}, w.live X.env obj = some cell → cell.kind = kindObject →
        ∃ tr, ObjectHistory X obj w w' tr
  | w, w', [], hf, _, _, _, _, _ => by
      simp only [World.fold, Except.ok.injEq] at hf; subst hf; exact ⟨[], .nil _⟩
  | w, w', .refusal r :: rest, hf, hh, hcan, cell, hl, hk => by
      obtain ⟨w₁, hs, -, hfr, hhr⟩ := fold_honest_cons hf hh
      have hrf : World.refuse X.env w r = .ok w₁ := hs
      have hstep : ObjectStep X obj w w₁ none := .refusal hrf
      obtain ⟨tr, htr⟩ := object_history_of_honest hfr hhr
        (fun id cl hl' => hcan id cl ((refuse_live hrf id).symm.trans hl'))
        ((object_step_none hstep).trans hl) hk
      exact ⟨tr, .cons hstep htr⟩
  | w, w', .turn t :: rest, hf, hh, hcan, cell, hl, hk => by
      obtain ⟨w₁, hadm, ⟨c, -, hc, -⟩, hfr, hhr⟩ := fold_honest_cons hf hh
      have hadm : World.admit X.env w t = .ok w₁ := hadm
      have hcan₁ := admit_cellsCanon hcan hadm
      rcases object_turn_cases hc hadm hl hk with ⟨hkeep, hnc, hnw, hnl, hni⟩ | ⟨edits, via, hb⟩ |
          ⟨laws', via, hb⟩ | ⟨n, wk, a, method, args, budget, via, hd⟩
      · have hstep : ObjectStep X obj w w₁ none := .keep hc hadm hkeep hnc hnw hnl hni
        obtain ⟨tr, htr⟩ := object_history_of_honest hfr hhr hcan₁ ((object_step_none hstep).trans hl) hk
        exact ⟨tr, .cons hstep htr⟩
      · obtain ⟨principal, laws, -, hau, hlw, -, cell', hl', -, -⟩ :=
          write_next_slots hc hadm hb hl (hcan _ _ hl)
        obtain ⟨tr, htr⟩ := object_history_of_honest hfr hhr hcan₁ hl' ((admit_kind hadm hl hl').trans hk)
        exact ⟨_, .cons (.write hc hadm hb hl (hcan _ _ hl) hau hlw) htr⟩
      · obtain ⟨principal, laws, -, hau, hlw, -, -, cell', hl', -⟩ := law_next_slots hc hadm hb hl
        obtain ⟨tr, htr⟩ := object_history_of_honest hfr hhr hcan₁ hl' ((admit_kind hadm hl hl').trans hk)
        exact ⟨_, .cons (.law hc hadm hb hl hau hlw) htr⟩
      · obtain ⟨cell₀, p, r, s, calls, rows, used, laws, hr, hp, hlw, -, cell', hl', -⟩ :=
          invoke_tree_slots hc hadm hd
        obtain ⟨tr, htr⟩ := object_history_of_honest hfr hhr hcan₁ hl' ((admit_kind hadm hl hl').trans hk)
        exact ⟨_, .cons (.nested hc hadm hd hr hp hlw) htr⟩

/-! ## The lift -/

omit [Ord D] [DecidableEq D] in
private theorem judge_mem {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {look : Pinned D}
    {pkg : Option D} {laws : List D} {old new : Slots} {r : Req D}
    (h : Lang.judge bytesOf digestOf look pkg laws old new r = .ok ()) {l : D} (hl : l ∈ pkg.toList ++ laws) :
    Lang.judgeOne bytesOf digestOf look l old new r = .ok () := by
  unfold Lang.judge at h
  cases pkg with
  | none =>
      simp only [Option.toList_none, List.nil_append] at hl
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i v hf
        refine Lang.forIn_yield_ok (fun l => Lang.judgeOne bytesOf digestOf look l old new r = .ok ()) laws _
          (fun a u s hs => ?_) (by cases v; exact hf) l hl
        split at hs
        · cases hs
        · rename_i v' hv
          simp only [Except.ok.injEq] at hs
          exact ⟨hs.symm, by cases v'; exact hv⟩
  | some q =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        simp only [Option.toList_some, List.cons_append, List.mem_cons] at hl
        rcases hl with rfl | hl
        · cases v; exact hv
        · split at h
          · cases h
          · rename_i v₂ hf
            refine Lang.forIn_yield_ok (fun l => Lang.judgeOne bytesOf digestOf look l old new r = .ok ()) laws _
              (fun a u s hs => ?_) (by cases v₂; exact hf) l hl
            split at hs
            · cases hs
            · rename_i v' hv'
              simp only [pure, Except.pure, Except.ok.injEq] at hs
              exact ⟨hs.symm, by cases v'; exact hv'⟩

omit [Ord D] [DecidableEq D] in
private theorem reqData_occasion (bytesOf : D → ByteArray) (r : Req D) :
    (Lang.reqData bytesOf r).field "occasion" = some (Lang.occasionData bytesOf r.occasion) := by
  simp [Lang.reqData, Lang.Data.field, Lang.Row.find?]

omit [Ord D] [DecidableEq D] in
/-- A request whose occasion field is a `relaw` or an `adopt` injection IS a law change or adoption. -/
private theorem occasion_relaw {bytesOf : D → ByteArray} {r : Req D} {ℓ : Lang.Label} {x : Lang.Data}
    (h : (Lang.reqData bytesOf r).field "occasion" = some (.inj ℓ x)) (hℓ : ℓ = "relaw" ∨ ℓ = "adopt") :
    ∃ ls, r.occasion = .relaw ls ∨ r.occasion = .adopt ls := by
  rw [reqData_occasion] at h
  cases ho : r.occasion with
  | relaw ls => exact ⟨ls, .inl rfl⟩
  | adopt ls => exact ⟨ls, .inr rfl⟩
  | birth => rw [ho] at h; simp [Lang.occasionData] at h; obtain ⟨rfl, -⟩ := h; rcases hℓ with h | h <;> exact absurd h (by decide)
  | write => rw [ho] at h; simp [Lang.occasionData] at h; obtain ⟨rfl, -⟩ := h; rcases hℓ with h | h <;> exact absurd h (by decide)
  | invoke m => rw [ho] at h; simp [Lang.occasionData] at h; obtain ⟨rfl, -⟩ := h; rcases hℓ with h | h <;> exact absurd h (by decide)

/-- **THE LIFT: a World's history around an object is a history of every law in force.** At a lawful
`Ctx` running the language (`Lang.program` over its own codec), take a law `t` that mentions no closure
package (field `ℓ` of the package `p`, a law's shape, as every stdlib law is). Along any
`ObjectHistory` in whose every judged step the law's id `law` is among the judging laws (the package
or the cell's laws) and reads as `p` in that step's view, from a live object whose state reads `o`:
the judged steps are a `Std.Chain (Std.Step [] t)` from `o`, step for step (each step's request is
the judge's request as data, its new state the judged new slots as read), under every lib. A
non-judged step changes nothing the chain sees (`object_step_none`); a judged step's old state is
the live one and its new state the next live one, key by key (`object_step_some`), so the steps
link. No premise but the history and the law in force: no typing (`judgeOne_admits_relib` takes none),
no canonicity (a write step carries its cell's), no order law (a nested step carries it). -/
theorem object_history_chain {rc : Lang.ReceiptCheck} {X : Ctx D} (hX : X.Lawful) (hprog : X.program = Lang.program X.env.bytes X.digestOf rc)
    {obj law : D} {p : Lang.Package} {fs : List (Lang.Label × Lang.Term)} {ℓ : Lang.Label} {t : Lang.Term}
    (hb : p.body = .record fs) (hℓ : ℓ ∈ p.laws) (hf : Lang.Row.find? ℓ fs = some t) (hlaw : Lang.IsLaw t)
    (hnr : Lang.NoRef t) :
    ∀ {w w' : World D} {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))},
      ObjectHistory X obj w w' tr →
      (∀ e ∈ tr, law ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 law = .ok p) →
      ∀ {cell : Cell} {o : Lang.Data}, w.live X.env obj = some cell →
        Lang.readState X.digestOf (Lang.recordRow p.state) (stateOf cell) = .ok o →
        ∃ steps, Lang.Std.Chain (Lang.Std.Step [] t) o steps ∧
          tr.map (fun e => (Lang.reqData X.env.bytes e.2.2.2.1,
            Lang.readState X.digestOf (Lang.recordRow p.state) e.2.2.2.2.2.1)) =
            steps.map (fun s => (s.1, .ok s.2)) := by
  intro w w' tr h
  induction h with
  | nil w => exact fun _ _ o _ _ => ⟨[], .nil o, rfl⟩
  | @cons w w₁ w' e rest hs _ ih =>
      intro hin cell o hl ho
      cases e with
      | none => exact ih hin ((object_step_none hs).trans hl) ho
      | some x =>
          obtain ⟨look, pkg, laws, r, old, new, calls⟩ := x
          obtain ⟨hold, hj, hkeep, -, -, cell', hl', hk⟩ := object_step_some hs hl
          obtain ⟨hmem, hpk⟩ := hin _ (List.mem_cons_self ..)
          rw [hprog] at hj
          have hj' : Lang.judgeContextual X.env.bytes X.digestOf look pkg laws old new r = .ok () := hj
          have hj1 := Lang.judgeContextual_mem hj' hmem
          obtain ⟨o', n, ho', hn, hall⟩ :=
            Lang.judgeOneContextual_admits_relib X.env.bytes X.digestOf (hX.digestOf_bytes law) hpk hb hj1
          rw [hold, ho] at ho'
          cases ho'
          have hadm := hall ℓ hℓ t hf hlaw hnr []
          have hn' : Lang.readState X.digestOf (Lang.recordRow p.state) (stateOf cell') = .ok n :=
            (Lang.readState_get hk).trans hn
          obtain ⟨steps, hch, hfa⟩ := ih (fun e he => hin e (List.mem_cons_of_mem _ he)) hl' hn'
          refine ⟨(Lang.reqData X.env.bytes r, n) :: steps, .cons ⟨hadm, fun ℓ' x' hocc hℓ' => ?_⟩ hch,
            by simp only [Option.toList_some, List.singleton_append, List.map_cons, hn, hfa]⟩
          obtain ⟨ls, hls⟩ := occasion_relaw hocc hℓ'
          have hno := hkeep ls hls
          rw [hno, hold, ho] at hn
          cases hn
          rfl

/-- **What each judged step ran.** Along an `ObjectHistory`, a step judged by no package (a write, a
law) returned no calls; a step judged by a package `q` (an invoke, signed or nested) is a run of
`q`, in the step's view, from the step's old state to its new state, of the method its request
names, returning the step's calls. -/
theorem object_history_runs {X : Ctx D} {obj : D} :
    ∀ {w w' : World D} {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))},
      ObjectHistory X obj w w' tr → ∀ e ∈ tr, (e.2.1 = none → e.2.2.2.2.2.2 = []) ∧
        ∀ q, e.2.1 = some q → ∃ rv method args fuel rows used, e.2.2.2.1.occasion = .invoke method ∧
          X.program.run e.1 rv q e.2.2.2.2.1 method args e.2.2.2.1 fuel = .ok (e.2.2.2.2.2.1, e.2.2.2.2.2.2, rows, used) := by
  intro w w' tr h
  induction h with
  | nil => simp
  | @cons w w₁ w' e rest hs _ ih =>
      intro x hx
      cases e with
      | none => exact ih x hx
      | some y =>
          rcases List.mem_cons.mp hx with rfl | hx
          · obtain ⟨look, pkg, laws, r, old, new, calls⟩ := x
            obtain ⟨cell, hl⟩ := object_step_live hs
            obtain ⟨hold, -, -, hn, hq, -⟩ := object_step_some hs hl
            exact ⟨hn, hq⟩
          · exact ih x hx

/-- **A history with a judged step starts from a state the law reads.** Under the lift's premises,
an `ObjectHistory` with a judged step starts at a World holding the object live, with a state that
reads, at the package's state type, as data. -/
theorem object_history_start {rc : Lang.ReceiptCheck} {X : Ctx D} (hX : X.Lawful) (hprog : X.program = Lang.program X.env.bytes X.digestOf rc)
    {obj law : D} {p : Lang.Package} :
    ∀ {w w' : World D} {tr : List (Pinned D × Option D × List D × Req D × Slots × Slots × List (Body D))},
      ObjectHistory X obj w w' tr →
      (∀ e ∈ tr, law ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 law = .ok p) → tr ≠ [] →
      ∃ cell o, w.live X.env obj = some cell ∧ Lang.readState X.digestOf (Lang.recordRow p.state) (stateOf cell) = .ok o := by
  intro w w' tr h
  induction h with
  | nil => intro _ hne; exact absurd rfl hne
  | @cons w w₁ w' e rest hs _ ih =>
      intro hin hne
      cases e with
      | none =>
          obtain ⟨cell, o, hl, ho⟩ := ih hin hne
          exact ⟨cell, o, (object_step_none hs).symm.trans hl, ho⟩
      | some x =>
          obtain ⟨look, pkg, laws, r, old, new, calls⟩ := x
          obtain ⟨cell, hl⟩ := object_step_live hs
          obtain ⟨hold, hj, -⟩ := object_step_some hs hl
          obtain ⟨hmem, hpk⟩ := hin _ (List.mem_cons_self ..)
          rw [hprog] at hj
          have hj' : Lang.judgeContextual X.env.bytes X.digestOf look pkg laws old new r = .ok () := hj
          obtain ⟨L, g, p', o, n, hload, hpg, ho, -, -⟩ := Lang.judgeOneContextual_ok X.env.bytes X.digestOf (Lang.judgeContextual_mem hj' hmem)
          obtain ⟨hpg', -⟩ := Lang.loadContextual_top X.env.bytes X.digestOf (fuel := Lang.closureDepthMax - 1)
            (hX.digestOf_bytes law) hpk hload
          rw [hpg'] at hpg
          cases hpg
          exact ⟨cell, o, hl, hold ▸ ho⟩

end Nanodregg.Kernel.Receive
