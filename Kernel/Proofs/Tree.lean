/-
# Kernel.Proofs.Tree — a call's tree of receivers (D5c, KERNEL-28, LEDGER-8)

* `invoke_ok`: an admitted invoke spent the owner's authority (as `actor`), ran the program on
  what the pool had left, its used ticks within that (`overTicks` otherwise), returned at most
  `callsMax` calls, and derived each of them by `sub` AS THE OBJECT, from a walk that has the
  object visited and the used ticks spent.
* `effect_as_signed` (KERNEL-28 (b)): a call of the tree derives exactly as the same Body signed
  at top level would, with the calling object as the actor: the deriver one level down is
  `dispatch` itself, the receiver the signed call goes through, and a kind an object may not
  exercise is `notCallable`.
* `visit_distinct`: the objects a tree invokes are pairwise distinct (re-entry is `revisited`).
* `derive_all`: any property of Drafts closed under concatenation, held by every receiver's own
  Draft and by an invoke's own state write, holds of the whole tree's Draft (how `dispatch_born`,
  `dispatch_value_born` and the authority theorems reach every effect).
-/
import Kernel.Proofs.Receive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [DecidableEq D]

/-- **An invoke, unfolded.** -/
theorem invoke_ok {X : Ctx D} {look : Pinned D} {c : Call D} {sub : Sub D} {wk : Walk D}
    {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {r : Draft D × Walk D}
    (h : invoke X look c sub wk actor obj method args budget via = .ok r) :
    obj ∉ wk.visited ∧ ∃ cell p rq new calls used,
      invokeRun X look c actor obj method via = .ok (cell, p, rq) ∧
      X.program.run look p (stateOf cell) method args rq (min budget wk.pool) = .ok (new, calls, used) ∧
      used ≤ min budget wk.pool ∧ calls.length ≤ Bounds.callsMax ∧
      deriveCalls sub obj ⟨[], writeOf obj (diffOps (stateOf cell) new), []⟩
        { wk with visited := obj :: wk.visited, pool := wk.pool - used } calls = .ok r := by
  unfold invoke at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, hv, ⟨cell, p, rq⟩, hrun, ⟨new, calls, used⟩, hp, ⟨⟩, hu, ⟨⟩, _, laws, _, ⟨⟩, _, ⟨⟩, hc, h⟩ := h
  rw [req_ok] at hv
  rw [req_ok, decide_eq_true_eq] at hu hc
  refine ⟨by simpa using hv, cell, p, rq, new, calls, used, hrun, hp, hu, hc, h⟩

omit [DecidableEq D] in
/-- A receiver that derives alone: its Draft, and the walk moved past its births. -/
theorem stepped_draft {wk : Walk D} {d : Except (Refusal D) (Draft D)} {r : Draft D × Walk D}
    (h : stepped wk d = .ok r) : d = .ok r.1 := by
  unfold stepped at h
  cases d with
  | error e => cases h
  | ok d => simp only [Except.map, Except.ok.injEq] at h; subst h; rfl

/-- The deriver one level down, by name: past the depth bound `callTooDeep`; otherwise a callable
Body goes through `dispatch`, and any other is `notCallable`. -/
theorem tree_succ {X : Ctx D} {look : Pinned D} {c : Call D} {n : Nat} {wk : Walk D} {obj : D}
    {b : Body D} :
    tree X look c (n + 1) wk obj b =
      if b.callable then dispatch X look c (tree X look c n) wk obj b
      else .error (.notCallable b.kindName) := rfl

/-- **Effects are derived as signed** (KERNEL-28 (b)). A call that the tree derives is a callable
Body, and its Draft is exactly `dispatch`'s for that Body with the calling object as the actor:
the derivation a signed call with that Body goes through, at the same walk. So an object's call
spends exactly the authority the object holds (`ownerAuthority` at the object), never the
signer's. -/
theorem effect_as_signed {X : Ctx D} {look : Pinned D} {c : Call D} {n : Nat} {wk : Walk D}
    {obj : D} {b : Body D} {r : Draft D × Walk D} (h : tree X look c n wk obj b = .ok r) :
    ∃ m, n = m + 1 ∧ b.callable = true ∧ dispatch X look c (tree X look c m) wk obj b = .ok r := by
  cases n with
  | zero => simp [tree] at h
  | succ m =>
      rw [tree_succ] at h
      split at h
      · exact ⟨m, rfl, by assumption, h⟩
      · cases h

omit [DecidableEq D] in
/-- A call's tree, folded: what holds of the Draft before, and of every call's Draft, holds of the
concatenation. -/
theorem foldCalls_all {P : Draft D → Prop} (hP : ∀ a b, P a → P b → P (a.append b)) {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → P r.1) {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D}, P acc.1 →
      calls.foldlM (callStep sub obj) acc = .ok r → P r.1
  | [], acc, r, ho, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ho
  | b :: rest, acc, r, ho, h => by
      rw [List.foldlM_cons] at h
      simp only [except_bind_ok] at h
      obtain ⟨s, hs1, h⟩ := h
      unfold callStep at hs1
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hs1
      obtain ⟨q, hq, rfl⟩ := hs1
      exact foldCalls_all hP hs rest _ (hP _ _ ho (hs _ _ _ _ hq)) h

/-- One receiver: an invoke contributes its own state write and its calls' Drafts; every other
kind its own Draft (`hbase`). -/
theorem dispatch_all {P : Draft D → Prop} (hP : ∀ a b, P a → P b → P (a.append b))
    (hown : ∀ obj ops, P ⟨[], writeOf obj ops, []⟩)
    {X : Ctx D} {look : Pinned D} {c : Call D} {Q : Body D → Prop}
    (hbase : ∀ (sub : Sub D) wk actor (b : Body D) r, Q b → b.isInvoke = false →
      dispatch X look c sub wk actor b = .ok r → P r.1)
    {sub : Sub D} (hs : ∀ wk a b r, sub wk a b = .ok r → P r.1)
    {wk : Walk D} {actor : D} {b : Body D} {r : Draft D × Walk D} (hq : Q b)
    (h : dispatch X look c sub wk actor b = .ok r) : P r.1 := by
  cases b with
  | invoke obj method args budget via =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hd⟩ := invoke_ok h
      exact foldCalls_all hP hs _ _ (hown _ _) hd
  | _ => exact hbase sub wk actor _ r hq rfl h

/-- Every level of the tree below the signed call: only CALLABLE receivers occur there, so a
property needs proving only of those (`hbase`). -/
theorem tree_all {P : Draft D → Prop} (hP : ∀ a b, P a → P b → P (a.append b))
    (hown : ∀ obj ops, P ⟨[], writeOf obj ops, []⟩)
    {X : Ctx D} {look : Pinned D} {c : Call D}
    (hbase : ∀ (sub : Sub D) wk actor (b : Body D) r, b.callable = true → b.isInvoke = false →
      dispatch X look c sub wk actor b = .ok r → P r.1) :
    ∀ n wk a b r, tree X look c n wk a b = .ok r → P r.1
  | 0, _, _, _, _, h => by simp [tree] at h
  | n + 1, wk, a, b, r, h => by
      obtain ⟨m, hm, hc, hd⟩ := effect_as_signed h
      have : m = n := by omega
      subst this
      exact dispatch_all (Q := fun b => b.callable = true) hP hown hbase (tree_all hP hown hbase m) hc hd

/-- **The whole tree.** A property of Drafts closed under concatenation, held by every
receiver's own Draft and by an invoke's own write, holds of a signed call's Draft. -/
theorem derive_all {P : Draft D → Prop} (hP : ∀ a b, P a → P b → P (a.append b))
    (hown : ∀ obj ops, P ⟨[], writeOf obj ops, []⟩)
    {X : Ctx D} {look : Pinned D} {c : Call D}
    (hbase : ∀ (sub : Sub D) wk actor (b : Body D) r, b.isInvoke = false →
      dispatch X look c sub wk actor b = .ok r → P r.1)
    {d : Draft D} (h : derive X look c = .ok d) : P d := by
  unfold derive at h
  cases hd : dispatch X look c (tree X look c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member c.unsigned.body with
  | error e => rw [hd] at h; cases h
  | ok r =>
      rw [hd] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      exact dispatch_all (Q := fun _ => True) hP hown (fun sub wk actor b r _ hi h => hbase sub wk actor b r hi h)
        (tree_all hP hown (fun sub wk actor b r _ hi h => hbase sub wk actor b r hi h) _) trivial hd

omit [DecidableEq D] in
theorem stepped_map {wk : Walk D} {d : Except (Refusal D) (Draft D)} :
    (stepped wk d).map (·.1) = d := by
  cases d <;> rfl

/-- The signed call's Draft, unfolded at the top: its Body's receiver at the signer, at walk
`⟨[], poolOf body, 0⟩`. -/
theorem derive_eq {X : Ctx D} {look : Pinned D} {c : Call D} :
    derive X look c = (dispatch X look c (tree X look c Bounds.callDepthMax) ⟨[], poolOf c.unsigned.body, 0⟩
      c.unsigned.member c.unsigned.body).map (·.1) := rfl

/-! ## Each object once -/

/-- What a walk does across a derivation: its visited list grows by a prefix and stays free of
repeats, and its tick pool never grows. -/
def Grows (wk : Walk D) (r : Draft D × Walk D) : Prop :=
  (∃ l, r.2.visited = l ++ wk.visited) ∧ (wk.visited.Nodup → r.2.visited.Nodup) ∧ r.2.pool ≤ wk.pool

omit [DecidableEq D] in
theorem foldCalls_grows {sub : Sub D} (hs : ∀ wk a b r, sub wk a b = .ok r → Grows wk r) {obj : D} :
    ∀ (calls : List (Body D)) (acc : Draft D × Walk D) {r : Draft D × Walk D},
      calls.foldlM (callStep sub obj) acc = .ok r → Grows acc.2 r
  | [], acc, r, h => by
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨⟨[], rfl⟩, id, Nat.le_refl _⟩
  | b :: rest, acc, r, h => by
      rw [List.foldlM_cons] at h
      simp only [except_bind_ok] at h
      obtain ⟨s, hs1, h⟩ := h
      unfold callStep at hs1
      simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hs1
      obtain ⟨q, hq, rfl⟩ := hs1
      obtain ⟨⟨l₁, h₁⟩, n₁, p₁⟩ := hs _ _ _ _ hq
      obtain ⟨⟨l₂, h₂⟩, n₂, p₂⟩ := foldCalls_grows hs rest _ h
      refine ⟨⟨l₂ ++ l₁, ?_⟩, fun hn => n₂ (n₁ hn), Nat.le_trans p₂ p₁⟩
      rw [h₂]; simp only at h₁ ⊢; rw [h₁, List.append_assoc]

omit [DecidableEq D] in
theorem stepped_walk {wk : Walk D} {d : Except (Refusal D) (Draft D)} {r : Draft D × Walk D}
    (h : stepped wk d = .ok r) : r.2.visited = wk.visited ∧ r.2.pool = wk.pool := by
  unfold stepped at h
  cases d with
  | error e => cases h
  | ok d => simp only [Except.map, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- An invoke records its object in the walk, and the calls it makes start from there. -/
theorem invoke_records {X : Ctx D} {look : Pinned D} {c : Call D} {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → Grows wk r) {wk : Walk D} {actor obj : D} {method : Nat}
    {args : ByteArray} {budget : Nat} {via : Option D} {r : Draft D × Walk D}
    (h : invoke X look c sub wk actor obj method args budget via = .ok r) :
    obj ∉ wk.visited ∧ obj ∈ r.2.visited ∧ Grows wk r := by
  obtain ⟨hfresh, _, _, _, _, _, used, _, _, _, _, hd⟩ := invoke_ok h
  obtain ⟨⟨l, hl⟩, hn, hp⟩ := foldCalls_grows hs _ _ hd
  simp only at hl hp
  refine ⟨hfresh, by rw [hl]; simp, ⟨⟨l ++ [obj], by rw [hl, List.append_assoc]; rfl⟩,
    fun hw => hn (List.nodup_cons.mpr ⟨hfresh, hw⟩), by omega⟩⟩

theorem dispatch_grows {X : Ctx D} {look : Pinned D} {c : Call D} {sub : Sub D}
    (hs : ∀ wk a b r, sub wk a b = .ok r → Grows wk r) {wk : Walk D} {actor : D} {b : Body D}
    {r : Draft D × Walk D} (h : dispatch X look c sub wk actor b = .ok r) : Grows wk r := by
  cases b with
  | invoke obj method args budget via => exact (invoke_records hs h).2.2
  | _ =>
      simp only [dispatch] at h
      obtain ⟨hv, hp⟩ := stepped_walk h
      exact ⟨⟨[], by rw [hv]; rfl⟩, fun hw => by rw [hv]; exact hw, by omega⟩

theorem tree_grows {X : Ctx D} {look : Pinned D} {c : Call D} :
    ∀ n wk a b r, tree X look c n wk a b = .ok r → Grows wk r
  | 0, _, _, _, _, h => by simp [tree] at h
  | n + 1, wk, a, b, r, h => by
      obtain ⟨m, hm, _, hd⟩ := effect_as_signed h
      have : m = n := by omega
      subst this
      exact dispatch_grows (tree_grows m) hd

/-- **Each object once** (`visit_distinct`). The objects a signed call's tree invokes, in the
order the walk visited them, are pairwise distinct: an invoke of an object already visited is
`revisited`, and every invoke records its object (the signed one among them). -/
theorem visit_distinct {X : Ctx D} {look : Pinned D} {c : Call D} {r : Draft D × Walk D}
    (h : dispatch X look c (tree X look c Bounds.callDepthMax) ⟨[], poolOf c.unsigned.body, 0⟩
      c.unsigned.member c.unsigned.body = .ok r) :
    r.2.visited.Nodup ∧
      ∀ obj method args budget via, c.unsigned.body = .invoke obj method args budget via → obj ∈ r.2.visited := by
  refine ⟨(dispatch_grows (tree_grows _) h).2.1 List.nodup_nil, fun obj method args budget via hb => ?_⟩
  rw [hb] at h
  exact (invoke_records (tree_grows _) h).2.1

/-- **One tick pool** (KERNEL-28 (c), LEDGER-8 (e)). Every run of a tree is given at most what the
pool has left (`invoke_ok`: `used ≤ min budget pool`, the pool then `pool - used`), the pool never
grows, and it starts at the signed budget capped at `treeTicksMax`: the ticks of all a call's runs
together are at most that. -/
theorem tree_pool {X : Ctx D} {look : Pinned D} {c : Call D} {r : Draft D × Walk D}
    (h : dispatch X look c (tree X look c Bounds.callDepthMax) ⟨[], poolOf c.unsigned.body, 0⟩
      c.unsigned.member c.unsigned.body = .ok r) :
    r.2.pool ≤ poolOf c.unsigned.body ∧ poolOf c.unsigned.body ≤ Bounds.treeTicksMax := by
  refine ⟨(dispatch_grows (tree_grows _) h).2.2, ?_⟩
  unfold poolOf
  split <;> omega

end Nanodregg.Kernel.Receive
