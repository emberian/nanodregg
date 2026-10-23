/-
# Lang.Proofs.StdHead — what the head law admits (E5, L2–L6)

Over the reference semantics, never by evaluating the term. An admitted write or invoke of a
`Std.headPackage` object:
* keeps `world` (`head_world_fixed`, L6);
* from `at` to `at`: the step count never falls, an equal step count keeps the height and roots,
  the height never falls (`head_at_at`: L2 `forkedHead`, L4 `staleHead` / `badHead`);
* from `at` to `forked`: names the held roots at the held step count, with other roots
  (`head_at_fork`, L5);
* from `forked`: changes nothing (`head_forked_frozen`, L3).
The states are data at `headStateTy` with their scalars in the language's bounds (what `readState`
reads: `readState_conforms`).
-/
import Lang.StdHead
import Lang.Proofs.Std

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

variable {lib : List Term}

/-- The scalars of an `at` head are in the language's bounds. -/
def AtOk (h : Nat) (r : ByteArray) (s : Nat) : Prop :=
  h < Bounds.natLimit ∧ r.size ≤ Bounds.digestBytesMax ∧ s < Bounds.natLimit

theorem atRec_conforms {h : Nat} {r : ByteArray} {s : Nat} (hk : AtOk h r s) :
    Conforms (atRec h r s) headAtTy :=
  .record (.cons (.nat hk.1) (.cons (.digest hk.2.1) (.cons (.nat hk.2.2) .nil)))

theorem case_scrut {env : Env} {i : Nat} {d : Data} {f : Label} {ℓ : Label} {w : Val}
    (hi : env[i]? = some d.toVal) (h : BigStep lib env (.get (.var i) f) (.ok (.inj ℓ w))) :
    ∃ y, d.field f = some (.inj ℓ y) ∧ w = y.toVal := by
  obtain ⟨x, hx, hv⟩ := bigStep_getVar hi h
  obtain ⟨y, rfl, rfl⟩ := Data.toVal_inj hv.symm
  exact ⟨y, hx, rfl⟩

/-- An admitted change kept `world` and ran the head's case with `new` at 2 and `old` at 3. -/
theorem head_change_case {rq n o occ : Data} (h : Admits lib headLaw rq n o)
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ) :
    (∃ s, o.field "world" = some (.digest s) ∧ n.field "world" = some (.digest s)) ∧
      ∃ env w, env[2]? = some n.toVal ∧ env[3]? = some o.toVal ∧
        BigStep lib env (headCase ⟨1⟩) (.ok (.inj "ok" w)) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [headLaw, lawOf, lawBody] at hb
  obtain ⟨x, hx⟩ := lawCase_change rfl ho hc hb
  simp only [headChange, At.oldF, At.newF, At.old, At.new] at hx
  obtain ⟨hd, hr⟩ := guard_ok hx
  obtain ⟨a, b, ha, hb', hp⟩ := bigStep_prim_ok hd
  obtain ⟨s, t, rfl, rfl, hst⟩ := primEval_deq_bool hp
  have h1 := getVar_digest (d := o) (i := 3) rfl ha
  have h2 := getVar_digest (d := n) (i := 2) rfl hb'
  simp only [decide_eq_true_eq] at hst
  subst hst
  exact ⟨⟨s, h1, h2⟩, _, _, rfl, rfl, hr⟩

/-- **L6**: an admitted change never changes `world`. -/
theorem head_world_fixed {rq occ : Data} {hd hd' : Data} {w w' : ByteArray}
    (h : Admits lib headLaw rq (headSt hd' w') (headSt hd w))
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ) : w' = w := by
  obtain ⟨⟨s, h1, h2⟩, -⟩ := head_change_case h ho hc
  simp [headSt, Data.field, Row.find?] at h1 h2
  rw [h1, h2]

/-- **L2 + L4**: from an `at` head to an `at` head, an admitted change never lowers the step count
(`staleHead`), keeps the head at an equal step count (`forkedHead`), and never lowers the height
(`badHead`). -/
theorem head_at_at {rq occ : Data} {h h' s s' : Nat} {r r' w w' : ByteArray}
    (hA : Admits lib headLaw rq (headSt (.inj "at" (atRec h' r' s')) w') (headSt (.inj "at" (atRec h r s)) w))
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ)
    (hk : AtOk h r s) (hk' : AtOk h' r' s') :
    s ≤ s' ∧ (s = s' → h = h' ∧ r = r') ∧ h ≤ h' := by
  obtain ⟨-, env, v, h2, h3, hcase⟩ := head_change_case hA ho hc
  simp only [headCase, At.oldF, At.old, At.under, At.newF, At.new] at hcase
  obtain ⟨ℓ, u, body, hs, hf, hb⟩ := bigStep_case_ok hcase
  obtain ⟨y, hy, rfl⟩ := case_scrut h3 hs
  simp [headSt, Data.field, Row.find?] at hy
  obtain ⟨rfl, rfl⟩ := hy
  simp only [Row.find?, if_true, Option.some.injEq] at hf
  subst hf
  obtain ⟨ℓ2, u2, body2, hs2, hf2, hb2⟩ := bigStep_case_ok hb
  obtain ⟨y2, hy2, rfl⟩ := case_scrut (i := 3) (d := headSt (.inj "at" (atRec h' r' s')) w') (by simpa using h2) hs2
  simp [headSt, Data.field, Row.find?] at hy2
  obtain ⟨rfl, rfl⟩ := hy2
  simp only [Row.find?, if_true, Option.some.injEq] at hf2
  subst hf2
  simp only [headAtAt] at hb2
  obtain ⟨hall, -⟩ := guards_ok hb2
  have g1 := hall _ (List.mem_cons_self ..)
  have g2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have g3 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only at g1 g2 g3
  -- steps
  obtain ⟨a1, b1, ha1, hb1, hp1⟩ := bigStep_prim_ok g1
  obtain ⟨m1, n1, rfl, rfl, hle1⟩ := primEval_le_true hp1
  have e1 := getVar_nat (d := atRec h r s) (i := 1) rfl ha1
  have e1' := getVar_nat (d := atRec h' r' s') (i := 0) rfl hb1
  simp [atRec, Data.field, Row.find?] at e1 e1'
  subst e1 e1'
  -- height
  obtain ⟨a3, b3, ha3, hb3, hp3⟩ := bigStep_prim_ok g3
  obtain ⟨m3, n3, rfl, rfl, hle3⟩ := primEval_le_true hp3
  have e3 := getVar_nat (d := atRec h r s) (i := 1) rfl ha3
  have e3' := getVar_nat (d := atRec h' r' s') (i := 0) rfl hb3
  simp [atRec, Data.field, Row.find?] at e3 e3'
  subst e3 e3'
  refine ⟨by omega, fun hss => ?_, by omega⟩
  -- an equal step count: the comparison ran and returned true
  rcases bigStep_ite_ok g2 with ⟨_, heq⟩ | ⟨hf, -⟩
  · have hd := (eqData_true (T := headAtTy) (dx := atRec h r s) (dy := atRec h' r' s') (by decide)
      (.var rfl) (.var rfl) heq (atRec_conforms hk) (atRec_conforms hk')).mp rfl
    simp [atRec] at hd
    exact ⟨hd.1, hd.2.1⟩
  · obtain ⟨a2, b2, ha2, hb2', hp2⟩ := bigStep_prim_ok hf
    obtain ⟨m2, n2, rfl, rfl, hd2⟩ := primEval_eq_bool hp2
    have e2 := getVar_nat (d := atRec h r s) (i := 1) rfl ha2
    have e2' := getVar_nat (d := atRec h' r' s') (i := 0) rfl hb2'
    simp [atRec, Data.field, Row.find?] at e2 e2'
    subst e2 e2'
    simp [hss] at hd2


theorem getVar_head {env : Env} {i : Nat} {hd : Data} {w : ByteArray} (hi : env[i]? = some (headSt hd w).toVal) :
    BigStep lib env (.get (.var i) "head") (.ok hd.toVal) :=
  .get (.var hi) (.field (t := .var 0) (env := [hd.toVal]) (by simp [Data.toVal, Data.rowToVal, Row.find?])
    (.var rfl))

/-- **L3**: a recorded fork never changes (`forkedHead`): an admitted change from a `forked` head
keeps it, at data of the head's type. -/
theorem head_forked_frozen {rq occ : Data} {f hd' : Data} {w w' : ByteArray}
    (hA : Admits lib headLaw rq (headSt hd' w') (headSt (.inj "forked" f) w))
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ)
    (hf : Conforms (.inj "forked" f) headTy) (hn : Conforms hd' headTy) :
    hd' = .inj "forked" f := by
  obtain ⟨-, env, v, h2, h3, hcase⟩ := head_change_case hA ho hc
  simp only [headCase, At.oldF, At.old, At.under, At.newF, At.new] at hcase
  obtain ⟨ℓ, u, body, hs, hfd, hb⟩ := bigStep_case_ok hcase
  obtain ⟨y, hy, rfl⟩ := case_scrut h3 hs
  simp [headSt, Data.field, Row.find?] at hy
  obtain ⟨rfl, rfl⟩ := hy
  simp [Row.find?] at hfd
  subst hfd
  obtain ⟨heq, -⟩ := guard_ok hb
  exact ((eqData_true (T := headTy) (dx := .inj "forked" f) (dy := hd') (by decide)
    (getVar_head (i := 4) (w := w) (by simpa using h3)) (getVar_head (i := 3) (w := w') (by simpa using h2))
    heq hf hn).mp rfl).symm

/-- **L5**: a recorded fork names the held roots at the held step count, with other roots. -/
theorem head_at_fork {rq occ : Data} {h s s' : Nat} {r held other w w' : ByteArray}
    (hA : Admits lib headLaw rq (headSt (.inj "forked" (forkRec held other s')) w') (headSt (.inj "at" (atRec h r s)) w))
    (ho : rq.field "occasion" = some occ) (hc : IsChange occ) :
    held = r ∧ s' = s ∧ other ≠ r := by
  obtain ⟨-, env, v, h2, h3, hcase⟩ := head_change_case hA ho hc
  simp only [headCase, At.oldF, At.old, At.under, At.newF, At.new] at hcase
  obtain ⟨ℓ, u, body, hs, hf, hb⟩ := bigStep_case_ok hcase
  obtain ⟨y, hy, rfl⟩ := case_scrut h3 hs
  simp [headSt, Data.field, Row.find?] at hy
  obtain ⟨rfl, rfl⟩ := hy
  simp only [Row.find?, if_true, Option.some.injEq] at hf
  subst hf
  obtain ⟨ℓ2, u2, body2, hs2, hf2, hb2⟩ := bigStep_case_ok hb
  obtain ⟨y2, hy2, rfl⟩ := case_scrut (i := 3) (d := headSt (.inj "forked" (forkRec held other s')) w') (by simpa using h2) hs2
  simp [headSt, Data.field, Row.find?] at hy2
  obtain ⟨rfl, rfl⟩ := hy2
  simp [Row.find?] at hf2
  subst hf2
  simp only [headAtFork] at hb2
  have hall := allOf_ok hb2
  have g1 := hall _ (List.mem_cons_self ..)
  have g2 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have g3 := hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only at g1 g2 g3
  obtain ⟨a1, b1, ha1, hb1, hp1⟩ := bigStep_prim_ok g1
  obtain ⟨x1, y1, rfl, rfl, hd1⟩ := primEval_deq_bool hp1
  have e1 := getVar_digest (d := forkRec held other s') (i := 0) rfl ha1
  have e1' := getVar_digest (d := atRec h r s) (i := 1) rfl hb1
  simp [forkRec, atRec, Data.field, Row.find?] at e1 e1'
  obtain ⟨a2, b2, ha2, hb2', hp2⟩ := bigStep_prim_ok g2
  obtain ⟨x2, y2', rfl, rfl, hd2⟩ := primEval_eq_bool hp2
  have e2 := getVar_nat (d := forkRec held other s') (i := 0) rfl ha2
  have e2' := getVar_nat (d := atRec h r s) (i := 1) rfl hb2'
  simp [forkRec, atRec, Data.field, Row.find?] at e2 e2'
  have g3' := notT_true g3
  obtain ⟨a3, b3, ha3, hb3, hp3⟩ := bigStep_prim_ok g3'
  obtain ⟨x3, y3, rfl, rfl, hd3⟩ := primEval_deq_bool hp3
  have e3 := getVar_digest (d := forkRec held other s') (i := 0) rfl ha3
  have e3' := getVar_digest (d := atRec h r s) (i := 1) rfl hb3
  simp [forkRec, atRec, Data.field, Row.find?] at e3 e3'
  subst e1 e1' e2 e2' e3 e3'
  simp at hd1 hd2 hd3
  exact ⟨hd1, hd2, hd3⟩

end Nanodregg.Lang.Std
