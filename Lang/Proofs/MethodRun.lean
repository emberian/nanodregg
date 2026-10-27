/-
# Lang.Proofs.MethodRun — running one method of a loaded package, forward (HOSTING-44)

The steps every run-grain theorem about a specific method takes, stated once:

* `runMeasured_inv`: `runMeasured`'s do-block inverted (the setup, the machine's value, the
  extracted result, its calls and its edits, the row acts);
* `apply4_method`: the receiver's application `apply4 g ℓ`, at a closure body whose field `ℓ` is a
  method term with no closure reference, runs that method's body over `[req, arg, state, rows]`;
  `apply4_method_iff`: and ends in nothing else;
* `get_data`: selecting a field of data put into the machine means the field's data;
* `means_toVal`: data conforming to a type means itself there.

The offer's proofs (`Lang.Proofs.StdOffer`, `StdOfferFuse`, `StdOfferEscrow`) use these.
-/
import Lang.Proofs.Extract
import Lang.Proofs.Rel

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem find_rowToVal_of {ℓ : Label} : ∀ {fs : List (Label × Data)} {x : Data},
    Row.find? ℓ fs = some x → Row.find? ℓ (Data.rowToVal fs) = some (.var 0, [x.toVal])
  | [], _, h => by simp [Row.find?] at h
  | (k, d) :: fs, x, h => by
    by_cases hk : ℓ = k
    · subst hk; simp only [Row.find?, if_true, Option.some.injEq] at h; subst h
      simp [Data.rowToVal, Row.find?]
    · simp only [Row.find?, hk, if_false] at h
      simp only [Data.rowToVal, Row.find?, hk, if_false]
      exact find_rowToVal_of h

/-- Selecting field `ℓ` of a term whose value is data `d` means `d`'s field. -/
theorem get_data {lib : List Term} {env : Env} {t : Term} {d x : Data} {ℓ : Label}
    (ht : BigStep lib env t (.ok d.toVal)) (hf : d.field ℓ = some x) :
    BigStep lib env (.get t ℓ) (.ok x.toVal) := by
  cases d with
  | record fs => exact .get ht (.field (find_rowToVal_of hf) (.var rfl))
  | _ => simp [Data.field] at hf

theorem find_suspend_of {ℓ : Label} {env : Env} : ∀ {fs : List (Label × Term)} {t : Term},
    Row.find? ℓ fs = some t → Row.find? ℓ (suspend env fs) = some (t, env)
  | [], _, h => by simp [Row.find?] at h
  | (k, u) :: fs, t, h => by
    by_cases hk : ℓ = k
    · subst hk; simp only [Row.find?, if_true, Option.some.injEq] at h; subst h
      simp [suspend, Row.find?]
    · simp only [Row.find?, hk, if_false] at h
      have := find_suspend_of (env := env) h
      simpa [suspend, Row.find?, hk] using this

/-- **The receiver's application runs the method's body**: at a closure body (`lib[g]`, the package
body relocated) whose field `ℓ` is a method term `λ rows. λ state. λ arg. λ req. body` naming no
closure package, `apply4 g ℓ` over `[req, arg, state, rows]` ends as `body` does there. -/
theorem apply4_method {lib : List Term} {g : Nat} {f : Nat → Nat} {pb : Term}
    {fs : List (Label × Term)} {ℓ : Label} {R S A Q : Ty} {body : Term} {req arg state rows : Val}
    {r : Except Fault Val}
    (hlib : lib[g]? = some (pb.relocate f)) (hb : pb = .record fs)
    (hf : Row.find? ℓ fs = some (.lam R (.lam S (.lam A (.lam Q body)))))
    (hn : NoRef (Term.lam R (.lam S (.lam A (.lam Q body)))))
    (h : BigStep lib [req, arg, state, rows] body r) :
    BigStep lib [req, arg, state, rows] (apply4 g ℓ) r := by
  subst hb
  have hrel : (Term.record fs).relocate f = .record (Term.relocateRow f fs) := by simp [Term.relocate]
  rw [hrel] at hlib
  have hf' : Row.find? ℓ (Term.relocateRow f fs) = some (.lam R (.lam S (.lam A (.lam Q body)))) := by
    rw [find_relocateRow, hf, Option.map_some, relocate_noRef f _ hn]
  have hget : BigStep lib [req, arg, state, rows] (.get (.ref g) ℓ)
      (.ok (.clo (.lam S (.lam A (.lam Q body))) [])) :=
    .get (.ref hlib .record) (.field (find_suspend_of hf') .lam)
  unfold apply4
  exact .app (.app (.app (.app hget (.var rfl) .lam) (.var rfl) .lam) (.var rfl) .lam) (.var rfl) h

/-- **The receiver's application ends exactly as the body does**: at `apply4_method`'s premises, with
the body's result `r` fixed, `apply4 g ℓ` ends in `r'` iff `r' = r` (`bigStep_deterministic`). So a
statement of what the body returns is a statement of what the receiver's application returns. -/
theorem apply4_method_iff {lib : List Term} {g : Nat} {f : Nat → Nat} {pb : Term}
    {fs : List (Label × Term)} {ℓ : Label} {R S A Q : Ty} {body : Term} {req arg state rows : Val}
    {r : Except Fault Val}
    (hlib : lib[g]? = some (pb.relocate f)) (hb : pb = .record fs)
    (hf : Row.find? ℓ fs = some (.lam R (.lam S (.lam A (.lam Q body)))))
    (hn : NoRef (Term.lam R (.lam S (.lam A (.lam Q body)))))
    (h : BigStep lib [req, arg, state, rows] body r) :
    ∀ r', BigStep lib [req, arg, state, rows] (apply4 g ℓ) r' ↔ r' = r :=
  fun _ => ⟨fun h' => bigStep_deterministic h' (apply4_method hlib hb hf hn h),
    fun e => e ▸ apply4_method hlib hb hf hn h⟩

/-- `runMeasured`'s do-block inverted, with the calls conjunct (`runMeasuredWith_ok` with `callsOf`). -/
theorem runMeasured_inv {D : Type} [DecidableEq D] {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots}
    {method : Nat} {args : ByteArray} {r : Req D} {budget : Nat} {s : Slots}
    {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {t n : Nat}
    (h : runMeasured bytesOf digestOf rc look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ S v used c e ds left es, runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S ∧
      run S.lib Bounds.stackMax (budget - S.preparation) 0 (State.init S.term S.env) = .value v used ∧
      (Machine.mk S.lib).extract S.ty (budget - S.preparation - used) v =
        .ok (.record [("calls", c), ("edits", e), ("state", .record ds)], left) ∧
      callsOf digestOf S.calls c = .ok calls ∧ editsOf S.rels r.self e = .ok es ∧
      rows = es.map (fun x => (x.slot, x.act)) := by
  unfold runMeasured runMeasuredWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i v used hrun
  split at h
  all_goals first | (simp at h; done) | skip
  rename_i c e ds left hx
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl, -, -⟩ := h
  exact ⟨S, v, used, c, e, ds, left, _, hS, hrun, hx, ‹callsOf _ _ _ = .ok _›, ‹editsOf _ _ _ = .ok _›, rfl⟩

mutual
/-- Data conforming to a type means itself there. -/
theorem means_toVal {lib : List Term} : ∀ {d : Data} {T : Ty}, Conforms d T → Means lib T d.toVal d
  | _, _, .nat _ => .nat
  | _, _, .bool => .bool
  | _, _, .bytes _ => .bytes
  | _, _, .digest _ => .digest
  | _, _, .record h => .record .record (rowMeans_toVal h)
  | _, _, .inj hf h => .inj hf (means_toVal h)

theorem rowMeans_toVal {lib : List Term} : ∀ {ds : List (Label × Data)} {r : List (Label × Ty)},
    RowConforms ds r → RowMeans lib r (Data.rowToVal ds) ds
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (.var rfl) (means_toVal h) (rowMeans_toVal hs)
end

end Nanodregg.Lang
