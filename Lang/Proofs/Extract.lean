/-
# Lang.Proofs.Extract — what extraction forces is the meaning: each field is its `get`'s value

`Machine.extract` forces a value into `Data` by running suspensions on the machine under a budget.
`Means lib T v d` says the same thing with no machine and no budget: `d` is what `v` MEANS at the
data type `T` under the reference semantics (`BigStep`, Lang.Proofs.BigStep) — a base value is its
own data; a record value unknots by its body's meaning (`Unrolls`) and each field's suspension means
a value whose data is the field's; an injection's payload means at its label's type.
It is the walk `Lang.Proofs.Need.Forces` makes: `Forces` is this relation with `Derives` sizes and
without the data, as `Derives` is `BigStep` with sizes (`means_forces` and
`forces_means` in `Lang.Proofs.Need`: one has an instance exactly when the other does).

* `extract_means`: whatever extraction returns, at any budget, is the meaning of the value
  (no premise: not typing, not a budget). `means_deterministic`: a value has at most one meaning
  at a type, so the extracted data is fixed by the reference semantics alone.
* `means_get` (the field lemma): if `t` means `v` and `v` means the record data `d` at `rec row`,
  then for each field `ℓ` of `d`, the data `d` holds at `ℓ` is the meaning, at `ℓ`'s type in `row`,
  of the value `.get t ℓ` means — for ANY derivation of `.get t ℓ`'s value (`BigStep` is
  deterministic), so a meaning computed another way (another evaluator, another budget, the
  reference run of a projection) fixes the extracted field. `means_get_exists`: that value exists;
  `means_field_exists`: every label of the row is a field of the data. `extract_get` composes it
  with `extract_means` for one machine extraction.
* `runMeasured_means`: the receiver's run of a method (`runMeasured`) extracted, at the method's
  own result type, the MEANING of the method application `apply4 g ℓ` under the loaded closure
  `L.lib`, in the run's environment (the request, arguments, state and rows data the setup read);
  its calls are `callsOf` of that meaning's `calls` field, its `state` field is a record conforming
  to the package's state row whose `stateSlots` there are the slots the run returned.
* `relib_apply4`: what the method application means does not depend on the closure beyond the
  package body: two libs holding one `NoRef` body at their indices give `apply4 g ℓ` and
  `apply4 g' ℓ` one meaning over every no-ref environment (`toVal4_noRef`: the receiver's is one).
  `Relib` composes through `get`, `app`, `case` (`relib_get`, `relib_app`, `relib_case`), so a
  projection a consumer computes under `[body]` at index 0 is the projection under `L.lib` at `g`
  (`load_top`, under its premises `digestOf (bytesOf pkg) = some pkg` and `readPackage look pkg = .ok p`,
  with `relocate_noRef` give `L.lib[g]? = some p.body` for a `NoRef` body). Underneath: `bigStep_relib`, a
  derivation of a no-ref term over a no-ref environment is one under every lib, and `means_relib`, a
  no-ref value's meaning is one under every lib.
* Teeth: `extract_get_tooth`: a record whose field is not its `get`'s meaning is never what
  extraction returns (a knot whose `g` is `self.a`, extracted with `g = 2`, at every budget);
  `extract_knot_ok`: the same value does extract, to `g = 1` (the premise is satisfiable).
  `relib_needs_one_body`: `ref 0` under `[1]` and under `[2]` mean differently, so `relib_ref`'s
  one-body premise is needed; `relib_needs_noRef`: one body `ref 1` at index 0 is not enough, so its
  `NoRef` premise is needed; `means_relib_needs_noRef`: a knot whose body is `ref 0` means `a = 1`
  under one lib and not under another. `run_state_tooth`: the `stateSlots` conjunct is not implied by
  the meaning: a field meaning `natLimit` at `nat` writes no slots.

The account step is not here: the data `.inj "of" {asset, owner}` reads as `AcctRef.of owner asset`
by `bodyOf` (`callData_bodyOf`, `bodyOf_callData`, needing `digestOf (bytesOf x) = some x`: Lang's
half, on main); `AcctRef.of o a` resolves to `accountId X o a` in `Kernel.Receive.Ledger` (KERNEL's,
by definition). A projection written over an INLINED method term (`methodAt`, the field term
applied in the run's environment, lib `[]`) is not `apply4`'s: the inlined field closes over the
run's environment where `.ref g` closes over `[]`, so the values differ while their data agree; a
consumer states its projection over `apply4 0 ℓ` under `[body]` and transfers it by `relib_apply4`.
-/
import Lang.Proofs.Agree
import Lang.Proofs.CallLive
import Lang.Proofs.Receiver
import Lang.Proofs.Canon

namespace Nanodregg.Lang

open Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {lib : List Term}

/-! ## The meaning of a value at a data type -/

/-- `v` unknots to the field suspensions `fs`: a record is its own fields; a knot unrolls by what
its body means with the knot as self (`Sel.knot`'s unrolling). -/
inductive Unrolls (lib : List Term) : Val → List (Label × (Term × Env)) → Prop
  | record {fs : List (Label × (Term × Env))} : Unrolls lib (.record fs) fs
  | knot {b : Term} {env : Env} {v : Val} {fs : List (Label × (Term × Env))} :
      BigStep lib (.knot b env :: env) b (.ok v) → Unrolls lib v fs → Unrolls lib (.knot b env) fs

mutual
/-- `d` is what `v` means at data type `T`, by the reference semantics: no machine, no budget. -/
inductive Means (lib : List Term) : Ty → Val → Data → Prop
  | nat {n : Nat} : Means lib .nat (.nat n) (.nat n)
  | bool {b : Bool} : Means lib .bool (.bool b) (.bool b)
  | bytes {s : ByteArray} : Means lib .bytes (.bytes s) (.bytes s)
  | digest {s : ByteArray} : Means lib .digest (.digest s) (.digest s)
  | record {row : List (Label × Ty)} {v : Val} {fs : List (Label × (Term × Env))} {ds : List (Label × Data)} :
      Unrolls lib v fs → RowMeans lib row fs ds → Means lib (.record row) v (.record ds)
  | inj {row : List (Label × Ty)} {ℓ : Label} {A : Ty} {w : Val} {d : Data} :
      Row.find? ℓ row = some A → Means lib A w d → Means lib (.sum row) (.inj ℓ w) (.inj ℓ d)

/-- Field by field, in row order: each suspension means a value, and that value means the field's
data at the field's type. -/
inductive RowMeans (lib : List Term) : List (Label × Ty) → List (Label × (Term × Env)) → List (Label × Data) → Prop
  | nil : RowMeans lib [] [] []
  | cons {ℓ : Label} {A : Ty} {row : List (Label × Ty)} {t : Term} {env : Env}
      {fs : List (Label × (Term × Env))} {w : Val} {d : Data} {ds : List (Label × Data)} :
      BigStep lib env t (.ok w) → Means lib A w d → RowMeans lib row fs ds →
      RowMeans lib ((ℓ, A) :: row) ((ℓ, (t, env)) :: fs) ((ℓ, d) :: ds)
end

/-! ## Extraction computes the meaning -/

theorem force_bigStep {m : Machine} {fuel : Nat} {t : Term} {env : Env} {v : Val} {f : Nat}
    (h : m.force fuel t env = .ok (v, f)) : BigStep m.lib env t (.ok v) := by
  unfold Machine.force at h
  split at h
  · rename_i v' used hv
    cases h
    exact run_bigStep hv
  · cases h

theorem unknot_unrolls {m : Machine} : ∀ {rounds fuel : Nat} {v : Val} {fs : List (Label × (Term × Env))} {f : Nat},
    m.unknot rounds fuel v = .ok (fs, f) → Unrolls m.lib v fs
  | rounds, fuel, .record fs', fs, f, h => by
    cases rounds <;> (simp only [Machine.unknot, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact .record)
  | 0, fuel, .knot b env, fs, f, h => by simp [Machine.unknot] at h
  | k + 1, fuel, .knot b env, fs, f, h => by
    simp only [Machine.unknot] at h
    split at h
    · rename_i v' fuel' hf
      exact .knot (force_bigStep hf) (unknot_unrolls h)
    · cases h
  | rounds, _, .nat _, _, _, h | rounds, _, .bool _, _, _, h | rounds, _, .bytes _, _, _, h
  | rounds, _, .digest _, _, _, h | rounds, _, .clo _ _, _, _, h | rounds, _, .inj _ _, _, _, h => by
    cases rounds <;> simp [Machine.unknot] at h

mutual
/-- **Extraction is the meaning**: whatever `extract` returns, at any budget, is what the value
means at the type. No typing premise: an ill-typed value does not extract (it is `stuck`). -/
theorem extract_means (m : Machine) : ∀ (T : Ty) {fuel : Nat} {v : Val} {d : Data} {f : Nat},
    m.extract T fuel v = .ok (d, f) → Means m.lib T v d
  | .nat, _, v, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; exact .nat
  | .bool, _, v, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; exact .bool
  | .bytes, _, v, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; exact .bytes
  | .digest, _, v, _, _, h => by
    cases v <;> simp [Machine.extract] at h
    obtain ⟨rfl, -⟩ := h; exact .digest
  | .fn _ _, _, v, _, _, h => by cases v <;> simp [Machine.extract] at h
  | .record row, _, _, _, _, h => by
    simp only [Machine.extract] at h
    split at h
    · rename_i fs fuel' hu
      split at h
      · rename_i ds fuel'' hr
        cases h
        exact .record (unknot_unrolls hu) (extractRow_means m row hr)
      · cases h
    · cases h
  | .sum row, _, v, _, _, h => by
    cases v with
    | inj ℓ w =>
      simp only [Machine.extract] at h
      split at h
      · rename_i d' fuel' ha
        cases h
        obtain ⟨A, hf, hm⟩ := extractArm_means m row ha
        exact .inj hf hm
      · cases h
    | _ => simp [Machine.extract] at h

theorem extractArm_means (m : Machine) : ∀ (row : List (Label × Ty)) {ℓ : Label} {fuel : Nat} {w : Val}
    {d : Data} {f : Nat}, m.extractArm row ℓ fuel w = .ok (d, f) → ∃ A, Row.find? ℓ row = some A ∧ Means m.lib A w d
  | [], _, _, _, _, _, h => by simp [Machine.extractArm] at h
  | (k, B) :: row, ℓ, _, _, _, _, h => by
    simp only [Machine.extractArm] at h
    split at h
    · rename_i hk
      exact ⟨B, by simp [Row.find?, hk], extract_means m B h⟩
    · rename_i hk
      obtain ⟨A, hf, hm⟩ := extractArm_means m row h
      exact ⟨A, by simp [Row.find?, hk, hf], hm⟩

theorem extractRow_means (m : Machine) : ∀ (row : List (Label × Ty)) {fuel : Nat}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)} {f : Nat},
    m.extractRow row fuel fs = .ok (ds, f) → RowMeans m.lib row fs ds
  | [], _, fs, _, _, h => by
    cases fs <;> simp [Machine.extractRow] at h
    obtain ⟨rfl, -⟩ := h; exact .nil
  | (ℓ, A) :: row, _, fs, _, _, h => by
    cases fs with
    | nil => simp [Machine.extractRow] at h
    | cons y fs =>
      obtain ⟨ℓ', t, env⟩ := y
      simp only [Machine.extractRow] at h
      split at h
      · rename_i hl
        subst hl
        split at h
        · rename_i v fuel' hfo
          split at h
          · rename_i d fuel'' hx
            split at h
            · rename_i ds' f' hr
              cases h
              exact .cons (force_bigStep hfo) (extract_means m A hx) (extractRow_means m row hr)
            · cases h
          · cases h
        · cases h
      · cases h
end

/-! ## One meaning -/

theorem unrolls_deterministic : ∀ {v : Val} {fs fs' : List (Label × (Term × Env))},
    Unrolls lib v fs → Unrolls lib v fs' → fs = fs'
  | _, _, _, .record, h' => by cases h'; rfl
  | _, _, _, .knot hb hu, h' => by
    cases h' with
    | knot hb' hu' => cases bigStep_deterministic hb hb'; exact unrolls_deterministic hu hu'

mutual
/-- A value has at most one meaning at a type. -/
theorem means_deterministic : ∀ {T : Ty} {v : Val} {d d' : Data}, Means lib T v d → Means lib T v d' → d = d'
  | _, _, _, _, .nat, h' | _, _, _, _, .bool, h' | _, _, _, _, .bytes, h' | _, _, _, _, .digest, h' => by
    cases h'; rfl
  | _, _, _, _, .record hu hr, h' => by
    cases h' with
    | record hu' hr' => cases unrolls_deterministic hu hu'; rw [rowMeans_deterministic hr hr']
  | _, _, _, _, .inj hf hm, h' => by
    cases h' with
    | inj hf' hm' => rw [hf] at hf'; cases hf'; rw [means_deterministic hm hm']

theorem rowMeans_deterministic : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))}
    {ds ds' : List (Label × Data)}, RowMeans lib row fs ds → RowMeans lib row fs ds' → ds = ds'
  | _, _, _, _, .nil, h' => by cases h'; rfl
  | _, _, _, _, .cons hb hm hr, h' => by
    cases h' with
    | cons hb' hm' hr' =>
      cases bigStep_deterministic hb hb'
      rw [means_deterministic hm hm', rowMeans_deterministic hr hr']
end

/-! ## The field lemma -/

/-- The first field `ℓ` of the data is the meaning of the first suspension `ℓ`, at the first type `ℓ`
has in the row (the three rows carry one label list). -/
theorem rowMeans_find : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {ds : List (Label × Data)},
    RowMeans lib row fs ds → ∀ {ℓ : Label} {dℓ : Data}, Row.find? ℓ ds = some dℓ →
      ∃ A t env w, Row.find? ℓ row = some A ∧ Row.find? ℓ fs = some (t, env) ∧
        BigStep lib env t (.ok w) ∧ Means lib A w dℓ
  | _, _, _, .nil, _, _, h => by simp [Row.find?] at h
  | _, _, _, .cons (ℓ := k) (A := A) (t := t) (env := env) (w := w) hb hm hr, ℓ, dℓ, h => by
    by_cases hk : ℓ = k
    · subst hk
      simp only [Row.find?, if_true, Option.some.injEq] at h
      subst h
      exact ⟨A, t, env, w, by simp [Row.find?], by simp [Row.find?], hb, hm⟩
    · simp only [Row.find?, if_neg hk] at h
      obtain ⟨A', t', env', w', h1, h2, h3, h4⟩ := rowMeans_find hr h
      exact ⟨A', t', env', w', by simp [Row.find?, hk, h1], by simp [Row.find?, hk, h2], h3, h4⟩

/-- The data row carries the type row's labels, in order. -/
theorem rowMeans_labels : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {ds : List (Label × Data)},
    RowMeans lib row fs ds → ds.map Prod.fst = row.map Prod.fst
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ hr => by simp [rowMeans_labels hr]

/-- Every field the type row names is a field of the data. -/
theorem rowMeans_find_row : ∀ {row : List (Label × Ty)} {fs : List (Label × (Term × Env))} {ds : List (Label × Data)},
    RowMeans lib row fs ds → ∀ {ℓ : Label} {A : Ty}, Row.find? ℓ row = some A → ∃ dℓ, Row.find? ℓ ds = some dℓ
  | _, _, _, .nil, _, _, h => by simp [Row.find?] at h
  | _, _, _, .cons (ℓ := k) (d := d) _ _ hr, ℓ, A, h => by
    by_cases hk : ℓ = k
    · exact ⟨d, by simp [Row.find?, hk]⟩
    · simp only [Row.find?, if_neg hk] at h
      obtain ⟨dℓ, h'⟩ := rowMeans_find_row hr h
      exact ⟨dℓ, by simp [Row.find?, hk, h']⟩

/-- A record meaning has every field its type names: `means_get`'s field premise is met for each
label of the row. -/
theorem means_field_exists {row : List (Label × Ty)} {v : Val} {d : Data} (hm : Means lib (.record row) v d)
    {ℓ : Label} {A : Ty} (hA : Row.find? ℓ row = some A) : ∃ dℓ, d.field ℓ = some dℓ := by
  cases hm with
  | record _ hr => exact rowMeans_find_row hr hA

/-- Selecting a field whose suspension is found after unknotting means what that suspension means. -/
theorem unrolls_sel : ∀ {v : Val} {fs : List (Label × (Term × Env))}, Unrolls lib v fs →
    ∀ {ℓ : Label} {t : Term} {env : Env} {r : Except Fault Val}, Row.find? ℓ fs = some (t, env) →
      BigStep lib env t r → Sel lib v ℓ r
  | _, _, .record, _, _, _, _, hf, hb => .field hf hb
  | _, _, .knot hb' hu, _, _, _, _, hf, hb => .knot hb' (unrolls_sel hu hf hb)

/-- `.get t ℓ` has a value whose meaning at `ℓ`'s type is the field `ℓ` of `t`'s record meaning. -/
theorem means_get_exists {env : Env} {t : Term} {v : Val} {row : List (Label × Ty)} {d : Data}
    (ht : BigStep lib env t (.ok v)) (hm : Means lib (.record row) v d) {ℓ : Label} {dℓ : Data}
    (hd : d.field ℓ = some dℓ) :
    ∃ A w, Row.find? ℓ row = some A ∧ BigStep lib env (.get t ℓ) (.ok w) ∧ Means lib A w dℓ := by
  cases hm with
  | record hu hr =>
    obtain ⟨A, t', env', w, h1, h2, h3, h4⟩ := rowMeans_find hr hd
    exact ⟨A, w, h1, .get ht (unrolls_sel hu h2 h3), h4⟩

/-- **The field lemma.** If `t` means `v` and `v` means the record data `d` at `rec row`, then for
every value `w` that `.get t ℓ` means (by any derivation), the field `ℓ` of `d` is `w`'s meaning at
`ℓ`'s type in the row. -/
theorem means_get {env : Env} {t : Term} {v : Val} {row : List (Label × Ty)} {d : Data}
    (ht : BigStep lib env t (.ok v)) (hm : Means lib (.record row) v d) {ℓ : Label} {dℓ : Data}
    (hd : d.field ℓ = some dℓ) {w : Val} (hw : BigStep lib env (.get t ℓ) (.ok w)) :
    ∃ A, Row.find? ℓ row = some A ∧ Means lib A w dℓ := by
  obtain ⟨A, w', h1, h2, h3⟩ := means_get_exists ht hm hd
  cases bigStep_deterministic hw h2
  exact ⟨A, h1, h3⟩

/-- **Extracting a record result forces each field to the meaning of its `get`**: one machine
extraction of `t`'s value at `rec row`, at any budget, holds at `ℓ` the meaning of the value
`.get t ℓ` means. -/
theorem extract_get {m : Machine} {env : Env} {t : Term} {v : Val} {row : List (Label × Ty)} {fuel : Nat}
    {d : Data} {f : Nat} (ht : BigStep m.lib env t (.ok v)) (h : m.extract (.record row) fuel v = .ok (d, f))
    {ℓ : Label} {dℓ : Data} (hd : d.field ℓ = some dℓ) {w : Val} (hw : BigStep m.lib env (.get t ℓ) (.ok w)) :
    ∃ A, Row.find? ℓ row = some A ∧ Means m.lib A w dℓ :=
  means_get ht (extract_means m _ h) hd hw

/-! ## The receiver's run extracts the method application's meaning -/

/-- Slots `stateSlots` wrote are of data conforming to the row, field by field (each field's bytes
decode back to it), when the data carries the row's labels. -/
theorem stateSlots_conforms : ∀ (row : List (Label × Ty)) (ds : List (Label × Data)) (i : Nat) (s : Slots),
    ds.map Prod.fst = row.map Prod.fst → stateSlots row ds i = some s → RowConforms ds row
  | [], [], _, _, _, _ => .nil
  | (ℓ, T) :: row, (ℓ', d) :: ds, i, s, hl, hs => by
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨rfl, hl⟩ := hl
    unfold stateSlots at hs
    split at hs
    · rename_i b s' he hs'
      exact .cons (decodeData_conforms (Wire.decodeData_eq_ok_iff.mpr he)) (stateSlots_conforms row ds (i + 1) s' hl hs')
    · cases hs
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- A meaning at a method's result type whose `state` field is a record carries the state row's labels. -/
theorem means_state_labels {S : Ty} {ks : List Ty} {E : Ty} {es : Nat} {v : Val} {c e : Data}
    {ds : List (Label × Data)} (h : Means lib (resultTy S ks E es) v (.record [("calls", c), ("edits", e), ("state", .record ds)])) :
    ds.map Prod.fst = (recordRow S).map Prod.fst := by
  unfold resultTy at h
  cases h with
  | record _ hr =>
    cases hr with
    | cons _ _ hr =>
      cases hr with
      | cons _ _ hr =>
        cases hr with
        | cons _ hm _ =>
          cases hm with
          | record _ hr' => exact rowMeans_labels hr'

section
variable {D : Type}

/-- **What the receiver's run extracts is a meaning**: a successful `runMeasured` loaded the closure,
resolved the method, read the state, decoded the arguments and built the rows; the method application
`apply4 g ℓ`, in the environment of those, means a value `v` (`BigStep`); the result extracted at the
method's own result type is `v`'s meaning there; the calls are `callsOf` of its `calls` field; its
`state` field is a record `ds` conforming to the package's state row, and the slots the run returned
are what `stateSlots` writes of `ds` there. `readState_go_stateSlots` reads them back to `ds` given
one more fact this does not state: every digest in `ds` passes `digestsOk` (the run does not
check it; that a run's digests come only from its checked inputs and literals is unproved). -/
theorem runMeasured_means {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)}
    {t n : Nat}
    (h : runMeasured bytesOf digestOf look rv pkg state method args r budget = .ok (s, calls, rows, t, n)) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (x : Label × Sig) (sd ad wd : Data) (v : Val) (c e : Data)
      (ds : List (Label × Data)),
      load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧
      L.pkgs[g]? = some p ∧ resolveMethod (D := D) p method = .ok x ∧
      readState digestOf (recordRow p.state) state = .ok sd ∧
      Wire.decodeData x.2.arg args = .ok ad ∧
      readsData digestOf p.rels rv r.self x.2.reads = .ok wd ∧
      BigStep L.lib [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] (apply4 g x.1) (.ok v) ∧
      Means L.lib (resultTy p.state x.2.calls (editTy p.rels) x.2.edits) v
        (.record [("calls", c), ("edits", e), ("state", .record ds)]) ∧
      callsOf digestOf c = .ok calls ∧ stateSlots (recordRow p.state) ds 0 = some s ∧
      RowConforms ds (recordRow p.state) := by
  unfold runMeasured at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i S hS
  obtain ⟨L, g, p, ℓ, sg, sd, ad, wd, -, hl, hp, hres, hsd, had, -, hwd, rfl⟩ := runSetup_spec hS
  simp only at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, -, -, -⟩ := h
  rename_i hext _ _ hss _ _ _ _ _ _ _ _ _
  have hm := extract_means _ _ hext
  exact ⟨L, g, p, (ℓ, sg), sd, ad, wd, _, _, _, _, hl, hp, hres, hsd, had, hwd, run_bigStep (by assumption),
    hm, by assumption, hss, stateSlots_conforms _ _ _ _ (means_state_labels hm) hss⟩

end

/-! ## A meaning that reaches no package does not depend on the closure

The receiver runs `apply4 g ℓ` under the loaded closure `L.lib`, where `.ref g` is the package body
(relocated, which is the identity on a body with no `ref`: `relocate_noRef`). A consumer that
computes what a method means under a lib of its own choosing, e.g. `[body]` with `apply4 0 ℓ`, gets
the same meaning under `L.lib` (`relib_apply4`): a term and environment that hold no `ref` never
read the closure. -/

/-- A value holds no closure reference: every closure, knot and suspension in it is a `NoRef` term
over such values. Data put into the machine is such a value (`toVal_noRef`). -/
inductive NoRefVal : Val → Prop
  | nat {n : Nat} : NoRefVal (.nat n)
  | bool {b : Bool} : NoRefVal (.bool b)
  | bytes {s : ByteArray} : NoRefVal (.bytes s)
  | digest {s : ByteArray} : NoRefVal (.digest s)
  | clo {b : Term} {env : Env} : NoRef b → (∀ v ∈ env, NoRefVal v) → NoRefVal (.clo b env)
  | record {fs : List (Label × (Term × Env))} :
      (∀ p ∈ fs, NoRef p.2.1) → (∀ p ∈ fs, ∀ v ∈ p.2.2, NoRefVal v) → NoRefVal (.record fs)
  | knot {b : Term} {env : Env} : NoRef b → (∀ v ∈ env, NoRefVal v) → NoRefVal (.knot b env)
  | inj {ℓ : Label} {w : Val} : NoRefVal w → NoRefVal (.inj ℓ w)

mutual
theorem toVal_noRef : ∀ d : Data, NoRefVal d.toVal
  | .nat _ => .nat
  | .bool _ => .bool
  | .bytes _ => .bytes
  | .digest _ => .digest
  | .record fs => .record (fun p hp => (rowToVal_noRef fs p hp).1) (fun p hp => (rowToVal_noRef fs p hp).2)
  | .inj _ d => .inj (toVal_noRef d)

theorem rowToVal_noRef : ∀ fs : List (Label × Data), ∀ p ∈ Data.rowToVal fs, NoRef p.2.1 ∧ ∀ v ∈ p.2.2, NoRefVal v
  | [] => fun p hp => by simp [Data.rowToVal] at hp
  | (_, d) :: fs => fun p hp => by
    simp only [Data.rowToVal, List.mem_cons] at hp
    rcases hp with rfl | hp
    · refine ⟨by simp [NoRef], fun v hv => ?_⟩
      simp only [List.mem_singleton] at hv
      subst hv
      exact toVal_noRef d
    · exact rowToVal_noRef fs p hp
end

/-- The receiver's environment (request, arguments, state, rows: four data) holds no reference. -/
theorem toVal4_noRef (a b c d : Data) : ∀ v ∈ [a.toVal, b.toVal, c.toVal, d.toVal], NoRefVal v := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> exact toVal_noRef _

theorem primEval_noRefVal {p : Prim} {x y v : Val} (h : primEval p x y = .ok v) : NoRefVal v := by
  unfold primEval at h
  split at h <;> (try unfold natResult at h) <;> (try split at h) <;> first | (cases h <;> constructor) | simp at h

theorem suspend_noRef {env : Env} {fs : List (Label × Term)} (hf : NoRefRow fs) (he : ∀ v ∈ env, NoRefVal v) :
    ∀ p ∈ suspend env fs, NoRef p.2.1 ∧ ∀ v ∈ p.2.2, NoRefVal v := by
  intro p hp
  simp only [suspend, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨NoRefStd.row_iff.mp hf q hq, he⟩

theorem knot_env_noRef {b : Term} {env : Env} (hb : NoRef b) (he : ∀ v ∈ env, NoRefVal v) :
    ∀ u ∈ Val.knot b env :: env, NoRefVal u := fun u hu => by
  simp only [List.mem_cons] at hu
  rcases hu with rfl | hu
  · exact .knot hb he
  · exact he u hu

mutual
/-- **A no-ref meaning is the closure's to ignore**: a derivation of a `NoRef` term over a no-ref
environment is a derivation under every other lib, and the value it means holds no reference. -/
theorem bigStep_relib {lib' : List Term} : ∀ {env : Env} {t : Term} {r : Except Fault Val},
    BigStep lib env t r → NoRef t → (∀ v ∈ env, NoRefVal v) →
      BigStep lib' env t r ∧ ∀ v, r = .ok v → NoRefVal v
  | _, _, _, .var h, _, he => ⟨.var h, fun v hv => by cases hv; exact he _ (List.mem_of_getElem? h)⟩
  | _, _, _, .lam, ht, he => ⟨.lam, fun v hv => by cases hv; exact .clo ht he⟩
  | _, _, _, .app hf ha hb, ht, he => by
    obtain ⟨hf', hfv⟩ := bigStep_relib hf ht.1 he
    obtain ⟨ha', hav⟩ := bigStep_relib ha ht.2 he
    have hc := hfv _ rfl
    cases hc with
    | clo hbn hce =>
      have hw := hav _ rfl
      obtain ⟨hb', hbv⟩ := bigStep_relib hb hbn (fun v hv => by
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hw
        · exact hce v hv)
      exact ⟨.app hf' ha' hb', hbv⟩
  | _, _, _, .appF hf, ht, he => ⟨.appF (bigStep_relib hf ht.1 he).1, fun v hv => by cases hv⟩
  | _, _, _, .appA hf ha, ht, he =>
    ⟨.appA (bigStep_relib hf ht.1 he).1 (bigStep_relib ha ht.2 he).1, fun v hv => by cases hv⟩
  | _, _, _, .fix hs, ht, he => by
    obtain ⟨hs', hsv⟩ := bigStep_relib hs ht he
    have hc := hsv _ rfl
    cases hc with
    | clo hbn hce => exact ⟨.fix hs', fun v hv => by cases hv; exact .knot hbn hce⟩
  | _, _, _, .fixE hs, ht, he => ⟨.fixE (bigStep_relib hs ht he).1, fun v hv => by cases hv⟩
  | _, _, _, .nat, _, _ => ⟨.nat, fun v hv => by cases hv; exact .nat⟩
  | _, _, _, .bool, _, _ => ⟨.bool, fun v hv => by cases hv; exact .bool⟩
  | _, _, _, .bytes, _, _ => ⟨.bytes, fun v hv => by cases hv; exact .bytes⟩
  | _, _, _, .digest, _, _ => ⟨.digest, fun v hv => by cases hv; exact .digest⟩
  | _, _, _, .refuse, _, _ => ⟨.refuse, fun v hv => by cases hv⟩
  | _, _, _, .prim ha hb hne, ht, he =>
    ⟨.prim (bigStep_relib ha ht.1 he).1 (bigStep_relib hb ht.2 he).1 hne, fun v hv => primEval_noRefVal hv⟩
  | _, _, _, .primL ha, ht, he => ⟨.primL (bigStep_relib ha ht.1 he).1, fun v hv => by cases hv⟩
  | _, _, _, .primR ha hb, ht, he =>
    ⟨.primR (bigStep_relib ha ht.1 he).1 (bigStep_relib hb ht.2 he).1, fun v hv => by cases hv⟩
  | _, _, _, .record, ht, he => ⟨.record, fun v hv => by cases hv; exact .record (fun p hp => (suspend_noRef ht he p hp).1) (fun p hp => (suspend_noRef ht he p hp).2)⟩
  | _, _, _, .get hs hsel, ht, he => by
    obtain ⟨hs', hsv⟩ := bigStep_relib hs ht he
    obtain ⟨hsel', hr⟩ := sel_relib hsel (hsv _ rfl)
    exact ⟨.get hs' hsel', hr⟩
  | _, _, _, .getE hs, ht, he => ⟨.getE (bigStep_relib hs ht he).1, fun v hv => by cases hv⟩
  | _, _, _, .extend hs hx, ht, he => by
    obtain ⟨hs', hsv⟩ := bigStep_relib hs ht.1 he
    obtain ⟨hx', hr⟩ := ext_relib hx (hsv _ rfl) ht.2 he
    exact ⟨.extend hs' hx', hr⟩
  | _, _, _, .extendE hs, ht, he => ⟨.extendE (bigStep_relib hs ht.1 he).1, fun v hv => by cases hv⟩
  | _, _, _, .inj hs, ht, he => by
    obtain ⟨hs', hsv⟩ := bigStep_relib hs ht he
    exact ⟨.inj hs', fun v hv => by cases hv; exact .inj (hsv _ rfl)⟩
  | _, _, _, .injE hs, ht, he => ⟨.injE (bigStep_relib hs ht he).1, fun v hv => by cases hv⟩
  | _, _, _, .case hs hf hb, ht, he => by
    obtain ⟨hs', hsv⟩ := bigStep_relib hs ht.1 he
    have hc := hsv _ rfl
    cases hc with
    | inj hw =>
      have hbn := NoRefStd.row_iff.mp ht.2 _ (find?_mem hf)
      obtain ⟨hb', hbv⟩ := bigStep_relib hb hbn (fun v hv => by
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hw
        · exact he v hv)
      exact ⟨.case hs' hf hb', hbv⟩
  | _, _, _, .caseE hs, ht, he => ⟨.caseE (bigStep_relib hs ht.1 he).1, fun v hv => by cases hv⟩
  | _, _, _, .iteT hc ha, ht, he => by
    obtain ⟨ha', hav⟩ := bigStep_relib ha ht.2.1 he
    exact ⟨.iteT (bigStep_relib hc ht.1 he).1 ha', hav⟩
  | _, _, _, .iteF hc hb, ht, he => by
    obtain ⟨hb', hbv⟩ := bigStep_relib hb ht.2.2 he
    exact ⟨.iteF (bigStep_relib hc ht.1 he).1 hb', hbv⟩
  | _, _, _, .iteE hc, ht, he => ⟨.iteE (bigStep_relib hc ht.1 he).1, fun v hv => by cases hv⟩
  | _, _, _, .ref _ _, ht, _ => ht.elim

theorem sel_relib {lib' : List Term} : ∀ {v : Val} {ℓ : Label} {r : Except Fault Val},
    Sel lib v ℓ r → NoRefVal v → Sel lib' v ℓ r ∧ ∀ w, r = .ok w → NoRefVal w
  | _, _, _, .field hf hb, hv => by
    cases hv with
    | record hfn hfe =>
      obtain ⟨hb', hr⟩ := bigStep_relib hb (hfn _ (find?_mem hf)) (hfe _ (find?_mem hf))
      exact ⟨.field hf hb', hr⟩
  | _, _, _, .knot hb hs, hv => by
    cases hv with
    | knot hbn hen =>
      have henv := knot_env_noRef hbn hen
      obtain ⟨hb', hbv⟩ := bigStep_relib hb hbn henv
      obtain ⟨hs', hr⟩ := sel_relib hs (hbv _ rfl)
      exact ⟨.knot hb' hs', hr⟩
  | _, _, _, .knotE hb, hv => by
    cases hv with
    | knot hbn hen =>
      have henv := knot_env_noRef hbn hen
      exact ⟨.knotE (bigStep_relib hb hbn henv).1, fun w hw => by cases hw⟩

theorem ext_relib {lib' : List Term} : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r : Except Fault Val},
    Ext lib v fs env r → NoRefVal v → NoRefRow fs → (∀ u ∈ env, NoRefVal u) →
      Ext lib' v fs env r ∧ ∀ w, r = .ok w → NoRefVal w
  | _, _, _, _, .record, hv, hf, he => by
    cases hv with
    | record hgn hge =>
      refine ⟨.record, fun w hw => ?_⟩
      cases hw
      refine .record (fun p hp => ?_) (fun p hp => ?_)
      · rcases Row.mem_merge hp with hp | hp
        · exact hgn p hp
        · exact (suspend_noRef hf he p hp).1
      · rcases Row.mem_merge hp with hp | hp
        · exact hge p hp
        · exact (suspend_noRef hf he p hp).2
  | _, _, _, _, .knot hb hx, hv, hf, he => by
    cases hv with
    | knot hbn hen =>
      have henv := knot_env_noRef hbn hen
      obtain ⟨hb', hbv⟩ := bigStep_relib hb hbn henv
      obtain ⟨hx', hr⟩ := ext_relib hx (hbv _ rfl) hf he
      exact ⟨.knot hb' hx', hr⟩
  | _, _, _, _, .knotE hb, hv, _, _ => by
    cases hv with
    | knot hbn hen =>
      have henv := knot_env_noRef hbn hen
      exact ⟨.knotE (bigStep_relib hb hbn henv).1, fun w hw => by cases hw⟩
end

/-- A no-ref value unknots to the same suspensions under every lib, and they hold no reference. -/
theorem unrolls_relib {lib' : List Term} : ∀ {v : Val} {fs : List (Label × (Term × Env))},
    Unrolls lib v fs → NoRefVal v →
      Unrolls lib' v fs ∧ ∀ p ∈ fs, NoRef p.2.1 ∧ ∀ u ∈ p.2.2, NoRefVal u
  | _, _, .record, hv => by
    cases hv with
    | record hn he => exact ⟨.record, fun p hp => ⟨hn p hp, he p hp⟩⟩
  | _, _, .knot hb hu, hv => by
    cases hv with
    | knot hbn hen =>
      obtain ⟨hb', hbv⟩ := bigStep_relib (lib' := lib') hb hbn (knot_env_noRef hbn hen)
      obtain ⟨hu', hf⟩ := unrolls_relib hu (hbv _ rfl)
      exact ⟨.knot hb' hu', hf⟩

mutual
/-- **A no-ref value's meaning is the closure's to ignore**: what a value holding no reference
means at a type under one lib, it means under every lib. -/
theorem means_relib {lib' : List Term} : ∀ {T : Ty} {v : Val} {d : Data},
    Means lib T v d → NoRefVal v → Means lib' T v d
  | _, _, _, .nat, _ => .nat
  | _, _, _, .bool, _ => .bool
  | _, _, _, .bytes, _ => .bytes
  | _, _, _, .digest, _ => .digest
  | _, _, _, .record hu hr, hv =>
    .record (unrolls_relib hu hv).1 (rowMeans_relib hr (unrolls_relib (lib' := lib') hu hv).2)
  | _, _, _, .inj hf hm, .inj hw => .inj hf (means_relib hm hw)

theorem rowMeans_relib {lib' : List Term} : ∀ {row : List (Label × Ty)}
    {fs : List (Label × (Term × Env))} {ds : List (Label × Data)},
    RowMeans lib row fs ds → (∀ p ∈ fs, NoRef p.2.1 ∧ ∀ u ∈ p.2.2, NoRefVal u) → RowMeans lib' row fs ds
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons hb hm hr, hf =>
    have h0 := hf _ (List.mem_cons_self ..)
    have hb' := bigStep_relib (lib' := lib') hb h0.1 h0.2
    .cons hb'.1 (means_relib hm (hb'.2 _ rfl)) (rowMeans_relib hr (fun p hp => hf p (List.mem_cons_of_mem _ hp)))
end

/-- `t` under `lib` and `t'` under `lib'` have one meaning over every no-ref environment, and it
holds no reference. -/
def Relib (lib lib' : List Term) (t t' : Term) : Prop :=
  ∀ {env : Env} {r : Except Fault Val}, (∀ v ∈ env, NoRefVal v) → BigStep lib env t r →
    BigStep lib' env t' r ∧ ∀ v, r = .ok v → NoRefVal v

theorem relib_noRef {lib' : List Term} {t : Term} (ht : NoRef t) : Relib lib lib' t t :=
  fun he h => bigStep_relib h ht he

/-- Two closures holding one no-ref body at their indices: the references mean the same. -/
theorem relib_ref {lib' : List Term} {g g' : Nat} {b : Term} (hg : lib[g]? = some b) (hg' : lib'[g']? = some b)
    (hb : NoRef b) : Relib lib lib' (.ref g) (.ref g') := by
  intro env r _ h
  cases h with
  | ref hi hbody =>
    rw [hg] at hi
    cases hi
    obtain ⟨hb', hr⟩ := bigStep_relib hbody hb (fun v hv => by cases hv)
    exact ⟨.ref hg' hb', hr⟩

theorem relib_app {lib' : List Term} {f f' a a' : Term} (hf : Relib lib lib' f f') (ha : Relib lib lib' a a') :
    Relib lib lib' (.app f a) (.app f' a') := by
  intro env r he h
  cases h with
  | app h1 h2 h3 =>
    obtain ⟨h1', h1v⟩ := hf he h1
    obtain ⟨h2', h2v⟩ := ha he h2
    have hc := h1v _ rfl
    cases hc with
    | clo hbn hce =>
      obtain ⟨h3', h3v⟩ := bigStep_relib h3 hbn (fun v hv => by
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact h2v _ rfl
        · exact hce v hv)
      exact ⟨.app h1' h2' h3', h3v⟩
  | appF h1 => exact ⟨.appF (hf he h1).1, fun v hv => by cases hv⟩
  | appA h1 h2 => exact ⟨.appA (hf he h1).1 (ha he h2).1, fun v hv => by cases hv⟩

theorem relib_get {lib' : List Term} {t t' : Term} {ℓ : Label} (ht : Relib lib lib' t t') :
    Relib lib lib' (.get t ℓ) (.get t' ℓ) := by
  intro env r he h
  cases h with
  | get h1 hs =>
    obtain ⟨h1', h1v⟩ := ht he h1
    obtain ⟨hs', hr⟩ := sel_relib hs (h1v _ rfl)
    exact ⟨.get h1' hs', hr⟩
  | getE h1 => exact ⟨.getE (ht he h1).1, fun v hv => by cases hv⟩

theorem relib_case {lib' : List Term} {t t' : Term} {arms : List (Label × Term)} (ht : Relib lib lib' t t')
    (harms : NoRefRow arms) : Relib lib lib' (.case t arms) (.case t' arms) := by
  intro env r he h
  cases h with
  | case h1 hf hb =>
    obtain ⟨h1', h1v⟩ := ht he h1
    have hc := h1v _ rfl
    cases hc with
    | inj hw =>
      obtain ⟨hb', hbv⟩ := bigStep_relib hb (NoRefStd.row_iff.mp harms _ (find?_mem hf)) (fun v hv => by
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hw
        · exact he v hv)
      exact ⟨.case h1' hf hb', hbv⟩
  | caseE h1 => exact ⟨.caseE (ht he h1).1, fun v hv => by cases hv⟩

/-- **The method application under two closures**: if both hold one no-ref body at their indices
(the receiver's `L.lib[g]?` is the package body relocated, `relocate_noRef`), the method
application means the same under each, over every no-ref environment (`toVal4_noRef`). -/
theorem relib_apply4 {lib' : List Term} {g g' : Nat} {b : Term} {ℓ : Label} (hg : lib[g]? = some b)
    (hg' : lib'[g']? = some b) (hb : NoRef b) : Relib lib lib' (apply4 g ℓ) (apply4 g' ℓ) :=
  relib_app (relib_app (relib_app (relib_app (relib_get (relib_ref hg hg' hb))
    (relib_noRef (t := .var 3) trivial)) (relib_noRef (t := .var 2) trivial))
    (relib_noRef (t := .var 1) trivial)) (relib_noRef (t := .var 0) trivial)

/-- **Tooth**: the shared body is needed: `ref 0` under `[1]` and under `[2]` mean differently. -/
theorem relib_needs_one_body : ¬ Relib [.nat 1] [.nat 2] (.ref 0) (.ref 0) := by
  intro h
  have h1 := (h (env := []) (fun v hv => by cases hv) (.ref rfl .nat)).1
  have h2 : BigStep [.nat 2] [] (.ref 0) (.ok (.nat 2)) := .ref rfl .nat
  have := bigStep_deterministic h1 h2
  cases this

/-- **Tooth**: the body must hold no reference: both libs hold `ref 1` at index 0, and `ref 0`
still means differently, through index 1. -/
theorem relib_needs_noRef : ¬ Relib [.ref 1, .nat 1] [.ref 1, .nat 2] (.ref 0) (.ref 0) := by
  intro h
  have h1 := (h (env := []) (fun v hv => by cases hv) (.ref rfl (.ref rfl .nat))).1
  have h2 : BigStep [.ref 1, .nat 2] [] (.ref 0) (.ok (.nat 2)) := .ref rfl (.ref rfl .nat)
  have := bigStep_deterministic h1 h2
  cases this

/-- **Tooth**: `means_relib` needs its value to hold no reference: the knot `knot (ref 0) []`
means `{a = 1}` under `[{a = 1}]` and not under `[{a = 2}]`. -/
theorem means_relib_needs_noRef :
    Means [.record [("a", .nat 1)]] (.record [("a", .nat)]) (.knot (.ref 0) []) (.record [("a", .nat 1)]) ∧
      ¬ Means [.record [("a", .nat 2)]] (.record [("a", .nat)]) (.knot (.ref 0) []) (.record [("a", .nat 1)]) := by
  refine ⟨.record (.knot (.ref rfl .record) .record) (.cons .nat .nat .nil), fun h => ?_⟩
  have h2 : Means [.record [("a", .nat 2)]] (.record [("a", .nat)]) (.knot (.ref 0) []) (.record [("a", .nat 2)]) :=
    .record (.knot (.ref rfl .record) .record) (.cons .nat .nat .nil)
  cases means_deterministic h h2

/-- **Tooth** (for `runMeasured_means`' `stateSlots` conjunct): it is not implied by the `Means`
conjunct. The record `{a = natLimit}` is a meaning at `rec {a : nat}` (a meaning has no bounds), and
`stateSlots` writes no slots of it; `{a = 1}` it writes. -/
theorem run_state_tooth :
    Means [] (.record [("a", .nat)]) (.record [("a", (.nat Bounds.natLimit, []))]) (.record [("a", .nat Bounds.natLimit)]) ∧
      stateSlots [("a", .nat)] [("a", .nat Bounds.natLimit)] 0 = none ∧
      ∃ s, stateSlots [("a", .nat)] [("a", .nat 1)] 0 = some s :=
  ⟨.record .record (.cons .nat .nat .nil), by decide, ⟨_, rfl⟩⟩

/-! ## Teeth -/

private abbrev knotBody : Term := .record [("a", .nat 1), ("g", .get (.var 0) "a")]

/-- `fix (λself. {a = 1, g = self.a})`: a knot whose `g` is its own `a`. -/
private abbrev knotRec : Term := .fix (.lam (.record [("a", .nat), ("g", .nat)]) knotBody)

private theorem knotRec_means : BigStep [] [] knotRec (.ok (.knot knotBody [])) := .fix .lam

private theorem knotRec_g : BigStep [] [] (.get knotRec "g") (.ok (.nat 1)) :=
  .get knotRec_means (.knot .record (.field rfl (.get (.var rfl) (.knot .record (.field rfl .nat)))))

/-- **Tooth**: a record whose field is not its `get`'s meaning is never what extraction returns:
the knot's `g` means `1`, so at every budget extraction does not return `g = 2`. -/
theorem extract_get_tooth {m : Machine} (hm : m.lib = []) {fuel f : Nat} :
    m.extract (.record [("a", .nat), ("g", .nat)]) fuel (.knot knotBody []) ≠
      .ok (.record [("a", .nat 1), ("g", .nat 2)], f) := by
  intro h
  cases m with
  | mk lib =>
    simp only at hm
    subst hm
    obtain ⟨A, -, hA⟩ := extract_get knotRec_means h (ℓ := "g") (dℓ := .nat 2) (by rfl) knotRec_g
    cases hA

/-- The premise is satisfiable: the same knot extracts, to `g = 1`. -/
theorem extract_knot_ok : ∃ f, (Machine.mk []).extract (.record [("a", .nat), ("g", .nat)]) 100
    (.knot knotBody []) = .ok (.record [("a", .nat 1), ("g", .nat 1)], f) :=
  ⟨_, rfl⟩

end Nanodregg.Lang
