/-
# Lang.Proofs.Sound — a checked program never gets stuck (preservation and progress for `step`)

`step_sound`: from a typed state, one step either continues in a typed state (preservation), or
halts with a value of the state's type, or faults by a name other than `stuck` (progress). So
`run_sound`: a run of a checked program ends with a value of its type or with one of the named
budget/arithmetic faults (`ticks`, `stack`, `overflow`, `underflow`, `divZero`, `tooLarge`), never
`stuck`, at every budget. `step_depth` keeps the O(1) depth counter equal to the stack's length.
-/
import Lang.Proofs.RunTy
import Lang.Proofs.Row
import Lang.Proofs.Check

namespace Nanodregg.Lang

variable {Δ : List Ty}

theorem EnvTy.lookup : ∀ {env : List Val} {Γ : List Ty}, EnvTy Δ env Γ →
    ∀ {i : Nat} {T : Ty}, Γ[i]? = some T → ∃ v, env[i]? = some v ∧ ValTy Δ v T
  | _, _, .nil, _, _, hi => by simp at hi
  | _, _, .cons hv _, 0, _, hi => by simp at hi ⊢; subst hi; exact hv
  | _, _, .cons _ he, i + 1, _, hi => by simpa using EnvTy.lookup he (by simpa using hi)

theorem ThunksTy.rel : ∀ {fs : List (Label × (Term × List Val))} {r : List (Label × Ty)},
    ThunksTy Δ fs r → Row.Rel (ThunkTy Δ) fs r
  | _, _, .nil => .nil
  | _, _, .cons he ht h => .cons (.mk he ht) (ThunksTy.rel h)

theorem ThunksTy.of_rel {fs : List (Label × (Term × List Val))} {r : List (Label × Ty)}
    (h : Row.Rel (ThunkTy Δ) fs r) : ThunksTy Δ fs r := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => cases hab with
    | mk he ht => exact .cons he ht ih

theorem FieldsTy.rel : ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
    FieldsTy Δ Γ fs r → Row.Rel (HasType Δ Γ) fs r
  | _, _, _, .nil => .nil
  | _, _, _, .cons ht h => .cons ht (FieldsTy.rel h)

theorem suspend_ty {env : List Val} {Γ : List Ty} {fs : List (Label × Term)}
    {r : List (Label × Ty)} (he : EnvTy Δ env Γ) (hf : FieldsTy Δ Γ fs r) :
    Row.Rel (ThunkTy Δ) (suspend env fs) r :=
  hf.rel.map_left (fun t => (t, env)) (fun _ _ ht => .mk he ht)

theorem ArmsTy.find : ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)}
    {B : Ty}, ArmsTy Δ Γ arms r B →
    ∀ {ℓ : Label} {A : Ty}, Row.find? ℓ r = some A →
      ∃ body, Row.find? ℓ arms = some body ∧ HasType Δ (A :: Γ) body B
  | _, _, _, _, @ArmsTy.one _ _ k _ _ _ hb, ℓ, _, hA => by
    by_cases e : ℓ = k
    · simp [Row.find?, e] at hA ⊢; subst hA; exact hb
    · simp [Row.find?, e] at hA
  | _, _, _, _, @ArmsTy.cons _ _ k _ _ _ _ _ hb h _, ℓ, _, hA => by
    by_cases e : ℓ = k
    · simp [Row.find?, e] at hA ⊢; subst hA; exact hb
    · simp only [Row.find?, e, if_false] at hA ⊢; exact ArmsTy.find h hA

/-! Canonical forms: a typed value has the shape its type says. -/

theorem ValTy.nat_inv {v : Val} (h : ValTy Δ v .nat) : ∃ n, v = .nat n := by
  cases h; exact ⟨_, rfl⟩

theorem ValTy.bytes_inv {v : Val} (h : ValTy Δ v .bytes) :
    ∃ s, v = .bytes s ∧ s.size ≤ Bounds.bytesMax := by
  cases h with
  | bytes hs => exact ⟨_, rfl, hs⟩

theorem ValTy.digest_inv {v : Val} (h : ValTy Δ v .digest) :
    ∃ s, v = .digest s ∧ s.size ≤ Bounds.digestBytesMax := by
  cases h with
  | digest hs => exact ⟨_, rfl, hs⟩

theorem ValTy.bool_inv {v : Val} (h : ValTy Δ v .bool) : ∃ b, v = .bool b := by
  cases h; exact ⟨_, rfl⟩

theorem ValTy.fn_inv {v : Val} {A B : Ty} (h : ValTy Δ v (.fn A B)) :
    ∃ b env Γ, v = .clo b env ∧ EnvTy Δ env Γ ∧ HasType Δ (A :: Γ) b B := by
  cases h with
  | clo he hb => exact ⟨_, _, _, rfl, he, hb⟩

theorem ValTy.sum_inv {v : Val} {r : List (Label × Ty)} (h : ValTy Δ v (.sum r)) :
    ∃ ℓ A w, v = .inj ℓ w ∧ Row.find? ℓ r = some A ∧ ValTy Δ w A := by
  cases h with
  | inj hA hw => exact ⟨_, _, _, rfl, hA, hw⟩

theorem natResult_sound (n : Nat) :
    match natResult n with
    | .ok r => ValTy Δ r .nat
    | .error e => e ≠ .stuck := by
  unfold natResult
  by_cases h : n < Bounds.natLimit
  · simp only [h, if_true]; exact .nat h
  · simp [h]

/-- A primitive on operands of its types yields a value of its result type, or a named
arithmetic fault; never `stuck`. -/
theorem primEval_sound {p : Prim} {a b : Val} (ha : ValTy Δ a p.left) (hb : ValTy Δ b p.right) :
    match primEval p a b with
    | .ok r => ValTy Δ r p.result
    | .error e => e ≠ .stuck := by
  cases p with
  | beq =>
    obtain ⟨x, rfl, _⟩ := ValTy.bytes_inv ha; obtain ⟨y, rfl, _⟩ := ValTy.bytes_inv hb
    exact .bool
  | deq =>
    obtain ⟨x, rfl, _⟩ := ValTy.digest_inv ha; obtain ⟨y, rfl, _⟩ := ValTy.digest_inv hb
    exact .bool
  | lenLe =>
    obtain ⟨x, rfl, _⟩ := ValTy.bytes_inv ha
    cases hb with
    | nat hy => simp only [primEval]; exact .bool
  | cat =>
    obtain ⟨x, rfl, _⟩ := ValTy.bytes_inv ha; obtain ⟨y, rfl, _⟩ := ValTy.bytes_inv hb
    simp only [primEval]
    by_cases h : x.size + y.size ≤ Bounds.bytesMax
    · simp only [h, if_true]; exact .bytes (by simpa [ByteArray.size_append] using h)
    · simp [h]
  | _ =>
    cases ha with
    | nat hx => cases hb with
      | nat hy =>
        rename_i x y
        simp only [primEval, Prim.result]
        first
          | exact natResult_sound _
          | exact .bool
          | (by_cases h : y ≤ x
             · simp only [h, if_true]; exact .nat (by omega)
             · simp [h])
          | (by_cases h : y = 0
             · simp [h]
             · simp only [h, if_false]; exact .nat (by have := Nat.div_le_self x y; omega))
          | (by_cases h : y = 0
             · simp [h]
             · simp only [h, if_false]; exact .nat (by have := Nat.mod_le x y; omega))

theorem ValTy.record_inv {v : Val} {r : List (Label × Ty)} (h : ValTy Δ v (.record r)) :
    (∃ fs, v = .record fs ∧ ThunksTy Δ fs r) ∨
    (∃ b env Γ, v = .knot b env ∧ EnvTy Δ env Γ ∧ HasType Δ (.record r :: Γ) b (.record r)) := by
  cases h with
  | record h => exact .inl ⟨_, rfl, h⟩
  | knot he hb => exact .inr ⟨_, _, _, rfl, he, hb⟩

/-- Preservation and progress in one statement: a typed state steps to a typed state, halts with
a value of its type, or faults by a name other than `stuck`. -/
theorem step_sound {lib : List Term} {s : State} {T : Ty} (hlib : LibTy Δ lib)
    (hs : StateTy Δ s T) : StepOK Δ T (step lib s) := by
  cases hs with
  | @eval t env Γ A k d T he ht hk =>
    cases ht with
    | var hi =>
      obtain ⟨v, hv, hvt⟩ := he.lookup hi
      simp only [step, hv]; exact .next (.ret hvt hk)
    | lam _ hb => exact .next (.ret (.clo he hb) hk)
    | app hf ha => exact .next (.eval he hf (.appL he ha hk))
    | fix ht => exact .next (.eval he ht (.fix hk))
    | nat hn => exact .next (.ret (.nat hn) hk)
    | bool => exact .next (.ret .bool hk)
    | bytes hn => exact .next (.ret (.bytes hn) hk)
    | digest hn => exact .next (.ret (.digest hn) hk)
    | prim ha hb => exact .next (.eval he ha (.primL he hb hk))
    | record _ hf => exact .next (.ret (.record (ThunksTy.of_rel (suspend_ty he hf))) hk)
    | get ht hf => exact .next (.eval he ht (.get hf hk))
    | extend ht _ hf => exact .next (.eval he ht (.extend he hf hk))
    | inj _ hA ht => exact .next (.eval he ht (.inj hA hk))
    | case ht ha => exact .next (.eval he ht (.case he ha hk))
    | ite hc ha hb => exact .next (.eval he hc (.ite he ha hb hk))
    | ref hi =>
      obtain ⟨body, hbody, hbt⟩ := hlib _ _ hi
      simp only [step, hbody]; exact .next (.eval .nil hbt hk)
    | refuse _ _ => simp only [step]; exact .fault (by simp)
  | @ret v A k d T hv hk =>
    cases hk with
    | nil => exact .halt hv
    | appL he ha hk => exact .next (.eval he ha (.appR hv hk))
    | appR hf hk =>
      obtain ⟨b, cenv, Γ, rfl, hce, hb⟩ := hf.fn_inv
      exact .next (.eval (.cons hv hce) hb hk)
    | fix hk =>
      obtain ⟨b, cenv, Γ, rfl, hce, hb⟩ := hv.fn_inv
      exact .next (.ret (.knot hce hb) hk)
    | primL he hb hk => exact .next (.eval he hb (.primR hv hk))
    | @primR p a k T ha hk =>
      have hp := primEval_sound ha hv
      simp only [step]
      revert hp
      cases primEval p a v with
      | ok r => intro hp; exact .next (.ret hp hk)
      | error e => intro hp; exact .fault hp
    | @get ℓ r A k T hA hk =>
      rcases hv.record_inv with ⟨fs, rfl, hfs⟩ | ⟨b, kenv, Γ, rfl, hke, hb⟩
      · obtain ⟨⟨t, env⟩, hfind, hth⟩ := hfs.rel.find ℓ hA
        cases hth with
        | mk he ht => simp only [step, hfind]; exact .next (.eval he ht hk)
      · exact .next (.eval (.cons hv hke) hb (.get hA hk))
    | @extend fs env Γ r r2 k T he hf hk =>
      rcases hv.record_inv with ⟨gs, rfl, hgs⟩ | ⟨b, kenv, Γ', rfl, hke, hb⟩
      · exact .next (.ret (.record (ThunksTy.of_rel (hgs.rel.merge (suspend_ty he hf)))) hk)
      · exact .next (.eval (.cons hv hke) hb (.extend he hf hk))
    | inj hA hk => exact .next (.ret (.inj hA hv) hk)
    | @case arms env Γ r B k T he ha hk =>
      obtain ⟨ℓ, A', w, rfl, hA, hw⟩ := hv.sum_inv
      obtain ⟨body, hfind, hbody⟩ := ha.find hA
      simp only [step, hfind]; exact .next (.eval (.cons hw he) hbody hk)
    | ite he ha hb hk =>
      obtain ⟨b, rfl⟩ := hv.bool_inv
      cases b
      · exact .next (.eval he hb hk)
      · exact .next (.eval he ha hk)

/-- Preservation, by itself. -/
theorem step_preserves {lib : List Term} {s s' : State} {T : Ty} (hlib : LibTy Δ lib)
    (hs : StateTy Δ s T) (h : step lib s = .next s') : StateTy Δ s' T := by
  have := step_sound hlib hs; rw [h] at this; cases this; assumption

/-- Progress, by itself: a typed state is never stuck. -/
theorem step_progress {lib : List Term} {s : State} {T : Ty} (hlib : LibTy Δ lib)
    (hs : StateTy Δ s T) : step lib s ≠ .fault .stuck := by
  intro h; have := step_sound hlib hs; rw [h] at this; cases this; contradiction

/-- The depth counter stays the stack's length, so `run`'s O(1) bound check is the stack bound. -/
theorem step_depth {lib : List Term} {s s' : State} (hd : DepthOK s) (h : step lib s = .next s') :
    DepthOK s' := by
  obtain ⟨c, k, d⟩ := s
  unfold DepthOK at hd ⊢
  simp only at hd
  subst hd
  cases c with
  | eval t env =>
    cases t <;> simp only [step, push] at h <;>
      (repeat' split at h) <;> (try simp at h) <;> (try (cases h; simp))
  | ret v =>
    cases k with
    | nil => simp [step] at h
    | cons f k =>
      cases f <;> simp only [step] at h <;>
        (repeat' split at h) <;> (try simp at h) <;> (try (cases h; simp))

/-- What a typed run may end with: a value of its type, or a named fault other than `stuck`. -/
def RunOK (Δ : List Ty) (T : Ty) : Outcome → Prop
  | .value v _ => ValTy Δ v T
  | .fault f _ => f ≠ .stuck

theorem run_sound {lib : List Term} {cap : Nat} {T : Ty} (hlib : LibTy Δ lib) :
    ∀ (n u : Nat) (s : State), StateTy Δ s T → RunOK Δ T (run lib cap n u s)
  | 0, _, _, _ => by simp [run, RunOK]
  | n + 1, u, s, hs => by
    have h := step_sound (lib := lib) hlib hs
    simp only [run]
    cases hst : step lib s with
    | halt v => rw [hst] at h; cases h; simpa [RunOK]
    | fault f => rw [hst] at h; cases h; simpa [RunOK]
    | next s' =>
      rw [hst] at h
      cases h with
      | next hs' =>
        by_cases hc : cap < s'.depth
        · simp [hc, RunOK]
        · simp only [hc, if_false]; exact run_sound hlib n (u + 1) s' hs'

/-- A checked program, run under any budget in a typed environment, never gets stuck: it ends
with a value of its type or a named budget/arithmetic fault, or the refusal its program wrote. -/
theorem eval_sound {lib : List Term} {b : Nat} {t : Term} {env : List Val} {Γ : List Ty}
    {T : Ty} (hlib : LibTy Δ lib) (he : EnvTy Δ env Γ) (ht : HasType Δ Γ t T) :
    RunOK Δ T (eval lib b t env) :=
  run_sound hlib _ _ _ (.eval he ht .nil)

/-- Only a primitive or a `refuse` faults: every other fault of `step` is `stuck`, so `ticks` and
`stack` come only from `run`, and (with `step_progress`) a typed state faults only in arithmetic or
by the refusal its program wrote (LANG-51). -/
theorem step_fault {lib : List Term} {s : State} {f : Fault} (h : step lib s = .fault f) :
    f = .stuck ∨ (∃ p a v k d, s = ⟨.ret v, .primR p a :: k, d⟩ ∧ primEval p a v = .error f) ∨
      ∃ T w env k d, s = ⟨.eval (.refuse T w) env, k, d⟩ ∧ f = .refused w := by
  obtain ⟨c, k, d⟩ := s
  cases c with
  | eval t env =>
    cases t with
    | refuse T w => simp only [step, Step.fault.injEq] at h; exact .inr (.inr ⟨T, w, env, k, d, rfl, h.symm⟩)
    | _ => left; simp only [step, push] at h <;> (repeat' split at h) <;> simp_all
  | ret v =>
    cases k with
    | nil => simp [step] at h
    | cons fr k =>
      cases fr with
      | primR p a =>
        simp only [step] at h
        split at h
        · simp at h
        · rename_i e he; cases h; exact .inr (.inl ⟨p, a, v, k, d, rfl, he⟩)
      | _ => left; simp only [step] at h <;> (repeat' split at h) <;> simp_all

theorem checkLib_sound {lib : List Term} (h : checkLib Δ lib = true) : LibTy Δ lib := by
  intro i T hT
  simp only [checkLib, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hi : i < lib.length := by
    have := (List.getElem?_eq_some_iff.mp hT).1; omega
  refine ⟨lib[i], List.getElem?_eq_getElem hi, ?_⟩
  have hmem : (lib[i], T) ∈ lib.zip Δ := by
    rw [List.mem_iff_getElem?]
    exact ⟨i, by simp [List.getElem?_zip_eq_some, List.getElem?_eq_getElem hi, hT]⟩
  exact check_iff.mp (hall _ hmem)

/-- End to end: a term the checker accepts, over a closure the checker accepts, run under any tick
budget, ends with a value of its type or a named fault that is not `stuck`. -/
theorem checked_never_stuck {lib : List Term} {t : Term} {T : Ty} {ticks : Nat}
    (hlib : checkLib Δ lib = true) (ht : check Δ t T = true) :
    RunOK Δ T (eval lib ticks t) :=
  eval_sound (checkLib_sound hlib) .nil (check_iff.mp ht)

end Nanodregg.Lang
