/-
# Lang.Proofs.Agree — the machine computes the reference semantics

`Ends lib s o n`: the machine, from `s`, ends with `o` (a value, or the fault a step raised) after
`n` steps, the stack bound ignored. `run_bigStep`: a run that ends with a value computed the
term's meaning (`BigStep`, Lang.Proofs.BigStep). `run_fault_bigStep`: a run that ends with an
arithmetic fault (anything but `stuck`, `ticks`, `stack`) computed the term's meaning too. With
`bigStep_deterministic`, two runs of one term that both end with a value or an arithmetic fault end
with the same one, because the LANGUAGE gives the term one meaning (`run_agree_meaning`).

The proof is a decomposition of machine runs: a run from `eval t env` on a stack `k` either ends in
a fault that is `t`'s meaning, or first returns `t`'s value `w` to `k` (`evalAgrees`); a run from a
`get ℓ` / `extend fs` frame first returns the selection's / extension's result (`selAgrees`,
`extAgrees`). By induction on the number of steps; a `stuck` ending is excluded (a checked program
never reaches it: `checked_never_stuck`).
-/
import Lang.Proofs.BigStep

namespace Nanodregg.Lang

variable {lib : List Term}

inductive Ends (lib : List Term) : State → (Except Fault Val) → Nat → Prop
  | halt {s v} : step lib s = .halt v → Ends lib s (.ok v) 1
  | fault {s f} : step lib s = .fault f → Ends lib s (.error f) 1
  | next {s s' o n} : step lib s = .next s' → Ends lib s' o n → Ends lib s o (n + 1)

theorem Ends.inv_next {s s' : State} {o : (Except Fault Val)} {n : Nat} (h : Ends lib s o n)
    (hs : step lib s = .next s') : ∃ n', n = n' + 1 ∧ Ends lib s' o n' := by
  cases h with
  | halt h => rw [hs] at h; cases h
  | fault h => rw [hs] at h; cases h
  | next h h' => rw [hs] at h; cases h; exact ⟨_, rfl, h'⟩

theorem Ends.inv_fault {s : State} {f : Fault} {o : (Except Fault Val)} {n : Nat} (h : Ends lib s o n)
    (hs : step lib s = .fault f) : o = .error f := by
  cases h with
  | halt h => rw [hs] at h; cases h
  | fault h => rw [hs] at h; cases h; rfl
  | next h _ => rw [hs] at h; cases h

theorem Ends.inv_halt {s : State} {v : Val} {o : (Except Fault Val)} {n : Nat} (h : Ends lib s o n)
    (hs : step lib s = .halt v) : o = .ok v := by
  cases h with
  | halt h => rw [hs] at h; cases h; rfl
  | fault h => rw [hs] at h; cases h
  | next h _ => rw [hs] at h; cases h

theorem Ends.pos {s : State} {o : (Except Fault Val)} {n : Nat} (h : Ends lib s o n) : 0 < n := by
  cases h <;> omega

/-- A primitive's frame pays its ticks (LANG-64) until the tick that computes it: a run from the
frame with `j` paid passes, no later, through the frame with some `j'` paid at which the next tick
computes (`primTicks ≤ j' + 1`). -/
theorem Ends.paid {p : Prim} {a v : Val} {k : List Frame} {d : Nat} {o : Except Fault Val} :
    ∀ (i j n : Nat), primTicks p a v ≤ j + 1 + i → Ends lib ⟨.ret v, .primR p a j :: k, d⟩ o n →
      ∃ j' n', n' ≤ n ∧ primTicks p a v ≤ j' + 1 ∧ Ends lib ⟨.ret v, .primR p a j' :: k, d⟩ o n'
  | 0, j, n, hi, h => ⟨j, n, Nat.le_refl _, by omega, h⟩
  | i + 1, j, n, hi, h => by
    by_cases hj : j + 1 < primTicks p a v
    · obtain ⟨n1, rfl, h1⟩ := h.inv_next (s' := ⟨.ret v, .primR p a (j + 1) :: k, d⟩)
        (by simp [step, primStep, hj])
      obtain ⟨j', n', hn, hj', h'⟩ := Ends.paid i (j + 1) n1 (by omega) h1
      exact ⟨j', n', by omega, hj', h'⟩
    · exact ⟨j, n, Nat.le_refl _, by omega, h⟩

/-- A run from `eval t env` on stack `k` ends in `t`'s faulting meaning, or returns `t`'s value. -/
def EvalAgrees (lib : List Term) (n : Nat) : Prop :=
  ∀ (t : Term) (env : Env) (k : List Frame) (d : Nat) (o : (Except Fault Val)), o ≠ .error .stuck →
    Ends lib ⟨.eval t env, k, d⟩ o n →
    (∃ e, o = .error e ∧ BigStep lib env t (.error e)) ∨
    (∃ w m, m < n ∧ BigStep lib env t (.ok w) ∧ Ends lib ⟨.ret w, k, d⟩ o m)

/-- A run returning `v` to a `get ℓ` frame ends in the selection's faulting meaning, or returns its
value to the rest of the stack. -/
def SelAgrees (lib : List Term) (n : Nat) : Prop :=
  ∀ (v : Val) (ℓ : Label) (k : List Frame) (d : Nat) (o : (Except Fault Val)), o ≠ .error .stuck →
    Ends lib ⟨.ret v, .get ℓ :: k, d + 1⟩ o n →
    (∃ e, o = .error e ∧ Sel lib v ℓ (.error e)) ∨
    (∃ w m, m < n ∧ Sel lib v ℓ (.ok w) ∧ Ends lib ⟨.ret w, k, d⟩ o m)

def ExtAgrees (lib : List Term) (n : Nat) : Prop :=
  ∀ (v : Val) (fs : List (Label × Term)) (env : Env) (k : List Frame) (d : Nat) (o : (Except Fault Val)),
    o ≠ .error .stuck → Ends lib ⟨.ret v, .extend fs env :: k, d + 1⟩ o n →
    (∃ e, o = .error e ∧ Ext lib v fs env (.error e)) ∨
    (∃ w m, m < n ∧ Ext lib v fs env (.ok w) ∧ Ends lib ⟨.ret w, k, d⟩ o m)


theorem agrees (N : Nat) :
    (∀ n ≤ N, EvalAgrees lib n) ∧ (∀ n ≤ N, SelAgrees lib n) ∧ (∀ n ≤ N, ExtAgrees lib n) := by
  induction N with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro n hn _ _ _ _ _ _ h; have := h.pos; omega
    · intro n hn _ _ _ _ _ _ h; have := h.pos; omega
    · intro n hn _ _ _ _ _ _ _ h; have := h.pos; omega
  | succ N ih =>
    obtain ⟨ihE, ihS, ihX⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro n hn t env k d o ho h
      cases t with
      | var i =>
        cases he : env[i]? with
        | none => exact absurd (h.inv_fault (by simp [step, he])) ho
        | some v =>
          obtain ⟨n1, rfl, h1⟩ := h.inv_next (s' := ⟨.ret v, k, d⟩) (by simp [step, he])
          exact .inr ⟨v, n1, by omega, .var he, h1⟩
      | lam A b =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .lam, h1⟩
      | nat v =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .nat, h1⟩
      | bool v =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .bool, h1⟩
      | bytes v =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .bytes, h1⟩
      | digest v =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .digest, h1⟩
      | record fs =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        exact .inr ⟨_, n1, by omega, .record, h1⟩
      | app f a =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) f env _ _ o ho h1 with ⟨e, rfl, hf⟩ | ⟨wf, m1, hm1, hf, h2⟩
        · exact .inl ⟨e, rfl, .appF hf⟩
        obtain ⟨m2, rfl, h3⟩ := h2.inv_next rfl
        rcases ihE m2 (by omega) a env _ _ o ho h3 with ⟨e, rfl, ha⟩ | ⟨wa, m3, hm3, ha, h4⟩
        · exact .inl ⟨e, rfl, .appA hf ha⟩
        cases wf
        case clo body cenv =>
          obtain ⟨m4, rfl, h5⟩ := h4.inv_next (s' := ⟨.eval body (wa :: cenv), k, d⟩) rfl
          rcases ihE m4 (by omega) body (wa :: cenv) k d o ho h5 with ⟨e, rfl, hb⟩ | ⟨w, m5, hm5, hb, h6⟩
          · exact .inl ⟨e, rfl, .app hf ha hb⟩
          · exact .inr ⟨w, m5, by omega, .app hf ha hb, h6⟩
        all_goals exact absurd (h4.inv_fault rfl) ho
      | fix t =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) t env _ _ o ho h1 with ⟨e, rfl, ht⟩ | ⟨wt, m1, hm1, ht, h2⟩
        · exact .inl ⟨e, rfl, .fixE ht⟩
        cases wt
        case clo body cenv =>
          obtain ⟨m2, rfl, h3⟩ := h2.inv_next (s' := ⟨.ret (.knot body cenv), k, d⟩) rfl
          exact .inr ⟨_, m2, by omega, .fix ht, h3⟩
        all_goals exact absurd (h2.inv_fault rfl) ho
      | prim p a b =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) a env _ _ o ho h1 with ⟨e, rfl, ha⟩ | ⟨x, m1, hm1, ha, h2⟩
        · exact .inl ⟨e, rfl, .primL ha⟩
        obtain ⟨m2, rfl, h3⟩ := h2.inv_next rfl
        rcases ihE m2 (by omega) b env _ _ o ho h3 with ⟨e, rfl, hb⟩ | ⟨y, m3, hm3, hb, h4⟩
        · exact .inl ⟨e, rfl, .primR ha hb⟩
        obtain ⟨j, m4', hm4, hj, h4⟩ := Ends.paid (primTicks p x y) 0 _ (by omega) h4
        have hj' : ¬ j + 1 < primTicks p x y := by omega
        cases hp : primEval p x y with
        | ok r =>
          obtain ⟨m4, rfl, h5⟩ := h4.inv_next (s' := ⟨.ret r, k, d⟩) (by simp [step, primStep, hj', hp])
          exact .inr ⟨r, m4, by omega, hp ▸ .prim ha hb (by rw [hp]; simp), h5⟩
        | error e =>
          have := h4.inv_fault (f := e) (by simp [step, primStep, hj', hp])
          subst this
          have hne : primEval p x y ≠ .error .stuck := by rw [hp]; exact ho
          exact .inl ⟨e, rfl, hp ▸ .prim ha hb hne⟩
      | get t ℓ =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) t env _ _ o ho h1 with ⟨e, rfl, ht⟩ | ⟨v, m1, hm1, ht, h2⟩
        · exact .inl ⟨e, rfl, .getE ht⟩
        rcases ihS m1 (by omega) v ℓ k d o ho h2 with ⟨e, rfl, hs⟩ | ⟨w, m2, hm2, hs, h3⟩
        · exact .inl ⟨e, rfl, .get ht hs⟩
        · exact .inr ⟨w, m2, by omega, .get ht hs, h3⟩
      | extend t fs =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) t env _ _ o ho h1 with ⟨e, rfl, ht⟩ | ⟨v, m1, hm1, ht, h2⟩
        · exact .inl ⟨e, rfl, .extendE ht⟩
        rcases ihX m1 (by omega) v fs env k d o ho h2 with ⟨e, rfl, hx⟩ | ⟨w, m2, hm2, hx, h3⟩
        · exact .inl ⟨e, rfl, .extend ht hx⟩
        · exact .inr ⟨w, m2, by omega, .extend ht hx, h3⟩
      | inj A ℓ t =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) t env _ _ o ho h1 with ⟨e, rfl, ht⟩ | ⟨w, m1, hm1, ht, h2⟩
        · exact .inl ⟨e, rfl, .injE ht⟩
        obtain ⟨m2, rfl, h3⟩ := h2.inv_next (s' := ⟨.ret (.inj ℓ w), k, d⟩) rfl
        exact .inr ⟨_, m2, by omega, .inj ht, h3⟩
      | case t arms =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) t env _ _ o ho h1 with ⟨e, rfl, ht⟩ | ⟨v, m1, hm1, ht, h2⟩
        · exact .inl ⟨e, rfl, .caseE ht⟩
        cases v
        case inj ℓ w =>
          cases hf : Row.find? ℓ arms with
          | none => exact absurd (h2.inv_fault (by simp [step, hf])) ho
          | some body =>
            obtain ⟨m2, rfl, h3⟩ := h2.inv_next (s' := ⟨.eval body (w :: env), k, d⟩) (by simp [step, hf])
            rcases ihE m2 (by omega) body (w :: env) k d o ho h3 with ⟨e, rfl, hb⟩ | ⟨r, m3, hm3, hb, h4⟩
            · exact .inl ⟨e, rfl, .case ht hf hb⟩
            · exact .inr ⟨r, m3, by omega, .case ht hf hb, h4⟩
        all_goals exact absurd (h2.inv_fault rfl) ho
      | ite c a b =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) c env _ _ o ho h1 with ⟨e, rfl, hc⟩ | ⟨v, m1, hm1, hc, h2⟩
        · exact .inl ⟨e, rfl, .iteE hc⟩
        cases v
        case bool bv =>
          cases bv with
          | true =>
            obtain ⟨m2, rfl, h3⟩ := h2.inv_next (s' := ⟨.eval a env, k, d⟩) rfl
            rcases ihE m2 (by omega) a env k d o ho h3 with ⟨e, rfl, ha⟩ | ⟨r, m3, hm3, ha, h4⟩
            · exact .inl ⟨e, rfl, .iteT hc ha⟩
            · exact .inr ⟨r, m3, by omega, .iteT hc ha, h4⟩
          | false =>
            obtain ⟨m2, rfl, h3⟩ := h2.inv_next (s' := ⟨.eval b env, k, d⟩) rfl
            rcases ihE m2 (by omega) b env k d o ho h3 with ⟨e, rfl, hb⟩ | ⟨r, m3, hm3, hb, h4⟩
            · exact .inl ⟨e, rfl, .iteF hc hb⟩
            · exact .inr ⟨r, m3, by omega, .iteF hc hb, h4⟩
        all_goals exact absurd (h2.inv_fault rfl) ho
      | ref i =>
        cases hi : lib[i]? with
        | none => exact absurd (h.inv_fault (by simp [step, hi])) ho
        | some body =>
          obtain ⟨n1, rfl, h1⟩ := h.inv_next (s' := ⟨.eval body [], k, d⟩) (by simp [step, hi])
          rcases ihE n1 (by omega) body [] k d o ho h1 with ⟨e, rfl, hb⟩ | ⟨r, m1, hm1, hb, h2⟩
          · exact .inl ⟨e, rfl, .ref hi hb⟩
          · exact .inr ⟨r, m1, by omega, .ref hi hb, h2⟩
      | refuse A w =>
        have := h.inv_fault (f := .refused w) rfl
        subst this
        exact .inl ⟨_, rfl, .refuse⟩
      | hole n σ =>
        have := h.inv_fault (f := .refused "holeUnresolved".toUTF8) rfl
        subst this
        exact .inl ⟨_, rfl, .hole⟩
    · intro n hn v ℓ k d o ho h
      cases v
      case record fs =>
        cases hf : Row.find? ℓ fs with
        | none => exact absurd (h.inv_fault (by simp [step, hf])) ho
        | some p =>
          obtain ⟨t, env⟩ := p
          obtain ⟨n1, rfl, h1⟩ := h.inv_next (s' := ⟨.eval t env, k, d⟩) (by simp [step, hf])
          rcases ihE n1 (by omega) t env k d o ho h1 with ⟨e, rfl, ht⟩ | ⟨w, m1, hm1, ht, h2⟩
          · exact .inl ⟨e, rfl, .field hf ht⟩
          · exact .inr ⟨w, m1, by omega, .field hf ht, h2⟩
      case knot body env =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) body _ _ _ o ho h1 with ⟨e, rfl, hb⟩ | ⟨v', m1, hm1, hb, h2⟩
        · exact .inl ⟨e, rfl, .knotE hb⟩
        rcases ihS m1 (by omega) v' ℓ k d o ho h2 with ⟨e, rfl, hs⟩ | ⟨w, m2, hm2, hs, h3⟩
        · exact .inl ⟨e, rfl, .knot hb hs⟩
        · exact .inr ⟨w, m2, by omega, .knot hb hs, h3⟩
      all_goals exact absurd (h.inv_fault rfl) ho
    · intro n hn v fs env k d o ho h
      cases v
      case record gs =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next (s' := ⟨.ret (.record (Row.merge gs (suspend env fs))), k, d⟩) rfl
        exact .inr ⟨_, n1, by omega, .record, h1⟩
      case knot body kenv =>
        obtain ⟨n1, rfl, h1⟩ := h.inv_next rfl
        rcases ihE n1 (by omega) body _ _ _ o ho h1 with ⟨e, rfl, hb⟩ | ⟨v', m1, hm1, hb, h2⟩
        · exact .inl ⟨e, rfl, .knotE hb⟩
        rcases ihX m1 (by omega) v' fs env k d o ho h2 with ⟨e, rfl, hx⟩ | ⟨w, m2, hm2, hx, h3⟩
        · exact .inl ⟨e, rfl, .knot hb hx⟩
        · exact .inr ⟨w, m2, by omega, .knot hb hx, h3⟩
      all_goals exact absurd (h.inv_fault rfl) ho

/-- A run that ends with a value or a step's fault, under any stack bound, is an `Ends`. -/
theorem run_ends {cap : Nat} : ∀ (fuel u : Nat) (s : State) {o : Outcome},
    run lib cap fuel u s = o →
      (∀ v used, o = .value v used → ∃ n, Ends lib s (.ok v) n) ∧
      (∀ f used, o = .fault f used → f ≠ .ticks → f ≠ .stack → ∃ n, Ends lib s (.error f) n)
  | 0, u, s, o, h => by
    subst h
    refine ⟨fun _ _ h => by simp [run] at h, fun f _ h ht _ => ?_⟩
    simp only [run, Outcome.fault.injEq] at h
    exact absurd h.1.symm ht
  | fuel + 1, u, s, o, h => by
    subst h
    simp only [run]
    cases hs : step lib s with
    | halt v =>
      refine ⟨fun v' _ h => ?_, fun _ _ h => by simp at h⟩
      simp only [Outcome.value.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨1, .halt hs⟩
    | fault f =>
      refine ⟨fun _ _ h => by simp at h, fun f' _ h _ _ => ?_⟩
      simp only [Outcome.fault.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨1, .fault hs⟩
    | next s' =>
      simp only
      split
      · exact ⟨fun _ _ h => by simp at h, fun f _ h _ hst => by
          simp only [Outcome.fault.injEq] at h; exact absurd h.1.symm hst⟩
      · obtain ⟨hv, hf⟩ := run_ends fuel (u + 1) s' rfl
        exact ⟨fun v used h => (hv v used h).elim fun n hn => ⟨n + 1, .next hs hn⟩,
          fun f used h ht hst => (hf f used h ht hst).elim fun n hn => ⟨n + 1, .next hs hn⟩⟩

theorem evalAgrees_init {t : Term} {env : Env} {o : (Except Fault Val)} {n : Nat} (ho : o ≠ .error .stuck)
    (h : Ends lib (State.init t env) o n) :
    (∃ e, o = .error e ∧ BigStep lib env t (.error e)) ∨ (∃ w, o = .ok w ∧ BigStep lib env t (.ok w)) := by
  rcases (agrees n).1 n (Nat.le_refl _) t env [] 0 o ho h with ⟨e, he, hb⟩ | ⟨w, m, _, hb, hw⟩
  · exact .inl ⟨e, he, hb⟩
  · exact .inr ⟨w, hw.inv_halt rfl, hb⟩

/-- **The machine computes the meaning.** A run that ends with a value, under any tick budget and
any stack bound, ended with the term's `BigStep` value. -/
theorem run_bigStep {cap fuel used : Nat} {t : Term} {env : Env} {v : Val}
    (h : run lib cap fuel 0 (State.init t env) = .value v used) : BigStep lib env t (.ok v) := by
  obtain ⟨n, hn⟩ := (run_ends fuel 0 _ h).1 v used rfl
  rcases evalAgrees_init (by simp) hn with ⟨e, he, _⟩ | ⟨w, hw, hb⟩
  · cases he
  · cases hw; exact hb

/-- A run that ends with an arithmetic fault ended with the term's `BigStep` fault. -/
theorem run_fault_bigStep {cap fuel used : Nat} {t : Term} {env : Env} {f : Fault}
    (h : run lib cap fuel 0 (State.init t env) = .fault f used) (hs : f ≠ .stuck) (ht : f ≠ .ticks)
    (hst : f ≠ .stack) : BigStep lib env t (.error f) := by
  obtain ⟨n, hn⟩ := (run_ends fuel 0 _ h).2 f used rfl ht hst
  rcases evalAgrees_init (fun e => hs (by cases e; rfl)) hn with ⟨e, he, hb⟩ | ⟨w, hw, _⟩
  · cases he; exact hb
  · cases hw

/-- Determinism is the language's: two runs of one term, under ANY budgets and stack bounds, that
both end with a value end with the same value. -/
theorem run_agree_meaning {cap cap' fuel fuel' used used' : Nat} {t : Term} {env : Env} {v v' : Val}
    (h : run lib cap fuel 0 (State.init t env) = .value v used)
    (h' : run lib cap' fuel' 0 (State.init t env) = .value v' used') : v = v' := by
  have := bigStep_deterministic (run_bigStep h) (run_bigStep h')
  cases this; rfl

/-- No budget turns a term's value into an arithmetic fault: one meaning per term. -/
theorem run_value_not_fault {cap cap' fuel fuel' used used' : Nat} {t : Term} {env : Env} {v : Val}
    {f : Fault} (h : run lib cap fuel 0 (State.init t env) = .value v used)
    (h' : run lib cap' fuel' 0 (State.init t env) = .fault f used') (hs : f ≠ .stuck)
    (ht : f ≠ .ticks) (hst : f ≠ .stack) : False := by
  have := bigStep_deterministic (run_bigStep h) (run_fault_bigStep h' hs ht hst)
  cases this

end Nanodregg.Lang
