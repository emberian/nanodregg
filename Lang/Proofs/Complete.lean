/-
# Lang.Proofs.Complete — every meaning is computed, given the resources

The converse of `Lang.Proofs.Agree`: if `t` means `.ok v` (`BigStep`), the machine reaches `v` under
every tick budget and stack bound past some finite pair (`bigStep_run`); if `t` means a fault, the
machine raises that fault (`bigStep_run_fault`). With `run_bigStep` this says the CEK machine and the
reference relation define the same function on every term the machine finishes: a value is the
machine's answer iff it is the term's meaning, budgets permitting.

`Reach lib cap s s' n`: `n` machine transitions from `s` to `s'`, each new state within the stack
bound `cap` (as `run` checks it). `Leads lib cap s k d r n`: from `s` the machine either reaches
`ret w` on stack `k` at depth `d` in `n` transitions (`r = .ok w`), or reaches a state whose step
raises `e` (`r = .error e`), `n` ticks counting that step.

Both directions are proved over the sized derivation (`derives_leads`, `Derives`): the machine
takes at least one transition per rule instance. `derives_lt_used`: a run that returns charges
more ticks than its meaning's derivation has rule instances (THE BAR's ratio is above 1).
-/
import Lang.Proofs.Derives

namespace Nanodregg.Lang

variable {lib : List Term}

inductive Reach (lib : List Term) (cap : Nat) : State → State → Nat → Prop
  | refl {s} : Reach lib cap s s 0
  | next {s s1 s' n} : step lib s = .next s1 → s1.depth ≤ cap → Reach lib cap s1 s' n →
      Reach lib cap s s' (n + 1)

theorem Reach.trans {cap : Nat} {s s1 s2 : State} {n m : Nat} (h1 : Reach lib cap s s1 n)
    (h2 : Reach lib cap s1 s2 m) : Reach lib cap s s2 (n + m) := by
  induction h1 with
  | refl => simpa using h2
  | next hs hd _ ih => rw [Nat.add_right_comm]; exact .next hs hd (ih h2)

theorem Reach.mono {cap cap' : Nat} {s s' : State} {n : Nat} (h : Reach lib cap s s' n)
    (hc : cap ≤ cap') : Reach lib cap' s s' n := by
  induction h with
  | refl => exact .refl
  | next hs hd _ ih => exact .next hs (Nat.le_trans hd hc) ih

/-- A reach is a prefix of every run long enough to cover it. -/
theorem run_reach {cap : Nat} {s s' : State} {n : Nat} (h : Reach lib cap s s' n) :
    ∀ (m u : Nat), run lib cap (n + m) u s = run lib cap m (u + n) s' := by
  induction h with
  | refl => intro m u; simp
  | @next s s1 s' n hs hd _ ih =>
    intro m u
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [run, hs, show ¬ cap < s1.depth by omega, if_false]
    rw [ih m (u + 1)]; congr 1; omega

/-- From `s` the machine returns `w` to stack `k` at depth `d` in `n` transitions (`ok`), or reaches
in `n` transitions a state whose step raises `e`, `n + 1` ticks counting that step (`err`). The
count is what `run` charges for it. -/
inductive Leads (lib : List Term) (cap : Nat) (s : State) (k : List Frame) (d : Nat) :
    Except Fault Val → Nat → Prop
  | ok {w n} : Reach lib cap s ⟨.ret w, k, d⟩ n → Leads lib cap s k d (.ok w) n
  | err {e s' n} : Reach lib cap s s' n → step lib s' = .fault e → Leads lib cap s k d (.error e) (n + 1)

theorem Leads.mono {cap cap' : Nat} {s : State} {k : List Frame} {d : Nat} {r : (Except Fault Val)} {n : Nat}
    (h : Leads lib cap s k d r n) (hc : cap ≤ cap') : Leads lib cap' s k d r n := by
  cases h with
  | ok h => exact .ok (h.mono hc)
  | err h hs => exact .err (h.mono hc) hs

/-- One transition in front. -/
theorem Leads.cons {cap : Nat} {s s1 : State} {k : List Frame} {d : Nat} {r : (Except Fault Val)} {n : Nat}
    (hs : step lib s = .next s1) (hd : s1.depth ≤ cap) (h : Leads lib cap s1 k d r n) :
    Leads lib cap s k d r (n + 1) := by
  cases h with
  | ok h => exact .ok (.next hs hd h)
  | err h hf => exact .err (.next hs hd h) hf

/-- A value returned to an inner stack, then the rest. -/
theorem Leads.bind {cap : Nat} {s : State} {k k' : List Frame} {d d' : Nat} {w : Val} {r : (Except Fault Val)}
    {n m : Nat} (h : Leads lib cap s k' d' (.ok w) n) (h2 : Leads lib cap ⟨.ret w, k', d'⟩ k d r m) :
    Leads lib cap s k d r (n + m) := by
  cases h with
  | ok h =>
    cases h2 with
    | ok h2 => exact .ok (h.trans h2)
    | err h2 hf => exact .err (h.trans h2) hf

/-- A fault on an inner stack is the fault of the whole. -/
theorem Leads.lift {cap : Nat} {s : State} {k k' : List Frame} {d d' : Nat} {e : Fault} {n : Nat}
    (h : Leads lib cap s k' d' (.error e) n) : Leads lib cap s k d (.error e) n := by
  cases h with
  | err h hf => exact .err h hf

/-- A step that raises `e` at once: one tick. -/
theorem Leads.now {cap : Nat} {s : State} {k : List Frame} {d : Nat} {e : Fault}
    (hs : step lib s = .fault e) : Leads lib cap s k d (.error e) 1 := .err .refl hs

/-- From a primitive's frame with `j` of its ticks paid, the machine pays the rest and then computes
it (LANG-64): `primTicks - j` transitions, ending in the primitive's meaning. -/
theorem prim_leads {cap : Nat} {p : Prim} {a v : Val} {k : List Frame} {d : Nat} (hd : d + 1 ≤ cap) :
    ∀ (i j : Nat), j + 1 + i = primTicks p a v →
      Leads lib cap ⟨.ret v, .primR p a j :: k, d + 1⟩ k d (primEval p a v) (i + 1)
  | 0, j, hi => by
    have hj : ¬ j + 1 < primTicks p a v := by omega
    cases hp : primEval p a v with
    | ok r =>
      exact .cons (s1 := ⟨.ret r, k, d⟩) (by simp [step, primStep, hj, hp]) (by dsimp only; omega) (.ok .refl)
    | error e => exact .now (by simp [step, primStep, hj, hp])
  | i + 1, j, hi => by
    have hj : j + 1 < primTicks p a v := by omega
    exact .cons (s1 := ⟨.ret v, .primR p a (j + 1) :: k, d + 1⟩) (by simp [step, primStep, hj])
      (by dsimp only; omega) (prim_leads hd i (j + 1) (by omega))

/-! ## The machine takes at least as many transitions as the meaning has rule instances

`derives_leads`: a derivation of size `n` (`Derives`, Lang.Proofs.Derives) is followed by the
machine in `m ≥ n` transitions: every rule instance costs it at least one. The stack bound it
needs is the derivation's nesting. -/

mutual
theorem derives_leads : ∀ {env : Env} {t : Term} {r : (Except Fault Val)} {n : Nat}, Derives lib env t r n →
    ∀ (k : List Frame) (d : Nat), ∃ D m, n ≤ m ∧ Leads lib (d + D) ⟨.eval t env, k, d⟩ k d r m
  | _, _, _, _, .var he, k, d => ⟨0, _, Nat.le_refl _, .cons (by simp [step, he]) (Nat.le_refl _) (.ok .refl)⟩
  | _, _, _, _, .lam, k, d | _, _, _, _, .nat, k, d | _, _, _, _, .bool, k, d | _, _, _, _, .bytes, k, d
  | _, _, _, _, .digest, k, d
  | _, _, _, _, .record, k, d => ⟨0, _, Nat.le_refl _, .cons rfl (Nat.le_refl _) (.ok .refl)⟩
  | _, _, _, _, .refuse, k, d => ⟨0, _, Nat.le_refl _, .now (by simp [step])⟩
  | _, _, _, _, .app (a := a) (env := env) (b := b) (cenv := cenv) hf ha hb, k, d => by
    obtain ⟨Df, mf, hf', lf⟩ := derives_leads hf (.appL a env :: k) (d + 1)
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha (.appR (.clo b cenv) :: k) (d + 1)
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb k d
    refine ⟨Df + Da + Db + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lf.mono (by omega))
      (.cons rfl (by dsimp only; omega) (.bind (la.mono (by omega))
        (.cons rfl (by dsimp only; omega) (lb.mono (by omega))))))⟩
    omega
  | _, _, _, _, .appF (a := a) (env := env) hf, k, d => by
    obtain ⟨Df, mf, hf', lf⟩ := derives_leads hf (.appL a env :: k) (d + 1)
    exact ⟨Df + 1, _, by omega, .cons rfl (by dsimp only; omega) (lf.mono (by omega)).lift⟩
  | _, _, _, _, .appA (a := a) (env := env) (v := v) hf ha, k, d => by
    obtain ⟨Df, mf, hf', lf⟩ := derives_leads hf (.appL a env :: k) (d + 1)
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha (.appR v :: k) (d + 1)
    refine ⟨Df + Da + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lf.mono (by omega))
      (.cons rfl (by dsimp only; omega) (la.mono (by omega)).lift))⟩
    omega
  | _, _, _, _, .fix (env := env) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.fix :: k) (d + 1)
    refine ⟨Dt + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lt.mono (by omega))
      (.cons rfl (by dsimp only; omega) (.ok .refl)))⟩
    omega
  | _, _, _, _, .fixE ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.fix :: k) (d + 1)
    exact ⟨Dt + 1, _, by omega, .cons rfl (by dsimp only; omega) (lt.mono (by omega)).lift⟩
  | _, _, _, _, .prim (env := env) (p := p) (b := b) (x := x) (y := y) ha hb _, k, d => by
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha (.primL p b env :: k) (d + 1)
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.primR p x 0 :: k) (d + 1)
    have hpos : primTicks p x y = (primBytes p x y - 1) / Bounds.wordBytes + 1 := rfl
    have hi : 0 + 1 + (primTicks p x y - 1) = primTicks p x y := by
      rw [hpos, Nat.add_sub_cancel, Nat.zero_add, Nat.add_comm]
    have hlast : Leads lib (d + (Da + Db + 1)) ⟨.ret y, .primR p x 0 :: k, d + 1⟩ k d (primEval p x y)
        (primTicks p x y - 1 + 1) :=
      prim_leads (p := p) (a := x) (v := y) (by omega) _ 0 hi
    refine ⟨Da + Db + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (la.mono (by omega))
      (.cons rfl (by dsimp only; omega) (.bind (lb.mono (by omega)) hlast)))⟩
    omega
  | _, _, _, _, .primL (env := env) (p := p) (b := b) ha, k, d => by
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha (.primL p b env :: k) (d + 1)
    exact ⟨Da + 1, _, by omega, .cons rfl (by dsimp only; omega) (la.mono (by omega)).lift⟩
  | _, _, _, _, .primR (env := env) (p := p) (b := b) (x := x) ha hb, k, d => by
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha (.primL p b env :: k) (d + 1)
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.primR p x 0 :: k) (d + 1)
    refine ⟨Da + Db + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (la.mono (by omega))
      (.cons rfl (by dsimp only; omega) (lb.mono (by omega)).lift))⟩
    omega
  | _, _, _, _, .get (ℓ := ℓ) ht hs, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.get ℓ :: k) (d + 1)
    obtain ⟨Ds, ms, hs', ls⟩ := dsel_leads hs k d
    refine ⟨Dt + Ds + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lt.mono (by omega)) (ls.mono (by omega)))⟩
    omega
  | _, _, _, _, .getE (ℓ := ℓ) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.get ℓ :: k) (d + 1)
    exact ⟨Dt + 1, _, by omega, .cons rfl (by dsimp only; omega) (lt.mono (by omega)).lift⟩
  | _, _, _, _, .extend (env := env) (fs := fs) ht hx, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.extend fs env :: k) (d + 1)
    obtain ⟨Dx, mx, hx', lx⟩ := dext_leads hx k d
    refine ⟨Dt + Dx + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lt.mono (by omega)) (lx.mono (by omega)))⟩
    omega
  | _, _, _, _, .extendE (env := env) (fs := fs) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.extend fs env :: k) (d + 1)
    exact ⟨Dt + 1, _, by omega, .cons rfl (by dsimp only; omega) (lt.mono (by omega)).lift⟩
  | _, _, _, _, .inj (ℓ := ℓ) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.inj ℓ :: k) (d + 1)
    refine ⟨Dt + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lt.mono (by omega))
      (.cons rfl (by dsimp only; omega) (.ok .refl)))⟩
    omega
  | _, _, _, _, .injE (ℓ := ℓ) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.inj ℓ :: k) (d + 1)
    exact ⟨Dt + 1, _, by omega, .cons rfl (by dsimp only; omega) (lt.mono (by omega)).lift⟩
  | _, _, _, _, .case (env := env) (arms := arms) (w := w) (body := body) ht hf hb, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.case arms env :: k) (d + 1)
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb k d
    refine ⟨Dt + Db + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lt.mono (by omega))
      (.cons (s1 := ⟨.eval body (w :: env), k, d⟩) (by simp [step, hf]) (by dsimp only; omega)
        (lb.mono (by omega))))⟩
    omega
  | _, _, _, _, .caseE (env := env) (arms := arms) ht, k, d => by
    obtain ⟨Dt, mt, ht', lt⟩ := derives_leads ht (.case arms env :: k) (d + 1)
    exact ⟨Dt + 1, _, by omega, .cons rfl (by dsimp only; omega) (lt.mono (by omega)).lift⟩
  | _, _, _, _, .iteT (env := env) (a := a) (b := b) hc ha, k, d => by
    obtain ⟨Dc, mc, hc', lc⟩ := derives_leads hc (.ite a b env :: k) (d + 1)
    obtain ⟨Da, ma, ha', la⟩ := derives_leads ha k d
    refine ⟨Dc + Da + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lc.mono (by omega))
      (.cons rfl (by dsimp only; omega) (la.mono (by omega))))⟩
    omega
  | _, _, _, _, .iteF (env := env) (a := a) (b := b) hc hb, k, d => by
    obtain ⟨Dc, mc, hc', lc⟩ := derives_leads hc (.ite a b env :: k) (d + 1)
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb k d
    refine ⟨Dc + Db + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lc.mono (by omega))
      (.cons rfl (by dsimp only; omega) (lb.mono (by omega))))⟩
    omega
  | _, _, _, _, .iteE (env := env) (a := a) (b := b) hc, k, d => by
    obtain ⟨Dc, mc, hc', lc⟩ := derives_leads hc (.ite a b env :: k) (d + 1)
    exact ⟨Dc + 1, _, by omega, .cons rfl (by dsimp only; omega) (lc.mono (by omega)).lift⟩
  | _, _, _, _, .ref (body := body) hi hb, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb k d
    exact ⟨Db, _, by omega, .cons (s1 := ⟨.eval body [], k, d⟩) (by simp [step, hi]) (by dsimp only; omega) lb⟩

theorem dsel_leads : ∀ {v : Val} {ℓ : Label} {r : (Except Fault Val)} {n : Nat}, DSel lib v ℓ r n →
    ∀ (k : List Frame) (d : Nat), ∃ D m, n ≤ m ∧ Leads lib (d + D) ⟨.ret v, .get ℓ :: k, d + 1⟩ k d r m
  | _, _, _, _, .field (t := t) (env := env) hf hb, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb k d
    exact ⟨Db, _, by omega, .cons (s1 := ⟨.eval t env, k, d⟩) (by simp [step, hf]) (by dsimp only; omega) lb⟩
  | _, _, _, _, .knot (ℓ := ℓ) hb hs, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.get ℓ :: k) (d + 1)
    obtain ⟨Ds, ms, hs', ls⟩ := dsel_leads hs k d
    refine ⟨Db + Ds + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lb.mono (by omega)) (ls.mono (by omega)))⟩
    omega
  | _, _, _, _, .knotE (ℓ := ℓ) hb, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.get ℓ :: k) (d + 1)
    exact ⟨Db + 1, _, by omega, .cons rfl (by dsimp only; omega) (lb.mono (by omega)).lift⟩

theorem dext_leads : ∀ {v : Val} {fs : List (Label × Term)} {env : Env} {r : (Except Fault Val)} {n : Nat},
    DExt lib v fs env r n →
    ∀ (k : List Frame) (d : Nat), ∃ D m, n ≤ m ∧ Leads lib (d + D) ⟨.ret v, .extend fs env :: k, d + 1⟩ k d r m
  | _, _, _, _, _, .record, k, d => ⟨0, _, Nat.le_refl _, .cons rfl (by dsimp only; omega) (.ok .refl)⟩
  | _, _, _, _, _, .knot (fs := fs) (env := env) hb hx, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.extend fs env :: k) (d + 1)
    obtain ⟨Dx, mx, hx', lx⟩ := dext_leads hx k d
    refine ⟨Db + Dx + 1, _, ?_, .cons rfl (by dsimp only; omega) (.bind (lb.mono (by omega)) (lx.mono (by omega)))⟩
    omega
  | _, _, _, _, _, .knotE (fs := fs) (env := env) hb, k, d => by
    obtain ⟨Db, mb, hb', lb⟩ := derives_leads hb (.extend fs env :: k) (d + 1)
    exact ⟨Db + 1, _, by omega, .cons rfl (by dsimp only; omega) (lb.mono (by omega)).lift⟩
end

/-- **Every meaning is computed.** If `t` means the value `v`, the machine returns `v` under every
stack bound from some `D` and every tick budget past some `n`. -/
theorem bigStep_run {t : Term} {env : Env} {v : Val} (h : BigStep lib env t (.ok v)) :
    ∃ D n, ∀ cap fuel, D ≤ cap → n < fuel → ∃ used, run lib cap fuel 0 (State.init t env) = .value v used := by
  obtain ⟨_, hd⟩ := bigStep_derives h
  obtain ⟨D, _, -, hl⟩ := derives_leads hd [] 0
  cases hl with
  | ok hr =>
    rename_i n
    refine ⟨0 + D, n, fun cap fuel hc hf => ⟨n + 1, ?_⟩⟩
    obtain ⟨m, rfl⟩ : ∃ m, fuel = n + (m + 1) := ⟨fuel - n - 1, by omega⟩
    rw [State.init, run_reach (hr.mono hc) (m + 1) 0]
    simp [run, step]

/-- If `t` means a fault, the machine raises it, budgets permitting. -/
theorem bigStep_run_fault {t : Term} {env : Env} {e : Fault} (h : BigStep lib env t (.error e)) :
    ∃ D n, ∀ cap fuel, D ≤ cap → n < fuel → ∃ used, run lib cap fuel 0 (State.init t env) = .fault e used := by
  obtain ⟨_, hd⟩ := bigStep_derives h
  obtain ⟨D, _, -, hl⟩ := derives_leads hd [] 0
  cases hl with
  | err hr hs =>
    rename_i s' n
    refine ⟨0 + D, n, fun cap fuel hc hf => ⟨n + 1, ?_⟩⟩
    obtain ⟨m, rfl⟩ : ∃ m, fuel = n + (m + 1) := ⟨fuel - n - 1, by omega⟩
    rw [State.init, run_reach (hr.mono hc) (m + 1) 0]
    simp [run, hs]

/-! ## Required ≤ ticks: a run that returns pays at least one tick per rule instance -/

/-- A run that returns follows every reach from its state: the reach's transitions are a prefix
of the run's, whatever stack bound the reach was taken under. -/
theorem reach_value {cap cap' : Nat} {s s' : State} {n : Nat} (h : Reach lib cap' s s' n) :
    ∀ {fuel u : Nat} {v : Val} {used : Nat}, run lib cap fuel u s = .value v used →
      ∃ fuel', fuel = fuel' + n ∧ run lib cap fuel' (u + n) s' = .value v used := by
  induction h with
  | refl => intro fuel u v used hr; exact ⟨fuel, rfl, hr⟩
  | @next s s1 s' n hs _ _ ih =>
    intro fuel u v used hr
    cases fuel with
    | zero => simp [run] at hr
    | succ f =>
      simp only [run, hs] at hr
      split at hr
      · cases hr
      · obtain ⟨f', rfl, hr'⟩ := ih hr
        exact ⟨f', by omega, by rw [show u + (n + 1) = u + 1 + n by omega]; exact hr'⟩

/-- **Ticks bound the derivation**: if `t` means `v` by a derivation of `n` rule instances and the
machine returns from `t` (under any stack bound and budget), it charged more than `n` ticks,
within its budget. So `n < used ≤ fuel`: the machine pays at least one tick per rule instance. -/
theorem derives_lt_used {t : Term} {env : Env} {v v' : Val} {n cap fuel used : Nat}
    (hd : Derives lib env t (.ok v) n) (hr : run lib cap fuel 0 (State.init t env) = .value v' used) :
    n < used ∧ used ≤ fuel := by
  obtain ⟨D, m, hnm, hl⟩ := derives_leads hd [] 0
  cases hl with
  | ok hreach =>
    obtain ⟨f', rfl, hr'⟩ := reach_value hreach hr
    cases f' with
    | zero => simp [run] at hr'
    | succ f =>
      simp only [run, step] at hr'
      cases hr'
      omega

end Nanodregg.Lang
