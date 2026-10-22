/- Guarded contextual closure: ClosureStatements. Moved without statement changes from Closure. -/
import Lang.Contextual.Closure

namespace Nanodregg.Lang.Contextual

variable {D : CalculusData} {E : Type}
  {HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop}


/-! ## The laws of a calculus, and the statements over closures -/

/-- The LAWS of a contextual calculus over its data `D` and a typing relation `HasTy`
(`HasTy Ω Ψ M A` is `Ω; Ψ ⊢ M : A`, meta-context `Ω`), each named after the CMTT fact it stands for. -/
structure CalculusLaws (D : CalculusData)
    (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) : Prop where
  /-- CMTT's meta-substitution lemma, partial form: the filled holes leave the meta-context. -/
  msubst_lemma : ∀ {Ω : List (HoleDecl D.Ctx D.Ty)} {Γ : D.Ctx} {P : D.Tm} {T : D.Ty}
    (σ : Nat → Option D.Tm), HasTy Ω Γ P T →
    (∀ d ∈ Ω, ∀ M, σ d.name = some M → HasTy [] d.ctx M d.ty) →
    HasTy (Ω.filter fun d => (σ d.name).isNone) Γ (D.msubst σ P) T
  check_sound : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty}, D.check Ψ M A = true → HasTy [] Ψ M A
  /-- The checker is complete: a `false` verdict is a refutation of typing, not an omission. -/
  check_complete : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty}, HasTy [] Ψ M A → D.check Ψ M A = true
  strengthen_lemma : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty} {x : Nat}, HasTy [] Ψ M A →
    D.uses M x = false → HasTy [] (D.drop Ψ x) (D.strengthen x M) A
  strengthen_factor : ∀ {M : D.Tm} {x : Nat}, D.uses M x = false → D.weaken x (D.strengthen x M) = M
  /-- Non-degeneracy of `drop`/`weaken`: a term typed WITHOUT `x`, weakened back, does not use `x`.
  With `hasTy_var`/`uses_var` it refutes both degenerate choices: `uses ≡ false` (refuted by
  `uses_var`) and `drop Ψ _ = Ψ` with `weaken = id` (`drop_removes`). -/
  weaken_avoids : ∀ {Ψ : D.Ctx} {M : D.Tm} {A : D.Ty} {x : Nat}, HasTy [] (D.drop Ψ x) M A →
    D.uses (D.weaken x M) x = false
  /-- The variable rule. -/
  hasTy_var : ∀ {Ψ : D.Ctx} {x : Nat} {A : D.Ty}, D.lookup Ψ x = some A → HasTy [] Ψ (D.var x) A
  /-- A variable uses itself. -/
  uses_var : ∀ {x : Nat}, D.uses (D.var x) x = true

/-- The template types at its closed type under the open interface of its holes. -/
def Template.Typed (tpl : Template D E)
    (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) : Prop :=
  HasTy (tpl.Ω.map Iface.decl) tpl.Γ tpl.P tpl.T

/-- DERIVABILITY: the template with the selected fillings types at its closed type, under the
meta-context of the holes still unfilled. -/
def Derivable (HasTy : List (HoleDecl D.Ctx D.Ty) → D.Ctx → D.Tm → D.Ty → Prop) (cl : Closure D E) :
    Prop :=
  HasTy ((cl.tpl.Ω.map Iface.decl).filter fun d => (cl.sigma d.name).isNone)
    cl.tpl.Γ (D.msubst cl.sigma cl.tpl.P) cl.tpl.T

/-- A hole's selection names a retained candidate whose filling passes the hole's checker. -/
def SlotFilled (I : Iface D E) (s : Slot D) : Prop :=
  ∀ i, s.selected = some i → ∃ c, s.cands[i]? = some c ∧ D.check I.ctx c.filling I.ty = true

/-- Every selection is well filled. -/
def WellFilled (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, SlotFilled I (cl.slot I.name)

/-- Every selected candidate's RECORDED status is `verified` (nothing awaits repair). -/
def Settled (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ i, (cl.slot I.name).selected = some i →
    ∃ c, (cl.slot I.name).cands[i]? = some c ∧ c.status = .verified

/-- AVAILABILITY: every support of every selected candidate is live in `w`. -/
def Available (w : World E) (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ c, cl.selectedCand I.name = some c → ∀ t ∈ effSupports I c, w.live t = true

/-- The recorded statuses are the judgment at `w`. -/
def Coherent (w : World E) (cl : Closure D E) : Prop :=
  ∀ I ∈ cl.tpl.Ω, ∀ c ∈ (cl.slot I.name).cands, c.status = judge I w c

end Nanodregg.Lang.Contextual
