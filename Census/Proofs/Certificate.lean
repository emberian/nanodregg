/- What is proved: fidelity to the checked Environment
after declaration projection. What is trusted: declaration/encodeExpr/expression projection, Expr.equal, Repr/JSON, Lean.Environment.checked,
Lean.collectAxioms (including its imported cache), compiler execution, and JSON/IO read-off.
No injectivity of Repr, foreign logic interpretation, or checker authentication is asserted. -/
import Census.CertificateData
import Lang.Proofs.Contextual.Certificate

namespace Census.Certificate

open Lean

/-- A returned context entry is the projection of an actual checked kernel declaration.
This does not claim that equality of serialized payloads implies ConstantInfo equality. -/
theorem read_environment {env : Environment}
    {c : Nanodregg.Lang.Contextual.Certificate.Certificate Name Expression Declaration} {fuel : Nat} {target : Name}
    (h : Nanodregg.Lang.Contextual.Certificate.read (reader env) fuel target = .ok c) :
    ∀ e ∈ c.context, ∃ ci, env.checked.get.find? e.name = some ci ∧
      declaration ci = e.body := by
  intro e he
  have hb := (Nanodregg.Lang.Contextual.Certificate.read_faithful h).bodies e he
  change Option.map declaration (env.checked.get.find? e.name) = some e.body at hb
  cases hc : env.checked.get.find? e.name with
  | none => simp [hc] at hb
  | some ci =>
    refine ⟨ci, rfl, ?_⟩
    simpa [hc] using hb

/-- The same exact environment projection is present along every finite dependency path. -/
theorem accepted_environment_reachable {env : Environment}
    {c : Nanodregg.Lang.Contextual.Certificate.Certificate Name Expression Declaration} {n : Name}
    (h : Nanodregg.Lang.Contextual.Certificate.accept (reader env) c = .ok ())
    (reach : Nanodregg.Lang.Contextual.Certificate.Reaches (reader env) c n) :
    ∃ ci, env.checked.get.find? n = some ci ∧
      (⟨n, declaration ci⟩ : Nanodregg.Lang.Contextual.Certificate.Entry Name Declaration) ∈ c.context := by
  obtain ⟨body, hm, hb⟩ := Nanodregg.Lang.Contextual.Certificate.accepted_reachable_definition h reach
  change Option.map declaration (env.checked.get.find? n) = some body at hb
  cases hc : env.checked.get.find? n with
  | none => simp [hc] at hb
  | some ci =>
    have eq : declaration ci = body := by simpa [hc] using hb
    exact ⟨ci, rfl, eq ▸ hm⟩

end Census.Certificate
