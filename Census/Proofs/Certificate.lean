/- What is proved: fidelity to the checked Environment
after declaration projection. What is trusted: declaration/encodeExpr/expression projection, Expr.equal, Repr/JSON, Lean.Environment.checked,
Lean.collectAxioms (including its imported cache), compiler execution, and JSON/IO read-off.
No injectivity of Repr, foreign logic interpretation, or checker authentication is asserted. -/
import Census.CertificateData
import Census.Proofs.CertificateReader

namespace Census.Certificate

open Lean

/-- A returned context entry is the projection of an actual checked kernel declaration.
This does not claim that equality of serialized payloads implies ConstantInfo equality. -/
theorem read_environment {env : Environment}
    {c : Census.CertificateReader.Certificate Name Expression Declaration} {fuel : Nat} {target : Name}
    (h : Census.CertificateReader.read (reader env) fuel target = .ok c) :
    ∀ e ∈ c.context, ∃ ci, env.checked.get.find? e.name = some ci ∧
      declaration ci = e.body := by
  intro e he
  have hb := (Census.CertificateReader.read_faithful h).bodies e he
  change Option.map declaration (env.checked.get.find? e.name) = some e.body at hb
  cases hc : env.checked.get.find? e.name with
  | none => simp [hc] at hb
  | some ci =>
    refine ⟨ci, rfl, ?_⟩
    simpa [hc] using hb

/-- The same exact environment projection is present along every finite dependency path. -/
theorem accepted_environment_reachable {env : Environment}
    {c : Census.CertificateReader.Certificate Name Expression Declaration} {n : Name}
    (h : Census.CertificateReader.accept (reader env) c = .ok ())
    (reach : Census.CertificateReader.Reaches (reader env) c n) :
    ∃ ci, env.checked.get.find? n = some ci ∧
      (⟨n, declaration ci⟩ : Census.CertificateReader.Entry Name Declaration) ∈ c.context := by
  obtain ⟨body, hm, hb⟩ := Census.CertificateReader.accepted_reachable_definition h reach
  change Option.map declaration (env.checked.get.find? n) = some body at hb
  cases hc : env.checked.get.find? n with
  | none => simp [hc] at hb
  | some ci =>
    have eq : declaration ci = body := by simpa [hc] using hb
    exact ⟨ci, rfl, eq ▸ hm⟩

end Census.Certificate
