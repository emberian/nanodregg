/- Emit a certificate from a real checked Lean environment; IO is a trusted read-off.
The command refuses absent/non-theorem targets, incomplete closure and missing axiom reads. -/
import Census.CertificateData

namespace Census.Certificate

open Lean Elab Command

syntax (name := certificateCensus) "#certificate_census " str ident : command

@[command_elab certificateCensus]
def elabCertificateCensus : CommandElab
  | `(#certificate_census $path:str $target:ident) => do
    let env ← getEnv
    let target := target.getId
    let c ← match Census.CertificateReader.read (reader env) 200000 target with
      | .ok c => pure c
      | .error e => throwError "CERTIFICATE RED: {reprStr e}"
    let axs := (← liftCoreM (collectAxioms target)).toList
    -- The shape closure may conservatively contain additional axioms.
    -- The target's exact collectAxioms result is kept separately and must be covered.
    unless axs.all (fun n => c.assumptions.contains n) do
      throwError "CERTIFICATE RED: collectAxioms escaped the context"
    let some ci := env.checked.get.find? target
      | throwError "CERTIFICATE RED: target disappeared"
    let pretty ← liftTermElabM (Meta.ppExpr ci.type)
    IO.FS.writeFile path.getString ((certificateJson c axs pretty.pretty).compress ++ "\n")
    logInfo m!"CERTIFICATE ok: {target}, {c.context.length} declarations, {axs.length} target axioms"
  | _ => throwUnsupportedSyntax

end Census.Certificate
