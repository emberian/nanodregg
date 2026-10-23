/- The certificate pin of a checked theorem (decisions/gates.md GATES-20u, review H3): what it says and what it
rests on, read from the built Environment through `Census.Certificate.lookup`, one level, never the closure.
  * statement: the theorem's type;
  * axioms: `collectAxioms` (a whole-cone fact: an axiom anywhere under the proof is in it);
  * supports: each constant the proof term references (the `dependencies` of the theorem's declaration), with
    its statement (its type);
  * vocabulary: each constant the statement names, with its declaration (a definition's body; an inductive's
    shape and its constructors).
A change in the cone that keeps these four is not a change of the certificate. IO is a trusted read-off;
gates/certificate.py takes the SHA-256 of each emitted encoding and compares. Refusals are by name. -/
import Census.CertificateData

namespace Census.Certificate

open Lean Elab Command

/-- What `n` means as a word of a statement: its declaration payload and, for an inductive, its constructors'
(their field types are the type's meaning). An error names the first constant without a checked declaration. -/
def meaning (env : Environment) (n : Name) : Except Name (List String) :=
  let ctors := match env.checked.get.find? n with
    | some (.inductInfo v) => v.ctors
    | _ => []
  (n :: ctors).mapM fun m => match lookup env m with
    | some d => .ok d.payload
    | none => .error m

syntax (name := certificatePin) "#certificate_pin " str ident : command

@[command_elab certificatePin]
def elabCertificatePin : CommandElab
  | `(#certificate_pin $path:str $target:ident) => do
    let env ← getEnv
    let target := target.getId
    let some body := lookup env target
      | throwError "CERTIFICATE RED: missing target {target}"
    unless body.theoremKind do
      throwError "CERTIFICATE RED: not a theorem {target}"
    let supports ← (body.dependencies.filter (· != target)).mapM fun n =>
      match lookup env n with
      | some d => pure (n.toString, toJson d.type.encoded)
      | none => throwError "CERTIFICATE RED: no declaration for support {n}"
    let vocabulary ← body.type.constants.mapM fun n =>
      match meaning env n with
      | .ok ps => pure (n.toString, toJson ps)
      | .error m => throwError "CERTIFICATE RED: no declaration for vocabulary {m}"
    let axs := (← liftCoreM (collectAxioms target)).toList
    let some ci := env.checked.get.find? target
      | throwError "CERTIFICATE RED: missing target {target}"
    let pretty ← liftTermElabM (Meta.ppExpr ci.type)
    IO.FS.writeFile path.getString ((Json.mkObj [
      ("target", toJson target.toString),
      ("statement", toJson body.type.encoded),
      ("statementPretty", toJson pretty.pretty),
      ("axioms", toJson (axs.map Name.toString)),
      ("supports", Json.mkObj supports),
      ("vocabulary", Json.mkObj vocabulary)]).compress ++ "\n")
    logInfo m!"CERTIFICATE ok: {target}, {supports.length} supports, {vocabulary.length} vocabulary, {axs.length} axioms"
  | _ => throwUnsupportedSyntax

end Census.Certificate
