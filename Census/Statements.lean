/- Statement census: inspect elaborated theorem types, after binders, for an outer Or. -/
import Lean

namespace Census.Statements

open Lean Elab Command Meta

def moduleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.bind fun idx => env.header.moduleNames[idx.toNat]?

def collisionName (n : Name) : Bool :=
  n.toString == "Collision" || n.toString.endsWith ".Collision"

def unboundedCollision (e : Expr) : Bool :=
  let e := e.consumeMData
  e.getAppFn.isConstOf ``Exists &&
    (e.find? fun x => x.getAppFn.constName?.any collisionName).isSome

def oneLine (s : String) : String :=
  (s.replace "\n" " ").replace "\t" " "

syntax (name := statementCensus) "#statement_census " str ident+ : command

@[command_elab statementCensus]
def elabStatementCensus : CommandElab
  | `(#statement_census $path:str $roots:ident*) => do
    let roots := roots.toList.map (·.getId)
    let env ← getEnv
    let mut rows : Array String := #[]
    let mut bad : Array String := #[]
    for (c, ci) in env.constants.map₁.toList do
      let some m := moduleOf env c | continue
      unless roots.any (·.isPrefixOf m) do continue
      let .thmInfo t := ci | continue
      let pair? ← liftTermElabM <| forallTelescope t.type fun _ concl => do
        let e := concl.consumeMData
        if e.getAppFn.isConstOf ``Or then
          let args := e.getAppArgs
          match args[0]?, args[1]? with
          | some a, some b =>
            let ap ← ppExpr a
            let bp ← ppExpr b
            pure (some (oneLine ap.pretty, oneLine bp.pretty, unboundedCollision a, unboundedCollision b))
          | _, _ => pure none
        else pure none
      let some (a, b, ac, bc) := pair? | continue
      let file := m.toString.replace "." "/" ++ ".lean"
      rows := rows.push s!"{file}\t{c}\t{a}\t{b}\t{if ac || bc then "RED" else "ok"}"
      if ac || bc then
        bad := bad.push s!"{file}: {c}: disjunct {if ac then "left" else "right"} is an unbounded existential Collision"
    let sortedRows := rows.toList.mergeSort (· ≤ ·)
    IO.FS.writeFile path.getString ("file\ttheorem\tleft\tright\tverdict\n" ++ String.intercalate "\n" sortedRows ++ "\n")
    if bad.isEmpty then
      logInfo m!"STATEMENT-CENSUS ok: {sortedRows.length} disjunctions in {path.getString}"
    else
      throwError m!"STATEMENT-CENSUS RED ({bad.size}):\n{String.intercalate "\n" bad.toList}"
  | _ => throwUnsupportedSyntax

end Census.Statements
