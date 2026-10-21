import Census.JournalExpr
import Census.Statements

namespace Census.Journal
open Lean Elab Command Meta JournalExpr

/-- Projection names are dependencies too (Expr.getUsedConstants alone misses them).
The returned list also records local premise applications, including instantiated arguments. -/
def expressionEdges (e : Expr) : IO (Array Name × Array Expr) := do
  let names ← IO.mkRef ({} : NameSet)
  let apps ← IO.mkRef (#[] : Array Expr)
  e.forEach fun x => do
    match x with
    | .const n _ => names.modify (·.insert n)
    | .proj n _ _ => names.modify (·.insert n)
    | .app .. =>
      if x.getAppFn.isBVar then apps.modify (·.push x)
    | _ => pure ()
  return ((← names.get).toArray.qsort (fun a b => a.toString < b.toString), ← apps.get)

def shapeEdges : ConstantInfo → List Name
  | .inductInfo i => i.ctors ++ i.all
  | .ctorInfo i => [i.induct]
  | .recInfo i => i.all ++ i.rules.map (·.ctor)
  | _ => []

def shapeData (table : IO.Ref Table) (ci : ConstantInfo) : CommandElabM Json := do
  match ci with
  | .inductInfo i => pure <| Json.mkObj [("params", toJson i.numParams), ("indices", toJson i.numIndices),
      ("nested", toJson i.numNested), ("recursive", toJson i.isRec), ("reflexive", toJson i.isReflexive)]
  | .ctorInfo i => pure <| toJson (i.cidx, i.numParams, i.numFields)
  | .recInfo i =>
      let mut rules : Array Json := #[]
      for r in i.rules do
        let rhs := toJson (← Table.add table r.rhs)
        rules := rules.push (Json.mkObj [("ctor", toJson r.ctor.toString),
          ("fields", toJson r.nfields), ("rhs", rhs)])
      pure <| Json.mkObj [("params", toJson i.numParams), ("indices", toJson i.numIndices),
        ("motives", toJson i.numMotives), ("minors", toJson i.numMinors), ("k", toJson i.k), ("rules", toJson rules)]
  | .defnInfo i => pure <| toJson (match i.hints with
      | .abbrev => "abbrev"
      | .opaque => "opaque"
      | .regular n => s!"regular:{n}")
  | _ => pure Json.null

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def savedTheorem (table : IO.Ref Table) (ci : ConstantInfo) : CommandElabM Saved := do
  let .thmInfo t := ci | throwError "INCOMPLETE COVERAGE: requested root is not a theorem"
  return ⟨.ofName t.name, t.levelParams.map N.ofName, ← Table.add table t.type, ← Table.add table t.value⟩

syntax (name := journalExport) "#journal_export " str ident+ : command

@[command_elab journalExport]
def elabExport : CommandElab
  | `(#journal_export $path:str $roots:ident*) => do
    let env ← getEnv
    let table ← IO.mkRef ({} : Table)
    let roots := roots.toList.map (·.getId)
    let mut todo := roots
    let mut seen : NameSet := {}
    let mut queued : NameSet := roots.foldl (fun s n => s.insert n) {}
    let mut rows : Array Json := #[]
    let mut saved : Array Saved := #[]
    for n in roots do
      let some ci := env.find? n | throwError "INCOMPLETE COVERAGE: missing root {n}"
      saved := saved.push (← savedTheorem table ci)
    -- Finite frontier budget: exhaustion is incomplete, never a smaller successful slice.
    for _ in [:100000] do
      if todo.isEmpty then break
      let n := todo.head!
      todo := todo.tail
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throwError "INCOMPLETE COVERAGE: missing dependency {n}"
      if !roots.contains n && ci.isTheorem then
        saved := saved.push (← savedTheorem table ci)
      let (typeDeps, _) ← expressionEdges ci.type
      let (valueDeps, applications) ← match ci.value? (allowOpaque := true) with
        | some v => expressionEdges v
        | none => pure (#[], #[])
      let shape := shapeEdges ci
      let mut recDeps : Array Name := #[]
      if let .recInfo ri := ci then
        for rule in ri.rules do
          recDeps := recDeps ++ (← expressionEdges rule.rhs).1
      for dep in typeDeps.toList ++ valueDeps.toList ++ recDeps.toList ++ shape do
        unless queued.contains dep do
          queued := queued.insert dep
          todo := dep :: todo
      let axioms ← liftCoreM (collectAxioms n)
      let value : Json ← match ci.value? (allowOpaque := true) with
        | some v => toJson <$> (Table.add table v)
        | none => pure Json.null
      let type := toJson (← Table.add table ci.type)
      let module := (Statements.moduleOf env n).map toString |>.getD "<current>"
      let applicationIds ← liftIO <| applications.mapM (Table.add table)
      rows := rows.push (Json.mkObj [
        ("name", toJson n.toString), ("kind", toJson (kind ci)),
        ("module", toJson module), ("levels", toJson (ci.levelParams.map N.ofName)),
        ("type", type), ("value", value), ("shape", ← shapeData table ci),
        ("typeDeps", toJson (typeDeps.map toString)), ("valueDeps", toJson (valueDeps.map toString)),
        ("shapeDeps", toJson ((shape ++ recDeps.toList).map toString)), ("axioms", toJson (axioms.map toString)),
        ("localApplications", toJson applicationIds)])
    unless todo.isEmpty do throwError "INCOMPLETE COVERAGE: export frontier exhausted"
    let tbl ← table.get
    let nodes ← match tbl.exprs.mapM (node tbl) with
      | .ok ns => pure ns
      | .error msg => throwError msg
    let out := Json.mkObj [("schema", toJson (1 : Nat)), ("complete", toJson true),
      ("roots", toJson (roots.map toString)), ("declarations", toJson rows), ("saved", toJson saved), ("nodes", toJson nodes)]
    IO.FS.writeFile path.getString (out.compress ++ "\n")
    logInfo m!"JOURNAL EXPORT complete: {rows.size} declarations; {roots.length} roots"
  | _ => throwUnsupportedSyntax

syntax (name := journalRecheck) "#journal_recheck " str str num : command

/-- Recheck the saved proof expression against the CURRENT root's type, under the CURRENT
environment. A fresh kernel name prevents a declaration cache from answering for this check.
The original expression is never freshly elaborated here. -/
@[command_elab journalRecheck]
def elabRecheck : CommandElab
  | `(#journal_recheck $input:str $output:str $budget:num) => do
    let txt ← IO.FS.readFile input.getString
    let js ← match Json.parse txt with
      | .ok j => pure j
      | .error msg => throwError "INCOMPLETE COVERAGE: {msg}"
    let saved ← match js.getObjValAs? (Array Saved) "saved" with
      | .ok x => pure x
      | .error msg => throwError "INCOMPLETE COVERAGE: {msg}"
    let nodes ← match js.getObjValAs? (Array Node) "nodes" with
      | .ok x => pure x
      | .error msg => throwError "INCOMPLETE COVERAGE: {msg}"
    let env ← getEnv
    let roots ← match js.getObjValAs? (Array String) "roots" with
      | .ok x => pure x
      | .error msg => throwError "INCOMPLETE COVERAGE: {msg}"
    for root in roots do
      unless (env.find? root.toName).isSome do
        throwError "INCOMPLETE COVERAGE: missing import/root {root}"
    let mut rows : Array Json := #[]
    for s in saved do
      let n := s.name.toName
      let some ci := env.find? n | do
        rows := rows.push <| Json.mkObj [("name", toJson n.toString),
          ("ok", toJson false), ("invoked", toJson false),
          ("diagnostic", toJson "current support declaration unavailable"), ("budget", toJson budget.getNat)]
        continue
      let v ← match (decode nodes (nodes.size + 1) s.value).run' {} with
        | .ok x => pure x
        | .error msg => throwError msg
      let decl := Declaration.thmDecl {
        name := Name.str n "journalRetainedCheck"
        levelParams := s.levels.map N.toName
        type := ci.type
        value := v }
      let start ← IO.getNumHeartbeats
      let (ok, diagnostic) ← match env.toKernelEnv.addDeclCore (start + budget.getNat).toUSize decl none with
        | .ok _ => pure (true, "kernel checked retained term")
        | .error e => do pure (false, ← (e.toMessageData (← getOptions)).toString)
      rows := rows.push (Json.mkObj [("name", toJson n.toString), ("ok", toJson ok), ("invoked", toJson true),
        ("diagnostic", toJson diagnostic), ("budget", toJson budget.getNat)])
    IO.FS.writeFile output.getString ((toJson rows).compress ++ "\n")
    logInfo m!"JOURNAL RECHECK: {rows.size} retained terms; {rows.filter (fun j => (j.getObjValAs? Bool "ok").toOption == some true) |>.size} checked"
  | _ => throwUnsupportedSyntax


syntax (name := journalAudit) "#journal_audit " str ident+ : command

@[command_elab journalAudit]
def elabAudit : CommandElab
  | `(#journal_audit $output:str $roots:ident*) => do
    let env ← getEnv
    let mut rows : Array Json := #[]
    for root in roots do
      let n := root.getId
      let some ci := env.find? n | throwError "INCOMPLETE COVERAGE: missing audit root {n}"
      let finding ← liftTermElabM <| forallTelescope ci.type fun _ concl => do
        let e := concl.consumeMData
        let mut bad := false
        if e.getAppFn.isConstOf ``Or then
          for branch in e.getAppArgs do
            let b := branch.consumeMData
            let hasHash := (b.find? fun x =>
              x.getAppFn.constName?.any (fun k => k.toString.endsWith ".hash")).isSome
            let bounded := (b.find? fun x => x.getAppFn.isConstOf ``List.Mem).isSome
            if b.getAppFn.isConstOf ``Exists && hasHash && !bounded then bad := true
        pure bad
      rows := rows.push <| Json.mkObj [("name", toJson n.toString),
        ("globalCollisionEscape", toJson finding),
        ("coverage", toJson "outer-disjunction/global-hash-existential detector; other semantic audits remain separate")]
    IO.FS.writeFile output.getString ((toJson rows).compress ++ "\n")
    logInfo m!"JOURNAL AUDIT: {rows.size} roots; {rows.filter (fun j => (j.getObjValAs? Bool "globalCollisionEscape").toOption == some true) |>.size} GLOBAL-COLLISION ESCAPE"
  | _ => throwUnsupportedSyntax

end Census.Journal
