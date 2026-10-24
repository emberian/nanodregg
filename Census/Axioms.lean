/-
# Census.Axioms — one tree-wide axiom check

`#axiom_census "allow.tsv" Kernel Codec …` visits every constant declared in a module whose
name starts with one of the given roots and computes the axioms it depends on. Each one must
be `propext`, `Quot.sound` or `Classical.choice`, or appear in the allow file as
`<declaration>\t<axiom>\t<reason>`. Anything else, `sorryAx` included, is an error naming the
declaration and the axiom. An allow-file row that matches nothing is also an error, so the
list cannot outlive the declaration it excuses.

This replaces per-theorem `#assert_axioms` lines: one census sees every declaration, including
the ones nobody wrote a line for. Nothing outside `Census` may import this module
(`gates/closure.py`).
-/
import Lean

namespace Census.Axioms

open Lean Elab Command

/-- The axioms every declaration may use without an allow-file row. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- One allow-file row: this declaration may use this axiom. -/
structure Allowance where
  decl : Name
  axiomName : Name
  deriving BEq

/-- Parse `decl<TAB>axiom<TAB>reason` lines; `#` starts a comment line. A malformed line is an
error, never skipped. -/
def parseAllowances (text : String) : Except String (List Allowance) :=
  text.splitOn "\n" |>.foldlM (init := []) fun acc line =>
    let line := line.trimAsciiEnd.toString
    if line.isEmpty || line.startsWith "#" then
      pure acc
    else
      match line.splitOn "\t" with
      | decl :: ax :: reason :: _ =>
        if reason.trimAscii.toString.isEmpty then
          throw s!"allow row without a reason: {line}"
        else
          pure (acc ++ [⟨decl.toName, ax.toName⟩])
      | _ => throw s!"allow row is not decl<TAB>axiom<TAB>reason: {line}"

/-- The module that declared `c`, if it was imported. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.bind fun idx => env.header.moduleNames[idx.toNat]?

/-- Whether a module belongs to one of the census roots. -/
def underRoots (roots : List Name) (m : Name) : Bool :=
  roots.any fun r => r.isPrefixOf m

/-- The census of every constant of a module under `roots` (and in `only`, when given: a landing's reach, GATES-20v
(c)). With `only`, an allow row is judged when its declaration is declared in the reach: a row for a declaration
outside the reach excuses an axiom the landing cannot have changed, and one whose declaration is not imported at all
(outside the reach, or deleted) is the whole census's to judge, at convergence. -/
def census (path : String) (roots : List Name) (only : Option NameSet) : CommandElabM Unit := do
    let text ← IO.FS.readFile path
    let allowances ← match parseAllowances text with
      | .ok a => pure a
      | .error e => throwError e
    let env ← getEnv
    let inScope := fun (m : Name) => underRoots roots m && (only.map (·.contains m)).getD true
    let mut checked := 0
    let mut bad : Array String := #[]
    let mut used : Array Allowance := #[]
    for (c, _) in env.constants.map₁.toList do
      let some m := moduleOf env c | continue
      unless inScope m do continue
      checked := checked + 1
      let axioms ← liftCoreM (collectAxioms c)
      for ax in axioms do
        if standardAxioms.contains ax then continue
        let row : Allowance := ⟨c, ax⟩
        if allowances.contains row then
          used := used.push row
        else
          bad := bad.push s!"{c} ({m}) uses {ax}"
    for row in allowances do
      let judged := match moduleOf env row.decl with
        | some m => inScope m
        | none => only.isNone
      if judged && !used.contains row then
        bad := bad.push s!"allow row matches nothing: {row.decl} {row.axiomName}"
    let scope := match only with | some o => s!" over {o.size} module(s) of the reach" | none => ""
    if bad.isEmpty then
      logInfo m!"AXIOM-CENSUS ok: {checked} declarations{scope}, {allowances.length} allowed rows"
    else
      throwError m!"AXIOM-CENSUS red ({bad.size}):\n{String.intercalate "\n" bad.toList}"

syntax (name := axiomCensus) "#axiom_census " str ident+ : command
syntax (name := axiomCensusIn) "#axiom_census_in " str str ident+ : command

@[command_elab axiomCensus]
def elabAxiomCensus : CommandElab
  | `(#axiom_census $path:str $roots:ident*) => census path.getString (roots.toList.map (·.getId)) none
  | _ => throwUnsupportedSyntax

@[command_elab axiomCensusIn]
def elabAxiomCensusIn : CommandElab
  | `(#axiom_census_in $path:str $mods:str $roots:ident*) => do
    let only := ((← IO.FS.readFile mods.getString).splitOn "\n").foldl
      (fun s m => if m.isEmpty then s else s.insert m.toName) {}
    census path.getString (roots.toList.map (·.getId)) (some only)
  | _ => throwUnsupportedSyntax

end Census.Axioms
