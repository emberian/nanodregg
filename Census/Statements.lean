/-
# Census.Statements — no conclusion escapes through a collision it may choose

`#statement_census "out.tsv" Kernel …` reads every theorem of the given roots, after its binders
and premises, and finds each disjunction in its conclusion (through `∧`, `↔`, `∃` and one-step
unfoldings of the tree's own definitions). A disjunct is RED when it holds a digest equation
`f a = f b` whose two sides both mention variables the statement itself chooses: bound by an `∃`
of the disjunct or of the conclusion, and not bounded by a conjunct `t ∈ L` over a list `L` built
only from the theorem's own objects (`∃ p ∈ S, …`, which is how `CollidesAmong hash S` and
`Trie.CollAmong S L` unfold). That is the pigeonhole shape: for `f` into a finite type it is
provable without any of the theorem's premises (KERNEL-56: `Collision`, `Trie.Coll`, `HashColl`;
logs/kernel21-ver-pigeon.lean proves it from `E.Lawful`).

The rule reads structure, never a name: a renamed or aliased escape unfolds to the same shape.
Before the tree, the command judges fixed fixtures (two that must read RED, two that must
read ok); a misread fixture is an error, so a detector that stopped detecting cannot print ok.
-/
import Lean

namespace Census.Statements

open Lean Elab Command Meta

def moduleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.bind fun idx => env.header.moduleNames[idx.toNat]?

def oneLine (s : String) : String :=
  (s.replace "\n" " ").replace "\t" " "

/-- Whether `e` mentions one of the chosen variables. -/
def mentions (chosen : Array Expr) (e : Expr) : Bool :=
  e.hasAnyFVar fun f => chosen.any (·.fvarId! == f)

/-- How many connectives deep the walks go. A statement deeper than this is not judged and reads RED
by name (`not judged`), never ok: the walks are total (CHARTER law 4: no `partial`). -/
def maxDepth : Nat := 256

/-- The conjuncts of an `∧`-spine, at most `d` levels down; below that the rest is one conjunct, which
the walks still enter. -/
def conjuncts : Nat → Expr → Array Expr
  | 0, e => #[e]
  | d + 1, e =>
    let e := e.consumeMData
    if e.isAppOfArity ``And 2 then conjuncts d e.appFn!.appArg! ++ conjuncts d e.appArg! else #[e]

/-- The chosen variables a spine of conjuncts leaves free. A conjunct `t ∈ L`, with `L` free of
free chosen variables, bounds every chosen variable of `t` to the finitely many elements of a list
the statement does not choose (`∃ p ∈ S, …`, as `CollidesAmong hash S` and `Trie.CollAmong S L`
unfold; `∃ c' v a, recordOf c' v a ∈ S ∧ …`). To a fixpoint: an element of a bounded list is
bounded. Each round that bounds something removes at least one variable, so `chosen.size + 1`
rounds reach the fixpoint; out of rounds, everything still chosen stays chosen (the red side). -/
def leftFreeRounds (cs : Array Expr) : Nat → Array Expr → Array Expr
  | 0, chosen => chosen
  | n + 1, chosen =>
    let bounded := cs.foldl (init := (#[] : Array Expr)) fun acc m =>
      let m := m.consumeMData
      if m.isAppOfArity ``Membership.mem 5 && !mentions chosen m.appFn!.appArg! then
        acc ++ chosen.filter fun x => m.appArg!.containsFVar x.fvarId!
      else acc
    if bounded.isEmpty then chosen
    else leftFreeRounds cs n (chosen.filter fun x => !bounded.contains x)

def leftFree (chosen : Array Expr) (cs : Array Expr) : Array Expr :=
  leftFreeRounds cs (chosen.size + 1) chosen

/-- How deep the walks unfold the tree's own definitions (an alias of an alias of an escape). -/
def unfoldFuel : Nat := 4

/-- The tree's own definition at the head of `e`, unfolded once, if any. -/
def unfoldOwn (roots : List Name) (e : Expr) : MetaM (Option Expr) := do
  let some c := e.getAppFn.constName? | return none
  let some m := moduleOf (← getEnv) c | return none
  unless roots.any (·.isPrefixOf m) do return none
  unfoldDefinition? e

/-- Open `∃ x, body` (eta-reduced or not); `x` is chosen until a conjunct bounds it. -/
def openExists {α} (chosen : Array Expr) (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let p := e.appArg!
  let n := match p.consumeMData with | .lam n .. => n | _ => `x
  withLocalDeclD n e.appFn!.appArg! fun x => k (chosen.push x) (mkApp p x).headBeta

def notJudged : String := s!"deeper than {maxDepth} connectives: not judged"

/-- The first digest equation in `e` whose two sides are both inputs the statement chooses: the
pigeonhole shape, provable of any map into a finite type without the theorem's premises. An
equation with one side the theorem's own (`txIdOf X c' = txIdOf X c`, a second preimage) is not
this shape. -/
def escape (roots : List Name) (fuel : Nat) : Nat → Array Expr → Expr → MetaM (Option String)
  | 0, _, _ => pure (some notJudged)
  | d + 1, chosen, e => do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Exists 2 then
    openExists chosen e (escape roots fuel d)
  else if e.isAppOfArity ``And 2 then
    let cs := conjuncts maxDepth e
    let free := leftFree chosen cs
    for c in cs do
      if let some r ← escape roots fuel d free c then return some r
    pure none
  else if e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
    match ← escape roots fuel d chosen e.appFn!.appArg! with
    | some r => pure (some r)
    | none => escape roots fuel d chosen e.appArg!
  else if e.isAppOfArity ``Eq 3 then
    let l := e.appFn!.appArg!.consumeMData
    let r := e.appArg!.consumeMData
    if l.isApp && r.isApp && l.getAppFn == r.getAppFn && l != r && mentions chosen l && mentions chosen r then
      pure (some s!"`{oneLine (← ppExpr e).pretty}` compares two inputs the statement chooses")
    else pure none
  else if fuel > 0 then
    match ← unfoldOwn roots e with
    | some e' => escape roots (fuel - 1) d chosen e'
    | none => pure none
  else pure none

/-- One disjunction of a conclusion: its two sides and, if either escapes, the reason. -/
structure Row where
  left : String
  right : String
  red : Option String

/-- Every maximal disjunction in a conclusion, judged under the variables the conclusion chooses. -/
def disjunctions (roots : List Name) (fuel : Nat) : Nat → Array Expr → Expr → MetaM (Array Row)
  | 0, _, e => return #[{ left := oneLine (← ppExpr e).pretty, right := "", red := some notJudged }]
  | d + 1, chosen, e => do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let red ← match ← escape roots unfoldFuel maxDepth chosen a with
      | some r => pure (some s!"left disjunct: {r}")
      | none => (·.map (s!"right disjunct: " ++ ·)) <$> escape roots unfoldFuel maxDepth chosen b
    pure #[{ left := oneLine (← ppExpr a).pretty, right := oneLine (← ppExpr b).pretty, red }]
  else if e.isAppOfArity ``Exists 2 then
    openExists chosen e (disjunctions roots fuel d)
  else if e.isAppOfArity ``And 2 then
    let cs := conjuncts maxDepth e
    let free := leftFree chosen cs
    cs.foldlM (init := #[]) fun acc c => return acc ++ (← disjunctions roots fuel d free c)
  else if e.isAppOfArity ``Iff 2 then
    return (← disjunctions roots fuel d chosen e.appFn!.appArg!) ++ (← disjunctions roots fuel d chosen e.appArg!)
  else if fuel > 0 then
    match ← unfoldOwn roots e with
    | some e' => disjunctions roots (fuel - 1) d chosen e'
    | none => pure #[]
  else pure #[]

/-- The disjunctions of a statement, after its binders and premises. -/
def judge (roots : List Name) (type : Expr) : MetaM (Array Row) :=
  forallTelescope type fun _ concl => disjunctions roots unfoldFuel maxDepth #[] concl

/-- The fixtures every run judges first: (statement, must read RED). The first is provable on its
own (`⟨0, 2, by decide, rfl⟩`), the second by choosing the list `[0, 2]`. The third ranges over a
list of the statement's own variables, the fourth is bounded by a guard on a term of its witnesses
(as `Protocol.Settle`'s colliding call is), and both must read ok. -/
def fixtures : CommandElabM (Array (Syntax.Term × Bool)) := do
  return #[
    (← `(True ∨ ∃ a b : Nat, a ≠ b ∧ a % 2 = b % 2), true),
    (← `(True ∨ ∃ L : List Nat, ∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ a % 2 = b % 2), true),
    (← `(∀ x y : Nat, True ∨ ∃ a ∈ [x, y], ∃ b ∈ [x, y], a ≠ b ∧ a % 2 = b % 2), false),
    (← `(∀ S : List (Nat × Nat), True ∨ ∃ a b, (a, b) ∈ S ∧ a ≠ b ∧ a % 2 = b % 2), false)]

/-- The modules a file names, one per line: a landing's reach (GATES-20v (c): the fast judge censuses what the
landing can change; a theorem outside the reach has the parent's statement over the parent's definitions). -/
def readModules (path : String) : IO NameSet := do
  return ((← IO.FS.readFile path).splitOn "\n").foldl (fun s m => if m.isEmpty then s else s.insert m.toName) {}

/-- The census: the fixtures, then every theorem of a module under `roots` (and in `only`, when given). -/
def census (path : String) (roots : List Name) (only : Option NameSet) : CommandElabM Unit := do
    for (stx, mustRed) in ← fixtures do
      let rows ← liftTermElabM do
        let e ← Term.elabTerm stx none
        Term.synthesizeSyntheticMVarsNoPostponing
        judge roots (← instantiateMVars e)
      let red := rows.any (·.red.isSome)
      unless rows.size == 1 && red == mustRed do
        throwError m!"STATEMENT-CENSUS harness: fixture `{stx}` read {if red then "RED" else "ok"} \
          over {rows.size} disjunctions; it must read {if mustRed then "RED" else "ok"} over 1"
    let env ← getEnv
    let mut rows : Array String := #[]
    let mut bad : Array String := #[]
    for (c, ci) in env.constants.map₁.toList do
      let some m := moduleOf env c | continue
      unless roots.any (·.isPrefixOf m) do continue
      if let some o := only then unless o.contains m do continue
      let .thmInfo t := ci | continue
      let found ← liftTermElabM <| judge roots t.type
      let file := m.toString.replace "." "/" ++ ".lean"
      for r in found do
        rows := rows.push s!"{file}\t{c}\t{r.left}\t{r.right}\t{if r.red.isSome then "RED" else "ok"}"
        if let some why := r.red then
          bad := bad.push s!"{file}: {c}: {why}"
    let sortedRows := rows.toList.mergeSort (· ≤ ·)
    IO.FS.writeFile path ("file\ttheorem\tleft\tright\tverdict\n" ++ String.intercalate "\n" sortedRows ++ "\n")
    let scope := match only with | some o => s!" over {o.size} module(s) of the reach" | none => ""
    if bad.isEmpty then
      logInfo m!"STATEMENT-CENSUS ok: {sortedRows.length} disjunctions in {path}{scope} (fixtures: 2 RED, 2 ok as required)"
    else
      throwError m!"STATEMENT-CENSUS RED ({bad.size}):\n{String.intercalate "\n" bad.toList}"

syntax (name := statementCensus) "#statement_census " str ident+ : command
syntax (name := statementCensusIn) "#statement_census_in " str str ident+ : command

@[command_elab statementCensus]
def elabStatementCensus : CommandElab
  | `(#statement_census $path:str $roots:ident*) => census path.getString (roots.toList.map (·.getId)) none
  | _ => throwUnsupportedSyntax

@[command_elab statementCensusIn]
def elabStatementCensusIn : CommandElab
  | `(#statement_census_in $path:str $mods:str $roots:ident*) => do
    census path.getString (roots.toList.map (·.getId)) (some (← readModules mods.getString))
  | _ => throwUnsupportedSyntax

end Census.Statements
