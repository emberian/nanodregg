/-
# Census.Statements — no conclusion escapes through a collision it may choose

`#statement_census "out.tsv" Kernel …` reads every theorem of the given roots, after its binders
and premises, and finds each disjunction in its conclusion (through `∧`, `↔`, `∃`, `∀`, `→` and up to four
unfoldings of the tree's own definitions; under a `∀` only what the disjunct itself chooses is chosen). A disjunct is RED when it holds a digest
equation `f a = f b` (or `(f a == f b) = true`, `decide (f a = f b) = true`) whose two sides both
mention variables the statement itself chooses: bound by an `∃` of the disjunct or of the conclusion
(or by a `¬ ∀`, which chooses), and not bounded by a conjunct `t ∈ L` over a list or array `L` built
only from the theorem's own objects, where `t` DETERMINES the variable: `t` is the variable, or a
constructor holding it (`∃ p ∈ S, …`, which is how `CollidesAmong hash S` and `Trie.CollAmong S L`
unfold; `(a, b) ∈ S`). `a.length ∈ [5]` bounds nothing: infinitely many lists have length 5
(GATES-20w; cv 01a1654c-543c). That is the pigeonhole shape: for `f` into a finite type it is
provable without any of the theorem's premises (KERNEL-56: `Collision`, `Trie.Coll`, `HashColl`;
logs/kernel21-ver-pigeon.lean proves it from `E.Lawful`). A negation is pushed inward (classically:
`¬ ∀` chooses, `¬ (A → B)` is `A ∧ ¬ B`, `¬ ¬ P` is `P`, `¬ (a ≠ b)` is `a = b`), unfolding any
definition it meets, so `¬ Function.Injective h` is the escape it is. Inside a disjunct the walk
enters a premise, never a dependent `∀`: an equation under `∀ i` between two inputs chosen outside it
is a collision of a map into a function space, which pigeonhole does not give.

The rule reads structure, never a name: a renamed or aliased escape unfolds to the same shape.
Before the tree, the command judges fixed fixtures (seven that must read RED, four that must
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

/-- How deep the walks unfold definitions (an alias of an alias of an escape). -/
def unfoldFuel : Nat := 4

/-- The chosen variables the element `t` of a membership DETERMINES: `t` itself, or the fields of a constructor
application (after unfolding a definition at its head, at most `fuel` times). A constructor is injective, so
finitely many elements determine finitely many fields; a projection or any other function determines nothing
(`a.length ∈ [5]` leaves `a` free). -/
def determined (chosen : Array Expr) : Nat → Expr → MetaM (Array Expr)
  | 0, _ => pure #[]
  | f + 1, t => do
    let t := (← instantiateMVars t).consumeMData
    if t.isFVar then return chosen.filter (·.fvarId! == t.fvarId!)
    let some c := t.getAppFn.constName? | return #[]
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      let args := t.getAppArgs
      if args.size != ci.numParams + ci.numFields then return #[]
      (args.extract ci.numParams args.size).foldlM (init := #[]) fun acc a => return acc ++ (← determined chosen f a)
    else
      match ← unfoldDefinition? t with
      | some t' => determined chosen f t'.headBeta
      | none => pure #[]

/-- Whether a membership's collection type is finite by construction: a `List` or an `Array`. A `Set` or any
other collection may be infinite, so its membership bounds nothing. -/
def finiteCollection (m : Expr) : Bool :=
  let γ := m.appFn!.appFn!.appFn!.appArg!     -- Membership.mem {α} {γ} [inst] (coll) (elem)
  γ.consumeMData.isAppOf ``List || γ.consumeMData.isAppOf ``Array

/-- The chosen variables a spine of conjuncts leaves free. A conjunct `t ∈ L`, with `L` a list or array free of
free chosen variables, bounds every chosen variable `t` determines to the finitely many elements of a collection
the statement does not choose (`∃ p ∈ S, …`, as `CollidesAmong hash S` and `Trie.CollAmong S L` unfold;
`(a, b) ∈ S`). To a fixpoint: an element of a bounded list is bounded. Each round that bounds something removes
at least one variable, so `chosen.size + 1` rounds reach the fixpoint; out of rounds, everything still chosen
stays chosen (the red side). -/
def leftFreeRounds (cs : Array Expr) : Nat → Array Expr → MetaM (Array Expr)
  | 0, chosen => pure chosen
  | n + 1, chosen => do
    let bounded ← cs.foldlM (init := (#[] : Array Expr)) fun acc m => do
      let m := m.consumeMData
      if m.isAppOfArity ``Membership.mem 5 && finiteCollection m && !mentions chosen m.appFn!.appArg! then
        return acc ++ (← determined chosen unfoldFuel m.appArg!)
      else return acc
    if bounded.isEmpty then pure chosen
    else leftFreeRounds cs n (chosen.filter fun x => !bounded.contains x)

def leftFree (chosen : Array Expr) (cs : Array Expr) : MetaM (Array Expr) :=
  leftFreeRounds cs (chosen.size + 1) chosen

/-- The tree's own definition at the head of `e`, unfolded once, if any. -/
def unfoldOwn (roots : List Name) (e : Expr) : MetaM (Option Expr) := do
  let some c := e.getAppFn.constName? | return none
  let some m := moduleOf (← getEnv) c | return none
  unless roots.any (·.isPrefixOf m) do return none
  unfoldDefinition? e

/-- One step of a negation pushed inward, classically: `¬ ¬ P` is `P`; `¬ (A ∧ B)` is `¬ A ∨ ¬ B`; `¬ (A ∨ B)` is
`¬ A ∧ ¬ B`; `¬ ∃ x, B` is `∀ x, ¬ B`; `¬ ∀ x, B` is `∃ x, ¬ B` (which CHOOSES `x`); `¬ (A → B)` is `A ∧ ¬ B`;
`¬ (a ≠ b)` is `a = b`; any other head is unfolded (`Function.Injective`, the tree's own aliases), at most `fuel`
times. `none`: nothing to push (`¬ (a = b)`, an atom). -/
def pushNot : Nat → Expr → MetaM (Option Expr)
  | 0, _ => pure none
  | f + 1, p => do
    let p := (← instantiateMVars p).consumeMData
    if p.isAppOfArity ``Not 1 then return some p.appArg!
    if p.isAppOfArity ``And 2 then return some (mkOr (mkNot p.appFn!.appArg!) (mkNot p.appArg!))
    if p.isAppOfArity ``Or 2 then return some (mkAnd (mkNot p.appFn!.appArg!) (mkNot p.appArg!))
    if p.isAppOfArity ``Ne 3 then
      return some (mkApp3 (.const ``Eq p.getAppFn.constLevels!) p.appFn!.appFn!.appArg! p.appFn!.appArg! p.appArg!)
    if p.isAppOfArity ``Exists 2 then
      let f := p.appArg!
      return some (.forallE `x p.appFn!.appArg! (mkNot (mkApp f (.bvar 0)).headBeta) .default)
    if let .forallE n t b bi := p then
      if b.hasLooseBVars then
        return some (mkApp2 (.const ``Exists [← getLevel t]) t (.lam n t (mkNot b) bi))
      return some (mkAnd t (mkNot b))
    if p.isAppOfArity ``Eq 3 then return none
    match ← unfoldDefinition? p with
    | some p' => pushNot f p'.headBeta
    | none => pure none

/-- An equation's two sides, with a Boolean one read as the equation it decides: `(x == y) = true`, `(x != y) =
false` and `decide (x = y) = true` compare `x` and `y`. -/
def sides (l r : Expr) : Expr × Expr :=
  let l := l.consumeMData
  let r := r.consumeMData
  let (b, v) := if r.isConstOf ``Bool.true || r.isConstOf ``Bool.false then (r, l)
    else if l.isConstOf ``Bool.true || l.isConstOf ``Bool.false then (l, r) else (r, l)
  let v := v.consumeMData
  if b.isConstOf ``Bool.true && v.isAppOfArity ``BEq.beq 4 then (v.appFn!.appArg!, v.appArg!)
  else if b.isConstOf ``Bool.false && v.isAppOfArity ``bne 4 then (v.appFn!.appArg!, v.appArg!)
  else if b.isConstOf ``Bool.true && v.isAppOfArity ``Decidable.decide 2 && v.appFn!.appArg!.isAppOfArity ``Eq 3 then
    let q := v.appFn!.appArg!
    (q.appFn!.appArg!, q.appArg!)
  else (l, r)

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
    let free ← leftFree chosen cs
    for c in cs do
      if let some r ← escape roots fuel d free c then return some r
    pure none
  else if e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
    match ← escape roots fuel d chosen e.appFn!.appArg! with
    | some r => pure (some r)
    | none => escape roots fuel d chosen e.appArg!
  else if e.isAppOfArity ``Not 1 then
    match ← pushNot unfoldFuel e.appArg! with
    | some e' => escape roots fuel d chosen e'
    | none => pure none
  else if let .forallE _ _ b _ := e then
    -- a premise `A → B`: an escape in `B` is one whatever `A` says. A dependent `∀ x, B` ends the walk: an
    -- equation under it compares two chosen inputs at EVERY `x` (a collision of the map into a function space,
    -- which pigeonhole does not give: `¬ Trie.Separates`'s `∀ i < depth` over the chosen keys)
    if b.hasLooseBVars then pure none
    else forallBoundedTelescope e (some 1) fun _ b => escape roots fuel d chosen b
  else if e.isAppOfArity ``Eq 3 then
    let (l, r) := sides e.appFn!.appArg! e.appArg!
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
    let free ← leftFree chosen cs
    cs.foldlM (init := #[]) fun acc c => return acc ++ (← disjunctions roots fuel d free c)
  else if e.isAppOfArity ``Iff 2 then
    return (← disjunctions roots fuel d chosen e.appFn!.appArg!) ++ (← disjunctions roots fuel d chosen e.appArg!)
  else if let .forallE _ _ b _ := e then
    -- a disjunction under a `∀` (or a premise) inside an `∃` is listed and judged too (GATES-20w). Under a dependent
    -- `∀` the choices made outside it are fixed for every value it gives, so only what the disjunct chooses itself
    -- is chosen there
    forallBoundedTelescope e (some 1) fun _ body =>
      disjunctions roots fuel d (if b.hasLooseBVars then #[] else chosen) body
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
(as `Protocol.Settle`'s colliding call is), and both must read ok. GATES-20w's five: a membership of a
projection bounds nothing; `¬ Function.Injective`, a Boolean equation and `¬ … ≠ …` are the escape; a
disjunction under a `∀` inside an `∃` is listed. The last two must read ok: `Function.Injective` stated, not
denied (its `∀` gives the inputs; nothing is chosen), and an equation under a `∀` between two chosen inputs
(a collision at every `i`, which no pigeonhole gives: this one is false). -/
def fixtures : CommandElabM (Array (Syntax.Term × Bool)) := do
  return #[
    (← `(True ∨ ∃ a b : Nat, a ≠ b ∧ a % 2 = b % 2), true),
    (← `(True ∨ ∃ L : List Nat, ∃ a ∈ L, ∃ b ∈ L, a ≠ b ∧ a % 2 = b % 2), true),
    (← `(∀ x y : Nat, True ∨ ∃ a ∈ [x, y], ∃ b ∈ [x, y], a ≠ b ∧ a % 2 = b % 2), false),
    (← `(∀ S : List (Nat × Nat), True ∨ ∃ a b, (a, b) ∈ S ∧ a ≠ b ∧ a % 2 = b % 2), false),
    (← `(True ∨ ∃ a b : List Nat, a.length ∈ [5] ∧ b.length ∈ [5] ∧ a ≠ b ∧ a.length % 2 = b.length % 2), true),
    (← `(True ∨ ¬ Function.Injective (fun n : Nat => n % 2)), true),
    (← `(True ∨ ∃ a b : Nat, a ≠ b ∧ (a % 2 == b % 2) = true), true),
    (← `(True ∨ ∃ a b : Nat, a ≠ b ∧ ¬ a % 2 ≠ b % 2), true),
    (← `(∃ n : Nat, ∀ m : Nat, m = n → (True ∨ ∃ a b : Nat, a ≠ b ∧ a % 2 = b % 2)), true),
    (← `(True ∨ Function.Injective (fun n : Nat => n % 2)), false),
    (← `(True ∨ ∃ a b : Nat, a ≠ b ∧ ∀ i : Nat, a % (i + 2) = b % (i + 2)), false)]

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
      logInfo m!"STATEMENT-CENSUS ok: {sortedRows.length} disjunctions in {path}{scope} (fixtures: 7 RED, 4 ok as required)"
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
