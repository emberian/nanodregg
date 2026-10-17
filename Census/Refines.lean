/-
# Census.Refines — every refinement carries its lawfulness theorem (CODEC-28)

`refine name c accept back` hides two functions from its `Shape`, so a codec's content tag
(`Codec.Tag.of`) sees only `name`. What pins `accept` is the refinement's lawfulness theorem
(`LawfulOn P (c …)` or `Lawful (c …)`): `Codec.Stream.refine_accept_iff` proves it fixes exactly what
`accept` admits. `#refine_census "allow.tsv" Kernel Codec …` finds every REFINE SITE under the given
roots, i.e. a definition whose body, under its lambdas, is `Codec.Stream.refine "<literal>" …` or a
`Codec.Stream.mk` whose shape is `Shape.refine "<literal>" …` (a hand-built refinement, like the World
codec). Each site needs a theorem whose conclusion, after its binders, is `Lawful (c …)` or
`LawfulOn P (c …)` with `c` as the head constant and `P` not the constant `False`.

A site that is canonical only up to an equivalence (the World and carried codecs, whose journal is
a `TreeMap`) gets an allow row instead: `<decl>\t<theorem>[,<theorem>…]\t<reason>`. Every theorem a row
names must exist and must state a decode of `c` (its type contains `Codec.Stream.decode (c …)`), so
the row records where the codec's canonicity lives rather than excusing it. A row whose declaration
is not a refine site, or is a site that has its own lawfulness theorem, is an error: the list cannot
outlive what it excuses. Nothing outside `Census` may import this module (`gates/closure.py`).
-/
import Lean

namespace Census.Refines

open Lean Elab Command Meta

def refineConst : Name := `Nanodregg.Codec.Stream.refine
def mkConst : Name := `Nanodregg.Codec.Stream.mk
def shapeRefine : Name := `Nanodregg.Codec.Shape.refine
def lawfulConst : Name := `Nanodregg.Codec.Stream.Lawful
def lawfulOnConst : Name := `Nanodregg.Codec.Stream.LawfulOn
def decodeConst : Name := `Nanodregg.Codec.Stream.decode

/-- The string a literal argument holds. -/
def strLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

/-- The refinement name a definition body is built with, if the body is a refine site. -/
def siteName? (body : Expr) : Option String :=
  let b := body.consumeMData
  let args := b.getAppArgs
  if b.getAppFn.isConstOf refineConst then
    args[2]? >>= strLit?
  else if b.getAppFn.isConstOf mkConst then
    match args[1]? with
    | some sh =>
      let sh := sh.consumeMData
      if sh.getAppFn.isConstOf shapeRefine then sh.getAppArgs[0]? >>= strLit? else none
    | none => none
  else none

/-- Is `p` (syntactically) the constant predicate `False`? -/
def constFalse (p : Expr) : Bool :=
  match p.consumeMData with
  | .lam _ _ b _ => b.consumeMData.isConstOf ``False
  | _ => false

/-- The codec a theorem's conclusion states lawfulness of, if any: `Lawful (c …)` or
`LawfulOn P (c …)` with `P` not constant `False`. -/
def lawfulHead? (concl : Expr) : Option Name :=
  let e := concl.consumeMData
  let args := e.getAppArgs
  if e.getAppFn.isConstOf lawfulConst then
    args[1]? >>= fun c => c.getAppFn.constName?
  else if e.getAppFn.isConstOf lawfulOnConst then
    match args[1]?, args[2]? with
    | some p, some c => if constFalse p then none else c.getAppFn.constName?
    | _, _ => none
  else none

/-- Does `t` state a decode of codec `c`? -/
def statesDecode (c : Name) (t : Expr) : Bool :=
  (t.find? fun e => e.isAppOf decodeConst &&
    (e.getAppArgs[1]?.map (·.getAppFn.isConstOf c) |>.getD false)).isSome

structure Row where
  decl : Name
  theorems : List Name

def parseRows (text : String) : Except String (List Row) :=
  text.splitOn "\n" |>.foldlM (init := []) fun acc line =>
    let line := line.trimAsciiEnd.toString
    if line.isEmpty || line.startsWith "#" then pure acc
    else match line.splitOn "\t" with
      | decl :: thms :: reason :: _ =>
        if reason.trimAscii.toString.isEmpty then throw s!"allow row without a reason: {line}"
        else
          let ts := (thms.splitOn ",").map (·.trimAscii.toString.toName)
          pure (acc ++ [⟨decl.toName, ts⟩])
      | _ => throw s!"allow row is not decl<TAB>theorem[,theorem]<TAB>reason: {line}"

def moduleOf (env : Environment) (c : Name) : Option Name :=
  env.getModuleIdxFor? c |>.bind fun idx => env.header.moduleNames[idx.toNat]?

syntax (name := refineCensus) "#refine_census " str ident+ : command

@[command_elab refineCensus]
def elabRefineCensus : CommandElab
  | `(#refine_census $path:str $roots:ident*) => do
    let roots := roots.toList.map (·.getId)
    let rows ← match parseRows (← IO.FS.readFile path.getString) with
      | .ok r => pure r
      | .error e => throwError e
    let env ← getEnv
    let under (c : Name) : Bool := match moduleOf env c with
      | some m => roots.any (·.isPrefixOf m)
      | none => false
    let mut sites : Array (Name × String) := #[]
    let mut proved : NameSet := {}
    for (c, ci) in env.constants.map₁.toList do
      unless under c do continue
      match ci with
      | .defnInfo d =>
        let s? ← liftTermElabM <| lambdaTelescope d.value fun _ b => pure (siteName? b)
        if let some s := s? then sites := sites.push (c, s)
      | .thmInfo t =>
        let h? ← liftTermElabM <| forallTelescope t.type fun _ concl => pure (lawfulHead? concl)
        if let some h := h? then proved := proved.insert h
      | _ => pure ()
    let mut bad : Array String := #[]
    let mut allowed := 0
    for (c, s) in sites do
      if proved.contains c then continue
      match rows.find? (·.decl == c) with
      | some _ => allowed := allowed + 1
      | none => bad := bad.push s!"refine site {c} (\"{s}\") has no lawfulness theorem (Lawful/LawfulOn _ ({c} …))"
    for row in rows do
      if !(sites.any (·.1 == row.decl)) then
        bad := bad.push s!"allow row matches no refine site: {row.decl}"
      else if proved.contains row.decl then
        bad := bad.push s!"allow row is stale: {row.decl} has its own lawfulness theorem"
      for t in row.theorems do
        match env.find? t with
        | some (.thmInfo ti) =>
          unless statesDecode row.decl ti.type do
            bad := bad.push s!"allow row {row.decl}: {t} states no decode of {row.decl}"
        | _ => bad := bad.push s!"allow row {row.decl}: {t} is not a theorem"
    if bad.isEmpty then
      logInfo m!"REFINE-CENSUS ok: {sites.size} refine sites, {sites.size - allowed} with a lawfulness theorem, {allowed} by allow row"
    else
      throwError m!"REFINE-CENSUS red ({bad.size}):\n{String.intercalate "\n" bad.toList}"
  | _ => throwUnsupportedSyntax

end Census.Refines
