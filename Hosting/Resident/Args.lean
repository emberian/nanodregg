/-
# Hosting.Resident.Args — a grain's argv is its plan, joined onto the operator's roots (HOSTING-27)

grain-launch starts every grain with its launch frame's paths as argv, one field after another
in `Plan` order (`launcher::plan_argv`): the program, then for each of read, write, exec, broker and
member a count followed by that many absolute paths. Hidden paths are not passed, since they name
what the grain must not see. The sandbox clears the environment and grants no `/proc` read, so argv
is the only way a confined grain learns where it is.

The resident trusts none of it until it is its plan. `place` reads the label, the grain id and the
entry out of the program path (`…/worlds/<l>/grains/<id>/pkg/<entry>`), computes Lean's own
`plan l g` for that resident grain, takes the three roots off the front of the paths, and accepts
only if the argv is EXACTLY that plan joined onto those roots, field for field
(`Proofs.Resident.place_render`). A reordered field (member sockets where broker sockets belong),
a dropped path or a stray one is refused `argvNotPlan`.
-/
import Hosting.Plan

namespace Nanodregg.Hosting.Resident

/-- The argv's fields, as bytes, in plan order (absolute paths). -/
structure Args where
  program : ByteArray
  read : List ByteArray
  write : List ByteArray
  exec : List ByteArray
  broker : List ByteArray
  member : List ByteArray
  deriving DecidableEq

/-- One field's argv words: its count, then its paths. -/
def fieldArgv (ps : List ByteArray) : List ByteArray := (toString ps.length).toUTF8 :: ps

/-- The argv grain-launch passes for `a` (after argv[0], which Lean's `main` does not see). -/
def Args.argv (a : Args) : List ByteArray :=
  a.program :: (fieldArgv a.read ++ fieldArgv a.write ++ fieldArgv a.exec ++ fieldArgv a.broker
    ++ fieldArgv a.member)

/-- One field off the front: a count, then that many words. -/
def takeField : List ByteArray → Option (List ByteArray × List ByteArray)
  | [] => none
  | c :: rest => do
    let n ← (String.fromUTF8? c).bind String.toNat?
    if n ≤ rest.length then some (rest.take n, rest.drop n) else none

/-- Argv read into fields, unchecked: a count before each field. -/
def fields (argv : List ByteArray) : Option Args := do
  let p :: rest := argv | none
  let (r, rest) ← takeField rest
  let (w, rest) ← takeField rest
  let (e, rest) ← takeField rest
  let (b, rest) ← takeField rest
  let (m, rest) ← takeField rest
  unless rest.isEmpty do none
  pure ⟨p, r, w, e, b, m⟩

/-- Read argv into fields; `none` unless it is exactly `Args.argv` of what it read
(`Proofs.Resident.parse_argv`): a count that does not spell a decimal the way `toString` does
(`01`, `+1`) is refused too. -/
def parse (argv : List ByteArray) : Option Args := (fields argv).filter (·.argv = argv)

/-- `root/rel`: a plan path joined onto a root, the way the launcher joins it (`Path::join` of a
relative, clean path onto an absolute root with no trailing slash). -/
def joinOnto (root : ByteArray) (rel : Path) : ByteArray :=
  root ++ ByteArray.mk #[Codec.Path.sep] ++ Codec.Path.join rel

/-- `b` with `suffix` removed from its end, if `b` ends with it. -/
def dropSuffix (b suffix : ByteArray) : Option ByteArray :=
  if suffix.size ≤ b.size ∧ b.extract (b.size - suffix.size) b.size = suffix then
    some (b.extract 0 (b.size - suffix.size))
  else none

/-- Where a resident is: the three roots and the grain Lean plans for. -/
structure Placed where
  root : ByteArray
  brokerRoot : ByteArray
  memberRoot : ByteArray
  label : ByteArray
  grain : Grain
  plan : Plan
  /-- the plan is Lean's for this label and grain -/
  planned : Hosting.plan label grain = .ok plan

/-- The argv the launcher derives from a placed plan: every path joined onto its root. -/
def Placed.args (p : Placed) : Args where
  program := joinOnto p.root p.plan.program
  read := p.plan.read.map (joinOnto p.root)
  write := p.plan.write.map (joinOnto p.root)
  exec := p.plan.exec.map (joinOnto p.root)
  broker := p.plan.broker.map (joinOnto p.brokerRoot)
  member := p.plan.member.map (joinOnto p.memberRoot)

/-- The root a field's first path was joined onto, given the plan's relative first path. -/
def rootOf (abs : List ByteArray) (rel : List Path) : Option ByteArray :=
  match abs, rel with
  | a :: _, r :: _ => dropSuffix a (ByteArray.mk #[Codec.Path.sep] ++ Codec.Path.join r)
  | _, _ => none

/-- The label, grain and roots an argv names, and Lean's plan for them, unchecked against the
rest of argv: the program path names the label, the grain and the entry; the roots come off the
front of the program path and of the first broker and member socket. -/
def candidate (a : Args) : Option Placed :=
  match Codec.Path.split a.program |>.reverse with
  | entry :: pk :: id :: gs :: l :: w :: _ =>
    if w = lit "worlds" ∧ gs = lit "grains" ∧ pk = lit "pkg" then
      let g : Grain := { idHex := id, kind := .resident, entry := entry }
      match h : Hosting.plan l g with
      | .ok pl => do
        let root ← dropSuffix a.program (ByteArray.mk #[Codec.Path.sep] ++ Codec.Path.join pl.program)
        let br ← rootOf a.broker pl.broker
        let mr ← rootOf a.member pl.member
        pure ⟨root, br, mr, l, g, pl, h⟩
      | .error _ => none
    else none
  | _ => none

/-- The resident's own plan from its argv, or `none` (`argvNotPlan`): the candidate, accepted only
if argv is exactly its plan joined onto its roots (`Proofs.Resident.place_args`). -/
def place (a : Args) : Option Placed := (candidate a).filter (·.args = a)

end Nanodregg.Hosting.Resident
