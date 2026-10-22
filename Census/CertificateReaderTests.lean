/- Executed tests of the certificate reader, using a finite environment with a cycle.
These are synthetic checks of the generic reader, not the requested nano theorem vector. -/
import Census.CertificateReader

namespace Census.CertificateReader.Tests

structure Body where
  type : List Nat
  dependencies : List Nat
  ax : Bool
  thm : Bool
  revision : Nat
  deriving DecidableEq, Repr

def checker : Checker := ⟨"test-logic", "test-toolchain", "test-revision", ["test-theory"]⟩

def body (n : Nat) : Body :=
  match n with
  | 0 => ⟨[1], [2], false, true, 0⟩
  | 1 => ⟨[], [], false, false, 0⟩
  | 2 => ⟨[], [3], false, false, 0⟩
  | 3 => ⟨[], [2], true, false, 0⟩
  | _ => ⟨[], [], false, false, 0⟩

def reader : Reader Nat (List Nat) Body :=
  ⟨fun n => if n < 5 then some (body n) else none,
   Body.type, id, Body.dependencies, Body.ax, Body.thm, checker⟩

private instance {E A : Type} [DecidableEq E] [DecidableEq A] : DecidableEq (Except E A) :=
  fun x y => match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => h (Except.ok.inj h'))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun h' => h (Except.error.inj h'))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

def outcome {A : Type} : Except Refusal A → Except Refusal Unit
  | .ok _ => .ok ()
  | .error e => .error e

def tests : Except Refusal (List (String × Except Refusal Unit × Except Refusal Unit)) := do
  let c ← read reader 100 0
  let absent := { c with context := c.context.filter (fun e => e.name != 3), assumptions := [] }
  let changed := { c with context := c.context.map fun e =>
    if e.name = 2 then { e with body := { e.body with revision := 1 } } else e }
  let extended := { c with context := c.context ++ [⟨4, body 4⟩] }
  return [
    ("positive/cycle", accept reader c, .ok ()),
    ("different-context/same-statement",
      if extended.statement = c.statement ∧ extended ≠ c then accept reader extended
      else .error .contextMismatch, .ok ()),
    ("checker", accept reader { c with checker := { checker with logic := "other-logic" } },
      .error .checkerMismatch),
    ("missing-target", accept reader { c with target := 9 }, .error .missingTarget),
    ("not-theorem", accept reader ⟨1, [], [⟨1, body 1⟩], [], checker⟩, .error .notTheorem),
    ("statement", accept reader { c with statement := [] }, .error .statementMismatch),
    ("target-context", accept reader
      { c with context := c.context.filter (fun e => e.name != 0) }, .error .contextMismatch),
    ("definition", accept reader changed, .error .contextMismatch),
    ("statement-constant", accept reader
      { c with context := c.context.filter (fun e => e.name != 1) }, .error .incompleteContext),
    ("transitive-constant", accept reader absent, .error .incompleteContext),
    ("assumptions", accept reader { c with assumptions := [] }, .error .assumptionsMismatch),
    ("fuel", outcome (read reader 0 0), .error .fuelExhausted),
    ("missing-read", outcome (read reader 100 9), .error .missingTarget),
    ("non-theorem-read", outcome (read reader 100 1), .error .notTheorem),
    ("missing-dependency-read", outcome (read
      { reader with lookup := fun n => if n = 3 then none else reader.lookup n } 100 0),
      .error .missingTarget)]

def run (args : List String) : IO UInt32 := do
  let rows ← match tests with
    | .error e => IO.println s!"FAIL certificate: setup {repr e}"; return 1
    | .ok rows => pure rows
  let rows := if args.contains "--harness-control" then
    rows ++ [("harness-control", .ok (), .error .contextMismatch)] else rows
  let mut failed := false
  for (name, actual, expected) in rows do
    if actual = expected then IO.println s!"PASS certificate: {name}"
    else
      IO.println s!"FAIL certificate: {name}; expected {repr expected}; actual {repr actual}"
      failed := true
  if failed then return 1
  IO.println "certificate-tests: GREEN"
  return 0

end Census.CertificateReader.Tests
