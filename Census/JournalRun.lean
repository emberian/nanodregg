import Census.Journal

namespace Census.JournalRun
open Lean Elab Command

structure Revision where
  claim : String
  target : String
  context : String
  definitions : String
  instanceId : String
  toolchain : String
deriving DecidableEq, Repr

inductive CheckResult where
  | checked
  | rejected
  | exhausted
  | incomplete
deriving DecidableEq, Repr

structure Receipt where
  revision : Revision
  artifact : String
  recipe : String
  inputs : List (String × String)
  result : CheckResult
  complete : Bool
deriving DecidableEq, Repr

abbrev Store := String → Option String

def inputsMatch (r : Receipt) (w : Store) : Bool :=
  r.inputs.all fun p => decide (w p.1 = some p.2)

def receiptCheck (r : Receipt) (rev : Revision) : Bool :=
  decide (r.revision = rev) && decide (r.result = .checked) && r.complete

inductive ReceiptVerdict where
  | verified
  | receiptMismatch
  | inputMismatch
  | pruned (blockers : List (Nat × Nat))
  | suspended (missing : List (Nat × Nat))
  | uncovered (cost budget : Nat)
deriving Repr

/-- Finite receipt authorization only. Lean proof replay is a separate command.
There is no term calculus, substitution, hypothetical judgment or toy world here. -/
def judgeReceipt (r : Receipt) (rev : Revision) (env : Store)
    (live supports blockers : List (Nat × Nat)) (cost budget : Nat) : ReceiptVerdict :=
  if receiptCheck r rev = false then .receiptMismatch
  else if inputsMatch r env = false then .inputMismatch
  else
    let blocked := blockers.filter live.contains
    let missing := supports.filter fun t => !live.contains t
    if !blocked.isEmpty then .pruned blocked
    else if !missing.isEmpty then .suspended missing
    else if cost ≤ budget then .verified else .uncovered cost budget

def field (j : Json) (key : String) (α : Type) [FromJson α] : CommandElabM α :=
  match j.getObjValAs? α key with
  | .ok x => pure x
  | .error e => throwError "INCOMPLETE COVERAGE: {e}"

def revision (j : Json) : CommandElabM Revision := do
  return ⟨← field j "claim" String, ← field j "target" String,
    ← field j "context" String, ← field j "definitions" String,
    ← field j "instanceId" String, ← field j "toolchain" String⟩

def receipt (j : Json) : CommandElabM Receipt := do
  let r ← revision (← field j "revision" Json)
  let inputs ← field j "inputs" (List (String × String))
  let result ← field j "result" String
  let result ← match result with
    | "checked" => pure CheckResult.checked
    | "rejected" => pure CheckResult.rejected
    | "exhausted" => pure CheckResult.exhausted
    | "incomplete" => pure CheckResult.incomplete
    | _ => throwError "INCOMPLETE COVERAGE: unknown receipt result"
  return ⟨r, ← field j "artifact" String, ← field j "recipe" String, inputs,
    result, ← field j "complete" Bool⟩

def statusName : ReceiptVerdict → String
  | .verified => "verified"
  | .suspended _ => "suspended"
  | .pruned _ => "pruned"
  | .receiptMismatch => "receiptMismatch"
  | .inputMismatch => "inputMismatch"
  | .uncovered _ _ => "uncovered"

syntax (name := journalJudge) "#journal_judge " str str : command

/-- Check finite Census receipt data. This command does not assert Lean truth or
execute a proof checker; kernel replay and semantic audit stay separate. -/
@[command_elab journalJudge]
def elabJudge : CommandElab
  | `(#journal_judge $input:str $output:str) => do
    let txt ← IO.FS.readFile input.getString
    let js ← match Json.parse txt with
      | .ok j => pure j
      | .error e => throwError "INCOMPLETE COVERAGE: {e}"
    let requests ← field js "requests" (Array Json)
    let inputs ← field js "world" (List (String × String))
    let inputMap := inputs.foldl (fun (m : Std.HashMap String String) p => m.insert p.1 p.2) {}
    let mut rows : Array Json := #[]
    for j in requests do
      let id ← field j "id" String
      let rev ← revision (← field j "revision" Json)
      let r ← receipt (← field j "receipt" Json)
      let live ← field j "live" (List (Nat × Nat))
      let supports ← field j "supports" (List (Nat × Nat))
      let blockers ← field j "blockers" (List (Nat × Nat))
      let cost ← field j "cost" Nat
      let budget ← field j "budget" Nat
      let verdict := judgeReceipt r rev (fun k => inputMap[k]?)
        live supports blockers cost budget
      rows := rows.push <| Json.mkObj [("id", toJson id), ("status", toJson (statusName verdict)),
        ("detail", toJson (reprStr verdict))]
    IO.FS.writeFile output.getString ((toJson rows).compress ++ "\n")
    logInfo m!"JOURNAL JUDGE: {rows.size} finite receipts"
  | _ => throwUnsupportedSyntax


end Census.JournalRun
