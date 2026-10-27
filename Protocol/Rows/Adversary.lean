/-
# Protocol.Rows.Adversary — a generated adversarial Host, judged by the member-level spec (DESIGN-QA Q6)

`adversary --seeds N` generates, per seed, a deployment and an environment and runs the real
follower against it (`Protocol.Rows.Loopback`: HOST's loop on its own thread, each actor's
`host follow` through `Host.Follow.answer`, custody, nd's attempt store), then judges the run by
what the member is promised (`Spec.Proofs.Claims` §2 and §4), never by a row's expected outcomes.

A seed draws:
* a SCRIPT: one member row's lines (`Protocol.rows`), its acts and argvs, with each line's own fault
  kept or dropped and a cold start sometimes added. The row's expectations are not read;
* the WRITER's lies (`Writer.Params`): a page that hides the rest of the log, a tip stated as the
  newest base, a forged base or certificate, an expiry without its height, `forgotten` as a refusal,
  a forged refusal record, a recorded call committed while answered refused, a read gate without its
  lower bound, a spent set forgotten, and the page budget (the deployed one, or one past the frame);
* the RELAY (`Loopback.Relay`): a tape of one move per exchange with the writer (drop, withhold,
  duplicate, flip a byte, replace the status, answer with nothing behind it, replay an earlier reply,
  edit a page's events, move its stated tip or base, inflate an expiry, `pageIo`), and a tape of
  continuation swaps (follow handed a continuation it handed the actor earlier).

The judge, over every top-level `nd` run (`Loopback.Seen`) and the end state:
* **okCommitted** (C(ii), member-level): a run of a submitting verb that ends `ok` froze or continued
  a call, and the member's own World after it journals THAT call (the harness knows which call the
  member's command froze; the continuation is not asked);
* **cancelOk** (C(ii), cancel): `cancel CALL` that ends `ok` leaves the member's World settling the
  call `refused cancelled`;
* **signsOwn** (C(i), member-level): every call-domain message custody signs in a run was asked for
  by a continuation carrying that run's own argv;
* **final** (C(iii)): a call the member's World settles `expired` or `refused` (any code) at the end
  of any run is not journaled by the writer's World at the end, and that World's `submit` refuses it;
* **oneHistory** (A1): after the script, the writer is reopened honest, the relay is honest, and each
  actor catches up twice, from its own World and from the genesis World; when the second succeeds,
  the first must succeed and reach the same step count and chain;
* **bounded**: no run ends on a harness bound (`tooManySteps`, `attemptFuel`, `tooDeep`) or with a
  reply the harness cannot decode (`badFrame`): every command ends within a named number of exchanges.

Any named refusal is a pass: the follower refused the lie. A finding is an `ok` (or a World) the
claims forbid. Each seed prints one `TRACE` line (its moves, outcomes, findings and the writer's end
World), each finding a `FINDING` line.

The known-red control (`--harness-control`, GATES-15): the same seeds, the swap move removed, against the system under
`Loopback.sys`'s mutation `trustCancel` (`cancel` ends `ok` on the writer's word, follow's settlement
skipped). The run must find something and read `FINDINGS … (harness-control: trustCancel)`, exit 1;
a control that finds nothing reads `ALL PASS` and gates/runs.py refuses the row. The swap is
removed because it alone finds okCommitted and signsOwn on the unmutated follower.
-/
import Protocol.Rows.Loopback
import Protocol.Rows.Deployed
import Kernel.Sim.Gen
import Std.Data.HashMap

namespace Nanodregg.Protocol.Rows.Adversary

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command
open Nanodregg.Protocol.Rows.Loopback
open Nanodregg.Kernel.Sim.Gen (Rng)

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The generator -/

/-- `n` draws, each below `bound`. -/
def Rng.draws (r : Rng) (bound : Nat) : Nat → List Nat × Rng
  | 0 => ([], r)
  | n + 1 =>
      let (x, r) := r.below bound
      let (xs, r) := Rng.draws r bound n
      (x :: xs, r)

/-- A uniform pick from a non-empty list (`d` if empty). -/
def pick {α : Type} (r : Rng) (d : α) (xs : List α) : α × Rng :=
  let (i, r) := r.below xs.length
  ((xs[i]?).getD d, r)

/-- The Host's word with nothing behind it, as a relay answers it. -/
def answers : List (Status × String) :=
  [(.refused, "cancelled"), (.refused, "stale"), (.refused, "refusedFinal"), (.ok, ""), (.uncertain, "forgotten"),
   (.uncertain, ""), (.declined, "stale"), (.absent, ""), (.refused, "expired"), (.refused, "badEnvelope")]

/-- One relay move, drawn. -/
def drawMove (r : Rng) : Move × Rng :=
  let (k, r) := r.below 14
  let (x, r) := r.next
  let x := x.toNat
  match k with
  | 0 => (.drop, r)
  | 1 => (.withhold, r)
  | 2 => (.duplicate, r)
  | 3 => (.flip (x % 4096), r)
  | 4 => (.status ((Status.all[x % Status.all.length]?).getD .ok), r)
  | 5 => let (a, r) := pick r (.ok, "") answers; (.answer a.1 a.2, r)
  | 6 => (.replay, r)
  | 7 =>
      let e : EventEdit := match x % 6 with
        | 0 => .flip (x / 6 % 64) | 1 => .dropLast | 2 => .dropFirst | 3 => .dup (x / 6 % 64)
        | 4 => .swap | _ => .forgeCancel
      (.events e, r)
  | 8 => (.tip 0, r)
  | 9 => (.tip (1 + x % 1000), r)
  | 10 => (.base, r)
  | 11 => (.expired (1 + x % 1000000), r)
  | 12 => (.pageIo, r)
  | _ => (.events .forgeCancel, r)

/-- The relay's host tape: `n` exchanges, each a move with probability `rate`/1000. -/
def drawHost (r : Rng) (rate : Nat) : Nat → List Move × Rng
  | 0 => ([], r)
  | n + 1 =>
      let (c, r) := r.below 1000
      let (m, r) := if c < rate then drawMove r else (.pass, r)
      let (ms, r) := drawHost r rate n
      (m :: ms, r)

/-- The resume tape: `n` resumes, each a swap with probability `rate`/1000. -/
def drawResume (r : Rng) (rate : Nat) : Nat → List (Option Nat) × Rng
  | 0 => ([], r)
  | n + 1 =>
      let (c, r) := r.below 1000
      let (x, r) := r.below 1024
      let (ms, r) := drawResume r rate n
      ((if c < rate then some x else none) :: ms, r)

/-- How long the tapes are: past them the relay is honest. -/
def tapeLength : Nat := 2000

/-- The writer's lies, by name, and how each sets `Writer.Params`. -/
def writerLies : List (String × (Writer.Params D → Writer.Params D)) :=
  [("lieTip", fun p => { p with lieTip := true }), ("lieBase", fun p => { p with lieBase := true }),
   ("forgeBase", fun p => { p with forgeBase := true }),
   ("forgeCertificate", fun p => { p with forgeCertificate := true }),
   ("unstatedExpiry", fun p => { p with unstatedExpiry := true }),
   ("forgottenRefused", fun p => { p with forgottenRefused := true }),
   ("forgeRefusal", fun p => { p with forgeRefusal := true }),
   ("admitsRecorded", fun p => { p with admitsRecorded := true }),
   ("ignoreNotBefore", fun p => { p with ignoreNotBefore := true }),
   ("forgetSpent", fun p => { p with forgetSpent := true })]

/-- The writer's lies that are IN its log, not only in its replies. -/
def logLies : List String := ["forgeRefusal", "admitsRecorded", "forgetSpent"]

/-- The page budgets a writer may page with: the deployed one, the guess the queue Bell outgrew, the
per-field budget before PROTOCOL-70, and the frame itself. -/
def budgets : List Nat := [Host.Page.budget, 16384, Bounds.frameBytesMax - 1024, Bounds.frameBytesMax]

/-- The faults a line keeps from its row whatever the coin says: they are the scenario (another
member's race, a thief, a wrong follower, a relay's forged invitation or receipt), not the Host's lie. -/
def scenarioFault : Fault → Bool
  | .race .. | .stolenKey _ | .wrongFollower _ | .forgeInvite _ | .forgeReceipt => true
  | _ => false

/-- The member rows, the generator's seeds. -/
def seedRows : List Row := rows.filter fun r => match r.drive with
  | .members _ => r.blockedOn.isNone
  | .exe .. => false

/-- The most times a seed repeats a row's line: past one window (the rows' window is 100), so a cold
follower meets `expired`, and no more (THE BAR's and coldCatchUp's counts are measurements, not lies). -/
def timesMax : Nat := 110

/-- What one seed draws. -/
structure Draw (D : Type) [Ord D] where
  row : Row
  lines : List Line
  lies : List String
  budget : Nat
  writer : Writer.Params D → Writer.Params D
  relay : Relay

/-- A seed's draw. -/
def draw (seed : Nat) : Draw D :=
  let r : Rng := ⟨(UInt64.ofNat seed) * 0x2545F4914F6CDD1D + 0x5851F42D4C957F2D⟩
  let (row, r) := pick r (seedRows.headD Protocol.journey) seedRows
  -- the lines: each row fault kept on a coin, a cold start on one in eight
  let (coins, r) := Rng.draws r 16 row.lines.length
  let lines := (row.lines.zip coins).map fun (l, c) =>
    let fault := if scenarioFault l.fault || c % 2 = 0 then l.fault
      else if c = 1 || c = 3 then .cold else .none
    { l with fault, times := min l.times timesMax, withinMs := none, prints := none }
  -- the writer's lies: each on one seed in ten
  let (ls, r) := Rng.draws r 10 (writerLies (D := D)).length
  let chosen := ((writerLies (D := D)).zip ls).filter (·.2 = 0) |>.map (·.1)
  let (bc, r) := r.below 16
  let (budget, r) := if bc = 0 then pick r Host.Page.budget budgets else (Host.Page.budget, r)
  -- the relay: a rate per seed, up to one move in eight exchanges; swaps on one seed in four
  let (rate, r) := r.below 120
  let (host, r) := drawHost r rate tapeLength
  let (sw, r) := r.below 4
  let (resume, _) := drawResume r (if sw = 0 then 20 else 0) tapeLength
  { row, lines, lies := chosen.map (·.1), budget,
    writer := fun p => chosen.foldl (fun p l => l.2 p) { p with pageBudget := budget },
    relay := { host, resume } }

/-! ## The judge -/

/-- A finding: the claim it breaks, and what was seen. -/
structure Finding where
  claim : String
  detail : String

def boundNames : List String := ["tooManySteps", "attemptFuel", "tooDeep", "badFrame"]

def argvText (argv : List String) : String :=
  " ".intercalate (argv.map fun a => if a.length > 16 then (a.take 16).toString ++ "…" else a)

/-- The judge of one top-level run. -/
def judgeRun (X : Ctx D) (s : Seen D) : List Finding :=
  let at_ := s!"run {s.run} {s.actor}: {argvText s.argv} => {s.outcome.text}"
  let cmd := parse (D := D) X.digestOf (s.argv.map String.toUTF8)
  let own := s.argv.map String.toUTF8
  let ok := s.outcome = .ok
  let committed : List Finding := match cmd with
    | .ok c =>
        if ok && submits c then
          match s.calls.getLast? >>= X.decodeCall with
          | none => [⟨"okCommitted", s!"{at_}: no call was frozen or continued"⟩]
          | some call =>
              if (s.world.journalAt X.env (txIdOf X call)).isSome then []
              else [⟨"okCommitted", s!"{at_}: the member's World does not journal the call its command froze"⟩]
        else []
    | .error _ => []
  let cancelled : List Finding := match cmd with
    | .ok (.cancel cb) =>
        if !ok then [] else
        match X.decodeCall cb with
        | none => [⟨"cancelOk", s!"{at_}: the cancelled call does not decode"⟩]
        | some c =>
            if Command.settleOf X s.self s.world c = .refused (cancelledCode (D := D)) then []
            else [⟨"cancelOk", s!"{at_}: the member's World does not settle the call refused cancelled"⟩]
    | _ => []
  let signs : List Finding := s.signs.filterMap fun (_, kargv) =>
    if kargv = own then none
    else some ⟨"signsOwn", s!"{at_}: custody signed a call planned from another argv ({argvText (kargv.map fun b => (String.fromUTF8? b).getD "?")})"⟩
  let bounded : List Finding := match s.outcome with
    | .refused n => if boundNames.contains n then [⟨"bounded", at_⟩] else []
    | _ => []
  committed ++ cancelled ++ signs.take 1 ++ bounded

/-- The calls a run's member World holds final (`expired`, or `refused` by any code). -/
def finals (X : Ctx D) (s : Seen D) : List (Seen D × Call D) :=
  s.calls.filterMap fun cb => (X.decodeCall cb).bind fun c =>
    match Command.settleOf X s.self s.world c with
    | .expired | .refused _ => some (s, c)
    | _ => none

/-- `sync` until it is not `behind`, at most `n` times. -/
def syncUp (name : String) : Nat → M D Expect
  | 0 => pure .behind
  | n + 1 => do
      let (o, _) ← command name ["sync"] .none 4
      if o = .behind then syncUp name n else pure o

/-- The ONE HISTORY check, with the writer reopened honest and the relay honest: each actor catches
up from its own World, then (a copy) from the genesis World. A member's World that the honest log does
not extend (the second ends `ok` and the first does not, or they end at different heads) is a finding;
an actor that cannot read even from genesis is not judged. Then the writer's World at the end. -/
def oneHistory (logLie : Bool) : M D (List Finding × Option (World D) × Nat) := do
  modify fun st => { st with relay := { st.relay with host := [], resume := [] } }
  let st ← get
  let w := st.sys.writer
  set { st with sys := { st.sys with writer := { R := w.R, X := w.X } } }
  match ← restart false with
  | .ok => pure ()
  | o =>
      -- a writer that lied IN its log (a forged refusal record, a recorded call committed, a spent
      -- set forgotten) leaves a Store its own reopen refuses by name: the lie is caught, by the Host
      if logLie then return ([], none, (← get).actors.length)
      return ([⟨"oneHistory", s!"the honest reopen of the writer's Store: {o.text}"⟩], none, 0)
  let mut out : List Finding := []
  let mut unjudged := 0
  if (← get).carriedFile.isSome then
    return ([], none, (← get).actors.length)
  for (name, _) in (← get).actors do
    let mine ← syncUp name 16
    let a ← actor name
    setActor name { a with follow := { world := (← get).genesis } }
    let fresh ← syncUp name 16
    let f ← actor name
    setActor name a
    if fresh ≠ .ok then
      unjudged := unjudged + 1
    else if mine ≠ .ok then
      out := out ++ [⟨"oneHistory", s!"{name}: the honest catch-up from its own World ends {mine.text}, from genesis ok"⟩]
    else if a.follow.world.steps ≠ f.follow.world.steps || a.follow.world.chain ≠ f.follow.world.chain then
      out := out ++ [⟨"oneHistory", s!"{name}: its World at {a.follow.world.steps} is not the honest log's fold at {f.follow.world.steps}"⟩]
  let st ← get
  match ← st.host.stop with
  | .ok (_, r) => pure (out, some r.world, unjudged)
  | .error e => pure (out ++ [⟨"oneHistory", s!"the writer stopped: {e}"⟩], none, unjudged)

/-- C(iii) at the writer's World at the end: no call a member's World held final is journaled there,
and its `submit` refuses it. -/
def finalAt (X : Ctx D) (wEnd : World D) (fs : List (Seen D × Call D)) : List Finding :=
  fs.filterMap fun (s, c) =>
    let at_ := s!"run {s.run} {s.actor}: {argvText s.argv}: settled {(Command.settleOf X s.self s.world c).text X.env.bytes}"
    if (wEnd.journalAt X.env (txIdOf X c)).isSome then some ⟨"final", s!"{at_}, and the writer's World journals it"⟩
    else match submit X wEnd c with
      | .ok _ => some ⟨"final", s!"{at_}, and the writer's World admits it"⟩
      | .error _ => none

/-! ## One seed -/

/-- How often the member runs a disturbed command again. -/
def retries : Nat := 2

/-- A move's kind: its name with its numbers dropped (`log:expired`, `k:`). -/
def moveKind (m : String) : String := String.ofList (m.toList.filter (!·.isDigit))

/-- What one seed did. -/
structure Outcome where
  seed : Nat
  row : String
  findings : List Finding
  trace : String
  unjudged : Nat
  /-- each run's line and each move, for `--show` -/
  shown : List String
  /-- each (move, outcome) of a run in which the move was made, for `--census` -/
  pairs : List String

/-- Run one seed under the parameters `R` and the control mutation `m`. -/
def runSeed (R : Rows.Params D) (m : Option Mutation) (noSwap : Bool) (seed : Nat) : IO Outcome := do
  let d : Draw D := draw seed
  let d := if noSwap then { d with relay := { d.relay with resume := [] } } else d
  let s := sys R m
  let s := { s with writer := d.writer s.writer }
  let st0 ← setup s
  let go : M D (List Finding × Nat) := do
    -- the member runs a command the relay disturbed again, at most `retries` more times
    for (l, i) in d.lines.zipIdx do
      let mut o ← (runLine i l l.times : M D Expect)
      for _ in List.range retries do
        if o = .ok then break
        match l.act with
        | .cmd _ => o ← runLine i l 1
        | _ => break
    let X ← Loopback.X
    let seen := (← get).seen.toList
    let perRun := seen.flatMap (judgeRun X)
    let fs := seen.flatMap (finals X)
    let (hist, wEnd, unjudged) ← oneHistory (d.lies.any logLies.contains)
    let fin := match wEnd with
      | some w => finalAt X w fs
      | none => []
    pure (perRun ++ hist ++ fin, unjudged)
  let ((found, unjudged), st) ← go.run { st0 with judging := true, relay := d.relay }
  let wEnd := match ← st.host.stop with
    | .ok (_, r) => s!"{r.world.steps}:{(Text.toHex (s.writer.X.env.bytes r.world.chain)).hash}"
    | .error _ => "stopped"
  let outs := "\n".intercalate (st.seen.toList.map fun x => s!"{x.run} {x.actor} {x.outcome.text}")
  let fnd := "\n".intercalate (found.map fun f => s!"{f.claim} {f.detail}")
  let made := "\n".intercalate st.relay.made.toList
  let trace := s!"TRACE adversary seed={seed} row={d.row.name} lies=[{",".intercalate d.lies}] budget={d.budget} \
    moves {st.relay.made.size}:{made.hash} runs {st.seen.size}:{outs.hash} findings {found.length}:{fnd.hash} \
    world {wEnd}"
  let shown := st.seen.toList.map (fun x => s!"  run {x.run} {x.actor}: {argvText x.argv} => {x.outcome.text}") ++
    [s!"  moves {" ".intercalate (st.relay.made.toList.filter (!·.endsWith ":pass"))}"] ++ st.log.toList.map ("  " ++ ·)
  let pairs := st.seen.toList.flatMap fun x =>
    (x.moves.filter (!·.endsWith ":pass")).map fun m => s!"{moveKind m} => {x.outcome.text}"
  pure { seed, row := d.row.name, findings := found, trace, unjudged, shown, pairs }

/-! ## The runner -/

/-- The controls: a member-level check removed. Only a mutation that lets an `ok` past follow's own
settlement is one: `trustCancel` ends `cancel` on the writer's word. The attempt-store plants
(`trustLookup`, `settleDecline`) and `followVerifyAll` were MEASURED blind here (600 seeds each, no
finding): follow's settlement and the page's stated chain still refuse by name behind them, so they
weaken a layer the member is not promised anything of; their rows catch them by the name the row
expects. -/
def controls : List (String × Mutation) := [("trustCancel", .trustCancel)]

/-- `adversary [--deployed] [--from S] [--seeds N] [--no-swap] [--show] [--census] [--harness-control]`. -/
structure Args where
  deployed : Bool := false
  start : Nat := 0
  count : Nat := 64
  control : Option (String × Mutation) := none
  verbose : Bool := false
  census : Bool := false
  /-- the continuation-swap move removed (every control runs without it: the swap alone finds
  okCommitted and signsOwn on the unmutated follower, so a control's red would not be its mutation's) -/
  noSwap : Bool := false

def parseArgs : List String → Args → Option Args
  | [], a => some a
  | "--deployed" :: rest, a => parseArgs rest { a with deployed := true }
  | "--show" :: rest, a => parseArgs rest { a with verbose := true }
  | "--census" :: rest, a => parseArgs rest { a with census := true }
  | "--no-swap" :: rest, a => parseArgs rest { a with noSwap := true }
  | "--from" :: n :: rest, a => n.toNat?.bind fun k => parseArgs rest { a with start := k }
  | "--seeds" :: n :: rest, a => n.toNat?.bind fun k => if k = 0 then none else parseArgs rest { a with count := k }
  | "--harness-control" :: rest, a =>
      (controls.head?).bind fun c => parseArgs rest { a with control := some c, noSwap := true }
  | _ :: _, _ => none

/-- Run the seeds; print a TRACE line per seed and a FINDING line per finding. Exit 0 when no seed
finds anything (`ALL PASS`), 1 when one does (`FINDINGS n`, naming `harness-control` under the
control, which must therefore exit 1). -/
def report (R : Rows.Params D) (a : Args) : IO UInt32 := do
  IO.println s!"adversary under {R.name}: seeds {a.start}..{a.start + a.count - 1} over {seedRows.length} seed rows{(a.control.map fun c => s!", control {c.1}").getD ""}"
  let mut total := 0
  let mut seedsRed := 0
  let mut unjudged := 0
  let mut tally : Std.HashMap String Nat := {}
  for seed in (List.range a.count).map (· + a.start) do
    let o ← runSeed R (a.control.map (·.2)) a.noSwap seed
    IO.println o.trace
    if a.verbose then for l in o.shown do IO.println l
    for f in o.findings do
      IO.println s!"FINDING seed={seed} row={o.row} claim={f.claim} {f.detail}"
    total := total + o.findings.length
    if !o.findings.isEmpty then seedsRed := seedsRed + 1
    unjudged := unjudged + o.unjudged
    if a.census then
      for p in o.pairs do tally := tally.insert p (tally.getD p 0 + 1)
    (← IO.getStdout).flush
  for (p, n) in tally.toList.toArray.qsort (fun x y => x.1 < y.1) do IO.println s!"CENSUS {p} {n}"
  IO.println s!"UNJUDGED {unjudged} actor catch-ups (could not read from genesis, or a carried World)"
  let under := (a.control.map fun c => s!" (harness-control: {c.1})").getD ""
  if total = 0 then IO.println "ALL PASS"; pure 0
  else IO.println s!"FINDINGS {total} on {seedsRed} of {a.count} seeds{under}"; pure 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | none =>
      IO.eprintln s!"usage: adversary [--deployed] [--from S] [--seeds N] [--no-swap] [--show] [--census] [--harness-control] (got {args})"
      pure 2
  | some a => if a.deployed then report Rows.Params.deployed a else report Rows.Params.toy a

end Nanodregg.Protocol.Rows.Adversary
