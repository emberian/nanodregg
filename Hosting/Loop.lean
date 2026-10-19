/-
# Hosting.Loop — one round of the controller, as a pure function

The controller exe (`Hosting.Cli`) follows its Store with HOST's tail and talks to `grain-launch`
over two pipes. Every round it hands `step` the ids the round's Turns touched or bore
(`Controller.touchedIds`) and the reports the launcher sent; `step` returns the actions to write and
what the controller remembers. Nothing here does IO, so the sim runs the same `step` the exe runs.

What `step` remembers is observation, never World state: which children run, their recent exits,
the launcher's clock (advisory: one report far in the future disables the crash-loop window; the
launcher is the operator's own process) and the last tick it accepted, and the id of every grain it launched (so an exit report, which names a
directory, sends that grain's id back through `reconcile`: a child that exits while its grain still
desires `running` is relaunched or refused `crashLoop`, never forgotten).

Per round: reports are folded in first (`State.absorb`), then every id is decided ONCE against
that memory (`ids` deduplicated, then paged by `Bounds.grainsMax` into `reconcile`), then the
actions are folded in (`State.after`): a launch marks the child running at once, so a second
round before its `started` report does not launch it again.

Laws the LAUNCHER keeps, which this memory relies on (`launcher/`): one child per grain (a launch
for a grain whose child is still up ends the launcher by name); reports in the order things
happened, on one FIFO pipe (so an old child's `exited` always precedes its successor's `started`,
and reports need no generation); and when the controller's pipe closes, every child is killed
before the launcher exits (so a restarted controller, whose memory starts empty, never meets an
orphan); and while idle, a `tick` report every `tickMs` of its clock (HOSTING-38).

THE CLOCK MOVES WITHOUT A TURN (HOSTING-38). The clock is the latest `atMs` the launcher reported,
ticks included; a tick less than `tickMs` past the last accepted tick is ignored (`State.clock`: it
moves nothing and costs no decision, `Proofs.Loop.tick_ignored`). When a round's clock passes the
window of a grain this process launched, which has no child and was crash-looping at the previous
clock, its id is decided again in that round (`lifted`, `Proofs.Loop.step_lifts`): relaunched if it
still qualifies, refused by name otherwise. Nothing else is re-decided, so a tick round that lifts
nothing emits nothing (`Proofs.Loop.step_quiet`). The clock is a report, never read by the
controller: `step` stays a function of the World and the reports (it is pure: no IO in its type, so
a replay is the same by construction). A window in Turns (the World's height) was refused: it would
pass only with strangers' traffic. That no accepted tick is ever ignored for good is the pairing,
not a theorem: grain-launch spaces its ticks by the same emitted `TICK_MS`, and a new launcher means a
new controller (`launcherGone`), whose memory starts at `State.empty`.
-/
import Hosting.Controller
import Hosting.Wire

namespace Nanodregg.Hosting.Loop

open Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Controller

variable {D : Type} [Ord D] [DecidableEq D]

/-- The controller's memory between rounds (memory only; a restart forgets it, HOSTING-7). -/
structure State (D : Type) where
  live : List Live
  /-- each grain this process launched: its directory and its World id -/
  launched : List (ByteArray × D)
  /-- the launcher's clock, the latest `atMs` it reported -/
  now : Nat
  /-- the `atMs` of the last tick the clock accepted -/
  tickAt : Nat

def State.empty : State D := ⟨[], [], 0, 0⟩

/-- Update the report of grain `g` (adding one when there is none). -/
def upsert (live : List Live) (g : ByteArray) (f : Live → Live) : List Live :=
  if live.any (·.grain == g) then live.map fun l => if l.grain == g then f l else l
  else live ++ [f { grain := g, running := false, exits := [] }]

/-- An exit at `t`: not running, `t` recorded, at most `restartsMax` exits kept (the most recent
reports; `crashLooping` needs no more). -/
def exitAt (t : Nat) (l : Live) : Live :=
  { l with running := false, exits := (t :: l.exits).take restartsMax }

/-- The grain a report names (a tick names none). -/
def _root_.Nanodregg.Hosting.Report.grain? : Report → Option ByteArray
  | .started g _ | .exited g _ _ | .failed g _ _ => some g
  | .tick _ => none

def _root_.Nanodregg.Hosting.Report.atMs : Report → Nat
  | .started _ t | .exited _ _ t | .failed _ _ t | .tick t => t.toNat

/-- One report folded in. A failed launch counts as an exit: a grain whose launch the sandbox
refuses is crash-looped, never relaunched every round. -/
def absorbOne (live : List Live) : Report → List Live
  | .started g _ => upsert live g fun l => { l with running := true }
  | .exited g _ t => upsert live g (exitAt t.toNat)
  | .failed g _ t => upsert live g (exitAt t.toNat)
  | .tick _ => live

/-- The ids an exit report sends back through `reconcile`. -/
def returning (launched : List (ByteArray × D)) (rs : List Report) : List D :=
  rs.filterMap fun r => match r with
    | .exited g _ _ | .failed g _ _ => (launched.find? (·.1 == g)).map (·.2)
    | _ => none

/-- One report on the clock `(now, tickAt)`: a tick moves it only when at least `tickMs` past the
last accepted tick (a faster ticker is ignored, by this rule, and costs no decision); every other
report moves `now` to its time when later. -/
def clockOne : Nat × Nat → Report → Nat × Nat
  | (n, k), .tick t => if k + tickMs ≤ t.toNat then (max n t.toNat, t.toNat) else (n, k)
  | (n, k), r => (max n r.atMs, k)

/-- One action folded in: a launch marks its child running. -/
def afterOne (live : List Live) (a : Action) : List Live :=
  match a.verdict with
  | .launch _ => upsert live a.grain fun l => { l with running := true }
  | _ => live

/-- `l` in pages of `n`, `fuel` pages at most (`pages n l.length l` covers `l` for `0 < n`). -/
def pages {α : Type} (n : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, l => l.take n :: pages n k (l.drop n)

/-- One action remembered: a launch records its grain's id (once). -/
def rememberOne (bytesOf : D → ByteArray) (ids : List D) (acc : List (ByteArray × D)) (a : Action) :
    List (ByteArray × D) :=
  match a.verdict with
  | .launch _ =>
    if acc.any (·.1 == a.grain) then acc else
    match ids.find? (fun i => dirOf (bytesOf i) == a.grain) with
    | some i => acc ++ [(a.grain, i)]
    | none => acc
  | _ => acc

/-- Remember the id of every grain launched this round. -/
def remember (bytesOf : D → ByteArray) (ids : List D) (launched : List (ByteArray × D))
    (acts : List Action) : List (ByteArray × D) :=
  acts.foldl (rememberOne bytesOf ids) launched

/-- Is `g` a grain this process launched? -/
def State.knows (st : State D) (g : ByteArray) : Bool := st.launched.any (·.1 == g)

/-- Does the report name a grain this process launched? (A tick names none.) -/
def State.knowsReport (st : State D) (r : Report) : Bool :=
  match r.grain? with
  | some g => st.knows g
  | none => false

/-- The live reports after the round's reports. A report for a grain this process never launched
is ignored: it marks nothing running (a `started` for a stranger would otherwise keep a child
"running" that no round decides) and grows nothing (a launcher cannot inflate the memory). -/
def State.absorb (st : State D) (rs : List Report) : List Live :=
  (rs.filter st.knowsReport).foldl absorbOne st.live

/-- The clock after the round's reports: `(now, tickAt)`. -/
def State.clock (st : State D) (rs : List Report) : Nat × Nat := rs.foldl clockOne (st.now, st.tickAt)

/-- The grains whose crash-loop window this round's clock passed: launched by this process, no
child, crash-looping at the previous clock `st.now` and not at `now`. At most one id per launched
grain (`Proofs.Loop.lifted_length`); none when the clock did not move. -/
def lifted (st : State D) (live : List Live) (now : Nat) : List D :=
  if now = st.now then [] else
  st.launched.filterMap fun x =>
    if !runningIn live x.1 && crashLooping st.now live x.1 && !crashLooping now live x.1 then some x.2
    else none

/-- The ids a round decides: the touched ones, the grains an exit report returned, and the grains
whose window the round's clock passed, once each. -/
def roundIds (st : State D) (touched : List D) (rs : List Report) : List D :=
  (touched ++ returning st.launched rs ++ lifted st (st.absorb rs) (st.clock rs).1).eraseDups

/-- Does the World's cell at `i` still qualify for a child: a lifecycle object that decodes and
desires `running`? -/
def qualifies (E : Env D) (pkgId : ByteArray) (w : World D) (i : D) : Bool :=
  match w.live E i with
  | none => false
  | some c => isGrain pkgId c && match grainOf ByteArray.empty c with
    | some (_, .running) => true
    | _ => false

/-- What the memory keeps after a round: a launched grain while its child runs or its cell still
qualifies; its report while the grain is kept. So the memory is bounded by the running children
and the qualifying grains of the World (`Proofs.Loop.step_kept`), never by history. -/
def prune (E : Env D) (pkgId : ByteArray) (w : World D) (live : List Live) (launched : List (ByteArray × D)) :
    List Live × List (ByteArray × D) :=
  let kept := launched.filter fun (g, i) => runningIn live g || qualifies E pkgId w i
  (live.filter fun l => kept.any (·.1 == l.grain), kept)

/-- One round: fold the reports in, decide every id once, fold the actions in. -/
def step (E : Env D) (bytesOf : D → ByteArray) (label pkgId : ByteArray) (w : World D) (st : State D)
    (touched : List D) (rs : List Report) : State D × List Action :=
  let live := st.absorb rs
  let c := st.clock rs
  let ids := roundIds st touched rs
  let acts := (pages Bounds.grainsMax ids.length ids).flatMap
    (reconcile E bytesOf label pkgId c.1 live w)
  let (live', launched') :=
    prune E pkgId w (acts.foldl afterOne live) (remember bytesOf ids st.launched acts)
  ({ live := live', launched := launched', now := c.1, tickAt := c.2 }, acts)

/-- Every cell slot id, live or tomb (a tomb decides as `none`), for the first round (O(store) once, at start: law 5's request path is the
per-round one). -/
def allIds (w : World D) : List D := w.cellIds

end Nanodregg.Hosting.Loop
