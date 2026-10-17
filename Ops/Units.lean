/-
# Ops.Units — service-manager units for `host`, rendered from the exit tables (ASSEMBLY D5/D10)

A unit is `nd-supervise SOCKET (--hide|--read|--write|--exec PATH)… -- HOST VERB …` (CLIENT's
grammar, client/src/bin/nd-supervise.rs) with the restart policy READ from the two exit tables
nd-supervise's one code space holds: the child's `Host.Status`, passed through, and the
supervisor's own `Protocol.SupervisorExit`. systemd restarts on failure except the fatal codes of
both (`RestartPreventExitStatus` = `preventCodes`), so a Store that refuses to open stops by name
instead of looping, and a restart-class exit that repeats is stopped by the unit's start limit.
The unit decides nothing: every number comes from the tables, every argument from the `Node`.

`deploy/units/EXITS.md` is the operator's table, rendered from the same two tables: code, name,
class, what systemd does, and what the operator does (`hostAction`, `supervisorAction`). Both are
exhaustive matches, so a status added to either table without an operator action does not build.

Topology (CLIENT-12 B, ASSEMBLY D10): the writer's node runs `host serve` as a system unit; each
member runs `host follow` on its own machine as a user unit, writing its own Store. The member's
id and grant come from an `EnvironmentFile` the operator writes once (`ND_MEMBER`, `ND_GRANT`);
systemd substitutes them into argv, so `host` still has argv as its one input.

Refusals (a unit that would run unconfined or mis-quoted is never rendered):
`nothingHidden` (nd-supervise itself refuses it at launch, CLIENT-8; refusing here keeps the
emitted file honest), `badPath` (outside `[A-Za-z0-9/._-]`, optionally after a leading `%h/`:
nothing a unit file would re-quote or expand), `relative`.

macOS: launchd cannot prevent a restart by exit code. Its plist restarts every non-zero exit after
`throttleSeconds`; a fatal refusal therefore repeats, by name, every throttle interval, truncating
nothing (accepted in ASSEMBLY §1 O1: the Mac is a member machine, never the writer's node).
-/
import Host.Exit
import Protocol.Exit

namespace Nanodregg.Ops.Units

open Nanodregg.Host
open Nanodregg.Protocol (SupervisorExit)

/-- An argument of the supervised program: a literal, or a variable the unit's environment file
supplies (systemd `${NAME}`). -/
inductive Arg where
  | lit (s : String)
  | var (name : String)
  deriving DecidableEq, Repr

/-- What runs: `host serve STORE`, or `host follow STORE MEMBER GRANT` with the member's ids from
its environment file. -/
inductive Role where
  | serve
  | follow
  deriving DecidableEq, Repr

structure Node where
  /-- the unit's name stem, e.g. `nd-host-serve` -/
  name : String
  role : Role
  /-- the directory holding `host` and `nd-supervise` -/
  bin : String
  store : String
  socket : String
  /-- paths the child must not see (the member's workspace first, CLIENT-8) -/
  hide : List String
  /-- `User=` of a system unit; `none` renders a user unit -/
  user : Option String
  /-- where a follow unit's `NAME.env` lives (the deployed member: `%h/.nd`) -/
  envDir : String := "%h/.nd"
  deriving Repr

inductive Refusal where
  | nothingHidden
  | badPath (path : String)
  | relative (path : String)
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .nothingHidden => "nothingHidden"
  | .badPath _ => "badPath"
  | .relative _ => "relative"

def plainChar (c : Char) : Bool := c.isAlphanum || c == '/' || c == '.' || c == '_' || c == '-'

/-- A path a unit file holds verbatim: absolute (or `%h/…`, the user's home), plain characters. -/
def checkPath (p : String) : Except Refusal String :=
  let body := if p.startsWith "%h/" then (p.drop 2).toString else p
  if !body.startsWith "/" then .error (.relative p)
  else if body.toList.all plainChar then .ok p
  else .error (.badPath p)

def envMember : String := "ND_MEMBER"
def envGrant : String := "ND_GRANT"

/-- The supervised program's arguments. -/
def Node.args (n : Node) : List Arg :=
  match n.role with
  | .serve => [.lit "serve", .lit n.store]
  | .follow => [.lit "follow", .lit n.store, .var envMember, .var envGrant]

/-- A unit, before it is text: the command line and the restart policy. -/
structure Service where
  node : Node
  /-- argv, `nd-supervise` first -/
  exec : List Arg
  /-- the codes the service manager must not restart -/
  prevent : List Nat

def supervisor (n : Node) : String := n.bin ++ "/nd-supervise"
def hostExe (n : Node) : String := n.bin ++ "/host"

/-- nd-supervise's grammar applied to the node: socket, `--write STORE`, `--exec HOST` (the
program must lie under a read or exec entry, CLIENT's `ProgramOutside`; without it every unit
exits 64 refusedAtLaunch, found by running the rendered argv on hbox), every `--hide`, `--`, the
host program and its arguments. -/
def Node.exec (n : Node) : List Arg :=
  [.lit (supervisor n), .lit n.socket, .lit "--write", .lit n.store, .lit "--exec", .lit (hostExe n)] ++
  n.hide.flatMap (fun h => [.lit "--hide", .lit h]) ++ [.lit "--", .lit (hostExe n)] ++ n.args

/-- Every path checks, or the first that does not. -/
def checkAll : List String → Except Refusal _root_.Unit
  | [] => .ok ()
  | p :: ps => match checkPath p with
    | .error e => .error e
    | .ok _ => checkAll ps

/-- The codes no unit restarts: the Host's fatal class, then the supervisor's own fatal exits
(nd-supervise passes the child's code through, so both live in one code space;
`SupervisorExit.code_disjoint_host` keeps them apart). -/
def preventCodes : List Nat := Status.codesOf .fatal ++ SupervisorExit.codesOf .fatal

def Service.ofNode (n : Node) : Except Refusal Service :=
  if n.hide.isEmpty then .error .nothingHidden else
  match checkAll ([n.bin, n.store, n.socket, n.envDir] ++ n.hide) with
  | .error e => .error e
  | .ok _ => .ok { node := n, exec := n.exec, prevent := preventCodes }

def Arg.systemd : Arg → String
  | .lit s => s
  | .var v => "${" ++ v ++ "}"

def spaced (xs : List String) : String := " ".intercalate xs

/-- Seconds between restarts (both managers), and systemd's stop timeout. -/
def restartSeconds : Nat := 2
def stopSeconds : Nat := 10

/-- systemd's start limit: more than `startBurst` starts inside `startIntervalSeconds` and the unit
fails instead of restarting. Without it a deterministic crash of a restart class (a child killed
by a signal on every start, `uncertain` on every open) loops every `restartSeconds` forever:
systemd's default (5 starts in 10 s) never trips at a 2 s restart. -/
def startIntervalSeconds : Nat := 120
def startBurst : Nat := 5

def Service.systemd (u : Service) : String :=
  let n := u.node
  let env := match n.role with
    | .serve => []
    | .follow => [s!"EnvironmentFile={n.envDir}/{n.name}.env"]
  let user := match n.user with
    | some us => [s!"User={us}"]
    | none => []
  let wanted := if n.user.isSome then "multi-user.target" else "default.target"
  "\n".intercalate ([
    "# GENERATED by emit-units from Ops/Units.lean, Host/Exit.lean and Protocol/Exit.lean — do not edit",
    "[Unit]",
    s!"Description=nanodregg host {match n.role with | .serve => "serve" | .follow => "follow"} under nd-supervise",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple"] ++ user ++ env ++ [
    s!"ExecStart={spaced (u.exec.map Arg.systemd)}",
    "Restart=on-failure",
    s!"RestartSec={restartSeconds}",
    s!"RestartPreventExitStatus={spaced (u.prevent.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    s!"TimeoutStopSec={stopSeconds}",
    "",
    "[Install]",
    s!"WantedBy={wanted}",
    ""])

def xml (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | '\'' => "&apos;"
    | c => c.toString) ""

/-- A launchd plist for `label`, with `%h` resolved to `home` (launchd expands nothing) and the
member's ids given literally (launchd has no environment file). -/
def Service.launchd (u : Service) (label home member grant : String) : String :=
  let res := fun (s : String) => if s.startsWith "%h/" then home ++ (s.drop 2).toString else s
  let arg := fun (a : Arg) => match a with
    | .lit s => res s
    | .var v => if v == envMember then member else grant
  let strings := u.exec.map fun a => s!"    <string>{xml (arg a)}</string>"
  "\n".intercalate ([
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
    "<!-- GENERATED by emit-units from Ops/Units.lean, Host/Exit.lean and Protocol/Exit.lean — do not edit -->",
    "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">",
    "<plist version=\"1.0\">",
    "<dict>",
    s!"  <key>Label</key><string>{xml label}</string>",
    "  <key>ProgramArguments</key>",
    "  <array>"] ++ strings ++ [
    "  </array>",
    "  <key>KeepAlive</key><dict><key>SuccessfulExit</key><false/></dict>",
    s!"  <key>ThrottleInterval</key><integer>{restartSeconds}</integer>",
    "  <key>Umask</key><integer>63</integer>",
    s!"  <key>StandardErrorPath</key><string>{xml (res ("%h/.nd/" ++ u.node.name ++ ".log"))}</string>",
    "</dict>",
    "</plist>",
    ""])

/-! ## The operator's exit table (deploy/units/EXITS.md) -/

/-- What the operator does when `host` ends with this status. Exhaustive: HOST adds a status, OPS
says what an operator does about it, or nothing builds. -/
def hostAction : Status → String
  | .eof => "nothing: the supervisor closed the stream"
  | .uncertain => "automatic; replies were `uncertain`, clients look their calls up"
  | .fuel => "never an exit: a fuel round reopens in process (D4); seen from outside, a defect: report to HOST"
  | .sealIo => "automatic; check the disk's space and errors"
  | .usage => "fix the unit's argv"
  | .entropy => "the OS random source failed: do not genesis on this box"
  | .recordTooLarge | .worldTooLarge | .indexTooLarge =>
    "a defect or the HOST-14 design limit: report to HOST"
  | .io => "a Store file is missing or unreadable: check the path and permissions (the call and errno are on stderr)"
  | .ioServing => "automatic; an IO error after the open: check the disk"
  | .locked => "another writer holds the Store: find its unit; never start a second"
  | .exists => "genesis into an existing Store: choose another path"
  | .badKey => "`STORE/key` is not 32 bytes: restore it from the backup"
  | .shortRead => "a file changed under the open: stop every writer, then `host check`"
  | .noBase | .baseTooLarge | .baseCorrupt | .baseUndecodable | .segmentShort | .tailTooLong =>
    "the Store is damaged or not a Store: restore (RUNBOOK §5)"
  | .foreignSegment => "`seg.log` is another Store's (or a pre-HOST-18 Store's): restore the three files together (RUNBOOK §5)"
  | .corrupt => "bad bytes with a verifying frame after them (at offset 0: the origin frame), or corrupt history before the base: restore (RUNBOOK §5)"
  | .record => "a record does not fold: a defect, report to HOST and KERNEL"
  | .indexShort => "index.log is shorter than the prefix the base names (a copy cut short, or the file truncated): restore index.log from this Store's own backup taken after its base.world; never restart it"
  | .indexCorrupt => "index.log's pages up to the base's indexOffset do not verify under this Store's key or do not end at the tag the base names: restore index.log from this Store's own backup; never restart it"
  | .tagWidth => "a broken sealer: a defect, report to HOST"
  | .behindAnchor => "the copy is truncated or rolled back: use a newer copy"
  | .chainMismatch => "the copy is another history: do not serve it"
  | .badIndex | .pageTooLarge | .pastEnd => "a page fault: report to HOST"
  | .shortBase => "the base changed under a read: run `host check`; if it repeats, report to HOST"
  | .reopenFailed => "the in-process reopen after a fuel round refused: run `host check STORE`; restore if it refuses"
  | .reopenDiverged => "a defect in open or append: keep the Store untouched, report to HOST"
  | .lifetime => "automatic: the restart budget is spent (not reached before the reader's own lifetime)"
  | .stream => "automatic: the request pipe broke; the restart re-pairs it with nd-supervise"
  | .noThreads => "the runtime ran a dedicated task inline: a build or platform defect, report to HOST"
  | .shapeMismatch => "the base was written under other codec shapes: re-genesis from a checked export (RUNBOOK §6)"
  | .foreignOrigin => "the segment's origin frame verifies under this Store's key but names another World (two Stores share a key file, one's seg.log spliced over the other's): restore seg.log from this Store's own backup; never restart it"

def supervisorName : SupervisorExit → String
  | .refusedAtLaunch => "refusedAtLaunch"
  | .childUnroutable => "childUnroutable"
  | .childSignaled => "childSignaled"

/-- What the operator does when nd-supervise ends on its own account. -/
def supervisorAction : SupervisorExit → String
  | .refusedAtLaunch => "refused before the child ran (nothing hidden, an unreadable argument, a socket it cannot bind, the sandbox's policy or mechanism): fix the unit or the box; the reason is on stderr"
  | .childUnroutable => "the child wrote a frame the mux cannot route: a defect in the child, report to HOST and CLIENT"
  | .childSignaled => "automatic; the child was killed by a signal (the OOM killer, an operator; on Linux any mechanism exit of 128 or more, bwrap's 128+N); a crash on every start stops at the start limit"

def classWord : ExitClass → String
  | .done => "done"
  | .restart => "restart"
  | .fatal => "fatal"

/-- What systemd does with the class, under the rendered unit. -/
def classSystemd : ExitClass → String
  | .done => "stays stopped (success)"
  | .restart => s!"restarted after {restartSeconds} s; failed past {startBurst} starts in {startIntervalSeconds} s"
  | .fatal => "stopped (RestartPreventExitStatus)"

def exitRow (code : Nat) (name : String) (k : ExitClass) (action : String) : String :=
  s!"| {code} | {name} | {classWord k} | {classSystemd k} | {action} |"

def exitsTable : String :=
  let host := (Status.all.map fun s => (s.code, exitRow s.code s.name s.cls (hostAction s))).mergeSort
    fun a b => decide (a.1 ≤ b.1)
  let sup := SupervisorExit.all.map fun e => exitRow e.code (supervisorName e) e.cls (supervisorAction e)
  "
".intercalate ([
    "<!-- GENERATED by emit-units from Ops/Units.lean, Host/Exit.lean and Protocol/Exit.lean — do not edit -->",
    "# Exit codes of a nanodregg unit",
    "",
    "A unit runs `nd-supervise … -- host …`. nd-supervise passes the child's code through, so one",
    "code space holds both tables: `host` (Host.Status, below 64) and nd-supervise's own",
    "(Protocol.SupervisorExit, 64 and up). `host` prints `refused NAME` or `exit NAME` on stderr.",
    "",
    "## host",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ host.map (·.2) ++ [
    "",
    "## nd-supervise",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ sup ++ [""])

/-! ## The emitted units (deploy/units/) -/

/-- The writer's node: a system unit, user `nd`. -/
def writer : Node :=
  { name := "nd-host-serve", role := .serve, bin := "/opt/nd/bin", store := "/srv/nd/store",
    socket := "/run/nd/host.sock", hide := ["/srv/nd/ws", "/home"], user := some "nd" }

/-- A member machine: a user unit, the member's own follow Store, its workspace hidden. -/
def member : Node :=
  { name := "nd-host-follow", role := .follow, bin := "/opt/nd/bin", store := "%h/.nd/follow-store",
    socket := "%h/.nd/ws/follow.sock", hide := ["%h/.nd/ws", "%h/.nd/holding"], user := none }

def emitted : List (String × Node) :=
  [("linux/nd-host-serve.service", writer), ("linux/nd-host-follow.service", member)]

def files : Except Refusal (List (String × String)) := do
  let units ← emitted.mapM fun (path, n) => do return (path, (← Service.ofNode n).systemd)
  return units ++ [("EXITS.md", exitsTable)]

/-- The live harness's nodes (deploy/live/): user units whose every path lies under `root`, so the
harness writes nothing outside it but the unit links. Two writers on ONE Store (the second must
stop `locked`, never restart), a follower, and a writer the harness gives a file-size limit (an
append that fails). Rendered by the same `Service.ofNode`/`systemd`
as the deployed units, so the harness judges the renderer, not a copy of it. -/
def liveNodes (root : String) : List Node :=
  let base : Node :=
    { name := "nd-ops-live-serve", role := .serve, bin := root ++ "/bin", store := root ++ "/store",
      socket := root ++ "/ws/serve.sock", hide := [root ++ "/ws"], user := none, envDir := root ++ "/env" }
  [base,
   { base with name := "nd-ops-live-serve2", socket := root ++ "/ws/serve2.sock" },
   { base with name := "nd-ops-live-follow", role := .follow, store := root ++ "/follow-store",
               socket := root ++ "/ws/follow.sock" },
   -- the harness adds `LimitFSIZE=` to this one (fault injection, deploy/live/harness.sh)
   { base with name := "nd-ops-live-fsize", store := root ++ "/fsize-store", socket := root ++ "/ws/fsize.sock" }]

def liveFiles (root : String) : Except Refusal (List (String × String)) :=
  (liveNodes root).mapM fun n => do return (n.name ++ ".service", (← Service.ofNode n).systemd)

/-- `emit-units DIR` writes; `emit-units --check DIR` refuses a file that differs. -/
def run : List String → IO UInt32
  | args => do
    match files with
    | .error r => IO.eprintln s!"emit-units: refused {r.name}"; return 2
    | .ok fs =>
      match args with
      | [dir] =>
        for (p, t) in fs do
          IO.FS.createDirAll ((System.FilePath.mk dir / p).parent.getD dir)
          IO.FS.writeFile (System.FilePath.mk dir / p) t
        return 0
      | ["--live", root, dir] =>
        match liveFiles root with
        | .error r => IO.eprintln s!"emit-units: refused {r.name}"; return 2
        | .ok ls =>
          IO.FS.createDirAll dir
          for (p, t) in ls do IO.FS.writeFile (System.FilePath.mk dir / p) t
          return 0
      | ["--check", dir] =>
        let mut bad := 0
        for (p, t) in fs do
          let path := System.FilePath.mk dir / p
          let cur ← if ← path.pathExists then IO.FS.readFile path else pure ""
          unless cur == t do IO.eprintln s!"emit-units: {path} differs from the table; regenerate it"; bad := bad + 1
        return if bad = 0 then 0 else 1
      | _ => IO.eprintln "usage: emit-units [--check] DIR | emit-units --live ROOT DIR"; return 2

end Nanodregg.Ops.Units
