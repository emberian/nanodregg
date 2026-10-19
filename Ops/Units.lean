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
import Host.Base
import Hosting.BrokerExit
import Hosting.Plan
import Hosting.LaunchExit
import Hosting.BrokerWire
import Protocol.Table

namespace Nanodregg.Ops.Units

open Nanodregg.Host
open Nanodregg.Protocol (SupervisorExit CommandExit)
open Nanodregg.Hosting (DeciderExit KeybrokerExit ControllerExit LaunchExit)

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
  /-- systemd's `RuntimeDirectory=` of a system unit: systemd makes `/run/NAME`, owned by `User=`,
  before the start (nothing else makes `/run/nd` on a fresh box) and removes it at stop;
  nd-supervise binds the socket afresh at every start. With it, `socket` is the socket's file
  name in that directory (`Node.sock`), so the socket cannot lie outside it -/
  runtime : Option String := none
  /-- a systemd template (`NAME@.service`, one instance per hosted World): `%i`, the instance, may
  stand in any path; a plain unit's paths never hold `%` (checkPath refuses it) -/
  template : Bool := false
  /-- the socket is shared with ONE group (CLIENT-21's `nd-supervise --group GID`, ROOT's ruling on
  HOSTING-17 §7): bound 0660 in a setgid 02710 directory of that group, the numeric gid from the
  unit's environment file (`ND_GID`) -/
  group : Bool := false
  deriving Repr

inductive Refusal where
  | nothingHidden
  | badPath (path : String)
  | relative (path : String)
  /-- a `RuntimeDirectory` on a user unit: systemd would make it under the user's runtime
  directory, not `/run`, and the socket's directory would not be the one rendered -/
  | runtimeOnUserUnit
  /-- the broker's hosted group is the key holder's user (HOSTING-17: grains would run as the
  uid that reads the provider keys and writes the Store; keybroker cannot tell it from the
  one-uid test, so the render refuses it) -/
  | hostedIsKeyHolder
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .nothingHidden => "nothingHidden"
  | .badPath _ => "badPath"
  | .relative _ => "relative"
  | .runtimeOnUserUnit => "runtimeOnUserUnit"
  | .hostedIsKeyHolder => "hostedIsKeyHolder"

def plainChar (c : Char) : Bool := c.isAlphanum || c == '/' || c == '.' || c == '_' || c == '-'

/-- A path a unit file holds verbatim: absolute (or `%h/…`, the user's home), plain characters;
in a template (`inst`), also systemd's instance specifier `%i`. -/
def checkPath (p : String) (inst : Bool := false) : Except Refusal String :=
  let body := if p.startsWith "%h/" then (p.drop 2).toString else p
  let body := if inst then body.replace "%i" "i" else body
  if !body.startsWith "/" then .error (.relative p)
  else if body.toList.all plainChar then .ok p
  else .error (.badPath p)

/-- The socket's path: in `/run/NAME/` under a runtime directory, else `socket` itself. -/
def Node.sock (n : Node) : String :=
  match n.runtime with
  | some r => "/run/" ++ r ++ "/" ++ n.socket
  | none => n.socket

def envMember : String := "ND_MEMBER"
def envGrant : String := "ND_GRANT"
/-- the numeric gid a shared socket's group has (`getent group nd`): operator data, as ND_PEER is -/
def envGid : String := "ND_GID"

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
  [.lit (supervisor n), .lit n.sock, .lit "--write", .lit n.store, .lit "--exec", .lit (hostExe n)] ++
  (if n.group then [.lit "--group", .var envGid] else []) ++
  n.hide.flatMap (fun h => [.lit "--hide", .lit h]) ++ [.lit "--", .lit (hostExe n)] ++ n.args

/-- Every path checks, or the first that does not. -/
def checkAll (ps : List String) (inst : Bool := false) : Except Refusal _root_.Unit :=
  match ps with
  | [] => .ok ()
  | p :: ps => match checkPath p inst with
    | .error e => .error e
    | .ok _ => checkAll ps inst

/-- The codes no unit restarts: the Host's fatal class, then the supervisor's own fatal exits
(nd-supervise passes the child's code through, so both live in one code space;
`SupervisorExit.code_disjoint_host` keeps them apart). -/
def preventCodes : List Nat := Status.codesOf .fatal ++ SupervisorExit.codesOf .fatal

/-- Every path of the node, its socket as rendered; under a runtime directory, the directory and
the socket's name are single components (the socket sits directly in `/run/NAME`). -/
def Node.check (n : Node) : Except Refusal _root_.Unit := do
  checkAll ([n.bin, n.store, n.sock, n.envDir] ++ n.hide) n.template
  if let some r := n.runtime then
    if r.isEmpty || r.contains '/' then throw (.badPath r)
    if n.socket.isEmpty || n.socket.contains '/' then throw (.badPath n.socket)

def Service.ofNode (n : Node) : Except Refusal Service :=
  if n.hide.isEmpty then .error .nothingHidden else
  if n.runtime.isSome && n.user.isNone then .error .runtimeOnUserUnit else
  match n.check with
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
    | .follow => [s!"EnvironmentFile={n.envDir}/{if n.template then "%i" else n.name}.env"]
  let user := match n.user with
    | some us => [s!"User={us}"]
    | none => []
  let rt := match n.runtime with
    | some r => [s!"RuntimeDirectory={r}"]
    | none => []
  let wanted := if n.user.isSome then "multi-user.target" else "default.target"
  "\n".intercalate ([
    "# GENERATED by emit-units from Ops/Units.lean, Host/Exit.lean and Protocol/Exit.lean — do not edit",
    "[Unit]",
    s!"Description=nanodregg host {match n.role with | .serve => "serve" | .follow => "follow"}{if n.template then " of World %i" else ""} under nd-supervise",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple"] ++ user ++ rt ++ env ++ [
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
  | .entryUnfit => "a defect: a seal met an index entry the entry layout cannot spell (HOST-31); keep the Store untouched, report to HOST"
  | .allowancePastBound => "genesis/join/import refused before writing: the World's allowance is past this binary's allowanceMax (a forged or foreign lineage, or an invitation made with another budget); do not import it (nothing was written)"
  | .potentialPastBound => "genesis/join/import refused before writing: the World's weight and allowance together (Kernel.potential) are past this binary's potentialMax, the weight bound its budget admits (a carried World heavier than a lineage that began under this budget can become, or a genesis past genesisWeightMax; rebuild the genesis with fewer or lighter founders) (nothing was written)"
  | .positionUnfit => "a defect: a seal at a segment position past u64, which a base cannot spell (HOST-46); nothing was written; keep the Store untouched, report to HOST"
  | .carryMismatch => "the carried file is not the one exported (digest), does not decode, or the imported Store reopened to other bytes (stderr names which): re-export from the STOPPED old Store and copy the printed digest exactly; remove a Store left by `carryMismatch reopen` and report it to HOST"
  | .inviteRefused => "the invitation does not verify against the key you trust (stderr names why): obtain a fresh invitation from your sponsor and check the sponsor key you were given; nothing was written"
  | .indexMoved => "automatic; index.log changed size under the writer (another process wrote or truncated it): the restart's open truncates orphan entries or refuses indexShort; if it repeats, find the other writer"
  | .io => "the STORE path or the IN file is absent, a Store file is unreadable (EACCES, EIO), or a file was removed between the open's check and its open: check the path and permissions (the call and errno are on stderr)"
  | .ioServing => "automatic; an IO error after the open: check the disk"
  | .locked => "another writer holds the Store: find its unit; never start a second"
  | .exists => "genesis into an existing Store: choose another path"
  | .badKey => "`STORE/key` is not 32 bytes: restore it from the backup"
  | .missing => "a Store file (key, seg.log, index.log or base.world; stderr names it) is absent from an existing STORE directory: never re-create it or genesis over it; restore the Store's files together from one backup (RUNBOOK §5); a directory left by a genesis that crashed part way is moved aside by hand, never deleted by a unit; if STORE names a directory that holds no Store at all, check the path"
  | .shortRead => "a file changed under the open: stop every writer, then `host check`"
  | .baseTooLarge | .baseCorrupt | .baseUndecodable | .segmentShort | .tailTooLong =>
    "the Store is damaged or not a Store: restore (RUNBOOK §5)"
  | .foreignSegment => "`seg.log` is another Store's (or a pre-HOST-18 Store's): restore the three files together (RUNBOOK §5)"
  | .corrupt => "bad bytes with a verifying frame after them (at offset 0: the origin frame), or corrupt history before the base: restore (RUNBOOK §5)"
  | .record => "a record does not fold: a defect, report to HOST and KERNEL"
  | .indexShort => "index.log is shorter than the entries the base counts (a copy cut short, or the file truncated): restore index.log from this Store's own backup taken after its base.world; never restart it"
  | .indexCorrupt => "an index.log entry the base counts does not verify under this Store's key at its position (from open: the last one; from `host check`: the entry named on stderr): restore index.log from this Store's own backup; never restart it"
  | .tagWidth => "a broken sealer: a defect, report to HOST"
  | .behindAnchor => "the copy is truncated or rolled back: use a newer copy"
  | .chainMismatch => "the copy is another history: do not serve it"
  | .badIndex => "an index.log entry a page read does not verify at its position (HOST-33); an exit only of `host check --anchor` (a writer answers that page `refused badIndex` and keeps serving): run `host check` on the stopped Store (it names the entry, indexCorrupt), restore index.log from this Store's own backup, and report to HOST"
  | .pageTooLarge | .pastEnd => "a page fault: report to HOST"
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
  | .refusedAtLaunch => "refused before the child ran (nothing hidden, an unreadable argument, a socket it cannot bind, the sandbox's policy or mechanism, a soft open-file limit below what the supervisor may hold): fix the unit or the box; the reason is on stderr. For `RLIMIT_NOFILE N is below the M fds it may hold` (CLIENT-28) raise the unit's LimitNOFILE (or `ulimit -n`) to at least M (73 at CONNECTIONS_MAX 64: its stdio, its socket, the child's two pipes, its SIGTERM pair, one per connection, one being refused `full`)"
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

/-! ## The provider-key broker (HOSTING-12/15/16): keybroker and its decider -/

/-- What the operator does when the decider (`hosting-broker`) ends; keybroker passes its code
through. Exhaustive: HOSTING adds an end, OPS says what an operator does, or nothing builds. -/
def deciderAction : DeciderExit → String
  | .keybrokerGone => "nothing: keybroker closed the decider's pipe (its own end is in keybroker's line)"
  | .usage => "the unit's argv for the decider is wrong: fix the keybroker unit"
  | .badFrame | .badRequest => "a defect in keybroker's framing: report to HOSTING"
  | .unencodable => "unreachable by theorem (step_encodes); seen, a defect: report to HOSTING"
  | .lifetime => "automatic: the decider's lifetime ended, a fresh one continues"
  | .noPackage => "the allowance package has no id: a build defect, report to HOSTING"
  | .store => "the Store the decider follows refused to open: run `host check STORE`; restore if it refuses (RUNBOOK §5)"
  | .behind => "automatic: the decider fell behind the writer's tail; a fresh open reads the World whole"
  | .io => "an IO error escaped the decider (the call and error are on stderr): check the Store's disk and permissions"
  | .residentsPastBound => "the World holds more resident grains than one keybroker serves (1024, HOSTING-26; stderr names the count): remove resident grains, or run a second World"

/-- What the operator does when keybroker ends on its own account. -/
def keybrokerAction : KeybrokerExit → String
  | .usage => "fix the unit's argv"
  | .keyFileLink | .keyFileNotRegular | .keyFileOwner | .keyFileMode | .keyFileLength | .keyFileIo =>
    "the provider key file fails custody: a regular file owned by `nd`, mode 0600 (RUNBOOK §2a)"
  | .keyFileDir => "a directory above the provider key file is writable by another or owned by another user: fix the chain (RUNBOOK §2a, Dir)"
  | .keyFileFormat => "the provider key file is not `SLOT KEY` lines, or repeats a slot: rewrite it"
  | .anchorsLink | .anchorsNotRegular | .anchorsOwner | .anchorsMode | .anchorsLength | .anchorsIo | .anchorsMissing =>
    "the anchors file fails custody or is missing: reinstall deploy/tls/anchors.pem owned by `nd`, mode 0644 (RUNBOOK §2a)"
  | .anchorsDir => "a directory above the anchors file is writable by another or owned by another user: fix the chain (RUNBOOK §2a, Dir)"
  | .anchorsMalformed => "the anchors file is not certificates only: reinstall deploy/tls/anchors.pem (the unit's ExecStartPre checks the installed copy)"
  | .pinsLink | .pinsNotRegular | .pinsOwner | .pinsMode | .pinsLength | .pinsIo =>
    "the pins file fails custody: install deploy/tls/pins (or the operator's computed pins) owned by `nd`, mode 0644 (RUNBOOK §2a)"
  | .pinsMissing =>
    "the pins file is missing: the unit stops and is not restarted (fatal, in RestartPreventExitStatus); install deploy/tls/pins (or the operator's computed pins) owned by `nd`, mode 0644 (RUNBOOK §2a), then start the unit"
  | .pinsDir => "a directory above the pins file is writable by another or owned by another user: fix the chain (RUNBOOK §2a, Dir)"
  | .pinsMalformed => "the pins file is not `HOST SHA256-HEX` lines (64 lowercase hex digits, each line ended by LF) or repeats a pin: rewrite it by the RUNBOOK's recipe"
  | .tlsConfig => "rustls refused the client configuration: a build defect, report to HOSTING"
  | .socket => "a resident socket could not be bound (a stale socket, a missing directory): stop the unit, check the runtime directory, start it"
  | .sockDir => "the broker's socket directory fails its checks: /run/nd-broker must be nd:nd-hosted mode 02710 (tmpfiles), every directory above it owned by root, and each resident directory in it nd's, mode 02710 (HOSTING-17, RUNBOOK §2a)"
  | .deciderRefused => "the sandbox refused the decider's policy or could not spawn it: check the mechanism (deploy/live/README.md) and the DECIDER path"
  | .pidFile => "the decider's PID file could not be written: check the runtime directory"
  | .deciderSignaled => "automatic; the decider was killed by a signal (OOM, an operator); a crash on every start stops at the start limit"
  | .deciderLost => "keybroker could not read its decider's end: nothing says a restart is safe; read the journal, then start the unit"
  | .deciderMechanism => "the decider's sandbox or program failed before the decider ran (stderr names the raw code: bwrap, a missing library, the unit's RestrictAddressFamilies — it needs AF_NETLINK): fix the mechanism (deploy/live/README.md), then start the unit"

/-- The codes the keybroker unit must not restart: both broker tables' fatal classes. -/
def brokerPreventCodes : List Nat := DeciderExit.codesOf .fatal ++ KeybrokerExit.codesOf .fatal

/-- The keybroker unit's operator data: paths through `checkPath`, the rest literal or from the
unit's environment file (`ND_OPERATOR`, `ND_PEER`: the `nd-hosted` uid, HOSTING-17). Which residents it
serves is the World's, never the operator's (HOSTING-26). -/
structure Broker where
  name : String
  bin : String
  /-- the directory holding the provider key, the anchors and the environment file (RUNBOOK §2a) -/
  etc : String
  /-- systemd's `RuntimeDirectory=` name: `/run/NAME` holds the PID file -/
  runtime : String
  /-- SOCKDIR (HOSTING-17): the operator's (tmpfiles, nd:nd-hosted 02710), outliving the unit, so a
  restarted broker stays reachable to running residents -/
  sockdir : String
  upstream : String
  store : String
  user : String
  /-- the hosted system user and its primary group (HOSTING-17): SOCKDIR's group, the only group
  served, never the key holder's -/
  hosted : String
  /-- `none`: the deployed SYSTEM unit (`User=`, PIDS = `/run/runtime`, systemd's RuntimeDirectory);
  `some DIR`: a USER unit of the live harness (deploy/live), PIDS = DIR, no `User=` and no
  RuntimeDirectory (a user manager would put it under the user's runtime directory) -/
  pidsDir : Option String := none
  deriving Repr

/-- keybroker's PIDS argument. -/
def Broker.pids (b : Broker) : String := b.pidsDir.getD ("/run/" ++ b.runtime)

def keybroker : Broker :=
  { name := "nd-keybroker", bin := "/opt/nd/bin", etc := "/etc/nd/keybroker", runtime := "nd-keybroker",
    sockdir := "/run/nd-broker", upstream := "api.anthropic.com:443", store := "/srv/nd/store", user := "nd",
    hosted := "nd-hosted" }

/-- A host:port with nothing a unit file would re-quote. -/
def plainAddr (a : String) : Bool :=
  !a.isEmpty && a.toList.all fun c => c.isAlphanum || c == '.' || c == '-' || c == ':'

def Broker.check (b : Broker) : Except Refusal _root_.Unit := do
  if b.hosted == b.user then throw .hostedIsKeyHolder
  checkAll [b.bin, b.etc, b.store, b.pids, b.sockdir]
  unless plainAddr b.upstream do throw (.badPath b.upstream)
  unless b.runtime.toList.all plainChar && !b.runtime.contains '/' do throw (.badPath b.runtime)
  unless !b.user.isEmpty && b.user.toList.all plainChar && !b.user.contains '/' do throw (.badPath b.user)
  unless !b.hosted.isEmpty && b.hosted.toList.all plainChar && !b.hosted.contains '/' do throw (.badPath b.hosted)

/-- SOCKDIR's `tmpfiles.d` line (HOSTING-17 §2): made at boot, outliving the unit (a restarted
broker stays reachable inside running sandboxes), owner the key holder, group the hosted user's,
mode 02710 (the broker writes; the group may only traverse; every inode made inside inherits the
group by the setgid bit). keybroker refuses `sockDir` (105) at start for any other shape. -/
def sockdirMode : String := "2710"

def Broker.tmpfiles (b : Broker) : Except Refusal String := do
  b.check
  return "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.keybroker) — do not edit",
    "# install as /etc/tmpfiles.d/nd-broker.conf (RUNBOOK §2a)",
    s!"d {b.sockdir} {sockdirMode} {b.user} {b.hosted} -",
    ""]

/-- The node's system users (`sysusers.d`): the key holder, who runs `host serve` and keybroker,
and the hosted user, who runs grain-launch, the controller and every grain; each with its own
primary group and no membership in the other's, so a sandbox escape is the hosted uid and reads
no provider key and writes no Store (HOSTING-17 §1). -/
def Broker.sysusers (b : Broker) : Except Refusal String := do
  b.check
  return "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.keybroker) — do not edit",
    "# install as /etc/sysusers.d/nd.conf, then `systemd-sysusers` (RUNBOOK §2a); no `m` line: neither user is in the other's group",
    s!"u {b.user} - \"nanodregg writer and provider-key broker\" - -",
    s!"u {b.hosted} - \"nanodregg hosted grains (never the key holder)\" - -",
    ""]

/-- keybroker's argv, in its order: KEYS ANCHORS PINS SOCKDIR PIDS UPSTREAM STORE OPERATOR PEER DECIDER.
PINS (HOSTING-28) is the operator's: a provider's key rotation rewrites it with no rebuild, so no
ExecStartPre compares it with the build's `deploy/tls/pins` (as one does the anchors). -/
def Broker.exec (b : Broker) : List Arg :=
  [.lit (b.bin ++ "/keybroker"), .lit (b.etc ++ "/provider.key"), .lit (b.etc ++ "/anchors.pem"),
   .lit (b.etc ++ "/pins"),
   .lit b.sockdir, .lit b.pids, .lit b.upstream, .lit b.store,
   .var "ND_OPERATOR", .var "ND_PEER", .lit (b.bin ++ "/hosting-broker")]

def Broker.systemd (b : Broker) : Except Refusal String := do
  b.check
  return "\n".intercalate ([
    "# GENERATED by emit-units from Ops/Units.lean and Hosting/BrokerExit.lean — do not edit",
    "[Unit]",
    "Description=nanodregg keybroker (the provider-key broker) and its decider",
    "Wants=network-online.target",
    "After=network-online.target",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple"] ++ (if b.pidsDir.isNone then [s!"User={b.user}"] else []) ++ [
    s!"EnvironmentFile={b.etc}/keybroker.env"] ++
    (if b.pidsDir.isNone then [s!"RuntimeDirectory={b.runtime}"] else []) ++ [
    "# the installed anchors must be the build's pinned roots, byte for byte, at every start (OPS-7)",
    s!"ExecStartPre={b.bin}/emit-anchors --check {b.etc}/anchors.pem",
    s!"ExecStart={spaced (b.exec.map Arg.systemd)}",
    "Restart=on-failure",
    s!"RestartSec={restartSeconds}",
    s!"RestartPreventExitStatus={spaced (brokerPreventCodes.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    "# AF_NETLINK: bwrap --unshare-net brings up the decider sandbox loopback over NETLINK_ROUTE; without it",
    "# the decider dies at every start (measured on burst5, systemd 255, OPS-3 run 1)",
    "RestrictAddressFamilies=AF_UNIX AF_INET AF_INET6 AF_NETLINK",
    s!"TimeoutStopSec={stopSeconds}",
    "",
    "[Install]",
    s!"WantedBy={if b.pidsDir.isNone then "multi-user.target" else "default.target"}",
    ""])

/-! ## The emitted units (deploy/units/) -/

/-- The writer's node: a system unit, user `nd`. -/
def writer : Node :=
  { name := "nd-host-serve", role := .serve, bin := "/opt/nd/bin", store := "/srv/nd/store",
    socket := "host.sock", hide := ["/srv/nd/ws", "/home"], user := some "nd", runtime := some "nd" }

/-- A member machine: a user unit, the member's own follow Store, its workspace hidden. -/
def member : Node :=
  { name := "nd-host-follow", role := .follow, bin := "/opt/nd/bin", store := "%h/.nd/follow-store",
    socket := "%h/.nd/ws/follow.sock", hide := ["%h/.nd/ws", "%h/.nd/holding"], user := none }

/-- The hosted follower (HOSTING-17 §7, ROOT's ruling): one per hosted World `%i`, as `nd-hosted`,
writing the follow Store the controller tails (`grain-launch` reads `ROOT/worlds/LABEL/store`).
Its socket is shared with group `nd` in the setgid `/run/nd-follow` (tmpfiles), so `nd`, the
trusted side, drives it (client `nd`, relaying to host.sock, which stays nd-only). It sees no
key directory and no home. -/
def hostedFollower : Node :=
  { name := "nd-hosted-follow", role := .follow, bin := "/opt/nd/bin",
    store := "/srv/nd-hosted/worlds/%i/store", socket := "/run/nd-follow/%i.sock",
    hide := ["/etc/nd", "/home"], user := some "nd-hosted", envDir := "/etc/nd/hosted",
    template := true, group := true }

/-- The follower sockets' directory: owned by the hosted user, group the writer's user, 02710
(CLIENT-21 refuses any other shape at launch, `sharedDirRefused` / `groupMismatch`). -/
def followDir : String := "/run/nd-follow"

/-- The member root (HOSTING-20, HOSTING-25): `/run/nd-member/<dirOf id>/nd.sock` is a resident's
member socket, served by nd-supervise as the key holder's user (nd) and reached by the hosted group:
the SOCKDIR idiom, owner nd, group nd-hosted, 02710 (CLIENT-21's `check_shared_dir` refuses any other
shape). Each resident's own directory in it is made with the member socket's unit. -/
def memberDir : String := Nanodregg.Hosting.memberRoot.text

def memberTmpfiles : String :=
  "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.memberDir) — do not edit",
    "# install as /etc/tmpfiles.d/nd-member.conf (RUNBOOK §2b)",
    s!"d {memberDir} {sockdirMode} {writer.user.getD ""} {hostedFollower.user.getD ""} -",
    ""]

def followTmpfiles : String :=
  "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.hostedFollower) — do not edit",
    "# install as /etc/tmpfiles.d/nd-follow.conf (RUNBOOK §2b)",
    s!"d {followDir} {sockdirMode} {hostedFollower.user.getD ""} {writer.user.getD ""} -",
    ""]

/-! ## The per-World member server (HOSTING-30, CLIENT-29): one nd-members per World -/

open Nanodregg.Hosting (MembersExit)

/-- What the operator does when nd-members ends on its own account (a resident's own trouble is never
an end: a name in the journal, `memberMissing` / `socketDirShared` / `memberCrashLoop` / `memberSpawn` / `memberStopping` /
`memberStopForced`,
and that resident unbound while the others are served). Exhaustive. -/
def membersAction : MembersExit → String
  | .usage => "the unit's argv does not parse: compare ExecStart with this unit's rendered argv"
  | .memberRoot => "MEMBER (/run/nd-member) is not nd's 02710 directory with a StrictModes-clean chain (fix the tmpfiles line, RUNBOOK §2b), or the decider answered a name that is not a grain directory name (a defect: report to HOSTING)"
  | .membersRoot => "MEMBERS (/srv/nd-members/L/members) is not a 0700 nd directory with a clean chain (RUNBOOK §2b)"
  | .followRoot => "FOLLOW (/run/nd-member-follow) is not a 0700 nd directory with a clean chain: fix the tmpfiles line (RUNBOOK §2b)"
  | .fdLimit => "RLIMIT_NOFILE is below the fds each resident's nd-supervise may hold (73 at CONNECTIONS_MAX 64): set the unit's LimitNOFILE to at least the M in the stderr line"
  | .deciderRefused => "the sandbox refused the decider's policy, or it could not be spawned: check the mechanism (deploy/live/README.md) and the decider path"
  | .pidFile => "a PID file in PIDS could not be written: check the unit's RuntimeDirectory"
  | .deciderSignaled => "automatic; the decider was killed by a signal; a crash on every start stops at the start limit"
  | .deciderLost => "the decider stopped answering `residents` and did not end: read its stderr in the journal, then start the unit by hand"
  | .deciderMechanism => "the decider's process ended with a code DeciderExit does not name (bwrap setup, a missing program or library, the unit's RestrictAddressFamilies): a restart meets the same thing; fix the mechanism"
  | .stateRoot => "STATE (/srv/nd-members/L/follow) is not a 0700 nd directory with a clean chain (RUNBOOK §2b)"
  | .rootsOverlap => "two of nd-members' roots nest: MEMBER, MEMBERS, STATE and FOLLOW must be pairwise disjoint trees (HOSTING-32); fix the unit's argv"

/-- The codes nd-members must not restart: the decider's fatal class and its own (only a signalled
decider restarts). -/
def membersPreventCodes : List Nat := DeciderExit.codesOf .fatal ++ MembersExit.codesOf .fatal

/-- The follower sockets' root (one directory per resident, each alone in it: CLIENT-20): nd's, 0700,
`FOLLOW/<dirOf>/follow.sock`; short, for sun_path. -/
def memberFollowDir : String := Nanodregg.Hosting.followSockRoot.text

/-- nd's own root for every World's resident members (HOSTING-32, `Hosting.membersHome`): nd 0700.
Each `/srv/nd-members/<L>` (nd 0700) and its `members` and `follow` are made at provisioning
(RUNBOOK §2b): one tmpfiles line per label cannot be a template. -/
def membersHomeDir : String := Nanodregg.Hosting.membersHome.text

def membersHomeTmpfiles : String :=
  "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.membersHomeDir) — do not edit",
    "# install as /etc/tmpfiles.d/nd-members.conf (RUNBOOK §2b)",
    s!"d {membersHomeDir} 0700 {writer.user.getD ""} {writer.user.getD ""} -",
    ""]

def memberFollowTmpfiles : String :=
  "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.memberFollowDir) — do not edit",
    "# install as /etc/tmpfiles.d/nd-member-follow.conf (RUNBOOK §2b)",
    s!"d {memberFollowDir} 0700 {writer.user.getD ""} {writer.user.getD ""} -",
    ""]

/-- The unit that serves every resident grain's member socket of one World `%i` (HOSTING-30): as nd, one
process asking its decider which resident grains the World holds, and per provisioned resident two
nd-supervise children (its own follower, its `nd --stdio`). The box's own value `ND_PEER` comes from
keybroker's environment file (the same value; there is no per-resident file, the member is provisioned
under MEMBERS and STATE, RUNBOOK §2b). The decider is `hosting-residents STORE` (HOSTING-33): it
answers only `residents`, so it takes no clock, no key slots and no operator
(`membersUnit_decider_store`, Ops/Proofs/Units.lean). -/
structure Members where
  name : String
  bin : String
  /-- MEMBER: the member root (`memberDir`) -/
  member : String
  /-- MEMBERS: `%i`'s provisioned member workspaces (`Hosting.membersRoot`); nd's 0700 -/
  members : String
  /-- STATE: `%i`'s follower Stores and `follow` files (`Hosting.stateRoot`); nd's 0700 -/
  state : String
  /-- FOLLOW: the follower sockets' root (`Hosting.followSockRoot`) -/
  follow : String
  /-- `/run/NAME` holds the decider's PID file and each child's -/
  runtime : String
  hostSock : String
  store : String
  hide : List String
  user : String
  /-- keybroker's environment file: ND_OPERATOR and ND_PEER -/
  envFile : String
  decider : String
  deciderArgs : List Arg

def membersUnit : Members :=
  { name := "nd-members", bin := "/opt/nd/bin", member := memberDir,
    members := (Nanodregg.Hosting.membersRoot (Nanodregg.Hosting.lit "%i")).text,
    state := (Nanodregg.Hosting.stateRoot (Nanodregg.Hosting.lit "%i")).text, follow := memberFollowDir,
    runtime := "nd-members-%i", hostSock := "/run/nd/host.sock", store := "/srv/nd/store",
    hide := ["/etc/nd", "/home"], user := "nd", envFile := "/etc/nd/keybroker/keybroker.env",
    decider := "/opt/nd/bin/hosting-residents",
    deciderArgs := [.lit "/srv/nd/store"] }


def Members.pids (m : Members) : String := "/run/" ++ m.runtime

def Members.check (m : Members) : Except Refusal _root_.Unit := do
  if m.hide.isEmpty then throw .nothingHidden
  checkAll ([m.bin, m.member, m.members, m.state, m.follow, m.pids, m.hostSock, m.store, m.envFile, m.decider] ++ m.hide) true

/-- nd-members' argv, in its order: MEMBER MEMBERS STATE FOLLOW PIDS HOST_SOCK PEER SUPERVISE ND HOST STORE,
the `--hide`s, `--`, the decider and its arguments (the parser refuses any other order, `usage` 150). -/
def Members.exec (m : Members) : List Arg :=
  [.lit (m.bin ++ "/nd-members"), .lit m.member, .lit m.members, .lit m.state, .lit m.follow, .lit m.pids, .lit m.hostSock,
   .var "ND_PEER", .lit (m.bin ++ "/nd-supervise"), .lit (m.bin ++ "/nd"), .lit (m.bin ++ "/host"), .lit m.store] ++
  m.hide.flatMap (fun h => [.lit "--hide", .lit h]) ++ [.lit "--", .lit m.decider] ++ m.deciderArgs

/-- TasksMax: nd-members covers 2 + 4 * RESIDENTS_MAX processes (two nd-supervise and their two children
per resident), plus each nd-supervise's threads (2 + 2 * connectionsMax). -/
def tasksMax : Nat :=
  2 + 4 * Nanodregg.Hosting.Broker.Bounds.residentsMax + 2 * Nanodregg.Hosting.Broker.Bounds.residentsMax * (2 + 2 * Nanodregg.Protocol.Bounds.connectionsMax)

def Members.systemd (m : Members) : Except Refusal String := do
  m.check
  return "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean and Hosting/BrokerExit.lean — do not edit",
    "[Unit]",
    "Description=nanodregg resident member sockets of World %i (nd-members)",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple",
    s!"User={m.user}",
    s!"EnvironmentFile={m.envFile}",
    s!"RuntimeDirectory={m.runtime}",
    "# TasksMax and RestrictAddressFamilies are unmeasured until a box window",
    s!"TasksMax={tasksMax}",
    s!"ExecStart={spaced (m.exec.map Arg.systemd)}",
    "Restart=on-failure",
    s!"RestartSec={restartSeconds}",
    s!"RestartPreventExitStatus={spaced (membersPreventCodes.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    "# AF_NETLINK: the decider's and the children's bwrap bring a sandbox loopback up over NETLINK_ROUTE",
    "RestrictAddressFamilies=AF_UNIX AF_NETLINK",
    s!"TimeoutStopSec={stopSeconds}",
    "",
    "[Install]",
    "WantedBy=multi-user.target",
    ""]

def unitFile (n : Node) : String :=
  s!"linux/{n.name}{if n.template then "@" else ""}.service"

/-! ## The grain launcher (HOSTING-10/17/19): grain-launch and its controller, per hosted World -/

/-- What the operator does when the controller (`hosting-controller`) ends; grain-launch passes its
code through. Exhaustive: HOSTING adds an end, OPS says what an operator does, or nothing builds. -/
def controllerAction : ControllerExit → String
  | .launcherGone => "nothing: grain-launch closed the controller's pipe (its own end is in grain-launch's line)"
  | .usage => "the unit's argv for the controller is wrong: fix the grain-launch unit"
  | .badLabel => "the World's label is refused for every grain (the unit's instance name): rename the instance to the World's label"
  | .noPackage => "the lifecycle package has no id: a build defect, report to HOSTING"
  | .store => "the follow Store the controller tails refused to open: run `host check /srv/nd-hosted/worlds/LABEL/store` as nd-hosted; restore or re-follow it (RUNBOOK §2b, §5)"
  | .torn | .badLength | .badReport => "a defect in grain-launch's report framing: report to HOSTING"
  | .unencodable => "unreachable by theorem (the controller's plans encode); seen, a defect: report to HOSTING"
  | .lifetime => "automatic: the controller's lifetime ended, a fresh one re-reads the World whole"
  | .io => "an IO error escaped the controller (stderr names the call and error): check the follow Store's disk and permissions"

/-- What the operator does when grain-launch ends on its own account. -/
def launchAction : LaunchExit → String
  | .usage => "the unit's argv is wrong or a root does not exist: fix the unit; make /srv/nd-hosted (RUNBOOK §2b)"
  | .rootsOverlap => "two of grain-launch's roots nest (HOSTING-17 §8, HOSTING-25): /srv/nd-hosted, /run/nd-broker and /run/nd-member must be pairwise disjoint trees"
  | .controllerRefused => "the sandbox refused the controller's policy or could not spawn it: check the mechanism (deploy/live/README.md) and the controller path"
  | .frame | .badAction | .badGrain | .duplicateLaunch | .foreignPath => "a defect in the controller's actions: keep the World's state, report to HOSTING"
  | .reportPipe => "automatic: the controller's pipe failed, a fresh launcher and controller start over (every grain was killed and reaped)"
  | .pidFile => "a grain's PID file could not be written: check /run/nd-grain-launch (the unit's RuntimeDirectory) and its disk"
  | .lifetime => "automatic: grain-launch's lifetime ended, a fresh one continues"
  | .controllerSignaled => "automatic; the controller was killed by a signal (OOM, an operator); a crash on every start stops at the start limit"
  | .controllerLost => "grain-launch could not wait on its controller: nothing says a restart is safe; read the journal, then start the unit"
  | .controllerMechanism => "the controller's sandbox or program failed before the controller ran (stderr names the raw code): fix the mechanism, then start the unit"
  | .layoutMissing => "a directory the World's layout requires is absent (stderr names it, e.g. /srv/nd-hosted/worlds/LABEL/store): make it as nd-hosted 0700 (RUNBOOK §2b), then start the unit"

/-- The codes the grain-launch unit must not restart: both launch tables' fatal classes. -/
def launchPreventCodes : List Nat := ControllerExit.codesOf .fatal ++ LaunchExit.codesOf .fatal

/-- The grain launcher, one per hosted World (`%i` = its label): runs as the hosted user, with its
grains' PID files in its own runtime directory, the controller tailing the World's follow Store
(HOSTING-17: never the writer's files), resident grains reaching their broker sockets under the
broker root. -/
structure Launcher where
  name : String
  bin : String
  /-- ROOT: the hosting root; `ROOT/worlds/%i/store` is the follow Store the controller reads -/
  root : String
  /-- BROKER: keybroker's SOCKDIR (`Broker.sockdir`) -/
  broker : String
  /-- MEMBER: the member root (HOSTING-20, HOSTING-25): `MEMBER/<dirOf id>/nd.sock` is the socket
  nd-supervise serves a resident's `nd --stdio` on, as nd; disjoint from ROOT and BROKER -/
  member : String
  /-- `/run/NAME/%i` holds the grains' PID files (systemd's RuntimeDirectory, owned by `user`) -/
  runtime : String
  /-- `User=` of the system unit; `none` renders a user unit (the live harness) -/
  user : Option String
  /-- the follower unit the controller's Store comes from -/
  follower : Node
  /-- `none`: PIDS is `/run/runtime/%i` (RuntimeDirectory); `some DIR`: PIDS is `DIR/%i` of a user
  unit, no RuntimeDirectory (the live harness) -/
  pidsDir : Option String := none
  /-- the unit stem of the follower's driver (`nd-follow-drive`): a HARD dependency (HOSTING-7's
  resident row, 113537f: the follow Store advances only while `nd sync` drives it, so a stopped
  driver is a resident that never sees a new turn). `none` only in the live harness, which has no
  writer to drive from -/
  driver : Option String := some "nd-follow-drive"
  deriving Repr

/-- grain-launch's PIDS argument. -/
def Launcher.pids (l : Launcher) : String := (l.pidsDir.getD ("/run/" ++ l.runtime)) ++ "/%i"

def grainLauncher : Launcher :=
  { name := "nd-grain-launch", bin := "/opt/nd/bin", root := "/srv/nd-hosted", broker := keybroker.sockdir,
    member := memberDir,
    runtime := "nd-grain-launch", user := some "nd-hosted", follower := hostedFollower }

def Launcher.store (l : Launcher) : String := l.root ++ "/worlds/%i/store"

/-- The controller must read the Store its follower writes, as the follower's own user. -/
def Launcher.paired (l : Launcher) : Bool := l.store == l.follower.store && l.follower.user == l.user

def Launcher.check (l : Launcher) : Except Refusal _root_.Unit := do
  unless l.paired do throw (.badPath l.store)
  checkAll [l.bin, l.root, l.broker, l.member, l.pids, l.store] true
  unless l.runtime.toList.all plainChar && !l.runtime.contains '/' do throw (.badPath l.runtime)

/-- grain-launch's argv, in its order: ROOT BROKER MEMBER LABEL PIDS CONTROLLER, then the
controller's own `STORE LABEL`. -/
def Launcher.exec (l : Launcher) : List Arg :=
  [.lit (l.bin ++ "/grain-launch"), .lit l.root, .lit l.broker, .lit l.member, .lit "%i", .lit l.pids,
   .lit (l.bin ++ "/hosting-controller"), .lit l.store, .lit "%i"]

def Launcher.systemd (l : Launcher) : Except Refusal String := do
  l.check
  let fol := unitFile l.follower |>.drop "linux/".length |>.toString |>.replace "@." "@%i."
  return "\n".intercalate ([
    "# GENERATED by emit-units from Ops/Units.lean and Hosting/LaunchExit.lean — do not edit",
    "[Unit]",
    "Description=nanodregg grain launcher and controller of World %i",
    "# the controller tails the World's own follow Store (HOSTING-17); residents reach keybroker",
    s!"Wants={fol}{match l.driver with | some d => s!" {d}@%i.service" | none => ""}",
    s!"After={fol}{match l.driver with | some d => s!" {d}@%i.service" | none => ""} {keybroker.name}.service",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple"] ++ (match l.user with | some u => [s!"User={u}"] | none => []) ++
    (if l.pidsDir.isNone then [s!"RuntimeDirectory={l.runtime}/%i"] else []) ++ [
    s!"ExecStart={spaced (l.exec.map Arg.systemd)}",
    "Restart=on-failure",
    s!"RestartSec={restartSeconds}",
    s!"RestartPreventExitStatus={spaced (launchPreventCodes.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    s!"TimeoutStopSec={stopSeconds}",
    "",
    "[Install]",
    s!"WantedBy={if l.user.isSome then "multi-user.target" else "default.target"}",
    ""])

/-! ## The follower's driver (HOSTING-17 §7, ROOT's ruling (B)): `nd sync` as nd, per hosted World -/

/-- What the operator does when `nd sync` ends (PROTOCOL-38's CommandExit). Exhaustive. -/
def commandAction : CommandExit → String
  | .ok => "nothing: the follower reached the writer's tip; the next run follows after the restart interval"
  | .refused => "a refusal by name (stderr `refused NAME`): the follower's observe-only member or its grant is not live, or its envelope key is not the member's current key; re-enrol it (RUNBOOK §2b) and start the unit"
  | .uncertain => "automatic: the writer answered `uncertain`; the next run re-reads"
  | .behind => "automatic: the catch-up read its page bound and is still behind; the next run continues from what was absorbed"
  | .client => "nd itself could not run (argv, a socket, the workspace; stderr names it): check /etc/nd/follow/LABEL and that both sockets exist; it is retried every interval"
  | .declined => "nothing: `sync` sends no call, so it is never `declined` (a submit's not-final refusal, PROTOCOL-41); seen from sync, report to PROTOCOL"
  | .open => "nothing: `sync` sends no call, so it never ends `open` (an attempt whose call may still land, PROTOCOL-46); seen from sync, report to PROTOCOL"
  | .hostContradicted => "nothing: `sync` sends no call, so the Host's word on a call is never contradicted (PROTOCOL-46); seen from sync, report to PROTOCOL"
  | .pageIo => "automatic: the writer could not read one page from its disk (its stderr has `STATUS page refused=pageIo`) and serves on; the next run asks again. If every run ends pageIo, the writer's disk is the fault (RUNBOOK §3)"

/-- How often the driver runs `nd sync`: systemd's `RestartSec` of an always-restarting unit. -/
def syncSeconds : Nat := 40

/-- The codes the driver must not run again: the command table's fatal class. -/
def drivePreventCodes : List Nat := CommandExit.codesOf .fatal

/-- The driver of one hosted World's follower (`%i` = its label): the trusted side (`nd`)
initiates to both sockets — the follower's (shared with group nd, `hostedFollower`) and the
writer's `host.sock` (nd-only) — with the follower's observe-only envelope key in an
envelope-only custody workspace (CLIENT-3) under the §2a chain. -/
structure Driver where
  name : String
  bin : String
  /-- the observe-only member's custody workspace (`ND_WORKSPACE`), one per World -/
  workspace : String
  user : String
  follower : Node
  hostSock : String
  deriving Repr

def followDriver : Driver :=
  { name := "nd-follow-drive", bin := "/opt/nd/bin", workspace := "/etc/nd/follow/%i", user := "nd",
    follower := hostedFollower, hostSock := writer.sock }

/-- The driver must run as the follower socket's group (the writer's user, `nd`), not as the
follower's own user, and talk to the writer's own socket. -/
def Driver.trusted (d : Driver) : Bool :=
  some d.user == writer.user && d.follower.user != some d.user && d.hostSock == writer.sock

def Driver.check (d : Driver) : Except Refusal _root_.Unit := do
  unless d.trusted do throw (.badPath d.hostSock)
  checkAll [d.bin, d.workspace, d.follower.sock, d.hostSock] true

def Driver.systemd (d : Driver) : Except Refusal String := do
  d.check
  let fol := unitFile d.follower |>.drop "linux/".length |>.toString |>.replace "@." "@%i."
  return "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean and Protocol/Exit.lean (CommandExit) — do not edit",
    "[Unit]",
    "Description=nanodregg follow driver of World %i (nd sync, the trusted side initiates)",
    s!"Wants={fol}",
    s!"After={fol} {writer.name}.service",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple",
    s!"User={d.user}",
    s!"Environment=ND_WORKSPACE={d.workspace} ND_FOLLOW_SOCK={d.follower.sock} ND_HOST_SOCK={d.hostSock}",
    s!"ExecStart={d.bin}/nd sync",
    "# every end runs again after the interval but the fatal class (a refusal by name)",
    "Restart=always",
    s!"RestartSec={syncSeconds}",
    s!"RestartPreventExitStatus={spaced (drivePreventCodes.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    "RestrictAddressFamilies=AF_UNIX",
    s!"TimeoutStopSec={stopSeconds}",
    "",
    "[Install]",
    "WantedBy=multi-user.target",
    ""]

def exitsTable : String :=
  let host := (Status.all.map fun s => (s.code, exitRow s.code s.name s.cls (hostAction s))).mergeSort
    fun a b => decide (a.1 ≤ b.1)
  let sup := SupervisorExit.all.map fun e => exitRow e.code (supervisorName e) e.cls (supervisorAction e)
  let kb := KeybrokerExit.all.map fun e => exitRow e.code e.name e.cls (keybrokerAction e)
  let dec := DeciderExit.all.map fun e => exitRow e.code ((toString (repr e)).splitOn ".").getLast! e.cls (deciderAction e)
  let gl := LaunchExit.all.map fun e => exitRow e.code e.name e.cls (launchAction e)
  let nd := CommandExit.all.map fun e => exitRow e.code ((toString (repr e)).splitOn ".").getLast! e.cls (commandAction e)
  let mem := MembersExit.all.map fun e => exitRow e.code e.name e.cls (membersAction e)
  let ctl := ControllerExit.all.map fun e => exitRow e.code ((toString (repr e)).splitOn ".").getLast! e.cls (controllerAction e)
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
    "|---|---|---|---|---|"] ++ sup ++ [
    "",
    "## keybroker (the nd-keybroker unit; its decider's codes below are passed through)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ kb ++ [
    "",
    "## hosting-broker (the decider, under keybroker)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ dec ++ [
    "",
    "## nd-members (the nd-members@ unit; its decider's codes above are passed through)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ mem ++ [
    "",
    "## grain-launch (the nd-grain-launch@ unit; its controller's codes below are passed through)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ gl ++ [
    "",
    "## hosting-controller (under grain-launch)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ ctl ++ [
    "",
    "## nd sync (the nd-follow-drive@ unit; Restart=always every RestartSec but the fatal class)",
    "",
    "| code | name | class | systemd | operator |",
    "|---|---|---|---|---|"] ++ nd ++ [""])

/-! ## The Store's files (deploy/units/STORE.md), rendered from `Host.Store.layout` -/

def kindWord : FileKind → String
  | .once => "written once (genesis)"
  | .appendOnly => "append-only"
  | .replaced => "replaced whole, atomically"
  | .transient => "transient: never read by an open, never backed up"

def storeTable : String :=
  let rows := Host.Store.layout.map fun f => s!"| `{f.name}` | {kindWord f.kind} | {f.holds} |"
  let order := Host.Store.backupOrder.zipIdx.map fun (f, i) => s!"{i + 1}. `{f}`"
  "\n".intercalate ([
    "<!-- GENERATED by emit-units from Ops/Units.lean and Host/Base.lean (Host.Store.layout, backupOrder) — do not edit -->",
    "# The files of a nanodregg Store",
    "",
    "| file | kind | holds |",
    "|---|---|---|"] ++ rows ++ [
    "",
    "## Backup order (a live Store may be copied while its writer runs)",
    "",
    "Copy the files in this order, each whole. The base comes before every append-only file, so each",
    "append-only copy holds at least the prefix the copied base names (`Host.Proofs.Base`",
    "`backupOrder_appendOnly_after_base`); a longer copy is a torn tail or orphan index entries, which",
    "an open handles. Restore with `host check STORE --anchor HEIGHT:CHAIN` (RUNBOOK §5).",
    ""] ++ order ++ [""])

def emitted : List Node := [writer, member, hostedFollower]

def files : Except Refusal (List (String × String)) := do
  let units ← emitted.mapM fun n => do return (unitFile n, (← Service.ofNode n).systemd)
  return units ++ [("linux/nd-keybroker.service", ← keybroker.systemd),
    ("linux/nd-grain-launch@.service", ← grainLauncher.systemd),
    ("linux/nd-follow-drive@.service", ← followDriver.systemd),
    ("linux/nd-members@.service", ← membersUnit.systemd),
    ("linux/tmpfiles/nd-broker.conf", ← keybroker.tmpfiles), ("linux/tmpfiles/nd-follow.conf", followTmpfiles),
    ("linux/tmpfiles/nd-member.conf", memberTmpfiles), ("linux/tmpfiles/nd-member-follow.conf", memberFollowTmpfiles),
    ("linux/tmpfiles/nd-members.conf", membersHomeTmpfiles), ("linux/sysusers/nd.conf", ← keybroker.sysusers),
    ("EXITS.md", exitsTable),
    ("STORE.md", storeTable)]

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

/-- The live harness's keybroker (deploy/live/broker.sh): the deployed renderer as a USER unit
whose every path lies under `root`, its upstream an unreachable local port (the row is the unit,
not the call). `user`/`hosted` only name the deployed pair's roles here: one uid runs it all. -/
def liveBroker (root : String) : Broker :=
  { keybroker with
    name := "nd-ops-live-keybroker"
    bin := root ++ "/bin"
    etc := root ++ "/etc"
    sockdir := root ++ "/broker"
    upstream := "127.0.0.1:9"
    store := root ++ "/store"
    pidsDir := some (root ++ "/pids") }

/-- The live hosted follower and launcher (deploy/live/hosted.sh): the deployed templates as user
units under `root` (one uid: the follower socket's group is this user's primary group, the
two-uid split is the deployment's). -/
def liveHostedFollower (root : String) : Node :=
  { hostedFollower with
    name := "nd-ops-live-hfollow"
    bin := root ++ "/bin"
    store := root ++ "/hosted/worlds/%i/store"
    socket := root ++ "/nd-follow/%i.sock"
    hide := [root ++ "/ws"]
    user := none
    envDir := root ++ "/env" }

def liveLauncher (root : String) : Launcher :=
  { grainLauncher with
    name := "nd-ops-live-grain"
    bin := root ++ "/bin"
    root := root ++ "/hosted"
    broker := root ++ "/broker"
    member := root ++ "/member"
    user := none
    follower := liveHostedFollower root
    driver := none
    pidsDir := some (root ++ "/pids") }

def liveFiles (root : String) : Except Refusal (List (String × String)) := do
  let units ← (liveNodes root).mapM fun n => do return (n.name ++ ".service", (← Service.ofNode n).systemd)
  let b := liveBroker root
  let f := liveHostedFollower root
  let l := liveLauncher root
  return units ++ [(b.name ++ ".service", ← b.systemd),
    (f.name ++ "@.service", (← Service.ofNode f).systemd), (l.name ++ "@.service", ← l.systemd)]

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
