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

namespace Nanodregg.Ops.Units

open Nanodregg.Host
open Nanodregg.Protocol (SupervisorExit)
open Nanodregg.Hosting (DeciderExit KeybrokerExit)

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
  | .carryMismatch => "the carried file is not the one exported (digest), does not decode, or the imported Store reopened to other bytes (stderr names which): re-export from the STOPPED old Store and copy the printed digest exactly; remove a Store left by `carryMismatch reopen` and report it to HOST"
  | .indexMoved => "automatic; index.log changed size under the writer (another process wrote or truncated it): the restart's open truncates orphan entries or refuses indexShort; if it repeats, find the other writer"
  | .io => "a Store file is missing or unreadable: check the path and permissions (the call and errno are on stderr)"
  | .ioServing => "automatic; an IO error after the open: check the disk"
  | .locked => "another writer holds the Store: find its unit; never start a second"
  | .exists => "genesis into an existing Store: choose another path"
  | .badKey => "`STORE/key` is missing or not 32 bytes (a directory that holds no Store, or a lost key): restore it from the backup"
  | .shortRead => "a file changed under the open: stop every writer, then `host check`"
  | .noBase | .baseTooLarge | .baseCorrupt | .baseUndecodable | .segmentShort | .tailTooLong =>
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
  | .tlsConfig => "rustls refused the client configuration: a build defect, report to HOSTING"
  | .socket => "a resident socket could not be bound (a stale socket, a missing directory): stop the unit, check the runtime directory, start it"
  | .sockDir => "the broker's socket directory fails its checks: /run/nd-broker must be nd:nd-hosted mode 02710 (tmpfiles), every directory above it owned by root, and each resident directory in it nd's, mode 02710 (HOSTING-17, RUNBOOK §2a)"
  | .deciderRefused => "the sandbox refused the decider's policy or could not spawn it: check the mechanism (deploy/live/README.md) and the DECIDER path"
  | .pidFile => "the decider's PID file could not be written: check the runtime directory"
  | .deciderSignaled => "automatic; the decider was killed by a signal (OOM, an operator); a crash on every start stops at the start limit"
  | .deciderLost => "keybroker could not read its decider's end: nothing says a restart is safe; read the journal, then start the unit"

/-- The codes the keybroker unit must not restart: both broker tables' fatal classes. -/
def brokerPreventCodes : List Nat := DeciderExit.codesOf .fatal ++ KeybrokerExit.codesOf .fatal

/-- The keybroker unit's operator data: paths through `checkPath`, the rest literal or from the
unit's environment file (`ND_OPERATOR`, `ND_RESIDENTS`, `ND_PEER`: the `nd-hosted` uid, HOSTING-17). -/
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
  deriving Repr

def keybroker : Broker :=
  { name := "nd-keybroker", bin := "/opt/nd/bin", etc := "/etc/nd/keybroker", runtime := "nd-keybroker",
    sockdir := "/run/nd-broker", upstream := "api.anthropic.com:443", store := "/srv/nd/store", user := "nd",
    hosted := "nd-hosted" }

/-- A host:port with nothing a unit file would re-quote. -/
def plainAddr (a : String) : Bool :=
  !a.isEmpty && a.toList.all fun c => c.isAlphanum || c == '.' || c == '-' || c == ':'

def Broker.check (b : Broker) : Except Refusal _root_.Unit := do
  if b.hosted == b.user then throw .hostedIsKeyHolder
  checkAll [b.bin, b.etc, b.store, "/run/" ++ b.runtime, b.sockdir]
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

/-- keybroker's argv, in its order: KEYS ANCHORS SOCKDIR PIDS UPSTREAM STORE OPERATOR RESIDENTS PEER DECIDER. -/
def Broker.exec (b : Broker) : List Arg :=
  [.lit (b.bin ++ "/keybroker"), .lit (b.etc ++ "/provider.key"), .lit (b.etc ++ "/anchors.pem"),
   .lit b.sockdir, .lit ("/run/" ++ b.runtime), .lit b.upstream, .lit b.store,
   .var "ND_OPERATOR", .var "ND_RESIDENTS", .var "ND_PEER", .lit (b.bin ++ "/hosting-broker")]

def Broker.systemd (b : Broker) : Except Refusal String := do
  b.check
  return "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean and Hosting/BrokerExit.lean — do not edit",
    "[Unit]",
    "Description=nanodregg keybroker (the provider-key broker) and its decider",
    "Wants=network-online.target",
    "After=network-online.target",
    s!"StartLimitIntervalSec={startIntervalSeconds}",
    s!"StartLimitBurst={startBurst}",
    "",
    "[Service]",
    "Type=simple",
    s!"User={b.user}",
    s!"EnvironmentFile={b.etc}/keybroker.env",
    s!"RuntimeDirectory={b.runtime}",
    "# the installed anchors must be the build's pinned roots, byte for byte, at every start (OPS-7)",
    s!"ExecStartPre={b.bin}/emit-anchors --check {b.etc}/anchors.pem",
    s!"ExecStart={spaced (b.exec.map Arg.systemd)}",
    "Restart=on-failure",
    s!"RestartSec={restartSeconds}",
    s!"RestartPreventExitStatus={spaced (brokerPreventCodes.map toString)}",
    "UMask=0077",
    "NoNewPrivileges=yes",
    "RestrictAddressFamilies=AF_UNIX AF_INET AF_INET6",
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
    "|---|---|---|---|---|"] ++ dec ++ [""])

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

def followTmpfiles : String :=
  "\n".intercalate [
    "# GENERATED by emit-units from Ops/Units.lean (Ops.Units.hostedFollower) — do not edit",
    "# install as /etc/tmpfiles.d/nd-follow.conf (RUNBOOK §2b)",
    s!"d {followDir} {sockdirMode} {hostedFollower.user.getD ""} {writer.user.getD ""} -",
    ""]

def unitFile (n : Node) : String :=
  s!"linux/{n.name}{if n.template then "@" else ""}.service"

def emitted : List Node := [writer, member, hostedFollower]

def files : Except Refusal (List (String × String)) := do
  let units ← emitted.mapM fun n => do return (unitFile n, (← Service.ofNode n).systemd)
  return units ++ [("linux/nd-keybroker.service", ← keybroker.systemd),
    ("linux/tmpfiles/nd-broker.conf", ← keybroker.tmpfiles), ("linux/tmpfiles/nd-follow.conf", followTmpfiles), ("linux/sysusers/nd.conf", ← keybroker.sysusers),
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
