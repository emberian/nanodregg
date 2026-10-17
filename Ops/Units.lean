/-
# Ops.Units — service-manager units for `host`, rendered from HOST's exit table (ASSEMBLY D5/D10)

A unit is `nd-supervise SOCKET (--hide|--read|--write|--exec PATH)… -- HOST VERB …` (CLIENT's
grammar, client/src/bin/nd-supervise.rs) with the restart policy READ from `Host.Status`:
systemd restarts on failure except the fatal codes (`RestartPreventExitStatus` = `codesOf .fatal`),
so a Store that refuses to open stops by name instead of looping. The unit decides nothing: every
number comes from the table, every argument from the `Node`.

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

namespace Nanodregg.Ops.Units

open Nanodregg.Host

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

/-- nd-supervise's grammar applied to the node: socket, `--write STORE`, every `--hide`, `--`,
the host program and its arguments. -/
def Node.exec (n : Node) : List Arg :=
  [.lit (supervisor n), .lit n.socket, .lit "--write", .lit n.store] ++
  n.hide.flatMap (fun h => [.lit "--hide", .lit h]) ++ [.lit "--", .lit (hostExe n)] ++ n.args

/-- Every path checks, or the first that does not. -/
def checkAll : List String → Except Refusal _root_.Unit
  | [] => .ok ()
  | p :: ps => match checkPath p with
    | .error e => .error e
    | .ok _ => checkAll ps

def Service.ofNode (n : Node) : Except Refusal Service :=
  if n.hide.isEmpty then .error .nothingHidden else
  match checkAll ([n.bin, n.store, n.socket] ++ n.hide) with
  | .error e => .error e
  | .ok _ => .ok { node := n, exec := n.exec, prevent := Status.codesOf .fatal }

def Arg.systemd : Arg → String
  | .lit s => s
  | .var v => "${" ++ v ++ "}"

def spaced (xs : List String) : String := " ".intercalate xs

/-- Seconds between restarts (both managers), and systemd's stop timeout. -/
def restartSeconds : Nat := 2
def stopSeconds : Nat := 10

def Service.systemd (u : Service) : String :=
  let n := u.node
  let env := match n.role with
    | .serve => []
    | .follow => [s!"EnvironmentFile=%h/.nd/{n.name}.env"]
  let user := match n.user with
    | some us => [s!"User={us}"]
    | none => []
  let wanted := if n.user.isSome then "multi-user.target" else "default.target"
  "\n".intercalate ([
    "# GENERATED by emit-units from Ops/Units.lean and Host/Exit.lean — do not edit",
    "[Unit]",
    s!"Description=nanodregg host {match n.role with | .serve => "serve" | .follow => "follow"} under nd-supervise",
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
    "<!-- GENERATED by emit-units from Ops/Units.lean and Host/Exit.lean — do not edit -->",
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

/-! ## The emitted units (ops/units/) -/

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

def files : Except Refusal (List (String × String)) :=
  emitted.mapM fun (path, n) => do return (path, (← Service.ofNode n).systemd)

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
      | ["--check", dir] =>
        let mut bad := 0
        for (p, t) in fs do
          let path := System.FilePath.mk dir / p
          let cur ← if ← path.pathExists then IO.FS.readFile path else pure ""
          unless cur == t do IO.eprintln s!"emit-units: {path} differs from the table; regenerate it"; bad := bad + 1
        return if bad = 0 then 0 else 1
      | _ => IO.eprintln "usage: emit-units [--check] DIR"; return 2

end Nanodregg.Ops.Units
