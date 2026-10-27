/-
# Hosting.BrokerExit — how keybroker and its decider end, as data (HOSTING-16, OPS-2's ask)

An exit status is a verdict (law 7), read by the service manager. keybroker's unit sees one code
space: keybroker's own ends (`KeybrokerExit`, 80 and up) and its decider's (`DeciderExit`, 70 and
up, and 7), which keybroker passes through when `hosting-broker` exits, as nd-supervise passes the Host's.
Only a code `DeciderExit` names is passed through (`decider_exit::ALL`); any other is the mechanism's
(`deciderMechanism`, fatal).
Each code has the Host's `ExitClass`: `done` (0 only), `restart` (a fresh start recovers) or `fatal`
(a restart would refuse again, or the refusal needs the operator). So `Ops.Units` is to render the unit's (OPS-2's next step)
`RestartPreventExitStatus` from `codesOf .fatal` of both tables and holds no list of its own.
keybroker reads its codes only from the emitted `broker_generated::keybroker_exit`.

The codes avoid 1 and 2 (an uncaught exception and a shell's misuse), 101 (a Rust panic's exit) and every Host and
nd-supervise code (`Hosting.Proofs.BrokerExit`).
-/
import Host.Exit

namespace Nanodregg.Hosting

open Nanodregg.Host (ExitClass)

/-- Every way `hosting-broker` ends, by kind (`BrokerCli.Exit.kind`). -/
inductive DeciderExit where
  /-- keybroker closed the pipe: the normal end -/
  | keybrokerGone
  /-- argv does not parse -/
  | usage
  /-- a frame from keybroker outside `1 ≤ len ≤ frameMax`: a defect in keybroker -/
  | badFrame
  /-- a `decide` header that does not decode: a defect in keybroker -/
  | badRequest
  /-- unreachable (`Proofs.Broker.step_encodes`), kept as the assertion -/
  | unencodable
  /-- `BrokerCli.lifetime` asks: a fresh life continues -/
  | lifetime
  /-- the allowance package has no id: a defect of the build -/
  | noPackage
  /-- the Store refused to open or to be followed: the operator's to look at -/
  | store
  /-- `drainMax` reads did not catch the tail up: a fresh open reads the World whole -/
  | behind
  /-- an IO error escaped: the call and error are on stderr -/
  | io
  /-- the World holds more resident grains than `Broker.Bounds.residentsMax`: their socket names
  do not fit one answer, and serving some of them would be a silent choice (HOSTING-26) -/
  | residentsPastBound
  deriving DecidableEq, Repr

namespace DeciderExit

def all : List DeciderExit :=
  [keybrokerGone, usage, badFrame, badRequest, unencodable, lifetime, noPackage, store, behind, io,
   residentsPastBound]

def code : DeciderExit → Nat
  | keybrokerGone => 0 | usage => 70 | badFrame => 71 | badRequest => 72 | unencodable => 73
  | lifetime => 74 | noPackage => 75 | store => 76 | behind => 77 | io => 78
  | residentsPastBound => 7

def cls : DeciderExit → ExitClass
  | keybrokerGone => .done
  | lifetime | behind => .restart
  | usage | badFrame | badRequest | unencodable | noPackage | store | io | residentsPastBound => .fatal

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end DeciderExit

/-- Every way `keybroker` ends on its own account (its decider's exit is passed through). -/
inductive KeybrokerExit where
  /-- argv does not parse -/
  | usage
  | keyFileLink
  | keyFileNotRegular
  | keyFileOwner
  | keyFileMode
  | keyFileLength
  | keyFileDir
  | keyFileIo
  /-- the key file is not `SLOT KEY` lines, or holds a duplicate slot, or one of the certify slot's
  two lines (`certify HEX`, `certify.next HEX`) without the other or not 64 hex digits (HOSTING-56) -/
  | keyFileFormat
  | anchorsLink
  | anchorsNotRegular
  | anchorsOwner
  | anchorsMode
  | anchorsLength
  | anchorsDir
  | anchorsMissing
  | anchorsIo
  /-- the anchor file is not valid certificates only (HOSTING-15) -/
  | anchorsMalformed
  | pinsLink
  | pinsNotRegular
  | pinsOwner
  | pinsMode
  | pinsLength
  | pinsDir
  | pinsMissing
  | pinsIo
  /-- the pin file is not `HOST SHA256-HEX` lines, each ended by LF, or names a pin twice (HOSTING-28) -/
  | pinsMalformed
  /-- rustls refused the client configuration: a defect of the build -/
  | tlsConfig
  /-- a resident socket could not be bound (a stale socket, a missing SOCKDIR) -/
  | socket
  /-- SOCKDIR or a resident's directory in it fails HOSTING-17's checks (owner, mode 02710, group,
  the StrictModes chain), or something other than the last life's socket sits at a socket path -/
  | sockDir
  /-- the sandbox refused the decider's policy, or the decider could not be spawned -/
  | deciderRefused
  /-- the decider's PID file could not be written -/
  | pidFile
  /-- the decider was killed by a signal (the OOM killer, an operator): transient by assumption -/
  | deciderSignaled
  /-- keybroker could not read its decider's end (`wait` failed), or the decider gave no answer within
  `Broker.Bounds.answerMsMax` and did not end (CLIENT-39): nothing says a restart is safe -/
  | deciderLost
  /-- the decider's process ended with a code `DeciderExit` does not name: the decider never ran
  its own end (its confinement step refused, the program or a library is missing), so a
  restart meets the same mechanism (HOSTING-23) -/
  | deciderMechanism
  /-- the parent-death link could not be set (`nanodregg_sandbox::die_with_parent`, CLIENT-38): a
  process of ours that would outlive the parent that spawned it does not start -/
  | parentDeath
  /-- the certify slot's last-certified file (`KEYS.certified`, HOSTING-56) fails the custody checks
  or could not be made empty when absent -/
  | certifiedState
  deriving DecidableEq, Repr

namespace KeybrokerExit

def all : List KeybrokerExit :=
  [usage, keyFileLink, keyFileNotRegular, keyFileOwner, keyFileMode, keyFileLength, keyFileDir,
   keyFileIo, keyFileFormat, anchorsLink, anchorsNotRegular, anchorsOwner, anchorsMode, anchorsLength,
   anchorsDir, anchorsMissing, anchorsIo, anchorsMalformed, pinsLink, pinsNotRegular, pinsOwner, pinsMode,
   pinsLength, pinsDir, pinsMissing, pinsIo, pinsMalformed, tlsConfig, socket, deciderRefused, pidFile,
   deciderSignaled, deciderLost, sockDir, deciderMechanism, parentDeath, certifiedState]

def code : KeybrokerExit → Nat
  | usage => 80 | keyFileLink => 81 | keyFileNotRegular => 82 | keyFileOwner => 83 | keyFileMode => 84
  | keyFileLength => 85 | keyFileDir => 86 | keyFileIo => 87 | keyFileFormat => 88
  | anchorsLink => 89 | anchorsNotRegular => 90 | anchorsOwner => 91 | anchorsMode => 92
  | anchorsLength => 93 | anchorsDir => 94 | anchorsMissing => 95 | anchorsIo => 96
  | anchorsMalformed => 97 | tlsConfig => 98 | socket => 99 | deciderRefused => 100 | pidFile => 103
  | deciderSignaled => 102 | deciderLost => 104 | sockDir => 105 | deciderMechanism => 79
  | pinsLink => 140 | pinsNotRegular => 141 | pinsOwner => 142 | pinsMode => 143 | pinsLength => 144
  | pinsDir => 145 | pinsMissing => 146 | pinsIo => 147 | pinsMalformed => 148 | parentDeath => 149
  | certifiedState => 163

/-- Every own end but a signalled decider is fatal: each is a file, an argument or the build, and
a restart reads the same one. -/
def cls : KeybrokerExit → ExitClass
  | deciderSignaled => .restart
  | _ => .fatal

/-- The name printed on stderr (`keybroker: NAME …`). -/
def name (e : KeybrokerExit) : String := ((toString (repr e)).splitOn ".").getLast!

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end KeybrokerExit

/-- Every way `nd-members` (HOSTING-30, CLIENT-29) ends on its own account. Its decider's exit is
passed through as keybroker's is (`DeciderExit`); a World holding more resident grains than
`Broker.Bounds.residentsMax` ends it with `DeciderExit.residentsPastBound`'s code 7, the same fact
under the same code, whichever side counts first. A resident's own trouble (a member not
provisioned, a socket directory not alone, a crash loop) is never an end: it is a name on stderr and
that resident unbound, because one resident must not stop the others. -/
inductive MembersExit where
  /-- argv does not parse -/
  | usage
  /-- MEMBER fails `custody::check_shared_dir` (owner, mode 02710, the StrictModes chain) -/
  | memberRoot
  /-- MEMBERS fails `custody::check_private_dir` -/
  | membersRoot
  /-- FOLLOW (the follower sockets' root) fails `custody::check_private_dir` -/
  | followRoot
  /-- RLIMIT_NOFILE is below the fds one resident's nd-supervise may hold (CLIENT-28): every child
  inherits the limit, so each would refuse at launch -/
  | fdLimit
  /-- the sandbox refused the decider's policy, or the decider could not be spawned -/
  | deciderRefused
  /-- a PID file could not be written -/
  | pidFile
  /-- the decider was killed by a signal: transient by assumption -/
  | deciderSignaled
  /-- the decider stopped answering `residents` (or answered out of turn) and did not end -/
  | deciderLost
  /-- the decider's process ended with a code `DeciderExit` does not name (HOSTING-23) -/
  | deciderMechanism
  /-- STATE (the follower Stores and `follow` files, `Hosting.stateRoot`, HOSTING-32) fails
  `custody::check_private_dir` -/
  | stateRoot
  /-- two of MEMBER, MEMBERS, STATE and FOLLOW nest, after canonicalizing (HOSTING-32: the stdio
  child's write set must never reach a follower Store; `Proofs.Plan.roots_disjoint` for the
  deployed roots) -/
  | rootsOverlap
  /-- the parent-death link could not be set (`nanodregg_sandbox::die_with_parent`, CLIENT-38): a
  process of ours that would outlive the parent that spawned it does not start -/
  | parentDeath
  deriving DecidableEq, Repr

namespace MembersExit

def all : List MembersExit :=
  [usage, memberRoot, membersRoot, followRoot, fdLimit, deciderRefused, pidFile, deciderSignaled,
   deciderLost, deciderMechanism, stateRoot, rootsOverlap, parentDeath]

def code : MembersExit → Nat
  | usage => 150 | memberRoot => 151 | membersRoot => 152 | followRoot => 153 | fdLimit => 154
  | deciderRefused => 155 | pidFile => 156 | deciderSignaled => 157 | deciderLost => 158
  | deciderMechanism => 159 | stateRoot => 160 | rootsOverlap => 161 | parentDeath => 162

/-- Every own end but a signalled decider is fatal: each is a root, an argument, a limit or the
build, and a restart reads the same one. -/
def cls : MembersExit → ExitClass
  | deciderSignaled => .restart
  | _ => .fatal

/-- The name printed on stderr (`nd-members: NAME …`). -/
def name (e : MembersExit) : String := ((toString (repr e)).splitOn ".").getLast!

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end MembersExit

/-- The restart policy of a restart-class end, one for every manager: the service manager's
(`Ops.Units` renders it as RestartSec, StartLimitBurst and StartLimitIntervalSec, and launchd's
ThrottleInterval) and nd-members' per resident (emitted `RESTART_SECONDS`, `START_BURST`,
`START_INTERVAL_SECONDS`, CLIENT-40). Seconds between restarts: -/
def restartSeconds : Nat := 2

/-- The start limit: more than `startBurst` starts inside `startIntervalSeconds` and the unit (or the
resident) fails instead of restarting. Without it a deterministic crash of a restart class (a child
killed by a signal on every start, `uncertain` on every open) loops every `restartSeconds` forever:
systemd's default (5 starts in 10 s) never trips at a 2 s restart. -/
def startIntervalSeconds : Nat := 120
def startBurst : Nat := 5

end Nanodregg.Hosting
