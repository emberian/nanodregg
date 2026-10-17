/-
# Hosting.BrokerExit — how keybroker and its decider end, as data (HOSTING-16, OPS-2's ask)

An exit status is a verdict (law 7), read by the service manager. keybroker's unit sees one code
space: keybroker's own ends (`KeybrokerExit`, 80 and up) and its decider's (`DeciderExit`, 70 and
up), which keybroker passes through when `hosting-broker` exits, as nd-supervise passes the Host's.
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
  deriving DecidableEq, Repr

namespace DeciderExit

def all : List DeciderExit :=
  [keybrokerGone, usage, badFrame, badRequest, unencodable, lifetime, noPackage, store, behind, io]

def code : DeciderExit → Nat
  | keybrokerGone => 0 | usage => 70 | badFrame => 71 | badRequest => 72 | unencodable => 73
  | lifetime => 74 | noPackage => 75 | store => 76 | behind => 77 | io => 78

def cls : DeciderExit → ExitClass
  | keybrokerGone => .done
  | lifetime | behind => .restart
  | usage | badFrame | badRequest | unencodable | noPackage | store | io => .fatal

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
  /-- the key file is not `SLOT KEY` lines, or holds a duplicate slot -/
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
  /-- rustls refused the client configuration: a defect of the build -/
  | tlsConfig
  /-- a resident socket could not be bound (a stale socket, a missing SOCKDIR) -/
  | socket
  /-- the sandbox refused the decider's policy, or the decider could not be spawned -/
  | deciderRefused
  /-- the decider's PID file could not be written -/
  | pidFile
  /-- the decider was killed by a signal (the OOM killer, an operator): transient by assumption -/
  | deciderSignaled
  /-- keybroker could not read its decider's end (`wait` failed): nothing says a restart is safe -/
  | deciderLost
  deriving DecidableEq, Repr

namespace KeybrokerExit

def all : List KeybrokerExit :=
  [usage, keyFileLink, keyFileNotRegular, keyFileOwner, keyFileMode, keyFileLength, keyFileDir,
   keyFileIo, keyFileFormat, anchorsLink, anchorsNotRegular, anchorsOwner, anchorsMode, anchorsLength,
   anchorsDir, anchorsMissing, anchorsIo, anchorsMalformed, tlsConfig, socket, deciderRefused, pidFile,
   deciderSignaled, deciderLost]

def code : KeybrokerExit → Nat
  | usage => 80 | keyFileLink => 81 | keyFileNotRegular => 82 | keyFileOwner => 83 | keyFileMode => 84
  | keyFileLength => 85 | keyFileDir => 86 | keyFileIo => 87 | keyFileFormat => 88
  | anchorsLink => 89 | anchorsNotRegular => 90 | anchorsOwner => 91 | anchorsMode => 92
  | anchorsLength => 93 | anchorsDir => 94 | anchorsMissing => 95 | anchorsIo => 96
  | anchorsMalformed => 97 | tlsConfig => 98 | socket => 99 | deciderRefused => 100 | pidFile => 103
  | deciderSignaled => 102 | deciderLost => 104

/-- Every own end but a signalled decider is fatal: each is a file, an argument or the build, and
a restart reads the same one. -/
def cls : KeybrokerExit → ExitClass
  | deciderSignaled => .restart
  | _ => .fatal

/-- The name printed on stderr (`keybroker: NAME …`). -/
def name (e : KeybrokerExit) : String := ((toString (repr e)).splitOn ".").getLast!

def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end KeybrokerExit

end Nanodregg.Hosting
