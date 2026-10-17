/-
# Host.Exit — how a `host` process ends, as data (ASSEMBLY-ops D5, ROOT ruling 2026-10-16)

An exit status is a verdict (law 7), read by the service manager and by `nd-supervise`, which
passes it through. So every way the process can end is one `Status` constructor with its own
code, and each code has one `ExitClass`:

* `done` — the request stream ended (`eof`); code 0, and no other status is 0;
* `restart` — the Store is sound and a fresh open recovers (`uncertain`, `fuel`, a seal's IO,
  `ioServing`);
* `fatal` — a restart would refuse again, or the refusal needs an operator: every open refusal,
  argv, and the bounds that should be unreachable (`recordTooLarge`, `worldTooLarge`,
  `indexTooLarge`: a defect, not load). `locked` is fatal by ROOT's ruling: whether a second
  writer may race a restart is the operator's decision, not an auto-restart's.

Unit files (`Ops.Units`) render their restart/prevent lists from `Status.codesOf`; they hold no
list of their own. Codes stay below 64 and never use 1 or 2 (nd-supervise's own exits, CLIENT's).
Theorems: `Host.Proofs.Exit`.
-/
import Host.Loop
import Host.Open
import Host.Page

namespace Nanodregg.Host

inductive ExitClass where
  | done
  | restart
  | fatal
  deriving DecidableEq, Repr

/-- Every way a `host` process ends. One constructor per exit code. -/
inductive Status where
  | eof
  | uncertain
  | fuel
  | sealIo
  /-- argv does not parse, or an argument's value is refused (founder keys, member, grant) -/
  | usage
  /-- the OS random source returned something other than 32 bytes (a premise at the FFI) -/
  | entropy
  | recordTooLarge
  | worldTooLarge
  | indexTooLarge
  /-- an IO call failed before a Store opened (a Store file absent, EACCES, EIO; genesis; check);
  the call and errno on stderr. Before this status existed it was an uncaught exception,
  exit 1 with no name -/
  | io
  /-- an IO error escaped `serve`/`follow` after the Store opened (restart, like `uncertain`) -/
  | ioServing
  | locked
  | exists
  | badKey
  | shortRead
  | noBase
  | baseTooLarge
  | baseCorrupt
  | baseUndecodable
  | segmentShort
  | tailTooLong
  /-- the 32 segment bytes before the base offset are not the base tag: another Store segment,
  or a pre-HOST-18 Store (HOST-18) -/
  | foreignSegment
  | corrupt
  | record
  | tagWidth
  /-- `host check --anchor`: the Store's World is lower than the anchor (a rollback, or a copy
  cut at a frame boundary) -/
  | behindAnchor
  /-- `host check --anchor`: at the anchor's height the chain is not the anchor's (another
  history) -/
  | chainMismatch
  /-- a `log` walk met an index entry whose chain is not a digest -/
  | badIndex
  /-- a page does not fit its reply's bounds -/
  | pageTooLarge
  /-- a `read` from past the end of the base's World bytes -/
  | pastEnd
  /-- the base file is shorter than its World: it changed under the read -/
  | shortBase
  deriving DecidableEq, Repr

namespace Status

def all : List Status :=
  [eof, uncertain, fuel, sealIo, usage, entropy, recordTooLarge, worldTooLarge, indexTooLarge, io, ioServing,
   locked, .exists, badKey, shortRead, noBase, baseTooLarge, baseCorrupt, baseUndecodable,
   segmentShort, tailTooLong, foreignSegment, corrupt, record, tagWidth, behindAnchor, chainMismatch,
   badIndex, pageTooLarge, pastEnd, shortBase]

def code : Status → Nat
  | eof => 0
  | uncertain => 3
  | fuel => 4
  | sealIo => 5
  | usage => 8
  | entropy => 9
  | recordTooLarge => 10
  | worldTooLarge => 11
  | indexTooLarge => 12
  | io => 13
  | ioServing => 6
  | locked => 16
  | .exists => 17
  | badKey => 18
  | shortRead => 19
  | noBase => 20
  | baseTooLarge => 21
  | baseCorrupt => 22
  | baseUndecodable => 23
  | segmentShort => 24
  | tailTooLong => 25
  | foreignSegment => 29
  | corrupt => 26
  | record => 27
  | tagWidth => 28
  | behindAnchor => 32
  | chainMismatch => 33
  | badIndex => 34
  | pageTooLarge => 35
  | pastEnd => 36
  | shortBase => 37

def cls : Status → ExitClass
  | eof => .done
  | uncertain | fuel | sealIo | ioServing => .restart
  | usage | entropy | recordTooLarge | worldTooLarge | indexTooLarge | io
  | locked | .exists | badKey | shortRead | noBase | baseTooLarge | baseCorrupt | baseUndecodable
  | segmentShort | tailTooLong | foreignSegment | corrupt | record | tagWidth | behindAnchor | chainMismatch
  | badIndex | pageTooLarge | pastEnd | shortBase => .fatal

/-- The name printed beside the code (`refused NAME` / `exit NAME` on stderr). -/
def name (s : Status) : String := ((toString (repr s)).splitOn ".").getLast!

/-- The codes of one class, in table order: what a unit file renders. -/
def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end Status

def SealFault.status : SealFault → Status
  | .worldTooLarge _ => .worldTooLarge
  | .indexTooLarge _ => .indexTooLarge
  | .io _ => .sealIo

def BaseFault.status : BaseFault → Status
  | .noBase => .noBase
  | .baseTooLarge _ => .baseTooLarge
  | .baseCorrupt => .baseCorrupt
  | .baseUndecodable _ => .baseUndecodable
  | .segmentShort _ _ => .segmentShort
  | .tailTooLong _ _ => .tailTooLong
  | .foreignSegment => .foreignSegment

def StoreFault.status {F : Type} : StoreFault F → Status
  | .locked => .locked
  | .exists => .exists
  | .badKey _ => .badKey
  | .shortRead _ _ => .shortRead
  | .base f => f.status
  | .log (.corrupt _) => .corrupt
  | .log (.record _ _) => .record
  | .seal f => f.status
  | .tagWidth => .tagWidth

def Page.Fault.status : Page.Fault → Status
  | .corrupt _ => .corrupt
  | .badIndex _ => .badIndex
  | .tooLarge => .pageTooLarge
  | .pastEnd _ _ => .pastEnd
  | .shortBase => .shortBase

def Exit.status : Exit → Status
  | .eof => .eof
  | .fuel => .fuel
  | .uncertain _ => .uncertain
  | .sealFailed f => f.status
  | .recordTooLarge _ => .recordTooLarge

end Nanodregg.Host
