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
list of their own. Codes stay below 64, below nd-supervise's own exits (64–66, `Protocol.Exit`), and
never use 1 (the runtime's exit for an uncaught exception, which must never read as a named status)
or 2 (the conventional exit for a shell's or a parser's misuse, kept free for the same reason).
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
  /-- a round's end inside the process: `Host.restarts` consumes it and reopens in process (D4),
  so `host` never exits with it; seen from outside it is a defect -/
  | fuel
  | sealIo
  /-- argv does not parse, or an argument's value is refused (founder keys, member, grant) -/
  | usage
  /-- the OS random source returned something other than 32 bytes (a premise at the FFI) -/
  | entropy
  | recordTooLarge
  | worldTooLarge
  | indexTooLarge
  /-- an IO call failed before a Store opened (an absent STORE path or IN file, EACCES, EIO, a file
  removed between the `missing` check and its open; genesis; check);
  the call and errno on stderr. Before this status existed it was an uncaught exception,
  exit 1 with no name -/
  | io
  /-- an IO error escaped `serve`/`follow` after the Store opened (restart, like `uncertain`) -/
  | ioServing
  | locked
  | exists
  | badKey
  | shortRead
  /-- a Store file is absent from an existing STORE directory (stderr names it, HOST-35) -/
  | missing
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
  /-- a `log` walk read an index entry that does not read back at its position under the Store's
  key, or whose chain is not a digest (HOST-33: the entry is refused when read, never used) -/
  | badIndex
  /-- a page does not fit its reply's bounds -/
  | pageTooLarge
  /-- a `read` from past the end of the base's World bytes -/
  | pastEnd
  /-- the base file is shorter than its World: it changed under the read -/
  | shortBase
  /-- a fuel restart's in-process reopen refused (D4) -/
  | reopenFailed
  /-- a fuel restart reopened a state other than the one the loop held: a defect in open or append -/
  | reopenDiverged
  /-- the restart budget is spent (unreachable before the reader's own lifetime) -/
  | lifetime
  /-- the request stream stopped inside a frame, with a bad length, a read error, or at the
  reader's frame lifetime; nd-supervise exits with the child, so a restart re-pairs the pipe -/
  | stream
  /-- a `.dedicated` task did not get its own thread (the runtime ran it inline): the reader would
  block the loop, and the resident would answer nothing -/
  | noThreads
  /-- the base was written under other codec shapes than this binary's (D2, HOST-20): an old
  shape refuses to load; re-genesis from a checked export carries the state (law 1) -/
  | shapeMismatch
  /-- the segment's origin frame verifies but states another World's genesis chain than the base
  World's origin (HOST-25): another Store's seg.log under a shared key file -/
  | foreignOrigin
  /-- `index.log` is shorter than the entries the base counts (HOST-30, HOST-33) -/
  | indexShort
  /-- the last entry the base counts does not read back at its position or is not the one the base
  names (open, HOST-33); from `host check`, any entry the base counts does not read back, name its
  record's offset, or keep heights ascending -/
  | indexCorrupt
  /-- a seal was handed an index entry outside the entry layout (a chain not the Store's width, a
  height or offset past u64): a defect (HOST-31, HOST-33) -/
  | entryUnfit
  /-- a seal found `index.log` at another size than the end of the entries the newest base counts:
  another process wrote or truncated it; the restart's open truncates orphans or refuses
  `indexShort` (HOST-31) -/
  | indexMoved
  /-- `host import`: the carried file does not hash to the operator's digest, does not decode, its
  anchor is not its carried height, the kernel refused the carried state, or the imported Store
  reopened to other carried bytes; `host export`: its own file did not read back (HOST-28) -/
  | carryMismatch
  /-- `host join`: the invitation does not decode, is signed by another key than the one the joiner
  trusts, or its signature does not verify over its bytes (`Protocol.Invite.accept`, PROTOCOL-42);
  stderr names which. Nothing was written -/
  | inviteRefused
  deriving DecidableEq, Repr

namespace Status

def all : List Status :=
  [eof, uncertain, fuel, sealIo, usage, entropy, recordTooLarge, worldTooLarge, indexTooLarge, io, ioServing,
   locked, .exists, badKey, shortRead, missing, baseTooLarge, baseCorrupt, baseUndecodable,
   segmentShort, tailTooLong, foreignSegment, corrupt, record, tagWidth, behindAnchor, chainMismatch,
   badIndex, pageTooLarge, pastEnd, shortBase, reopenFailed, reopenDiverged, lifetime, stream, noThreads,
   shapeMismatch, foreignOrigin, indexShort, indexCorrupt, entryUnfit, indexMoved, carryMismatch,
   inviteRefused]

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
  | missing => 20
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
  | reopenFailed => 38
  | reopenDiverged => 39
  | lifetime => 40
  | stream => 41
  | noThreads => 42
  | shapeMismatch => 43
  | foreignOrigin => 30
  | indexShort => 45
  | indexCorrupt => 46
  | entryUnfit => 47
  | indexMoved => 48
  | carryMismatch => 49
  | inviteRefused => 44

def cls : Status → ExitClass
  | eof => .done
  | uncertain | fuel | sealIo | ioServing | lifetime | stream | indexMoved => .restart
  | usage | entropy | recordTooLarge | worldTooLarge | indexTooLarge | io
  | locked | .exists | badKey | shortRead | missing | baseTooLarge | baseCorrupt | baseUndecodable
  | segmentShort | tailTooLong | foreignSegment | corrupt | record | tagWidth | behindAnchor | chainMismatch
  | badIndex | pageTooLarge | pastEnd | shortBase | reopenFailed | reopenDiverged | noThreads
  | shapeMismatch | foreignOrigin | indexShort | indexCorrupt | entryUnfit | carryMismatch | inviteRefused => .fatal

/-- The name printed beside the code (`refused NAME` / `exit NAME` on stderr). -/
def name (s : Status) : String := ((toString (repr s)).splitOn ".").getLast!

/-- The codes of one class, in table order: what a unit file renders. -/
def codesOf (k : ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end Status

def SealFault.status : SealFault → Status
  | .worldTooLarge _ => .worldTooLarge
  | .indexTooLarge _ => .indexTooLarge
  | .entryUnfit _ => .entryUnfit
  | .indexMoved _ _ => .indexMoved
  | .io _ => .sealIo

def BaseFault.status : BaseFault → Status
  | .baseTooLarge _ => .baseTooLarge
  | .baseCorrupt => .baseCorrupt
  | .baseUndecodable _ => .baseUndecodable
  | .segmentShort _ _ => .segmentShort
  | .tailTooLong _ _ => .tailTooLong
  | .foreignSegment => .foreignSegment
  | .shapeMismatch _ _ => .shapeMismatch
  | .foreignOrigin => .foreignOrigin
  | .indexShort _ _ => .indexShort
  | .indexCorrupt => .indexCorrupt

def StoreFault.status {F : Type} : StoreFault F → Status
  | .locked => .locked
  | .exists => .exists
  | .badKey _ => .badKey
  | .missing _ => .missing
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
  | .recordTooLarge _ _ => .recordTooLarge
  | .reopenFailed _ => .reopenFailed
  | .reopenDiverged => .reopenDiverged
  | .lifetime => .lifetime
  | .stream _ => .stream

end Nanodregg.Host
