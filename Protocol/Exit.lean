/-
# Protocol.Exit — how `nd-supervise` itself ends, as data (CLIENT, OPS's ask 2026-10-17)

`nd-supervise` passes its child's exit status through, so the service manager reads ONE code space:
the Host's (`Host.Exit.Status`, codes below 64, never 1 or 2) and the supervisor's own three, here.
Each has the Host's `ExitClass`, so a unit file renders one prevent list from both tables
(`Ops.Units`), and the Rust reads the codes only from the emitted `generated::supervisor_exit`.

It is its own module (not `Protocol.Table`): `Host.Loop` imports `Protocol.Table`, and this
imports `Host.Exit` for `ExitClass`; nothing in Host imports it. Theorems: `Protocol.Proofs.Exit`.
-/
import Host.Exit
import Protocol.Command.Exit

namespace Nanodregg.Protocol

/-- Every way `nd-supervise` ends on its own account (the child's own exit is passed through). -/
inductive SupervisorExit where
  /-- refused before the child ran: nothing hidden, an argument it cannot read, a socket it cannot
  bind, the sandbox refusing the policy or missing its mechanism (CLIENT-8/9) -/
  | refusedAtLaunch
  /-- the child wrote a frame the mux cannot route: a defect in the child, which a restart would
  only repeat -/
  | childUnroutable
  /-- the child was killed by a signal (the OOM killer, earlyoom, an operator): transient by
  assumption; a deterministic crash then restarts under the unit's start limit -/
  | childSignaled
  deriving DecidableEq, Repr

namespace SupervisorExit

def all : List SupervisorExit := [refusedAtLaunch, childUnroutable, childSignaled]

def code : SupervisorExit → Nat
  | refusedAtLaunch => 64
  | childUnroutable => 65
  | childSignaled => 66

def cls : SupervisorExit → Host.ExitClass
  | refusedAtLaunch | childUnroutable => .fatal
  | childSignaled => .restart

/-- The codes of one class, in table order: what a unit file adds to the Host's. -/
def codesOf (k : Host.ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end SupervisorExit

-- The restart class of each command end (Protocol.Command.Exit holds the codes).
namespace CommandExit

def cls : CommandExit → Host.ExitClass
  | ok | absent => .done
  | uncertain | behind | client => .restart
  | refused => .fatal

/-- The codes of one class, in table order. -/
def codesOf (k : Host.ExitClass) : List Nat := (all.filter (·.cls == k)).map code

end CommandExit

end Nanodregg.Protocol
