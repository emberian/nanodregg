/-
# Protocol.Command.Exit — how `nd COMMAND` ends, its codes (PROTOCOL-38)

The command machine answers `done` with these codes; their restart classes are in `Protocol.Exit`
(which imports `Host.Exit`; this module does not, so the machine's import closure stays the
Protocol's). Theorems: `Protocol.Proofs.Exit`.
-/

namespace Nanodregg.Protocol

/-- How `nd COMMAND` ends: the `done` code follow's command machine answers (`Command.Machine`),
which nd passes through, plus nd's own failure. A timer that runs `nd sync` reads this table's
classes (OPS renders from `codesOf`). Every code but `ok` is one no Host or supervisor exit uses
(`Protocol.Proofs.Exit`), so a code names one end whichever table a reader holds (PROTOCOL-38). -/
inductive CommandExit where
  /-- the command did what it says (a write committed, a read held, `sync` reached the tip) -/
  | ok
  /-- refused by a name, printed `refused NAME` -/
  | refused
  /-- the Host's reply was `uncertain`: the attempt goes on by lookup -/
  | uncertain
  /-- the lookup answered `absent`: the Host never saw the call -/
  | absent
  /-- the catch-up read `Bounds.pagesPerCommandMax` pages and is still behind the writer's tip:
  what was absorbed is kept, run again (printed `behind HEIGHT TIP`) -/
  | behind
  /-- the writer refused the call by name and did not record it (`Status.declined`, PROTOCOL-41):
  not final, the attempt stays open (printed `declined NAME`) -/
  | declined
  /-- nd itself could not run the command (its argv, a socket, the workspace) -/
  | client
  deriving DecidableEq, Repr

namespace CommandExit

def all : List CommandExit := [ok, refused, uncertain, absent, behind, client, declined]

def code : CommandExit → Nat
  | ok => 0 | refused => 1 | uncertain => 2 | absent => 50 | behind => 51 | client => 52
  | declined => 53

def ofCode? (n : Nat) : Option CommandExit := all.find? (·.code == n)

end CommandExit

end Nanodregg.Protocol
