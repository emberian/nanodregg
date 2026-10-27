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
  /-- the catch-up read `Bounds.pagesPerCommandMax` pages and is still behind the writer's tip:
  what was absorbed is kept, run again (printed `behind STEPS TIP`: two step counts) -/
  | behind
  /-- the writer refused the call by name and did not record it (`Status.declined`, PROTOCOL-41):
  not final, the attempt stays open (printed `declined NAME`) -/
  | declined
  /-- nd itself could not run the command (its argv, a socket, the workspace) -/
  | client
  /-- every send was answered `absent` and follow's own World says the call's window is still live
  (PROTOCOL-46): the signed bytes may still land, so the attempt stays OPEN; running the command
  again would sign a second call. A restart runs it again, which probes the same bytes (printed
  `open`) -/
  | «open»
  /-- the Host said committed or refused and the member's own follow says otherwise (PROTOCOL-46):
  the attempt stays open and the Host's word is named (printed `hostContradicted HOSTSAID
  FOLLOWSAID`) -/
  | hostContradicted
  /-- the writer refused a page `pageIo` (HOST-48): its IO failed building that page and it serves
  on, so this is "not now", never "never". What was absorbed is kept and nothing was signed past
  it; an attempt in flight stays open. Run again after the writer's next page (printed `pageIo`) -/
  | pageIo
  deriving DecidableEq, Repr

namespace CommandExit

def all : List CommandExit := [ok, refused, uncertain, behind, client, declined, «open», hostContradicted, pageIo]

def code : CommandExit → Nat
  | ok => 0 | refused => 1 | uncertain => 2 | behind => 51 | client => 52
  | declined => 53 | «open» => 54 | hostContradicted => 55 | pageIo => 57
  -- 56 is the Host's `positionUnfit` (`code_disjoint_host`)
  -- 50 was `absent` (deleted by PROTOCOL-46: `absent` is never the end of an attempt); never reused

def ofCode? (n : Nat) : Option CommandExit := all.find? (·.code == n)

end CommandExit

end Nanodregg.Protocol
