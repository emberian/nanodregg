/-
# Spec.Sim.Law — the unjudged kernel and the law and cancel runs (B3, C(ii) cancel; `Spec.Proofs.Law`)

The trivial system `unjudged`: the deployed system over `Xu`, the deployed program with a `judge`
that admits every step. The law run: from `wGenesis` the founder installs `Std.boundedPackage
{n : nat} n 5` and creates a data object under it with `n = 0`, then writes `n := 3` (admitted) or
`n := 9` (refused `lawDenied` by the kernel, admitted by `unjudged`). The cancel run: the founder
cancels its `issue 1000`, and follow steps the writer's tip page at the end of `cancel CALL`.
Tooling (closure C9): what is computed of these is stated in `Spec.Proofs.Law`.
-/
import Spec.Sim.Run
import Lang.StdGen
import Host.Page

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The law run's inputs -/

/-- A record state `{n : nat}` under the stdlib law `bounded` (`n ≤ 5`). -/
def lPkg : Lang.Package := Lang.Std.boundedPackage [("n", .nat)] "n" 5

def lBytes : ByteArray := (Lang.Wire.encodePackage lPkg).getD .empty

/-- A natural as the bytes of a state slot of type `nat`. -/
def natBytes (n : Nat) : ByteArray := (Lang.Wire.encodeData .nat (.nat n)).getD .empty

/-- The founder installs the package; its cell is ROM, at its content id. -/
def lInstall : Call Digest := fCall wGenesis [] (.install lBytes)
def lId : Digest := romIdOf Xd.env { kind := kindPackage, discipline := .rom, slots := [(0, lBytes)] }
def lW1 : World Digest := (staged wGenesis lInstall).1

/-- The founder creates a data object judged by the package's law, `n = 0`. -/
def lCreate : Call Digest := fCall lW1 [lId] (.create none [lId] [(stateBase, natBytes 0)])
def lObj : Digest := cellIdOf Xd.env (txIdOf Xd lCreate) 0
def lW2 : World Digest := (staged lW1 lCreate).1

def lLog : List (Step Digest) := (staged wGenesis lInstall).2 ++ (staged lW1 lCreate).2

/-- The founder writes `n := v`, pinning the object and the package. -/
def lWrite (v : Nat) : Call Digest := fCall lW2 [lObj, lId] (.write lObj [(0, some (natBytes v))] none)

/-- The law term `bounded` the package holds, and the package's fields. -/
def lLaw : Lang.Term := Lang.Std.bounded (.record [("n", .nat)]) "n" 5
def lFields : List (Lang.Label × Lang.Term) := [("bounded", lLaw), ("set", Lang.Std.setMethod [("n", .nat)])]

/-! ## The unjudged kernel -/

/-- The deployed program with a `judge` that admits every step. -/
def Xu : Ctx Digest := { Xd with program := { Xd.program with judge := fun _ _ _ _ _ _ => .ok () } }

/-- **The unjudged kernel**: every field that reads the program reads `Xu`, so no law judges a write,
a law change, a birth or an invoke's new state (TOPLEVEL-SPEC §3.FLOOR `unjudgedKernel`). -/
def unjudged (d : ByteArray → ByteArray) : System Digest :=
  { deployed d with
    X := Xu
    receive := receive Xu
    recordedBy := recordedBy Xu
    submit := submit Xu
    follow := Command.step Xu Codec.Deployed.digestCodec
      ⟨Host.Deployed.world, World.steps, d, Host.Deployed.c.worldBytesMax⟩
    settle := Command.settleOf Xu
    handle := Host.handle Xu }

/-! ## The cancel run's inputs -/

/-- The founder cancels its `issue 1000` (never submitted), signed by its current key. -/
def cSig : ByteArray := Ed25519.sign (wSeed "f0") (Xd.cancelMessage vIssue)

/-- The log the writer records for the cancel (`Receive.cancel`: a refusal `cancelled`). -/
def cancelLog : List (Step Digest) :=
  match Receive.cancel Xd wGenesis vIssue cSig with
  | .recorded _ r _ => [.refusal r]
  | _ => []

/-- The World the writer records it on. -/
def cWorld : World Digest :=
  match Receive.cancel Xd wGenesis vIssue cSig with
  | .recorded _ _ w => w
  | _ => wGenesis

def cCb : ByteArray := Xd.callBytes vIssue

/-- `cancel CALL` at the log phase of its second catch-up, the writer having said `refused cancelled`
(`saidCancelledBit` in `tried`). -/
def cKb : ByteArray :=
  (Command.State.bytes ⟨["cancel".toUTF8, (Text.toHex cCb).toUTF8], 2,
    [Text.u64 cWorld.steps, .empty, Text.u64 0, Text.u64 (cWorld.height + sMe.window),
      Text.u64 Command.saidCancelledBit]⟩).getD .empty

/-- The writer's page at its tip: no events, its step count and chain. -/
def cRes : ByteArray :=
  ByteArray.mk #[Status.ok.code] ++
    ((Host.Page.bytes { steps := cWorld.steps, chain := Xd.env.bytes cWorld.chain } cWorld.steps
      cWorld.height 0 .empty .empty).toOption.getD .empty)

end Nanodregg.Spec
