/-
# Spec.Sim.Escrow — the lazy one-party escrow and the deployed escrow runs

The trivial component `Spec.Proofs.Escrow` refuses (`esLazy`: LEDGER's escrow whose law judges no
invoke and whose refund spends its own once key, `"refund"`, not the shared `"payout"`; the Ledger
journey's two-keys + skip-judge plant, as a package) and a run at the deployed `Ctx` from `wGenesis`:
the founder installs a package, issues α, opens its account and mints 20, creates an escrow object of
the package on terms {amount 5, asset α, the founder every party}, opens the escrow's account,
grants it `transfer 5` on its own account, deposits through that grant, and tops the escrow's
account up by 5. On the World that leaves, it signs a release, and on the World the release leaves,
a refund. Tooling (closure C9): what is computed of these is stated in `Spec.Proofs.Escrow`.
-/
import Spec.Sim.Run
import Ledger.Escrow

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Lang
open Nanodregg.Ledger.Escrow

/-! ## The lazy escrow -/

/-- A law that judges no invoke: births and adoptions still `open`, writes and law changes `frozen`. -/
def esLazyLaw : Term := Std.lawOf5 stateTy startC startC frozenC frozenC (fun _ => Std.okT)

/-- The methods, `refund` spending `"refund"`: the two payouts are two nullifiers. -/
def esLazyMethods : List (Label × Ty × List Ty × Term) :=
  methods.map fun (ℓ, A, ks, t) =>
    if ℓ = "refund" then
      (ℓ, A, ks, .lam (.record []) (.lam stateTy (.lam unit (.lam reqTy (resultT
        (callsT [someCallT T (transferT (ofT (rq "self")) (ofT (st "depositor")) noneD (someB (.bytes "refund".toUTF8)))])
        (.record (keep "refunded")))))))
    else (ℓ, A, ks, t)

/-- **The lazy escrow**: no law on its invokes, and two once keys for its two payouts. Either guard
alone keeps one payout (the law refuses `settled`; the shared key is the kernel's `spent`). -/
def esLazy : Package := { Std.pkgOf stateTy [("escrow", esLazyLaw)] esLazyMethods with doc := escrowDoc.toUTF8 }

/-! ## The run -/

/-- A call of the founder (current key) against `w`, window end `201 + i`, no row pins. -/
def esCall (w : World Digest) (i : Nat) (pins : List Digest) (b : Body Digest) : Call Digest :=
  let u : Unsigned Digest :=
    { world := w.origin, member := wMember, key := wKey, notBefore := 0, validUntil := 201 + i,
      pins := (wMember :: pins).map fun c => (c, pinOf Xd.env (w.entry Xd.env c)), maxCharge := 1000000,
      body := b }
  ⟨u, Ed25519.sign (wSeed "f0") (Xd.callMessage u)⟩

def esIdOf (w : World Digest) (c : Call Digest) : Digest :=
  match submit Xd w c with
  | .ok (t, _) => (createdIds t).headD Digest.zero
  | .error _ => Digest.zero

/-- The escrow's terms: 5 of `asset`, the founder depositor, beneficiary and arbiter. -/
def esTerms (asset : Digest) : Terms :=
  ⟨5, wMember.bytes, asset.bytes, wMember.bytes, wMember.bytes, "spec-escrow".toUTF8⟩

/-- A computed escrow run: the package, the escrow object, the denomination, the setup log and the
World it stages. -/
structure EsRun where
  pkg : Digest
  obj : Digest
  asset : Digest
  log : List (Step Digest)
  world : World Digest

def esRun (P : Package) : EsRun :=
  let c1 := esCall wGenesis 1 [] (.install ((Wire.encodePackage P).getD .empty))
  let pkg := esIdOf wGenesis c1
  let (w1, l1) := staged wGenesis c1
  let c2 := esCall w1 2 [] (.issue 100)
  let α := esIdOf w1 c2
  let (w2, l2) := staged w1 c2
  let aA := accountId Xd wMember α
  let (w3, l3) := staged w2 (esCall w2 3 [α] (.account α wMember))
  let (w4, l4) := staged w3 (esCall w3 4 [α, aA] (.transfer (.well α) (.of wMember α) 20 none none))
  let c5 := esCall w4 5 [pkg] (.create (some pkg) [] ((seed (esTerms α)).getD []))
  let e := esIdOf w4 c5
  let (w5, l5) := staged w4 c5
  let aE := accountId Xd e α
  let (w6, l6) := staged w5 (esCall w5 6 [α, e] (.account α e))
  let c7 := esCall w6 7 [aA, e] (.grant aA e [.transfer 5] none)
  let g := esIdOf w6 c7
  let (w7, l7) := staged w6 c7
  let (w8, l8) := staged w7 (esCall w7 8 [pkg, e, α, aA, aE, g]
    (.invoke e deposit ((depositArgs g.bytes).getD .empty) 100000 none))
  let (w9, l9) := staged w8 (esCall w8 9 [α, aA, aE] (.transfer (.of wMember α) (.of e α) 5 none none))
  { pkg, obj := e, asset := α, log := l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9, world := w9 }

/-- A payout invoke of the escrow (`release` or `refund`) against `w`. -/
def esPayout (r : EsRun) (w : World Digest) (i method : Nat) : Call Digest :=
  esCall w i [r.pkg, r.obj, r.asset, accountId Xd wMember r.asset, accountId Xd r.obj r.asset]
    (.invoke r.obj method (noArgs.getD .empty) 100000 none)

/-- Whether a result is `ok`, and its value (else `d`). -/
def esOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def esGet {ε α : Type} (e : Except ε α) (d : α) : α :=
  match e with
  | .ok a => a
  | .error _ => d

/-- One invoke step of an object history, computed: the call's Turn and World, `invokeRun`'s
(cell, package, request), the run's (state, calls, rows, used), the cell's laws. -/
structure EsStep where
  w : World Digest
  c : Call Digest
  t : Turn Digest
  w' : World Digest
  ir : Cell × Digest × Req Digest
  run : Slots × List (Body Digest) × List (RowSlot Digest × RowAct) × Nat
  laws : List Digest

def esStep (r : EsRun) (w : World Digest) (i method : Nat) : EsStep :=
  let c := esPayout r w i method
  let t := esGet (receive Xd w c) tMint
  let ir := esGet (invokeRun Xd (pinned Xd.env w c.unsigned.pins) c c.unsigned.member r.obj method none)
    (mintCell, r.pkg, reqOf c.unsigned r.obj r.obj .birth)
  { w, c, t, w' := esGet (World.admit Xd.env w t) w, ir,
    run := esGet (Xd.program.run (pinned Xd.env w c.unsigned.pins) (rowView Xd.env w c.unsigned) ir.2.1
      (stateOf ir.1) method (noArgs.getD .empty) ir.2.2 (min 100000 (poolOf c.unsigned.body))) ([], [], [], 0),
    laws := esGet (lawsOf Xd r.obj ir.1) [] }

/-- The step's facts: derived, admitted, an invoke of the object, `invokeRun`, the run and the laws
`ok` at the values held, and the package the step reads is `P`. -/
def esStepOk (P : Package) (r : EsRun) (method : Nat) (s : EsStep) : Bool :=
  esOk (receive Xd s.w s.c) && esOk (World.admit Xd.env s.w s.t) &&
    decide (s.c.unsigned.body = .invoke r.obj method (noArgs.getD .empty) 100000 none) &&
    esOk (invokeRun Xd (pinned Xd.env s.w s.c.unsigned.pins) s.c s.c.unsigned.member r.obj method none) &&
    esOk (Xd.program.run (pinned Xd.env s.w s.c.unsigned.pins) (rowView Xd.env s.w s.c.unsigned) s.ir.2.1
      (stateOf s.ir.1) method (noArgs.getD .empty) s.ir.2.2 (min 100000 (poolOf s.c.unsigned.body))) &&
    esOk (lawsOf Xd r.obj s.ir.1) &&
    decide (s.ir.2.1 = r.pkg) &&
    esOk (readPackage (pinned Xd.env s.w s.c.unsigned.pins) r.pkg) &&
    decide (esGet (readPackage (pinned Xd.env s.w s.c.unsigned.pins) r.pkg) default = P)

/-- A computed step's history entry (`ObjectStep.invoke`'s). -/
def esEntry (s : EsStep) : Pinned Digest × Option Digest × List Digest × Req Digest × Slots × Slots × List (Body Digest) :=
  (pinned Xd.env s.w s.c.unsigned.pins, some s.ir.2.1, s.laws, s.ir.2.2, stateOf s.ir.1, s.run.1, s.run.2.1)

/-- The floor's run (under the lazy escrow: a release, then a refund on the World it leaves, each
paying out) and the inhabited run (under the deployed escrow: a release). -/
def esUnfair : EsRun := esRun esLazy
def esFair : EsRun := esRun escrow

end Nanodregg.Spec
