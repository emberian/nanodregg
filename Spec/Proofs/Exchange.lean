/-
# Spec.Proofs.Exchange — B2's exchange: a fuse that admits pays each party what its offer wants

**`Integrity.exchange S`** (TOPLEVEL-SPEC §3.2, PROT-8 under LANG-77/82): a signed fuse of an object
whose package is the system's exchange package (`S.exchange theta roles …`), which the system's
`receive` derives and its `admit` admits from canonical cells and rows, pays each party what its
offer wants: both legs move, each out of its party's account by exactly its amount and into the peer
offer's `payTo` account; the two offers are one pair and their legs match (`LegsMatch`: what each
party receives meets what its offer wants); each offer row is retracted in the Turn and absent after
it, so a leg moves once (no later fuse reads that offer); every denomination's sum is unchanged.

Premises, each needed: the program is the language over the system's own codec and receipt check
(`S.X.program = Lang.program S.X.env.bytes S.X.digestOf S.rc`: the package means nothing under
another program; `rfl` at `deployed`); the roles type is well formed; the fuse's shape (its body,
its decoded deal naming `{x', y'}`, both live objects of `pkg`, `pkg` read as `S.exchange …` at the
call's pins); canonical cells and rows (`Kept`'s canon, carried because the claim is generic in `D`);
every id reading back (`ofBytes_bytes`: true of every `Digest`, a premise only because the claim is
generic in `D`). None is false of the deployed system.

* `top_integrity_exchange`: `Lang.Std.escrow_fuse_admitted`.
* `floor_integrity_exchange`: the claim refuses `lazyExchange` (P8j, the judge of the legs `true`):
  a deployed run (`exUnfair`) ends in a fuse the deployed kernel admits that pays X 1 β where X's
  offer wants 7 β. Under the deployed package that fuse is refused `unfairLegs` (LE7 at the deployed
  `Ctx`).
* `inhabited_exchange`: under the deployed package a fair fuse (`exFair`: Y gives 7 β) is derived and
  admitted from a World the genesis World folds to, with every premise of the claim: the top
  theorem's case is reached.

Not here: `world/escrow/Escrow` is LEDGER's one-party escrow (`Ledger.Escrow.escrow`), whose promise
`escrow_invokes_one_payout` (at most one payout over an `ObjectHistory`) is another package and
another claim.
-/
import Spec.Sim.Exchange
import Lang.Proofs.StdOfferEscrowFuse
import Kernel.Proofs.Cells
import Kernel.Proofs.Rows
import Codec.Proofs.Digest

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Lang Nanodregg.Lang.Std

/-! ## The claim -/

section
variable {D : Type} [Ord D] [_root_.Std.TransOrd D] [_root_.Std.LawfulEqOrd D] [DecidableEq D]

/-- **B2, exchange. A fuse that admits pays each party what its offer wants, both legs, once.** A
signed call invoking `x'.fuse` of an object whose package `pkg` is `S.exchange theta roles …`, its
deal naming the pair `{x', y'}` (both live objects of `pkg`, every id reading back), which `S.receive`
derives into `t` and `S.admit` admits from canonical cells and rows to `w'`: both parties' legs moved
with their offer rows (`EscrowLegMoved` of `x'` on the fuser's argument and of `y'` on the deal the
fuser's run encoded for it), the two offers are one pair `ox`, `oy` whose legs match, and every
denomination's sum is unchanged. -/
def Integrity.exchange (S : System D) : Prop :=
  ∀ {theta roles : List Label} {ol sl pt budget : Nat} {w w' : World D} {c : Call D}
    {t : Turn D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D},
    S.X.program = Lang.program S.X.env.bytes S.X.digestOf S.rc → (offerRoleTy roles).wf = true →
    S.receive w c = .ok t → S.admit w t = .ok w' → w.Canon S.X.env → w.RowsCanon S.X.env →
    c.unsigned.body = .invoke x' offerFuseIx args b via →
    Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th),
        ("via", v)]) →
    S.X.digestOf xb = some x' → S.X.digestOf yb = some y' → S.X.digestOf (S.X.env.bytes pkg) = some pkg →
    S.X.digestOf (S.X.env.bytes x') = some x' → S.X.digestOf (S.X.env.bytes y') = some y' →
    readPackage (pinned S.X.env w c.unsigned.pins) pkg = .ok (S.exchange theta roles ol sl pt budget) →
    (∃ cl, w.live S.X.env x' = some cl ∧ cl.slots.get slotPackage = some (S.X.env.bytes pkg)) →
    (∃ cl, w.live S.X.env y' = some cl ∧ cl.slots.get slotPackage = some (S.X.env.bytes pkg)) →
    ∃ ox oy,
      EscrowLegMoved S.X.env.bytes S.X.digestOf S.rc S.X w w' c t pkg theta roles ol sl
        (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th),
          ("via", v)]) x' ox oy ∧
      EscrowLegMoved S.X.env.bytes S.X.digestOf S.rc S.X w w' c t pkg theta roles ol sl
        (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]) y' oy ox ∧
      ∀ dn, w'.valueSum dn = w.valueSum dn

end

/-! ## The top theorem -/

/-- **TOP (B2, exchange).** The deployed system (`Lang.Std.escrow_fuse_admitted`). -/
theorem top_integrity_exchange (d : ByteArray → ByteArray) : Integrity.exchange (deployed d) := by
  intro theta roles ol sl pt budget w w' c t args b via pkg keys th v xb yb x' y' hX hR hc ha hcan hrc hb hdec
    hxd hyd hid hrx hry hp hx hy
  exact escrow_fuse_admitted hX hc hb hdec hxd hyd hid hid hp hR hx hy hrx hry ha hcan hrc

/-! ## The lazy exchange is one term away from the deployed one -/

theorem escrowPackageWith_fair (theta roles : List Label) (a b c e : Nat) :
    escrowPackageWith escrowFairT theta roles a b c e = offerEscrowPackageOf theta roles a b c e := rfl

/-! ## Reading the runs -/

theorem okB_eq {ε α : Type} {e : Except ε α} (d : α) (h : okB e = true) : e = .ok (getOk e d) := by
  cases e with
  | ok a => rfl
  | error _ => cases h

theorem legsMatchB_of {o q : Data} (h : LegsMatch o q) : legsMatchB o q = true := by
  obtain ⟨ga, gb, wa, wb, qa, qb, va, vb, h1, h2, h3, h4, r1, l1, r2, l2⟩ := h
  subst r1 r2
  simp [legsMatchB, h1, h2, h3, h4, escrowLegD, l1, l2]

theorem readsFair_of {E : Type} {r : Except E Data} {k o kq q : Data}
    (hr : r = .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
      ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]))
    (h : LegsMatch o q) : readsFair r = true := by
  subst hr
  exact legsMatchB_of h

theorem ofBytes_bytes (x : Digest) : Digest.ofBytes? x.bytes = some x := by
  simp [Digest.ofBytes?, x.size_eq]

theorem eObjOf_live {w : World Digest} {pkg o : Digest} (h : eObjOf w pkg o = true) :
    ∃ cl, w.live Xd.env o = some cl ∧ cl.slots.get slotPackage = some (Xd.env.bytes pkg) := by
  unfold eObjOf at h
  cases hl : w.live Xd.env o with
  | none => rw [hl] at h; cases h
  | some cl => rw [hl] at h; exact ⟨cl, rfl, of_decide_eq_true h⟩

/-- A run whose facts hold: every premise of the claim at the run's fuse, at the deployed `Ctx`
(the facts' Bool, read as propositions; no case on the run's results). -/
theorem exFacts_sound {P : Package} {r : ExRun} (h : exFacts P r = true) :
    World.fold Xd.env wGenesis r.log = .ok (exW r) ∧ receive Xd (exW r) r.fuse = .ok (exT r) ∧
      World.admit Xd.env (exW r) (exT r) = .ok (exW' r) ∧ (exW r).Canon Xd.env ∧ (exW r).RowsCanon Xd.env ∧
      r.fuse.unsigned.body = .invoke r.x offerFuseIx r.fuseArg 1000000 none ∧
      Wire.decodeData (offerFuseArg eTheta) r.fuseArg = .ok (eDeal r.x r.y r.g) ∧
      readPackage (pinned Xd.env (exW r) r.fuse.unsigned.pins) r.pkg = .ok P ∧
      (∃ cl, (exW r).live Xd.env r.x = some cl ∧ cl.slots.get slotPackage = some (Xd.env.bytes r.pkg)) ∧
      (∃ cl, (exW r).live Xd.env r.y = some cl ∧ cl.slots.get slotPackage = some (Xd.env.bytes r.pkg)) := by
  unfold exFacts at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hf, hc⟩, ha⟩, hb⟩, henc⟩, hp⟩, hp'⟩, hx⟩, hy⟩ := h
  have hf' : World.fold Xd.env wGenesis r.log = .ok (exW r) := okB_eq wGenesis hf
  have hg : wGenesis.Canon Xd.env := by unfold wGenesis; exact receive_genesis_canon Xd _ _ _ _ _
  have hgr : wGenesis.RowsCanon Xd.env := by unfold wGenesis; exact receive_genesis_rowsCanon Xd _ _ _ _ _
  refine ⟨hf', okB_eq tMint hc, okB_eq (exW r) ha, fold_canon hg hf', fold_rowsCanon hgr hf',
    of_decide_eq_true hb, Wire.decodeData_eq_ok_iff.mpr (of_decide_eq_true henc), ?_, eObjOf_live hx, eObjOf_live hy⟩
  rw [okB_eq default hp, of_decide_eq_true hp']

/-! ## The floor: the judge that ignores the legs -/

/-- **The unfair run**: the claim's premises hold at `exUnfair`'s fuse under the lazy package, and the
offers X's run reads do not match (X wants 7 β, Y gives 1 β). -/
theorem run_unfair_fuse : (exFacts eLazy exUnfair && !readsFair (exReads exUnfair)) = true := by
  native_decide

/-- **FLOOR (B2, exchange).** The claim refuses the exchange whose judge ignores the legs: at the
deployed system with the lazy package, a fuse the kernel derives and admits from a World the genesis
World folds to pays X 1 β where X's offer wants 7 β. -/
theorem floor_integrity_exchange (d : ByteArray → ByteArray) : ¬ Integrity.exchange (lazyExchange d) := by
  intro h
  have hr := run_unfair_fuse
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hr
  obtain ⟨hfacts, hfair⟩ := hr
  obtain ⟨-, hc, ha, hcan, hrc, hb, hdec, hpk, hx, hy⟩ := exFacts_sound hfacts
  unfold exReads at hfair
  clear hfacts
  revert hc ha hcan hrc hb hdec hpk hx hy hfair
  generalize exW' exUnfair = w'
  generalize exT exUnfair = t
  generalize exW exUnfair = w
  generalize exUnfair.fuse = c
  generalize exUnfair.fuseArg = args
  generalize exUnfair.x = x
  generalize exUnfair.y = y
  generalize exUnfair.pkg = pkg
  generalize exUnfair.g = g
  intro hfair hc ha hcan hrc hb hdec hpk hx hy
  have hX : (lazyExchange d).X.program =
      Lang.program (lazyExchange d).X.env.bytes (lazyExchange d).X.digestOf (lazyExchange d).rc := rfl
  have hR : (offerRoleTy eRoles).wf = true := by decide
  obtain ⟨ox, oy, hmx, -, -⟩ := h (ol := 64) (sl := 1024) (pt := offerSessionPatience) (budget := 100000)
    hX hR hc ha hcan hrc hb hdec (ofBytes_bytes x) (ofBytes_bytes y) (ofBytes_bytes pkg)
    (ofBytes_bytes x) (ofBytes_bytes y) hpk hx hy
  obtain ⟨keys, pair, th, k, kq, amt, ab, pb, asset, payTo, kb, -, -, -, hm, -, -, hl, -⟩ := hmx
  have hm' : methodReads Xd.env.bytes Xd.digestOf (Protocol.Foreign.check Codec.Deployed.env Codec.Deployed.digestCodec)
      (pinned Xd.env w c.unsigned.pins) pkg (escrowRels eTheta eRoles 64 1024) (rowView Xd.env w c.unsigned) x
      (eDeal x y g) offerRead offerRead = _ := hm
  rw [readsFair_of hm' hl] at hfair
  cases hfair

/-! ## Inhabited: a fair fuse under the deployed package -/

/-- **The fair run**: the claim's premises hold at `exFair`'s fuse under the deployed package. -/
theorem run_fair_fuse : exFacts eFairPkg exFair = true := by
  native_decide

/-- **INHABITED (B2, exchange).** At the deployed system, from a World the genesis World folds to, a
signed fuse of an object of the deployed exchange package, its deal naming two live objects of that
package, is derived by `receive` and admitted by `admit` from canonical cells and rows: every
premise of the claim holds, so the top theorem's legs-moved case is reached. -/
theorem inhabited_exchange (d : ByteArray → ByteArray) :
    ∃ (l : List (Step Digest)) (w w' : World Digest) (c : Call Digest) (t : Turn Digest) (args : ByteArray)
      (x y pkg g : Digest),
      World.fold Xd.env wGenesis l = .ok w ∧ (deployed d).receive w c = .ok t ∧ (deployed d).admit w t = .ok w' ∧
      w.Canon Xd.env ∧ w.RowsCanon Xd.env ∧ c.unsigned.body = .invoke x offerFuseIx args 1000000 none ∧
      Wire.decodeData (offerFuseArg eTheta) args = .ok (eDeal x y g) ∧
      readPackage (pinned Xd.env w c.unsigned.pins) pkg =
        .ok ((deployed d).exchange eTheta eRoles 64 1024 offerSessionPatience 100000) ∧
      (∃ cl, w.live Xd.env x = some cl ∧ cl.slots.get slotPackage = some (Xd.env.bytes pkg)) ∧
      (∃ cl, w.live Xd.env y = some cl ∧ cl.slots.get slotPackage = some (Xd.env.bytes pkg)) := by
  obtain ⟨hf, hc, ha, hcan, hrc, hb, hdec, hpk, hx, hy⟩ := exFacts_sound run_fair_fuse
  revert hf hc ha hcan hrc hb hdec hpk hx hy
  generalize exW' exFair = w'
  generalize exT exFair = t
  generalize exW exFair = w
  generalize exFair.log = l
  generalize exFair.fuse = c
  generalize exFair.fuseArg = args
  generalize exFair.x = x
  generalize exFair.y = y
  generalize exFair.pkg = pkg
  generalize exFair.g = g
  intro hf hc ha hcan hrc hb hdec hpk hx hy
  exact ⟨l, w, w', c, t, args, x, y, pkg, g, hf, hc, ha, hcan, hrc, hb, hdec, hpk, hx, hy⟩

end Nanodregg.Spec
