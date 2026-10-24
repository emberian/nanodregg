/-
# Lang.Proofs.StdOfferEscrowFuse — the escrow's fuse at the admitted Turn: both legs move with both retracts (PROT-8)

`Lang.Proofs.StdOfferEscrow` states each escrow method at `Lang.program`'s run: a returned take makes
ONE call, its own offer's leg to its peer's `payTo` (`escrow_take_run_sound`). This module states the
fuse at the grain the kernel commits: a signed call invoking the matcher `z.fuse` of the escrow
package, which `receive` turns into a Turn `t` and `World.admit` admits to `w'`.

* `EscrowLegMoved … P`: party `P`'s take read its own pinned offer `o` (the one the deal names for
  `P`, `NamedKey`) and its peer's `q`, found them `JointOk`; `P`'s offer row is retracted in `t` and
  absent in `w'`; and `o`'s leg `{amount, asset}` LEFT `P`'s account in that asset (its balance in
  `w'` is exactly `amount` lower) and ARRIVED in the account of `q`'s `payTo` in that asset (exactly
  `amount` higher), each account keeping its denomination and floor.
* `escrow_fuse_admitted`: both parties' legs moved (`EscrowLegMoved` of `x'` and of `y'`, on the one
  `{keys, pair, theta}` the matcher forwarded), and every denomination's sum is what it was. That
  last conjunct IS `Kernel.Proofs.Value.admit_value` read at this Turn, not a second count of the
  two legs.

How the Turn holds the two transfers: the signed fuse is the walk's root (`dispatched_of_signed`), its
run made exactly the two `take` invokes (`fuse_calls`), each was dispatched one level down
(`dispatched_signed_children`), each take's run made exactly its one transfer
(`escrow_take_run_sound`), that transfer was dispatched one level further down
(`dispatched_invoke_children`), and a dispatched transfer's two balance writes are THE acts at their
cells in the sealed Turn (`Kernel.Receive.transfer_reads_back_dispatched`, through `duplicateEffect`).
A fuse in which either take or either transfer refuses derives no Turn; that branch is true of every
refusal and is no conjunct here.
-/
import Lang.Proofs.StdOfferEscrow
import Kernel.Proofs.LedgerNext

namespace Nanodregg.Lang.Std

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

/-- **One escrow leg moved with its row** (PROT-8, at the admitted Turn `t` from `w` to `w'`). Party
`P`'s take, on the forwarded `{keys, pair, theta}`, read its own pinned offer `{k, o}` (the one the
deal names for `P`) and its peer's `{kq, q}` and found them `JointOk`; its offer row `⟨P, 0, kb⟩` is
retracted in `t` and absent in `w'`; `o.give = {amount, asset}` left `P`'s account in `asset`
and arrived in the account of `q.payTo` in `asset`, each balance moved by exactly `amount`. -/
def EscrowLegMoved (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) (rc : Lang.ReceiptCheck)
    (X : Ctx D) (w w' : World D) (c : Call D) (t : Turn D) (pkg : D) (theta roles : List Label) (ol sl : Nat)
    (keys pair th : Data) (P : D) : Prop :=
  ∃ (k o kq q : Data) (amt : Nat) (ab pb : ByteArray) (asset payTo : D) (kb : ByteArray),
    methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (escrowRels theta roles ol sl)
      (rowView X.env w c.unsigned) P (.record [("keys", keys), ("pair", pair), ("theta", th)]) offerRead offerRead =
      .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
        ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
    NamedKey (bytesOf P) keys pair k ∧ JointOk (offerLabels theta) o q th ∧
    o.field "give" = some (.record [("amount", .nat amt), ("asset", .digest ab)]) ∧
    q.field "payTo" = some (.digest pb) ∧ digestOf ab = some asset ∧ digestOf pb = some payTo ∧
    keyBytes (escrowDecl theta roles ol) k = some kb ∧
    (∃ τ ∈ t.rows, τ.slot = .row ⟨P, 0, kb⟩ ∧ τ.act = .retract) ∧
    rowAt X.env w'.rows (.row ⟨P, 0, kb⟩) = none ∧
    ∃ sv dv, (w.live X.env ((AcctRef.of P asset).resolve X)).bind Value.ofCell = some sv ∧
      (w.live X.env ((AcctRef.of payTo asset).resolve X)).bind Value.ofCell = some dv ∧
      (w'.live X.env ((AcctRef.of P asset).resolve X)).bind Value.ofCell =
        some { sv with balance := sv.balance - amt } ∧
      (w'.live X.env ((AcctRef.of payTo asset).resolve X)).bind Value.ofCell =
        some { dv with balance := dv.balance + amt }

/-- One party: a take of `P` the walk dispatched (with a level below it), on an object of the escrow
package whose id reads back, moved its leg with its row (`EscrowLegMoved`) on the `{keys, pair,
theta}` its deal decodes to. -/
private theorem escrow_party {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {pkg : D} (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (ha : World.admit X.env w t = .ok w') (hrc : w.RowsCanon X.env)
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerEscrowPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    {n : Nat} {wk : Walk D} {actor P : D} {deal : ByteArray} {b : Nat} {vP : Option D}
    (hd : Dispatched X w c (n + 1) wk actor (.invoke P offerTakeIx deal b vP))
    (hP : ∃ cl, w.live X.env P = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrP : digestOf (bytesOf P) = some P) :
    ∃ keys pair th, Wire.decodeData (offerTakeArg theta) deal =
        .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl keys pair th P := by
  obtain ⟨cell, p, rq, new, calls, rows, used, hir, hrun, -, hcov⟩ := dispatched_invoke_rows hc hd
  obtain rfl := invokeRun_pkg hir hP hidK
  have hrun' := hrun
  rw [hX] at hrun'
  obtain ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, self', asset, payTo, kb, sb, vb, hdec, hm, hn, hj, hg, hpb,
    h1, h2, h3, hcalls, hkb, -, -, hrows⟩ := escrow_take_run_sound bytesOf digestOf hR hid hp hrun'
  obtain ⟨hself, -, -⟩ := invokeRun_req hir
  rw [hself] at hm hn h1 hrows
  rw [hrP] at h1
  cases h1
  subst hcalls hrows
  obtain ⟨wk', ht⟩ := dispatched_invoke_children hc hd hir hrun 0 (by simp)
  obtain ⟨sv, dv, hs0, hd0, hs1, hd1⟩ := transfer_reads_back_dispatched hc ha ht
  obtain ⟨τ, hτ, hsτ, haτ⟩ := hcov (.row ⟨P, 0, kb⟩, .retract) (by simp)
  exact ⟨keys, pair, th, hdec, k, o, kq, q, amt, ab, pb, asset, payTo, kb, hm, hn, hj, hg, hpb, h2, h3, hkb,
    ⟨τ, hτ, hsτ, haτ⟩, admit_retract_row hrc ha hτ hsτ haτ, sv, dv, hs0, hd0, hs1, hd1⟩

/-- **A signed escrow fuse that the World admits moves both legs with both retracts** (PROT-8, the
Turn grain; the escrow twin of `fuse_atomic`, `jointLaw_sound` and `invitation_once`). A signed call
invoking the matcher `z.fuse` of the escrow package `offerEscrowPackageOf …`, its arguments naming
`x` and `y` (digests `x'`, `y'`, each reading back), the three objects of that one package, which
`receive` turns into `t` and `World.admit` admits from canonical cells and rows to `w'`: the
forwarded deal IS one `{keys, pair, theta}` (a value, LANG-77; the matcher's run encoded it once for both takes), and on it BOTH parties' legs moved with their
rows (`EscrowLegMoved` of `x'` and of `y'`: each offer row the deal names retracted in `t` and absent
in `w'`, each leg out of its party's account by exactly its amount and into its peer offer's `payTo`
account by exactly that amount); and every denomination's sum over the World is unchanged
(`admit_value`, read here, not recounted). Mutation P8d (the take pays nothing: its call slot
`none`) makes `escrow_take_run_sound`, which this proof reads for each party, false: no leg moves. -/
theorem escrow_fuse_admitted {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl budget : Nat} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {z : D} {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {deal : Data} {vX vY : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke z offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("deal", deal), ("viaX", vX), ("viaY", vY), ("x", .digest xb), ("y", .digest yb)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerEscrowPackageOf theta roles ol sl budget))
    (hR : (offerRoleTy roles).wf = true)
    (hz : ∃ cl, w.live X.env z = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrx : digestOf (bytesOf x') = some x') (hry : digestOf (bytesOf y') = some y')
    (ha : World.admit X.env w t = .ok w') (hcan : w.Canon X.env) (hrc : w.RowsCanon X.env) :
    ∃ keys pair th,
      deal = .record [("keys", keys), ("pair", pair), ("theta", th)] ∧
      EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl keys pair th x' ∧
      EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl keys pair th y' ∧
      ∀ d, w'.valueSum d = w.valueSum d := by
  have hroot := dispatched_of_signed (X := X) (w := w) hb
  obtain ⟨cz, pz, rqz, newz, callsz, rowsz, usedz, hirz, hrunz, -, -⟩ := dispatched_invoke_rows hc hroot
  obtain rfl := invokeRun_pkg hirz hz hidK
  have hrunz' := hrunz
  rw [hX] at hrunz'
  obtain ⟨deal', xb', yb', vx, vy, x'', y'', vx', vy', db, hdec', hdx, hdy, -, -, hdb, hcz, rfl⟩ :=
    fuse_calls bytesOf digestOf (budget := budget) hid hp rfl rfl escrow_fuse_resolve rfl (by simp [Row.find?]) hrunz'
  rw [hdec] at hdec'
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq,
    Data.digest.injEq, true_and, and_true] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hdec'
  rw [hxd] at hdx
  rw [hyd] at hdy
  cases hdx
  cases hdy
  subst hcz
  obtain ⟨wkx, hdxd⟩ := dispatched_signed_children hc hb hirz hrunz 0 (by simp)
  obtain ⟨wky, hdyd⟩ := dispatched_signed_children hc hb hirz hrunz 1 (by simp)
  obtain ⟨keys, pair, th, hdx, hmx⟩ := escrow_party (n := 2) hX hc ha hrc hid hidK hp hR hdxd hx hrx
  obtain ⟨keys', pair', th', hdy, hmy⟩ := escrow_party (n := 2) hX hc ha hrc hid hidK hp hR hdyd hy hry
  have hdeal : deal = .record [("keys", keys), ("pair", pair), ("theta", th)] := by
    have h1 := Wire.decodeData_eq_ok_iff.mpr hdb
    rw [h1] at hdx
    exact Except.ok.inj hdx
  rw [hdx] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  exact ⟨keys, pair, th, hdeal, hmx, hmy, fun d => admit_value hcan ha d⟩

end Nanodregg.Lang.Std
