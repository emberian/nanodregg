/-
# Lang.Proofs.StdOfferEscrowFuse — the escrow's fuse at the admitted Turn: both legs move with both retracts (PROT-8, LANG-77)

`Lang.Proofs.StdOfferEscrow` states each escrow method at `Lang.program`'s run: a returned take makes
ONE call, its own offer's leg to its peer's `payTo` (`escrow_take_run_sound`); a returned fuse makes
TWO, its own leg and the invoke of its peer's take on the judged deal (`escrow_fuse_run_sound`). This
module states the fuse at the grain the kernel commits: a signed call invoking `x'.fuse` of the escrow
package, which `receive` turns into a Turn `t` and `World.admit` admits to `w'`.

* `EscrowLegMoved … ad P`: party `P`'s run, on its argument `ad`, read its own pinned offer `o` (the one
  the deal names for `P`, `NamedKey`) and its peer's `q`, found them `JointOk`; `P`'s offer row is
  retracted in `t` and absent in `w'`; and `o`'s leg `{amount, asset}` LEFT `P`'s account in that asset
  (its balance in `w'` is exactly `amount` lower) and ARRIVED in the account of `q`'s `payTo` in that
  asset (exactly `amount` higher), each account keeping its denomination and floor.
* `escrow_fuse_admitted`: both parties' legs moved (`EscrowLegMoved` of the fuser `x'` on its argument
  `{keys, pair, theta, via}` and of its peer `y'` on the `{keys, pair, theta}` the fuser's run encoded for
  it), and every denomination's sum is what it was. That last conjunct IS `Kernel.Proofs.Value.admit_value`
  read at this Turn, not a second count of the two legs.

How the Turn holds the two transfers: the signed fuse is the walk's root (`dispatched_of_signed`); its
run made exactly its leg's transfer and the invoke of `y'`'s take (`escrow_fuse_run_sound`); each was
dispatched one level down (`dispatched_signed_children`); the take's run made exactly its one
transfer (`escrow_take_run_sound`), dispatched one level further (`dispatched_invoke_children`); and a
dispatched transfer's two balance writes are THE acts at their cells in the sealed Turn
(`Kernel.Receive.transfer_reads_back_dispatched`, through `duplicateEffect`). A fuse in which the
take or either transfer refuses derives no Turn; that branch is true of every refusal and is no
conjunct here.
-/
import Lang.Proofs.StdOfferEscrow
import Kernel.Proofs.LedgerNext

namespace Nanodregg.Lang.Std

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [Std.TransOrd D] [Std.LawfulEqOrd D] [DecidableEq D]

/-- **One escrow leg moved with its row** (PROT-8, at the admitted Turn `t` from `w` to `w'`). Party
`P`'s run, on its argument `ad` (the deal, with the fuser's `via` or without), read its own pinned
offer `{k, o}` (the one the deal names for `P`) and its peer's `{kq, q}`, found them `JointOk` and
their legs matching (`LegsMatch o q`, LANG-82: what `q` gives meets what `o` wants, and what `o` gives
meets what `q` wants); its offer row `⟨P, 0, kb⟩` is retracted in `t` and absent in `w'`;
`o.give = {amount, asset}` left `P`'s account in `asset` and arrived in the account of `q.payTo` in
`asset`, each balance moved by exactly `amount`. `o` and `q` are parameters, so a statement can say
which offers two parties' legs are. -/
def EscrowLegMoved (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D) (rc : Lang.ReceiptCheck)
    (X : Ctx D) (w w' : World D) (c : Call D) (t : Turn D) (pkg : D) (theta roles : List Label) (ol sl : Nat)
    (ad : Data) (P : D) (o q : Data) : Prop :=
  ∃ (keys pair th k kq : Data) (amt : Nat) (ab pb : ByteArray) (asset payTo : D) (kb : ByteArray),
    ad.field "keys" = some keys ∧ ad.field "pair" = some pair ∧ ad.field "theta" = some th ∧
    methodReads bytesOf digestOf rc (pinned X.env w c.unsigned.pins) pkg (escrowRels theta roles ol sl)
      (rowView X.env w c.unsigned) P ad offerRead offerRead =
      .ok (.record [("offer", .record [("p0", .inj "some" (.record [("key", k), ("val", .inj "some" o)]))]),
        ("peer", .record [("offer", .record [("p0", .inj "some" (.record [("key", kq), ("val", .inj "some" q)]))])])]) ∧
    NamedKey (bytesOf P) keys pair k ∧ JointOk (offerLabels theta) o q th ∧ LegsMatch o q ∧
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

/-- The peer's take: a take of `P` the walk dispatched (with a level below it), on an object of the
escrow package whose id reads back, moved its leg with its row (`EscrowLegMoved`) on the
`{keys, pair, theta}` its deal decodes to. -/
private theorem escrow_party {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {pkg : D} (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (ha : World.admit X.env w t = .ok w') (hrc : w.RowsCanon X.env)
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    {n : Nat} {wk : Walk D} {actor P : D} {caller : Option D} {deal : ByteArray} {b : Nat} {vP : Option D}
    (hd : Dispatched X w c (n + 1) wk actor caller (.invoke P offerTakeIx deal b vP))
    (hP : ∃ cl, w.live X.env P = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrP : digestOf (bytesOf P) = some P) :
    ∃ keys pair th o q, Wire.decodeData (offerTakeArg theta) deal =
        .ok (.record [("keys", keys), ("pair", pair), ("theta", th)]) ∧
      EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl
        (.record [("keys", keys), ("pair", pair), ("theta", th)]) P o q := by
  obtain ⟨cell, p, rq, new, calls, rows, used, hir, hrun, -, hcov⟩ := dispatched_invoke_rows hc hd
  obtain rfl := invokeRun_pkg hir hP hidK
  have hrun' := hrun
  rw [hX] at hrun'
  obtain ⟨keys, pair, th, k, o, kq, q, amt, ab, pb, self', asset, payTo, kb, sb, vb, hdec, hm, hn, -, hj, hl, hg, hpb,
    h1, h2, h3, hcalls, hkb, -, -, hrows⟩ := escrow_take_run_sound bytesOf digestOf hR hid hp hrun'
  obtain ⟨hself, -, -⟩ := invokeRun_req hir
  rw [hself] at hm hn h1 hrows
  rw [hrP] at h1
  cases h1
  subst hcalls hrows
  obtain ⟨wk', ht⟩ := dispatched_invoke_children hc hd hir hrun 0 (by simp)
  obtain ⟨sv, dv, hs0, hd0, hs1, hd1⟩ := transfer_reads_back_dispatched hc ha ht
  obtain ⟨τ, hτ, hsτ, haτ⟩ := hcov (.row ⟨P, 0, kb⟩, .retract) (by simp)
  exact ⟨keys, pair, th, o, q, hdec, keys, pair, th, k, kq, amt, ab, pb, asset, payTo, kb,
    by simp [Data.field, Row.find?], by simp [Data.field, Row.find?], by simp [Data.field, Row.find?],
    hm, hn, hj, hl, hg, hpb, h2, h3, hkb, ⟨τ, hτ, hsτ, haτ⟩, admit_retract_row hrc ha hτ hsτ haτ, sv, dv, hs0, hd0, hs1, hd1⟩

/-- **A signed escrow fuse that the World admits moves both legs with both retracts** (PROT-8 under
LANG-77, the Turn grain; the escrow twin of `fuse_atomic`, `jointLaw_sound` and `invitation_once`). A
signed call invoking `x'.fuse` of the escrow package `offerEscrowPackageOf …`, its deal naming the pair
`{x', y'}` (digests `xb`, `yb`, each reading back), both objects of that one package, which
`receive` turns into `t` and `World.admit` admits from canonical cells and rows to `w'`: BOTH parties'
legs moved with their rows — the fuser `x'` on its own argument, its peer `y'` on the
`{keys, pair, theta}` the fuser's run ENCODED for it, one value (`EscrowLegMoved` of each: the offer row
the deal names retracted in `t` and absent in `w'`, the leg out of its party's account by exactly its
amount and into its peer offer's `payTo` account by exactly that amount); the two parties' offers are
ONE pair `ox`, `oy` — the offer `x'` read under its peer is the one `y'` consumed and vice versa — and
their legs match (`LegsMatch`, LANG-82): `x'` receives `oy.give` at `ox.payTo`, which meets `ox.want`,
and `y'` receives `ox.give` at `oy.payTo`, which meets `oy.want`; and every denomination's sum over
the World is unchanged (`admit_value`, read here, not recounted). Mutation P8j (the judge ignores the
legs) makes the `LegsMatch` conjuncts unprovable: LE7's unfair deal is admitted. Mutation P8d (the take pays
nothing: its call slot `none`) makes `escrow_take_run_sound`, read for the peer, false: no leg moves. -/
theorem escrow_fuse_admitted {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D} {rc : Lang.ReceiptCheck}
    {theta roles : List Label} {ol sl pt budget : Nat} {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {args : ByteArray} {b : Nat} {via : Option D} {pkg : D} {keys th v : Data}
    {xb yb : ByteArray} {x' y' : D}
    (hX : X.program = Lang.program bytesOf digestOf rc) (hc : receive X w c = .ok t)
    (hb : c.unsigned.body = .invoke x' offerFuseIx args b via)
    (hdec : Wire.decodeData (offerFuseArg theta) args =
      .ok (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]))
    (hxd : digestOf xb = some x') (hyd : digestOf yb = some y')
    (hid : digestOf (bytesOf pkg) = some pkg) (hidK : X.digestOf (X.env.bytes pkg) = some pkg)
    (hp : readPackage (pinned X.env w c.unsigned.pins) pkg = .ok (offerEscrowPackageOf theta roles ol sl pt budget))
    (hR : (offerRoleTy roles).wf = true)
    (hx : ∃ cl, w.live X.env x' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hy : ∃ cl, w.live X.env y' = some cl ∧ cl.slots.get slotPackage = some (X.env.bytes pkg))
    (hrx : digestOf (bytesOf x') = some x') (hry : digestOf (bytesOf y') = some y')
    (ha : World.admit X.env w t = .ok w') (hcan : w.Canon X.env) (hrc : w.RowsCanon X.env) :
    ∃ ox oy, EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl
      (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th), ("via", v)]) x' ox oy ∧
    EscrowLegMoved bytesOf digestOf rc X w w' c t pkg theta roles ol sl
      (.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]) y' oy ox ∧
    ∀ d, w'.valueSum d = w.valueSum d := by
  have hroot := dispatched_of_signed (X := X) (w := w) hb
  obtain ⟨cx, px, rqx, newx, callsx, rowsx, usedx, hirx, hrunx, -, hcov⟩ := dispatched_invoke_rows hc hroot
  obtain rfl := invokeRun_pkg hirx hx hidK
  have hrunx' := hrunx
  rw [hX] at hrunx'
  obtain ⟨keys', pair', th', v', k, o, kq, q, amt, ab, pb, self', asset, payTo, p, db, vg, kb, sb, vb, hdec', hm, hn, hj, hl,
    hg, hpb, h1, h2, h3, hpeer, hdb, -, hcalls, hkb, -, -, hrows⟩ := escrow_fuse_run_sound bytesOf digestOf hR hid hp hrunx'
  rw [hdec] at hdec'
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec'
  obtain ⟨hselfx, -, -⟩ := invokeRun_req hirx
  rw [hselfx] at hm hn h1 hrows hpeer
  rw [hrx] at h1
  cases h1
  subst hcalls hrows
  -- the fuser's leg: its transfer, the first call, dispatched one level down
  obtain ⟨wkx, htx⟩ := dispatched_signed_children hc hb hirx hrunx 0 (by simp)
  obtain ⟨svx, dvx, hsx0, hdx0, hsx1, hdx1⟩ := transfer_reads_back_dispatched hc ha htx
  obtain ⟨τx, hτx, hsτx, haτx⟩ := hcov (.row ⟨x', 0, kb⟩, .retract) (by simp)
  -- the peer's take: the second call, dispatched one level down; the peer is `y'`, since the peer
  -- `x'` itself would be `revisited` (`x'` is in the walk below the root)
  obtain ⟨wky, hdyd⟩ := dispatched_signed_children hc hb hirx hrunx 1 (by simp)
  have hpx : p ≠ x' := fun e => dispatched_invoke_fresh hc hdyd (by
    rcases dispatched_actor_visited hdyd with h | h
    · simp [Bounds.callDepthMax] at h
    · rw [e]; exact h)
  have hpy : p = y' := by
    obtain ⟨a0, b0, hf, -, hcase⟩ := peerOf_party bytesOf digestOf hpeer
    simp only [Data.field, Row.find?, ↓reduceIte] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rcases hcase with ⟨-, hb0⟩ | ⟨-, ha0⟩
    · rw [hyd] at hb0; exact (Option.some.inj hb0).symm
    · rw [hxd] at ha0; exact absurd (Option.some.inj ha0).symm hpx
  subst hpy
  obtain ⟨keys', pair', th', oy, qy, hdy, hmy⟩ := escrow_party (n := 2) hX hc ha hrc hid hidK hp hR hdyd hy hry
  have h1' := Wire.decodeData_eq_ok_iff.mpr hdb
  rw [h1'] at hdy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hdy
  obtain ⟨rfl, rfl, rfl⟩ := hdy
  -- the coupling (READ-LANGPROOFS F10): the offer X read under its peer is the one Y consumed, and
  -- the one Y read under its peer is X's own, as `jointLaw_sound` shows for `Std.offer`
  have hmy' := hmy
  obtain ⟨-, -, -, ky, kqy, -, -, -, -, -, -, -, -, -, hmry, -⟩ := hmy'
  have hne : x' ≠ p := fun e => hpx e.symm
  have hfy : (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]), ("theta", th)]).field
      "pair" = some (.record [("a", .digest xb), ("b", .digest yb)]) := by simp [Data.field, Row.find?]
  obtain ⟨px, Ax, Bx, hpx', hox, hqx, hRx⟩ := methodReads_offer hm
  obtain ⟨py, Ay, By, hpy', hoy, hqy, hRy⟩ := methodReads_offer hmry
  rw [hpeer] at hpx'
  cases hpx'
  rcases peer_of_pair hfy hxd hyd hrx hry hne (.inr rfl) hpy' with ⟨hyx, -⟩ | ⟨-, rfl⟩
  · exact absurd hyx.symm hne
  simp only [Data.record.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at hRx hRy
  obtain ⟨rfl, rfl⟩ := hRx
  obtain ⟨rfl, rfl⟩ := hRy
  rw [readsData_offer_args _ (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]),
    ("theta", th)]), hoy] at hqx
  rw [readsData_offer_args _ (Data.record [("keys", keys), ("pair", .record [("a", .digest xb), ("b", .digest yb)]),
    ("theta", th), ("via", v)]), hox] at hqy
  simp only [Except.ok.injEq, Data.record.injEq, List.cons.injEq, Prod.mk.injEq, Data.inj.injEq, true_and,
    and_true] at hqx hqy
  obtain ⟨-, rfl⟩ := hqx
  obtain ⟨-, rfl⟩ := hqy
  refine ⟨_, _, ⟨keys, .record [("a", .digest xb), ("b", .digest yb)], th, k, kq, amt, ab, pb, asset, payTo, kb,
    by simp [Data.field, Row.find?], by simp [Data.field, Row.find?], by simp [Data.field, Row.find?],
    hm, hn, hj, hl, hg, hpb, h2, h3, hkb, ⟨τx, hτx, hsτx, haτx⟩, admit_retract_row hrc ha hτx hsτx haτx,
    svx, dvx, hsx0, hdx0, hsx1, hdx1⟩, hmy, fun d => admit_value hcan ha d⟩

end Nanodregg.Lang.Std
