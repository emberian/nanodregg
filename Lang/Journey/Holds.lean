/-
# Lang.Journey.Holds — §HV: a row of a `holds` relation is backed by value the run moves (LANG-90, DESIGN-TYPES §3.1)

A Vault package, written in the surface: relation `vault` keyed by `n` whose value holds a LEG,
`(holds leg)`. `deposit {amount pay grant n}` inserts a row holding `amount` of the vault's asset and
transfers `pay` from the depositor into the vault object (through the depositor's grant);
`depositUnpaid {amount n}` inserts with no transfer; `deposit2 {each total grant n m}` inserts two
rows of `each` under one transfer of `total`; `withdraw {amount n}` retracts row `n` and pays `amount`
out to the vault's owner; `withdrawUnpaid {n}` retracts and pays nothing.

HV1 a paid deposit is admitted; HV2 an unpaid one is refused `legUnfunded vault` and HV3 a half-paid
one too; HV4 two legs of 3 under one transfer of 6 are admitted (the check sums per asset); HV5 a
withdraw that pays the leg is admitted; HV6 one that pays nothing is refused `legStranded vault` and
HV7 one that pays short too, the row and the value staying where they were. Before LANG-90 HV2, HV3,
HV6 and HV7 are admitted: the object holds value no row names, or a row names value the object never
received.
-/
import Lang.Journey.Effect

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

def vaultSurface : String := "
(package
  (doc \"Rows of vault hold legs of value; every insert is paid in and every retract paid out.\")
  (state (rec (asset digest) (owner digest)))
  (rel vault (key (n nat)) (val (rec (leg (rec (amount nat) (asset digest))))) (limit 16) (retract) (holds leg))
  (method deposit (arg (rec (amount nat) (grant digest) (n nat) (pay nat))) (calls (transfer)) (edits 1)
      (effect (moves 1000))
    (done state
      (insert vault (record (n arg.n)) (record (leg (record (amount arg.amount) (asset state.asset)))))
      (transfer (amount arg.pay) (dst (AcctRef of (record (asset state.asset) (owner req.self))))
                (once (none bytes)) (src (AcctRef of (record (asset state.asset) (owner req.agent))))
                (via (some digest arg.grant)))))
  (method depositUnpaid (arg (rec (amount nat) (n nat))) (edits 1)
    (done state
      (insert vault (record (n arg.n)) (record (leg (record (amount arg.amount) (asset state.asset)))))))
  (method deposit2 (arg (rec (each nat) (grant digest) (m nat) (n nat) (total nat))) (calls (transfer)) (edits 2)
      (effect (moves 1000))
    (done state
      (insert vault (record (n arg.n)) (record (leg (record (amount arg.each) (asset state.asset)))))
      (insert vault (record (n arg.m)) (record (leg (record (amount arg.each) (asset state.asset)))))
      (transfer (amount arg.total) (dst (AcctRef of (record (asset state.asset) (owner req.self))))
                (once (none bytes)) (src (AcctRef of (record (asset state.asset) (owner req.agent))))
                (via (some digest arg.grant)))))
  (method withdraw (arg (rec (amount nat) (n nat))) (calls (transfer)) (edits 1) (effect (moves 1000))
    (done state
      (retract vault (record (n arg.n)))
      (transfer (amount arg.amount) (dst (AcctRef of (record (asset state.asset) (owner state.owner))))
                (once (none bytes)) (src (AcctRef of (record (asset state.asset) (owner req.self))))
                (via (none digest)))))
  (method withdrawUnpaid (arg (rec (n nat))) (edits 1)
    (done state (retract vault (record (n arg.n))))))
"

def vaultPackage : Except String Package :=
  match Surface.readPackage vaultSurface with
  | .ok p => .ok p
  | .error e => .error s!"{repr e}"

def hvRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let X := ctxWith prog
  let mut r := r0
  let p ← match vaultPackage with
    | .ok p => pure p
    | .error e => return note r s!"HV0 the Vault does not read: {e}" false
  let some pb := Wire.encodePackage p | return note r "HV0 the Vault has no bytes" false
  let ix (m : Label) : Nat := p.methods.idxOf m
  let some vd := Row.find? "vault" p.rels | return note r "HV0 no vault relation" false
  let mk (r : Run) (m : Sim.Member) (ids : List D) (body : Body D) : Run × String × Option D :=
    let (r', v, t) := go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host (m.id :: ids)) body)
    (r', v, t.bind fun t => (createdIds t).head?)
  let (r1, v1, pkg?) := mk r a [] (.install pb)
  r := r1
  let some pkg := pkg? | return note r s!"HV0 install the Vault: {v1}" false
  let (r2, vα, α?) := mk r a [] (.issue 100)
  r := r2
  let some α := α? | return note r s!"HV0 issue α: {vα}" false
  let some seed := stateSlots (recordRow p.state) [("asset", .digest (Sim.dc.bytes α)), ("owner", .digest (Sim.dc.bytes b.id))] 0
    | return note r "HV0 no seed bytes" false
  let (r3, vx, ox?) := mk r a [pkg, α, b.id] (.create (some pkg) [] seed)
  r := r3
  let some ox := ox? | return note r s!"HV0 create the vault object: {vx}" false
  let acct (owner asset : D) : D := accountId X owner asset
  let mut setup : List String := [v1, vα, vx]
  for owner in [ox, a.id, b.id] do
    let (r', v, _) := mk r a [α] (.account α owner)
    r := r'; setup := setup ++ [v]
  let (r4, vf, _) := mk r a [α, acct a.id α] (.transfer (.well α) (.of a.id α) 50 none none)
  r := r4; setup := setup ++ [vf]
  let (r5, vg, g?) := mk r a [ox, acct a.id α] (.grant (acct a.id α) ox [.transfer 100] none)
  r := r5; setup := setup ++ [vg]
  let some g := g? | return note r s!"HV0 grant: {vg}" false
  let bal (w : World D) (owner : D) : Int := (lvBalance w (acct owner α)).getD (-1)
  let present (w : World D) (n : Nat) : Bool := (hole_pinAt ox w 0 vd (.record [("n", .nat n)])).any fun (s, _) =>
    (rowAt Sim.env w.rows s).isSome
  let w0 := r.st.host
  r := note r s!"HV0 A installs the Vault (rel vault … (holds leg)), issues α, creates V \{asset α, owner B}, opens the three accounts, funds A with 50 and grants V transfer 100 on A's account: {setup}; A holds {bal w0 a.id} α, V {bal w0 ox}"
    (setup.all (· == "admitted") && bal w0 a.id == 50 && bal w0 ox == 0)
  let cells := [pkg, ox, α, g, acct ox α, acct a.id α, acct b.id α]
  let inv (r : Run) (m : Label) (arg : Data) (rows : List (RowSlot D × D) := []) : Run × String :=
    match (do let (_, sg) ← (resolveMethod (D := D) p (ix m)).toOption; Wire.encodeData sg.arg arg) with
    | none => (r, "no bytes")
    | some x =>
      let (r', v, _) := go prog r (signedRows r.st a (Sim.S.pinsFor r.st.host (a.id :: cells)) rows []
        (.invoke ox (ix m) x 100000 none))
      (r', v)
  let gD : Data := .digest (Sim.dc.bytes g)
  let refused (v why : String) : Bool := v.startsWith "refused program" && (v.splitOn why).length > 1
  -- HV1 a paid deposit
  let (r6, v6) := inv r "deposit" (.record [("amount", .nat 10), ("grant", gD), ("n", .nat 0), ("pay", .nat 10)])
  let w1 := r6.st.host
  r := note r6 s!"HV1 A deposits 10 into row 0 paying 10: {v6}; V holds {bal w1 ox} α, row 0 present {present w1 0}"
    (v6 == "admitted" && bal w1 ox == 10 && bal w1 a.id == 40 && present w1 0)
  -- HV2 an unpaid deposit
  let (r7, v7) := inv r "depositUnpaid" (.record [("amount", .nat 10), ("n", .nat 1)])
  r := note r s!"HV2 A inserts row 1 holding 10 and pays nothing: {v7}; row 1 present {present r7.st.host 1}"
    (refused v7 "legUnfunded vault" && !present r7.st.host 1 && bal r7.st.host ox == 10)
  -- HV3 a half-paid deposit
  let (r8, v8) := inv r "deposit" (.record [("amount", .nat 10), ("grant", gD), ("n", .nat 1), ("pay", .nat 5)])
  r := note r s!"HV3 A inserts row 1 holding 10 and pays 5: {v8}; V holds {bal r8.st.host ox} α (still 10)"
    (refused v8 "legUnfunded vault" && !present r8.st.host 1 && bal r8.st.host ox == 10)
  -- HV4 two legs of 3 under one transfer of 6: the check sums per asset
  let (r9, v9) := inv r "deposit2" (.record [("each", .nat 3), ("grant", gD), ("m", .nat 3), ("n", .nat 2), ("total", .nat 6)])
  let w4 := r9.st.host
  r := note r9 s!"HV4 A inserts rows 2 and 3 holding 3 each under one transfer of 6: {v9}; V holds {bal w4 ox} α"
    (v9 == "admitted" && bal w4 ox == 16 && present w4 2 && present w4 3)
  -- HV5 a withdraw that pays the leg out
  let (r10, v10) := inv r "withdraw" (.record [("amount", .nat 10), ("n", .nat 0)]) (hole_pinAt ox r.st.host 0 vd (.record [("n", .nat 0)]))
  let w5 := r10.st.host
  -- HV6 a withdraw that pays nothing (from the World before HV5)
  let (r11, v11) := inv r "withdrawUnpaid" (.record [("n", .nat 0)]) (hole_pinAt ox r.st.host 0 vd (.record [("n", .nat 0)]))
  -- HV7 a withdraw that pays short
  let (r12, v12) := inv r "withdraw" (.record [("amount", .nat 4), ("n", .nat 0)]) (hole_pinAt ox r.st.host 0 vd (.record [("n", .nat 0)]))
  r := note r10 s!"HV5 A withdraws row 0 paying its 10 to B: {v10}; V holds {bal w5 ox} α (was 16), B {bal w5 b.id}, row 0 present {present w5 0}"
    (v10 == "admitted" && bal w5 ox == 6 && bal w5 b.id == 10 && !present w5 0)
  r := note r s!"HV6 A retracts row 0 (holding 10) paying nothing: {v11}; row 0 present {present r11.st.host 0}, V holds {bal r11.st.host ox} α (still 16)"
    (refused v11 "legStranded vault" && present r11.st.host 0 && bal r11.st.host ox == 16)
  r := note r s!"HV7 A retracts row 0 (holding 10) paying 4: {v12}; row 0 present {present r12.st.host 0}, V holds {bal r12.st.host ox} α (still 16)"
    (refused v12 "legStranded vault" && present r12.st.host 0 && bal r12.st.host ox == 16)
  return r

def holdsSession : Run :=
  let X := ctxWith langProgram
  let fk := [("hv-a".toUTF8, "hv-a-next".toUTF8), ("hv-b".toUTF8, "hv-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 12) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"HV genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    hvRows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

initialize register { name := "holds", run := pure holdsSession }

end Nanodregg.Lang.Journey
