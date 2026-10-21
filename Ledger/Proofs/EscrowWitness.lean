/-
# Ledger.Proofs.EscrowWitness — two runs of the escrow that the kernel evaluates

`escrow_runs_deployed` bounds the payouts of every `Runs` of the node's program; this module shows
the premise is met and the bound attained, by kernel reduction, not by a sim. On the node's codec
(`Codec.Digest`, `Lang.program Digest.bytes Digest.ofBytes?`), an object whose package cell holds
`encodePackage escrow`, born `open`, is deposited into by its depositor and then released by them:

* `escrow_runs_witness`: both runs succeed and both judges admit, so the pair is a `Runs` of the
  deployed program, and it returns exactly one payout.
* `escrow_second_release_refused` (tooth): releasing again from the `released` slots is still a
  successful run returning a payout; the judge refuses every transition out of those slots. The
  bound is the judge's.
* `escrow_link_bites` (tooth): the admitted release from `held`, repeated on the same `held` slots,
  would pay twice; only the link (the next run reads what the last wrote) rules it out.

How the kernel reaches it: `load` is mutual well-founded recursion (`load`/`loadAll`,
`termination_by`), which `decide +kernel` cannot unfold, and decoding the package bytes in the
kernel does not fit in memory. So the closure is loaded by `load`'s equation (`load_one`, one
package, no imports), the package is read from its INSTALL bytes (`readPackage_installed` over
`encodePackage escrow = some b`, no decode), `runSetup` is assembled from its pieces
(`setup_eq`), and only what follows (the machine run, the extraction, `stateSlots`, `callsOf`, the
law) is left to `decide +kernel`; nothing is evaluated by compiled code.
-/
import Ledger.Proofs.EscrowRun


namespace Nanodregg.Ledger.Proofs
open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Ledger.Escrow

section
variable {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}

theorem load_one {look : Pinned D} {fuel : Nat} {idb : ByteArray} {id : D} {p : Package} {r : Loaded × Nat}
    (hid : digestOf idb = some id) (hp : readPackage look id = .ok p) (himp : p.imports = [])
    (hadm : admitPackage digestOf idb p ⟨[], [], []⟩ [] = .ok r) :
    load digestOf look (fuel + 1) idb ⟨[], [], []⟩ = .ok r := by
  unfold load
  rw [loadUsing.eq_def]
  simp only [indexIn, idOf, hid, hp, himp]
  rw [loadAllUsing.eq_def]
  exact hadm

theorem admit_one {idb : ByteArray} {p : Package} (hc : p.checkWith [] = .ok ())
    (hl : checkLits digestOf p = .ok ()) :
    admitPackage digestOf idb p ⟨[], [], []⟩ [] =
      .ok (⟨[idb], [p.body.relocate fun i => ([] : List Nat).getD i 0], [p]⟩, 0) := by
  simp [admitPackage, ifacesAt, hc, hl]

private theorem setup_eq {look : Pinned D} {rv : RowView D} {pkg : D} {state : Slots} {method : Nat}
    {args : ByteArray} {r : Req D} {L : Loaded} {g : Nat} {p : Package} {ℓ : Label} {sg : Sig} {sd ad wd : Data}
    (hq : reqOk bytesOf r = true) (hl : load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hm : resolveMethod (D := D) p method = .ok (ℓ, sg))
    (hs : readState digestOf (recordRow p.state) state = .ok sd)
    (ha : Wire.decodeData sg.arg args = .ok ad) (had : digestsOk digestOf ad.digests = true)
    (hw : readsData digestOf p.rels rv r.self sg.reads = .ok wd) :
    runSetup bytesOf digestOf look rv pkg state method args r = .ok
      { lib := L.lib, pkgs := L.pkgs.length, g, rels := p.rels, label := ℓ, row := recordRow p.state,
        ty := resultTy p.state sg.calls (editTy p.rels) sg.edits, state := sd, args := ad,
        reads := wd, term := apply4 g ℓ, env := [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] } := by
  simp [runSetup, runSetupWith, hq, hl, hp, hm, hs, ha, had, hw, bind, Except.bind, pure, Except.pure]

private theorem judge_of_one {look : Pinned D} {L : Loaded} {g : Nat} {p : Package} {pkg : D}
    {old new : Slots} {r : Req D} {o n : Data} {ℓ : Label}
    (hq : reqOk bytesOf r = true) (hl : load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (ho : readState digestOf (recordRow p.state) old = .ok o)
    (hn : readState digestOf (recordRow p.state) new = .ok n) (hls : p.laws = [ℓ])
    (hlaw : runLaw L.lib (.get (.ref g) ℓ) o n (reqData bytesOf r) = .ok (.ok ())) :
    Lang.judge bytesOf digestOf look (some pkg) [] old new r = .ok () := by
  simp [Lang.judge, judgeOne, judgeOneWith, hq, hl, hp, ho, hn, hls, hlaw, bind, Except.bind, pure, Except.pure]

private theorem ok_of_check {α ε : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : (match x with | .ok b => decide (b = a) | .error _ => false) = true) : x = .ok a := by
  split at h
  · simp at h; subst h; rfl
  · cases h

end

private abbrev DD := Codec.Digest
private def dg (n : UInt8) : DD := ⟨⟨Array.replicate 32 n⟩, by simp [ByteArray.size]⟩
@[irreducible] private def pkgB : ByteArray := (Wire.encodePackage escrow).getD .empty
private def pcell : Cell := { kind := kindPackage, discipline := .rom, slots := [(0, pkgB)] }
private def pid : DD := dg 11
private def look : Pinned DD := fun i => if i = pid then .ok (some pcell) else .ok none
private abbrev bo : DD → ByteArray := Codec.Digest.bytes
private abbrev dO : ByteArray → Option DD := Codec.Digest.ofBytes?

private theorem pkgB_eq : Wire.encodePackage escrow = some pkgB := by
  have h := escrow_encodes
  unfold pkgB
  cases he : Wire.encodePackage escrow with
  | none => rw [he] at h; cases h
  | some b => rfl

private theorem hread : readPackage look pid = .ok escrow := by
  refine readPackage_installed (cell := pcell) (b := pkgB) ?_ (by simp [pcell, Slots.get]) pkgB_eq
  simp [readKind, look, pcell]

private theorem hchecks : escrow.checkWith [] = .ok () := by
  have := escrow_checks
  split at this
  · assumption
  · cases this

private theorem hlits : checkLits dO escrow = .ok () := by
  have h : (checkLits dO escrow matches .ok ()) = true := by decide +kernel
  split at h
  · assumption
  · cases h

private def L0 : Loaded := ⟨[bo pid], [escrow.body.relocate fun i => ([] : List Nat).getD i 0], [escrow]⟩

private theorem hload : load dO look closureDepthMax (bo pid) ⟨[], [], []⟩ = .ok (L0, 0) :=
  load_one (fuel := 7) (Codec.Deployed.digestOf_bytes pid) hread rfl (admit_one hchecks hlits)

private def terms : Terms := ⟨5, bo (dg 1), bo (dg 2), bo (dg 3), bo (dg 4), "n".toUTF8⟩
private def s0 : Slots := (seed terms).getD []
private def slotsAt (p : Label) : Slots :=
  match stateD terms p with
  | .record fs => (stateSlots (recordRow escrow.state) fs 0).getD []
  | _ => []
private def noRows : RowView DD := ⟨fun _ _ => [], fun _ _ => .ok []⟩
private def gr : DD := dg 5
private def a1 : ByteArray := (depositArgs (bo gr)).getD .empty
private def r1 : Req DD := { agent := dg 4, principal := dg 4, self := dg 9, notBefore := 0, validUntil := 0, occasion := .invoke 0 }

private theorem hq1 : reqOk bo r1 = true := by decide +kernel
private theorem hs0 : readState dO (recordRow escrow.state) s0 = .ok (stateD terms "open") := by rfl
private theorem ha1 : Wire.decodeData depositArg a1 = .ok (.record [("grant", .digest (bo gr))]) := by rfl
private theorem hw0 : readsData dO escrow.rels noRows (dg 9) [] = .ok (.record []) := by rfl

private theorem run1 : (match runMeasured bo dO look noRows pid s0 0 a1 r1 100000 with
    | .ok (s, _, _, _, _) => decide (s = slotsAt "held") | .error _ => false) = true := by
  have hS1 := setup_eq (bytesOf := bo) (digestOf := dO) (look := look) (rv := noRows) (pkg := pid)
    (method := 0) hq1 hload rfl rfl hs0 ha1 (by decide +kernel) hw0
  unfold runMeasured runMeasuredWith
  rw [hS1]
  decide +kernel


private def a2 : ByteArray := noArgs.getD .empty
private def r2 : Req DD := { agent := dg 4, principal := dg 4, self := dg 9, notBefore := 0, validUntil := 0, occasion := .invoke 2 }
private theorem hq2 : reqOk bo r2 = true := by decide +kernel
private theorem hs1 : readState dO (recordRow escrow.state) (slotsAt "held") = .ok (stateD terms "held") := by rfl
private theorem hs2 : readState dO (recordRow escrow.state) (slotsAt "released") = .ok (stateD terms "released") := by rfl
private theorem ha2 : Wire.decodeData unit a2 = .ok (.record []) := by rfl

private theorem run2 : (match runMeasured bo dO look noRows pid (slotsAt "held") 2 a2 r2 100000 with
    | .ok (s, _, _, _, _) => decide (s = slotsAt "released") | .error _ => false) = true := by
  have hS := setup_eq (bytesOf := bo) (digestOf := dO) (look := look) (rv := noRows) (pkg := pid)
    (method := 2) hq2 hload rfl rfl hs1 ha2 (by decide +kernel) hw0
  unfold runMeasured runMeasuredWith
  rw [hS]
  decide +kernel

private theorem law_ok {o n rq : Data} (h : (runLaw L0.lib (.get (.ref 0) "escrow") o n rq matches .ok (.ok ())) = true) :
    runLaw L0.lib (.get (.ref 0) "escrow") o n rq = .ok (.ok ()) := by
  split at h
  · assumption
  · cases h

private theorem judge1 : Lang.judge bo dO look (some pid) [] s0 (slotsAt "held") r1 = .ok () :=
  judge_of_one hq1 hload rfl hs0 hs1 rfl (law_ok (by decide +kernel))

private theorem judge2 : Lang.judge bo dO look (some pid) [] (slotsAt "held") (slotsAt "released") r2 = .ok () :=
  judge_of_one hq2 hload rfl hs1 hs2 rfl (law_ok (by decide +kernel))

private theorem judge_live {old new : Slots} {r : Req DD}
    (h : Lang.judge bo dO look (some pid) [] old new r = .ok ()) :
    (Lang.program bo dO).judge look (some pid) [] old new r = .ok () := by
  change judgeContextual bo dO look (some pid) [] old new r = .ok ()
  unfold judgeContextual
  simp only [judgeOneContextual_leaf_closed (show dO (bo pid) = some pid from Codec.Deployed.digestOf_bytes pid) hread rfl rfl]
  exact h

private theorem run_ok {state : Slots} {m : Nat} {args : ByteArray} {r : Req DD} {s' : Slots}
    (h : (match runMeasured bo dO look noRows pid state m args r 100000 with
      | .ok (s, _, _, _, _) => decide (s = s') | .error _ => false) = true) :
    ∃ calls rows used, (Lang.program bo dO).run look noRows pid state m args r 100000 = .ok (s', calls, rows, used) := by
  split at h
  · rename_i s c rw t n hm
    simp only [decide_eq_true_eq] at h
    subst h
    refine ⟨c, rw, t, ?_⟩
    change (runMeasuredLive bo dO look noRows pid state m args r 100000).map _ = _
    rw [runMeasuredLive_leaf_closed (show dO (bo pid) = some pid from Codec.Deployed.digestOf_bytes pid) hread rfl rfl, hm]
    rfl
  · cases h

/-- **The chain's premise is met, and its bound is reached** at the node's program: an escrow object
whose package cell holds `encodePackage escrow`, born `open` (amount 5, four distinct parties), is
deposited into by its depositor and then released by them. Both runs evaluate in the kernel's own
reduction and both judges admit, so this is a `Runs` of `Host.Deployed.X`'s program, and it returns
exactly one payout: `escrow_runs_deployed`'s premise is satisfiable and its `≤ 1` is attained. -/
theorem escrow_runs_witness : ∃ (pkg : Codec.Digest) (state : Slots) (runs : List (List (Body Codec.Digest))),
    Runs (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program pkg escrow state runs ∧
      payoutCalls runs = 1 := by
  obtain ⟨c1, w1, u1, h1⟩ := run_ok run1
  obtain ⟨c2, w2, u2, h2⟩ := run_ok run2
  refine ⟨pid, s0, [c1, c2], .cons hread h1 (judge_live judge1) (fun _ => rfl) (.cons hread h2 (judge_live judge2) (fun _ => rfl) (.nil _)), ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx1⟩ := escrow_run_deployed hread h1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hx2⟩ := escrow_run_deployed hread h2
  rcases hx1 with ⟨-, -, _, _, _, -, -, -, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> try cases h
  rcases hx2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, _, -, rfl⟩ <;> try cases h
  simp [payoutCalls, isPayoutCall]

private theorem run3 : (match runMeasured bo dO look noRows pid (slotsAt "released") 2 a2 r2 100000 with
    | .ok (s, _, _, _, _) => decide (s = slotsAt "released") | .error _ => false) = true := by
  have hS := setup_eq (bytesOf := bo) (digestOf := dO) (look := look) (rv := noRows) (pkg := pid)
    (method := 2) hq2 hload rfl rfl hs2 ha2 (by decide +kernel) hw0
  unfold runMeasured runMeasuredWith
  rw [hS]
  decide +kernel

/-- **Tooth: a second payout is a successful run the judge refuses.** After the witness's release,
the same release run again, from the `released` slots, still evaluates and returns a payout (the
method does not read its phase); what keeps it out of every `Runs` is the judge, which refuses
every transition out of those slots (`escrow_judge_settled`). So `escrow_runs_one_payout`'s bound
is the judge's, on the deployed program, not a property of the runs alone. -/
theorem escrow_second_release_refused : ∃ (look : Pinned Codec.Digest) (rv : RowView Codec.Digest)
    (pkg : Codec.Digest) (state : Slots) (args : ByteArray) (r : Req Codec.Digest) (s : Slots)
    (calls : List (Body Codec.Digest)) (rows : List (RowSlot Codec.Digest × RowAct)) (used : Nat),
    readPackage look pkg = .ok escrow ∧
    (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program.run look rv pkg state
      release args r 100000 = .ok (s, calls, rows, used) ∧ payoutCalls [calls] = 1 ∧
    ∀ (laws : List Codec.Digest) (new : Slots) (r' : Req Codec.Digest),
      (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program.judge look (some pkg)
        laws state new r' ≠ .ok () := by
  obtain ⟨c, w, u, h⟩ := run_ok run3
  refine ⟨look, noRows, pid, slotsAt "released", a2, r2, _, c, w, u, hread, h, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hx⟩ := escrow_run_deployed hread h
    rcases hx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, _, -, rfl⟩ <;> try cases h
    simp [payoutCalls, isPayoutCall]
  · intro laws new r' hj
    obtain ⟨o, n, ho, _, ha⟩ := escrow_step_admits_live (fun d => Codec.Deployed.digestOf_bytes d) hread hj
    rw [hs2] at ho
    cases ho
    exact escrow_absorbing (.inl ⟨_, rfl⟩) ha

/-- **Tooth for the link: an admitted payout step repeated is two payouts.** The witness's release
(from `held`, by the depositor) is a successful run of the node's program that the judge admits and
that returns a payout; taken twice, as a sequence whose second step reads the same `held` slots
again, it would pay twice. What rules that sequence out of `Runs` is the link alone: the slots the
first release wrote are not, key by key, the slots the second reads (they differ at the phase). So
`Runs`' `∀ k, next.get k = s.get k` (KERNEL's `invoke_next_run` for admitted invokes) is not idle. -/
theorem escrow_link_bites : ∃ (look : Pinned Codec.Digest) (rv : RowView Codec.Digest) (pkg : Codec.Digest)
    (state s : Slots) (args : ByteArray) (r : Req Codec.Digest) (calls : List (Body Codec.Digest))
    (rows : List (RowSlot Codec.Digest × RowAct)) (used : Nat),
    readPackage look pkg = .ok escrow ∧
    (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program.run look rv pkg state
      release args r 100000 = .ok (s, calls, rows, used) ∧
    (Codec.Deployed.ctx (Lang.program Codec.Digest.bytes Codec.Digest.ofBytes?)).program.judge look (some pkg)
      [] state s r = .ok () ∧
    payoutCalls [calls, calls] = 2 ∧ ¬ ∀ k, state.get k = s.get k := by
  obtain ⟨c, w, u, h⟩ := run_ok run2
  refine ⟨look, noRows, pid, slotsAt "held", slotsAt "released", a2, r2, c, w, u, hread, h, judge_live judge2, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hx⟩ := escrow_run_deployed hread h
    rcases hx with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, _, -, rfl⟩ <;> try cases h
    simp [payoutCalls, isPayoutCall]
  · intro hk
    have := hk (stateBase + 6)
    revert this
    decide +kernel

end Nanodregg.Ledger.Proofs
