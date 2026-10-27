/-
# Hosting.Proofs.BellRow — the answered row is the kept answer (B8's join, HOSTING-44)

`SocketStrong.delivered_answer_committed_strong` says an `ok` answer for `(r, t)` journaled, on the
member's own World, a call invoking the bell at `sh.answer` whose argument bytes ARE
`answerDatum r t`. This module says what that call writes; the bell is the deployed Bell (`Lang.Bell.shapeOk`,
checked by the resident of the configured object's package, HOSTING-45):

* `lifetime_invoke_kept`: the `t` the resident invoked for `r` is the kept answer: the one the
  process started with (`m.kept`, read back from the volume) or one it kept, with `keep r t true`,
  in the same lifetime.
* `answered_row_is_kept_answer`: every run of that journaled call's invoke, at the bell's package
  read as a Bell, that returned (on any view, any state, any request: the run a commit of the call
  performs, `ObjectStep.invoke`), writes exactly two row acts: the upsert of `rings` at the ring's
  key `(r.ringer, r.notBefore)` to `answered (some (ask t))` with capture `ask {text := r.text, to :=
  r.to}`, and the retract of `pending` there; the request was the resident's; its calls are, by the
  ring's aim: none, no call; some `{cand, method, target, via}`, exactly the forward of `t` to the
  target (HOSTING-53); and the upsert is the `answer` step of the log row's machine
  (`Lang.Std.WaitingStep`) over the row the kernel found at its key.

The join: the strong theorem's args, decoded at `answerArgTy` (`Lang.Wire.decodeData_eq_ok_iff`),
are the run's argument (`Lang.Bell.answer_run`); the method at `sh.answer` is labelled `answer`
(`describe_shape`, carried by the strong theorem); the guard is the waiting guard
(`Lang.Bell.bell_monitored`).

* `answered_row_committed` (premise form, over those conclusions; HOSTING-47): when the frames `S`
  follow was handed took its World from a base that held no entry at the call's id to one that
  journals it, the call's bytes are among the calls those frames carried and the call was received
  and admitted at a World holding the bell's package, and the World it left HOLDS `rings` at the
  ring's key `answeredVal` (with the aim as captured) and no `pending` row there (`Lang.Bell.answer_commits`, through
  `Committed.journal_committed`); or two different inputs among the call's bytes and the frames'
  calls share one `domTx` digest (`CollidesAmong` over that explicit list).

That `pk` is the Bell is the resident's own check, not a premise: `Resident.bellCore` refuses
`notBell` at the first describe unless the description's `core` line (the package cell's bytes)
decodes to a package with `Lang.Bell.shapeOk` (HOSTING-45), and `describe_shape` carries it.

Not claimed, and named: that follow's base World lacked the entry, or is canonical (premises of
`answered_row_committed`; the freshness premise is what makes the base's own entry no answer); that every `answered` row of the bell came from the resident's socket (a
converse: another holder of the resident's key could invoke `answer`, the custody question,
HOSTING-32). The composite, the resident's own call taken to its commit inside one statement, is not
stated: there the call is chosen by the conclusion, and a hash disjunct over a chosen target is a
collision the statement may pick (the census's red shape).
-/
import Hosting.Proofs.SocketStrong
import Lang.Proofs.Bell
import Lang.Proofs.BellCommit
import Hosting.Proofs.Committed

namespace Nanodregg.Hosting.Proofs.Lifetime

open Nanodregg.Hosting Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentRun

/-! ## The invoked answer is a kept answer -/

theorem keptAfter_some : ∀ {k : Option (Ring × ByteArray)} {es : List Ev} {r : Ring} {t : ByteArray},
    keptAfter k es = some (r, t) → k = some (r, t) ∨ Ev.keep r t true ∈ es
  | k, [], r, t, h => .inl h
  | k, e :: es, r, t, h => by
    cases e with
    | keep r' t' b =>
      cases b with
      | true =>
        rcases keptAfter_some (k := some (r', t')) (es := es) h with h' | h'
        · cases h'; exact .inr (List.mem_cons_self ..)
        · exact .inr (List.mem_cons_of_mem _ h')
      | false =>
        rcases keptAfter_some (k := k) (es := es) h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_cons_of_mem _ h')
    | forget b =>
      cases b with
      | true =>
        rcases keptAfter_some (k := none) (es := es) h with h' | h'
        · cases h'
        · exact .inr (List.mem_cons_of_mem _ h')
      | false =>
        rcases keptAfter_some (k := k) (es := es) h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_cons_of_mem _ h')
    | cmd c x =>
      rcases keptAfter_some (k := k) (es := es) h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')
    | ask r' q x =>
      rcases keptAfter_some (k := k) (es := es) h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')
    | say s =>
      rcases keptAfter_some (k := k) (es := es) h with h' | h'
      · exact .inl h'
      · exact .inr (List.mem_cons_of_mem _ h')

/-- What a tick invokes is the answer it was handed (`m.kept`) or one it kept itself. -/
theorem tick_invoke_kept {w : Where} {m : Mem} {es : List Ev} {a : Tick}
    (h : Runs (tickP w m) es a) {sh : Shape} {r : Ring} {t : ByteArray}
    {x : Except String Reply} (he : Ev.cmd (.invoke sh r t) x ∈ core es) :
    m.kept = some (r, t) ∨ Ev.keep r t true ∈ core es := by
  obtain ⟨-, -, -, hinv⟩ := tick_counts h
  have hmem : (r, t) ∈ invokes (core es) := List.mem_filterMap.mpr ⟨_, he, rfl⟩
  rcases hinv with hn | ⟨r', t', hrt, hc⟩
  · rw [hn] at hmem; cases hmem
  · rw [hrt, List.mem_singleton] at hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
    rcases hc with ⟨_, _, _, _, hd, _⟩ | ⟨_, _, _, _, _, pre, post, _, _, _, hc⟩
    · exact .inl (decideTick_answer_kept hd)
    · exact .inr (by rw [hc]; simp)

/-- **The resident invokes only kept answers**: in one process's lifetime, an invoke of `(r, t)`
is of the answer the process started with or one it kept (`keep r t true`) in the same lifetime. -/
theorem lifetime_invoke_kept {w : Where} :
    ∀ {m : Mem} {ess : List (List Ev)}, Ticks w m ess → ∀ {sh : Shape} {r : Ring} {t : ByteArray}
      {x : Except String Reply}, Ev.cmd (.invoke sh r t) x ∈ core ess.flatten →
      m.kept = some (r, t) ∨ Ev.keep r t true ∈ core ess.flatten := by
  intro m ess hl
  induction hl with
  | nil => intro sh r t x he; simp at he
  | last hr => intro sh r t x he; simpa using tick_invoke_kept hr (by simpa using he)
  | @next m₁ m' es₁ rest hr _ ih =>
    intro sh r t x he
    rw [List.flatten_cons, core_append] at he ⊢
    rcases List.mem_append.mp he with he | he
    · rcases tick_invoke_kept hr he with h | h
      · exact .inl h
      · exact .inr (List.mem_append_left _ h)
    · rcases ih he with h | h
      · rw [kept_follows hr] at h
        rcases keptAfter_some h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_append_left _ (mem_core_keep h'))
      · exact .inr (List.mem_append_right _ h)

end Nanodregg.Hosting.Proofs.Lifetime

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The join -/

/-- `Lang.Bell.toData` is injective. -/
private theorem toData_inj {a b : Option Lang.Data} (h : Lang.Bell.toData a = Lang.Bell.toData b) : a = b := by
  cases a <;> cases b <;> simp_all [Lang.Bell.toData]

/-- **The answered row is the kept answer** (B8's join). In one resident process's lifetime (the
strong theorem's premises), an invoke of `answer` for `(r, t)` that came back `ok`: `t` is a kept
answer of `r` (`lifetime_invoke_kept`), and follow's World at its `ok` journals a call of the
member's invoking the bell `o` at `sh.answer` with argument bytes `args`, where the bell's package
`P` reads as `pk` with `sh.answer` labelled `answer`, and `pk` IS the Bell (`Lang.Bell.shapeOk`: the
resident read the description's `core` line and checked it, HOSTING-45, `describe_shape`). Every
run of that invoke that returned (the program at `P` on any view that reads `P` as `pk`, any state,
any request) signed by the resident, makes no call when the ring is unaimed and exactly the forward
of `t` to the aim's target (at its method, through the Bell's grant `via`, with `proposalData cand
via t`) when it is aimed, and writes exactly: `rings` at the ring's key `(r.ringer, r.notBefore)`
upserted to `answered (some (ask t))` with capture `ask {text := r.text, to := r.to}`, and `pending`
retracted there; and that upsert is the `answer` step of the log row's machine over the row the
kernel found at the key. -/
theorem answered_row_is_kept_answer [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D}
    {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D} {w : Resident.Where} {m : Resident.Mem}
    {ess : List (List Resident.Ev)}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (h : ResidentRun.Ticks w m ess) (hm : m.shape = none) (hk : Lifetime.KeptOk m.kept)
    (hs : StdioLeg X dc B me w.conf (Resident.core ess.flatten))
    {sh : Resident.Shape} {r : Resident.Ring} {t : ByteArray} {rr : Resident.Reply}
    (hi : Resident.Ev.cmd (.invoke sh r t) (.ok rr) ∈ Resident.core ess.flatten)
    (hok : rr.exit = CommandExit.ok.code) (rc : Lang.ReceiptCheck) :
    (m.kept = some (r, t) ∨ Resident.Ev.keep r t true ∈ Resident.core ess.flatten) ∧
    ∃ (o g : D) (wf wb : World D) (u : Unsigned D) (sig : ByteArray) (hh : Nat) (td : D) (args : ByteArray)
      (P : D) (pc : Cell) (pk : Lang.Package) (sg : Lang.Sig),
      X.digestOf w.conf.bell = some o ∧ u.member = me.member ∧
      u.body = .invoke o sh.answer args invokeBudget (some g) ∧
      wf.journalAt X.env (txIdOf X ⟨u, sig⟩) = some (hh, td) ∧
      X.decodeCall (X.callBytes ⟨u, sig⟩) = some ⟨u, sig⟩ ∧ Reach X dc B me wb wf ∧
      PackageAt X wb o P pc ∧ Lang.readPackage (worldLook X.env wb) P = .ok pk ∧
      Lang.resolveMethod (D := D) pk sh.answer = .ok ("answer", sg) ∧ Lang.Bell.shapeOk pk = true ∧
      (∀ {look : Pinned D} {rv : RowView D} {state : Slots} {req : Req D}
        {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat},
        X.digestOf (X.env.bytes P) = some P → Lang.readPackage look P = .ok pk →
        (Lang.program X.env.bytes X.digestOf rc).run look rv P state sh.answer args req budget =
          .ok (s, calls, rows, used) →
        ((r.to = none ∧ calls = []) ∨
          ∃ (a : Resident.Aim) (tD vD : D) (ab : ByteArray), r.to = some a ∧
            X.digestOf a.target = some tD ∧ X.digestOf a.via = some vD ∧
            Lang.Wire.encodeData Lang.Bell.proposalTy (Lang.Bell.proposalData a.cand a.via t) = some ab ∧
            calls = [.invoke tD a.method ab 100000 (some vD)]) ∧
        (∃ b, Lang.readState X.digestOf (Lang.recordRow Lang.Bell.S) state =
          .ok (.record [("open", .bool b), ("resident", .digest (X.env.bytes req.agent))])) ∧
        (∃ kb vb, Lang.keyBytes Lang.Bell.rings (Lang.Bell.keyData r.notBefore r.ringer) = some kb ∧
          Lang.Wire.encodeData Lang.Bell.rings.val (Lang.Bell.answeredVal r.text t (r.to.map Resident.Aim.data)) = some vb ∧
          rows = [(.row ⟨req.self, 1, kb⟩, .upsert 0 vb), (.row ⟨req.self, 0, kb⟩, .retract)]) ∧
        ∃ (lib : List Lang.Term) (sd : Lang.Data) (es' : List (Lang.Edit D)), rows = es'.map (fun x => (x.slot, x.act)) ∧
          ∀ x ∈ es', x.label = "rings" → ∃ old, Lang.guardOld X.digestOf rv req.self x = .ok old ∧
            Lang.Std.WaitingStep lib Lang.Bell.resumer (some Lang.Bell.patience) Lang.Bell.withdraw (Lang.reqData X.env.bytes req) sd x.data old) := by
  refine ⟨Lifetime.lifetime_invoke_kept h hi, ?_⟩
  obtain ⟨o, g, wf, u, sig, hh, td, args, ho, -, hmem, hbody, henc, hj, hrt, wb, P, pc, pk, sg, hwb, hpat, hrp,
    hres, hshape⟩ := delivered_answer_committed_strong hX h hm hk hs hi hok
  refine ⟨o, g, wf, wb, u, sig, hh, td, args, P, pc, pk, sg, ho, hmem, hbody, hj, hrt, hwb, hpat, hrp, hres, hshape, ?_⟩
  intro look rv state req budget s calls rows used hid hlook hrun
  have hdec : Lang.Wire.decodeData Lang.Bell.answerArg args =
      .ok (Lang.Bell.answerData r.notBefore r.text r.ringer t (r.to.map Resident.Aim.data)) :=
    Lang.Wire.decodeData_eq_ok_iff.mpr henc
  obtain ⟨nb, x, k, y, to, kb, vb, hdec', -, -, hst, hcalls, hkb, -, hvb, hrows⟩ :=
    Lang.Bell.answer_run X.env.bytes X.digestOf hid hlook hshape hres hrun
  rw [hdec] at hdec'
  simp only [Lang.Bell.answerData, Except.ok.injEq, Lang.Data.record.injEq, List.cons.injEq, Prod.mk.injEq,
    Lang.Data.nat.injEq, Lang.Data.bytes.injEq, Lang.Data.digest.injEq, and_true, true_and] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl, hto⟩ := hdec'
  obtain rfl := toData_inj hto.symm
  obtain ⟨S, es', -, hrows', hmon⟩ := Lang.Bell.bell_monitored X.env.bytes X.digestOf hid hlook hshape hrun
  refine ⟨?_, hst, ⟨kb, vb, hkb, hvb, hrows⟩, S.lib, S.state, es', hrows', hmon⟩
  rcases hcalls with ⟨hn, hc⟩ | ⟨c, mt, tg, vi, tD, vD, ab, hsome, htD, hvD, hab, hc⟩
  · exact .inl ⟨Option.map_eq_none_iff.mp hn, hc⟩
  · obtain ⟨a, ha, hd⟩ := Option.map_eq_some_iff.mp hsome
    obtain ⟨c', m', o', v'⟩ := a
    simp only [Resident.Aim.data, Lang.Bell.aimData, Lang.Data.record.injEq, List.cons.injEq, Prod.mk.injEq,
      Lang.Data.nat.injEq, Lang.Data.digest.injEq, and_true, true_and] at hd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hd
    exact .inr ⟨_, tD, vD, ab, ha, htD, hvD, hab, hc⟩

/-! ## The commit -/

/-- **The answered row is on the World that committed the call** (HOSTING-44's commit half, cv
01a16821-5835; restated HOSTING-47). Premise form, over what `answered_row_is_kept_answer`
concludes: follow's frames, with results `S`, take the World from `wb`, which held NO journal entry
at `c`'s id, to the settling World `wf`, which does; at `wb` the bell `o` holds package `P` in a ROM
cell, `P` reads as a Bell `pk` labelling `m` `answer`; `c` invokes `o` at `m` with `args`, its
canonical bytes read back as itself. Then `c`'s bytes are among the calls those frames carried
(`pathCalls S`) and `c` was received at a World `v` where the bell still holds `P` and admitted
from canonical rows to `v'`, the entry being `(v.height + 1, turnDigest)` of its Turn, and `v'` holds
at `rings` of `o`, at the ring's key, `answeredVal x y` and no `pending` row there
(`Lang.Bell.answer_commits`), the arguments decoding to that ring's `answerData`; or two different
inputs among `c`'s bytes and the frames' calls share one `domTx` digest (`CollidesAmong` over that
explicit list).

Stated over the call as a premise, not inside `answered_row_is_kept_answer`'s existential: there
the call is one the statement chooses. Canonical journal and rows at `wb` are premises (follow's
base is not proved canonical here). -/
theorem answered_row_committed [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D} {dc : Codec.Stream D}
    {B : Thin.Base (World D)} {me : Self D} {rc : Lang.ReceiptCheck}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (hXp : X.program = Lang.program X.env.bytes X.digestOf rc)
    {S : List ByteArray} {wb wf : World D} (hr : ReachOn X dc B me S wb wf) {o P : D} {pc : Cell}
    (hpat : PackageAt X wb o P pc) (hjc : wb.JournalCanon X.env) (hrc : wb.RowsCanon X.env)
    (hid : X.digestOf (X.env.bytes P) = some P) {pk : Lang.Package}
    (hrp : Lang.readPackage (worldLook X.env wb) P = .ok pk) (hs : Lang.Bell.shapeOk pk = true)
    {m : Nat} {sg : Lang.Sig} (hres : Lang.resolveMethod (D := D) pk m = .ok ("answer", sg))
    {c : Call D} {args : ByteArray} {budget : Nat} {via : Option D}
    (hb : c.unsigned.body = .invoke o m args budget via) (hc : X.decodeCall (X.callBytes c) = some c)
    (hfresh : wb.journalAt X.env (txIdOf X c) = none)
    {e : Nat × D} (hj : wf.journalAt X.env (txIdOf X c) = some e) :
    (X.callBytes c ∈ pathCalls S ∧ ∃ (v v' : World D) (t : Turn D), ∃ nb x k y to kb vb ver,
        PackageAt X v o P pc ∧ receive X v c = .ok t ∧ World.admit X.env v t = .ok v' ∧
        e = (v.height + 1, turnDigest X.env t) ∧
        Lang.Wire.decodeData Lang.Bell.answerArg args = .ok (Lang.Bell.answerData nb x k y to) ∧
        Lang.keyBytes Lang.Bell.rings (Lang.Bell.keyData nb k) = some kb ∧
        Lang.Wire.encodeData Lang.Bell.rings.val (Lang.Bell.answeredVal x y to) = some vb ∧
        rowAt X.env v'.rows (.row ⟨o, 1, kb⟩) = some (.row 0 vb ver) ∧
        rowAt X.env v'.rows (.row ⟨o, 0, kb⟩) = none) ∨
      CollidesAmong X.env.hash ((X.callBytes c :: pathCalls S).map (domTx, ·)) := by
  rcases journal_committed hX absorbStep_packageAt packageAt_atGenesis hr hpat hjc hrc hc hfresh hj with
    ⟨hbS, v, v', t, hqv, hrv, hrcv, ha, rfl⟩ | h2
  · have hqv' := hqv
    obtain ⟨hlo, hpl, -⟩ := hqv'
    obtain ⟨cl, hl, -, hpo⟩ : ∃ cl, v.live X.env o = some cl ∧ cl.kind = kindObject ∧
        packageOf X o cl = .ok (some P) := by
      rcases hlo with h | ht
      · exact h
      · -- a retired bell (KERNEL-70) derives no invoke: the invoke's run reads it live
        obtain ⟨_, _, _, _, _, _, _, hir, -⟩ :=
          Lang.dispatched_invoke_rows hrcv (dispatched_of_signed (X := X) (w := v) hb)
        have h0 := invokeRun_live hir
        have hn : v.live X.env o = none := by unfold World.live; rw [ht]
        rw [hn] at h0; cases h0
    have hrp' : Lang.readPackage (worldLook X.env v) P = .ok pk :=
      (readPackage_live (hpl.trans hpat.2.1.symm)).trans hrp
    obtain ⟨nb, x, k, y, to, kb, vb, ver, h1, h2, h3, h4, h5⟩ :=
      Lang.Bell.answer_commits hXp hrcv hb ⟨cl, hl, hpo⟩ hid rfl hrp' hs hres ha hrv
    exact .inl ⟨hbS, v, v', t, nb, x, k, y, to, kb, vb, ver, hqv, hrcv, ha, rfl, h1, h2, h3, h4, h5⟩
  · exact .inr h2

end Nanodregg.Hosting.Proofs.Socket
