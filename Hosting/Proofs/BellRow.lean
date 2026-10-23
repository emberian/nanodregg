/-
# Hosting.Proofs.BellRow — the answered row is the kept answer (B8's join, HOSTING-44)

`SocketStrong.delivered_answer_committed_strong` says an `ok` answer for `(r, t)` journaled, on the
member's own World, a call invoking the bell at `sh.answer` whose argument bytes ARE
`answerDatum r t`. This module says what that call writes when the bell is the deployed Bell
(`Lang.Bell.shapeOk`, computed of the shipped core by `Lang.Journey`'s LBw):

* `lifetime_invoke_kept`: the `t` the resident invoked for `r` is the kept answer: the one the
  process started with (`m.kept`, read back from the volume) or one it kept, with `keep r t true`,
  in the same lifetime.
* `answered_row_is_kept_answer`: every run of that journaled call's invoke, at the bell's package
  read as a Bell, that returned (on any view, any state, any request: the run a commit of the call
  performs, `ObjectStep.invoke`), writes exactly two row acts: the upsert of `rings` at the ring's
  key `(r.ringer, r.notBefore)` to `answered (some (ask t))` with capture `ask {text := r.text}`, and
  the retract of `pending` there; the request was the resident's; and the upsert is the `answer`
  step of the log row's machine (`Lang.Std.WaitingStep`) over the row the kernel found at its key.

The join: the strong theorem's args, decoded at `answerArgTy` (`Lang.Wire.decodeData_eq_ok_iff`),
are the run's argument (`Lang.Bell.answer_run`); the method at `sh.answer` is labelled `answer`
(`describe_shape`, carried by the strong theorem); the guard is the waiting guard
(`Lang.Bell.bell_monitored`).

Not claimed, and named: that the World which commits the journaled call holds these rows after it
(the kernel's rows application, `rowsRun`, has no read-back lemma at a written slot); that a
journal entry at `txIdOf` was put by a commit of this call (`journalAt` is read here, the step that
wrote it is not reconstructed); that every `answered` row of the bell came from the resident's
socket (a converse: another holder of the resident's key could invoke `answer`, the custody
question, HOSTING-32).
-/
import Hosting.Proofs.SocketStrong
import Lang.Proofs.Bell

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
    ∀ {m : Mem} {es : List Ev}, Lifetime w m es → ∀ {sh : Shape} {r : Ring} {t : ByteArray}
      {x : Except String Reply}, Ev.cmd (.invoke sh r t) x ∈ core es →
      m.kept = some (r, t) ∨ Ev.keep r t true ∈ core es := by
  intro m es hl
  induction hl with
  | last hr => intro sh r t x he; exact tick_invoke_kept hr he
  | @next m₁ m' es₁ rest hr _ ih =>
    intro sh r t x he
    rw [core_append] at he ⊢
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

/-- **The answered row is the kept answer** (B8's join). In one resident process's lifetime (the
strong theorem's premises), an invoke of `answer` for `(r, t)` that came back `ok`: `t` is a kept
answer of `r` (`lifetime_invoke_kept`), and follow's World at its `ok` journals a call of the
member's invoking the bell `o` at `sh.answer` with argument bytes `args`, where the bell's package
`P` reads as `pk` with `sh.answer` labelled `answer`. If `pk` is the Bell (`Lang.Bell.shapeOk`), every
run of that invoke that returned (the program at `P` on any view that reads `P` as `pk`, any state,
any request) signed by the resident, makes no calls, and writes exactly: `rings` at the ring's key
`(r.ringer, r.notBefore)` upserted to `answered (some (ask t))` with capture `ask {text := r.text}`,
and `pending` retracted there; and that upsert is the `answer` step of the log row's machine over
the row the kernel found at the key. -/
theorem answered_row_is_kept_answer [Std.TransOrd D] [Std.LawfulEqOrd D] {X : Ctx D}
    {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D} {w : Resident.Where} {m : Resident.Mem}
    {es : List Resident.Ev}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (h : Lifetime.Lifetime w m es) (hm : m.shape = none) (hk : Lifetime.KeptOk m.kept)
    (hs : StdioLeg X dc B me w.conf (Resident.core es))
    {sh : Resident.Shape} {r : Resident.Ring} {t : ByteArray} {rr : Resident.Reply}
    (hi : Resident.Ev.cmd (.invoke sh r t) (.ok rr) ∈ Resident.core es)
    (hok : rr.exit = CommandExit.ok.code) (rc : Lang.ReceiptCheck) :
    (m.kept = some (r, t) ∨ Resident.Ev.keep r t true ∈ Resident.core es) ∧
    ∃ (o g : D) (wf wp : World D) (u : Unsigned D) (sig : ByteArray) (hh : Nat) (td : D) (args : ByteArray)
      (P : D) (pc : Cell) (pk : Lang.Package),
      X.digestOf w.conf.bell = some o ∧ u.member = me.member ∧
      u.body = .invoke o sh.answer args invokeBudget (some g) ∧
      wf.journalAt X.env (txIdOf X ⟨u, sig⟩) = some (hh, td) ∧
      PackageAt X wp o P pc ∧ Lang.readPackage (worldLook X.env wp) P = .ok pk ∧
      (Lang.Bell.shapeOk pk = true → ∀ {look : Pinned D} {rv : RowView D} {state : Slots} {req : Req D}
        {budget : Nat} {s : Slots} {calls : List (Body D)} {rows : List (RowSlot D × RowAct)} {used : Nat},
        X.digestOf (X.env.bytes P) = some P → Lang.readPackage look P = .ok pk →
        (Lang.program X.env.bytes X.digestOf rc).run look rv P state sh.answer args req budget =
          .ok (s, calls, rows, used) →
        calls = [] ∧
        (∃ b, Lang.readState X.digestOf (Lang.recordRow Lang.Bell.S) state =
          .ok (.record [("open", .bool b), ("resident", .digest (X.env.bytes req.agent))])) ∧
        (∃ kb vb, Lang.keyBytes Lang.Bell.rings (Lang.Bell.keyData r.notBefore r.ringer) = some kb ∧
          Lang.Wire.encodeData Lang.Bell.rings.val (Lang.Bell.answeredVal r.text t) = some vb ∧
          rows = [(.row ⟨req.self, 1, kb⟩, .upsert 0 vb), (.row ⟨req.self, 0, kb⟩, .retract)]) ∧
        ∃ (lib : List Lang.Term) (sd : Lang.Data) (es' : List (Lang.Edit D)), rows = es'.map (fun x => (x.slot, x.act)) ∧
          ∀ x ∈ es', x.label = "rings" → ∃ old, Lang.guardOld X.digestOf rv req.self x = .ok old ∧
            Lang.Std.WaitingStep lib Lang.Bell.resumer (some Lang.Bell.patience) (Lang.reqData X.env.bytes req) sd x.data old) := by
  refine ⟨Lifetime.lifetime_invoke_kept h hi, ?_⟩
  obtain ⟨o, g, wf, u, sig, hh, td, args, ho, -, hmem, hbody, henc, hj, wp, P, pc, pk, sg, hpat, hrp, hres⟩ :=
    delivered_answer_committed_strong hX h hm hk hs hi hok
  refine ⟨o, g, wf, wp, u, sig, hh, td, args, P, pc, pk, ho, hmem, hbody, hj, hpat, hrp, ?_⟩
  intro hshape look rv state req budget s calls rows used hid hlook hrun
  have hdec : Lang.Wire.decodeData Lang.Bell.answerArg args = .ok (Lang.Bell.answerData r.notBefore r.text r.ringer t) :=
    Lang.Wire.decodeData_eq_ok_iff.mpr henc
  obtain ⟨nb, x, k, y, kb, vb, hdec', -, -, hst, hcalls, hkb, -, hvb, hrows⟩ :=
    Lang.Bell.answer_run X.env.bytes X.digestOf hid hlook hshape hres hrun
  rw [hdec] at hdec'
  simp only [Lang.Bell.answerData, Except.ok.injEq, Lang.Data.record.injEq, List.cons.injEq, Prod.mk.injEq,
    Lang.Data.nat.injEq, Lang.Data.bytes.injEq, Lang.Data.digest.injEq, and_true, true_and] at hdec'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hdec'
  obtain ⟨S, es', -, hrows', hmon⟩ := Lang.Bell.bell_monitored X.env.bytes X.digestOf hid hlook hshape hrun
  exact ⟨hcalls, hst, ⟨kb, vb, hkb, hvb, hrows⟩, S.lib, S.state, es', hrows', hmon⟩

end Nanodregg.Hosting.Proofs.Socket
