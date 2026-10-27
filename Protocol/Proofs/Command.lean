/-
# Protocol.Proofs.Command — the verbs, the parser's bound, and consent

Consent (PROTOCOL-4, HOST-9): the only call follow ever hands the client to submit is
`X.callBytes ⟨u, sig⟩` for a `u` that `plan` produced on follow's World — and `plan` produces `u`
only when the receivers derive a Turn from it on that World AND `World.admit` accepts that Turn.
So a member is never asked to submit a call its own fold refuses.
-/
import Kernel.Proofs.RootedFold
import Protocol.Command.Machine
import Protocol.Proofs.PostOr
import Protocol.Proofs.Table
import Kernel.Proofs.Receive
import Kernel.Proofs.Fold
import Kernel.Proofs.Refusals
import Kernel.Proofs.Rederive
import Lang.Proofs.Print
import Lang.Proofs.PrintLine
import Lang.Proofs.Invoke

namespace Nanodregg.Protocol.Command

open Nanodregg.Kernel Nanodregg.Kernel.Receive

theorem Verb.ofWord?_word (v : Verb) : Verb.ofWord? v.word = some v := by
  cases v <;> decide

theorem Verb.mem_all (v : Verb) : v ∈ Verb.all := by cases v <;> decide

theorem Verb.words_distinct : (Verb.all.map Verb.word).Nodup := by decide

/-- The SIZE ceiling, as a fact about the type. -/
theorem Verb.at_most_twenty : Verb.all.length ≤ 20 := by decide

theorem ParseRefusal.name_injective (a b : ParseRefusal) (h : a.name = b.name) : a.tag = b.tag := by
  cases a <;> cases b <;> simp_all [ParseRefusal.name, ParseRefusal.tag]

theorem parse_past_bound {D : Type} (digestOf : ByteArray → Option D) (argv : List ByteArray)
    (h : argvSize argv > Bounds.argvBytesMax) :
    parse digestOf argv = .error (.argvPastBound (argvSize argv)) := by
  simp [parse, h]; rfl

theorem hexDigit_utf8Size_fin : ∀ k : Fin 16, (Text.hexDigit (UInt8.ofNat k.val)).utf8Size = 1 := by
  decide

theorem hexDigit_utf8Size {n : UInt8} (h : n.toNat < 16) : (Text.hexDigit n).utf8Size = 1 := by
  simpa using hexDigit_utf8Size_fin ⟨n.toNat, h⟩

/-- Hex is two ASCII digits a byte. -/
theorem toHex_utf8ByteSize (b : ByteArray) : (Text.toHex b).utf8ByteSize = 2 * b.size := by
  have hi (x : UInt8) : (Text.hexDigit (x >>> 4)).utf8Size = 1 :=
    hexDigit_utf8Size (by have := x.toNat_lt; simp [UInt8.toNat_shiftRight]; omega)
  have lo (x : UInt8) : (Text.hexDigit (x &&& 15)).utf8Size = 1 :=
    hexDigit_utf8Size (by simp [UInt8.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
  unfold Text.toHex
  rw [← Array.foldl_toList]
  have h : ∀ (l : List UInt8) (s : String),
      (l.foldl (fun (s : String) (x : UInt8) =>
        (s.push (Text.hexDigit (x >>> 4))).push (Text.hexDigit (x &&& 15))) s).utf8ByteSize =
        s.utf8ByteSize + 2 * l.length := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x xs ih =>
      intro s
      simp only [List.foldl, ih, String.utf8ByteSize_push, hi, lo, List.length_cons]
      omega
  rw [h, Array.length_toList]
  show ("" : String).utf8ByteSize + 2 * b.data.size = 2 * b.data.size
  rw [String.utf8ByteSize_empty, Nat.zero_add]

/-- **A confirm's argv fits** (LANG-76): `receipt CALL`, the call in hex, is within `argvBytesMax`
for every call the kernel admits (`World.admit` bounds a call by `eventBytesMax`), so no committed
call's confirm is refused `argvPastBound`. -/
theorem receipt_argv_fits (call : ByteArray) (h : call.size ≤ Kernel.Bounds.eventBytesMax) :
    argvSize ["receipt".toUTF8, (Text.toHex call).toUTF8] ≤ Bounds.argvBytesMax := by
  have hs : (Text.toHex call).toUTF8.size = 2 * call.size := by
    rw [String.toUTF8_eq_toByteArray, String.size_toByteArray, toHex_utf8ByteSize]
  have h7 : "receipt".toUTF8.size = 7 := by decide
  simp only [argvSize, List.map, List.sum_cons, List.sum_nil, hs, h7]
  simp only [Bounds.argvBytesMax, Kernel.Bounds.eventBytesMax] at h ⊢
  omega

variable {D : Type} [Ord D] [DecidableEq D]


theorem derivePins_keeps {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) →
      u'.member = u.member ∧ u'.key = u.key ∧ u'.body = u.body
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · have := derivePins_keeps n _ u' t h
        simpa using this
      · split at h
        · cases h
        · have := derivePins_keeps n _ u' t h
          simpa using this
      · cases h
      · cases h; exact ⟨rfl, rfl, rfl⟩

/-- **Every row pin `derivePins` adds is the planning World's** (KERNEL-54): a row pin of the result
was the input's, or is `rowPinAt` of follow's World at some row key, the leaf's digest or absence at
its relation's floor as `w` holds them. -/
theorem derivePins_rowPins {X : Ctx D} {w : World D} :
    ∀ (n : Nat) (u u' : Unsigned D) (t : Turn D), derivePins X w n u = .ok (u', t) →
      ∀ p ∈ u'.rowPins, p ∈ u.rowPins ∨ ∃ key, p = rowPinAt X.env w key
  | 0, _, _, _, h => by simp [derivePins] at h
  | n + 1, u, u', t, h => by
      simp only [derivePins] at h
      split at h
      · have := derivePins_rowPins n _ u' t h
        exact this
      · split at h
        · cases h
        · intro p hp
          have ih := derivePins_rowPins n _ u' t h
          rcases ih p hp with hm | hk
          · simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact .inl hm
            · exact .inr ⟨_, rfl⟩
          · exact .inr hk
      · cases h
      · cases h; intro p hp; exact .inl hp

/-- `planUnchecked` derives `t` from `u` on follow's World, and `u` is the member's own call. -/
theorem planUnchecked_derives {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray}
    {rs : SignedReads D} {b : Body D}
    {u : Unsigned D} {t : Turn D} (h : planUnchecked X me w key rs b = .ok (u, t)) :
    u.member = me.member ∧ u.key = key ∧ u.body = b ∧
      deriveTurn X (pinned X.env w u.pins) (rowView X.env w u) ⟨u, ByteArray.empty⟩ = .ok t := by
  simp only [planUnchecked, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    obtain ⟨u1, t1⟩ := p
    have hk := derivePins_keeps _ _ _ _ hp
    simp only at h
    split at h
    · cases h
    · rename_i t' ht
      cases h
      exact ⟨hk.1, hk.2.1, hk.2.2, ht⟩

/-- **The call `planUnchecked` returns carries only row pins its own World holds** (KERNEL-54, the
plan side of PROTOCOL-16's gap 4; `plan` returns the same call): every row pin of it is `rowPinAt`
of follow's World at its key. -/
theorem planUnchecked_rowPins {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray}
    {rs : SignedReads D} {b : Body D}
    {u : Unsigned D} {t : Turn D} (h : planUnchecked X me w key rs b = .ok (u, t)) :
    ∀ p ∈ u.rowPins, ∃ k, p = rowPinAt X.env w k := by
  simp only [planUnchecked, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    obtain ⟨u1, t1⟩ := p
    simp only at h
    split at h
    · cases h
    · cases h
      intro q hq
      rcases derivePins_rowPins _ _ _ _ hp q hq with hm | hk
      · -- a row the command pinned (`signedReads`' points), at follow's World
        simp only [List.mem_map] at hm
        obtain ⟨k, -, rfl⟩ := hm
        exact ⟨k, rfl⟩
      · exact hk

/-- `plan` offers `u` only if follow's World derives a Turn from it and admits that Turn. -/
theorem plan_admits {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray}
    {rs : SignedReads D} {b : Body D}
    {u : Unsigned D} (h : plan X me w key rs b = .ok u) :
    u.member = me.member ∧ u.key = key ∧ u.body = b ∧
    ∃ t w', deriveTurn X (pinned X.env w u.pins) (rowView X.env w u) ⟨u, ByteArray.empty⟩ = .ok t ∧
      World.admit X.env w t = .ok w' := by
  unfold plan at h
  split at h
  · cases h
  · rename_i u' t hp
    split at h
    · cases h
    · rename_i w' hw
      cases h
      obtain ⟨h1, h2, h3, h4⟩ := planUnchecked_derives hp
      exact ⟨h1, h2, h3, t, w', h4, hw⟩

omit [Ord D] [DecidableEq D] in
theorem refusedAt_ne_submit {X : Ctx D} {r : Refusal D} {call k : ByteArray} :
    refusedAt X r ≠ .submit call k := by
  unfold refusedAt; split <;> simp [refused]

/-- A description is printed or refused, never a step that asks for anything. -/
theorem describe_ne_submit {X : Ctx D} {w : World D} {obj : D} {call k : ByteArray} :
    describe X w obj ≠ .submit call k := by
  unfold describe
  repeat' split
  all_goals simp [refused, printed]

/-- A range read is printed or refused, never a step that asks for anything (PROTOCOL-51). -/
theorem rangeRender_ne_submit {X : Ctx D} {w : World D} {obj : D} {rel : String} {most : Nat}
    {pre : Option String} {call k : ByteArray} : rangeRender X w obj rel most pre ≠ .submit call k := by
  unfold rangeRender
  split
  · simp [refused]
  · split <;> simp [refused, printed]

omit [Ord D] [DecidableEq D] in
theorem envelopeSign_ne_submit {t : Nat} {m k' call k : ByteArray} : envelopeSign t m k' ≠ .submit call k := by
  unfold envelopeSign; split <;> simp

omit [Ord D] [DecidableEq D] in
theorem unknownKeyEnd_ne_submit {X : Ctx D} {cmd : Cmd D} {call k : ByteArray} :
    unknownKeyEnd X cmd ≠ .submit call k := by
  intro h; unfold unknownKeyEnd at h; split at h
  · simp [refused] at h
  · exact refusedAt_ne_submit h

omit [Ord D] [DecidableEq D] in
theorem custodyEnd_ne_submit {X : Ctx D} {cmd : Cmd D} {st : State} {r : Refusal D} {call k : ByteArray} :
    custodyEnd X cmd st r ≠ .submit call k := by
  intro h; unfold custodyEnd at h; split at h
  · split at h
    · exact unknownKeyEnd_ne_submit h
    · simp [refused] at h
  · simp [refused] at h

omit [Ord D] [DecidableEq D] in
/-- The PROTOCOL-46 arms answer no submit: a refused envelope, the receipt lines, a settlement. -/
theorem envelopeRefused_ne_submit {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p call k : ByteArray} : envelopeRefused X me argv cmd a b c d p ≠ .submit call k := by
  intro h
  unfold envelopeRefused next at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | (simp [refused] at h; done) | (simp [notServed] at h; done) | exact unknownKeyEnd_ne_submit h | ((try dsimp only at h); exact envelopeSign_ne_submit h)

theorem receiptLines_ne_submit {X : Ctx D} {dc : Codec.Stream D} {me : Self D} {w : World D}
    {cb call k : ByteArray} : receiptLines X dc me w cb ≠ .submit call k := by
  intro h
  unfold receiptLines at h
  repeat' split at h
  all_goals simp [refused, printed] at h

/-- What `absorbSync` accepted, `absorbPage` accepted (PROTOCOL-74: the walk only refuses). -/
theorem absorbSync_ok {X : Ctx D} {me : Self D} {cmd : Cmd D} {w : World D} {evs : List ByteArray}
    {steps base : Nat} {chain : ByteArray} {x : World D × List (Kernel.Step D × D) × Option (World D)}
    (h : absorbSync X me cmd w evs steps chain base = .ok x) : absorbPage X w evs steps chain base = .ok x := by
  unfold absorbSync at h
  split at h
  · cases h
  · rename_i w' ts wb hp
    split at h
    · split at h
      · cases h
      · cases h; exact hp
    · cases h; exact hp

omit [DecidableEq D] in
theorem attestTip_ne_submit {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {sb call k : ByteArray} : attestTip X me w argv sb ≠ .submit call k := by
  intro h
  unfold attestTip next at h
  repeat' split at h
  all_goals simp [refused] at h

/-- The `sync` tip (PROTOCOL-74) prints, refuses or asks for the attestation's signature: never a submit. -/
theorem syncTip_ne_submit {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {sb call k : ByteArray} {mode : SyncMode} : syncTip X me w argv sb mode ≠ .submit call k := by
  intro h
  cases mode with
  | attest => exact attestTip_ne_submit h
  | tip => simp [syncTip, printed] at h
  | to steps chain => simp [syncTip, printed] at h
  | check b =>
      simp only [syncTip] at h
      repeat' split at h
      all_goals simp [refused, printed] at h

omit [Ord D] [DecidableEq D] in
theorem attestDone_ne_submit {sb u result call k : ByteArray} : attestDone (D := D) sb u result ≠ .submit call k := by
  intro h
  unfold attestDone at h
  repeat' split at h
  all_goals simp [refused, printed] at h

theorem sendCancel_ne_submit {X : Ctx D} {w : World D} {argv : List ByteArray} {cb result call k : ByteArray} :
    sendCancel X w argv cb result ≠ .submit call k := by
  intro h
  unfold sendCancel next at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | simp [refused] at h

omit [DecidableEq D] in
theorem cancelCatchUp_ne_submit {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {said : Nat} {call k : ByteArray} : cancelCatchUp X me w argv said ≠ .submit call k := by
  intro h
  unfold cancelCatchUp next at h
  dsimp only at h
  split at h <;> simp [refused] at h

omit [DecidableEq D] in
theorem cancelAnswer_ne_submit {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {result call k : ByteArray} : cancelAnswer X me w argv result ≠ .submit call k := by
  intro h
  unfold cancelAnswer at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | exact cancelCatchUp_ne_submit h | simp [refused, declined] at h

theorem cancelSettled_ne_submit {X : Ctx D} {me : Self D} {w : World D} {c : Call D} {said : Bool}
    {call k : ByteArray} : cancelSettled X me w c said ≠ .submit call k := by
  intro h
  unfold cancelSettled attemptContradicted at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | simp [refused, printed] at h

theorem cancelTip_ne_submit {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {cb t call k : ByteArray} : cancelTip X me w argv cb t ≠ .submit call k := by
  intro h; unfold cancelTip at h
  repeat' split at h
  all_goals first
    | (simp [refused] at h; done)
    | (unfold next at h; split at h <;> simp [refused] at h; done)
    | exact cancelSettled_ne_submit h

theorem settled_ne_submit {X : Ctx D} {me : Self D} {w : World D} {out cb result call k : ByteArray} :
    settled X me w out cb result ≠ .submit call k := by
  intro h
  unfold settled at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | simp [refused, declined] at h
  all_goals (unfold attemptContradicted at h; split at h <;> simp [refused] at h)

theorem settleStep_ne_submit {X : Ctx D} {me : Self D} {w : World D} {cmd : Cmd D}
    {out cb result call k : ByteArray} : settleStep X me w cmd out cb result ≠ .submit call k := by
  intro h; unfold settleStep at h; split at h
  · exact settled_ne_submit h
  · simp [refused] at h

/-- **Follow answers `ok` to a submitted call only on its own World's word** (R7, E2's T0): whatever
end the attempt store hands step 4 (nd's loop over `Attempt.next`, which follow does not run),
`settled` is `done ok` only when the call bytes step 3 put in the continuation decode, and follow's
own settlement of that call on its current World is committed. -/
theorem settled_ok {X : Ctx D} {me : Self D} {w : World D} {out cb result o e : ByteArray}
    (h : settled X me w out cb result = .done CommandExit.ok.code.toUInt8 o e) :
    ∃ c hh td, X.decodeCall cb = some c ∧ settleOf X me w c = .committed hh td := by
  cases hv : ownSettle X me w cb with
  | some v =>
    cases v with
    | committed hh td =>
      unfold ownSettle at hv
      obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp hv
      exact ⟨c, hh, td, hc, he⟩
    | _ =>
      unfold settled attemptContradicted refusedAt refused declined at h
      simp only [hv] at h
      repeat' split at h
      all_goals simp [CommandExit.code] at h
  | none =>
    unfold settled attemptContradicted refusedAt refused declined at h
    simp only [hv] at h
    repeat' split at h
    all_goals simp [CommandExit.code] at h

/-- **`step`'s settlement**: a step on a phase-4 continuation that answers `done ok` is `settled`'s
`ok`, so the continuation's last item (the call bytes step 3 handed out to submit) decodes as a call
that follow's own World, the World this step runs on, settles committed (`settled_ok`). -/
theorem step_settled_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result o e : ByteArray} {argv acc : List ByteArray}
    (hst : State.ofBytes kb = some ⟨argv, 4, acc⟩)
    (h : step X dc B me f kb result = (f', p, .done CommandExit.ok.code.toUInt8 o e)) :
    ∃ cb c hh td, acc.getLast? = some cb ∧ X.decodeCall cb = some c ∧
      settleOf X me f.world c = .committed hh td := by
  unfold step at h
  simp only [hst, Option.map_some, Option.getD_some] at h
  split at h
  · rename_i hs; cases hs
  · simp [refused, CommandExit.code] at h
  · rename_i st cmd hs _
    simp only [Option.some.injEq] at hs
    subst hs
    have h4 : ∀ b, stepResult (D := D) b 4 result = .ok result := by intro b; cases b <;> rfl
    simp only [h4] at h
    split at h
    all_goals first
      | (simp [refused, CommandExit.code] at h; done)
      | (exfalso; revert ‹(4 : UInt8) = _›; decide)
      | (simp only [Prod.mk.injEq] at h
         obtain ⟨-, -, h⟩ := h
         unfold settleStep at h
         split at h
         · obtain ⟨c, hh, td, hc, hv⟩ := settled_ok h
           exact ⟨_, c, hh, td, rfl, hc, hv⟩
         · simp [refused, CommandExit.code] at h)

/-- The writer's `unknownKey` states no height, so it is never read as `expired`. -/
theorem expiredHeight_unknownKey : expiredHeight? ReadRefusal.unknownKey.payload = none := by decide

omit [Ord D] [DecidableEq D] in
/-- **The incoming key is asked ONCE per command** (PROTOCOL-46): with `tried`'s incoming bit set, a
second `unknownKey` ends the command `refused unknownKey`, never another `signIncoming`. -/
theorem envelopeRefused_once {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p : ByteArray} {h upTo t : Nat} (hs : Text.ofU64 a = some h) (hu : Text.ofU64 c = some upTo)
    (ht : Text.ofU64 d = some t) (hb : t &&& incomingBit ≠ 0)
    (hk : p = ReadRefusal.unknownKey.payload) :
    envelopeRefused X me argv cmd a b c d p = unknownKeyEnd X cmd := by
  have hx : expiredHeight? p = none := hk ▸ expiredHeight_unknownKey
  unfold envelopeRefused
  rw [hx, hs, hu, ht]
  simp only [hk, if_true]
  have : (t &&& incomingBit == 0) = false := by simpa using hb
  simp [this]

omit [Ord D] [DecidableEq D] in
/-- **A write is never retried by the incoming key**: its plan would be signed by the old key against
an envelope the incoming key signed. It ends `refused unknownKey`, with the hint to sync. -/
theorem envelopeRefused_write {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p : ByteArray} {h upTo t : Nat} (hs : Text.ofU64 a = some h) (hu : Text.ofU64 c = some upTo)
    (ht : Text.ofU64 d = some t) (hw : readOnly cmd = false)
    (hk : p = ReadRefusal.unknownKey.payload) :
    envelopeRefused X me argv cmd a b c d p = refusedAt X (.host "unknownKey") := by
  have hx : expiredHeight? p = none := hk ▸ expiredHeight_unknownKey
  unfold envelopeRefused
  rw [hx, hs, hu, ht]
  simp [hk, hw, unknownKeyEnd]

/-- **The writer's word survives custody's refusal of the incoming key** (ROOT's rule (a),
PROTOCOL-56): when the step `step` resumes asked custody for `signIncoming` and custody refused it,
by ANY name (`notArmed`, `noRotation` under `nd --stdio`, or another), the command ends as the
writer's `unknownKey` ends it (`unknownKeyEnd`), never by custody's name. -/
theorem step_incoming_writer_word {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f : Follow D} {kb result : ByteArray} {st : State} {cmd : Cmd D} {c : CustodyRefusal}
    (hst : State.ofBytes kb = some st) (hp : parse X.digestOf st.argv = .ok cmd)
    (hin : askedIncoming st = true) (hres : custodyResult (D := D) result = .error (.custody c)) :
    (step X dc B me f kb result).2.2 = unknownKeyEnd X cmd := by
  have h1 : st.phase = 1 := by
    simp only [askedIncoming, Bool.and_eq_true, beq_iff_eq] at hin; exact hin.1
  have hsr : ∀ b : Bool, stepResult (D := D) b st.phase result = .error (.custody c) := by
    intro b; simp [stepResult, custodyPhase, h1, hres]
  unfold step
  simp only [hst, Option.map_some, Option.getD_some, hp, hsr, custodyEnd, hin, if_true]

omit [Ord D] [DecidableEq D] in
/-- The tooth: a custody refusal of any OTHER step ends the command by custody's own name. -/
theorem custodyEnd_own_word {X : Ctx D} {cmd : Cmd D} {st : State} {c : CustodyRefusal}
    (hin : askedIncoming st = false) : custodyEnd X cmd st (.custody c) = refused (D := D) (.custody c) := by
  simp [custodyEnd, hin]

/-- **Custody's own word ends every other custody step** (the complement of
`step_incoming_writer_word`, over `step` itself): when the state `step` resumes did NOT ask
`signIncoming` and its phase is one custody answers, a custody refusal by any name ends the command
by that name. With `step_asked_signIncoming` (a state with `askedIncoming` travels only with
`signIncoming`), no refused `sign`, `signNext` or `precommit` is turned into the writer's word. -/
theorem step_custody_own_word {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f : Follow D} {kb result : ByteArray} {st : State} {cmd : Cmd D} {c : CustodyRefusal}
    (hst : State.ofBytes kb = some st) (hp : parse X.digestOf st.argv = .ok cmd)
    (hin : askedIncoming st = false) (hph : custodyPhase false st.phase = true)
    (hres : custodyResult (D := D) result = .error (.custody c)) :
    (step X dc B me f kb result).2.2 = refused (D := D) (.custody c) := by
  have hsr : ∀ b : Bool, stepResult (D := D) b st.phase result = .error (.custody c) := by
    intro b
    have hb : custodyPhase b st.phase = true := by
      cases b
      · exact hph
      · simp only [custodyPhase, Bool.false_and, Bool.or_false, Bool.true_and] at hph ⊢
        simp [hph]
    simp [stepResult, hb, hres]
  unfold step
  simp only [hst, Option.map_some, Option.getD_some, hp, hsr, custodyEnd, hin, Bool.false_eq_true,
    if_false]

/-- Consent at the wire: the only call `step` hands the client to submit is a call over a `u`
that `plan` produced on follow's own World (hence derived and admitted there, `plan_admits`), from
the body and the range reads ONE command gives on that World (`body`, `signedReads`). -/
theorem step_submit_planned {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D}
    {kb result call k : ByteArray} (h : step X dc B me f kb result = (f', p, .submit call k)) :
    f' = f ∧ p = .steps [] ∧ ∃ cmd sg rs b u sig, body X me f.world sg cmd = .ok b ∧
      signedReads X f.world cmd = .ok rs ∧ plan X me f.world sg.key rs b = .ok u ∧
      call = X.callBytes ⟨u, sig⟩ := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind, notServed, Prod.mk.injEq, reduceCtorEq, and_false] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq, reduceCtorEq, and_false] at h)
  -- a page's self-head posts (PROTOCOL-75): a submit survives `postOr` only when none fired
  all_goals (try (obtain ⟨h1, h0, h2⟩ := h; have h := And.intro h1 (And.intro h0 (postOr_submit_elim h2))))
  all_goals (try (simp only [reduceCtorEq, and_false] at h; done))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; unfold render at h; repeat' split at h
                  all_goals simp [refused, printed] at h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact custodyEnd_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact describe_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact rangeRender_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact refusedAt_ne_submit h))
  all_goals (try (exfalso; exact refusedAt_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact envelopeRefused_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; (try dsimp only at h); exact envelopeSign_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact receiptLines_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact syncTip_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact attestDone_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact settleStep_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact sendCancel_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact cancelAnswer_ne_submit h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact cancelTip_ne_submit h))
  all_goals (try (obtain ⟨h1, h0, h2⟩ := h; injection h2 with h3 h4; subst h1 h0 h3
                  exact ⟨rfl, rfl, _, _, _, _, _, _, ‹body _ _ _ _ _ = _›, ‹signedReads _ _ _ = _›,
                    ‹plan _ _ _ _ _ _ = _›, rfl⟩))
  done

omit [Ord D] [DecidableEq D] in
/-- The expiry retry is ONE per command: once a command has re-signed, a further `expired` ends it
`expired` by name (PROTOCOL-19). -/
theorem reSign_tried (me : Self D) (upTo height : Nat) :
    reSign (D := D) me true upTo height = .error (.expired height) := by
  simp [reSign]

omit [Ord D] [DecidableEq D] in
/-- A re-signed envelope covers the writer's stated height by exactly one window, and only when
the refused envelope did not already cover it (a writer that contradicts itself gets no second
signature). -/
theorem reSign_ok {me : Self D} {tried : Bool} {upTo height upTo' : Nat}
    (h : reSign (D := D) me tried upTo height = .ok upTo') :
    tried = false ∧ upTo < height ∧ upTo' = height + me.window ∧ upTo' < 2 ^ 64 := by
  unfold reSign at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, rfl, hc.2⟩
  · cases h

/-! ## What follow persists, its own fold admitted (HOST-22; `absorb_admits` and
`absorbPage_admits` proved by HOST-5, restated over steps for KERNEL-47 by PROTOCOL-8)

The premise that lets a follower reopen its own Store exactly as the writer does (`World.fold`,
no signature verified at reopen; ROOT's ruling on HOST-22): every step `host follow` appends was
re-derived from the writer's logged event and taken by follow's OWN `World.step` before the
append. A Turn was admitted by `World.admit`; a refusal was recorded by `World.refuse` after
follow's own `judge` recorded it, or its own `cancel` recorded it under the event's signature. The follow-time teeth are the rows' `audit` row (plant
`followVerifyAll`, line 13) and the `refusedFinal` row (plant `admitsRecorded`). -/

/-! ### A page event read back (`eventOf`, `eventBytes`) -/

theorem tag_size (b : UInt8) : (⟨#[b]⟩ : ByteArray).size = 1 := rfl

theorem tagged_pos (b : UInt8) (e : ByteArray) : 0 < (⟨#[b]⟩ ++ e : ByteArray).size := by
  simp only [ByteArray.size_append, tag_size]
  omega

theorem tagged_head (b : UInt8) (e : ByteArray) :
    (⟨#[b]⟩ ++ e : ByteArray)[0]'(tagged_pos b e) = b := by
  rw [ByteArray.getElem_append_left (by rw [tag_size]; exact Nat.zero_lt_one)]
  rfl

theorem tagged_tail (b : UInt8) (e : ByteArray) :
    (⟨#[b]⟩ ++ e : ByteArray).extract 1 (⟨#[b]⟩ ++ e : ByteArray).size = e :=
  ByteArray.extract_append_eq_right (tag_size b).symm (by simp only [ByteArray.size_append, tag_size])

theorem untag {e : ByteArray} (h : 0 < e.size) : e = ⟨#[e[0]]⟩ ++ e.extract 1 e.size := by
  have h1 : (⟨#[e[0]]⟩ : ByteArray).size = 1 := rfl
  apply ByteArray.ext_getElem
  · simp only [ByteArray.size_append, h1, ByteArray.size_extract]; omega
  · intro i hi hj
    by_cases hi0 : i = 0
    · subst hi0
      rw [ByteArray.getElem_append_left (by rw [h1]; exact Nat.zero_lt_one)]
      rfl
    · rw [ByteArray.getElem_append_right (by rw [h1]; omega)]
      simp only [ByteArray.getElem_extract, h1]
      congr 1
      omega

/-- What `eventOf` reads an event as, by its tag. -/
theorem eventOf_some {e : ByteArray} {ev : Kernel.Event} (h : eventOf e = some ev) :
    (e[0]? = some eventTurn ∧ ev = .turn (eventCall e)) ∨
    (e[0]? = some eventRefusal ∧ ev = .refusal (eventCall e)) ∨
    (e[0]? = some eventCancel ∧ ∃ sig cb, cancelParts e = some (sig, cb) ∧ ev = .cancel sig cb) := by
  unfold eventOf at h
  by_cases hpos : 0 < e.size
  · rw [dif_pos hpos] at h
    have h0 : e[0]? = some e[0] := getElem?_pos e 0 hpos
    by_cases hc : e[0] = eventCancel
    · rw [if_pos hc] at h
      cases hp : cancelParts e with
      | none => rw [hp] at h; cases h
      | some p =>
        obtain ⟨sig, cb⟩ := p
        rw [hp] at h
        change some (Kernel.Event.cancel sig cb) = some ev at h
        exact .inr (.inr ⟨by rw [h0, hc], sig, cb, rfl, (Option.some.inj h).symm⟩)
    · rw [if_neg hc] at h
      by_cases ht : e[0] = eventTurn
      · rw [if_pos ht] at h
        exact .inl ⟨by rw [h0, ht], (Option.some.inj h).symm⟩
      · rw [if_neg ht] at h
        by_cases hr : e[0] = eventRefusal
        · rw [if_pos hr] at h
          exact .inr (.inl ⟨by rw [h0, hr], (Option.some.inj h).symm⟩)
        · rw [if_neg hr] at h; cases h
  · rw [dif_neg hpos] at h; cases h

/-- THE tag-2 event reads back as its signature and call, for a signature `cancelAuth` admits. -/
theorem cancelParts_cancelEvent {sig b : ByteArray} (hpos : 0 < sig.size)
    (hle : sig.size ≤ Kernel.Bounds.cancelBytesMax) :
    ∃ h0 : 0 < (cancelEvent sig b).size, (cancelEvent sig b)[0] = eventCancel ∧
      cancelParts (cancelEvent sig b) = some (sig, b) := by
  have h8 : (Codec.Stream.nat64.bytes sig.size).size = 8 := by
    rw [Codec.Stream.nat64_bytes]; rfl
  unfold cancelEvent
  generalize hE : (⟨#[eventCancel]⟩ ++ Codec.Stream.nat64.bytes sig.size ++ sig ++ b : ByteArray) = e
  have ho : Codec.Stream.OccursAt e 0 e := Codec.Stream.occursAt_self e
  rw [← hE] at ho
  obtain ⟨ho, hcb⟩ := Codec.Stream.occursAt_append.mp ho
  obtain ⟨ho, hsig⟩ := Codec.Stream.occursAt_append.mp ho
  obtain ⟨ht, hn⟩ := Codec.Stream.occursAt_append.mp ho
  rw [hE] at ht hn hsig hcb
  have h1 : (⟨#[eventCancel]⟩ : ByteArray).size = 1 := rfl
  simp only [ByteArray.size_append, h1, h8, Nat.zero_add] at hn hsig hcb
  have hsize : e.size = 1 + 8 + sig.size + b.size := by
    rw [← hE]; simp only [ByteArray.size_append, h1, h8]
  have hget : Codec.Stream.nat64.get e 1 = .ok (sig.size, 9) := by
    have := Codec.Stream.nat64_lawfulOn.get_of_occurs sig.size e 1 (by
      have : Kernel.Bounds.cancelBytesMax < 2 ^ 64 := by decide
      omega) hn
    rw [this, h8]
  have hx1 : e.extract 9 (9 + sig.size) = sig := by
    have := hsig.2; simpa using this
  have hx2 : e.extract (9 + sig.size) e.size = b := by
    have := hcb.2
    rw [show 1 + 8 + sig.size + b.size = e.size by omega] at this
    simpa using this
  have hparts : cancelParts e = some (sig, b) := by
    unfold cancelParts
    simp only [hget]
    rw [if_pos ⟨hpos, hle, by omega⟩, hx1, hx2]
  have h0 : 0 < e.size := by omega
  have htag : e[0] = eventCancel := by
    obtain ⟨_, hk⟩ := Codec.Stream.occursAt_iff_getElem.mp ht
    exact hk 0 (by decide)
  exact ⟨h0, htag, hparts⟩

/-- **A step event reads back as itself** (`eventBytes`' reader is `eventOf`), for a cancel whose
signature `cancelAuth` admits (non-empty, at most `cancelBytesMax`: every recorded cancel's). -/
theorem eventOf_eventBytes {ev : Kernel.Event}
    (hc : ∀ sig b, ev = .cancel sig b → 0 < sig.size ∧ sig.size ≤ Kernel.Bounds.cancelBytesMax) :
    eventOf (eventBytes ev) = some ev := by
  cases ev with
  | turn b =>
    have hne : ¬ eventTurn = eventCancel := by decide
    simp only [eventOf, eventBytes, tagged_pos, ↓reduceDIte, tagged_head, hne, ↓reduceIte, eventCall,
      tagged_tail]
  | refusal b =>
    have hne : ¬ eventRefusal = eventCancel := by decide
    have hnt : ¬ eventRefusal = eventTurn := by decide
    simp only [eventOf, eventBytes, tagged_pos, ↓reduceDIte, tagged_head, hne, hnt, ↓reduceIte, eventCall,
      tagged_tail]
  | cancel sig b =>
    obtain ⟨hpos, hle⟩ := hc sig b rfl
    obtain ⟨h0, htag, hparts⟩ := cancelParts_cancelEvent (b := b) hpos hle
    show eventOf (cancelEvent sig b) = _
    unfold eventOf
    rw [dif_pos h0, if_pos htag, hparts]
    rfl

/-- **What follow absorbs is what the one re-deriver derives**: an event is absorbed to `p` exactly
when it reads back (`eventOf`) as an event `Receive.rederive` takes to `p`. -/
theorem absorbStep_ok {X : Ctx D} {w : World D} {e : ByteArray} {p : Kernel.Step D × World D} :
    absorbStep X w e = .ok p ↔ ∃ ev, eventOf e = some ev ∧ Receive.rederive X w ev = .ok p := by
  unfold absorbStep
  cases he : eventOf e with
  | none => simp
  | some ev =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hr : Receive.rederive X w ev <;> simp [Except.mapError]

/-- One absorbed step is a step of follow's own World. -/
theorem absorbStep_step {X : Ctx D} {w w' : World D} {e : ByteArray} {s : Kernel.Step D}
    (h : absorbStep X w e = .ok (s, w')) : World.step X.env w s = .ok w' := by
  obtain ⟨ev, -, hr⟩ := absorbStep_ok.mp h
  exact rederive_step hr

theorem absorb_admits {X : Ctx D} :
    ∀ (evs : List ByteArray) {w w' : World D} {acc ts : Array (Kernel.Step D × D)},
      absorb X w acc evs = .ok (w', ts) →
        ∃ l, ts.toList = acc.toList ++ l ∧ World.RootedFold X.env w l w'
  | [], w, w', acc, ts, h => by
    simp only [absorb, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl⟩
  | e :: es, w, w', acc, ts, h => by
    unfold absorb at h
    split at h
    · rename_i s w₁ hs
      obtain ⟨l, hl, hf⟩ := absorb_admits es h
      exact ⟨(s, World.roots X.env w₁) :: l, by simp [hl], ⟨w₁, absorbStep_step hs, rfl, hf⟩⟩
    · cases h

/-- Rooted runs compose: a run to `wb`, then one from `wb`, is a run of both. -/
theorem rooted_append {W T R N : Type} {admit : W → T → Except R W} {note : W → N} :
    ∀ {w wb w' : W} {l₁ l₂ : List (T × N)}, Rooted admit note w l₁ wb → Rooted admit note wb l₂ w' →
      Rooted admit note w (l₁ ++ l₂) w'
  | w, wb, w', [], l₂, h₁, h₂ => by simp only [Rooted] at h₁; subst h₁; simpa using h₂
  | w, wb, w', (t, n) :: rest, l₂, h₁, h₂ => by
      obtain ⟨w₁, ha, hn, hr⟩ := h₁
      exact ⟨w₁, ha, hn, rooted_append hr h₂⟩

/-- What `absorbPage` accepted, unfolded: ONE fold of the page cut at the stated base (its prefix to
the base, then the rest from where the prefix stopped), ending at the writer's stated pair, and the
World at the cut returned exactly when the fold sits at the base there. -/
theorem absorbPage_ok {X : Ctx D} {w w' : World D} {evs : List ByteArray} {steps base : Nat}
    {chain : ByteArray} {ts : List (Kernel.Step D × D)} {wb? : Option (World D)}
    (h : absorbPage X w evs steps chain base = .ok (w', ts, wb?)) :
    ∃ wb tb ts', absorb X w #[] (evs.take (base - w.steps)) = .ok (wb, tb) ∧
      absorb X wb tb (evs.drop (base - w.steps)) = .ok (w', ts') ∧ ts = ts'.toList ∧
      (w'.steps = steps ∧ X.env.bytes w'.chain = chain) ∧
      wb? = (if wb.steps = base then some wb else none) := by
  unfold absorbPage at h
  split at h
  · cases h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p₁ h₁
    split at h
    · cases h
    · rename_i p₂ h₂
      split at h
      · rename_i hc
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨p₁.1, p₁.2, p₂.2, h₁, h₂, rfl, hc, rfl⟩
      · cases h

theorem absorbPage_admits {X : Ctx D} {w w' : World D} {evs : List ByteArray} {steps base : Nat}
    {chain : ByteArray} {ts : List (Kernel.Step D × D)} {wb? : Option (World D)}
    (h : absorbPage X w evs steps chain base = .ok (w', ts, wb?)) :
    World.RootedFold X.env w ts w' := by
  obtain ⟨wb, tb, ts', h₁, h₂, rfl, -, -⟩ := absorbPage_ok h
  obtain ⟨l₁, hl₁, hf₁⟩ := absorb_admits _ h₁
  obtain ⟨l₂, hl₂, hf₂⟩ := absorb_admits _ h₂
  rw [hl₂, hl₁]
  simpa using rooted_append hf₁ hf₂

/-- **A page longer than one follower record is refused before any of it is absorbed** (HOST-41):
`pageTooLong`, by name, with the page's count; `step` answers an `absorbPage` error with follow's
state unchanged and nothing to persist (its `same` arm). -/
theorem absorbPage_tooLong {X : Ctx D} {w : World D} {evs : List ByteArray} {steps base : Nat}
    {chain : ByteArray} (h : Bounds.pageStepsMax < evs.length) :
    absorbPage X w evs steps chain base = .error (.pageTooLong evs.length) := by
  unfold absorbPage
  exact if_pos h

/-- What a page `absorbPage` accepts ends at the writer's stated step count: the pair the kernel's
`fold_reaches_host` binds (with the chain), so an honest page leaves follow's World equal to the
writer's, or exhibits a hash collision. -/
theorem absorbPage_steps {X : Ctx D} {w w' : World D} {evs : List ByteArray} {steps base : Nat}
    {chain : ByteArray} {ts : List (Kernel.Step D × D)} {wb? : Option (World D)}
    (h : absorbPage X w evs steps chain base = .ok (w', ts, wb?)) :
    w'.steps = steps ∧ X.env.bytes w'.chain = chain :=
  (absorbPage_ok h).choose_spec.choose_spec.choose_spec.2.2.2.1

/-- **The World follow keeps for a writer's base is ON the page's chain-checked fold, at exactly the
stated step count** (PROTOCOL-47): the steps follow persists split at it, a run of follow's own
`World.step` from its World to it and on from it to the page's end (`absorbPage_steps`: the writer's
stated pair). So the World whose digest `invite` may pin is one follow derived on the path it
checked, never a fork of it and never bytes the writer sent. -/
theorem absorbPage_base {X : Ctx D} {w w' wb : World D} {evs : List ByteArray} {steps base : Nat}
    {chain : ByteArray} {ts : List (Kernel.Step D × D)}
    (h : absorbPage X w evs steps chain base = .ok (w', ts, some wb)) :
    wb.steps = base ∧ ∃ l₁ l₂, ts = l₁ ++ l₂ ∧ World.RootedFold X.env w l₁ wb ∧
      World.RootedFold X.env wb l₂ w' := by
  obtain ⟨wb', tb, ts', h₁, h₂, rfl, -, hw⟩ := absorbPage_ok h
  obtain ⟨l₁, hl₁, hf₁⟩ := absorb_admits _ h₁
  obtain ⟨l₂, hl₂, hf₂⟩ := absorb_admits _ h₂
  split at hw
  · rename_i hs
    cases hw
    refine ⟨hs, l₁, l₂, ?_, hf₁, hf₂⟩
    rw [hl₂, hl₁]
    simp
  · cases hw

/-! ## PROTOCOL-47: `invite` pins its own base -/

/-- **What `invite` pins is the base follow verified itself, and the writer states that very
base**: the step count and digest follow recorded (its own World's, `absorbPage_base`), equal to
the step count and digest the writer's last page stated as its newest base. -/
theorem pinOf_ok {v : Option (Nat × ByteArray)} {s : Nat} {d : ByteArray} {p : Thin.Pin}
    (h : pinOf v s d = .ok p) : v = some (p.steps, p.digest) ∧ p.steps = s ∧ p.digest = d := by
  unfold pinOf at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hs hd
        cases h
        exact ⟨rfl, Classical.not_not.mp hs, Classical.not_not.mp hd⟩
  · cases h

/-- Nothing verified: `noBase`, never a pin (a restarted follow, before its fold next sits at the
writer's base). -/
theorem pinOf_none (s : Nat) (d : ByteArray) : pinOf none s d = .error .noBase := rfl

/-- The writer's newest base is at another step count than the one follow verified (a newer seal
follow never crossed, or a page that raced a seal): `noBase`. -/
theorem pinOf_other {s s' : Nat} {d d' : ByteArray} (hs : s' ≠ s) :
    pinOf (some (s', d')) s d = .error .noBase := by
  simp [pinOf, hs]

/-- **The tooth**: the writer states a digest for the base that is not follow's own World there
(a lie about where its base is, or a forged base): `baseMismatch`, by name. -/
theorem pinOf_forged {s : Nat} {d d' : ByteArray} (hd : d' ≠ d) :
    pinOf (some (s, d')) s d = .error .baseMismatch := by
  simp [pinOf, hd]

/-- A page the follower reads states its base at or below its tip: a base past the tip is no base
of that log, and `logPage` reads no page from it (`step` answers a page it cannot read
`badResult`, its `none` arm). -/
theorem logPage_base_le {b : ByteArray} {p : LogPage} (h : logPage b = some p) :
    p.baseSteps ≤ p.tipSteps := by
  unfold logPage at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
    split at h
    · rename_i hc
      cases h
      exact hc.2
    · cases h
  · cases h

/-- **What follow persists, its own fold taken, each roots digest its own.** Every pair follow
persists is a step its own `World.step` took, in order from its World, beside the roots digest of
the World that step reached (HOST-29, KERNEL-47), ending at follow's next World. -/
theorem step_persists_admitted {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {ts : List (Kernel.Step D × D)} {kb result : ByteArray} {r : Reply}
    (h : step X dc B me f kb result = (f', .steps ts, r)) :
    World.RootedFold X.env f.world ts f'.world := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind, Prod.mk.injEq, Persist.steps.injEq] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq, Persist.steps.injEq, reduceCtorEq, false_and,
    and_false] at h)
  all_goals first
    | (obtain ⟨rfl, rfl, -⟩ := h; dsimp only; exact absorbPage_admits (absorbSync_ok (by assumption)))
    | (obtain ⟨rfl, rfl, -⟩ := h; rfl)

/-- HOST-22's consumer: what follow persists folds, with `World.fold`, to follow's next World. -/
theorem step_persists_folds {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {ts : List (Kernel.Step D × D)} {kb result : ByteArray} {r : Reply}
    (h : step X dc B me f kb result = (f', .steps ts, r)) :
    World.fold X.env f.world (ts.map Prod.fst) = .ok f'.world :=
  RootedFold.fold (step_persists_admitted h)

/-- **What follow remembers of a writer's base is its own** (PROTOCOL-47): after any step, follow's
`verified` is what it was, or cleared (an adopt: another World), or follow's own digest of a World
`absorbPage` accepted at the writer's stated base on a chain-checked page (`absorbPage_base`). No
step stores a digest the writer stated. -/
theorem step_verified {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result : ByteArray} {r : Reply}
    (h : step X dc B me f kb result = (f', p, r)) :
    f'.verified = f.verified ∨ f'.verified = none ∨
      ∃ evs steps chain base w' ts wb, absorbPage X f.world evs steps chain base = .ok (w', ts, some wb) ∧
        f'.verified = some (wb.steps, B.digest (B.world.bytes wb)) := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind] at h)
  all_goals (repeat' split at h)
  all_goals (simp only [Prod.mk.injEq] at h)
  all_goals (obtain ⟨rfl, -, -⟩ := h)
  all_goals first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; exact ⟨_, _, _, _, _, _, _, absorbSync_ok (by assumption), rfl⟩)

/-! ## A recorded refusal, as the follower meets it (KERNEL-44, PROTOCOL-41) -/

/-- **A writer that admits a call it recorded refused is caught by name.** On follow's World the
call's transaction id holds a recorded refusal (and no journal entry), so a Turn event for that call
is refused `refusedFinal` with the recorded code: the kernel's own refusal, never re-derived. -/
theorem absorbStep_refusedFinal {X : Ctx D} {w : World D} {e : ByteArray} {c : Call D} {code : Nat}
    (hpos : 0 < e.size) (htag : e[0] = eventTurn) (hdec : X.decodeCall (e.extract 1 e.size) = some c)
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = some code) :
    absorbStep X w e = .error (.reject (.refusedFinal code)) := by
  have hs : submit X w c = .error (.rejected (.refusedFinal code)) := by
    unfold submit; rw [hj, hr]
  have hne : ¬ eventTurn = eventCancel := by decide
  have he : eventOf e = some (.turn (eventCall e)) := by
    unfold eventOf
    simp only [hpos, ↓reduceDIte, htag, hne, ↓reduceIte]
  have hrd : Receive.rederive X w (.turn (eventCall e)) = .error (.rejected (.refusedFinal code)) := by
    simp only [rederive, eventCall, hdec, hs]
  rw [show absorbStep X w e = (Receive.rederive X w (.turn (eventCall e))).mapError
    (ofVerdict (w.steps + 1)) by simp only [absorbStep, he], hrd]
  rfl

/-- What `World.refuse` recorded for `c`'s record (`recordOf`, any cancel field) is in the World it
reached: `c` answers the verdict's code, which names the verdict; nothing else about the World but
the refusals and the step count moved. -/
theorem refuse_answers {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {a : ByteArray}
    (href : World.refuse X.env w (recordOf X c v a) = .ok w') :
    refusedAnswer X w' c = some v.code ∧ codeName v.code = some v.name ∧
      w'.height = w.height ∧ w'.steps = w.steps + 1 ∧ w'.journalAt X.env (txIdOf X c) = none := by
  have hrec := refuse_recorded href
  obtain ⟨-, -, -, hjn, -, -⟩ := refuse_facts href
  refine ⟨?_, codeName_code v, (refuse_frame href).2.2.1, refuse_steps href, ?_⟩
  · unfold refusedAnswer
    rw [show (recordOf X c v a).txId = txIdOf X c from rfl] at hrec
    rw [hrec]; rfl
  · rw [refuse_journalAt href]; exact hjn

/-- What `judge` recorded for `c` is in the World it reached: `c` answers the verdict's code, which
names the verdict; nothing else about the World but the refusals and the step count moved. -/
theorem recorded_answers {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (hj : judge X w c = .recorded v r w') :
    r = refusedOf X c v ∧ refusedAnswer X w' c = some v.code ∧ codeName v.code = some v.name ∧
      w'.height = w.height ∧ w'.steps = w.steps + 1 ∧ w'.journalAt X.env (txIdOf X c) = none := by
  obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
  exact ⟨rfl, refuse_answers href⟩

/-- **An absorbed refusal answers its call by name.** After follow absorbs a refusal event (tag 1, a
judged refusal: its call is the event past the tag and the record carries no cancel signature) or a
cancel event (tag 2: `cancelParts` reads the signature and the call, and the record carries exactly
that signature, which `cancelAuth` verified on follow's World), its World holds `c`'s recorded code (and no journal entry for it), and that code
names the verdict: so a later `submit` of `c` on that World is `refusedFinal` (`Receive.submit`'s
second arm) without re-deriving, and `lookup` answers `refused NAME` (`Receive.codeName_code`). -/
theorem absorbStep_refusal_recorded {X : Ctx D} {w w' : World D} {e : ByteArray} {r : Refused D}
    (h : absorbStep X w e = .ok (.refusal r, w')) :
    ∃ c v a, r = recordOf X c v a ∧
      ((e[0]? = some eventRefusal ∧ a = ByteArray.empty ∧ X.decodeCall (e.extract 1 e.size) = some c) ∨
        (e[0]? = some eventCancel ∧ v = .refused .cancelled ∧ cancelAuth X w c a = .ok () ∧
          ∃ cb, cancelParts e = some (a, cb) ∧ X.decodeCall cb = some c)) ∧
      refusedAnswer X w' c = some v.code ∧ codeName v.code = some v.name ∧ w'.height = w.height ∧
      w'.steps = w.steps + 1 ∧ w'.journalAt X.env (txIdOf X c) = none := by
  obtain ⟨ev, hev, hr⟩ := absorbStep_ok.mp h
  rcases rederive_ok hr with ⟨b, c, t, -, -, -, hs⟩ | ⟨b, c, v, r', rfl, hc, hj, hs⟩ |
      ⟨sig, b, c, v, r', rfl, hc, hco, hs⟩
  · cases hs
  · cases hs
    rcases eventOf_some hev with ⟨-, h1⟩ | ⟨ht, h1⟩ | ⟨-, _, _, -, h1⟩
    · cases h1
    · obtain rfl := Kernel.Event.refusal.inj h1
      obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
      exact ⟨_, _, ByteArray.empty, rfl, .inl ⟨ht, rfl, hc⟩, refuse_answers href⟩
    · cases h1
  · cases hs
    rcases eventOf_some hev with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨ht, sig', cb, hp, h1⟩
    · cases h1
    · cases h1
    · simp only [Kernel.Event.cancel.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨ha, rfl, rfl, href⟩ := cancel_recorded hco
      exact ⟨_, _, _, rfl, .inr ⟨ht, rfl, ha, _, hp, hc⟩, refuse_answers href⟩

/-- **What `cancelParts` reads back is the tag-2 shape**: an event it splits into `s` and `cb` IS its
first byte, `s`'s eight-byte length, `s` and `cb`, with `0 < s.size ≤ cancelBytesMax`. -/
theorem cancelParts_some {e s cb : ByteArray} (h : cancelParts e = some (s, cb)) (h0 : 0 < e.size) :
    e = ⟨#[e[0]]⟩ ++ Codec.Stream.nat64.bytes s.size ++ s ++ cb ∧
      0 < s.size ∧ s.size ≤ Kernel.Bounds.cancelBytesMax := by
  unfold cancelParts at h
  split at h
  · rename_i n j hg
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, hj, hn⟩ := Codec.Stream.nat64_lawfulOn.occurs_of_get hg
      have h8 : (Codec.Stream.nat64.bytes n).size = 8 := by
        rw [Codec.Stream.nat64_bytes]; rfl
      rw [h8] at hj
      subst hj
      have hs : (e.extract (1 + 8) (1 + 8 + n)).size = n := by
        rw [ByteArray.size_extract]; omega
      have hcb : (e.extract (1 + 8 + n) e.size).size = e.size - (1 + 8 + n) := by
        rw [ByteArray.size_extract]; omega
      have h1 : (⟨#[e[0]]⟩ : ByteArray).size = 1 := rfl
      rw [hs]
      refine ⟨?_, hc.1, hc.2.1⟩
      have ho : Codec.Stream.OccursAt e 0 (⟨#[e[0]]⟩ ++ Codec.Stream.nat64.bytes n ++
          e.extract (1 + 8) (1 + 8 + n) ++ e.extract (1 + 8 + n) e.size) := by
        refine Codec.Stream.occursAt_append.mpr ⟨Codec.Stream.occursAt_append.mpr
          ⟨Codec.Stream.occursAt_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
        · refine Codec.Stream.occursAt_iff_getElem.mpr ⟨by rw [h1]; omega, fun k hk => ?_⟩
          have hk0 : k = 0 := by rw [h1] at hk; omega
          subst hk0
          rfl
        · rw [h1, Nat.zero_add]; exact hn
        · refine ⟨?_, ?_⟩
          · simp only [ByteArray.size_append, h1, h8, hs]; omega
          · simp only [ByteArray.size_append, h1, h8, hs, Nat.zero_add]
        · refine ⟨?_, ?_⟩
          · simp only [ByteArray.size_append, h1, h8, hs, hcb]; omega
          · simp only [ByteArray.size_append, h1, h8, hs, hcb, Nat.zero_add]
            congr 1; omega
      exact Codec.Stream.eq_of_occursAt_zero ho (by simp only [ByteArray.size_append, h1, h8, hs, hcb]; omega)
    · cases h
  · cases h

/-- **An event that reads back is the bytes of what it reads as** (one encoding per event): the
writer's `eventBytes` is the only spelling `eventOf` reads. -/
theorem eventBytes_eventOf {e : ByteArray} {ev : Kernel.Event} (h : eventOf e = some ev) :
    eventBytes ev = e := by
  have hpos : 0 < e.size := by
    by_cases hp : 0 < e.size
    · exact hp
    · unfold eventOf at h; rw [dif_neg hp] at h; cases h
  have h0 : e[0]? = some e[0] := getElem?_pos e 0 hpos
  rcases eventOf_some h with ⟨ht, rfl⟩ | ⟨ht, rfl⟩ | ⟨ht, sig, cb, hp, rfl⟩
  · rw [h0] at ht
    show ⟨#[eventTurn]⟩ ++ eventCall e = e
    rw [← Option.some.inj ht]; exact (untag hpos).symm
  · rw [h0] at ht
    show ⟨#[eventRefusal]⟩ ++ eventCall e = e
    rw [← Option.some.inj ht]; exact (untag hpos).symm
  · obtain ⟨he, -, -⟩ := cancelParts_some hp hpos
    rw [h0] at ht
    show cancelEvent sig cb = e
    unfold cancelEvent
    rw [← Option.some.inj ht]; exact he.symm

/-- **One encoding per record** (PROTOCOL-60, HOST-17's condition): a tag-2 event that follow absorbs
into a record `r` IS `cancelEvent r.cancel r.event`, byte for byte, whenever the call codec reads
only its own bytes (`hcanon`; deployed: `Codec.Kernel.eq_callBytes_of_decodeCall`). So the writer's
`stepEvent` is the only tag-2 encoding of a cancel: no other length, padding or split re-records it.
This is the tooth of `cancelParts`' length checks, which no plant can see (an event they refuse
fails to decode or to verify anyway). -/
theorem absorbStep_cancel_canonical {X : Ctx D} {w w' : World D} {e : ByteArray} {r : Refused D}
    (hcanon : ∀ b c, X.decodeCall b = some c → b = X.callBytes c)
    (h : absorbStep X w e = .ok (.refusal r, w')) (htag : e[0]? = some eventCancel) :
    e = cancelEvent r.cancel r.event := by
  obtain ⟨c, v, a, rfl, hsrc, -⟩ := absorbStep_refusal_recorded h
  rcases hsrc with ⟨ht, -, -⟩ | ⟨-, -, -, cb, hp, hdec⟩
  · rw [ht] at htag
    exact absurd (Option.some.inj htag) (by decide)
  · have h0 : 0 < e.size := by
      by_cases hn : 0 < e.size
      · exact hn
      · rw [getElem?_neg e 0 hn] at htag; cases htag
    have htag0 : e[0] = eventCancel := by
      rw [getElem?_pos e 0 h0] at htag; exact Option.some.inj htag
    obtain ⟨he, -, -⟩ := cancelParts_some hp h0
    show e = cancelEvent a (X.callBytes c)
    unfold cancelEvent
    rw [← hcanon cb c hdec, ← htag0]
    exact he

/-- **A cancel event re-records exactly the writer's cancel** (PROTOCOL-60, the C1 gap): when the
writer's `cancel` of `c` signed `sig` recorded `r` and reached `w'`, the follower absorbing THE
tag-2 event of that record (`cancelEvent r.cancel r.event`, which `Host.Page.stepEvent` serves for
it: `Host.Page.stepEvent_cancel`) takes the same record to the same World, so its chain keeps the
writer's. Before tag 2 the page served `1 ‖ call`: the follower's `judge` re-derived a record with
no signature (or admitted the call), and its chain broke on the first cancel. -/
theorem absorbStep_cancelEvent {X : Ctx D} {w w' : World D} {c : Call D} {sig : ByteArray}
    {v : Verdict D} {r : Refused D} (hdec : X.decodeCall (X.callBytes c) = some c)
    (hc : Receive.cancel X w c sig = .recorded v r w') :
    absorbStep X w (cancelEvent r.cancel r.event) = .ok (.refusal r, w') := by
  obtain ⟨ha, -, rfl, -⟩ := cancel_recorded hc
  obtain ⟨hpos, hle⟩ := cancelAuth_size ha
  have he : eventOf (cancelEvent sig (X.callBytes c)) = some (.cancel sig (X.callBytes c)) :=
    eventOf_eventBytes (ev := .cancel sig (X.callBytes c)) (fun s b h => by cases h; exact ⟨hpos, hle⟩)
  show absorbStep X w (cancelEvent sig (X.callBytes c)) = _
  simp only [absorbStep, he, rederive, hdec, hc, Except.mapError]

/-! ## `read OBJ` of a programmed object (PROTOCOL-48) -/

/-- `stateValue`'s value is the one `Lang.readState` reads at the package's state row. -/
theorem stateValue_reads {X : Ctx D} {w : World D} {obj : D} {cell : Cell}
    {row : List (Lang.Label × Lang.Ty)} {d : Lang.Data}
    (h : stateValue X w obj cell = .ok (some (row, d))) :
    Lang.readState X.digestOf row (stateOf cell) = .ok d := by
  unfold stateValue objectPackage at h
  simp only [bind, Except.bind, Except.mapError] at h
  repeat' split at h
  all_goals (try simp only [pure, Except.pure, reduceCtorEq, Except.ok.injEq, Option.some.injEq,
    Prod.mk.injEq] at h)
  all_goals (try (obtain ⟨rfl, rfl⟩ := h))
  all_goals (try assumption)
  all_goals (try cases h)

/-- **`read OBJ` of a programmed object prints exactly what `Lang.Read` reads back to its state**: the
one line is `Lang.Print.data` of the value `Lang.readState` reads at the package's state row, and
`Lang.Read.readData` at that row reads the line back to that very value (`Lang.Print.readData_data`). -/
theorem readText_reads {X : Ctx D} {w : World D} {obj : D} {cell : Cell}
    {row : List (Lang.Label × Lang.Ty)} {d : Lang.Data} {out : String}
    (hv : stateValue X w obj cell = .ok (some (row, d))) (ht : readText X w obj cell = .ok out) :
    ∃ t, out = t ++ "\n" ∧ Lang.Read.readData (.record row) t = .ok d := by
  have hr := stateValue_reads hv
  unfold readText at ht
  rw [hv] at ht
  simp only [bind, Except.bind] at ht
  split at ht
  · rename_i hwf
    split at ht
    · rename_i t hp
      simp only [pure, Except.pure, Except.ok.injEq] at ht
      exact ⟨t, ht.symm, Lang.Print.readData_data (Lang.readState_conforms hr) hwf hp⟩
    · cases ht
  · cases ht


/-! ## A method's refusal by its own name (cv 01a15039) -/

omit [Ord D] [DecidableEq D] in
/-- **A method's refusal reaches the member's output in its own words** (cv 01a15039, LANG-51's
`refuse T "why"`): `refused program` stays the verdict on stderr, and the reason LANG gave (the
Bell's `answer: refused notResident`) is the hint line on stdout, on one line. -/
theorem refusedAt_program (X : Ctx D) (why : String) :
    refusedAt X (.receive (.program why)) =
      .done CommandExit.refused.code.toUInt8 s!"hint program: {oneLine why}\n".toUTF8
        s!"refused program\n".toUTF8 := rfl

/-! ## Stale BEHIND, from the member's own fold (KERNEL-54, PROTOCOL-15's conditions 1 and 2) -/

/-- **What `staleBehind` says** (PROTOCOL-73): the member's own call for its own World, planned at a
height follow has reached, whose authority follow's World passes (`signedBy`) and whose pins it refuses
(`checkPins`, which refuses nothing but `stale`): the Host's own first two judgements, in its order. -/
theorem staleBehind_spec {X : Ctx D} {me : Self D} {w : World D} {c : Call D}
    (h : staleBehind X me w c = true) :
    c.unsigned.member = me.member ∧ c.unsigned.world = me.world ∧ c.unsigned.notBefore ≤ w.height ∧
      signedBy X w c false = .ok () ∧
      ∃ x, checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges = .error (.stale x) := by
  unfold staleBehind at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, hw⟩, hn⟩, hr⟩ := h
  refine ⟨hm, hw, hn, ?_⟩
  split at hr
  · cases hr
  · rename_i hs
    split at hr
    · rename_i e he
      obtain ⟨x, rfl⟩ := checkPins_error_stale he
      exact ⟨hs, x, he⟩
    · cases hr

/-- **The Host declines exactly what `staleBehind` says** (PROTOCOL-73, law 1 with KERNEL-66): where
the call is neither journaled nor recorded, `staleBehind` holds only of a call `submit` refuses `stale`
and `judge` declines (never records): the client's word and the Host's are one function's. -/
theorem staleBehind_declined {X : Ctx D} {me : Self D} {w : World D} {c : Call D}
    (hj : w.journalAt X.env (txIdOf X c) = none) (hr : refusedAnswer X w c = none)
    (h : staleBehind X me w c = true) :
    ∃ y, submit X w c = .error (.rejected (.stale y)) ∧ judge X w c = .declined (.rejected (.stale y)) := by
  obtain ⟨-, -, -, hsb, x, hp⟩ := staleBehind_spec h
  have hs : submit X w c = .error (.rejected (.stale x)) := by
    unfold submit; rw [hj, hr, hsb]; simp only [hp]
  exact ⟨x, hs, judge_stale_declined hs rfl⟩

/-- **A call this World would admit is never stale BEHIND here** (the tooth of the settlement's
stale arm): wherever `submit` admits the call, `staleBehind` is false, so its settlement there is
never `refused stale`. -/
theorem staleBehind_admissible {X : Ctx D} {me : Self D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) : staleBehind X me w c = false := by
  cases h : staleBehind X me w c with
  | false => rfl
  | true =>
    obtain ⟨-, -, -, hsb, x, hp⟩ := staleBehind_spec h
    have hs' := hs
    unfold submit at hs'
    split at hs'
    · cases hs'
    · split at hs'
      · cases hs'
      · rw [hsb] at hs'; simp only [hp] at hs'; cases hs'

omit [Ord D] [DecidableEq D] in
/-- **The settlement's stale arm** (`Settle.ofReceipt`): an absent receipt inside a live window
that the journal still answers settles `refused staleCode` exactly when follow's fold says stale
BEHIND, and `open` otherwise. With `b` = `staleBehind` (`Command.settleOf`, what `receipt CALL`
prints): `Settle.settleOf_stale` and `Settle.settleOf_admissible_open`. -/
theorem settle_absent_stale {fg b : Bool} {H vu : Nat} (hf : fg = false) (hv : ¬ vu ≤ H) :
    Settle.ofReceipt (D := D) fg b H vu .absent = (if b then .refused staleCode else .open) := by
  subst hf
  cases b <;> simp [Settle.ofReceipt, hv]

/-! ## `read OBJ REL K [PREFIX]` (PROTOCOL-51) -/

omit [Ord D] [DecidableEq D] in
/-- An `Option` `mapM` that succeeds keeps the length and pairs each output with its input. -/
theorem mapM_some_zip {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.length = xs.length ∧ ∀ p ∈ ys.zip xs, f p.2 = some p.1
  | [], ys, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hl : xs.mapM f with
      | none => simp [hx, hl] at h
      | some ys' =>
        simp only [hx, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hz⟩ := mapM_some_zip hl
        refine ⟨by simp [hlen], fun p hp => ?_⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact hz p hp

/-- The relation `relationOf` names is the package's own: `objectPackage` (the package every method
run loads) declares it at index `i` (the kernel's `rel`) as `d`. -/
theorem relationOf_spec {X : Ctx D} {w : World D} {obj : D} {cell : Cell} {rel : String} {i : Nat}
    {d : Lang.RelDecl} (h : relationOf X w obj cell rel = .ok (i, d)) :
    ∃ pk, objectPackage X w obj cell = .ok (some pk) ∧ Lang.relIndex pk.rels rel = some i ∧
      Lang.Row.find? rel pk.rels = some d := by
  unfold relationOf at h
  split at h
  · cases h
  · cases h
  · rename_i pk hp
    split at h
    · rename_i i' d' hi hd
      cases h
      exact ⟨pk, hp, hi, hd⟩
    · cases h

/-- **`rangeListing` is THE range read's listing**: the prefix's bytes, `Kernel.rangeOf`'s rows (not
refused past K), and a prefix no wider than the relation's keys. -/
theorem rangeListing_ok {X : Ctx D} {w : World D} {obj : D} {i : Nat} {d : Lang.RelDecl} {most : Nat}
    {pre : Option String} {pb : ByteArray} {width : Nat} {l : List (RowSlot D × RowLeaf)}
    (h : rangeListing X w obj i d most pre = .ok (pb, width, l)) :
    prefixBytes d pre = some pb ∧ rangeOf X.env w.rows obj i pb most = some (width, some l) ∧
      pb.size ≤ width := by
  unfold rangeListing at h
  cases hpb : prefixBytes d pre with
  | none => rw [hpb] at h; cases h
  | some pb' =>
    rw [hpb] at h
    simp only at h
    cases hro : rangeOf X.env w.rows obj i pb' most with
    | none => rw [hro] at h; cases h
    | some q =>
      obtain ⟨width', lo⟩ := q
      rw [hro] at h
      simp only at h
      by_cases hw : pb'.size ≤ width'
      · rw [if_pos hw] at h
        cases lo with
        | none => cases h
        | some l' => cases h; exact ⟨rfl, hro, hw⟩
      · rw [if_neg hw] at h; cases h

/-- **`read OBJ REL K [PREFIX]` prints exactly the range read's rows, each on a line `Lang.Read`
reads back to its row** (PROTOCOL-51). Lines `ts` mean: the object's package declares REL (index `i`,
declaration `d`); K is within the declared `limit`; PREFIX is the bytes `pb`, at most the key width;
THE range read (`Kernel.rangeOf`, a method's range read's own function) lists `l` (not refused);
`Lang.rangeRowData` (a method's range slots' own conversion) makes it the data `ds`; there is ONE
line per listed row (`ts.length = l.length = ds.length`: none dropped, none added); and each line,
paired with its datum (`ts.zip ds`), is `Lang.Print.data` text that `Lang.Read.readData` at the
relation's row type reads back to that datum, the datum of the listed row in the same place, with
no line break in it (`Lang.Print.data_one_line`). What `l` holds — the
rows under `obj` and REL whose key starts with the prefix, in ascending key-byte order, at most K —
is `Kernel.range_rows_exact` (premise `pb.size ≤ width` given here). -/
theorem rangeLines_reads {X : Ctx D} {w : World D} {obj : D} {cell : Cell} {rel : String} {most : Nat}
    {pre : Option String} {ts : List String} (h : rangeLines X w obj cell rel most pre = .ok ts) :
    ∃ i d pb width l ds, relationOf X w obj cell rel = .ok (i, d) ∧ most ≤ d.limit ∧
      prefixBytes d pre = some pb ∧ rangeOf X.env w.rows obj i pb most = some (width, some l) ∧
      pb.size ≤ width ∧ Lang.rangeRowData X.digestOf rel d l = .ok ds ∧ ts.length = l.length ∧
      ts.length = ds.length ∧
      ∀ p ∈ ts.zip ds, Lang.Read.readData (Lang.rowTy d) p.1 = .ok p.2 ∧
        ∀ c ∈ p.1.toList, c ≠ '\n' ∧ c ≠ '\r' := by
  unfold rangeLines at h
  cases hrel : relationOf X w obj cell rel with
  | error r => rw [hrel] at h; cases h
  | ok p =>
    obtain ⟨i, d⟩ := p
    rw [hrel] at h
    simp only at h
    by_cases hlim : most ≤ d.limit
    · rw [if_pos hlim] at h
      unfold rowLines at h
      cases hL : rangeListing X w obj i d most pre with
      | error r => rw [hL] at h; cases h
      | ok q =>
        obtain ⟨pb, width, l⟩ := q
        obtain ⟨hpb, hro, hw⟩ := rangeListing_ok hL
        rw [hL] at h
        simp only at h
        cases hds : Lang.rangeRowData X.digestOf rel d l with
        | error r => rw [hds] at h; cases h
        | ok ds =>
          rw [hds] at h
          simp only at h
          by_cases hwf : (Lang.rowTy d).wf = true
          · rw [if_pos hwf] at h
            cases hts : ds.mapM Lang.Print.data with
            | none => rw [hts] at h; cases h
            | some ts' =>
              rw [hts] at h
              cases h
              obtain ⟨hlen, hz⟩ := mapM_some_zip hts
              refine ⟨i, d, pb, width, l, ds, rfl, hlim, hpb, hro, hw, hds, ?_, hlen, ?_⟩
              · rw [hlen, Lang.rangeRowData_length hds]
              · intro p hp
                have hd := hz p hp
                exact ⟨Lang.Print.readData_data
                    (Lang.rangeRowData_conforms hds p.2 (List.of_mem_zip hp).2) hwf hd,
                  Lang.Print.data_one_line hd⟩
          · rw [if_neg hwf] at h; cases h
    · rw [if_neg hlim] at h; cases h

/-- **K past the declared `limit` is refused by name** (PROTOCOL-51): `rangePastLimit`, before any
row is read. -/
theorem rangeLines_pastLimit {X : Ctx D} {w : World D} {obj : D} {cell : Cell} {rel : String}
    {most i : Nat} {d : Lang.RelDecl} {pre : Option String} (hrel : relationOf X w obj cell rel = .ok (i, d))
    (hk : d.limit < most) :
    rangeLines X w obj cell rel most pre = .error (.rangePastLimit most) := by
  unfold rangeLines
  rw [hrel]
  simp only
  rw [if_neg (by omega)]

/-! ## `pageIo` is "not now" (HOST-48, PROTOCOL-49)

Only two phases receive a page reply: the log phase (2, a `.host .log` page) and adopt's base-page
phase (7, a `.host .read` page). No other phase (3, 5, 8, the submit) is answered by a page, so these
two theorems are every place a `pageIo` reply can arrive. Each returns follow's state `f` unchanged
with `.steps []`: the pages earlier steps absorbed were persisted by those steps and stay. -/

/-- The writer's reply to a page whose IO failed, as a step result: `refused ‖ pageIo`. -/
theorem pageIo_hostReply :
    hostReply (ByteArray.mk #[Status.refused.code] ++ pageIoName.toByteArray) =
      some (.refused, pageIoName.toByteArray) := by decide

theorem pageIo_not_expired : expiredHeight? pageIoName.toByteArray = none := by decide

theorem pageIo_ne_unknownKey : pageIoName.toByteArray ≠ ReadRefusal.unknownKey.payload := by decide

/-- `notServed` ends with the code `pageIo`, never `refused`'s (restart class: `CommandExit.pageIo_restart`). -/
theorem notServed_code : (∃ out err, notServed = .done CommandExit.pageIo.code.toUInt8 out err) ∧
    CommandExit.pageIo.code ≠ CommandExit.refused.code :=
  ⟨⟨_, _, rfl⟩, by decide⟩

/-- **A page refused `pageIo` ends a catch-up restart-class** (HOST-48): at the log phase (2) of any
verb but `init`, the writer's `refused pageIo` is answered `notServed`, follow's state unchanged and
nothing persisted, never `refused` (exit 1). The three u64 fields hold as every state the machine
writes holds them. -/
theorem step_pageIo_log {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f : Follow D} {kb a b c d e : ByteArray} {argv : List ByteArray} {cmd : Cmd D} {s u t : Nat}
    (hst : State.ofBytes kb = some ⟨argv, 2, [a, b, c, d, e]⟩) (hp : parse X.digestOf argv = .ok cmd)
    (hni : ∀ sp, cmd ≠ .init sp) (ha : Text.ofU64 a = some s) (hd : Text.ofU64 d = some u)
    (he : Text.ofU64 e = some t) :
    step X dc B me f kb (ByteArray.mk #[Status.refused.code] ++ pageIoName.toUTF8) =
      (f, .steps [], notServed) := by
  unfold step
  simp only [hst, Option.map_some, Option.getD_some, hp]
  cases cmd
  case init sp => exact absurd rfl (hni sp)
  all_goals simp [stepResult, custodyPhase, pageIo_hostReply, envelopeRefused, pageIo_not_expired, pageIo_ne_unknownKey, ha, hd, he]

/-- **A base page refused `pageIo` ends an adoption restart-class** (HOST-48): at adopt's base-page
phase (7), the writer's `refused pageIo` is answered `notServed`, follow's state (its download in
progress included) unchanged and nothing persisted, never `refused`. -/
theorem step_pageIo_base {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f : Follow D} {kb o pg u t : ByteArray} {argv : List ByteArray} {inv key : ByteArray} {i : Invite.Invitation D}
    {off pages upTo tried : Nat}
    (hst : State.ofBytes kb = some ⟨argv, 7, [o, pg, u, t]⟩) (hp : parse X.digestOf argv = .ok (.adopt inv key))
    (hi : adoptPin X me inv key = .ok i) (ho : Text.ofU64 o = some off) (hpg : Text.ofU64 pg = some pages)
    (hu : Text.ofU64 u = some upTo) (ht : Text.ofU64 t = some tried) :
    step X dc B me f kb (ByteArray.mk #[Status.refused.code] ++ pageIoName.toUTF8) =
      (f, .steps [], notServed) := by
  unfold step
  simp only [hst, Option.map_some, Option.getD_some, hp]
  simp [stepResult, custodyPhase, pageIo_hostReply, pageIo_not_expired, hi, ho, hpg, hu, ht]

/-! ## The `uncertain` hint (cv 01a150b1) -/

/-- A recorded code's name is one of the kernel's two name tables. -/
theorem codeName_mem {k : Nat} {n : String} (h : codeName k = some n) :
    n ∈ refusalNames ++ rejectNames := by
  unfold codeName at h
  split at h
  · exact List.mem_append_left _ (List.mem_of_getElem? h)
  · exact List.mem_append_right _ (List.mem_of_getElem? h)

omit [Ord D] [DecidableEq D] in
/-- **Every refusal follow's machine prints is in `hintNames`, but the Host's word**: the table a hint
is read against misses no name Lean's own refusals produce. -/
theorem hintNames_complete (r : Refusal D) (h : ∀ n, r ≠ .host n) : r.name ∈ hintNames := by
  cases r with
  | host n => exact absurd rfl (h n)
  | receive r =>
      have hm := codeName_mem (codeName_code (D := D) (.refused r))
      simp only [Verdict.name] at hm
      simp only [Refusal.name, hintNames, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl (Or.inr hm)
      · exact Or.inr hm
  | reject r =>
      have hm := codeName_mem (codeName_code (D := D) (.rejected r))
      simp only [Verdict.name] at hm
      simp only [Refusal.name, hintNames, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl (Or.inr hm)
      · exact Or.inr hm
  | parse p =>
      cases p <;> simp [Refusal.name, ParseRefusal.name, hintNames, hintReps]
  | thin t =>
      cases t <;> simp [Refusal.name, Thin.Refusal.name, hintNames, hintReps]
  | custody c =>
      cases c <;> simp [Refusal.name, CustodyRefusal.name, CustodyRefusal.all, hintNames, hintReps]
  | invite i =>
      cases i with
      | inputs g => cases g <;> simp [Refusal.name, Invite.Refusal.name, GenesisRefusal.name, hintNames, hintReps]
      | _ => simp [Refusal.name, Invite.Refusal.name, hintNames, hintReps]
  | attest a =>
      cases a <;> simp [Refusal.name, Head.Refusal.name, Head.Refusal.all, hintNames, hintReps]
  | certified a =>
      cases a <;> simp [Refusal.name, Head.CertRefusal.name, Head.CertRefusal.all, hintNames, hintReps]
  | _ => simp [Refusal.name, hintNames, hintReps]

/-- **The hint is read iff** the payload is at most `Bounds.hintBytesMax` bytes and its first line
is byte for byte `refused NAME`, NAME in `hintNames`. -/
theorem confirmHint_iff (p : ByteArray) (n : String) :
    confirmHint p = some n ↔ p.size ≤ Bounds.hintBytesMax ∧ n ∈ hintNames ∧
      firstLine p = ("refused " ++ n).toUTF8 := by
  unfold confirmHint
  constructor
  · intro h
    split at h
    · rename_i hs
      have h2 := List.find?_some h
      simp only [decide_eq_true_eq] at h2
      exact ⟨hs, List.mem_of_find?_eq_some h, h2⟩
    · cases h
  · rintro ⟨hs, hm, hl⟩
    rw [if_pos hs]
    obtain ⟨m, hfm⟩ : ∃ m, hintNames.find?
        (fun n => decide (firstLine p = ("refused " ++ n).toUTF8)) = some m :=
      Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨n, hm, decide_eq_true hl⟩)
    rw [hfm]
    have hl' := List.find?_some hfm
    simp only [decide_eq_true_eq] at hl'
    rw [hl] at hl'
    simp only [String.toUTF8_eq_toByteArray] at hl'
    rw [(String.append_right_inj "refused ").1 (String.toByteArray_inj.1 hl')]

/-- The tooth: a NAME outside Lean's table (any other text, a Host name the table lacks) is never
shown as a hint, whatever the payload. -/
theorem confirmHint_foreign {p : ByteArray} {n : String} (h : n ∉ hintNames) : confirmHint p ≠ some n :=
  fun hc => h ((confirmHint_iff p n).1 hc).2.1

/-- Liveness: the refusal PROTOCOL-55 found, follow's `refused badResult` line, is read as its hint. -/
theorem confirmHint_badResult : confirmHint "refused badResult\n".toUTF8 = some "badResult" := by
  decide +kernel

/-- **`settled`'s `uncertain` arm**: exit `uncertain`, `uncertain` on stderr, and on stdout the hint
`confirmHint` reads from the attempt's payload, or nothing. -/
theorem settled_uncertain (X : Ctx D) (me : Self D) (w : World D) (out cb p : ByteArray) :
    settled X me w out cb (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p) =
      .done CommandExit.uncertain.code.toUInt8 (uncertainOut p) "uncertain\n".toUTF8 := by
  have hsz : (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).size = 1 + p.size := by
    simp [ByteArray.size_append]
  have hx : (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).extract 1
      (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).size = p := by
    rw [hsz]; exact ByteArray.extract_append_eq_right rfl (by simp)
  unfold settled
  rw [dif_pos (by omega), hx]
  rfl

/-! ## `cancel CALL` (PROTOCOL-63) -/

/-- **A well-formed cancel event its own re-judge does not record is `cancelForged`**: a tag-2 event
whose parts read and whose call decodes, but that `Receive.cancel` on follow's World does not
record under the event's signature (it does not verify under the call's member's key there, the
call names another World, or `World.refuse` declines it), is refused by the name the follower's
re-derivation gives it (`Receive.rederive`: `cancelForged`), never the positional `eventMismatch`. -/
theorem absorbStep_cancelForged {X : Ctx D} {w : World D} {e sig cb : ByteArray} {c : Call D}
    (h0 : e[0]? = some eventCancel) (hp : cancelParts e = some (sig, cb)) (hc : X.decodeCall cb = some c)
    (hn : ∀ v r w', Receive.cancel X w c sig ≠ .recorded v r w') :
    absorbStep X w e = .error (.receive .cancelForged) := by
  have hpos : 0 < e.size := by
    rcases Nat.eq_zero_or_pos e.size with hz | hz
    · rw [getElem?_neg e 0 (by omega)] at h0; cases h0
    · exact hz
  have he : e[0] = eventCancel := by
    rw [getElem?_pos e 0 hpos] at h0; exact Option.some.inj h0
  have hev : eventOf e = some (.cancel sig cb) := by
    unfold eventOf
    rw [dif_pos hpos, if_pos he, hp]
    rfl
  have hrd : Receive.rederive X w (.cancel sig cb) = .error (.refused .cancelForged) := by
    cases hrc : Receive.cancel X w c sig with
    | recorded v r w' => exact absurd hrc (hn v r w')
    | admitted t w' => simp only [rederive, hc, hrc]
    | declined v => simp only [rederive, hc, hrc]
  rw [show absorbStep X w e = (Receive.rederive X w (.cancel sig cb)).mapError
    (ofVerdict (w.steps + 1)) by simp only [absorbStep, hev], hrd]
  rfl

/-- **A cancel admits nothing** (law 1 beside `Op.effect_write_iff`): `Receive.cancel` only records a
refusal or declines. The writer's `cancel` op takes exactly its World and its staging
(`Host.step_cancel`, HOST-66), so with this `submit` stays the one admission path. -/
theorem cancel_never_admits (X : Ctx D) (w : World D) (c : Call D) (sig : ByteArray) (t : Turn D)
    (w' : World D) : Receive.cancel X w c sig ≠ .admitted t w' := by
  unfold Receive.cancel
  split
  · exact fun h => by cases h
  · split <;> exact fun h => by cases h

/-- **Follow sends only a cancel its own World records** (PROTOCOL-63): when phase 9 of `cancel CALL`
(`sendCancel`) relays an op, the op is `cancel`, its payload is THE tag-2 event of custody's
signature and the call (`cancelEvent`, the bytes the log will serve, `absorbStep_cancelEvent`), and
`Receive.cancel` on follow's World records that cancel: the call decodes and names this World, and
custody's signature verifies under the call's member's current key there (`cancel_recorded`'s
`cancelAuth`) inside the call's window. So, on follow's World, a cancel of another member's
call, of a call past its window or of one already recorded is not relayed by this phase; that no
OTHER arm relays `cancel` is `step_host_cancel`. -/
theorem sendCancel_host {X : Ctx D} {w : World D} {argv : List ByteArray} {cb result : ByteArray}
    {op : Op} {p k : ByteArray} (h : sendCancel X w argv cb result = .host op p k) :
    op = .cancel ∧ ∃ s c v r w', Signed.ofBytes result = some s ∧ X.decodeCall cb = some c ∧
      Receive.cancel X w c s.signature = .recorded v r w' ∧ p = cancelEvent s.signature cb := by
  unfold sendCancel at h
  split at h
  · rename_i s c hs hc
    split at h
    · rename_i v r w' hrec
      unfold next at h
      split at h
      · simp only [Reply.host.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, s, c, v, r, w', hs, hc, hrec, rfl⟩
      · simp [refused] at h
    all_goals first
      | (unfold refusedAt at h; split at h <;> simp [refused] at h)
      | simp [refused] at h
  all_goals simp [refused] at h

/-- The tooth: a cancel `Receive.cancel` declines on follow's World is never relayed. -/
theorem sendCancel_declined_not_host {X : Ctx D} {w : World D} {argv : List ByteArray}
    {cb result : ByteArray} {s : Signed} {c : Call D} {v : Verdict D}
    (hs : Signed.ofBytes result = some s) (hc : X.decodeCall cb = some c)
    (hd : Receive.cancel X w c s.signature = .declined v) (op : Op) (p k : ByteArray) :
    sendCancel X w argv cb result ≠ .host op p k := by
  intro h
  obtain ⟨-, s', c', _, _, _, hs', hc', hrec, -⟩ := sendCancel_host h
  rw [hs] at hs'; cases hs'
  rw [hc] at hc'; cases hc'
  rw [hd] at hrec; cases hrec

/-! ### No helper relays an op (PROTOCOL-63: `step_host_cancel`) -/

omit [Ord D] [DecidableEq D] in
theorem refusedAt_ne_host {X : Ctx D} {r : Refusal D} {op : Op} {p k : ByteArray} :
    refusedAt X r ≠ .host op p k := by
  unfold refusedAt; split <;> simp [refused]

theorem describe_ne_host {X : Ctx D} {w : World D} {obj : D} {op : Op} {p k : ByteArray} :
    describe X w obj ≠ .host op p k := by
  unfold describe
  repeat' split
  all_goals simp [refused, printed]

theorem rangeRender_ne_host {X : Ctx D} {w : World D} {obj : D} {rel : String} {most : Nat}
    {pre : Option String} {op : Op} {p k : ByteArray} : rangeRender X w obj rel most pre ≠ .host op p k := by
  unfold rangeRender
  split
  · simp [refused]
  · split <;> simp [refused, printed]

omit [Ord D] [DecidableEq D] in
theorem envelopeSign_ne_host {t : Nat} {m k' : ByteArray} {op : Op} {p k : ByteArray} :
    envelopeSign t m k' ≠ .host op p k := by
  unfold envelopeSign; split <;> simp

omit [Ord D] [DecidableEq D] in
theorem unknownKeyEnd_ne_host {X : Ctx D} {cmd : Cmd D} {op : Op} {p k : ByteArray} :
    unknownKeyEnd X cmd ≠ .host op p k := by
  intro h; unfold unknownKeyEnd at h; split at h
  · simp [refused] at h
  · exact refusedAt_ne_host h

omit [Ord D] [DecidableEq D] in
theorem custodyEnd_ne_host {X : Ctx D} {cmd : Cmd D} {st : State} {r : Refusal D} {op : Op}
    {p k : ByteArray} : custodyEnd X cmd st r ≠ .host op p k := by
  intro h; unfold custodyEnd at h; split at h
  · split at h
    · exact unknownKeyEnd_ne_host h
    · simp [refused] at h
  · simp [refused] at h

omit [Ord D] [DecidableEq D] in
theorem envelopeRefused_ne_host {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p' : ByteArray} {op : Op} {p k : ByteArray} : envelopeRefused X me argv cmd a b c d p' ≠ .host op p k := by
  intro h
  unfold envelopeRefused next at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_host h | (simp [refused] at h; done) | (simp [notServed] at h; done) | exact unknownKeyEnd_ne_host h | ((try dsimp only at h); exact envelopeSign_ne_host h) | simp at h

theorem receiptLines_ne_host {X : Ctx D} {dc : Codec.Stream D} {me : Self D} {w : World D}
    {cb : ByteArray} {op : Op} {p k : ByteArray} : receiptLines X dc me w cb ≠ .host op p k := by
  intro h
  unfold receiptLines at h
  repeat' split at h
  all_goals simp [refused, printed] at h

omit [DecidableEq D] in
theorem cancelCatchUp_ne_host {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {said : Nat} {op : Op} {p k : ByteArray} : cancelCatchUp X me w argv said ≠ .host op p k := by
  intro h
  unfold cancelCatchUp next at h
  dsimp only at h
  split at h <;> simp [refused] at h

omit [DecidableEq D] in
theorem cancelAnswer_ne_host {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {result : ByteArray} {op : Op} {p k : ByteArray} : cancelAnswer X me w argv result ≠ .host op p k := by
  intro h
  unfold cancelAnswer at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_host h | exact cancelCatchUp_ne_host h | simp [refused, declined] at h

theorem cancelSettled_ne_host {X : Ctx D} {me : Self D} {w : World D} {c : Call D} {said : Bool}
    {op : Op} {p k : ByteArray} : cancelSettled X me w c said ≠ .host op p k := by
  intro h
  unfold cancelSettled attemptContradicted at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_host h | simp [refused, printed] at h

omit [DecidableEq D] in
theorem attestTip_ne_host {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {sb : ByteArray} {op : Op} {p k : ByteArray} : attestTip X me w argv sb ≠ .host op p k := by
  intro h
  unfold attestTip next at h
  repeat' split at h
  all_goals simp [refused] at h

theorem syncTip_ne_host {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {sb : ByteArray} {mode : SyncMode} {op : Op} {p k : ByteArray} : syncTip X me w argv sb mode ≠ .host op p k := by
  intro h
  cases mode with
  | attest => exact attestTip_ne_host h
  | tip => simp [syncTip, printed] at h
  | to steps chain => simp [syncTip, printed] at h
  | check b =>
      simp only [syncTip] at h
      repeat' split at h
      all_goals simp [refused, printed] at h

omit [Ord D] [DecidableEq D] in
theorem attestDone_ne_host {sb u result : ByteArray} {op : Op} {p k : ByteArray} :
    attestDone (D := D) sb u result ≠ .host op p k := by
  intro h
  unfold attestDone at h
  repeat' split at h
  all_goals simp [refused, printed] at h

theorem cancelTip_ne_host {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {cb t : ByteArray} {op : Op} {p k : ByteArray} : cancelTip X me w argv cb t ≠ .host op p k := by
  intro h; unfold cancelTip at h
  repeat' split at h
  all_goals first
    | (simp [refused] at h; done)
    | (unfold next at h; split at h <;> simp [refused] at h; done)
    | exact cancelSettled_ne_host h

theorem settled_ne_host {X : Ctx D} {me : Self D} {w : World D} {out cb result : ByteArray} {op : Op}
    {p k : ByteArray} : settled X me w out cb result ≠ .host op p k := by
  intro h
  unfold settled at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_host h | simp [refused, declined] at h
  all_goals (unfold attemptContradicted at h; split at h <;> simp [refused] at h)

theorem settleStep_ne_host {X : Ctx D} {me : Self D} {w : World D} {cmd : Cmd D}
    {out cb result : ByteArray} {op : Op} {p k : ByteArray} : settleStep X me w cmd out cb result ≠ .host op p k := by
  intro h; unfold settleStep at h; split at h
  · exact settled_ne_host h
  · simp [refused] at h

/-- **Every `cancel` op follow ever relays is a cancel its own World records** (PROTOCOL-63; the
whole machine, not one phase): if `step` hands the client a `host` step for the `cancel` op, follow's
state is unchanged and the payload is THE tag-2 event `cancelEvent s.signature cb` of a call `c`
that `cb` decodes to, which `Receive.cancel` on follow's World records under that signature (so
`cancelAuth` held there: the signature verifies under the CALL's member's key, inside the call's
window ON FOLLOW'S WORLD, not yet recorded there). It is phase 9's `sendCancel` (`sendCancel_host`);
no other arm relays `cancel`. -/
theorem step_host_cancel {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result pl k : ByteArray}
    (h : step X dc B me f kb result = (f', p, .host .cancel pl k)) :
    f' = f ∧ p = .steps [] ∧ ∃ (s : Signed) (c : Call D) (v : Verdict D) (r : Refused D) (w' : World D) (cb : ByteArray),
      X.decodeCall cb = some c ∧
      Receive.cancel X f.world c s.signature = .recorded v r w' ∧ pl = cancelEvent s.signature cb := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind, notServed, Prod.mk.injEq, reduceCtorEq, and_false] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq, reduceCtorEq, and_false, Reply.host.injEq, false_and] at h)
  all_goals (try (obtain ⟨h1, h0, h2⟩ := h; have h := And.intro h1 (And.intro h0 (postOr_host_elim h2))))
  all_goals (try (simp only [reduceCtorEq, and_false] at h; done))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; unfold render at h; repeat' split at h
                  all_goals simp [refused, printed] at h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact custodyEnd_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact describe_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact rangeRender_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact refusedAt_ne_host h))
  all_goals (try (exfalso; exact refusedAt_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact envelopeRefused_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; (try dsimp only at h); exact envelopeSign_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact receiptLines_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact syncTip_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact attestDone_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact settleStep_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact cancelAnswer_ne_host h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact cancelTip_ne_host h))
  all_goals (try (obtain ⟨h1, h0, h2⟩ := h; subst h1 h0
                  obtain ⟨-, s, c, v, r, w', -, hc, hrec, hp⟩ := sendCancel_host h2
                  exact ⟨rfl, rfl, s, c, v, r, w', _, hc, hrec, hp⟩))
  done

/-! ### `cancel CALL` ends `ok` only on follow's own World (PROTOCOL-71) -/

omit [Ord D] [DecidableEq D] in
theorem refusedAt_ne_ok {X : Ctx D} {r : Refusal D} {o e : ByteArray} : refusedAt X r ≠ .done CommandExit.ok.code.toUInt8 o e := by
  unfold refusedAt; split <;> simp [refused, CommandExit.code]

omit [Ord D] [DecidableEq D] in
theorem custodyEnd_ne_ok {X : Ctx D} {cmd : Cmd D} {st : State} {r : Refusal D} {o e : ByteArray} :
    custodyEnd X cmd st r ≠ .done CommandExit.ok.code.toUInt8 o e := by
  intro h; unfold custodyEnd at h; split at h
  · split at h
    · unfold unknownKeyEnd at h; split at h
      · simp [refused, CommandExit.code] at h
      · exact refusedAt_ne_ok h
    · simp [refused, CommandExit.code] at h
  · simp [refused, CommandExit.code] at h

omit [Ord D] [DecidableEq D] in
theorem envelopeRefused_ne_ok {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p o e : ByteArray} : envelopeRefused X me argv cmd a b c d p ≠ .done CommandExit.ok.code.toUInt8 o e := by
  intro h
  unfold envelopeRefused next at h
  repeat' split at h
  all_goals first
    | exact refusedAt_ne_ok h
    | (simp [refused, notServed, CommandExit.code] at h; done)
    | (unfold unknownKeyEnd at h; split at h
       · simp [refused, CommandExit.code] at h
       · exact refusedAt_ne_ok h)
    | ((try dsimp only at h); unfold envelopeSign at h; split at h <;> simp at h)

theorem sendCancel_ne_ok {X : Ctx D} {w : World D} {argv : List ByteArray} {cb result o e : ByteArray} :
    sendCancel X w argv cb result ≠ .done CommandExit.ok.code.toUInt8 o e := by
  intro h
  unfold sendCancel next at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_ok h | simp [refused, CommandExit.code] at h

omit [DecidableEq D] in
theorem cancelAnswer_ne_ok {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {result o e : ByteArray} : cancelAnswer X me w argv result ≠ .done CommandExit.ok.code.toUInt8 o e := by
  intro h
  unfold cancelAnswer at h
  repeat' split at h
  all_goals first
    | exact refusedAt_ne_ok h
    | (unfold cancelCatchUp next at h; dsimp only at h; split at h <;> simp [refused, CommandExit.code] at h; done)
    | simp [refused, declined, CommandExit.code] at h

/-- **`cancelSettled` is `ok` only on follow's own settlement**: the writer said cancelled, and the
World the second catch-up reached settles the call `refused cancelled`. -/
theorem cancelSettled_ok {X : Ctx D} {me : Self D} {w : World D} {c : Call D} {said : Bool}
    {o e : ByteArray} (h : cancelSettled X me w c said = .done CommandExit.ok.code.toUInt8 o e) :
    said = true ∧ settleOf X me w c = .refused (cancelledCode (D := D)) := by
  unfold cancelSettled at h
  split at h
  · rename_i code hv
    split at h
    · rename_i hc; exact ⟨rfl, by rw [hv, hc]⟩
    · unfold attemptContradicted at h; simp [CommandExit.code] at h
  · exact absurd h refusedAt_ne_ok
  all_goals (unfold attemptContradicted at h; simp [CommandExit.code] at h)

theorem settleStep_ok {X : Ctx D} {me : Self D} {w : World D} {cmd : Cmd D} {out cb result o e : ByteArray}
    (h : settleStep X me w cmd out cb result = .done CommandExit.ok.code.toUInt8 o e) :
    submits cmd = true ∧ settled X me w out cb result = .done CommandExit.ok.code.toUInt8 o e := by
  unfold settleStep at h
  split at h
  · exact ⟨‹_›, h⟩
  · simp [refused, CommandExit.code] at h

/-- The tip of a cancel's catch-up is `ok` only by `cancelSettled`'s settlement. -/
theorem cancelTip_ok {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray} {cb t o e : ByteArray}
    (h : cancelTip X me w argv cb t = .done CommandExit.ok.code.toUInt8 o e) :
    ∃ c, X.decodeCall cb = some c ∧ settleOf X me w c = .refused (cancelledCode (D := D)) := by
  unfold cancelTip at h
  split at h
  · simp [refused, CommandExit.code] at h
  · simp [refused, CommandExit.code] at h
  · rename_i c _ hc _
    split at h
    · unfold next at h; split at h <;> simp [refused, CommandExit.code] at h
    · exact ⟨c, hc, (cancelSettled_ok h).2⟩

/-- **`cancel CALL` exits `ok` only when follow's own World records the cancel** (PROTOCOL-71, the
class PROTOCOL-64 closed at step 4; readers A7): whatever continuation and result the client hands
back, a step of a `cancel CALL` command that ends `done ok` has caught follow up to a World (the one
it answers with) whose settlement of the call is `refused cancelled`: the writer's `refused
cancelled` is never enough. Under any other phase a cancel's step refuses, asks, or is handed on. -/
theorem cancel_ok_settled {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result o e cb : ByteArray} {st : State}
    (hst : State.ofBytes kb = some st) (hcmd : parse X.digestOf st.argv = .ok (.cancel cb))
    (h : step X dc B me f kb result = (f', p, .done CommandExit.ok.code.toUInt8 o e)) :
    ∃ c, X.decodeCall cb = some c ∧ settleOf X me f'.world c = .refused (cancelledCode (D := D)) := by
  unfold step at h
  simp only [hst, Option.map_some, Option.getD_some, hcmd] at h
  repeat' split at h
  -- the arms of other verbs
  all_goals (try contradiction)
  all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨h1, -, h⟩ := h)
  all_goals (try (replace h := postOr_done_ok_elim h))
  all_goals (try (exfalso; first
    | exact refusedAt_ne_ok h
    | exact custodyEnd_ne_ok h
    | exact envelopeRefused_ne_ok h
    | exact sendCancel_ne_ok h
    | exact cancelAnswer_ne_ok h
    | (simp [refused, behind, CommandExit.code] at h; done)
    | (unfold envelopeSign at h; split at h <;> simp at h; done)
    | (unfold next at h; split at h
       · (try dsimp only at h); (try (unfold envelopeSign at h; split at h)) <;> simp at h
       · simp [refused, CommandExit.code] at h
       done)))
  -- phase 4 under a verb that does not submit
  all_goals (try (exfalso; have := (settleStep_ok h).1; simp [submits] at this; done))
  -- what is left: the settlement at the second catch-up's tip
  all_goals (subst h1; exact cancelTip_ok h)

end Nanodregg.Protocol.Command
