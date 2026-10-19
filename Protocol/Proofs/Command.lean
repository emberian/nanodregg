/-
# Protocol.Proofs.Command — the verbs, the parser's bound, and consent

Consent (PROTOCOL-4, HOST-9): the only call follow ever hands the client to submit is
`X.callBytes ⟨u, sig⟩` for a `u` that `plan` produced on follow's World — and `plan` produces `u`
only when the receivers derive a Turn from it on that World AND `World.admit` accepts that Turn.
So a member is never asked to submit a call its own fold refuses.
-/
import Kernel.Proofs.RootedFold
import Protocol.Command.Machine
import Protocol.Proofs.Table
import Kernel.Proofs.Receive
import Kernel.Proofs.Fold
import Kernel.Proofs.Refusals
import Kernel.Proofs.Audit
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
theorem planUnchecked_derives {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray} {b : Body D}
    {u : Unsigned D} {t : Turn D} (h : planUnchecked X me w key b = .ok (u, t)) :
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
theorem planUnchecked_rowPins {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray} {b : Body D}
    {u : Unsigned D} {t : Turn D} (h : planUnchecked X me w key b = .ok (u, t)) :
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
      · simp at hm
      · exact hk

/-- `plan` offers `u` only if follow's World derives a Turn from it and admits that Turn. -/
theorem plan_admits {X : Ctx D} {me : Self D} {w : World D} {key : ByteArray} {b : Body D}
    {u : Unsigned D} (h : plan X me w key b = .ok u) :
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
  split
  · simp [refused]
  · split <;> simp [refused, printed]

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

omit [Ord D] [DecidableEq D] in
theorem settled_ne_submit {X : Ctx D} {out result call k : ByteArray} :
    settled X out result ≠ .submit call k := by
  intro h
  unfold settled at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | simp [refused, declined] at h

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
that `plan` produced on follow's own World (hence derived and admitted there, `plan_admits`). -/
theorem step_submit_planned {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D}
    {kb result call k : ByteArray} (h : step X dc B me f kb result = (f', p, .submit call k)) :
    f' = f ∧ p = .steps [] ∧ ∃ key b u sig, plan X me f.world key b = .ok u ∧ call = X.callBytes ⟨u, sig⟩ := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind, notServed, Prod.mk.injEq, reduceCtorEq, and_false] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq, reduceCtorEq, and_false] at h)
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
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact settled_ne_submit h))
  all_goals (try (obtain ⟨h1, h0, h2⟩ := h; injection h2 with h3 h4; subst h1 h0 h3
                  exact ⟨rfl, rfl, _, _, _, _, ‹plan _ _ _ _ _ = _›, rfl⟩))
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
follow's own `judge` recorded it. The follow-time teeth are the rows' `audit` row (plant
`followVerifyAll`, line 13) and the `refusedFinal` row (plant `admitsRecorded`). -/

/-- One absorbed step is a step of follow's own World. -/
theorem absorbStep_step {X : Ctx D} {w w' : World D} {e : ByteArray} {s : Kernel.Step D}
    (h : absorbStep X w e = .ok (s, w')) : World.step X.env w s = .ok w' := by
  unfold absorbStep at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (obtain ⟨rfl, rfl⟩ := h)
  · exact (submit_ok ‹_›).2.2
  · exact (judge_recorded ‹_›).2.2.2

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
    | (obtain ⟨rfl, rfl, -⟩ := h; dsimp only; exact absorbPage_admits (by assumption))
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
    | (right; right; exact ⟨_, _, _, _, _, _, _, by assumption, rfl⟩)

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
  unfold absorbStep
  simp only [hpos, ↓reduceDIte, hdec, htag, ↓reduceIte, hs]

/-- What `judge` recorded for `c` is in the World it reached: `c` answers the verdict's code, which
names the verdict; nothing else about the World but the refusals and the step count moved. -/
theorem recorded_answers {X : Ctx D} {w w' : World D} {c : Call D} {v : Verdict D} {r : Refused D}
    (hj : judge X w c = .recorded v r w') :
    r = refusedOf X c v ∧ refusedAnswer X w' c = some v.code ∧ codeName v.code = some v.name ∧
      w'.height = w.height ∧ w'.steps = w.steps + 1 ∧ w'.journalAt X.env (txIdOf X c) = none := by
  obtain ⟨-, -, rfl, href⟩ := judge_recorded hj
  have hrec := refuse_recorded href
  obtain ⟨-, -, -, hjn, -, -⟩ := refuse_facts href
  refine ⟨rfl, ?_, codeName_code v, (refuse_frame href).2.2.1, refuse_steps href, ?_⟩
  · unfold refusedAnswer
    rw [show (refusedOf X c v).txId = txIdOf X c from rfl] at hrec
    rw [hrec]; rfl
  · rw [refuse_journalAt href]; exact hjn

/-- **An absorbed refusal answers its call by name.** After follow absorbs a refusal event for
call `c`, its World holds `c`'s recorded code (and no journal entry for it), and that code names the
verdict `judge` refused it with: so a later `submit` of `c` on that World is `refusedFinal`
(`Receive.submit`'s second arm) without re-deriving, and `lookup` answers `refused NAME`
(`Receive.codeName_code`). -/
theorem absorbStep_refusal_recorded {X : Ctx D} {w w' : World D} {e : ByteArray} {r : Refused D}
    (h : absorbStep X w e = .ok (.refusal r, w')) :
    ∃ c v, X.decodeCall (e.extract 1 e.size) = some c ∧ r = refusedOf X c v ∧
      refusedAnswer X w' c = some v.code ∧ codeName v.code = some v.name ∧ w'.height = w.height ∧
      w'.steps = w.steps + 1 ∧ w'.journalAt X.env (txIdOf X c) = none := by
  unfold absorbStep at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and,
    Kernel.Step.refusal.injEq] at h)
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, ‹_›, recorded_answers ‹_›⟩

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

/-- **What `staleBehind` says**: the member's own call for its own World, planned at a height
follow has reached, whose Turn follow's World derives and refuses `stale` by the kernel's name. -/
theorem staleBehind_spec {X : Ctx D} {me : Self D} {w : World D} {c : Call D}
    (h : staleBehind X me w c = true) :
    c.unsigned.member = me.member ∧ c.unsigned.world = me.world ∧ c.unsigned.notBefore ≤ w.height ∧
      ∃ t x, receive X w c = .ok t ∧ World.admit X.env w t = .error (.stale x) := by
  unfold staleBehind at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hm, hw⟩, hn⟩, hr⟩ := h
  refine ⟨hm, hw, hn, ?_⟩
  split at hr
  · rename_i t ht
    split at hr
    · rename_i x hx
      exact ⟨t, x, ht, hx⟩
    · cases hr
  · cases hr

/-- **A call this World would admit is never stale BEHIND here** (the tooth of the settlement's
stale arm): wherever `submit` admits the call, `staleBehind` is false, so its settlement there is
never `refused stale`. -/
theorem staleBehind_admissible {X : Ctx D} {me : Self D} {w w' : World D} {c : Call D} {t : Turn D}
    (hs : submit X w c = .ok (t, w')) : staleBehind X me w c = false := by
  obtain ⟨-, hr, ha⟩ := submit_ok hs
  cases h : staleBehind X me w c with
  | false => rfl
  | true =>
    obtain ⟨-, -, -, t', x, hr', ha'⟩ := staleBehind_spec h
    rw [hr] at hr'
    cases hr'
    rw [ha] at ha'
    cases ha'

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
      cases hpb : prefixBytes d pre with
      | none => rw [hpb] at h; cases h
      | some pb =>
        rw [hpb] at h
        simp only at h
        cases hro : rangeOf X.env w.rows obj i pb most with
        | none => rw [hro] at h; cases h
        | some q =>
          obtain ⟨width, lo⟩ := q
          rw [hro] at h
          simp only at h
          by_cases hw : pb.size ≤ width
          · rw [if_pos hw] at h
            cases lo with
            | none => cases h
            | some l =>
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
          · rw [if_neg hw] at h; cases h
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

omit [Ord D] [DecidableEq D] in
/-- **`settled`'s `uncertain` arm**: exit `uncertain`, `uncertain` on stderr, and on stdout the hint
`confirmHint` reads from the attempt's payload, or nothing. -/
theorem settled_uncertain (X : Ctx D) (out p : ByteArray) :
    settled X out (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p) =
      .done CommandExit.uncertain.code.toUInt8 (uncertainOut p) "uncertain\n".toUTF8 := by
  have hsz : (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).size = 1 + p.size := by
    simp [ByteArray.size_append]
  have hx : (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).extract 1
      (ByteArray.mk #[Attempt.Action.uncertain.code] ++ p).size = p := by
    rw [hsz]; exact ByteArray.extract_append_eq_right rfl (by simp)
  unfold settled
  rw [dif_pos (by omega), hx]
  rfl

end Nanodregg.Protocol.Command
