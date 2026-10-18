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
      · cases h
      · cases h; exact ⟨rfl, rfl, rfl⟩

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

omit [Ord D] [DecidableEq D] in
theorem envelopeSign_ne_submit {t : Nat} {m k' call k : ByteArray} : envelopeSign t m k' ≠ .submit call k := by
  unfold envelopeSign; split <;> simp

omit [Ord D] [DecidableEq D] in
/-- The PROTOCOL-46 arms answer no submit: a refused envelope, the receipt lines, a settlement. -/
theorem envelopeRefused_ne_submit {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p call k : ByteArray} : envelopeRefused X me argv cmd a b c d p ≠ .submit call k := by
  intro h
  unfold envelopeRefused next at h
  repeat' split at h
  all_goals first | exact refusedAt_ne_submit h | (simp [refused] at h; done) | ((try dsimp only at h); exact envelopeSign_ne_submit h)

theorem receiptLines_ne_submit {X : Ctx D} {dc : Codec.Stream D} {w : World D} {cb call k : ByteArray} :
    receiptLines X dc w cb ≠ .submit call k := by
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
    envelopeRefused X me argv cmd a b c d p =
      if readOnly cmd then refused (D := D) (.host "unknownKey") else refusedAt X (.host "unknownKey") := by
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
  simp [hk, hw]

/-- Consent at the wire: the only call `step` hands the client to submit is a call over a `u`
that `plan` produced on follow's own World (hence derived and admitted there, `plan_admits`). -/
theorem step_submit_planned {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D}
    {kb result call k : ByteArray} (h : step X dc B me f kb result = (f', p, .submit call k)) :
    f' = f ∧ p = .steps [] ∧ ∃ key b u sig, plan X me f.world key b = .ok u ∧ call = X.callBytes ⟨u, sig⟩ := by
  unfold step next at h
  repeat' split at h
  all_goals (try simp only [refused, printed, behind, Prod.mk.injEq, reduceCtorEq, and_false] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq, reduceCtorEq, and_false] at h)
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; unfold render at h; repeat' split at h
                  all_goals simp [refused, printed] at h))
  all_goals (try (exfalso; obtain ⟨_, _, h⟩ := h; exact describe_ne_submit h))
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
`followVerifyAll`, line 13) and the `refused` row (plant `admitsRecorded`). -/

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

end Nanodregg.Protocol.Command
