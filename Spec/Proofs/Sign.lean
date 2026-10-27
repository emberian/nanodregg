/-
# Spec.Proofs.Sign — C(i) SIGNING (TOPLEVEL-SPEC §4): what follow offers custody to sign

**What it promises.** One frame of the member's follower hands custody a message by three reply
constructors, `sign`, `signNext` and `signIncoming`. Their arms in `Command.step`:

* `sign`: an envelope (`envelopeMessage`: every catch-up page, the `expired` re-sign, `cancel`'s
  second catch-up), an adopt envelope (`adoptEnvelope`, an `envelopeMessage` too), `init`'s
  possession proof (`possessionMessage`), an invitation (`Invite.message`), a head attestation
  (`Head.message`, `sync --attest`), a cancel (`cancelMessage`), and a call (`callMessage u`, at
  the tip of a write's catch-up). (`start` also signs `whoami`; `System` has no `start` field.)
* `signNext`: only `rotate`'s call (`callMessage u`, phase 5).
* `signIncoming`: only envelopes (PROTOCOL-46).

A CALL signature is therefore not a reply constructor but a message in the call domain, and the
claims say so:

* `Consent.signs`: every message follow offers in the call domain (`callMessage v`, any `v`: exactly
  the messages a signature over which could authenticate a call) is `callMessage u` for the `u`
  `plan` produced on the World follow holds after the step (`f'.world`: the caught-up World at a
  write's tip; follow's World for `rotate`), from the `body` and `signedReads` of the command the
  continuation's argv parses to: the member's own call, its derived Turn admitted there by the
  system's kernel.
* `Consent.signShapes`: every message follow offers is one of six shapes, each its own domain
  (`Protocol.Proofs.Domains`): that planned call, an envelope of the member's own World, member and
  grant, a possession proof, an invitation, a head attestation, or a cancel.

**Premises.** None. What is OWED is named, not assumed: the argv (and custody's `Signed` result
the continuation carries, whose key is `u.key`) are client-held bytes, the relay's under an arbitrary
relay (SPEC-4). Per step the claims say what IS true: whatever is signed in the call domain was
planned from the argv the continuation carries, on follow's own World, and that World admits it.
"The member's own argv" needs the relay premise TOPLEVEL-SPEC §11.2 removes (the command's state
kept inside follow).

**Floor.** `relaySigner` checks that the continuation decodes and its argv parses, then has custody
sign the Host's bytes. Both claims refuse it on a DECODING, PARSING continuation (`sync`, which signs
no call): `Consent.signs` because `sync` has no call `body`, so nothing planned the call message it
signed; `Consent.signShapes` because the empty reply is of no shape (every domain has positive
length). A lazy signer escapes only by planning the call itself on its own World.
-/
import Spec.Proofs.Floor
import Spec.Sim.Sign
import Protocol.Proofs.Command
import Protocol.Proofs.Domains
import Protocol.Proofs.PostOr
import Protocol.Proofs.Incoming

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The claims -/

section Claims

variable {D : Type} [Ord D] [DecidableEq D]

/-- **C(i). Every call-domain message follow offers custody was planned on follow's own World.**
A follow step that hands custody `msg` to sign (`sign`, `signNext` or `signIncoming`), where `msg`
is a call message (`callMessage v`, any `v`), read a continuation that decodes to a state whose
argv parses to a command, and `msg` is `callMessage u` for the `u` that `plan` produced on the World
follow holds after the step (`f'.world`: the caught-up World of a write's tip, follow's World for
`rotate`) from that command's `body` and `signedReads` there: the member's own call, deriving a
Turn that World admits under the system's kernel. -/
def Consent.signs (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res msg k : ByteArray) (p : Command.Persist D)
    (r : Command.Reply) (v : Unsigned D),
    S.follow me f kb res = (f', p, r) →
    (r = .sign msg k ∨ r = .signNext msg k ∨ r = .signIncoming msg k) →
    msg = S.X.callMessage v →
    ∃ (st : Command.State) (cmd : Command.Cmd D) (sg : Command.Signed) (rs : Command.SignedReads D)
      (b : Body D) (u : Unsigned D),
      Command.State.ofBytes kb = some st ∧ Command.parse S.X.digestOf st.argv = .ok cmd ∧
      Command.body S.X me f'.world sg cmd = .ok b ∧ Command.signedReads S.X f'.world cmd = .ok rs ∧
      Command.plan S.X me f'.world sg.key rs b = .ok u ∧ msg = S.X.callMessage u ∧
      u.member = me.member ∧
      ∃ t w', deriveTurn S.X (pinned S.X.env f'.world u.pins) (rowView S.X.env f'.world u)
          ⟨u, ByteArray.empty⟩ = .ok t ∧ S.admit f'.world t = .ok w'

/-- **C(i), every arm. Every message follow offers custody is one of six shapes**: a call planned
as in `Consent.signs`, an envelope of the member's own World, member and grant, a possession
proof, an invitation, a head attestation, or a cancel. -/
def Consent.signShapes (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res msg k : ByteArray) (p : Command.Persist D)
    (r : Command.Reply),
    S.follow me f kb res = (f', p, r) →
    (r = .sign msg k ∨ r = .signNext msg k ∨ r = .signIncoming msg k) →
    (∃ (st : Command.State) (cmd : Command.Cmd D) (sg : Command.Signed) (rs : Command.SignedReads D)
      (b : Body D) (u : Unsigned D),
      Command.State.ofBytes kb = some st ∧ Command.parse S.X.digestOf st.argv = .ok cmd ∧
      Command.body S.X me f'.world sg cmd = .ok b ∧ Command.signedReads S.X f'.world cmd = .ok rs ∧
      Command.plan S.X me f'.world sg.key rs b = .ok u ∧ msg = S.X.callMessage u) ∨
    (∃ start notBefore validUntil,
      msg = Envelope.message S.X me.world me.member me.grant start notBefore validUntil) ∨
    (∃ sponsor next key, msg = possessionMessage S.X sponsor next key) ∨
    (∃ u, msg = Invite.message u) ∨ (∃ u, msg = Head.message u) ∨ (∃ c, msg = S.X.cancelMessage c)

end Claims

/-! ## What `step` offers custody, generically -/

section Step

open Command

variable {D : Type} [Ord D] [DecidableEq D]

/-- A reply hands custody `msg` to sign. -/
def Asks (r : Reply) (msg : ByteArray) : Prop :=
  ∃ k, r = .sign msg k ∨ r = .signNext msg k ∨ r = .signIncoming msg k

/-- The call shape: `msg` is the call message of a `u` that `plan` produced on `w` from the command
the continuation `kb`'s argv parses to. -/
def Planned (X : Ctx D) (me : Self D) (w : World D) (kb msg : ByteArray) : Prop :=
  ∃ (st : State) (cmd : Cmd D) (sg : Signed) (rs : SignedReads D) (b : Body D) (u : Unsigned D),
    State.ofBytes kb = some st ∧ parse X.digestOf st.argv = .ok cmd ∧
    body X me w sg cmd = .ok b ∧ signedReads X w cmd = .ok rs ∧
    plan X me w sg.key rs b = .ok u ∧ msg = X.callMessage u

/-- The six shapes (`Consent.signShapes`' conclusion). -/
def Shape (X : Ctx D) (me : Self D) (w : World D) (kb msg : ByteArray) : Prop :=
  Planned X me w kb msg ∨
    (∃ start notBefore validUntil,
      msg = Envelope.message X me.world me.member me.grant start notBefore validUntil) ∨
    (∃ sponsor next key, msg = possessionMessage X sponsor next key) ∨
    (∃ u, msg = Invite.message u) ∨ (∃ u, msg = Head.message u) ∨ (∃ c, msg = X.cancelMessage c)

omit [Ord D] [DecidableEq D] in
theorem asks_cont {r : Reply} {msg : ByteArray} (h : Asks r msg) : ∃ k, r.cont = some k := by
  obtain ⟨k, h | h | h⟩ := h <;> exact ⟨k, by rw [h]; rfl⟩

omit [Ord D] [DecidableEq D] in
theorem not_asks_of_cont {r : Reply} {msg : ByteArray} (h : r.cont = none) : ¬ Asks r msg := by
  intro ha
  obtain ⟨k, hk⟩ := asks_cont ha
  rw [h] at hk; cases hk

omit [Ord D] [DecidableEq D] in
theorem asks_sign {m k msg : ByteArray} (h : Asks (.sign m k) msg) : msg = m := by
  obtain ⟨_, h | h | h⟩ := h
  · cases h; rfl
  · cases h
  · cases h

omit [Ord D] [DecidableEq D] in
theorem asks_signNext {m k msg : ByteArray} (h : Asks (.signNext m k) msg) : msg = m := by
  obtain ⟨_, h | h | h⟩ := h
  · cases h
  · cases h; rfl
  · cases h

omit [Ord D] [DecidableEq D] in
theorem asks_signIncoming {m k msg : ByteArray} (h : Asks (.signIncoming m k) msg) : msg = m := by
  obtain ⟨_, h | h | h⟩ := h
  · cases h
  · cases h
  · cases h; rfl

omit [Ord D] [DecidableEq D] in
theorem not_asks_refused {r : Command.Refusal D} {msg : ByteArray} : ¬ Asks (refused (D := D) r) msg :=
  not_asks_of_cont (by simp [refused, Reply.cont])

theorem asks_postOr {X : Ctx D} {w : World D} {ts : List (Kernel.Step D × D)} {w' : World D}
    {r : Reply} {msg : ByteArray} (h : Asks (postOr X w ts w' r) msg) : Asks r msg := by
  rcases postOr_cases X w ts w' r with hp | ⟨s, m, -, hp⟩
  · rw [hp] at h; exact h
  · rw [hp] at h; exact absurd h not_asks_refused

omit [Ord D] [DecidableEq D] in
theorem envelopeSign_asks {t : Nat} {m k msg : ByteArray} (h : Asks (envelopeSign t m k) msg) :
    msg = m := by
  unfold envelopeSign at h
  split at h
  · exact asks_sign h
  · exact asks_signIncoming h

omit [Ord D] [DecidableEq D] in
theorem envelopeRefused_asks {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {a b c d p msg : ByteArray} (h : Asks (envelopeRefused X me argv cmd a b c d p) msg) :
    ∃ s n v, msg = Envelope.message X me.world me.member me.grant s n v := by
  unfold envelopeRefused next at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals first
    | exact absurd h not_asks_refused
    | exact absurd h (not_asks_of_cont refusedAt_cont)
    | exact absurd h (not_asks_of_cont unknownKeyEnd_cont)
    | (refine absurd h (not_asks_of_cont ?_); simp [notServed, Reply.cont]; done)
    | (obtain rfl := asks_signIncoming h; exact ⟨_, _, _, rfl⟩)
    | (obtain rfl := envelopeSign_asks h; exact ⟨_, _, _, rfl⟩)

omit [DecidableEq D] in
theorem cancelCatchUp_asks {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {said : Nat} {msg : ByteArray} (h : Asks (cancelCatchUp X me w argv said) msg) :
    ∃ s n v, msg = Envelope.message X me.world me.member me.grant s n v := by
  unfold cancelCatchUp next at h
  dsimp only at h
  split at h
  · obtain rfl := asks_sign h; exact ⟨_, _, _, rfl⟩
  · exact absurd h not_asks_refused

omit [DecidableEq D] in
theorem cancelAnswer_asks {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {result msg : ByteArray} (h : Asks (cancelAnswer X me w argv result) msg) :
    ∃ s n v, msg = Envelope.message X me.world me.member me.grant s n v := by
  unfold cancelAnswer at h
  repeat' split at h
  all_goals first
    | exact cancelCatchUp_asks h
    | exact absurd h (not_asks_of_cont refusedAt_cont)
    | exact absurd h not_asks_refused
    | (refine absurd h (not_asks_of_cont ?_); simp [declined, Reply.cont]; done)

theorem cancelTip_asks {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {cb t msg : ByteArray} (h : Asks (cancelTip X me w argv cb t) msg) :
    ∃ c, msg = X.cancelMessage c := by
  unfold cancelTip at h
  repeat' split at h
  all_goals first
    | exact absurd h not_asks_refused
    | exact absurd h (not_asks_of_cont cancelSettled_cont)
    | (unfold next at h; split at h
       · obtain rfl := asks_sign h; exact ⟨_, rfl⟩
       · exact absurd h not_asks_refused)

theorem sendCancel_not_asks {X : Ctx D} {w : World D} {argv : List ByteArray} {cb result msg : ByteArray} :
    ¬ Asks (sendCancel X w argv cb result) msg := by
  intro h
  unfold sendCancel next at h
  repeat' split at h
  all_goals first
    | exact absurd h not_asks_refused
    | exact absurd h (not_asks_of_cont refusedAt_cont)
    | (simp [Asks] at h; done)

theorem syncTip_asks {X : Ctx D} {me : Self D} {w : World D} {argv : List ByteArray}
    {sb msg : ByteArray} {mode : SyncMode} (h : Asks (syncTip X me w argv sb mode) msg) :
    ∃ u, msg = Head.message u := by
  cases mode with
  | tip => (refine absurd h (not_asks_of_cont ?_); simp [syncTip, printed, Reply.cont]; done)
  | to steps chain => (refine absurd h (not_asks_of_cont ?_); simp [syncTip, printed, Reply.cont]; done)
  | check b =>
      simp only [syncTip] at h
      repeat' split at h
      all_goals first
        | exact absurd h not_asks_refused
        | (refine absurd h (not_asks_of_cont ?_); simp [printed, Reply.cont]; done)
  | attest =>
      simp only [syncTip] at h
      unfold attestTip next at h
      repeat' split at h
      all_goals first
        | exact absurd h not_asks_refused
        | (obtain rfl := asks_sign h; exact ⟨_, rfl⟩)

/-! Each shape, at the head constant a `step` leaf names (the leaves are dispatched at reducible
transparency: unifying two DIFFERENT message heads at default transparency unfolds their domain
literals, a whnf timeout). -/

section Shapes

variable {X : Ctx D} {me : Self D} {w : World D} {kb : ByteArray}

theorem shape_envelopeMessage {a b : Nat} : Shape X me w kb (envelopeMessage X me a b) :=
  .inr (.inl ⟨_, _, _, rfl⟩)

theorem shape_adoptEnvelope {a b : Nat} : Shape X me w kb (adoptEnvelope X me a b) :=
  .inr (.inl ⟨_, _, _, rfl⟩)

theorem shape_possession {s n : D} {key : ByteArray} : Shape X me w kb (possessionMessage X s n key) :=
  .inr (.inr (.inl ⟨_, _, _, rfl⟩))

theorem shape_invite {u : ByteArray} : Shape X me w kb (Invite.message u) :=
  .inr (.inr (.inr (.inl ⟨_, rfl⟩)))

theorem shape_planned {st : State} {cmd : Cmd D} {sg : Signed} {rs : SignedReads D} {b : Body D}
    {u : Unsigned D} (hst : State.ofBytes kb = some st) (hp : parse X.digestOf st.argv = .ok cmd)
    (hb : body X me w sg cmd = .ok b) (hr : signedReads X w cmd = .ok rs)
    (hpl : plan X me w sg.key rs b = .ok u) : Shape X me w kb (X.callMessage u) :=
  .inl ⟨st, cmd, sg, rs, b, u, hst, hp, hb, hr, hpl, rfl⟩

theorem shape_planned_rotate {st : State} {sg : Signed} {b : Body D} {u : Unsigned D}
    (hst : State.ofBytes kb = some st) (hp : parse X.digestOf st.argv = .ok .rotate)
    (hb : body X me w sg .rotate = .ok b) (hpl : plan X me w sg.key {} b = .ok u) :
    Shape X me w kb (X.callMessage u) :=
  shape_planned hst hp hb rfl hpl

theorem envelopeSign_shape {t a b : Nat} {k msg : ByteArray}
    (h : Asks (envelopeSign t (envelopeMessage X me a b) k) msg) : Shape X me w kb msg := by
  obtain rfl := envelopeSign_asks h; exact shape_envelopeMessage

theorem envelopeRefused_shape {argv : List ByteArray} {cmd : Cmd D} {a b c d p msg : ByteArray}
    (h : Asks (envelopeRefused X me argv cmd a b c d p) msg) : Shape X me w kb msg :=
  .inr (.inl (envelopeRefused_asks h))

theorem cancelAnswer_shape {argv : List ByteArray} {w₀ : World D} {result msg : ByteArray}
    (h : Asks (cancelAnswer X me w₀ argv result) msg) : Shape X me w kb msg :=
  .inr (.inl (cancelAnswer_asks h))

theorem cancelTip_shape {argv : List ByteArray} {w₀ : World D} {cb t msg : ByteArray}
    (h : Asks (cancelTip X me w₀ argv cb t) msg) : Shape X me w kb msg :=
  .inr (.inr (.inr (.inr (.inr (cancelTip_asks h)))))

theorem syncTip_shape {argv : List ByteArray} {w₀ : World D} {sb msg : ByteArray} {mode : SyncMode}
    (h : Asks (syncTip X me w₀ argv sb mode) msg) : Shape X me w kb msg :=
  .inr (.inr (.inr (.inr (.inl (syncTip_asks h)))))

omit [Ord D] [DecidableEq D] in
theorem not_asks_host {op : Protocol.Op} {pl k msg : ByteArray} : ¬ Asks (.host op pl k) msg := by
  rintro ⟨_, h | h | h⟩ <;> cases h

omit [Ord D] [DecidableEq D] in
theorem not_asks_submit {c k msg : ByteArray} : ¬ Asks (.submit c k) msg := by
  rintro ⟨_, h | h | h⟩ <;> cases h

omit [Ord D] [DecidableEq D] in
theorem not_asks_precommit {k msg : ByteArray} : ¬ Asks (.precommit k) msg := by
  rintro ⟨_, h | h | h⟩ <;> cases h

omit [Ord D] [DecidableEq D] in
theorem not_asks_done {e : UInt8} {o r msg : ByteArray} : ¬ Asks (.done e o r) msg := by
  rintro ⟨_, h | h | h⟩ <;> cases h

end Shapes

/-- **What one `step` offers custody**: every message it hands custody to sign, by any of the three
signing replies, is one of the six shapes, its call shape planned on the World follow holds after
the step from the command the continuation's argv parses to. -/
theorem step_asks {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result msg : ByteArray} {r : Reply}
    (h : step X dc B me f kb result = (f', p, r)) (ha : Asks r msg) :
    Shape X me f'.world kb msg := by
  unfold step at h
  cases hst : State.ofBytes kb with
  | none =>
    simp only [hst, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact absurd ha not_asks_refused
  | some st =>
    cases hp : parse X.digestOf st.argv with
    | error e =>
      simp only [hst, hp, Option.map_some, Option.getD_some, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact absurd ha not_asks_refused
    | ok cmd =>
      simp only [hst, hp, Option.map_some, Option.getD_some] at h
      unfold next at h
      repeat' (first | split at h | (revert h; split <;> intro h))
      all_goals (simp only [Prod.mk.injEq] at h; obtain ⟨hf, -, hr⟩ := h; subst hf hr)
      all_goals (try replace ha := asks_postOr ha)
      all_goals first
        | with_reducible exact absurd ha not_asks_refused
        | with_reducible exact absurd ha not_asks_done
        | with_reducible exact absurd ha not_asks_host
        | with_reducible exact absurd ha not_asks_submit
        | with_reducible exact absurd ha not_asks_precommit
        | with_reducible exact absurd ha (not_asks_of_cont refusedAt_cont)
        | with_reducible exact absurd ha (not_asks_of_cont custodyEnd_cont)
        | with_reducible exact absurd ha (not_asks_of_cont render_cont)
        | with_reducible exact absurd ha (not_asks_of_cont describe_cont)
        | with_reducible exact absurd ha (not_asks_of_cont rangeRender_cont)
        | with_reducible exact absurd ha (not_asks_of_cont receiptLines_cont)
        | with_reducible exact absurd ha (not_asks_of_cont settleStep_cont)
        | with_reducible exact absurd ha (not_asks_of_cont attestDone_cont)
        | with_reducible exact absurd ha sendCancel_not_asks
        | (refine absurd ha (not_asks_of_cont ?_); simp [printed, behind, notServed, Reply.cont]; done)
        | with_reducible exact envelopeRefused_shape ha
        | with_reducible exact cancelAnswer_shape ha
        | with_reducible exact cancelTip_shape ha
        | with_reducible exact syncTip_shape ha
        | with_reducible exact envelopeSign_shape ha
        | (obtain rfl := asks_sign ha; with_reducible exact shape_envelopeMessage)
        | (obtain rfl := asks_sign ha; with_reducible exact shape_adoptEnvelope)
        | (obtain rfl := asks_sign ha; with_reducible exact shape_possession)
        | (obtain rfl := asks_sign ha; with_reducible exact shape_invite)
        | (obtain rfl := asks_sign ha; with_reducible exact shape_planned hst ‹_› ‹_› ‹_› ‹_›)
        | (obtain rfl := asks_signNext ha; with_reducible exact shape_planned_rotate hst ‹_› ‹_› ‹_›)

/-- A call-domain message of the six shapes is the planned one: every other domain differs from
`domCall` at a byte both hold (`Protocol.Proofs.Domains`), and `plan` offers only the member's own
call whose derived Turn the World admits (`plan_admits`). -/
theorem shape_call {X : Ctx D} {me : Self D} {w : World D} {kb msg : ByteArray} {v : Unsigned D}
    (hs : Shape X me w kb msg) (hv : msg = X.callMessage v) :
    ∃ (st : State) (cmd : Cmd D) (sg : Signed) (rs : SignedReads D) (b : Body D) (u : Unsigned D),
      State.ofBytes kb = some st ∧ parse X.digestOf st.argv = .ok cmd ∧
      body X me w sg cmd = .ok b ∧ signedReads X w cmd = .ok rs ∧
      plan X me w sg.key rs b = .ok u ∧ msg = X.callMessage u ∧ u.member = me.member ∧
      ∃ t w', deriveTurn X (pinned X.env w u.pins) (rowView X.env w u) ⟨u, ByteArray.empty⟩ = .ok t ∧
        World.admit X.env w t = .ok w' := by
  subst hv
  rcases hs with ⟨st, cmd, sg, rs, b, u, hst, hp, hb, hr, hpl, hm⟩ | ⟨s, n, vu, he⟩ | ⟨sp, nx, key, he⟩ |
      ⟨u, he⟩ | ⟨u, he⟩ | ⟨c, he⟩
  · obtain ⟨hmem, -, -, t, w', hd, ha⟩ := plan_admits hpl
    exact ⟨st, cmd, sg, rs, b, u, hst, hp, hb, hr, hpl, hm, hmem, t, w', hd, ha⟩
  · exact absurd he.symm (envelope_call_disjoint X v me.world me.member me.grant s n vu)
  · exact absurd he (call_not_possession X v sp nx key)
  · exact absurd he.symm (invite_not_call X v u)
  · exact absurd he.symm (head_not_call X v u)
  · exact absurd he.symm (cancel_not_call X c v)

end Step

/-! ## The deployed system -/

/-- **C(i) of the deployed system**: `step_asks`, `shape_call` (`plan_admits`, the domain
separations). -/
theorem top_consent_signs (d : ByteArray → ByteArray) : Consent.signs (deployed d) := by
  intro me f f' kb res msg k p r v h hr hv
  change Command.step Host.Deployed.X Codec.Deployed.digestCodec _ me f kb res = (f', p, r) at h
  exact shape_call (step_asks h ⟨k, hr⟩) hv

/-- **C(i), every arm, of the deployed system**: `step_asks`. -/
theorem top_consent_signShapes (d : ByteArray → ByteArray) : Consent.signShapes (deployed d) := by
  intro me f f' kb res msg k p r h hr
  change Command.step Host.Deployed.X Codec.Deployed.digestCodec _ me f kb res = (f', p, r) at h
  exact step_asks h ⟨k, hr⟩

/-! ## The floor: the follower that has custody sign the Host's bytes -/

/-- `kSync` decodes to a state whose argv is `sync`. -/
theorem sync_decodes : (Command.State.ofBytes kSync).map (·.argv) = some ["sync".toUTF8] := by
  decide +kernel

/-- `sync` parses to `sync` at its tip. -/
theorem sync_parses : Command.parse Xd.digestOf ["sync".toUTF8] = .ok (.sync .tip) := by rfl

/-- The relay signer signs on `kSync`. -/
theorem relaySigner_signs (d : ByteArray → ByteArray) (me : Command.Self Digest) (f : Command.Follow Digest)
    (res : ByteArray) : (relaySigner d).follow me f kSync res = (f, .steps [], .sign res .empty) := by
  have hk := sync_decodes
  cases hs : Command.State.ofBytes kSync with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    have ha : st.argv = ["sync".toUTF8] := by simpa using hk
    have hp : Command.parse Host.Deployed.X.digestOf st.argv = .ok (.sync .tip) := by
      rw [ha]; exact sync_parses
    unfold relaySigner
    dsimp only
    rw [hs]
    dsimp only
    rw [hp]

/-- **FLOOR (C(i)).** The claim refuses the relay signer, on a continuation that decodes and parses:
handed a call message as the Host's reply on `kSync`, it offers it to custody, and `sync` has no
call body, so nothing planned it. -/
theorem floor_consent_signs (d : ByteArray → ByteArray) : ¬ Consent.signs (relaySigner d) := by
  intro h
  have hk := sync_decodes
  cases hs : Command.State.ofBytes kSync with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    have ha : st.argv = ["sync".toUTF8] := by simpa using hk
    have hp : Command.parse (relaySigner d).X.digestOf st.argv = .ok (.sync .tip) := by
      rw [ha]; exact sync_parses
    obtain ⟨st', cmd, sg, rs, b, u, hst', hp', hb, -⟩ :=
      h wMe ⟨wGenesis, none, none⟩ ⟨wGenesis, none, none⟩ kSync
        ((relaySigner d).X.callMessage wCall.unsigned) ((relaySigner d).X.callMessage wCall.unsigned)
        .empty (.steps []) (.sign ((relaySigner d).X.callMessage wCall.unsigned) .empty) wCall.unsigned
        (relaySigner_signs d _ _ _) (.inl rfl) rfl
    rw [hs] at hst'
    cases hst'
    rw [hp] at hp'
    cases hp'
    cases hb

theorem empty_ne_append {a b : ByteArray} (h : 0 < a.size) : ByteArray.empty ≠ a ++ b := by
  intro e
  have := congrArg ByteArray.size e
  simp only [ByteArray.size_append] at this
  have h0 : ByteArray.empty.size = 0 := rfl
  omega

/-- **FLOOR (C(i), every arm).** The claim refuses the relay signer, on a continuation that decodes
and parses: the empty reply it offers is of no shape (each begins with a domain of positive length). -/
theorem floor_consent_signShapes (d : ByteArray → ByteArray) : ¬ Consent.signShapes (relaySigner d) := by
  intro h
  rcases h wMe ⟨wGenesis, none, none⟩ ⟨wGenesis, none, none⟩ kSync .empty .empty .empty (.steps [])
      (.sign .empty .empty) (relaySigner_signs d _ _ _) (.inl rfl) with
    ⟨-, -, -, -, -, u, -, -, -, -, -, he⟩ | ⟨s, n, v, he⟩ | ⟨sp, nx, key, he⟩ | ⟨u, he⟩ | ⟨u, he⟩ | ⟨c, he⟩
  · exact empty_ne_append (by decide) he
  · unfold Envelope.message at he
    simp only [ByteArray.append_assoc] at he
    exact empty_ne_append (by decide) he
  · unfold possessionMessage at he
    simp only [ByteArray.append_assoc] at he
    exact empty_ne_append (by decide) he
  · exact empty_ne_append (by decide) he
  · exact empty_ne_append (by decide) he
  · exact empty_ne_append (by decide) he

/-! ## Inhabited: the deployed follower offers custody a call message -/

/-- **The signing run**: follow, holding the genesis World, steps the founder's `rotate` at its
precommit phase and asks custody `signNext` over the call message of the rotation `plan` produces
there. -/
theorem run_signs :
    (match Command.plan Xd sMe wGenesis wNext {} (.rotate wNext (nextKeyDigest Xd iPending)) with
     | .ok u => callAsked ((deployed storeDigest).follow sMe ⟨wGenesis, none, none⟩ iKb iRes).2.2 u
     | .error _ => false) = true := by
  native_decide

theorem callAsked_eq {r : Command.Reply} {u : Unsigned Digest} (h : callAsked r u = true) :
    ∃ k, r = .signNext (Xd.callMessage u) k := by
  cases r <;> simp_all [callAsked]

/-- **INHABITED (C(i)).** The deployed follower offers custody a call-domain message: the claim's
premise is reached, and `top_consent_signs` says what that message is. -/
theorem inhabited_signs :
    ∃ (me : Command.Self Digest) (f f' : Command.Follow Digest) (kb res msg k : ByteArray)
      (p : Command.Persist Digest) (v : Unsigned Digest),
      (deployed storeDigest).follow me f kb res = (f', p, .signNext msg k) ∧
        msg = (deployed storeDigest).X.callMessage v := by
  have hr := run_signs
  cases hpl : Command.plan Xd sMe wGenesis wNext {} (.rotate wNext (nextKeyDigest Xd iPending)) with
  | error e => rw [hpl] at hr; cases hr
  | ok u =>
    rw [hpl] at hr
    dsimp only at hr
    revert hr
    generalize iKb = kb
    generalize iRes = res
    intro hr
    cases hR : (deployed storeDigest).follow sMe ⟨wGenesis, none, none⟩ kb res with
    | mk f' rest =>
      obtain ⟨p, rp⟩ := rest
      rw [hR] at hr
      obtain ⟨k, hk⟩ := callAsked_eq hr
      subst hk
      exact ⟨sMe, ⟨wGenesis, none, none⟩, f', kb, res, _, k, p, u, hR, rfl⟩

end Nanodregg.Spec
