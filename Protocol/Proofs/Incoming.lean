/-
# Protocol.Proofs.Incoming — once a command signs by the incoming key, it stays signed by it

PROTOCOL-46 (CLIENT-13 amended): a command of a verb that signs no call asks custody ONCE to sign
its envelope with the armed rotation's incoming key, and every later envelope of that command too
(`envelopeRefused` sets `incomingBit` in the continuation's `tried`; `envelopeSign` reads it). Only
the local fact was proved (`envelopeRefused_once`). Here, across the whole step machine:

* `State.ofBytes_bytes`: a continuation reads back as the state written (`stateFrame` is lawful and
  `Text.unlist ∘ Text.fitList` is the identity);
* `step_incoming_kept`: if the state a step resumes is an envelope phase (1 or 2) whose `tried` has
  `incomingBit`, every envelope-phase state the step hands on has a `tried` with it too, and every
  phase-1 continuation (the next envelope to sign) rides on a `signIncoming` reply, never `.sign`. Its
  conclusion is its premise for the next step, so it holds along a command's whole run. With
  `envelopeRefused_once`, a second `unknownKey` is never answered by a third envelope.

Remark (prose, not a theorem): only a `readOnly` command ever gets the bit (`envelopeRefused`'s
`readOnly cmd` guard), and it leaves phases 1 and 2 only by ending (`render`, `describe`, `sync`,
`receiptLines`: no continuation). A write's continuations past phase 2 carry no `tried`.
-/
import Protocol.Command.Machine
import Protocol.Proofs.Frames
import Protocol.Proofs.Wire
import Protocol.Proofs.Page

namespace Nanodregg.Protocol.Command

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

theorem stateFrame_lawful : Stream.Lawful stateFrame := Layout.codec_lawful _ _ _

theorem mapM_fit_val {max : Nat} :
    ∀ {l : List ByteArray} {r : List (Bytes max)}, l.mapM (Text.fit max) = some r → r.map (·.1) = l
  | [], r, h => by simp at h; subst h; rfl
  | b :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hb : Text.fit max b with
    | none => simp [hb] at h
    | some x =>
      cases hl : l.mapM (Text.fit max) with
      | none => simp [hb, hl] at h
      | some r' =>
        simp only [hb, hl, pure, Option.some.injEq] at h
        subst h
        simp [fit_val hb, mapM_fit_val hl]

theorem unlist_fitList {max : Nat} {l : List ByteArray} {v : Bounded max (Bytes max)}
    (h : Text.fitList max l = some v) : Text.unlist v = l := by
  unfold Text.fitList at h
  cases hl : l.mapM (Text.fit max) with
  | none => simp [List.mapM_toArray, hl] at h
  | some r =>
    simp only [List.mapM_toArray, hl] at h
    simp at h
    obtain ⟨_, rfl⟩ := h
    simp [Text.unlist, mapM_fit_val hl]

/-- **A continuation reads back as the state written.** -/
theorem State.ofBytes_bytes {s : State} {b : ByteArray} (h : s.bytes = some b) :
    State.ofBytes b = some s := by
  unfold State.bytes at h
  cases ha : Text.fitList Bounds.frameBytesMax s.argv with
  | none => simp [ha, bind, Option.bind] at h
  | some a =>
    cases hc : Text.fitList Bounds.frameBytesMax s.acc with
    | none => simp [ha, hc, bind, Option.bind] at h
    | some c =>
      simp only [ha, hc, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      simp only [State.ofBytes, Stream.decode_bytes stateFrame_lawful, unlist_fitList ha, unlist_fitList hc]

omit [Ord D] [DecidableEq D] in
theorem next_cont {s : State} {g : ByteArray → Reply} {k : ByteArray}
    (hg : ∀ k', (g k').cont = some k') (h : (next (D := D) s g).cont = some k) :
    State.ofBytes k = some s := by
  unfold next at h
  split at h
  · rename_i b hb
    rw [hg] at h
    cases h
    exact State.ofBytes_bytes hb
  · simp [refused, Reply.cont] at h

omit [Ord D] [DecidableEq D] in
/-- A step that hands on a continuation through `next` is the reply `g` built on it, and the
continuation reads back as the state `next` wrote. -/
theorem next_spec {s : State} {g : ByteArray → Reply} {k : ByteArray}
    (hg : ∀ k', (g k').cont = some k') (h : (next (D := D) s g).cont = some k) :
    next (D := D) s g = g k ∧ State.ofBytes k = some s := by
  unfold next at h ⊢
  cases hb : s.bytes with
  | none => simp [hb, refused, Reply.cont] at h
  | some b =>
    simp only [hb] at h ⊢
    rw [hg] at h
    cases h
    exact ⟨rfl, State.ofBytes_bytes hb⟩

theorem incoming_or {t b : Nat} (ht : t < 2 ^ 64) (hb : b < 2 ^ 64) :
    Text.ofU64 (Text.u64 (t ||| b)) = some (t ||| b) :=
  ofU64_u64 (Nat.or_lt_two_pow ht hb)

theorem incomingBit_or_left {t b : Nat} (h : t &&& incomingBit ≠ 0) : (t ||| b) &&& incomingBit ≠ 0 := by
  intro h'
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun n => n.testBit i) h'
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at this ⊢
  cases hi : t.testBit i <;> simp_all

theorem incomingBit_or_self (t : Nat) : (t ||| incomingBit) &&& incomingBit ≠ 0 := by
  intro h'
  have := congrArg (fun n => n.testBit 1) h'
  have h2 : Nat.testBit incomingBit 1 = true := by decide
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, h2] at this
  simp at this

theorem ofU64_lt {b : ByteArray} {n : Nat} (h : Text.ofU64 b = some n) : n < 2 ^ 64 := by
  unfold Text.ofU64 at h
  split at h
  · rename_i v _
    cases h
    exact v.toNat_lt
  · cases h

omit [Ord D] [DecidableEq D] in
theorem refusedAt_cont {X : Ctx D} {r : Refusal D} : (refusedAt X r).cont = none := by
  unfold refusedAt; split <;> simp [refused, Reply.cont]

theorem describe_cont {X : Ctx D} {w : World D} {obj : D} : (describe X w obj).cont = none := by
  unfold describe
  split
  · simp [refused, Reply.cont]
  · split <;> simp [refused, printed, Reply.cont]

theorem rangeRender_cont {X : Ctx D} {w : World D} {obj : D} {rel : String} {most : Nat}
    {pre : Option String} : (rangeRender X w obj rel most pre).cont = none := by
  unfold rangeRender
  split
  · simp [refused, Reply.cont]
  · split <;> simp [refused, printed, Reply.cont]

theorem render_cont {X : Ctx D} {w : World D} {obj : D} {ex : List (Nat × ByteArray)} :
    (render X w obj ex).cont = none := by
  unfold render
  repeat' split
  all_goals simp [refused, printed, Reply.cont]

theorem receiptLines_cont {X : Ctx D} {dc : Codec.Stream D} {w : World D} {cb : ByteArray} :
    (receiptLines X dc w cb).cont = none := by
  unfold receiptLines
  repeat' split
  all_goals simp [refused, printed, Reply.cont]

theorem envelopeSign_cont {t : Nat} {m k : ByteArray} : (envelopeSign t m k).cont = some k := by
  unfold envelopeSign; split <;> rfl

omit [Ord D] [DecidableEq D] in
theorem settled_cont {X : Ctx D} {out result : ByteArray} : (settled X out result).cont = none := by
  unfold settled
  repeat' split
  all_goals first | exact refusedAt_cont | simp [refused, declined, Reply.cont]

omit [Ord D] [DecidableEq D] in
/-- **The writer's refusal of an envelope, once the incoming key is in use, is answered by the
incoming key**: if the refused envelope's `tried` has `incomingBit`, a continuation `envelopeRefused`
hands on is phase 1, its `tried` has `incomingBit`, and the reply carrying it is `signIncoming`. With
the bit set the `unknownKey` arm only refuses (no continuation), so the content is the `expired`
re-sign: `envelopeSign` of a `tried` that has the bit, which adds only `expiredBit`. -/
theorem envelopeRefused_incoming {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Cmd D}
    {startB pagesB upToB triedB p k : ByteArray} {st' : State} {t : Nat} (htr : Text.ofU64 triedB = some t)
    (hb : t &&& incomingBit ≠ 0)
    (h : (envelopeRefused X me argv cmd startB pagesB upToB triedB p).cont = some k)
    (hs : State.ofBytes k = some st') :
    st'.phase = 1 ∧ (∃ t', st'.tried = some t' ∧ t' &&& incomingBit ≠ 0) ∧
      ∃ m, envelopeRefused X me argv cmd startB pagesB upToB triedB p = .signIncoming m k := by
  unfold envelopeRefused at h ⊢
  rw [htr] at h ⊢
  cases hte : expiredHeight? p <;> cases hs0 : Text.ofU64 startB <;> cases hu : Text.ofU64 upToB <;>
    simp only [hte, hs0, hu] at h ⊢
  all_goals (try (simp [refused, Reply.cont] at h; done))
  · split at h
    · rename_i hp
      simp only [hp, if_true] at ⊢
      split at h
      · rename_i hr
        simp only [hr, if_true] at ⊢
        obtain ⟨hn, hs1⟩ := next_spec (fun _ => rfl) h
        rw [hs1] at hs
        cases hs
        exact ⟨rfl, ⟨t ||| incomingBit, by simp only [State.tried]; exact incoming_or (ofU64_lt htr) (by decide),
          incomingBit_or_self t⟩, _, hn⟩
      · split at h
        · simp [refused, Reply.cont] at h
        · rw [refusedAt_cont] at h; cases h
    · split at h <;> simp [refused, notServed, Reply.cont] at h
  · split at h
    · simp [refused, Reply.cont] at h
    · -- `split at h` split the goal's `match reSign …` with it
      obtain ⟨hn, hs1⟩ := next_spec (fun _ => envelopeSign_cont) h
      rw [hs1] at hs
      cases hs
      refine ⟨rfl, ⟨t ||| expiredBit, by simp only [State.tried]; exact incoming_or (ofU64_lt htr) (by decide),
        incomingBit_or_left hb⟩, ?_⟩
      rw [hn]
      simp [envelopeSign, hb]

omit [Ord D] [DecidableEq D] in
theorem State.tried_shape {st : State} {t : Nat} (h : st.tried = some t) :
    (st.phase = 1 ∧ ∃ a b c d, st.acc = [a, b, c, d] ∧ Text.ofU64 d = some t) ∨
      (st.phase = 2 ∧ ∃ a b c d e, st.acc = [a, b, c, d, e] ∧ Text.ofU64 e = some t) := by
  unfold State.tried at h
  split at h
  · rename_i hp ha; exact .inl ⟨hp, _, _, _, _, ha, h⟩
  · rename_i hp ha; exact .inr ⟨hp, _, _, _, _, _, ha, h⟩
  · cases h

/-- **Once a command signs by the incoming key, every envelope after is signed by it**: if the state a
step resumes is an envelope phase (1 or 2) whose `tried` has `incomingBit`, then every envelope-phase
state the step hands on (a reply's continuation) has a `tried`, and it has `incomingBit`; and a
phase-1 continuation (an envelope to be signed) is carried by `signIncoming`, never `sign`. Both are
conclusions, so steps chain: the next step's premise is this step's conclusion. -/
theorem step_incoming_kept {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result k : ByteArray} {r : Reply} {st st' : State} {t : Nat}
    (hst : State.ofBytes kb = some st) (ht : st.tried = some t) (hb : t &&& incomingBit ≠ 0)
    (h : step X dc B me f kb result = (f', p, r)) (hk : r.cont = some k)
    (hs' : State.ofBytes k = some st') :
    (st'.phase = 1 ∨ st'.phase = 2 → ∃ t', st'.tried = some t' ∧ t' &&& incomingBit ≠ 0) ∧
      (st'.phase = 1 → ∃ m, r = .signIncoming m k) := by
  obtain ⟨argv, phase, acc⟩ := st
  rcases State.tried_shape ht with ⟨hp, a, b, c, d, ha, hd⟩ | ⟨hp, a, b, c, d, e, ha, he⟩
  all_goals (dsimp only at hp ha; subst hp ha)
  all_goals (unfold step at h; simp only [hst, Option.map_some, Option.getD_some] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (obtain ⟨-, -, rfl⟩ := h)
  all_goals (try (simp [refused, printed, behind, notServed, Reply.cont] at hk; done))
  all_goals (try (rw [refusedAt_cont] at hk; cases hk; done))
  all_goals (try (rw [render_cont] at hk; cases hk; done))
  all_goals (try (rw [describe_cont] at hk; cases hk; done))
  all_goals (try (rw [rangeRender_cont] at hk; cases hk; done))
  all_goals (try (rw [receiptLines_cont] at hk; cases hk; done))
  all_goals (try (rw [settled_cont] at hk; cases hk; done))
  all_goals (try (obtain rfl : _ = _ := Option.some.inj ‹some _ = some _›))
  all_goals (try (obtain ⟨hn, hs0⟩ := next_spec (fun _ => rfl) hk; rw [hs0] at hs'; cases hs'; rw [hn]; simp_all [State.tried]; done))
  all_goals (try (obtain ⟨hn, hs0⟩ := next_spec (fun _ => envelopeSign_cont) hk; rw [hs0] at hs'; cases hs'; rw [hn]; simp_all [State.tried, envelopeSign]; done))
  -- what is left: the writer refused the envelope (`envelopeRefused`), from phase 2
  all_goals (rename_i hph hacc _)
  · simp at hph
  · simp only [List.cons.injEq, and_true] at hacc
    obtain ⟨-, -, -, -, rfl⟩ := hacc
    obtain ⟨-, h1, m, h2⟩ := envelopeRefused_incoming he hb hk hs'
    exact ⟨fun _ => h1, fun _ => ⟨m, h2⟩⟩
