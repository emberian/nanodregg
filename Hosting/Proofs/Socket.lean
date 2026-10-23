/-
# Hosting.Proofs.Socket — the member socket: an `ok` answer is committed on the member's own World (E2b)

The resident (`Hosting.Resident.Run`) reaches its member's follower through ONE socket: its argv goes to
`nd --stdio`, which drives follow's command machine (`Protocol.Command.start`/`step`) and hands back the
command's `done`. Every theorem over `ResidentRun.Runs` already covers every reply that socket could give.
This module states what an `ok` one MEANS on the member's side, under ONE premise about bytes:

- `Moves`/`Reach`: follow's World moves only by the frames follow answers (`Command.step` on any
  continuation, any result, any connection's: the deployed `Host.Follow.loop`), HOSTING-43.
- `FollowRun`: one command of follow's machine as the leg drives it: `start` on the argv, `step` on each
  continuation follow handed out with SOME result (the attempt store's, custody's, the Host's: chosen,
  never trusted), follow's World `Reach`ed between frames (other commands' frames), ending in a `done`
  handed out at a follow state the run names.
- `LegFrom` / `StdioLeg` (the `gates/tcb.tsv` row `stdio-leg`): read along the resident's effects in the
  order it performed them, each `ok`-exit reply is the `done` of a follower run of exactly that command's
  argv, from a World follow reached from where the last such run ended: ONE follower serves the resident.
  Every other reply and every failure claims nothing. Rust is trusted to MOVE three byte fields (the
  argv in, each continuation back, the `done` out) to that one follower and for nothing else: after T0
  (PROTOCOL-64) follow's only `ok` for a submitted call is its own World's settlement, so nd's attempt
  loop, custody and the Host's status choose the RESULT a step is handed, which `FollowRun` quantifies
  over, never the exit. Satisfiable: `stdioLeg_errors`.
- The machine facts the join reads (follow's, no premise): `step_cont` (every continuation a step hands
  on carries the step's argv; a phase-4 one is step 3's submit of a call `plan` produced on that step's
  World), `start_cont`/`start_ne_ok`, `step_invoke_ok` (an invoke ends `ok` only at the settlement),
  `invokeArgv_parse` (the resident's invoke argv parses to `invoke` of the config's bell, at
  `sh.answer`, with the printed text, through the config's grant; `ofHex_hex`), `run_invoke_ok`.
- R1-R3 on the resident's side, no premise: `resident_argv_on_stdio` (every argv starts `read` or
  `invoke`, both on the stdio surface: nd's screen never fires on it), `deliverAfter_unsettled` (an exit
  neither `ok` nor `refused` is followed by what a failure is followed by).
- `delivered_answer_committed`: an `ok` invoke of `answer` for `(r, t)` was the kept answer (or this
  tick's), and follow's World at its `ok` journals a call that invokes the bell at `sh.answer` with the
  bytes read from the text `answerArg r t` at the bell's own method. `answer_args_at_answerArgTy`: at a
  method of type `answerArgTy` those bytes are `answerDatum r t`'s. The strong form, that the method's
  type IS `answerArgTy` on the World the call was planned on, is `SocketStrong`'s
  `delivered_answer_committed_strong` (HOSTING-43).

NOT claimed here. The bell's ROW: what the compiled Bell's `answer` writes is
`Lang.Proofs.Bell.answer_run`, joined to the strong form in `BellRow.answered_row_is_kept_answer`
(HOSTING-44) at the run grain; that the committing World then HOLDS that row is not stated anywhere, so
LITP's "the join stays a journey row" stands for it. A commit whose reply is LOST (follow appends, then dies before
`port.send`; the resident sees `.error` or exit `client`) is PROT-5's at-most-once and out of this card:
nothing here claims the converse of ok ⇒ journaled. Nor: that an ok reply's stdout is the receipt, who
else holds the resident's key, liveness, or that nd's attempt loop implements `Attempt.next`.
-/
import Hosting.Proofs.ResidentRun
import Hosting.Proofs.Lifetime
import Protocol.Proofs.Command
import Protocol.Proofs.Incoming
import Protocol.Proofs.Settle
import Std.Data.String.ToNat

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

omit [Ord D] [DecidableEq D] in
theorem envelopeRefused_cont {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Command.Cmd D}
    {startB pagesB upToB triedB p k : ByteArray}
    (h : (envelopeRefused X me argv cmd startB pagesB upToB triedB p).cont = some k) :
    ∃ acc, State.ofBytes k = some ⟨argv, 1, acc⟩ := by
  unfold envelopeRefused at h
  repeat' split at h
  all_goals first
    | (simp [refused, notServed, Reply.cont] at h; done)
    | (rw [refusedAt_cont] at h; cases h)
    | (rw [unknownKeyEnd_cont] at h; cases h)
    | exact ⟨_, next_cont (fun _ => rfl) h⟩
    | exact ⟨_, next_cont (fun _ => envelopeSign_cont) h⟩

theorem step_cont {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result k : ByteArray} {r : Command.Reply} {st st' : State}
    (hst : State.ofBytes kb = some st) (h : Command.step X dc B me f kb result = (f', p, r))
    (hk : r.cont = some k) (hs' : State.ofBytes k = some st') :
    st'.argv = st.argv ∧ (st'.phase = 4 → ∃ cmd s rs b u sig, Command.parse X.digestOf st.argv = .ok cmd ∧
      Command.body X me f.world s cmd = .ok b ∧ Command.signedReads X f.world cmd = .ok rs ∧
      Command.plan X me f.world s.key rs b = .ok u ∧ st'.acc.getLast? = some (X.callBytes ⟨u, sig⟩)) := by
  obtain ⟨argv, phase, acc⟩ := st
  unfold Command.step at h
  simp only [hst, Option.map_some, Option.getD_some] at h
  split at h
  · rename_i hs; cases hs
  · simp only [Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; simp [refused, Reply.cont] at hk
  rename_i st cmd hs hp
  simp only [Option.some.injEq] at hs
  subst hs
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (obtain ⟨-, -, rfl⟩ := h)
  all_goals (try (simp [refused, printed, behind, notServed, Reply.cont] at hk; done))
  all_goals (try (rw [refusedAt_cont] at hk; cases hk; done))
  all_goals (try (rw [custodyEnd_cont] at hk; cases hk; done))
  all_goals (try (rw [render_cont] at hk; cases hk; done))
  all_goals (try (rw [describe_cont] at hk; cases hk; done))
  all_goals (try (rw [rangeRender_cont] at hk; cases hk; done))
  all_goals (try (rw [receiptLines_cont] at hk; cases hk; done))
  all_goals (try (rw [settled_cont] at hk; cases hk; done))
  all_goals (try (rw [cancelAnswer_cont] at hk; cases hk; done))
  all_goals (try (rw [sendCancel_cont hk] at hs'; cases hs'; simp; done))
  all_goals (try (obtain ⟨acc', ha⟩ := envelopeRefused_cont hk; rw [ha] at hs'; cases hs'; simp; done))
  all_goals (try (obtain ⟨hn, hs0⟩ := next_spec (fun _ => rfl) hk; rw [hs0] at hs'; cases hs'; simp; done))
  all_goals (try (obtain ⟨hn, hs0⟩ := next_spec (fun _ => envelopeSign_cont) hk; rw [hs0] at hs'; cases hs'; simp; done))
  -- what is left: step 3's submit, the one phase-4 continuation
  obtain ⟨-, hs0⟩ := next_spec (fun _ => rfl) hk
  rw [hs0] at hs'
  cases hs'
  exact ⟨rfl, fun _ => ⟨_, _, _, _, _, _, hp, ‹body _ _ _ _ _ = _›, ‹signedReads _ _ _ = _›,
    ‹Command.plan _ _ _ _ _ _ = _›, rfl⟩⟩

/-- `start` hands on only an envelope (phase 1) or an adopt (phase 6) state, over the argv it was given. -/
theorem start_cont {X : Ctx D} {me : Self D} {f : Follow D} {argv : List ByteArray} {k : ByteArray}
    {st' : State} (hk : (Command.start X me f argv).cont = some k) (hs' : State.ofBytes k = some st') :
    st'.argv = argv ∧ st'.phase ≠ 4 := by
  unfold Command.start at hk
  dsimp only at hk
  repeat' split at hk
  all_goals first
    | (simp [refused, Reply.cont] at hk; done)
    | (obtain ⟨-, hs0⟩ := next_spec (fun _ => rfl) hk; rw [hs0] at hs'; cases hs'
       exact ⟨rfl, by simp⟩)

/-- `start` never answers `ok`: its only ends are refusals. -/
theorem start_ne_ok {X : Ctx D} {me : Self D} {f : Follow D} {argv : List ByteArray} {o e : ByteArray} :
    Command.start X me f argv ≠ .done CommandExit.ok.code.toUInt8 o e := by
  intro h
  unfold Command.start next at h
  dsimp only at h
  repeat' split at h
  all_goals simp [refused, CommandExit.code] at h

/-! ## No `ok` from a refusal or a continuation -/

omit [Ord D] [DecidableEq D] in
theorem refusedAt_ne_ok {X : Ctx D} {r : Command.Refusal D} {o e : ByteArray} :
    refusedAt X r ≠ .done CommandExit.ok.code.toUInt8 o e := by
  unfold refusedAt; split <;> simp [refused, CommandExit.code]

omit [Ord D] [DecidableEq D] in
theorem custodyEnd_ne_ok {X : Ctx D} {cmd : Command.Cmd D} {st : State} {r : Command.Refusal D}
    {o e : ByteArray} : custodyEnd X cmd st r ≠ .done CommandExit.ok.code.toUInt8 o e := by
  unfold custodyEnd unknownKeyEnd
  repeat' split
  all_goals first | exact refusedAt_ne_ok | simp [refused, CommandExit.code]

omit [Ord D] [DecidableEq D] in
theorem next_ne_ok {s : State} {g : ByteArray → Command.Reply} {o e : ByteArray}
    (hg : ∀ k, (g k).cont = some k) : next (D := D) s g ≠ .done CommandExit.ok.code.toUInt8 o e := by
  unfold next; split
  · intro h; have := hg ‹_›; rw [h] at this; cases this
  · simp [refused, CommandExit.code]

omit [Ord D] [DecidableEq D] in
theorem envelopeRefused_ne_ok {X : Ctx D} {me : Self D} {argv : List ByteArray} {cmd : Command.Cmd D}
    {startB pagesB upToB triedB p o e : ByteArray} :
    envelopeRefused X me argv cmd startB pagesB upToB triedB p ≠ .done CommandExit.ok.code.toUInt8 o e := by
  unfold envelopeRefused unknownKeyEnd
  repeat' split
  all_goals first
    | exact refusedAt_ne_ok
    | exact next_ne_ok (fun _ => rfl)
    | exact next_ne_ok (fun _ => envelopeSign_cont)
    | simp [refused, notServed, CommandExit.code]

/-- **An invoke ends `ok` only at the settlement**: a step of an `invoke` command (every parse of its
argv is an invoke) that answers `done ok` resumes a phase-4 state. Every other arm an invoke can
reach hands on a continuation or ends by a refusal, `behind`, or `pageIo`; `printed` is read,
describe, range, sync, receipt, init, adopt, invite and cancel only. -/
theorem step_invoke_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {kb result o e : ByteArray} {st : State}
    (hst : State.ofBytes kb = some st)
    (hinv : ∀ cmd, Command.parse X.digestOf st.argv = .ok cmd → ∃ obj m a rg via, cmd = .invoke obj m a rg via)
    (h : Command.step X dc B me f kb result = (f', p, .done CommandExit.ok.code.toUInt8 o e)) :
    st.phase = 4 := by
  obtain ⟨argv, phase, acc⟩ := st
  unfold Command.step at h
  simp only [hst, Option.map_some, Option.getD_some] at h
  split at h
  · rename_i hs; cases hs
  · simp [refused, CommandExit.code] at h
  rename_i st cmd hs hp
  simp only [Option.some.injEq] at hs
  subst hs
  obtain ⟨obj, m, a, rg, via, rfl⟩ := hinv _ hp
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (try (obtain ⟨-, -, h⟩ := h))
  all_goals (try contradiction)
  all_goals (try (simp [refused, behind, CommandExit.code] at h; done))
  all_goals (try (exact absurd h refusedAt_ne_ok))
  all_goals (try (exact absurd h custodyEnd_ne_ok))
  all_goals (try (exact absurd h envelopeRefused_ne_ok))
  all_goals (try (exact absurd h (next_ne_ok (fun _ => rfl))))
  all_goals (try (exact absurd h (next_ne_ok (fun _ => envelopeSign_cont))))
  all_goals assumption

/-! ## The resident's invoke argv, as follow parses it -/

theorem fromUTF8_toUTF8' (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?]; exact ⟨s.isValidUTF8, rfl⟩

private theorem hexVal_digit : ∀ n, n < 16 → Text.hexVal (Lang.Print.hexDigit n) = some n.toUInt8 := by
  decide

private theorem byte_split (x : UInt8) : (x.toNat / 16).toUInt8 * 16 + (x.toNat % 16).toUInt8 = x := by
  apply UInt8.toNat_inj.mp
  have := x.toNat_lt
  have h16 : (16 : UInt8).toNat = 16 := rfl
  simp only [UInt8.toNat_add, UInt8.toNat_mul, Nat.toUInt8, UInt8.toNat_ofNat', h16]
  omega

private theorem unhex_hexChars : ∀ (l : List UInt8) (acc : ByteArray),
    Text.unhex acc (l.foldr (fun x cs => Lang.Print.hexDigit (x.toNat / 16) ::
      Lang.Print.hexDigit (x.toNat % 16) :: cs) []) = some (acc ++ ⟨l.toArray⟩)
  | [], acc => by simp [Text.unhex]; ext1; simp
  | x :: l, acc => by
    simp only [List.foldr_cons, Text.unhex]
    rw [hexVal_digit _ (Nat.div_lt_of_lt_mul (by have := x.toNat_lt; omega)),
      hexVal_digit _ (Nat.mod_lt _ (by decide))]
    simp only [bind, Option.bind, byte_split]
    rw [unhex_hexChars l]
    congr 1; ext1; simp [ByteArray.push]

/-- Lang's lowercase hex reads back by the command language's reader: the bell and the grant the
resident names are the bytes of its config. -/
theorem ofHex_hex (b : ByteArray) : Text.ofHex (Lang.Print.hex b) = some b := by
  unfold Text.ofHex Lang.Print.hex Lang.Print.hexChars
  rw [String.toList_ofList, ← Array.foldr_toList, unhex_hexChars]
  congr 1

omit [Ord D] [DecidableEq D] in
/-- **The resident's invoke, as follow reads it**: whenever follow parses the argv the resident
sends for an answer, it is `invoke` of the object the config's `bell` names, at the method index the
description read (`sh.answer`), with exactly the argument text the resident printed, no range read,
through the grant the config names. -/
theorem invokeArgv_parse {X : Ctx D} {c : Resident.Conf} {sh : Resident.Shape} {a : String}
    {cmd : Command.Cmd D} (h : Command.parse X.digestOf (Resident.invokeArgv c sh a) = .ok cmd) :
    ∃ o g, X.digestOf c.bell = some o ∧ X.digestOf c.grant = some g ∧
      cmd = .invoke o sh.answer a {} (some g) := by
  unfold Command.parse Resident.invokeArgv Resident.hexOf at h
  split at h
  · cases h
  have hv : Verb.ofWord? "invoke" = some .invoke := by decide
  have hsv : splitVia ["--via", Lang.Print.hex c.grant] = ([], ["--via", Lang.Print.hex c.grant]) := by
    simp [splitVia]
  simp only [List.zipIdx, mapEx, fromUTF8_toUTF8', hv, bind, Except.bind, pure, Except.pure] at h
  have hn : (toString sh.answer).toNat? = some sh.answer := Nat.toNat?_repr _
  simp only [parseVerb, hsv, readsArg, pinsArg, viaArg, digestArg, numArg, ofHex_hex, hn] at h
  cases hb : X.digestOf c.bell <;> cases hg : X.digestOf c.grant <;>
    simp [hb, hg, Option.bind, bind, Except.bind, pure, Except.pure, Except.map] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-- An invoke's call body on follow's World: the object's package, and the argument TEXT read at that
package's method by `Lang.argsOf`. -/
theorem body_invoke {X : Ctx D} {me : Self D} {w : World D} {s : Signed} {o : D} {m : Nat} {a : String}
    {rg : InvokeReads} {via : Option D} {b : Body D}
    (h : Command.body X me w s (.invoke o m a rg via) = .ok b) :
    ∃ p args, invokedPackage X w o = .ok p ∧ Lang.argsOf X.digestOf (worldLook X.env w) p m a = .ok args ∧
      b = .invoke o m args invokeBudget via := by
  simp only [Command.body, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i args ha
      cases h
      exact ⟨p, args, hp, ha, rfl⟩
    · cases h

/-! ## Follow's run of one command, as the stdio leg drives it -/

/-- **Follow's World moves by its own frames.** `Moves w w'`: one frame follow answers, from a state
whose World is `w` to one whose World is `w'`: `Command.step` on ANY continuation with ANY result,
any connection's (the deployed loop, `Host.Follow.loop`: `answer`'s `Command.step`; `start` moves
nothing). A process restart reopens the World follow's steps persisted (HOST-22). -/
def Moves (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D) (w w' : World D) : Prop :=
  ∃ (f f' : Follow D) (kb res : ByteArray) (p : Persist D) (r : Command.Reply),
    f.world = w ∧ Command.step X dc B me f kb res = (f', p, r) ∧ f'.world = w'

/-- Follow's World, after any number of frames. -/
inductive Reach (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D) :
    World D → World D → Prop
  | refl (w : World D) : Reach X dc B me w w
  | tail {w w₁ w₂ : World D} : Reach X dc B me w w₁ → Moves X dc B me w₁ w₂ → Reach X dc B me w w₂

theorem Reach.trans {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w₁ w₂ : World D} (h₁ : Reach X dc B me w₁ w₂) : ∀ {w₃}, Reach X dc B me w₂ w₃ → Reach X dc B me w₁ w₃
  | _, .refl _ => h₁
  | _, .tail h hm => .tail (h₁.trans h) hm

theorem Reach.step {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w : World D} {f f' : Follow D} {kb res : ByteArray} {p : Persist D} {r : Command.Reply}
    (h : Reach X dc B me w f.world) (hs : Command.step X dc B me f kb res = (f', p, r)) :
    Reach X dc B me w f'.world :=
  .tail h ⟨f, f', kb, res, p, r, rfl, hs, rfl⟩

/-- **One command of follow's machine as the leg drives it**: `start` on the argv, then `step` on each
continuation follow handed out, with SOME result (the attempt store's, custody's, the Host's: chosen,
never trusted), follow's World moved between frames only by follow's own frames (`Reach`: other
commands' steps), ending in a `done` whose exit and bytes are the run's end. `FollowRun X dc B me f r
fe fin`: follow, at `f`, has just handed out `r`; the command ends `fin`, handed out at `fe`. -/
inductive FollowRun (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D) :
    Follow D → Command.Reply → Follow D → UInt8 × ByteArray × ByteArray → Prop
  | done {f : Follow D} {e : UInt8} {o r : ByteArray} : FollowRun X dc B me f (.done e o r) f (e, o, r)
  | step {f g f' fe : Follow D} {r r' : Command.Reply} {k res : ByteArray} {p : Persist D}
      {fin : UInt8 × ByteArray × ByteArray}
      (hk : r.cont = some k) (hg : Reach X dc B me f.world g.world)
      (hs : Command.step X dc B me g k res = (f', p, r')) (rest : FollowRun X dc B me f' r' fe fin) :
      FollowRun X dc B me f r fe fin

/-- A run moves follow's World only by its own frames. -/
theorem run_reach {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f fe : Follow D} {r : Command.Reply} {fin : UInt8 × ByteArray × ByteArray}
    (h : FollowRun X dc B me f r fe fin) : Reach X dc B me f.world fe.world := by
  induction h with
  | done => exact .refl _
  | step _ hg hs _ ih => exact (hg.step hs).trans ih

/-- What a phase-4 continuation's call bytes are: step 3's submit of a call `plan` produced, on a
World follow reached from `w₀`, for the command `argv` parses to. -/
def Planned (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D) (w₀ : World D)
    (argv : List ByteArray) (acc : List ByteArray) : Prop :=
  ∃ (w : World D), Reach X dc B me w₀ w ∧ ∃ cmd s rs b u sig, Command.parse X.digestOf argv = .ok cmd ∧
    Command.body X me w s cmd = .ok b ∧ Command.signedReads X w cmd = .ok rs ∧
    Command.plan X me w s.key rs b = .ok u ∧ acc.getLast? = some (X.callBytes ⟨u, sig⟩)

/-- Every continuation a reply carries is a state of `argv`, and a phase-4 one is `Planned`. -/
def ContOf (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D) (w₀ : World D)
    (argv : List ByteArray) (r : Command.Reply) : Prop :=
  ∀ k st, r.cont = some k → State.ofBytes k = some st →
    st.argv = argv ∧ (st.phase = 4 → Planned X dc B me w₀ argv st.acc)

/-- A continuation that does not decode is refused `badState`: no `ok`, no continuation. -/
theorem step_bad {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {f f' : Follow D} {p : Persist D} {k res : ByteArray} {r' : Command.Reply}
    (hs : Command.step X dc B me f k res = (f', p, r')) (hn : State.ofBytes k = none) :
    r' = refused (D := D) .badState := by
  unfold Command.step at hs
  simp only [hn, Prod.mk.injEq] at hs
  exact hs.2.2.symm

/-- The continuation a step hands on keeps `ContOf`, from the World the step ran at. -/
theorem contOf_step {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w₀ : World D} {argv : List ByteArray} {r r' : Command.Reply} {g f' : Follow D} {p : Persist D}
    {k res : ByteArray} (hc : ContOf X dc B me w₀ argv r) (hk : r.cont = some k)
    (hg : Reach X dc B me w₀ g.world) (hs : Command.step X dc B me g k res = (f', p, r')) :
    ContOf X dc B me w₀ argv r' := by
  intro k' st' hk' hs'
  cases hst : State.ofBytes k with
  | none => rw [step_bad hs hst] at hk'; simp [refused, Reply.cont] at hk'
  | some st =>
    obtain ⟨harg, -⟩ := hc k st hk hst
    obtain ⟨ha, h4⟩ := step_cont hst hs hk' hs'
    refine ⟨ha.trans harg, fun hp => ?_⟩
    obtain ⟨cmd, s, rs, b, u, sig, h1, h2, h3, h4', h5⟩ := h4 hp
    exact ⟨g.world, hg, cmd, s, rs, b, u, sig, harg ▸ h1, h2, h3, h4', h5⟩

/-- **A run of an invoke that ends `ok` settled a planned call committed on follow's own World**: the
`done ok` is the settlement step (`step_invoke_ok`), its continuation came from step 3's submit
(`step_cont`, through `ContOf`), so its call bytes are a call `plan` produced from that command's body
on a World follow reached, and follow's World at the settlement settles the decoded call committed
(`step_settled_ok`, T0). -/
theorem run_invoke_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w₀ : World D} {argv : List ByteArray}
    (hinv : ∀ cmd, Command.parse X.digestOf argv = .ok cmd → ∃ obj m a rg via, cmd = .invoke obj m a rg via) :
    ∀ {f : Follow D} {r : Command.Reply} {fe : Follow D} {fin : UInt8 × ByteArray × ByteArray},
      FollowRun X dc B me f r fe fin → Reach X dc B me w₀ f.world → ContOf X dc B me w₀ argv r →
      (∀ o e, r ≠ .done CommandExit.ok.code.toUInt8 o e) → fin.1 = CommandExit.ok.code.toUInt8 →
      ∃ (g : Follow D), ∃ acc, Planned X dc B me w₀ argv acc ∧ ∃ cb c hh td, acc.getLast? = some cb ∧
        X.decodeCall cb = some c ∧ settleOf X me g.world c = .committed hh td := by
  intro f r fe fin hrun
  induction hrun with
  | done =>
    intro _ _ hnd he
    exact absurd (by simp only at he; rw [he]) (hnd _ _)
  | @step f g f' fe r r' k res p fin hk hg hs rest ih =>
    intro hw hc hnd he
    have hwg := hw.trans hg
    by_cases hd : ∃ o e, r' = .done CommandExit.ok.code.toUInt8 o e
    · obtain ⟨o, e, rfl⟩ := hd
      cases hst : State.ofBytes k with
      | none => have := step_bad hs hst; simp [refused, CommandExit.code] at this
      | some st =>
        obtain ⟨harg, hpl⟩ := hc k st hk hst
        have h4 : st.phase = 4 := step_invoke_ok hst (harg ▸ hinv) hs
        obtain ⟨argv', phase, acc⟩ := st
        simp only at h4 harg
        subst h4
        obtain ⟨cb, c, hh, td, hcb, hdc, hv⟩ := step_settled_ok hst hs
        exact ⟨g, acc, hpl rfl, cb, c, hh, td, hcb, hdc, hv⟩
    · exact ih (hwg.step hs) (contOf_step hc hk hwg hs) (fun o e h => hd ⟨o, e, h⟩) he

theorem start_contOf {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {w₀ : World D} {f : Follow D} {argv : List ByteArray} :
    ContOf X dc B me w₀ argv (Command.start X me f argv) := by
  intro k st hk hs
  obtain ⟨ha, h4⟩ := start_cont hk hs
  exact ⟨ha, fun h => absurd h h4⟩

/-! ## The member socket: what the resident's leg is trusted for -/

/-- **The resident's member commands against ONE follower** (the transport premise, the `stdio-leg`
row). Read along the resident's effects in the order it performed them, from follow's World `w`:
an `ok`-exit reply to `.cmd c` is the `done` of a follower run of exactly `c`'s argv, started at a
World follow reached from `w` (follow answers other frames in between), and the reading goes on
from the World that `done` was handed out at; every other reply and every failure claims nothing
(follow's World may have moved meanwhile: the next run starts at a World `Reach`ed). The `ok` bit is
Lean's: after T0 (PROTOCOL-64) follow's only `ok` for a submitted call is its own World's settlement. -/
def LegFrom (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D)
    (conf : Resident.Conf) : World D → List Resident.Ev → Prop
  | _, [] => True
  | w, .cmd c (.ok rr) :: es =>
    if rr.exit = CommandExit.ok.code then
      ∃ f₀ fe, Reach X dc B me w f₀.world ∧
        FollowRun X dc B me f₀ (Command.start X me f₀ (c.argv conf)) fe (rr.exit.toUInt8, rr.stdout, rr.stderr) ∧
        LegFrom X dc B me conf fe.world es
    else LegFrom X dc B me conf w es
  | w, _ :: es => LegFrom X dc B me conf w es

/-- **The transport premise, named** (`gates/tcb.tsv` row `stdio-leg`): the resident's member
effects `es` are `LegFrom` some World of follow's. A hypothesis of the theorems below only. -/
def StdioLeg (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D)
    (conf : Resident.Conf) (es : List Resident.Ev) : Prop :=
  ∃ w, LegFrom X dc B me conf w es

/-- The premise is satisfiable: a trace whose member commands all failed (crash-stop) meets it, from
any World. -/
theorem legFrom_errors {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {conf : Resident.Conf} (w : World D) :
    ∀ {es : List Resident.Ev}, (∀ c x, Resident.Ev.cmd c x ∈ es → ∃ e, x = .error e) →
      LegFrom X dc B me conf w es
  | [], _ => trivial
  | e :: es, h => by
    have h' : ∀ c x, Resident.Ev.cmd c x ∈ es → ∃ e, x = .error e :=
      fun c x hx => h c x (List.mem_cons_of_mem _ hx)
    match e with
    | .cmd c (.ok rr) => obtain ⟨e, he⟩ := h c (.ok rr) (List.mem_cons_self ..); cases he
    | .cmd c (.error _) => exact legFrom_errors (es := es) w h'
    | .keep _ _ _ => exact legFrom_errors (es := es) w h'
    | .forget _ => exact legFrom_errors (es := es) w h'
    | .ask _ _ _ => exact legFrom_errors (es := es) w h'
    | .say _ => exact legFrom_errors (es := es) w h'

theorem stdioLeg_errors {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {conf : Resident.Conf} {es : List Resident.Ev} (w : World D)
    (h : ∀ c x, Resident.Ev.cmd c x ∈ es → ∃ e, x = .error e) : StdioLeg X dc B me conf es :=
  ⟨w, legFrom_errors w h⟩

/-- Reading on past effects moves only forward: a suffix is read from a World follow reached. -/
theorem legFrom_suffix {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {conf : Resident.Conf} :
    ∀ (pre : List Resident.Ev) {w : World D} {es : List Resident.Ev}, LegFrom X dc B me conf w (pre ++ es) →
      ∃ w', Reach X dc B me w w' ∧ LegFrom X dc B me conf w' es
  | [], w, es, h => ⟨w, .refl w, h⟩
  | e :: pre, w, es, h => by
    match e with
    | .cmd c (.ok rr) =>
      simp only [List.cons_append, LegFrom] at h
      split at h
      · obtain ⟨f₀, fe, hr, hrun, hl⟩ := h
        obtain ⟨w', hr', hl'⟩ := legFrom_suffix pre hl
        exact ⟨w', (hr.trans (run_reach hrun)).trans hr', hl'⟩
      · exact legFrom_suffix pre h
    | .cmd c (.error _) => exact legFrom_suffix pre (by simpa [LegFrom] using h)
    | .keep _ _ _ => exact legFrom_suffix pre (by simpa [LegFrom] using h)
    | .forget _ => exact legFrom_suffix pre (by simpa [LegFrom] using h)
    | .ask _ _ _ => exact legFrom_suffix pre (by simpa [LegFrom] using h)
    | .say _ => exact legFrom_suffix pre (by simpa [LegFrom] using h)

/-- An `ok` reply at the head of what is read is a follower run of its argv. -/
theorem legFrom_ok {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {conf : Resident.Conf} {w : World D} {c : Resident.Cmd} {rr : Resident.Reply} {es : List Resident.Ev}
    (h : LegFrom X dc B me conf w (.cmd c (.ok rr) :: es)) (hok : rr.exit = CommandExit.ok.code) :
    ∃ f₀ fe, Reach X dc B me w f₀.world ∧
      FollowRun X dc B me f₀ (Command.start X me f₀ (c.argv conf)) fe (rr.exit.toUInt8, rr.stdout, rr.stderr) ∧
      LegFrom X dc B me conf fe.world es := by
  simp only [LegFrom, if_pos hok] at h
  exact h

/-- **Every `ok` reply of a trace is a follower run of its argv** (the per-event reading the
text-grain theorem takes). -/
theorem stdioLeg_event {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)} {me : Self D}
    {conf : Resident.Conf} {es : List Resident.Ev} {c : Resident.Cmd} {rr : Resident.Reply}
    (hs : StdioLeg X dc B me conf es) (hi : Resident.Ev.cmd c (.ok rr) ∈ es) (hok : rr.exit = CommandExit.ok.code) :
    ∃ f₀ fe, FollowRun X dc B me f₀ (Command.start X me f₀ (c.argv conf)) fe (rr.exit.toUInt8, rr.stdout, rr.stderr) := by
  obtain ⟨w, hl⟩ := hs
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hi
  obtain ⟨w', -, hl'⟩ := legFrom_suffix pre hl
  obtain ⟨f₀, fe, -, hrun, -⟩ := legFrom_ok hl' hok
  exact ⟨f₀, fe, hrun⟩

/-! ## R1-R3 on the resident's side (no premise) -/

/-- **R1 is unreachable from the resident**: every command it sends starts with `read` or `invoke`,
both on the stdio surface, so nd's `notOnSurface` screen never fires on its argv. -/
theorem resident_argv_on_stdio (conf : Resident.Conf) (c : Resident.Cmd) :
    ∃ word rest, word ∈ stdioWords ∧ c.argv conf = word.toUTF8 :: rest := by
  have hr : "read" ∈ stdioWords := List.mem_map.mpr ⟨.read, List.mem_filter.mpr ⟨Verb.mem_all _, rfl⟩, rfl⟩
  have hi : "invoke" ∈ stdioWords := List.mem_map.mpr ⟨.invoke, List.mem_filter.mpr ⟨Verb.mem_all _, rfl⟩, rfl⟩
  cases c with
  | describe => exact ⟨"read", _, hr, rfl⟩
  | read sh => exact ⟨"read", _, hr, rfl⟩
  | reread sh => exact ⟨"read", _, hr, rfl⟩
  | invoke sh r t =>
    unfold Resident.Cmd.argv
    dsimp only
    split
    · exact ⟨"invoke", _, hi, rfl⟩
    · rename_i hn
      exact absurd hn (Option.isSome_iff_ne_none.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some _ _))

/-- **R2 and R3 are crash-stop to the resident**: an answer whose exit is neither `ok` nor `refused`
(nd's `client`, `hostContradicted`, `open`, `uncertain`, `declined`) is followed by exactly what a
failed connection is followed by: nothing. -/
theorem deliverAfter_unsettled {sh : Resident.Shape} {r : Resident.Ring} {rr : Resident.Reply} {e : String}
    {rest : List Resident.Ev} (hok : rr.exit ≠ CommandExit.ok.code) (hre : rr.exit ≠ CommandExit.refused.code) :
    ResidentRun.DeliverAfter sh r (.ok rr) rest ↔ ResidentRun.DeliverAfter sh r (.error e) rest := by
  simp [ResidentRun.DeliverAfter, hok, hre]

/-! ## The delivered answer -/

private theorem invoke_mem_invokes {sh : Resident.Shape} {r : Resident.Ring} {t : ByteArray}
    {x : Except String Resident.Reply} {es : List Resident.Ev} (h : Resident.Ev.cmd (.invoke sh r t) x ∈ es) :
    (r, t) ∈ Resident.invokes es := by
  unfold Resident.invokes
  exact List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- **The delivered answer is committed on the member's own World** (E2b; premise `StdioLeg`, the
`stdio-leg` row; codec premise `hX`, discharged at the deployed codec by
`Codec.Proofs.Deployed.eq_callBytes_of_decodeCall`). On every path of a tick, an invoke of `answer`
for `(r, t)` whose reply came back `ok`:
- the resident's side: `(r, t)` was the kept answer the tick was handed, or this tick kept it
  (`tick_counts`, no premise);
- the member's side: follow parsed exactly the argv the resident printed for `(r, t)`, planned on its
  World a call (`plan`, hence derived and admitted there) whose body invokes the object the config's
  `bell` names, at the method the description read, with the argument bytes `Lang.argsOf` reads from
  the TEXT `answerArg r t` at that object's own method, through the config's grant; and follow's World
  at the moment it said `ok` journals that call's transaction id (T0's `step_settled_ok`, then
  `settle_committed`: the journal entry itself, no collision disjunct).

NOT claimed here: that those argument bytes are `answerDatum r t` at `answerArgTy` (the strong form):
the resident checked the method's type only when it read the description (`Shape.read`), maybe in an
earlier tick and at an earlier World; `SocketStrong.delivered_answer_committed_strong` makes that join.
The bell's ROW (`rings[(notBefore, ringer)].answered = some (ask t)`): that is the Bell's `answer`
method (`Lang.Proofs.Bell.answer_run`), joined in `BellRow.answered_row_is_kept_answer` (HOSTING-44). A commit whose reply is
LOST is PROT-5's at-most-once: nothing here claims the converse of ok ⇒ journaled. Also not claimed:
that an ok reply's stdout is the receipt (`settled` returns step 3's pre-submit `out`), who else holds
the resident's key, liveness, and that nd's attempt loop implements `Attempt.next`.

Tooth (this theorem's, not T0's): `Cmd.argv`'s invoke arm printing `answerArg r r.text` (the ring's
own text as the answer). The event still names `(r, t)`, so `tick_counts`, `bell_resident_conforms` and
T0's `settled_ok`/`step_settled_ok` stay true; this statement's argv join does not. -/
theorem delivered_answer_committed {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)}
    {me : Self D} {w : Resident.Where} {m : Resident.Mem} {es : List Resident.Ev} {a : Resident.Tick}
    (hX : ∀ b c, X.decodeCall b = some c → X.callBytes c = b)
    (h : ResidentRun.Runs (Resident.tickP w m) es a) (hs : StdioLeg X dc B me w.conf (Resident.core es))
    {sh : Resident.Shape} {r : Resident.Ring} {t : ByteArray} {rr : Resident.Reply}
    (hi : Resident.Ev.cmd (.invoke sh r t) (.ok rr) ∈ Resident.core es)
    (hok : rr.exit = CommandExit.ok.code) :
    (m.kept = some (r, t) ∨ Resident.Ev.keep r t true ∈ Resident.core es) ∧
    ∃ (o g : D) (txt : String) (wp wf : World D) (pk : D) (args : ByteArray) (u : Unsigned D)
      (sig : ByteArray) (hh : Nat) (td : D),
      Resident.answerArg r t = some txt ∧ X.digestOf w.conf.bell = some o ∧ X.digestOf w.conf.grant = some g ∧
      invokedPackage X wp o = .ok pk ∧
      Lang.argsOf X.digestOf (worldLook X.env wp) pk sh.answer txt = .ok args ∧
      (∃ s rs, Command.plan X me wp s rs (.invoke o sh.answer args invokeBudget (some g)) = .ok u) ∧
      u.member = me.member ∧ u.body = .invoke o sh.answer args invokeBudget (some g) ∧
      wf.journalAt X.env (txIdOf X ⟨u, sig⟩) = some (hh, td) := by
  refine ⟨?_, ?_⟩
  · -- the resident's side: `tick_counts`'s one invoke
    obtain ⟨-, -, -, hinv⟩ := ResidentRun.tick_counts h
    have hmem := invoke_mem_invokes hi
    rcases hinv with hn | ⟨r', t', hrt, hc⟩
    · rw [hn] at hmem; cases hmem
    · rw [hrt, List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
      rcases hc with ⟨_, _, _, _, hd, _⟩ | ⟨_, _, _, _, _, pre, post, _, _, _, hc⟩
      · exact .inl (Lifetime.decideTick_answer_kept hd)
      · exact .inr (by rw [hc]; simp)
  · -- the member's side: the premise names a follower run of exactly this argv
    obtain ⟨txt, htxt⟩ := Option.isSome_iff_exists.mp (Nanodregg.Hosting.Proofs.Resident.answerArg_some r t)
    have hv : (Resident.Cmd.invoke sh r t).argv w.conf = Resident.invokeArgv w.conf sh txt := by
      unfold Resident.Cmd.argv
      dsimp only
      rw [htxt]
    obtain ⟨f₀, fe, hrun⟩ := stdioLeg_event hs hi hok
    rw [hv] at hrun
    have hinv : ∀ cmd, Command.parse X.digestOf (Resident.invokeArgv w.conf sh txt) = .ok cmd →
        ∃ obj m a rg via, cmd = .invoke obj m a rg via := by
      intro cmd hp
      obtain ⟨o, g, -, -, rfl⟩ := invokeArgv_parse hp
      exact ⟨_, _, _, _, _, rfl⟩
    obtain ⟨gf, acc, ⟨wp, -, cmd, s, rs, b, u, sig, hp, hb, hr, hpl, hacc⟩, cb, c, hh, td, hcb, hdc, hset⟩ :=
      run_invoke_ok (w₀ := f₀.world) hinv hrun (.refl _) start_contOf (fun _ _ => start_ne_ok) (by simp [hok])
    rw [hacc] at hcb
    cases hcb
    obtain ⟨o, g, ho, hg, rfl⟩ := invokeArgv_parse hp
    obtain ⟨pk, args, hpk, hargs, rfl⟩ := body_invoke hb
    obtain ⟨hmem, -, hbody, -⟩ := plan_admits hpl
    have htx : txIdOf X c = txIdOf X ⟨u, sig⟩ := by unfold txIdOf; rw [hX _ _ hdc]
    have hj := Protocol.Settle.settle_committed hset
    rw [htx] at hj
    exact ⟨o, g, txt, wp, gf.world, pk, args, u, sig, hh, td, htxt, ho, hg, hpk, hargs, ⟨s.key, rs, hpl⟩,
      hmem, hbody, hj⟩

omit [Ord D] [DecidableEq D] in
/-- **The strong form at the type it was checked at** (no premise beyond the ring's bounds): at a
method whose argument type is `answerArgTy`, the bytes `Lang.argsOf` reads from `answerArg r t` are
the wire encoding of `answerDatum r t`, the ring's key, its text, and the answer. -/
theorem answer_args_at_answerArgTy {digestOf : ByteArray → Option D} {look : Pinned D} {pkg : D} {m : Nat}
    {r : Resident.Ring} {t : ByteArray} {txt : String} {args : ByteArray}
    (hn : r.notBefore < Lang.Bounds.natLimit) (hx : r.text.size ≤ Lang.Bounds.bytesMax)
    (hg : r.ringer.size ≤ Lang.Bounds.digestBytesMax) (ht : t.size ≤ Lang.Bounds.bytesMax)
    (htxt : Resident.answerArg r t = some txt) (h : Lang.argsOf digestOf look pkg m txt = .ok args) :
    ∃ pk ℓ sg, Lang.readPackage look pkg = .ok pk ∧ Lang.resolveMethod (D := D) pk m = .ok (ℓ, sg) ∧
      (sg.arg = Resident.answerArgTy → Lang.Wire.encodeData Resident.answerArgTy (Resident.answerDatum r t) = some args) := by
  simp only [Lang.argsOf, bind, Except.bind] at h
  split at h
  · cases h
  rename_i pk hpk
  split at h
  · cases h
  rename_i x hres
  obtain ⟨ℓ, sg⟩ := x
  refine ⟨pk, ℓ, sg, hpk, hres, fun hty => ?_⟩
  have hrd := Nanodregg.Hosting.Proofs.Resident.answerArg_reads hn hx hg ht htxt
  dsimp only at h
  rw [hty] at h
  simp only [Lang.readAt, hrd] at h
  by_cases hd : Lang.digestsOk digestOf (Resident.answerDatum r t).digests = true
  · simp only [hd, if_true] at h
    cases he : Lang.Wire.encodeData Resident.answerArgTy (Resident.answerDatum r t) with
    | none => simp [he, throw, throwThe, MonadExceptOf.throw] at h
    | some b => simp [he, pure, Except.pure] at h; rw [h]
  · simp [hd] at h

end Nanodregg.Hosting.Proofs.Socket
