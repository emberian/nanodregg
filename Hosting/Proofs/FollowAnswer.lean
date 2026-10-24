/-
# Hosting.Proofs.FollowAnswer — follow's answer to a frame moves its World only by `Command.step` (HOSTING-50)

`Host.Follow.loop` answers each frame by `Host.Follow.answer`, a pure function of follow's state and
the frame, and goes on with the World `answer` returned (gates/tcb.tsv `follow-loop`: the three arms
of the IO loop that hand that World on, through `Host.append` for absorbed steps, are the trusted
part). This module is the pure half, which the old `stdio-leg` row carried as trust:

- `answer_world`: the World `answer` returns is the one it was given (a refusal before the machine, a
  hang-up, `Command.start`), or the World of `Command.step` on the frame's own continuation and
  result.
- `answer_reach`: so it is `ReachOn` the frame's own result (`Socket.ReachOn`, the premise
  `StdioLeg` and the journal join quantify over): `[]`, or `[res]` for the `res` the frame decoded to.
-/
import Hosting.Proofs.Socket
import Host.Follow

namespace Nanodregg.Hosting.Proofs.Socket

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Protocol.Command

variable {D : Type} [Ord D] [DecidableEq D]

/-- **What `answer` does to follow's World**: nothing, or one `Command.step` on the continuation and
the result the frame itself carries (a `resume` frame that decoded to `v`). -/
theorem answer_world (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D)
    (fs : Follow D) (f : Host.Frame) :
    (Host.Follow.answer X dc B me fs f).1.world = fs.world ∨
      ∃ v, Protocol.resumeFrame.decode f.payload = .ok v ∧
        ∃ (fs' : Follow D) (p : Persist D) (r : Command.Reply),
          Command.step X dc B me fs v.1.1 v.2.1.1 = (fs', p, r) ∧
            (Host.Follow.answer X dc B me fs f).1.world = fs'.world := by
  unfold Host.Follow.answer
  split
  · split <;> exact .inl rfl
  · split
    · exact .inl rfl
    · dsimp only; split <;> exact .inl rfl
  · split
    · exact .inl rfl
    · rename_i k res heq
      dsimp only
      refine .inr ⟨(k, res, ()), heq, _, _, _, rfl, ?_⟩
      split <;> rfl
  · exact .inl rfl

/-- **Follow's answer to a frame is a `ReachOn` of that frame's own result**: `[]` (no step), or
`[res]` for the result `res` the `resume` frame decoded to. -/
theorem answer_reach (X : Ctx D) (dc : Codec.Stream D) (B : Thin.Base (World D)) (me : Self D)
    (fs : Follow D) (f : Host.Frame) :
    ∃ S, (S = [] ∨ ∃ v, Protocol.resumeFrame.decode f.payload = .ok v ∧ S = [v.2.1.1]) ∧
      ReachOn X dc B me S fs.world (Host.Follow.answer X dc B me fs f).1.world := by
  rcases answer_world X dc B me fs f with h | ⟨v, hv, fs', p, r, hs, h⟩
  · exact ⟨[], .inl rfl, h ▸ ReachOn.refl _⟩
  · exact ⟨[v.2.1.1], .inr ⟨v, hv, rfl⟩, h ▸ ReachOn.step (S := []) (ReachOn.refl _) hs⟩

end Nanodregg.Hosting.Proofs.Socket
