/-
# Spec.Proofs.Durable2 — §5 DURABILITY, the follower's Store and the resident's volume

**D2, `Durable.follower`.** Every step of follow's command machine (`S.follow`, what `host follow`
answers a `resume` frame with) that persists steps persists a rooted run of the system's own kernel
from follow's World to the World it moves to: each step taken by `S.step` in order, beside the roots
digest of the World it reached, ending at follow's next World. No premise. `follow_answer_persists`
says the frame handler (`Host.Follow.answer`) persists nothing else: a frame persists either no step
or exactly what the machine's step persists.
Not stated (owed): "appended before sent". In `Host.Follow.loop` the `.steps ts` arm runs
`Host.append` (the record, `fsync`ed) before `port.send`, but the loop is `IO` over `Store`/`Port`
records of `IO` actions, so no theorem can speak of their order today; it becomes statable when the
loop is an interpreter over effect records (§11.4, as `Hosting.Resident.Prog` already is). The
`.adopt w'` clause (the adopted World is a `Start`) is A1's (`OneHistory.member`, under
`keyFaithful`), not repeated here.

**D3, `Durable.resident S`** (over the field `S.keep`). The resident's kept answer survives every crash intact or as it
was: a keep stopped after ANY prefix of its steps comes back, in every crash outcome, with the old
kept text or the new one; a completed keep comes back with exactly the new text; the restart's
resume (`durableResumeVia keep`, the deployed `resumeOps`) comes back with exactly what the start
read. Premises of the prefix clause, each an invariant the volume keeps (`Hosting.Proofs.ResidentVolume`,
`fresh_*`, `live_*`, `stable_*`), each true of the empty volume: `Stable` (the kept name and its
file durable), `Fresh` (every inode named is allocated), `Live` (the live entry is remembered); the
resume clause excludes an unreadable entry (the start stops `volume` before resuming it). Over the
contract `Resident.Volume`; that the filesystem meets it is the operator's.
-/
import Spec.Sim.Durable2
import Spec.Proofs.Floor
import Protocol.Proofs.Command
import Host.Follow
import Kernel.Proofs.RootedFold
import Hosting.Proofs.ResidentVolume

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Hosting.Resident Nanodregg.Hosting.Proofs.ResidentVolume

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## D2: the follower's Store -/

/-- **D2.** What a step of follow's machine persists is a rooted run of the system's kernel from
follow's World to its next one. -/
def Durable.follower (S : System D) : Prop :=
  ∀ (me : Command.Self D) (f f' : Command.Follow D) (kb res : ByteArray) (ts : List (Step D × D))
    (r : Command.Reply), S.follow me f kb res = (f', .steps ts, r) →
    Rooted S.step (World.roots S.X.env) f.world ts f'.world

/-- The system's step is the kernel's, for a system whose `admit`/`refuse` are the kernel's. -/
theorem system_step_eq (S : System D) (ha : S.admit = World.admit S.X.env)
    (hr : S.refuse = World.refuse S.X.env) : S.step = World.step S.X.env := by
  funext w s
  cases s <;> simp [System.step, World.step, ha, hr]

/-- **D2 of the deployed system**: `step_persists_admitted` (PROTOCOL). -/
theorem top_durable_follower (d : ByteArray → ByteArray) : Durable.follower (deployed d) := by
  intro me f f' kb res ts r h
  rw [system_step_eq _ rfl rfl]
  dsimp only [deployed] at h
  exact Command.step_persists_admitted h

/-- What `host follow`'s frame handler persists: no step, or exactly what the machine's step
persists (a `resume` frame); a `command` frame, a hang-up and every refusal persist nothing. -/
theorem follow_answer_persists {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)}
    {me : Command.Self D} {fs fs' : Command.Follow D} {fr : Host.Frame} {ts : List (Step D × D)}
    {st : UInt8} {pl : ByteArray}
    (h : Host.Follow.answer X dc B me fs fr = (fs', .steps ts, st, pl)) :
    ts = [] ∨ ∃ kb res r, Command.step X dc B me fs kb res = (fs', .steps ts, r) := by
  unfold Host.Follow.answer at h
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals first
    | exact .inl (Command.Persist.steps.inj h.2.1).symm
    | exact .inl (Command.Persist.steps.inj h.2.1)
    | (obtain ⟨rfl, rfl, -⟩ := h; exact .inr ⟨_, _, _, ‹_›⟩)
    | (split at h <;> (try simp only [Prod.mk.injEq] at h) <;> first
        | exact .inl (Command.Persist.steps.inj h.2.1).symm
        | exact .inl (Command.Persist.steps.inj h.2.1)
        | (obtain ⟨rfl, rfl, -⟩ := h; exact .inr ⟨_, _, _, ‹_›⟩))

/-- **FLOOR (D2).** The claim refuses the follower that takes the World it is told: it persists no
step, yet moves its World (one more Turn than it has steps), which no empty run reaches. -/
theorem floor_durable_follower (d : ByteArray → ByteArray) : ¬ Durable.follower (trustingFollower d) := by
  intro h
  have hr := h ⟨oneDigest, oneDigest, oneDigest, 0⟩ ⟨wGenesis, none, none⟩ _ .empty .empty [] _ rfl
  have he : told wGenesis = wGenesis := hr
  have hh := congrArg World.height he
  have hg : wGenesis.height = wGenesis.steps := by
    unfold wGenesis
    simp [genesisWorld, World.genesis]
  simp only [told] at hh
  omega

/-! ## D3: the resident's volume -/

/-- **D3.** A keep is atomic across a crash after any prefix of its steps, durable once complete,
and the resume over it reads back what the start read. -/
def Durable.resident {D : Type} [Ord D] [DecidableEq D] (S : System D) : Prop :=
  (∀ (v : Vol) (w : Where) (s : String), Stable v w.kept → Fresh v → Live v →
    ∀ (n : Nat) (v' : Vol), Crash (v.applyAll ((S.keep w s).take n)) v' →
      v'.read w.kept = v.read w.kept ∨ v'.read w.kept = some (some s)) ∧
  (∀ (v : Vol) (w : Where) (s : String) (v' : Vol), Crash (v.applyAll (S.keep w s)) v' →
    v'.read w.kept = some (some s)) ∧
  (∀ (v : Vol) (w : Where), v.read w.kept ≠ some none → ∀ v' : Vol,
    Crash (v.applyAll (durableResumeVia S.keep w (v.read w.kept))) v' → v'.read w.kept = v.read w.kept)

/-- The resume over the deployed keep is the deployed resume. -/
theorem durableResumeVia_keepOps (w : Where) (r : Option (Option String)) :
    durableResumeVia keepOps w r = resumeOps w r := by
  rcases r with _ | _ | _ <;> rfl

/-- **D3 of the deployed resident**: `keep_atomic`, `keep_durable`, `resume_durable`. -/
theorem top_durable_resident (d : ByteArray → ByteArray) : Durable.resident (deployed d) :=
  ⟨fun v w s hs hf hl n v' hc => keep_atomic v w s hs hf hl n v' hc,
   fun v w s v' hc => keep_durable v w s v' hc,
   fun v w hu v' hc => by
     change Crash (v.applyAll (durableResumeVia keepOps w (v.read w.kept))) v' at hc
     rw [durableResumeVia_keepOps] at hc
     exact resume_durable v w hu v' hc⟩

/-- The empty volume holds every name durably. -/
theorem stable_empty (p : System.FilePath) : Stable Vol.empty p :=
  ⟨rfl, fun _ h => by simp [Vol.empty] at h⟩

/-- **FLOOR (D3).** The claim refuses the in-place keep: from the empty volume, a crash after its
fourth step (`in_place_loses_both`) leaves the kept name unreadable, neither nothing nor the text. -/
theorem floor_durable_resident (d : ByteArray → ByteArray) :
    ¬ Durable.resident { deployed d with keep := inPlaceKeep } := by
  intro h
  obtain ⟨v', hc, hr⟩ := in_place_loses_both Vol.empty durableWhere "a" fresh_empty live_empty
  have := h.1 Vol.empty durableWhere "a" (stable_empty _) fresh_empty live_empty 4 v' hc
  rw [hr] at this
  simp [Vol.read, Vol.empty] at this

end Nanodregg.Spec
