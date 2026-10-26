/-
# Spec.Proofs.Member — A1 of the deployed system: the member's World is an audited fold from a start

`step_world_start`: one frame of the command machine leaves follow's World as it was, moves it by
`absorbPage` (every event re-derived), or adopts a base `Thin.accept` took under the pin of an
invitation signed by the key the CONTINUATION names, for the member's own World. (A sharpening of
`Protocol.Proofs.FollowHead.step_world`, whose third arm says only `atGenesis`.) Under a relay whose
`adopt` continuations name the trusted key (`keyFaithful`), that base is a `Start`; every other move
is an audited fold (`Host.absorb_sound`), and folds compose (`fold_append`, `honest_append`).
-/
import Spec.Proofs.Bridge
import Protocol.Proofs.FollowHead
import Protocol.Proofs.Thin
import Host.Proofs.Refine
import Codec.Proofs.Deployed

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

variable {D : Type} [Ord D] [DecidableEq D]

/-- **What one frame does to follow's World**, with the adopt arm's evidence. -/
theorem step_world_start {X : Ctx D} {dc : Codec.Stream D} {B : Thin.Base (World D)}
    {me : Command.Self D} {f f' : Command.Follow D} {p : Command.Persist D} {kb res : ByteArray}
    {r : Command.Reply} (h : Command.step X dc B me f kb res = (f', p, r)) :
    f'.world = f.world ∨
      (∃ (evs : List ByteArray) (steps : Nat) (chain : ByteArray) (base : Nat)
          (ts : List (Kernel.Step D × D)) (wb : Option (World D)),
        Command.absorbPage X f.world evs steps chain base = .ok (f'.world, ts, wb)) ∨
      (∃ (st : Command.State) (inv key : ByteArray) (i : Invite.Invitation D)
          (dl : Option Thin.Download) (page : Thin.Page),
        Command.State.ofBytes kb = some st ∧
        Command.parse X.digestOf st.argv = .ok (Command.Cmd.adopt inv key) ∧
        Command.adoptPin X me inv key = .ok i ∧ Thin.accept B i.pin dl page = .ok (.done f'.world) ∧
        f'.world.origin = me.world) := by
  unfold Command.step at h
  repeat' split at h
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (repeat' split at h)
  all_goals (try simp only [Prod.mk.injEq] at h)
  all_goals (try (obtain ⟨rfl, -, -⟩ := h))
  all_goals first
    | exact .inl rfl
    | exact .inr (.inl ⟨_, _, _, _, _, _, Command.absorbSync_ok ‹_›⟩)
    | skip
  all_goals (try (cases ‹_ = Command.Cmd.adopt _ _›))
  all_goals
    have hst := ‹Command.State.ofBytes kb = some _›
    have hp := ‹Command.parse _ _ = Except.ok (Command.Cmd.adopt _ _)›
    have hpin := ‹Command.adoptPin _ _ _ _ = Except.ok _›
    have hacc := ‹Thin.accept _ _ _ _ = Except.ok (Thin.Progress.done _)›
    have ho := ‹¬ _ ≠ me.world›
    rw [hst] at hp
    exact .inr (.inr ⟨_, _, _, _, _, _, hst, hp, hpin, hacc, by simpa using ho⟩)


private abbrev Xd : Ctx Digest := Host.Deployed.X

/-- The deployed World codec is canonical (`Thin.accept_done`'s premise). -/
theorem world_canonical (b : ByteArray) (v : World Digest)
    (h : Host.Deployed.world.decode b = .ok v) : Host.Deployed.world.bytes v = b :=
  (Codec.Deployed.eq_bytes_of_world_decode (w := v) h).symm

/-- An absorbed run of events is an audited fold (the deployed call codec is canonical). -/
theorem absorb_audited {w w' : World Digest} {acc ts : Array (Kernel.Step Digest × Digest)}
    {evs : List ByteArray} (h : Command.absorb Xd w acc evs = .ok (w', ts)) :
    ∃ l, World.fold Xd.env w l = .ok w' ∧ Honest Xd w l := by
  obtain ⟨ps, -, hr, hh, -⟩ := Host.absorb_sound (fun _ _ hd => (Codec.Deployed.eq_callBytes_of_decodeCall _ hd).2.symm) h
  exact ⟨_, RootedFold.fold hr, hh⟩

/-- **One frame of the deployed follower, under a key-faithful relay**: follow's World moves by an
audited fold, or it is replaced by a start (an adopted base pinned by the trusted sponsor). -/
theorem moves_deployed {d : ByteArray → ByteArray} {me : Command.Self Digest} {trusted : ByteArray}
    {w w' : World Digest} (hm : Moves (deployed d) (keyFaithful (deployed d)) me trusted w w') :
    (∃ l, World.fold Xd.env w l = .ok w' ∧ Honest Xd w l) ∨ Start (deployed d) me trusted w' := by
  obtain ⟨f, f', kb, res, p, r, hk, rfl, hs, rfl⟩ := hm
  have hs' : Command.step Xd Codec.Deployed.digestCodec (deployed d).B me f kb res = (f', p, r) := hs
  rcases step_world_start hs' with he | ⟨evs, steps, chain, base, ts, wb, ha⟩ |
      ⟨st, inv, key, i, dl, page, hst, hp, hpin, hacc, ho⟩
  · exact .inl ⟨[], by rw [he]; rfl, trivial⟩
  · obtain ⟨wb', tb, ts', h₁, h₂, -⟩ := Command.absorbPage_ok ha
    obtain ⟨l₁, f₁, hh₁⟩ := absorb_audited h₁
    obtain ⟨l₂, f₂, hh₂⟩ := absorb_audited h₂
    exact .inl ⟨l₁ ++ l₂, fold_append.mpr ⟨_, f₁, f₂⟩, honest_append hh₁ f₁ hh₂⟩
  · obtain rfl := hk st inv key hst hp
    obtain ⟨hd, hn⟩ := Thin.accept_done world_canonical hacc
    exact .inr (.pinned hpin hd hn ho)

/-- **A1 of the deployed system, under a key-faithful relay.** -/
theorem top_oneHistory_member (d : ByteArray → ByteArray) :
    OneHistory.member (deployed d) (keyFaithful (deployed d)) := by
  intro me trusted w₀ w hs hr
  induction hr with
  | refl => exact ⟨_, [], hs, audited_deployed.mpr ⟨rfl, trivial⟩⟩
  | tail _ hm ih =>
    obtain ⟨w₁, l, hs₁, ha⟩ := ih
    rw [audited_deployed] at ha
    rcases moves_deployed hm with ⟨l', hf', hh'⟩ | hs'
    · exact ⟨w₁, l ++ l', hs₁, audited_deployed.mpr
        ⟨fold_append.mpr ⟨_, ha.1, hf'⟩, honest_append ha.2 ha.1 hh'⟩⟩
    · exact ⟨_, [], hs', audited_deployed.mpr ⟨rfl, trivial⟩⟩

end Nanodregg.Spec
