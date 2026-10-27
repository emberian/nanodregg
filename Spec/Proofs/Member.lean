/-
# Spec.Proofs.Member — A1 of the deployed system: the member's World is an audited fold from a start

`step_world_start`: one frame of the command machine leaves follow's World as it was, moves it by
`absorbPage` (every event re-derived), or, from a World that holds nothing (`atGenesis`), adopts a
base `Thin.accept` took under the pin of an invitation signed by the key the CONTINUATION names,
for the member's own World, its certificate checked (`Head.certifiesWorld`). (A sharpening of
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
        f'.world.origin = me.world ∧ Command.atGenesis f.world = true ∧
        ∃ cert, Head.certifiesWorld X f'.world cert = .ok ()) := by
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
    have hg := ‹¬ (!Command.atGenesis _) = true›
    have hc := ‹Head.certifiesWorld _ _ _ = Except.ok ()›
    rw [hst] at hp
    exact .inr (.inr ⟨_, _, _, _, _, _, hst, hp, hpin, hacc, by simpa using ho, by simpa using hg, _, hc⟩)


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
audited fold, or a World that holds nothing is replaced by a base pinned by the trusted sponsor for
the member's own World, its certificate checked. -/
theorem moves_deployed {d : ByteArray → ByteArray} {me : Command.Self Digest} {trusted : ByteArray}
    {w w' : World Digest} (hm : Moves (deployed d) (keyFaithful (deployed d)) me trusted w w') :
    (∃ l, Audited (deployed d) w l w') ∨
      (Command.atGenesis w = true ∧ PinnedBase (deployed d) me trusted w' ∧
        ∃ cert, Head.certifiesWorld (deployed d).X w' cert = .ok ()) := by
  obtain ⟨f, f', kb, res, p, r, hk, rfl, hs, rfl⟩ := hm
  have hs' : Command.step Xd Codec.Deployed.digestCodec (deployed d).B me f kb res = (f', p, r) := hs
  rcases step_world_start hs' with he | ⟨evs, steps, chain, base, ts, wb, ha⟩ |
      ⟨st, inv, key, i, dl, page, hst, hp, hpin, hacc, ho, hg, cert, hc⟩
  · exact .inl ⟨[], audited_deployed.mpr ⟨by rw [he]; rfl, trivial⟩⟩
  · obtain ⟨wb', tb, ts', h₁, h₂, -⟩ := Command.absorbPage_ok ha
    obtain ⟨l₁, f₁, hh₁⟩ := absorb_audited h₁
    obtain ⟨l₂, f₂, hh₂⟩ := absorb_audited h₂
    exact .inl ⟨l₁ ++ l₂, audited_deployed.mpr ⟨fold_append.mpr ⟨_, f₁, f₂⟩, honest_append hh₁ f₁ hh₂⟩⟩
  · obtain rfl := hk st inv key hst hp
    obtain ⟨hd, hn⟩ := Thin.accept_done world_canonical hacc
    exact .inr ⟨hg, ⟨inv, i, hpin, hd, hn, ho⟩, cert, hc⟩

/-- **A1 of the deployed system, under a key-faithful relay**: per frame (`moves_deployed`), and
along every run from the member's own start. -/
theorem top_oneHistory_member (d : ByteArray → ByteArray) :
    OneHistory.member (deployed d) (keyFaithful (deployed d)) := by
  refine ⟨fun me trusted w w' hm => moves_deployed hm, ?_⟩
  intro me trusted w₀ w _ hr
  induction hr with
  | refl => exact .refl _
  | tail _ hm ih =>
    rcases moves_deployed hm with ⟨l, ha⟩ | ⟨hg, hp, -⟩
    · exact .extend ih ha
    · exact .adopt ih hg hp

/-! ## The new A1 implies the old: the member's World is an audited fold from a start -/

section Generic

variable {S : System D}

theorem sfold_cons {w w₁ w₂ : World D} {s : Step D} {rest : List (Step D)}
    (h : S.fold w (s :: rest) = .ok w₂) (hs : S.step w s = .ok w₁) : S.fold w₁ rest = .ok w₂ := by
  simp only [System.fold, hs] at h
  split at h
  · rename_i w'' hr; cases h; exact hr
  · cases h

theorem sfold_append : ∀ {w w₁ w₂ : World D} {l l' : List (Step D)},
    S.fold w l = .ok w₁ → S.fold w₁ l' = .ok w₂ → S.fold w (l ++ l') = .ok w₂
  | w, w₁, w₂, [], l', h₁, h₂ => by
      simp only [System.fold, Except.ok.injEq] at h₁; subst h₁; simpa using h₂
  | w, w₁, w₂, s :: rest, l', h₁, h₂ => by
      cases hs : S.step w s with
      | error r => simp only [System.fold, hs] at h₁; cases h₁
      | ok w' =>
        have hr := sfold_append (sfold_cons h₁ hs) h₂
        simp only [List.cons_append, System.fold, hs, hr]

theorem decided_append : ∀ {w w₁ : World D} {l l' : List (Step D)},
    S.fold w l = .ok w₁ → Decided S w l → Decided S w₁ l' → Decided S w (l ++ l')
  | w, w₁, [], l', h₁, _, h₃ => by
      simp only [System.fold, Except.ok.injEq] at h₁; subst h₁; simpa using h₃
  | w, w₁, .turn t :: rest, l', h₁, h₂, h₃ => by
      obtain ⟨c, hc, hr, hk⟩ := h₂
      exact ⟨c, hc, hr, fun w' ha =>
        decided_append (sfold_cons h₁ (by simpa [System.step] using ha)) (hk w' ha) h₃⟩
  | w, w₁, .refusal r :: rest, l', h₁, h₂, h₃ => by
      obtain ⟨c, v, wr, hc, hr, hk⟩ := h₂
      exact ⟨c, v, wr, hc, hr, fun w' ha =>
        decided_append (sfold_cons h₁ (by simpa [System.step] using ha)) (hk w' ha) h₃⟩

theorem kept_audited {me : Command.Self D} {trusted : ByteArray} {w₀ w : World D}
    (hs : Start S me trusted w₀) (hk : Kept S me trusted w₀ w) :
    ∃ w₁ l, Start S me trusted w₁ ∧ Audited S w₁ l w := by
  induction hk with
  | refl => exact ⟨_, [], hs, rfl, trivial⟩
  | extend _ ha ih =>
    obtain ⟨w₁, l₁, hs₁, hf₁, hd₁⟩ := ih
    exact ⟨w₁, _, hs₁, sfold_append hf₁ ha.1, decided_append hf₁ hd₁ ha.2⟩
  | adopt _ _ hp =>
    obtain ⟨inv, i, hpin, hd, hn, ho⟩ := hp
    exact ⟨_, [], .pinned hpin hd hn ho, rfl, trivial⟩

/-- **The restated A1 is a strengthening**: it implies the old statement, that every World a run
from a start reaches is an audited fold from SOME start. -/
theorem OneHistory.member_audited {relay : ByteArray → ByteArray → Prop}
    (h : OneHistory.member S relay) (me : Command.Self D) (trusted : ByteArray) {w₀ w : World D}
    (hs : Start S me trusted w₀) (hr : Reach S relay me trusted w₀ w) :
    ∃ w₁ l, Start S me trusted w₁ ∧ Audited S w₁ l w :=
  kept_audited hs (h.2 me trusted w₀ w hs hr)

end Generic

end Nanodregg.Spec
