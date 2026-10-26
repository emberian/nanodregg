/-
# Spec.Proofs.Floor — each claim refutes a trivial system, and a deployed run reaches it

The tree's whole vacuity obligation (TOPLEVEL-SPEC §1.3). For each claim of `Spec.Proofs.Claims`:

* REFUTED: `deployed` with one field replaced by what a lazy implementation would do, and a theorem
  that the claim is false of it. A claim that held of every system would hold of these.
* INHABITED: a deployed run that reaches the claim's non-trivial case, so the claim is not true
  only of a system that never admits anything.

The deployed run is computed, not modelled: a genesis World with one founder, built by the kernel
from Ed25519 keys, and one signed call of that founder (a `rotate` to its precommitted key), decided
by THE re-deriver at the deployed `Ctx`. Its facts are closed computations at the deployed digest,
hash and signature, which the kernel cannot reduce (cSHAKE256 and Ed25519 under whnf), so they are
`native_decide` (allow rows in `gates/axioms-allow.tsv`, trust rows in `gates/tcb.tsv`).
-/
import Spec.Proofs.Bridge
import Spec.Trivial
import Kernel.Proofs.Origin
import Kernel.Proofs.Refusals
import Kernel.Sim.Deployed
import Kernel.Proofs.Admit
import Kernel.Proofs.Refuse
import Protocol.Proofs.Foreign

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The deployed run -/

private abbrev Xd : Ctx Digest := Host.Deployed.X

private def wSeed (t : String) : ByteArray := Kernel.Sim.Deployed.seed t.toUTF8

private def wKey : ByteArray := Ed25519.publicKey (wSeed "f0")
private def wNext : ByteArray := Ed25519.publicKey (wSeed "f0-next")

/-- One founder, its key and its precommitted next key. -/
private def wGenesis : World Digest :=
  genesisWorld Xd "spec".toUTF8 "spec-0".toUTF8 100000000 [(wKey, nextKeyDigest Xd wNext)]
    Authority.none

private def wMember : Digest := founderId Xd wGenesis.origin 0

/-- The founder rotates to its precommitted key, signed by that key (a rotate is signed by the key it moves to, `receiveWith_key`). -/
private def wCall : Call Digest :=
  let u : Unsigned Digest :=
    { world := wGenesis.origin, member := wMember, key := wNext, notBefore := 0, validUntil := 101,
      pins := [(wMember, pinOf Xd.env (wGenesis.entry Xd.env wMember))], maxCharge := 1000000,
      body := .rotate wNext (nextKeyDigest Xd (Ed25519.publicKey (wSeed "f0-next-next"))) }
  ⟨u, Ed25519.sign (wSeed "f0-next") (Xd.callMessage u)⟩

/-- The log the writer stages for that call. -/
private def wLog : List (Step Digest) :=
  match submit Xd wGenesis wCall with
  | .ok (t, _) => [.turn t]
  | .error _ => []

theorem run_rederives : (rederiveLog Xd wGenesis wLog).toOption.map World.height = some 1 := by
  native_decide

/-- **The deployed run**: from a genesis World, a log that THE re-deriver accepts reaches a World of
positive height (an admitted Turn: a refusal does not move the height). -/
theorem deployed_run : ∃ (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × Digest))
    (auth : Authority) (l : List (Step Digest)) (w : World Digest),
    World.fold Xd.env (genesisWorld Xd name nonce allowance founders auth) l = .ok w ∧
      Honest Xd (genesisWorld Xd name nonce allowance founders auth) l ∧ 0 < w.height := by
  have hh := run_rederives
  cases hr : rederiveLog Xd wGenesis wLog with
  | error e => rw [hr] at hh; cases hh
  | ok w =>
    rw [hr] at hh
    have h1 : w.height = 1 := by simpa [Except.toOption] using hh
    have hs : World.fold Xd.env wGenesis wLog = .ok w ∧ Honest Xd wGenesis wLog := rederiveLog_sound hr
    unfold wGenesis at hs
    revert hs
    generalize wLog = l
    intro hs
    exact ⟨_, _, _, _, _, l, w, hs.1, hs.2, by omega⟩

/-- **INHABITED (§2, §3).** The deployed system has an audited log from a start that admits a Turn. -/
theorem inhabited_audited (d : ByteArray → ByteArray) (me : Command.Self Digest) (trusted : ByteArray) :
    ∃ g l w, Start (deployed d) me trusted g ∧ Audited (deployed d) g l w ∧ 0 < w.height := by
  obtain ⟨name, nonce, a, fs, au, l, w, hf, hh, hw⟩ := deployed_run
  refine ⟨genesisWorld Host.Deployed.X name nonce a fs au, l, w, Start.genesis name nonce a fs au, ?_, hw⟩
  exact audited_deployed.mpr ⟨hf, hh⟩

/-! ## §2 ONE HISTORY: the follower that takes the World it is told -/

/-- A digest other than the zero one. -/
private def oneDigest : Digest := ⟨⟨Array.replicate 32 1⟩, by simp [ByteArray.size]⟩

private theorem state_empty : Command.State.ofBytes ByteArray.empty = none := by decide +kernel

/-- **FLOOR (A1).** Even under the relay premise the deployed theorem needs, the claim refuses the
trusting follower: the World it reaches has more Turns than steps and another World's origin, which
no audited fold from a genesis or from a pinned base of the member's own World can reach. -/
theorem floor_oneHistory_member (d : ByteArray → ByteArray) :
    ¬ OneHistory.member (trustingFollower d) (keyFaithful (trustingFollower d)) := by
  intro h
  let me : Command.Self Digest := ⟨oneDigest, oneDigest, oneDigest, 0⟩
  have hmove : Moves (trustingFollower d) (keyFaithful (trustingFollower d)) me .empty wGenesis
      (told wGenesis) :=
    by
      refine ⟨⟨wGenesis, none, none⟩, _, .empty, .empty, _, _, ?_, rfl, rfl, rfl⟩
      intro st _ _ hs
      rw [state_empty] at hs
      cases hs
  obtain ⟨w₁, l, hs, ha⟩ := h me .empty _ _
    (.genesis "spec".toUTF8 "spec-0".toUTF8 100000000 [(wKey, nextKeyDigest Xd wNext)] Authority.none)
    (.tail (.refl _) hmove)
  have hf := ((audited_iff (trustingFollower d) rfl rfl rfl rfl).mp ha).1
  cases hs with
  | genesis name nonce a fs au =>
    have := reach_height_le_steps hf
    simp only [told] at this
    omega
  | pinned _ _ _ ho =>
    have := fold_origin hf
    simp only [told] at this
    rw [ho] at this
    exact absurd (congrArg (fun x : Digest => x.bytes.data) this) (by decide)

/-! ## §2 ONE HISTORY (A2): the chain that binds nothing -/

/-- The run's call with another next-key digest: the founder could have rotated either way. -/
private def wCall2 : Call Digest :=
  let u : Unsigned Digest :=
    { wCall.unsigned with body := .rotate wNext (nextKeyDigest Xd (Ed25519.publicKey (wSeed "f0-other"))) }
  ⟨u, Ed25519.sign (wSeed "f0-next") (Xd.callMessage u)⟩

private def wLog2 : List (Step Digest) :=
  match submit Xd wGenesis wCall2 with
  | .ok (t, _) => [.turn t]
  | .error _ => []

/-- No two distinct preimages in the list hash alike: `CollidesAmong`'s negation, as a computation. -/
private def collisionFree (hash : String → ByteArray → Digest) (S : List (String × ByteArray)) : Bool :=
  S.all fun p => S.all fun q => decide (p = q ∨ hash p.1 p.2 ≠ hash q.1 q.2)

private theorem not_collides {hash : String → ByteArray → Digest} {S : List (String × ByteArray)}
    (h : collisionFree hash S = true) : ¬ CollidesAmong hash S := by
  rintro ⟨p, hp, q, hq, hne, he⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h p hp) q hq
  simp only [decide_eq_true_eq] at this
  rcases this with h' | h'
  · exact hne h'
  · exact h' he

/-- **The two rotations**: each admits at the genesis World; the first's World journals the first
call and the second's does not; and no two of the two folds' link inputs collide. -/
theorem run_two_rotations :
    (match wLog, wLog2 with
     | [.turn t₁], [.turn t₂] =>
        match World.admit Xd.env wGenesis t₁, World.admit Xd.env wGenesis t₂ with
        | .ok w₁, .ok w₂ =>
            (w₁.journalAt Xd.env (txIdOf Xd wCall)).isSome && (w₂.journalAt Xd.env (txIdOf Xd wCall)).isNone &&
              collisionFree Xd.env.hash (foldPres Xd.env wGenesis wLog ++ foldPres Xd.env wGenesis wLog2)
        | _, _ => false
     | _, _ => false) = true := by
  native_decide

/-- **FLOOR (A2).** The claim refuses a kernel whose chain does not move: two different rotations
reach two Worlds of one step count and one chain, with no collision among the link inputs. -/
theorem floor_oneHistory_pair (d : ByteArray → ByteArray) : ¬ OneHistory.pair (chainless d) := by
  intro h
  have hr := run_two_rotations
  revert hr
  generalize wLog = L₁
  generalize wLog2 = L₂
  intro hr
  split at hr
  · rename_i t₁ t₂
    split at hr
    · rename_i w₁ w₂ ha₁ ha₂
      simp only [Bool.and_eq_true] at hr
      obtain ⟨⟨hj₁, hj₂⟩, hc⟩ := hr
      have hf₁ : (chainless d).fold wGenesis [.turn t₁] = .ok { w₁ with chain := wGenesis.chain } := by
        simp [System.fold, System.step, chainless, deployed, ha₁, Except.map]
      have hf₂ : (chainless d).fold wGenesis [.turn t₂] = .ok { w₂ with chain := wGenesis.chain } := by
        simp [System.fold, System.step, chainless, deployed, ha₂, Except.map]
      rcases h hf₁ hf₂ (by simp [admit_steps ha₁, admit_steps ha₂]) rfl with he | hcol
      · have := congrArg (fun w : World Digest => (w.journalAt Xd.env (txIdOf Xd wCall)).isSome) he
        simp only [World.journalAt] at this hj₁ hj₂
        simp_all
      · exact not_collides hc hcol
    · cases hr
  · cases hr

/-! ## §4 CONSENT: the follower that reports the Host's word, the settlement that is always final -/

private def wCb : ByteArray := Xd.callBytes wCall

/-- A settle-phase continuation carrying the run's call. -/
private def wKb : ByteArray := (Command.State.bytes ⟨[], 4, [wCb]⟩).getD .empty

theorem run_continuation :
    (Command.State.ofBytes wKb).map (fun s => decide (s.argv = [] ∧ s.phase = 4 ∧ s.acc = [wCb])) =
      some true := by
  native_decide

theorem run_call_decodes : Xd.decodeCall wCb = some wCall := by native_decide

/-- **FLOOR (C(ii)).** The claim refuses a follower that says `ok` of a call its World does not
journal: the run's call, at the genesis World, before anyone submitted it. -/
theorem floor_consent_okCommitted (d : ByteArray → ByteArray) : ¬ Consent.okCommitted (hostWord d) := by
  intro h
  have hk := run_continuation
  cases hs : Command.State.ofBytes wKb with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    obtain ⟨argv, ph, acc⟩ := st
    have hb : argv = [] ∧ ph = 4 ∧ acc = [wCb] := by simpa using hk
    obtain ⟨rfl, rfl, rfl⟩ := hb
    obtain ⟨cb, c, hh, td, hl, hd, hj⟩ :=
      h ⟨oneDigest, oneDigest, oneDigest, 0⟩ ⟨wGenesis, none, none⟩ _ wKb .empty .empty .empty _ [] [wCb]
        hs rfl
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    have hd' : Xd.decodeCall wCb = some c := hd
    rw [run_call_decodes] at hd'
    cases hd'
    have hj' : wGenesis.journalAt Xd.env (txIdOf Xd wCall) = some (hh, td) := hj
    rw [wGenesis, Foreign.genesisWorld_journalAt] at hj'
    cases hj'

private theorem genesisWorld_refusalsCanon {D : Type} [Ord D] [DecidableEq D] (X : Ctx D)
    (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × D)) (au : Authority) :
    (genesisWorld X name nonce a fs au).RefusalsCanon X.env :=
  genesis_refusalsCanon X.env (originOf X name nonce a fs au) a

private theorem genesisWorld_journalCanon {D : Type} [Ord D] [DecidableEq D] (X : Ctx D)
    (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × D)) (au : Authority) :
    (genesisWorld X name nonce a fs au).JournalCanon X.env :=
  genesis_journalCanon X.env (originOf X name nonce a fs au) a

theorem run_call_admits :
    (match submit Xd wGenesis wCall with | .ok _ => true | .error _ => false) = true := by
  native_decide

/-- **FLOOR (C(iii)).** The claim refuses a settlement that calls final a call the writer then
admits: the run's call, on the genesis World, on the empty extension. -/
theorem floor_consent_final (d : ByteArray → ByteArray) : ¬ Consent.final (alwaysFinal d) := by
  intro h
  have hrc : wGenesis.RefusalsCanon Xd.env := genesisWorld_refusalsCanon Xd _ _ _ _ _
  have hjc : wGenesis.JournalCanon Xd.env := genesisWorld_journalCanon Xd _ _ _ _ _
  have ha := run_call_admits
  cases hs : submit Xd wGenesis wCall with
  | error _ => rw [hs] at ha; cases ha
  | ok out =>
    revert hs hrc hjc
    generalize wGenesis = g
    generalize wCall = c
    intro hrc hjc hs
    exact h ⟨oneDigest, oneDigest, oneDigest, 0⟩ c (l := []) hrc hjc (.inl rfl) rfl out hs

/-! ## §8 SHOWN: the host that serves every frame -/

private theorem envelope_empty : Envelope.ofBytes Xd ByteArray.empty = none := by decide +kernel

/-- **FLOOR (G2).** The claim refuses a host that defers a frame whose payload is no envelope. -/
theorem floor_shown (d : ByteArray → ByteArray) : ¬ Shown.onlyFollowers (openHost d) := by
  intro h
  obtain ⟨e, he, -⟩ := h wGenesis ⟨0, 0, .empty⟩ (.log 0) rfl
  have : Envelope.ofBytes Xd ByteArray.empty = some e := he
  rw [envelope_empty] at this
  cases this

end Nanodregg.Spec
