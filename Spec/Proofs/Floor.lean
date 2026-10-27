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
import Spec.Sim.Run
import Kernel.Proofs.Origin
import Kernel.Proofs.Refusals
import Kernel.Sim.Deployed
import Kernel.Proofs.Admit
import Kernel.Proofs.Refuse
import Protocol.Proofs.Foreign

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec

/-! ## The deployed run -/

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

theorem state_empty : Command.State.ofBytes ByteArray.empty = none := by decide +kernel

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

theorem not_collides {hash : String → ByteArray → Digest} {S : List (String × ByteArray)}
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

theorem genesisWorld_refusalsCanon {D : Type} [Ord D] [DecidableEq D] (X : Ctx D)
    (name nonce : ByteArray) (a : Nat) (fs : List (ByteArray × D)) (au : Authority) :
    (genesisWorld X name nonce a fs au).RefusalsCanon X.env :=
  genesis_refusalsCanon X.env (originOf X name nonce a fs au) a

theorem genesisWorld_journalCanon {D : Type} [Ord D] [DecidableEq D] (X : Ctx D)
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

theorem envelope_empty : Envelope.ofBytes Xd ByteArray.empty = none := by decide +kernel

/-- **FLOOR (G2).** The claim refuses a host that defers a frame whose payload is no envelope. -/
theorem floor_shown (d : ByteArray → ByteArray) : ¬ Shown.onlyFollowers (openHost d) := by
  intro h
  obtain ⟨e, he, -⟩ := h wGenesis ⟨0, 0, .empty⟩ (.log 0) rfl
  have : Envelope.ofBytes Xd ByteArray.empty = some e := he
  rw [envelope_empty] at this
  cases this

/-! ## §3 INTEGRITY (B2): the kernel that mints -/

/-- **The mint**: at the genesis World the kernel refuses the Turn `notConserved` (and only
`checkValue` refuses it: the minting kernel admits it), and the World the minting kernel reaches
holds a balance sum of the denomination the genesis World does not. -/
theorem run_mint :
    ((match World.admit Xd.env wGenesis tMint with | .error (.notConserved _) => true | _ => false) &&
      match checkMinting Xd.env wGenesis tMint with
      | .ok (posts, rr) =>
          decide ((commitWith Xd.env wGenesis tMint posts rr).valueSum mintDenom ≠ wGenesis.valueSum mintDenom)
      | .error _ => false) = true := by
  native_decide

/-- One Turn the minting kernel's checks pass is a one-step fold of it. -/
theorem minting_fold_one (d : ByteArray → ByteArray) {g : World Digest} {t : Turn Digest}
    {posts : List (Post Digest)} {rr : Rows Digest × Nat} (hm : checkMinting Xd.env g t = .ok (posts, rr)) :
    (minting d).fold g [.turn t] = .ok (commitWith Xd.env g t posts rr) := by
  have hs : (minting d).admit g t = .ok (commitWith Xd.env g t posts rr) := by
    show (match checkMinting Xd.env g t with
      | .ok (posts, rr) => Except.ok (commitWith Xd.env g t posts rr)
      | .error r => .error r) = _
    rw [hm]
  simp only [System.fold, System.step, hs]

/-- **FLOOR (B2).** The claim refuses the kernel that admits without `checkValue`: from the
(canonical) genesis World, one Turn bearing an unbalanced value cell changes a denomination's sum. -/
theorem floor_integrity_value (d : ByteArray → ByteArray) : ¬ Integrity.value (minting d) := by
  intro h
  have hc : wGenesis.Canon Xd.env := by unfold wGenesis; exact receive_genesis_canon Xd _ _ _ _ _
  have hr := run_mint
  simp only [Bool.and_eq_true] at hr
  obtain ⟨-, hr⟩ := hr
  revert hr hc
  generalize wGenesis = g
  generalize tMint = t
  intro hc hr
  cases hm : checkMinting Xd.env g t with
  | error e => rw [hm] at hr; cases hr
  | ok pr =>
    obtain ⟨posts, rr⟩ := pr
    rw [hm] at hr
    exact (decide_eq_true_iff.mp hr) (h hc (minting_fold_one d hm) mintDenom).1

/-! ## §3 INTEGRITY (B3): the writer that rewrites the package slot -/

/-- The create re-derives from genesis (so the object's World is an honest fold, canonical), the
object is live with no package; the raw writer derives the write and the kernel admits it, and the
object's package after is not its package before. -/
theorem run_raw_write :
    (match rederiveLog Xd wGenesis oLog with
     | .ok w₁ => decide (w₁.height = 1) &&
      match rawReceive w₁ oWrite with
      | .ok tw =>
          match World.admit Xd.env w₁ tw with
          | .ok w₂ => decide (Xd.decodeCall tw.event = some oWrite) &&
              match w₁.live Xd.env oId, w₂.live Xd.env oId with
              | some cell, some cell' => decide (cell.kind = kindObject) &&
                  (match packageOf Xd oId cell with | .ok none => true | _ => false) &&
                  (match packageOf Xd oId cell' with | .ok (some _) => true | _ => false)
              | _, _ => false
          | .error _ => false
      | .error _ => false
     | .error _ => false) = true := by
  native_decide

/-- **FLOOR (B3).** The claim refuses the kernel whose `write` reaches the package slot: an audited
one-step log from a canonical World (the genesis World and the founder's create) moves the
object's package. -/
theorem floor_integrity_law (d : ByteArray → ByteArray) : ¬ Integrity.law (rawWriter d) := by
  intro h
  have hr := run_raw_write
  cases ho : rederiveLog Xd wGenesis oLog with
  | error e => rw [ho] at hr; cases hr
  | ok w₁ =>
  rw [ho] at hr
  dsimp only at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨-, hr⟩ := hr
  have hcan : CellsCanon Xd.env w₁ := by
    have hs := (rederiveLog_sound ho).1
    unfold wGenesis at hs
    exact fold_cellsCanon (genesis_cellsCanon Xd _ _ _ _ _) hs
  revert hr
  generalize oWrite = c
  generalize oId = obj
  intro hr
  cases htw : rawReceive w₁ c with
  | error e => rw [htw] at hr; cases hr
  | ok tw =>
    rw [htw] at hr
    dsimp only at hr
    cases ha : World.admit Xd.env w₁ tw with
    | error e => rw [ha] at hr; cases hr
    | ok w₂ =>
      rw [ha] at hr
      dsimp only at hr
      simp only [Bool.and_eq_true] at hr
      obtain ⟨hd, hr⟩ := hr
      cases hl : w₁.live Xd.env obj with
      | none => rw [hl] at hr; cases hr
      | some cell =>
        cases hl' : w₂.live Xd.env obj with
        | none => rw [hl, hl'] at hr; cases hr
        | some cell' =>
          rw [hl, hl'] at hr
          dsimp only at hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
          obtain ⟨⟨hk, hp₁⟩, hp₂⟩ := hr
          have hs : (rawWriter d).admit w₁ tw = .ok w₂ := ha
          have ha' : Audited (rawWriter d) w₁ [.turn tw] w₂ :=
            ⟨by simp only [System.fold, System.step, hs],
              ⟨c, decide_eq_true_eq.mp hd, htw, fun _ _ => trivial⟩⟩
          obtain ⟨-, ⟨cell'', hl'', hpk⟩, -⟩ :=
            h (obj := obj) (law := oneDigest) (p := pkg0) (fs := [("law", law0)]) (ℓ := "law") (t := law0)
              rfl (by simp [pkg0]) (by simp [Lang.Row.find?]) ⟨_, _, _, _, rfl⟩
              (by simp [law0, Lang.NoRef]) ha' hcan hl hk
          have hl₂ : w₂.live Xd.env obj = some cell'' := hl''
          have hpk' : packageOf Xd obj cell'' = packageOf Xd obj cell := hpk
          rw [hl'] at hl₂
          cases hl₂
          rw [hpk'] at hp₂
          revert hp₁ hp₂
          cases packageOf Xd obj cell with
          | error _ => intro h₁; cases h₁
          | ok o => cases o <;> intro h₁ h₂ <;> cases h₁ <;> cases h₂

/-! ## §4 CONSENT, inhabited: a command settled `ok`, a settlement final -/

theorem okDone_eq {r : Command.Reply} (h : okDone r = true) :
    ∃ o e, r = .done CommandExit.ok.code.toUInt8 o e := by
  cases r <;> simp_all [okDone]

/-- **The settled run**: follow, holding the World THE re-deriver reaches on the run's log, steps the
settle phase of the rotate that submitted it and ends `done ok`. -/
theorem run_settled :
    ((match Command.State.ofBytes wKbS with | some st => decide (st.phase = 4) | none => false) &&
      match rederiveLog Xd wGenesis wLog with
      | .ok w =>
          okDone ((deployed storeDigest).follow wMe ⟨w, none, none⟩ wKbS wRes).2.2
      | .error _ => false) = true := by
  native_decide

/-- **INHABITED (C(ii)).** The deployed follower ends a command `done ok` at the settle phase. -/
theorem inhabited_okCommitted :
    ∃ (me : Command.Self Digest) (f f' : Command.Follow Digest) (kb res o e : ByteArray)
      (p : Command.Persist Digest) (argv acc : List ByteArray),
      Command.State.ofBytes kb = some ⟨argv, 4, acc⟩ ∧
        (deployed storeDigest).follow me f kb res = (f', p, .done CommandExit.ok.code.toUInt8 o e) := by
  have hr := run_settled
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hk, hr⟩ := hr
  cases hs : Command.State.ofBytes wKbS with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    obtain ⟨argv, ph, acc⟩ := st
    have hph : ph = 4 := of_decide_eq_true hk
    subst hph
    cases hw : rederiveLog Xd wGenesis wLog with
    | error e => rw [hw] at hr; cases hr
    | ok w =>
      rw [hw] at hr
      dsimp only at hr
      revert hs hr
      generalize wKbS = kb
      generalize wRes = res
      intro hs hr
      cases hR : (deployed storeDigest).follow wMe ⟨w, none, none⟩ kb res with
      | mk f' rest =>
        obtain ⟨p, rp⟩ := rest
        rw [hR] at hr
        obtain ⟨o, e, hd⟩ := okDone_eq hr
        subst hd
        exact ⟨wMe, ⟨w, none, none⟩, f', kb, res, o, e, p, argv, acc, hs, hR⟩

/-- **The expired run**: the writer would admit `cExp` at the genesis World; after the run's one
step, follow settles it `expired`. -/
theorem run_expired :
    ((match submit Xd wGenesis cExp with | .ok _ => true | .error _ => false) &&
      match rederiveLog Xd wGenesis wLog with
      | .ok w => (match Command.settleOf Xd wMe w cExp with | .expired => true | _ => false)
      | .error _ => false) = true := by
  native_decide

/-- **INHABITED (C(iii)).** On a World an audited fold reaches, follow settles `expired` a call the
writer would have admitted at the fold's start: the claim's premise is reached by a call that was
not final before. -/
theorem inhabited_final (d : ByteArray → ByteArray) :
    ∃ (me : Command.Self Digest) (g : World Digest) (l : List (Step Digest)) (w : World Digest)
      (c : Call Digest) (out : Turn Digest × World Digest),
      Audited (deployed d) g l w ∧ (deployed d).submit g c = .ok out ∧
        w.RefusalsCanon Xd.env ∧ w.JournalCanon Xd.env ∧ (deployed d).settle me w c = .expired := by
  have hrc : wGenesis.RefusalsCanon Xd.env := by unfold wGenesis; exact genesisWorld_refusalsCanon Xd _ _ _ _ _
  have hjc : wGenesis.JournalCanon Xd.env := by unfold wGenesis; exact genesisWorld_journalCanon Xd _ _ _ _ _
  have hr := run_expired
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hs, hr⟩ := hr
  cases hsub : submit Xd wGenesis cExp with
  | error e => rw [hsub] at hs; cases hs
  | ok out =>
    cases hw : rederiveLog Xd wGenesis wLog with
    | error e => rw [hw] at hr; cases hr
    | ok w =>
      rw [hw] at hr
      dsimp only at hr
      have hfh := rederiveLog_sound hw
      cases hv : Command.settleOf Xd wMe w cExp
      all_goals rw [hv] at hr
      all_goals first | (cases hr; done) | skip
      revert hrc hjc hsub hfh hv
      generalize wGenesis = g
      generalize cExp = c
      generalize wLog = l
      intro hrc hjc hsub hfh hv
      exact ⟨wMe, g, l, w, c, out, audited_deployed.mpr hfh, hsub,
        fold_refusalsCanon hrc hfh.1, fold_journalCanon hjc hfh.1, hv⟩

/-! ## §4 CONSENT (cancel): the follower that says ok on the writer's word -/

/-- The continuation parses as `cancel` of the run's call, and at the genesis World follow does not
settle that call `refused cancelled`. -/
theorem run_cancel_state :
    ((match Command.State.ofBytes wKbC with
      | some st => (match Command.parse (D := Digest) Xd.digestOf st.argv with
          | .ok (.cancel cb) => decide (cb = wCb)
          | _ => false)
      | none => false) &&
      match Command.settleOf Xd wMe wGenesis wCall with
      | .refused code => decide (code ≠ Command.cancelledCode (D := Digest))
      | _ => true) = true := by
  native_decide

/-- **FLOOR (C(ii), cancel).** The claim refuses a follower that ends a cancel `ok` without settling
it on its own World (the pre-PROTOCOL-71 `cancelAnswer`): at the genesis World, the run's call is not
cancelled. -/
theorem floor_consent_cancelOk (d : ByteArray → ByteArray) : ¬ Consent.cancelOk (hostWord d) := by
  intro h
  have hr := run_cancel_state
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hk, hv⟩ := hr
  cases hs : Command.State.ofBytes wKbC with
  | none => rw [hs] at hk; cases hk
  | some st =>
    rw [hs] at hk
    dsimp only at hk
    cases hp : Command.parse (D := Digest) Xd.digestOf st.argv with
    | error e => rw [hp] at hk; cases hk
    | ok cmd =>
      rw [hp] at hk
      cases cmd
      all_goals dsimp only at hk
      all_goals first | (cases hk; done) | skip
      rename_i cb
      have hcb : cb = wCb := of_decide_eq_true hk
      subst hcb
      obtain ⟨c, hd, hset⟩ := h wMe ⟨wGenesis, none, none⟩ _ wKbC .empty .empty .empty _ st _ hs hp rfl
      have hd' : Xd.decodeCall wCb = some c := hd
      rw [run_call_decodes] at hd'
      cases hd'
      revert hset hv
      generalize wGenesis = g
      generalize wCall = c
      intro hv hset
      have hset' : Command.settleOf Xd wMe g c = .refused Command.cancelledCode := hset
      rw [hset'] at hv
      simp at hv

/-! ## §8 SHOWN, inhabited: a page served past a passing envelope -/

/-- The writer, at the genesis World, defers the founder's `log` frame (a page of the log). -/
theorem run_shown : (match Host.handle Xd wGenesis wFrame with | .defer _ => true | _ => false) = true := by
  native_decide

/-- **INHABITED (G2).** The deployed writer serves a page: the claim's premise is reached by a
frame whose envelope passes. -/
theorem inhabited_shown (d : ByteArray → ByteArray) :
    ∃ (w : World Digest) (f : Host.Frame) (dd : Host.Deferred), (deployed d).handle w f = .defer dd := by
  have hr := run_shown
  cases hh : Host.handle Xd wGenesis wFrame
  all_goals rw [hh] at hr
  all_goals first | (cases hr; done) | skip
  revert hh
  generalize wGenesis = g
  generalize wFrame = fr
  intro hh
  exact ⟨g, fr, _, hh⟩

/-! ## §3 INTEGRITY (B2), inhabited: value moved -/

/-- **The value run**: THE re-deriver accepts the three calls from genesis, and the account holds 10. -/
theorem run_value :
    (match rederiveLog Xd wGenesis vLog with
     | .ok w => decide (w.height = 3) &&
         match w.live Xd.env vAcct with
         | some cell => (Value.ofCell cell).map (·.balance) == some 10
         | none => false
     | .error _ => false) = true := by
  native_decide

/-- **INHABITED (B2).** An audited log from a genesis World moves value: at its end a value cell
holds a balance, though the genesis World holds no value cell (so another holds its negation). -/
theorem inhabited_value (d : ByteArray → ByteArray) :
    ∃ (g : World Digest) (l : List (Step Digest)) (w : World Digest) (id : Digest) (cell : Cell),
      Audited (deployed d) g l w ∧ w.live Xd.env id = some cell ∧ (Value.ofCell cell).map (·.balance) = some 10 := by
  have hr := run_value
  cases hw : rederiveLog Xd wGenesis vLog with
  | error e => rw [hw] at hr; cases hr
  | ok w =>
    rw [hw] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨-, hr⟩ := hr
    have hfh := rederiveLog_sound hw
    cases hl : w.live Xd.env vAcct with
    | none => rw [hl] at hr; cases hr
    | some cell =>
      rw [hl] at hr
      dsimp only at hr
      have hb : (Value.ofCell cell).map (·.balance) = some 10 := by simpa using hr
      revert hfh hl
      generalize wGenesis = g
      generalize vLog = l
      generalize vAcct = id
      intro hfh hl
      exact ⟨g, l, w, id, cell, audited_deployed.mpr hfh, hl, hb⟩

/-! ## §4 CONSENT (stale): the settlement that says stale on its own word -/

theorem run_plan :
    (match Command.plan Xd sMe wGenesis wKey {} (.issue 1000) with
     | .ok u => decide (u = sU)
     | .error _ => false) = true := by
  native_decide

/-- The genesis checks pass; the writer admits the planned call at the World it was planned on; and
no two of its pin inputs there collide. -/
theorem run_planned :
    ((match checkGenesis Xd "spec".toUTF8 "spec-0".toUTF8 100000000 [(wKey, nextKeyDigest Xd wNext)]
        Authority.none with | .ok () => true | .error _ => false) &&
      (match submit Xd wGenesis ⟨sU, Ed25519.sign (wSeed "f0") (Xd.callMessage sU)⟩ with
        | .ok _ => true | .error _ => false) &&
      collisionFree Xd.env.hash (Command.behindPres Xd.env wGenesis wGenesis sU)) = true := by
  native_decide

/-- **FLOOR (C(iii), stale).** The claim refuses a settlement that calls `refused stale` a call the
writer then admits: the founder's planned call, at the genesis World, on the empty extension. -/
theorem floor_consent_staleFinal (d : ByteArray → ByteArray) : ¬ Consent.staleFinal (staleOnWord d) := by
  intro h
  have hr := run_planned
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨hg, hs⟩, hc⟩ := hr
  have hfit : wGenesis.CellsFit Codec.Kernel.Cell.Fits Xd.env := by
    cases hgc : checkGenesis Xd "spec".toUTF8 "spec-0".toUTF8 100000000 [(wKey, nextKeyDigest Xd wNext)] Authority.none with
    | error e => rw [hgc] at hg; cases hg
    | ok u =>
      unfold wGenesis
      exact genesis_cellsFit (checkGenesis_ok.mp hgc) deployed_bytes_fit
  have hrc : wGenesis.RowsCanon Xd.env := by unfold wGenesis; exact receive_genesis_rowsCanon Xd _ _ _ _ _
  have hok : wGenesis.RowsOk Xd.env := by unfold wGenesis; exact receive_genesis_rowsOk Xd _ _ _ _ _
  have hrfc : wGenesis.RefusalsCanon Xd.env := by unfold wGenesis; exact genesisWorld_refusalsCanon Xd _ _ _ _ _
  have hjc : wGenesis.JournalCanon Xd.env := by unfold wGenesis; exact genesisWorld_journalCanon Xd _ _ _ _ _
  have hpb := run_plan
  have hrs : Command.signedReads Xd wGenesis (Command.Cmd.rotate (D := Digest)) = .ok {} := rfl
  revert hs hc hfit hrc hok hrfc hjc hpb hrs
  generalize Ed25519.sign (wSeed "f0") (Xd.callMessage sU) = sig
  generalize wGenesis = g
  generalize sMe = me
  generalize wKey = key
  generalize sU = u
  intro hc hs hfit hrc hok hrfc hjc hpb hrs
  cases hpl : Command.plan Xd me g key {} (.issue 1000) with
  | error e => rw [hpl] at hpb; cases hpb
  | ok u' =>
  rw [hpl] at hpb
  have hu : u = u' := (of_decide_eq_true hpb).symm
  subst hu
  have hp := hpl
  cases hsub : submit Xd g ⟨u, sig⟩ with
  | error e => rw [hsub] at hs; cases hs
  | ok out =>
    have hset : (staleOnWord d).settle me g ⟨u, sig⟩ = .refused staleCode := rfl
    rcases h me (l₁ := []) (l₂ := []) ⟨u, sig⟩ hfit hrc hok hrs hp rfl hrfc hjc rfl rfl hset with hn | hcol
    · exact hn out hsub
    · exact not_collides hc hcol



end Nanodregg.Spec
