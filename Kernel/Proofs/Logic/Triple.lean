/-
# Kernel.Proofs.Logic.Triple — the receivers' contract and the call-level frame (KERNEL-58, Q1)

A receiver never sees the World: it sees `Pinned D`, which answers for the ids the caller pinned
and refuses `unpinned` for any other (`Kernel/Receive/Call.lean`). Locality is the receivers' type,
so no assertion language is built here; this module names what is already true and adds the one
rule a CALL lacked.

- `Derived X c t` (`Kernel.Proofs.Receive`) is the contract every derived Turn keeps with its call;
  `receive_derived` proves it. `submit_derived` is the same fact as a triple.
- `Triple X P c Q`: every run of `c` from a `P`-World that `receive` derives and `World.admit`
  admits lands in `Q`. It is a definition over the two functions, not a second semantics.
- `CallFoot X c w`: what a call may write at the World it is derived against, read off the call
  and that World only: the cells it pinned (every touch is a pin, `Derived.pinned`), an id the World
  has not taken (a birth: `checkCreates` refuses a taken one), a nullifier the World has not spent
  (`checkNullifiers`). `callFoot_of_turn`: the derived Turn's footprint (`CellFoot`) lies inside it.
- `Indep X c R`: `R` survives any change confined to the call's footprint. `submit_frame` is the
  frame rule: `{P} c {Q}` and `Indep X c R` give `{P ∧ R} c {Q ∧ R}`. Cells only; a rows or journal
  frame takes its trie's canonicity inside the field, as `Frame` does.
- `not_callFoot_live`: at a live cell the footprint is exactly "pinned", so `indep_live` (an
  unpinned live cell is kept) is, for a call-derived Turn at a LIVE object, what `ObjectStep.other`'s
  two turn-level hypotheses (no touch, not born) say (`Kernel.Proofs.Logic.History`; its `frame`
  step is this footprint form): liveness stands in for "not born".
- What it does not frame: a `keep` pin is inside (`CellFoot` leaves it out), and every untaken id
  and unspent nullifier is inside, so an assertion about an absent id or an unspent nullifier is
  never `Indep` of any call. Sound, and exact where it is used: a live object no pin names.

Teeth (on a toy `Ctx`: every signature verifies, the hash is its input's first byte; the receivers,
the seal and the admission are the deployed definitions): `callFoot_needs_born` (a `create` writes a
cell it never pinned), `submit_frame_needs_indep` (a `rotate` writes the member it pinned: the frame
without `Indep` is false), `derived_needs_receive` (an admitted Turn need not be `Derived` of a
call: an admitted Turn with an empty event is `Derived` of no call at all).
-/
import Kernel.Proofs.Receive
import Kernel.Proofs.Frame

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- **What a call may write** at the World `w` it is derived against: a cell it pinned, an id `w`
has not taken (live or tombstoned), a nullifier `w` has not spent. -/
inductive CallFoot (X : Ctx D) (c : Call D) (w : World D) : Slot D → Prop
  | pinned {p : D × D} (hp : p ∈ c.unsigned.pins) : CallFoot X c w (.cell p.1)
  | born {i : D} (hi : w.taken X.env i = false) : CallFoot X c w (.cell i)
  | spent {n : D} (hn : w.isSpent X.env n = false) : CallFoot X c w (.nullifier n)

/-- `{P} c {Q}`: every run of `c` from a `P`-World that `receive` derives and `World.admit` admits
lands in `Q` (of the World before, the Turn, the World after). -/
def Triple (X : Ctx D) (P : World D → Prop) (c : Call D) (Q : World D → Turn D → World D → Prop) : Prop :=
  ∀ w t w', P w → receive X w c = .ok t → World.admit X.env w t = .ok w' → Q w t w'

/-- `R` reads nothing a run of `c` may write: any World agreeing with a `R`-World `w` outside the
call's footprint at `w` is an `R`-World. -/
def Indep (X : Ctx D) (c : Call D) (R : World D → Prop) : Prop :=
  ∀ w w', (∀ s, ¬ CallFoot X c w s → w'.trie.get (trieSpec X.env) s = w.trie.get (trieSpec X.env) s) →
    R w → R w'

/-- **The contract, as a triple.** From any World, a derived and admitted run's Turn is `Derived`
of its call. -/
theorem submit_derived {X : Ctx D} {c : Call D} : Triple X (fun _ => True) c (fun _ t _ => Derived X c t) :=
  fun _ _ _ _ hr _ => receive_derived hr

/-- **The Turn's footprint is inside the call's.** A touch is a pin, a birth is an id the World had
not taken, a spent nullifier was unspent. -/
theorem callFoot_of_turn {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') {s : Slot D}
    (h : CellFoot t s) : CallFoot X c w s := by
  cases h with
  | @touched x hx _ =>
      have hp : (x.cell, x.seen) ∈ c.unsigned.pins := by
        rw [← (receive_derived hr).pinned]
        exact List.mem_map_of_mem hx
      exact .pinned hp
  | @born i hi =>
      refine .born ?_
      obtain ⟨posts, hk, -⟩ := admit_ok ha
      have hcr := hk.creates
      unfold checkCreates at hcr
      simp only [except_bind_ok] at hcr
      obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hf⟩ := hcr
      have := (forEx_ok.mp hf) i hi
      rw [req_ok] at this
      simpa using this
  | @spent n hn => exact .spent ((admit_nullifiers ha).1 n hn).1

/-- **The call-level frame, as reads.** Outside the call's footprint every cells-trie slot reads as
before; no premise beyond the run. -/
theorem call_frame {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') :
    ∀ s, ¬ CallFoot X c w s → w'.trie.get (trieSpec X.env) s = w.trie.get (trieSpec X.env) s :=
  fun s hs => (admit_Frame ha).cells s fun hf => hs (callFoot_of_turn hr ha hf)

/-- **The frame rule.** An assertion independent of a call's footprint rides along any triple of
that call. -/
theorem submit_frame {X : Ctx D} {c : Call D} {P R : World D → Prop}
    {Q : World D → Turn D → World D → Prop} (h : Triple X P c Q) (hR : Indep X c R) :
    Triple X (fun w => P w ∧ R w) c (fun w t w' => Q w t w' ∧ R w') :=
  fun w t w' hpr hr ha => ⟨h w t w' hpr.1 hr ha, hR w w' (call_frame hr ha) hpr.2⟩

/-- **At a live cell the footprint is the pins.** A live cell is taken, so it is never born: it is
outside the call's footprint exactly when no pin names it. -/
theorem not_callFoot_live {X : Ctx D} {w : World D} {c : Call D} {obj : D} {cell : Cell}
    (hl : w.live X.env obj = some cell) :
    ¬ CallFoot X c w (.cell obj) ↔ ∀ p ∈ c.unsigned.pins, p.1 ≠ obj := by
  constructor
  · intro h p hp hpo
    exact h (hpo ▸ .pinned hp)
  · intro h hf
    cases hf with
    | pinned hp => exact h _ hp rfl
    | born hi => rw [live_taken hl] at hi; cases hi

/-- **An unpinned live cell is kept by the call**: the assertion "`obj` is live and holds `cell`" is
independent of every call that does not pin `obj`. -/
theorem indep_live {X : Ctx D} {c : Call D} {obj : D} {cell : Cell}
    (hobj : ∀ p ∈ c.unsigned.pins, p.1 ≠ obj) : Indep X c (fun w => w.live X.env obj = some cell) := by
  intro w w' hf hl
  have he := hf (.cell obj) ((not_callFoot_live hl).mpr hobj)
  unfold World.live World.entry at hl ⊢
  rw [he]; exact hl

/-! ## Teeth -/

private def tEnv : Env UInt8 where
  hash _ b := b.data.getD 0 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

/-- Every signature verifies; a call's bytes are its window end; the program judges everything
`ok` and runs nothing (no tooth here runs a method). -/
private def tCtx : Ctx UInt8 where
  env := tEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := ⟨#[UInt8.ofNat c.unsigned.validUntil]⟩
  decodeCall _ := none
  digestOf b := if b.size = 1 then some (b.data.getD 0 0) else none
  verify _ _ _ := true
  program :=
    { checkInstall := fun _ _ => .ok ()
      judge := fun _ _ _ _ _ _ => .ok ()
      run := fun _ _ _ _ _ _ _ _ => .error (.program "none")
      rels := fun _ _ _ => .ok [] }

/-- Member 7: current key `42`, precommitted next key `43` (whose toy digest is `43`). -/
private def tMember : Cell :=
  { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩), (slotNext, ⟨#[43]⟩)] }

private def tW : World UInt8 :=
  { trie := Trie.T.empty.insert (trieSpec tEnv) (.cell 7) (.entry (.live tMember 0)),
    journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

/-- Member 7, pinning itself, window `[1, vu]`, signs `body` with `key`. -/
private def tCall (key : ByteArray) (vu : Nat) (body : Body UInt8) : Call UInt8 :=
  { unsigned :=
      { world := 0, member := 7, key, notBefore := 1, validUntil := vu,
        pins := [(7, pinOf tEnv (tW.entry tEnv 7))], maxCharge := 100000, body }
    signature := ByteArray.empty }

/-- Rotate to key `43`, precommitting `50`: writes the pinned member. -/
private def cRot : Call UInt8 := tCall ⟨#[43]⟩ 6 (.rotate ⟨#[43]⟩ 50)
/-- Create a data object with no state: bears it at `cellIdOf tx 0`, which is `5` here, unpinned. -/
private def cNew : Call UInt8 := tCall ⟨#[42]⟩ 5 (.create none [] [])

private def tDummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty, member := 0 }

private def tTurn (c : Call UInt8) : Turn UInt8 := ((receive tCtx tW c).toOption).getD tDummy
private def tAfter (c : Call UInt8) : World UInt8 := ((World.admit tEnv tW (tTurn c)).toOption).getD tW

private theorem t_receive {c : Call UInt8} (h : (receive tCtx tW c).isOk = true) :
    receive tCtx tW c = .ok (tTurn c) := by
  unfold tTurn
  cases hf : receive tCtx tW c with
  | error e => rw [hf] at h; cases h
  | ok t => rfl

private theorem t_admit {c : Call UInt8} (h : (World.admit tEnv tW (tTurn c)).isOk = true) :
    World.admit tCtx.env tW (tTurn c) = .ok (tAfter c) := by
  show World.admit tEnv tW (tTurn c) = .ok (((World.admit tEnv tW (tTurn c)).toOption).getD tW)
  cases hf : World.admit tEnv tW (tTurn c) with
  | error e => rw [hf] at h; cases h
  | ok w' => rfl

private theorem rot_receive : receive tCtx tW cRot = .ok (tTurn cRot) := t_receive (by decide +kernel)
private theorem rot_admit : World.admit tCtx.env tW (tTurn cRot) = .ok (tAfter cRot) := t_admit (by decide +kernel)
private theorem new_receive : receive tCtx tW cNew = .ok (tTurn cNew) := t_receive (by decide +kernel)
private theorem new_admit : World.admit tCtx.env tW (tTurn cNew) = .ok (tAfter cNew) := t_admit (by decide +kernel)

/-- **Tooth: `born` is in the call's footprint.** A `create` derived and admitted from a World
holding only its signer writes a cell no pin names and no nullifier is: the frame over the pins
and the unspent nullifiers alone is false for it. -/
theorem callFoot_needs_born :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (c : Call UInt8) (t : Turn UInt8),
      receive X w c = .ok t ∧ World.admit X.env w t = .ok w' ∧
      ¬ ∀ s, (∀ p ∈ c.unsigned.pins, s ≠ .cell p.1) → (∀ n, w.isSpent X.env n = false → s ≠ .nullifier n) →
        w'.trie.get (trieSpec X.env) s = w.trie.get (trieSpec X.env) s := by
  refine ⟨tCtx, tW, tAfter cNew, cNew, tTurn cNew, new_receive, new_admit, fun hall => ?_⟩
  have h := hall (.cell 5) (by decide) (fun _ _ h => by cases h)
  revert h
  decide +kernel

/-- **Tooth: the frame rule needs `Indep`.** A `rotate` derived and admitted writes the member it
pinned, so "member 7 holds `tMember`" holds before and not after: without `Indep` the frame of
`{True} c {True}` is false, and the assertion is not independent of the call. -/
theorem submit_frame_needs_indep :
    Triple tCtx (fun _ => True) cRot (fun _ _ _ => True) ∧
      ¬ Triple tCtx (fun w => True ∧ w.live tEnv 7 = some tMember) cRot
          (fun _ _ w' => True ∧ w'.live tEnv 7 = some tMember) ∧
      ¬ Indep tCtx cRot (fun w => w.live tEnv 7 = some tMember) := by
  have hlive : tW.live tEnv 7 = some tMember := by decide +kernel
  have hafter : (tAfter cRot).live tEnv 7 ≠ some tMember := by decide +kernel
  refine ⟨fun _ _ _ _ _ _ => trivial, fun h => hafter (h tW _ _ ⟨trivial, hlive⟩ rot_receive rot_admit).2,
    fun hi => hafter (hi tW _ (call_frame rot_receive rot_admit) hlive)⟩

/-- The `create`'s Turn with its event emptied and its charge re-priced: still admitted. -/
private def tBare : Turn UInt8 :=
  let t0 : Turn UInt8 := { tTurn cNew with event := .empty, charge := 0 }
  { t0 with charge := t0.weight }

/-- **Tooth: the contract is `receive`'s, not admission's.** `World.admit` takes a Turn whose event
is empty, and that Turn is `Derived` of NO call (every call's bytes here are one byte long). -/
theorem derived_needs_receive :
    ∃ (X : Ctx UInt8) (w w' : World UInt8) (t : Turn UInt8),
      World.admit X.env w t = .ok w' ∧ ∀ c, ¬ Derived X c t := by
  have h : (World.admit tEnv tW tBare).isOk = true := by decide +kernel
  cases hf : World.admit tEnv tW tBare with
  | error e => rw [hf] at h; cases h
  | ok w' =>
      refine ⟨tCtx, tW, w', tBare, hf, fun c hd => ?_⟩
      have hs := congrArg ByteArray.size hd.event
      have h0 : tBare.event.size = 0 := rfl
      have h1 : (tCtx.callBytes c).size = 1 := rfl
      omega

end Nanodregg.Kernel.Receive
