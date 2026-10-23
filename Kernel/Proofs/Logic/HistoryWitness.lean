/-
# Kernel.Proofs.Logic.HistoryWitness — the run-level lift, on instances the kernel evaluates (KERNEL-28)

`Kernel.Proofs.Logic.History`'s theorems are not true of an empty premise:

* `object_history_chain_witnessed`: every premise of `object_history_chain` holds together, through
  `Lang.program`, on `Kernel.Proofs.InvokeWitness`'s signed invoke (counter object 5, `bump 4` from
  `n = 3`), with the counter's `NoRef` law `cap` in force; the lift's conclusion is a one-step chain.
* `write_history_witnessed`: a `write` step is inhabited: a member writes a data object (no package,
  no laws) on a toy `Ctx` running the language, derived and admitted, the state moving.
* `object_history_needs_inForce` (tooth): on that write history, whose one judged step no law
  judged, a `NoRef` law that admits nothing has no chain of the history's length from any state:
  without `object_history_chain`'s in-force premise its conclusion is false.

The toy `Env` is `Kernel.Proofs.Logic.Triple`'s (one-byte digests, the hash an input's first byte,
every signature accepted); the receivers, the seal, the admission and the language are the
deployed definitions.
-/
import Kernel.Proofs.Logic.History
import Kernel.Proofs.InvokeWitness

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- **The lift's premises hold together, and its conclusion is a one-step chain.** -/
theorem object_history_chain_witnessed :
    ∃ (X : Ctx UInt8) (obj p : UInt8) (w w' : World UInt8)
      (tr : List (Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8)))
      (pk : Lang.Package) (tl : Lang.Term) (cell : Cell) (o : Lang.Data) (steps : List (Lang.Data × Lang.Data)),
      X.Lawful ∧ X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧ ObjectHistory X obj w w' tr ∧
      (∀ e ∈ tr, p ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 p = .ok pk) ∧ Lang.NoRef tl ∧
      w.live X.env obj = some cell ∧ Lang.readState X.digestOf (Lang.recordRow pk.state) (stateOf cell) = .ok o ∧
      Lang.Std.Chain (Lang.Std.Step [] tl) o steps ∧ steps.length = 1 := by
  obtain ⟨X, w, w', c, t, obj, method, args, budget, via, cell, p, r, s, calls, rows, used, pk, fs, ℓ, tl,
    hX, hprog, hc, ha, hb, hr, hp, -, hpk, hbody, hℓ, hf, hlaw, hnr⟩ := invoke_lift_witnessed
  obtain ⟨laws, hlw, -⟩ := invoke_next_judged hc ha hb hr hp
  have h : ObjectHistory X obj w w' _ := .cons (.invoke hc ha hb hr hp hlw) (.nil w')
  have hin : ∀ e ∈ [(pinned X.env w c.unsigned.pins, some p, laws, r, stateOf cell, s, calls)],
      p ∈ e.2.1.toList ++ e.2.2.1 ∧ Lang.readPackage e.1 p = .ok pk := by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨by simp, hpk⟩
  obtain ⟨cell₀, o, hl, ho⟩ := object_history_start hX hprog h hin (by simp)
  obtain ⟨steps, hch, hmap⟩ := object_history_chain hX hprog hbody hℓ hf hlaw hnr h hin hl ho
  have hlen := congrArg List.length hmap
  simp only [List.length_map, Option.toList_some, List.singleton_append, List.length_cons, List.length_nil] at hlen
  exact ⟨X, obj, p, w, w', _, pk, tl, cell₀, o, steps, hX, hprog, h, hin, hnr, hl, ho, hch, hlen.symm⟩

/-! ## A write step -/

private def hEnv : Env UInt8 where
  hash _ b := b.data.getD 0 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def hDigestOf (b : ByteArray) : Option UInt8 := if b.size = 1 then some (b.data.getD 0 0) else none

/-- The toy `Ctx`, running the language at its own codec. -/
private def hCtx : Ctx UInt8 where
  env := hEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := ⟨#[UInt8.ofNat c.unsigned.validUntil]⟩
  decodeCall _ := none
  digestOf := hDigestOf
  verify _ _ _ := true
  program := Lang.program hEnv.bytes hDigestOf Lang.noReceipts

private def hMember : Cell := { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩)] }

/-- Data object 5: owner 7, no package, no laws, state key 16 holding `3`. -/
private def hObj : Cell :=
  { kind := kindObject, discipline := .ram, slots := [(slotOwner, ⟨#[7]⟩), (stateBase, ⟨#[3]⟩)] }

private def hW : World UInt8 :=
  { trie := (Trie.T.empty.insert (trieSpec hEnv) (.cell 5) (.entry (.live hObj 0))).insert (trieSpec hEnv)
      (.cell 7) (.entry (.live hMember 0)),
    journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

/-- Member 7 writes `4` at state key 16 of object 5, as its owner, pinning both. -/
private def hCall : Call UInt8 :=
  { unsigned :=
      { world := 0, member := 7, key := ⟨#[42]⟩, notBefore := 1, validUntil := 5,
        pins := [(5, pinOf hEnv (hW.entry hEnv 5)), (7, pinOf hEnv (hW.entry hEnv 7))], maxCharge := 100000,
        body := .write 5 [(0, some ⟨#[4]⟩)] none }
    signature := ByteArray.empty }

private def hDummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty }

private def hTurn : Turn UInt8 := ((receive hCtx hW hCall).toOption).getD hDummy
private def hAfter : World UInt8 := ((World.admit hEnv hW hTurn).toOption).getD hW

private theorem h_receive : receive hCtx hW hCall = .ok hTurn := by
  have h : (receive hCtx hW hCall).isOk = true := by decide +kernel
  unfold hTurn
  cases hf : receive hCtx hW hCall with
  | error e => rw [hf] at h; cases h
  | ok t => rfl

private theorem h_admit : World.admit hCtx.env hW hTurn = .ok hAfter := by
  have h : (World.admit hEnv hW hTurn).isOk = true := by decide +kernel
  show World.admit hEnv hW hTurn = .ok (((World.admit hEnv hW hTurn).toOption).getD hW)
  cases hf : World.admit hEnv hW hTurn with
  | error e => rw [hf] at h; cases h
  | ok w' => rfl

private theorem h_live : hW.live hCtx.env 5 = some hObj := by decide +kernel

private theorem h_history :
    ObjectHistory hCtx 5 hW hAfter [(pinned hCtx.env hW hCall.unsigned.pins, none, [],
      reqOf hCall.unsigned 5 7 .write, stateOf hObj, applyEdits (stateOf hObj) [(0, some ⟨#[4]⟩)], [])] :=
  .cons (.write h_receive h_admit rfl h_live (by decide) rfl rfl) (.nil hAfter)

/-- **A write step is inhabited**: a member's write of a data object, derived and admitted through
the language, is a one-step `ObjectHistory` whose judged step moves the state. -/
theorem write_history_witnessed :
    ∃ (X : Ctx UInt8) (obj : UInt8) (w w' : World UInt8)
      (tr : List (Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8))),
      X.Lawful ∧ X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧ ObjectHistory X obj w w' tr ∧
      ∃ e ∈ tr, e.2.2.2.2.2.1 ≠ e.2.2.2.2.1 :=
  ⟨hCtx, 5, hW, hAfter, _, ⟨fun _ => rfl⟩, rfl, h_history, _, List.mem_singleton_self _, by decide⟩

/-- **Tooth: the in-force premise is load-bearing.** On the write history above (lawful, running
the language, the object live, one judged step, judged by no law), a `NoRef` law of a law's shape
that refuses everything has no chain of the history's length from any state: `object_history_chain`
with its in-force premise dropped would conclude one. -/
theorem object_history_needs_inForce :
    ∃ (X : Ctx UInt8) (obj : UInt8) (w w' : World UInt8)
      (tr : List (Pinned UInt8 × Option UInt8 × List UInt8 × Req UInt8 × Slots × Slots × List (Body UInt8)))
      (cell : Cell) (tl : Lang.Term),
      X.Lawful ∧ X.program = Lang.program X.env.bytes X.digestOf Lang.noReceipts ∧ ObjectHistory X obj w w' tr ∧
      w.live X.env obj = some cell ∧ tr ≠ [] ∧ Lang.NoRef tl ∧ Lang.IsLaw tl ∧
      ∀ o, ¬ ∃ steps, Lang.Std.Chain (Lang.Std.Step [] tl) o steps ∧ steps.length = tr.length := by
  refine ⟨hCtx, 5, hW, hAfter, _, hObj,
    .lam (.record []) (.lam (.record []) (.lam (.record []) (.refuse (.record []) "no".toUTF8))),
    ⟨fun _ => rfl⟩, rfl, h_history, h_live, by simp, trivial, ⟨_, _, _, _, rfl⟩, ?_⟩
  rintro o ⟨steps, hch, hlen⟩
  cases hch with
  | nil => simp at hlen
  | cons hs _ =>
      obtain ⟨⟨cenv, w, hb⟩, -⟩ := hs
      cases hb

end Nanodregg.Kernel.Receive
