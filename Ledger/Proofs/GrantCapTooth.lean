/-
# Ledger.Proofs.GrantCapTooth — without `LedgerContiguous`, a grant moves more than it had left

`grant_moves_le_cap` takes `LedgerContiguous` at the start of the log. This module shows it is the
premise the bound rests on: a World with canonical cells, holding a grant whose transfer ledger has
a gap (entries at `transferBase` and `transferBase + 4`, 10 left), audits a log of two signed
transfers of 10 through it (each re-derived from its decoded call by the REAL `receive` and admitted
by `World.admit`). Every other premise of the theorem holds; the two steps' amounts sum to 20 > 10;
the balances moved 20. KERNEL-30's `gap_never_falls` is the same fact at one cell; this is it along
an audited history.

The instance: one-byte digests (the hash of `b` is `64 + 8·b₀ + b₁`), every signature accepted, a
call's bytes its window end, a decoder that reads each of the two turns' events back as its call;
member 1 (key `42`) is the grantee, account `(3, 4)` holds 100 and is owned by 3, who issued grant 6
to 1 on it; account `(1, 4)` is empty. Hand-built, not reached from a genesis (it could not be:
`genesis_ledgerContiguous`). Everything is `decide +kernel`.
-/
import Ledger.Proofs.GrantCap
import Lang.Program

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Kernel Nanodregg.Kernel.Receive

private theorem of_isOk {ε α : Type} {x : Except ε α} {d : α} (h : x.isOk = true) : x = .ok (x.toOption.getD d) := by
  cases x with
  | ok a => rfl
  | error _ => cases h

private def isOkAs {ε α : Type} [DecidableEq α] : Except ε α → α → Bool
  | .ok b, a => decide (b = a)
  | .error _, _ => false

private theorem of_isOkAs {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : isOkAs x a = true) : x = .ok a := by
  cases x with
  | ok b => simp only [isOkAs, decide_eq_true_eq] at h; rw [h]
  | error _ => cases h

private def gEnv : Env UInt8 where
  hash _ b := 64 + 8 * b.data.getD 0 0 + b.data.getD 1 0
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def digestOf (b : ByteArray) : Option UInt8 := if b.size = 1 then some (b.data.getD 0 0) else none

/-- The `Ctx` the calls and turns are built in (no decoder: `receive` never decodes). -/
private def gX0 : Ctx UInt8 where
  env := gEnv
  unsignedBytes _ := ByteArray.empty
  callBytes c := ⟨#[UInt8.ofNat c.unsigned.validUntil]⟩
  decodeCall _ := none
  digestOf := digestOf
  verify _ _ _ := true
  program := Nanodregg.Lang.program gEnv.bytes digestOf

private def mem : UInt8 := 1
private def own : UInt8 := 3
private def asset : UInt8 := 4
private def gr : UInt8 := 6

private def memberCell : Cell := { kind := kindMember, discipline := .ram, slots := [(slotKey, ⟨#[42]⟩)] }

private def funded (owner : UInt8) (b : Int) : Cell :=
  let c := accountCell gX0 owner (gEnv.bytes asset) 0
  { c with slots := c.slots.set Value.balanceKey (Value.balanceBytes b) }

/-- The gapped grant: 3's grant to 1 on 3's account, its transfer ledger at `transferBase` and
`transferBase + 4`, 10 left. -/
private def gapGrant : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := slotsOf [(grantTarget, gEnv.bytes (accountId gX0 own asset)), (grantGrantee, gEnv.bytes mem),
      (grantIssuer, gEnv.bytes own), (transferBase, countBytes 10), (transferBase + 4, countBytes 10)] }

private def cells : List (UInt8 × Cell) :=
  [(mem, memberCell), (gr, gapGrant), (accountId gX0 own asset, funded own 100), (accountId gX0 mem asset, funded mem 0)]

private def w0 : World UInt8 :=
  { trie := cells.foldl (fun t p => t.insert (trieSpec gEnv) (.cell p.1) (.entry (.live p.2 0))) Trie.T.empty,
    journal := .empty, refusals := .empty, rows := .empty, height := 0, steps := 0,
    chain := 0, allowance := 1000000, origin := 0 }

private def pinsAt (w : World UInt8) : List (UInt8 × UInt8) := cells.map fun p => (p.1, pinOf gEnv (w.entry gEnv p.1))

/-- Member 1 moves 10 out of 3's account into its own, through grant 6, window `[1, vu]`. -/
private def callAt (w : World UInt8) (vu : Nat) : Call UInt8 :=
  { unsigned :=
      { world := 0, member := mem, key := ⟨#[42]⟩, notBefore := 1, validUntil := vu, pins := pinsAt w,
        maxCharge := 100000, body := .transfer (.of own asset) (.of mem asset) 10 (some gr) none }
    signature := .empty }

private def dummy : Turn UInt8 :=
  { txId := 0, notBefore := 0, validUntil := 0, touches := [], creates := [], nullifiers := [],
    charge := 0, event := .empty }

private def c1 : Call UInt8 := callAt w0 5
private def t1 : Turn UInt8 := ((receive gX0 w0 c1).toOption).getD dummy
private def w1 : World UInt8 := ((World.admit gEnv w0 t1).toOption).getD w0
private def c2 : Call UInt8 := callAt w1 6
private def t2 : Turn UInt8 := ((receive gX0 w1 c2).toOption).getD dummy
private def w2 : World UInt8 := ((World.admit gEnv w1 t2).toOption).getD w1

/-- The audit's `Ctx`: `gX0` with a decoder that reads each turn's event (its call's bytes, the
window end) back as its call. -/
private def gX : Ctx UInt8 :=
  { gX0 with decodeCall := fun b => if b = ⟨#[5]⟩ then some c1 else if b = ⟨#[6]⟩ then some c2 else none }

private theorem w0_canon : CellsCanon gX.env w0 := by
  intro id cell h
  have key : ((List.range 256).all fun n => match w0.live gEnv (UInt8.ofNat n) with
      | some c => Slots.ascending c.slots | none => true) = true := by decide +kernel
  have := List.all_eq_true.mp key id.toNat (List.mem_range.mpr id.toNat_lt)
  rw [UInt8.ofNat_toNat] at this
  change w0.live gEnv id = some cell at h
  rw [h] at this
  exact this

private theorem w0_audit : audit gX w0 [.turn t1, .turn t2] = .ok w2 := of_isOk (by decide +kernel)

private theorem step1 : auditStep gX w0 (.turn t1) = .ok w1 := by
  have hr : receive gX w0 c1 = .ok t1 := of_isOkAs (by decide +kernel)
  have ha : World.admit gX.env w0 t1 = .ok w1 := of_isOk (by decide +kernel)
  have hd : gX.decodeCall t1.event = some c1 := by decide +kernel
  exact auditTurn_ok.mpr ⟨⟨c1, hd, hr⟩, ha⟩

private theorem step2 : auditStep gX w1 (.turn t2) = .ok w2 := by
  have hr : receive gX w1 c2 = .ok t2 := of_isOkAs (by decide +kernel)
  have ha : World.admit gX.env w1 t2 = .ok w2 := of_isOk (by decide +kernel)
  have hd : gX.decodeCall t2.event = some c2 := by decide +kernel
  exact auditTurn_ok.mpr ⟨⟨c2, hd, hr⟩, ha⟩

private def steps : List (Step UInt8 × World UInt8) := [(.turn t1, w1), (.turn t2, w2)]

/-- **Tooth for `grant_moves_le_cap`: without `LedgerContiguous`, the bound fails.** Every other
premise holds: the cells are canonical, `g` is a live grant whose transfer ledger has `left` left,
and the log is audited (`audit X w l = .ok w'`, its turns re-derived from their decoded calls). Its
steps are the audit's own (a chain of `auditStep`s), and each dispatched a signed transfer of 10 through `g` (`MovesThrough`).
Yet the amounts sum past `left`: 20 moved against 10, as the balances show. The World is not
`LedgerContiguous` (the grant's ledger has a gap), and that alone is what fails. -/
theorem grant_cap_needs_contiguous :
    ∃ (X : Ctx UInt8) (g : UInt8) (w w' : World UInt8) (l : List (Step UInt8)) (cell : Cell) (i left : Nat)
      (stp : List (Step UInt8 × World UInt8)) (amt : World UInt8 × Step UInt8 × World UInt8 → Nat)
      (src dst : AcctRef UInt8),
      CellsCanon X.env w ∧ ¬ LedgerContiguous X.env w ∧
      w.live X.env g = some cell ∧ cell.kind = kindGrant ∧ ledgerLeft transferBase g cell = .ok (i, left) ∧
      audit X w l = .ok w' ∧ stp.map Prod.fst = l ∧
      Nanodregg.Lang.Std.Chain (fun s n o => auditStep X o s = .ok n) w stp ∧
      (∀ x ∈ (w :: stp.map Prod.snd).zip stp, MovesThrough X g x.1 x.2.1 (amt x)) ∧
      left < (((w :: stp.map Prod.snd).zip stp).map amt).sum ∧
      ((w.live X.env (src.resolve X)).bind Value.ofCell).map Value.balance = some 100 ∧
      ((w'.live X.env (src.resolve X)).bind Value.ofCell).map Value.balance = some 80 ∧
      ((w'.live X.env (dst.resolve X)).bind Value.ofCell).map Value.balance = some 20 := by
  refine ⟨gX, gr, w0, w2, [.turn t1, .turn t2], gapGrant, 2, 10, steps, fun _ => 10, .of own asset, .of mem asset,
    w0_canon, ?_, by decide +kernel, rfl, of_isOkAs (by decide +kernel), w0_audit, rfl,
    .cons step1 (.cons step2 (.nil w2)), ?_, by decide,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro h
    have := h gr gapGrant (by decide +kernel) rfl transferBase (.inr (.inl rfl))
    revert this
    decide +kernel
  · intro x hx
    simp only [steps, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨t1, c1, _, _, _, .of own asset, .of mem asset, none, rfl, by decide +kernel, Dispatched.root⟩
    · exact ⟨t2, c2, _, _, _, .of own asset, .of mem asset, none, rfl, by decide +kernel, Dispatched.root⟩

end Nanodregg.Ledger.Proofs
