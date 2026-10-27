/-
# Spec.Proofs.Cap — B2's grant cap: a grant moves at most what it had left

TOPLEVEL-SPEC §3.2. **The claim** (`Integrity.grantCap`): along an audited log, for the log's own
chain of the system's steps (`System.Steps`), the transfers dispatched through a live grant sum to
at most what its transfer ledger had left at the start, and the credit lines extended through it to
at most what its credit ledger had left. A move is read off the call the step's event decodes to
(`MovesThrough`/`CreditsThrough`: the signed Body, or a call an object's run returned at any depth,
the walk of the call's own program), never off the system's `receive`, so a floor may swap it.

**Premises**, each needed:
* `Audited S w l w'`: the log is folded and every step is the system's own decision.
* `CellsCanon` and `LedgerContiguous` at the start: canonicity, true of every World a follower
  reaches (`genesis_cellsCanon`, `genesis_ledgerContiguous`, `honest_ledgerContiguous`). Without
  `LedgerContiguous` the bound fails (`Ledger.Proofs.GrantCapTooth.grant_cap_needs_contiguous`: a
  grant whose ledger has a gap moves 20 under a cap of 10).
* `g` live, a grant, and its ledger reading `left`: what is bounded.

**Top** `top_integrity_grantCap`: `grant_moves_le_cap`, `grant_credits_le_cap`
(`Ledger/Proofs/GrantCap.lean`) through `audited_deployed`; the system's chain is the lemma's
(`chain_eq`: the kernel's step is a function). **Floors** `floor_integrity_grantCap`,
`floor_integrity_grantCap_credit`: the capless kernel (`Spec.Sim.Cap.capless`), one per half: the
founder grants itself a cap of 10 on its well and moves (extends) 10 through it twice; both derive
and admit, and 20 > 10. **Inhabited** `inhabited_integrity_grantCap`: under the deployed kernel one
move of 10 through that grant admits, so the premise is reached with a positive amount.

Owed: nothing for the deployed system. The nested case of a move reads the kernel's walk of the
call's tree, so for a system with another `receive` only the moves that walk would dispatch are
counted (the floors need only the signed Body).
-/
import Spec.Proofs.Bridge
import Spec.Sim.Cap
import Ledger.Proofs.GrantCap
import Codec.Proofs.Digest

namespace Nanodregg.Spec

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Protocol Nanodregg.Codec
open Nanodregg.Ledger.Proofs (GrantStep MovesThrough CreditsThrough grant_moves_le_cap grant_credits_le_cap)

section
variable {D : Type} [Ord D] [DecidableEq D]

/-- One step of a log under the system's kernel, as a `Std.Chain` relation (`R rq n o`: from `o`,
step `rq` reaches `n`). -/
def System.Steps (S : System D) (s : Step D) (n o : World D) : Prop := S.step o s = .ok n

/-- **B2. Grant cap.** Along an audited log from a World whose cells are canonical and whose
grants' ledgers are contiguous, with `g` a live grant: for the log's own chain of steps, any choice
of one amount per step, each 0 or the amount of a transfer the step dispatched through `g`, sums to
at most what `g`'s transfer ledger had left at the start; and likewise credit lines on its credit
ledger. -/
def Integrity.grantCap (S : System D) : Prop :=
  ∀ {g : D} {w w' : World D} {l : List (Step D)} {cell : Cell},
    Audited S w l w' → CellsCanon S.X.env w → LedgerContiguous S.X.env w →
    w.live S.X.env g = some cell → cell.kind = kindGrant →
    ∀ {steps : List (Step D × World D)}, steps.map Prod.fst = l → Lang.Std.Chain S.Steps w steps →
      (∀ {i left : Nat}, ledgerLeft transferBase g cell = .ok (i, left) →
        ∀ amt : World D × Step D × World D → Nat,
          (∀ x ∈ (w :: steps.map Prod.snd).zip steps, amt x = 0 ∨ MovesThrough S.X g x.1 x.2.1 (amt x)) →
          (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ left) ∧
      (∀ {i left : Nat}, ledgerLeft creditBase g cell = .ok (i, left) →
        ∀ amt : World D × Step D × World D → Nat,
          (∀ x ∈ (w :: steps.map Prod.snd).zip steps, amt x = 0 ∨ CreditsThrough S.X g x.1 x.2.1 (amt x)) →
          (((w :: steps.map Prod.snd).zip steps).map amt).sum ≤ left)

end

/-- Two chains over one list of requests, the first's relation inside the second's and the second
functional, are one chain. -/
theorem chain_eq {Q St : Type} {R R' : Q → St → St → Prop} (hR : ∀ q n o, R q n o → R' q n o)
    (hfun : ∀ q n n' o, R' q n o → R' q n' o → n = n') :
    ∀ {o : St} {s₁ s₂ : List (Q × St)}, Lang.Std.Chain R o s₁ → Lang.Std.Chain R' o s₂ →
      s₁.map Prod.fst = s₂.map Prod.fst → s₁ = s₂
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, h => by simp at h
  | o, (q, n) :: r₁, (q', n') :: r₂, h₁, h₂, hm => by
      cases h₁ with
      | cons hs₁ hc₁ =>
      cases h₂ with
      | cons hs₂ hc₂ =>
      simp only [List.map_cons, List.cons.injEq] at hm
      obtain ⟨rfl, hm⟩ := hm
      have := hfun q n n' o (hR _ _ _ hs₁) hs₂
      subst this
      rw [chain_eq hR hfun hc₁ hc₂ hm]

theorem deployed_step (d : ByteArray → ByteArray) (o : World Digest) (s : Step Digest) :
    (deployed d).step o s = World.step Xd.env o s := by
  cases s <;> rfl

/-- **B2's grant cap, of the deployed system**: `grant_moves_le_cap`, `grant_credits_le_cap`. -/
theorem top_integrity_grantCap (d : ByteArray → ByteArray) : Integrity.grantCap (deployed d) := by
  intro g w w' l cell ha hcan hlc hl hk steps hmap hc
  rw [audited_deployed] at ha
  have hst : ∀ {steps' : List (Step Digest × World Digest)}, steps'.map Prod.fst = l →
      Lang.Std.Chain (GrantStep Xd g) w steps' → steps' = steps := fun hm' hc' =>
    chain_eq (R' := (deployed d).Steps)
      (fun q n o h => show (deployed d).step o q = .ok n from (deployed_step d o q).trans h.1.1)
      (fun _ _ _ _ h₁ h₂ => Except.ok.inj (h₁.symm.trans h₂)) hc' hc (hm'.trans hmap.symm)
  refine ⟨fun hleft amt hamt => ?_, fun hleft amt hamt => ?_⟩
  · obtain ⟨steps', hm', hc', hb⟩ := grant_moves_le_cap hcan hlc hl hk hleft ha.1 ha.2
    rw [hst hm' hc'] at hb
    exact hb amt hamt
  · obtain ⟨steps', hm', hc', hb⟩ := grant_credits_le_cap hcan hlc hl hk hleft ha.1 ha.2
    rw [hst hm' hc'] at hb
    exact hb amt hamt

/-! ## The floor: the kernel without the cap (`Spec.Sim.Cap.capless`) -/

theorem okThen_eq {ε α : Type} {r : Except ε α} {k : α → Bool} (h : okThen r k = true) :
    ∃ a, r = .ok a ∧ k a = true := by
  cases r with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem someThen_eq {α : Type} {r : Option α} {k : α → Bool} (h : someThen r k = true) :
    ∃ a, r = some a ∧ k a = true := by
  cases r with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- **The capless run**: THE re-deriver accepts issue, account and grant from genesis; the grant is
live with 10 left on its transfer ledger; the capless kernel derives and the kernel admits two moves
of 10 through it, each Turn's event decoding to its call. -/
theorem run_capless :
    okThen (rederiveLog Xd wGenesis gLog) (fun w₃ =>
      someThen (w₃.live Xd.env gId) (fun cell => decide (cell.kind = kindGrant) &&
        okThen (ledgerLeft transferBase gId cell) (fun p => decide (p.2 = 10))) &&
      okThen (caplessReceive w₃ gMove1) (fun t₁ => decide (Xd.decodeCall t₁.event = some gMove1) &&
        okThen (World.admit Xd.env w₃ t₁) (fun w₄ =>
          okThen (caplessReceive w₄ gMove2) (fun t₂ => decide (Xd.decodeCall t₂.event = some gMove2) &&
            okThen (World.admit Xd.env w₄ t₂) (fun _ => true))))) = true := by
  native_decide

/-- **The capless credit run**: as `run_capless`, with a grant of `credit 10` and two credit lines
of 10 through it. -/
theorem run_capless_credit :
    okThen (rederiveLog Xd wGenesis cLog) (fun w₃ =>
      someThen (w₃.live Xd.env cId) (fun cell => decide (cell.kind = kindGrant) &&
        okThen (ledgerLeft creditBase cId cell) (fun p => decide (p.2 = 10))) &&
      okThen (caplessReceive w₃ cLine1) (fun t₁ => decide (Xd.decodeCall t₁.event = some cLine1) &&
        okThen (World.admit Xd.env w₃ t₁) (fun w₄ =>
          okThen (caplessReceive w₄ cLine2) (fun t₂ => decide (Xd.decodeCall t₂.event = some cLine2) &&
            okThen (World.admit Xd.env w₄ t₂) (fun _ => true))))) = true := by
  native_decide

theorem cLine1_body : cLine1.unsigned.body = .credit vWell (.of wMember vWell) 10 (some cId) := rfl

theorem cLine2_body : cLine2.unsigned.body = .credit vWell (.of wMember vWell) 10 (some cId) := rfl

theorem gMove1_body : gMove1.unsigned.body = .transfer (.well vWell) (.of wMember vWell) 10 (some gId) none :=
  rfl

theorem gMove2_body : gMove2.unsigned.body = .transfer (.well vWell) (.of wMember vWell) 10 (some gId) none :=
  rfl

/-- What a capless run fact gives, at any log, grant, ledger and pair of calls: an audited two-step
log under the capless kernel from a World THE re-deriver reaches from genesis (so canonical and
contiguous), at which `g` is a live grant with 10 left on the ledger at `base`. -/
theorem capless_run (d : ByteArray → ByteArray) {log : List (Step Digest)} {g : Digest} {base : Nat}
    {c₁ c₂ : Call Digest}
    (hr : okThen (rederiveLog Xd wGenesis log) (fun w₃ =>
      someThen (w₃.live Xd.env g) (fun cell => decide (cell.kind = kindGrant) &&
        okThen (ledgerLeft base g cell) (fun p => decide (p.2 = 10))) &&
      okThen (caplessReceive w₃ c₁) (fun t₁ => decide (Xd.decodeCall t₁.event = some c₁) &&
        okThen (World.admit Xd.env w₃ t₁) (fun w₄ =>
          okThen (caplessReceive w₄ c₂) (fun t₂ => decide (Xd.decodeCall t₂.event = some c₂) &&
            okThen (World.admit Xd.env w₄ t₂) (fun _ => true))))) = true) :
    ∃ (w₃ w₄ w₅ : World Digest) (t₁ t₂ : Turn Digest) (cell : Cell) (i : Nat),
      Audited (capless d) w₃ [.turn t₁, .turn t₂] w₅ ∧ CellsCanon Xd.env w₃ ∧ LedgerContiguous Xd.env w₃ ∧
      w₃.live Xd.env g = some cell ∧ cell.kind = kindGrant ∧ ledgerLeft base g cell = .ok (i, 10) ∧
      Lang.Std.Chain (capless d).Steps w₃ [(.turn t₁, w₄), (.turn t₂, w₅)] ∧
      Xd.decodeCall t₁.event = some c₁ ∧ Xd.decodeCall t₂.event = some c₂ := by
  obtain ⟨w₃, ho, hr⟩ := okThen_eq hr
  have hcl : CellsCanon Xd.env w₃ ∧ LedgerContiguous Xd.env w₃ := by
    have hs := rederiveLog_sound ho
    unfold wGenesis at hs
    exact honest_ledgerContiguous (genesis_cellsCanon Xd _ _ _ _ _) (genesis_ledgerContiguous Xd _ _ _ _ _)
      hs.1 hs.2
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hg, hr⟩ := hr
  obtain ⟨cell, hl, hg⟩ := someThen_eq hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hk, hg⟩ := hg
  obtain ⟨⟨i, left⟩, hlf, hg⟩ := okThen_eq hg
  have h10 : left = 10 := of_decide_eq_true hg
  subst h10
  obtain ⟨t₁, ht₁, hr⟩ := okThen_eq hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hd₁, hr⟩ := hr
  obtain ⟨w₄, ha₁, hr⟩ := okThen_eq hr
  obtain ⟨t₂, ht₂, hr⟩ := okThen_eq hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hd₂, hr⟩ := hr
  obtain ⟨w₅, ha₂, -⟩ := okThen_eq hr
  have hd₁' : Xd.decodeCall t₁.event = some c₁ := of_decide_eq_true hd₁
  have hd₂' : Xd.decodeCall t₂.event = some c₂ := of_decide_eq_true hd₂
  have hs₁ : (capless d).admit w₃ t₁ = .ok w₄ := ha₁
  have hs₂ : (capless d).admit w₄ t₂ = .ok w₅ := ha₂
  refine ⟨w₃, w₄, w₅, t₁, t₂, cell, i, ⟨by simp only [System.fold, System.step, hs₁, hs₂],
      ⟨c₁, hd₁', ht₁, fun w' hw' => by
        rw [hs₁] at hw'
        cases hw'
        exact ⟨c₂, hd₂', ht₂, fun _ _ => trivial⟩⟩⟩, hcl.1, hcl.2, hl, hk, hlf,
    .cons (show (capless d).step w₃ (.turn t₁) = .ok w₄ from hs₁)
      (.cons (show (capless d).step w₄ (.turn t₂) = .ok w₅ from hs₂) (.nil _)), hd₁', hd₂'⟩

/-- Two steps each counted 10 sum to 20. -/
theorem two_tens {α : Type} (a : α) (x y : Step Digest × α) :
    (((a :: [x, y].map Prod.snd).zip [x, y]).map fun (_ : α × Step Digest × α) => 10).sum = 20 := rfl

theorem mem_two {α β : Type} {a b c : α} {x y : β} {p : α × β × α}
    (h : p ∈ (a :: [(x, b), (y, c)].map Prod.snd).zip [(x, b), (y, c)]) :
    p = (a, x, b) ∨ p = (b, y, c) := by
  simpa using h

/-- **FLOOR (B2, grant cap: transfers).** The claim refuses the kernel whose transfer does not spend
its grant's ledger: from the (canonical, contiguous) World after the founder's issue, account and
grant of `transfer 10` on its well, an audited two-step log moves 10 through the grant twice. -/
theorem floor_integrity_grantCap (d : ByteArray → ByteArray) : ¬ Integrity.grantCap (capless d) := by
  intro h
  have hb₁ := gMove1_body
  have hb₂ := gMove2_body
  have hr := capless_run d run_capless
  revert hb₁ hb₂ hr
  generalize gMove1 = c₁
  generalize gMove2 = c₂
  generalize vWell = vw
  generalize wMember = me
  generalize gId = g
  intro hb₁ hb₂ hr
  obtain ⟨w₃, w₄, w₅, t₁, t₂, cell, i, hau, hcan, hlc, hl, hk, hlf, hc, hd₁, hd₂⟩ := hr
  have hm₁ : MovesThrough Xd g w₃ (.turn t₁) 10 := by
    have hroot := Dispatched.root (X := Xd) (w := w₃) (c := c₁)
    rw [hb₁] at hroot
    exact ⟨t₁, c₁, _, _, _, _, _, _, rfl, hd₁, hroot⟩
  have hm₂ : MovesThrough Xd g w₄ (.turn t₂) 10 := by
    have hroot := Dispatched.root (X := Xd) (w := w₄) (c := c₂)
    rw [hb₂] at hroot
    exact ⟨t₂, c₂, _, _, _, _, _, _, rfl, hd₂, hroot⟩
  have hb := (h hau hcan hlc hl hk (steps := [(.turn t₁, w₄), (.turn t₂, w₅)]) rfl hc).1 hlf
    (fun _ => 10) fun x hx => by
      rcases mem_two hx with rfl | rfl
      · exact .inr hm₁
      · exact .inr hm₂
  rw [two_tens] at hb
  omega

/-- **FLOOR (B2, grant cap: credit lines).** The claim refuses the kernel whose credit line does not
spend its grant's ledger: after the founder's grant of `credit 10` on its well, an audited two-step
log extends 10 of credit through the grant twice. -/
theorem floor_integrity_grantCap_credit (d : ByteArray → ByteArray) : ¬ Integrity.grantCap (capless d) := by
  intro h
  have hb₁ := cLine1_body
  have hb₂ := cLine2_body
  have hr := capless_run d run_capless_credit
  revert hb₁ hb₂ hr
  generalize cLine1 = c₁
  generalize cLine2 = c₂
  generalize vWell = vw
  generalize wMember = me
  generalize cId = g
  intro hb₁ hb₂ hr
  obtain ⟨w₃, w₄, w₅, t₁, t₂, cell, i, hau, hcan, hlc, hl, hk, hlf, hc, hd₁, hd₂⟩ := hr
  have hm₁ : CreditsThrough Xd g w₃ (.turn t₁) 10 := by
    have hroot := Dispatched.root (X := Xd) (w := w₃) (c := c₁)
    rw [hb₁] at hroot
    exact ⟨t₁, c₁, _, _, _, _, _, rfl, hd₁, hroot⟩
  have hm₂ : CreditsThrough Xd g w₄ (.turn t₂) 10 := by
    have hroot := Dispatched.root (X := Xd) (w := w₄) (c := c₂)
    rw [hb₂] at hroot
    exact ⟨t₂, c₂, _, _, _, _, _, rfl, hd₂, hroot⟩
  have hb := (h hau hcan hlc hl hk (steps := [(.turn t₁, w₄), (.turn t₂, w₅)]) rfl hc).2 hlf
    (fun _ => 10) fun x hx => by
      rcases mem_two hx with rfl | rfl
      · exact .inr hm₁
      · exact .inr hm₂
  rw [two_tens] at hb
  omega


/-! ## Inhabited: one move of 10 through the grant, under the deployed kernel -/

/-- **The deployed move**: THE re-deriver accepts issue, account and grant from genesis; the grant
is live with 10 left on its transfer ledger; the kernel derives and admits one move of 10 through
it, the Turn's event decoding to its call. -/
theorem run_deployed_move :
    okThen (rederiveLog Xd wGenesis gLog) (fun w₃ =>
      someThen (w₃.live Xd.env gId) (fun cell => decide (cell.kind = kindGrant) &&
        okThen (ledgerLeft transferBase gId cell) (fun p => decide (p.2 = 10))) &&
      okThen (receive Xd w₃ gMove1) (fun t₁ => decide (Xd.decodeCall t₁.event = some gMove1) &&
        okThen (World.admit Xd.env w₃ t₁) (fun _ => true))) = true := by
  native_decide

/-- What `run_deployed_move`'s shape gives, at any log, grant and call. -/
theorem deployed_run_one (d : ByteArray → ByteArray) {log : List (Step Digest)} {g : Digest}
    {c₁ : Call Digest}
    (hr : okThen (rederiveLog Xd wGenesis log) (fun w₃ =>
      someThen (w₃.live Xd.env g) (fun cell => decide (cell.kind = kindGrant) &&
        okThen (ledgerLeft transferBase g cell) (fun p => decide (p.2 = 10))) &&
      okThen (receive Xd w₃ c₁) (fun t₁ => decide (Xd.decodeCall t₁.event = some c₁) &&
        okThen (World.admit Xd.env w₃ t₁) (fun _ => true))) = true) :
    ∃ (w₃ w₄ : World Digest) (t₁ : Turn Digest) (cell : Cell) (i : Nat),
      Audited (deployed d) w₃ [.turn t₁] w₄ ∧ CellsCanon Xd.env w₃ ∧ LedgerContiguous Xd.env w₃ ∧
      w₃.live Xd.env g = some cell ∧ cell.kind = kindGrant ∧ ledgerLeft transferBase g cell = .ok (i, 10) ∧
      Lang.Std.Chain (deployed d).Steps w₃ [(.turn t₁, w₄)] ∧ Xd.decodeCall t₁.event = some c₁ := by
  obtain ⟨w₃, ho, hr⟩ := okThen_eq hr
  have hcl : CellsCanon Xd.env w₃ ∧ LedgerContiguous Xd.env w₃ := by
    have hs := rederiveLog_sound ho
    unfold wGenesis at hs
    exact honest_ledgerContiguous (genesis_cellsCanon Xd _ _ _ _ _) (genesis_ledgerContiguous Xd _ _ _ _ _)
      hs.1 hs.2
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hg, hr⟩ := hr
  obtain ⟨cell, hl, hg⟩ := someThen_eq hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hk, hg⟩ := hg
  obtain ⟨⟨i, left⟩, hlf, hg⟩ := okThen_eq hg
  have h10 : left = 10 := of_decide_eq_true hg
  subst h10
  obtain ⟨t₁, ht₁, hr⟩ := okThen_eq hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨hd₁, hr⟩ := hr
  obtain ⟨w₄, ha₁, -⟩ := okThen_eq hr
  have hd₁' : Xd.decodeCall t₁.event = some c₁ := of_decide_eq_true hd₁
  have hs₁ : (deployed d).admit w₃ t₁ = .ok w₄ := ha₁
  refine ⟨w₃, w₄, t₁, cell, i, ⟨by simp only [System.fold, System.step, hs₁],
      ⟨c₁, hd₁', ht₁, fun _ _ => trivial⟩⟩, hcl.1, hcl.2, hl, hk, hlf,
    .cons (show (deployed d).step w₃ (.turn t₁) = .ok w₄ from hs₁) (.nil _), hd₁'⟩

/-- **INHABITED (B2, grant cap).** The deployed system reaches the claim's premise with a positive
amount: an audited log, from a canonical and contiguous World holding a live grant with 10 left on
its transfer ledger, whose one step moves 10 through it. -/
theorem inhabited_integrity_grantCap (d : ByteArray → ByteArray) :
    ∃ (g : Digest) (w w' : World Digest) (l : List (Step Digest)) (cell : Cell) (i : Nat)
      (steps : List (Step Digest × World Digest)),
      Audited (deployed d) w l w' ∧ CellsCanon Xd.env w ∧ LedgerContiguous Xd.env w ∧
      w.live Xd.env g = some cell ∧ cell.kind = kindGrant ∧ ledgerLeft transferBase g cell = .ok (i, 10) ∧
      steps.map Prod.fst = l ∧ Lang.Std.Chain (deployed d).Steps w steps ∧
      ∃ x ∈ (w :: steps.map Prod.snd).zip steps, MovesThrough Xd g x.1 x.2.1 10 := by
  have hb₁ := gMove1_body
  have hr := deployed_run_one d run_deployed_move
  revert hb₁ hr
  generalize gMove1 = c₁
  generalize vWell = vw
  generalize wMember = me
  generalize gId = g
  intro hb₁ hr
  obtain ⟨w₃, w₄, t₁, cell, i, hau, hcan, hlc, hl, hk, hlf, hc, hd₁⟩ := hr
  have hroot := Dispatched.root (X := Xd) (w := w₃) (c := c₁)
  rw [hb₁] at hroot
  exact ⟨g, w₃, w₄, [.turn t₁], cell, i, [(.turn t₁, w₄)], hau, hcan, hlc, hl, hk, hlf, rfl, hc,
    (w₃, .turn t₁, w₄), by simp, ⟨t₁, c₁, _, _, _, _, _, _, rfl, hd₁, hroot⟩⟩

end Nanodregg.Spec
