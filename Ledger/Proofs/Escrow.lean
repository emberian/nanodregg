/-
# Ledger.Proofs.Escrow — what the escrow's law admits, and that it pays out at most once

The law theorems read an ADMITTED law (`Std.Admits`: its body means `ok` over the reference
semantics, for ANY old state, new state and request as data) back to facts about the phases and
the signer, compositionally from LANG's inversion lemmas (`Lang.Proofs.Std`); the receiver's run of
the package field produces exactly `Admits` (`Std.runLaw_ref_admits`).

* `escrow_invoke`: an admitted invoke is method 0 `open → held` signed by the depositor, or 1
  `held → refunded` by the beneficiary or the arbiter, or 2 `held → released` by the depositor or
  the arbiter. `escrow_start`: a birth or adoption is at `open`. `escrow_frozen`: no write, no
  law change.
* `escrow_absorbing`: from `released` or `refunded` nothing is admitted.
* `escrow_law_payout_once`: along ANY chain of law-admitted acts, from any state, at most one is a
  payout (an invoke of method 1 or 2).
* `escrow_method_results`: what each method returns, whole (`methodResult`: the receiver's method
  application `apply4 0 ℓ` under `[escrow.body]`, extracted at its result type), for every value
  of every term (amount, parties, asset, the object itself, the grant, the phase) and of every
  other request field and the rows: 1 and 2 transfer `amount` out of `of self asset` through no
  grant (`none`) spending `"payout"`; 0 transfers into it through the grant, spending the creator's
  `nonce`; each carries the terms unchanged and sets its target phase. What the RECEIVER's run
  extracts is this result (`Ledger.Proofs.EscrowRun.escrow_run_calls`).
  `escrow_slots`: each method's signature has exactly one call slot, a transfer.
* the package's statement, over the receiver's own runs, is `escrow_runs_one_payout`
  (Ledger.Proofs.EscrowRun): along any sequence of runs the receiver commits, at most one payout;
  `Ledger.Proofs.EscrowWitness` meets its premise and reaches the bound by kernel evaluation.
  `escrow_deposit_first`: from `open`, a deposit comes before any payout. The kernel's own guard
  behind it is `Kernel.Proofs.Ledger.transfer_once` on the ONE nullifier `onceNullifier
  (accountId e asset) "payout"`, which both payouts spend (LEDGER-6 (d)).
* `escrow_admits`: a birth, a deposit, a refund and a release are each admitted (so no law theorem
  holds by an empty premise). `escrow_judge_admits`: the receiver's `runLaw` of the loaded body's
  field `escrow` gives `Admits … law`.
* `escrow_verdicts`: the refusal NAMES, by `runLaw` (the receiver's runner, `lawTicks`), for every
  phase pair, method and signer role, at representative distinct party bytes: what `lawDenied`
  carries on the wire.
* `escrow_text_reads`: `world/escrow/Escrow` (`Print.package escrow`) reads back as the package;
  `escrow_decodes`: its install bytes decode to it.

Not proved here, and why (the gaps at Deployed, each named):
* that between two invokes a programmed object's state changes only by its methods is KERNEL's
  (`hasMethods`); the chain theorems do not need it, since the law refuses writes and relaws itself;
* the verdict NAMES are an instance (parties distinct, amount 5); the admitted/refused facts are
  general (`escrow_invoke` …).
-/
import Ledger.Escrow
import Lang.Print
import Lang.Read
import Lang.Eval
import Lang.Proofs.Std
import Lang.Proofs.Print
import Lang.Proofs.Wire
import Ledger.EscrowSpec

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang
open Nanodregg.Lang.Std (At Admits LawEnv)
open Nanodregg.Ledger.Escrow

variable {lib : List Term}

/-! ## Facts about data -/

/-- The phase field of `d` is `p`. -/
def PhaseIs (d : Data) (p : Label) : Prop := ∃ y, d.field "phase" = some (.inj p y)

/-- The request's signer is party `f` of state `o`. -/
def Signs (rq o : Data) (f : Label) : Prop :=
  ∃ s, rq.field "agent" = some (.digest s) ∧ o.field f = some (.digest s)

def Settled (d : Data) : Prop := PhaseIs d "released" ∨ PhaseIs d "refunded"

theorem phase_unique {d : Data} {p q : Label} (hp : PhaseIs d p) (hq : PhaseIs d q) : p = q := by
  obtain ⟨y, hy⟩ := hp
  obtain ⟨z, hz⟩ := hq
  rw [hy] at hz
  injection hz with h; injection h

theorem find_mem {α : Type} {ℓ : Label} {b : α} :
    ∀ {row : List (Label × α)}, Row.find? ℓ row = some b → ℓ ∈ row.map Prod.fst
  | [], h => by simp [Row.find?] at h
  | (k, a) :: rest, h => by
    simp only [Row.find?] at h
    split at h
    · rename_i hk; subst hk; simp
    · exact List.mem_cons_of_mem _ (find_mem h)

/-! ## The clauses -/

private theorem methodIs_true {x : Data} {E : Env} {m : Nat}
    (h : BigStep lib (x.toVal :: E) (methodIs ⟨1⟩ m) (.ok (.bool true))) : x = .nat m := by
  obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok h
  obtain ⟨k, k', rfl, rfl, hd⟩ := Std.primEval_eq_bool hp
  cases bigStep_nat_inv hv
  simp at hd; subst hd
  have hx := bigStep_var_ok hu
  simp at hx
  exact Data.toVal_nat hx

private theorem clause_ok {x rq n o : Data} {E : Env} {src dst : Label} {why : String}
    {who : List Label} {w : Val}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E) (methodClause ⟨1⟩ src why who dst) (.ok (.inj "ok" w))) :
    PhaseIs o src ∧ PhaseIs n dst ∧ ∃ f ∈ who, Signs rq o f := by
  have hl := Std.allOf_ok h
  have h1 := hl (isPh ((⟨1⟩ : At).oldF "phase") src, why) (by simp)
  have h2 := hl (Std.anyOf (who.map (agentIs ⟨1⟩)), "notParty") (by simp)
  have h3 := hl (isPh ((⟨1⟩ : At).newF "phase") dst, "badPhase") (by simp)
  refine ⟨Std.isState_true (d := o) (i := 3) rfl h1, Std.isState_true (d := n) (i := 2) rfl h3, ?_⟩
  obtain ⟨c, hc, hct⟩ := Std.anyOf_true h2
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
  exact ⟨f, hf, Std.deq_fields (d := rq) (e := o) (i := 1) (j := 3) rfl rfl hct⟩

/-! ## The law -/

/-- **An admitted invoke is one of the three edges, signed by a party it names.** -/
theorem escrow_invoke {rq n o x : Data} (h : Admits lib law rq n o)
    (ho : rq.field "occasion" = some (.inj "invoke" x)) :
    (x = .nat deposit ∧ PhaseIs o "open" ∧ PhaseIs n "held" ∧ Signs rq o "depositor") ∨
    (x = .nat refund ∧ PhaseIs o "held" ∧ PhaseIs n "refunded" ∧
      (Signs rq o "beneficiary" ∨ Signs rq o "arbiter")) ∨
    (x = .nat release ∧ PhaseIs o "held" ∧ PhaseIs n "released" ∧
      (Signs rq o "depositor" ∨ Signs rq o "arbiter")) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [law, Std.lawOf5, Std.lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := Std.lawCase5_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  obtain ⟨_, hrest⟩ := Std.guard_ok hbody
  rcases bigStep_ite_ok hrest with ⟨h0, hr⟩ | ⟨_, hr⟩
  · obtain ⟨a, b, f, hf, hs⟩ := clause_ok hr
    simp at hf; subst hf
    exact .inl ⟨methodIs_true h0, a, b, hs⟩
  rcases bigStep_ite_ok hr with ⟨h1, hr⟩ | ⟨_, hr⟩
  · obtain ⟨a, b, f, hf, hs⟩ := clause_ok hr
    refine .inr (.inl ⟨methodIs_true h1, a, b, ?_⟩)
    simp at hf; rcases hf with rfl | rfl
    · exact .inl hs
    · exact .inr hs
  rcases bigStep_ite_ok hr with ⟨h2, hr⟩ | ⟨_, hr⟩
  · obtain ⟨a, b, f, hf, hs⟩ := clause_ok hr
    refine .inr (.inr ⟨methodIs_true h2, a, b, ?_⟩)
    simp at hf; rcases hf with rfl | rfl
    · exact .inl hs
    · exact .inr hs
  · exact (Std.refusedT_not_ok hr).elim

/-- **A birth or an adoption is at `open`**, before and after. -/
theorem escrow_start {rq n o : Data} {ℓ : Label} {x : Data} (h : Admits lib law rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hℓ : ℓ = "birth" ∨ ℓ = "adopt") :
    PhaseIs o "open" ∧ PhaseIs n "open" := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [law, Std.lawOf5, Std.lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := Std.lawCase5_arm rfl ho hb
  have hl : ∀ p ∈ [(isPh ((⟨1⟩ : At).oldF "phase") "open", "notOpen"),
      (isPh ((⟨1⟩ : At).newF "phase") "open", "notOpen")], BigStep lib (x.toVal :: LawEnv rq n o cenv) p.1 (.ok (.bool true)) := by
    rcases hℓ with rfl | rfl <;> (simp [Row.find?] at hf; subst hf; exact Std.allOf_ok hbody)
  exact ⟨Std.isState_true (d := o) (i := 3) rfl (hl (isPh ((⟨1⟩ : At).oldF "phase") "open", "notOpen") (by simp)),
    Std.isState_true (d := n) (i := 2) rfl (hl (isPh ((⟨1⟩ : At).newF "phase") "open", "notOpen") (by simp))⟩

/-- **No write and no law change is admitted.** -/
theorem escrow_frozen {rq n o : Data} {ℓ : Label} {x : Data}
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hℓ : ℓ = "write" ∨ ℓ = "relaw") :
    ¬ Admits lib law rq n o := by
  rintro ⟨cenv, w, hb⟩
  simp only [law, Std.lawOf5, Std.lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := Std.lawCase5_arm rfl ho hb
  rcases hℓ with rfl | rfl <;> (simp [Row.find?] at hf; subst hf; exact Std.refusedT_not_ok hbody)

/-- An admitted act names one of the five occasions. -/
theorem escrow_occasion {rq n o : Data} (h : Admits lib law rq n o) :
    ∃ ℓ x, rq.field "occasion" = some (.inj ℓ x) ∧
      (ℓ = "adopt" ∨ ℓ = "birth" ∨ ℓ = "invoke" ∨ ℓ = "relaw" ∨ ℓ = "write") := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [law, Std.lawOf5, Std.lawBody, Std.lawCase5] at hb
  obtain ⟨ℓ, y, body, hd, hf, _⟩ := Std.case_field (d := rq) (i := 0) rfl hb
  have hm := find_mem hf
  simp at hm
  exact ⟨ℓ, y, hd, hm⟩

/-- **Settled is absorbing**: from `released` or `refunded` the law admits nothing. -/
theorem escrow_absorbing {rq n o : Data} (hs : Settled o) : ¬ Admits lib law rq n o := by
  intro h
  obtain ⟨ℓ, x, ho, hℓ⟩ := escrow_occasion h
  have notLive : ∀ p, PhaseIs o p → p = "open" ∨ p = "held" → False := by
    intro p hp hq
    rcases hs with hs | hs <;> rcases hq with rfl | rfl <;>
      exact absurd (phase_unique hs hp) (by decide)
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · exact notLive _ (escrow_start h ho (.inr rfl)).1 (.inl rfl)
  · exact notLive _ (escrow_start h ho (.inl rfl)).1 (.inl rfl)
  · rcases escrow_invoke h ho with ⟨_, a, _⟩ | ⟨_, a, _⟩ | ⟨_, a, _⟩
    · exact notLive _ a (.inl rfl)
    · exact notLive _ a (.inr rfl)
    · exact notLive _ a (.inr rfl)
  · exact escrow_frozen ho (.inr rfl) h
  · exact escrow_frozen ho (.inl rfl) h

/-! ## At most one payout -/

/-- A chain of acts on one escrow, each admitted by the law over the state the previous one left:
`(request, new state)` pairs from `o`. -/
inductive Chain (lib : List Term) : Data → List (Data × Data) → Prop
  | nil (o : Data) : Chain lib o []
  | cons {o rq n : Data} {rest : List (Data × Data)} :
      Admits lib law rq n o → Chain lib n rest → Chain lib o ((rq, n) :: rest)

theorem invoked_some {rq : Data} {m : Nat} (h : invoked rq = some m) :
    rq.field "occasion" = some (.inj "invoke" (.nat m)) := by
  unfold invoked at h
  split at h
  · cases h; assumption
  · cases h

theorem payout_settles {rq n o : Data} (h : Admits lib law rq n o) (hp : isPayout rq = true) :
    Settled n := by
  simp only [isPayout, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with hp | hp <;>
  · rcases escrow_invoke h (invoked_some hp) with ⟨hx, _⟩ | ⟨hx, _, b, _⟩ | ⟨hx, _, b, _⟩
    · injection hx with hx; simp [deposit, refund, release] at hx
    · first | exact .inr b | (injection hx with hx; simp [deposit, refund, release] at hx)
    · first | exact .inl b | (injection hx with hx; simp [deposit, refund, release] at hx)

theorem settled_chain {o : Data} {steps : List (Data × Data)} (hs : Settled o) (h : Chain lib o steps) :
    steps = [] := by
  cases h with
  | nil => rfl
  | cons ha _ => exact (escrow_absorbing hs ha).elim

/-- **The law admits at most one payout in any chain of acts**, from any state. -/
theorem escrow_law_payout_once {o : Data} {steps : List (Data × Data)} (h : Chain lib o steps) :
    payouts steps ≤ 1 := by
  induction h with
  | nil => simp [payouts]
  | @cons o rq n rest ha hr ih =>
    by_cases hp : isPayout rq = true
    · rw [settled_chain (payout_settles ha hp) hr]
      simp [payouts, hp]
    · simp only [payouts, List.filter_cons, hp] at ih ⊢
      simpa using ih

/-! ## The calls the methods make, for every value of the terms -/

/-- **What each method returns**, whole, as the receiver extracts it under `[escrow.body]`: for
every amount, party, asset, object id, grant and phase, and every other field of the request and
every rows record, `deposit` moves `amount` from the depositor's account into the escrow's own
through the grant, spending the creator's `nonce`; `refund` and `release` move `amount` out of the
escrow's own account to the depositor and to the beneficiary, through no grant, spending
`"payout"`. Every method writes the terms back unchanged and sets its target phase (`held`,
`refunded`, `released`), so the amount a payout moves is the amount the deposit moved and the
parties the law checks are the parties the creator set. -/
theorem escrow_method_results (amount : Nat) (arb asset ben dep nk self g : ByteArray) (p : Label)
    (agent nb occ pr vu arg rows : Data) :
    methodResult "deposit" (stateOf amount arb asset ben dep nk p) (.record [("grant", .digest g)])
        (reqAt agent nb occ pr self vu) rows =
      some (resultD (transferD (ofD dep asset) (ofD self asset) amount (optSome (.digest g)) (optSome (.bytes nk)))
        (stateOf amount arb asset ben dep nk "held")) ∧
    methodResult "refund" (stateOf amount arb asset ben dep nk p) arg (reqAt agent nb occ pr self vu) rows =
      some (resultD (transferD (ofD self asset) (ofD dep asset) amount optNone (optSome (.bytes payoutKey)))
        (stateOf amount arb asset ben dep nk "refunded")) ∧
    methodResult "release" (stateOf amount arb asset ben dep nk p) arg (reqAt agent nb occ pr self vu) rows =
      some (resultD (transferD (ofD self asset) (ofD ben asset) amount optNone (optSome (.bytes payoutKey)))
        (stateOf amount arb asset ben dep nk "released")) := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **No payout before the deposit**: along a chain of law-admitted acts from an `open` escrow,
the first act that is a deposit or a payout is a deposit (`held` is entered only by method 0). -/
theorem escrow_deposit_first {o : Data} {steps : List (Data × Data)} (h : Chain lib o steps)
    (ho : PhaseIs o "open") : depositFirst steps = true := by
  induction h with
  | nil => rfl
  | @cons o rq n rest ha hr ih =>
    obtain ⟨ℓ, x, hocc, hℓ⟩ := escrow_occasion ha
    have notHeld : PhaseIs o "held" → False := fun hh => absurd (phase_unique ho hh) (by decide)
    rcases hℓ with rfl | rfl | rfl | rfl | rfl
    · have := (escrow_start ha hocc (.inr rfl)).2
      have hinv : invoked rq = none := by simp [invoked, hocc]
      simp [depositFirst, hinv, isPayout, ih this]
    · have := (escrow_start ha hocc (.inl rfl)).2
      have hinv : invoked rq = none := by simp [invoked, hocc]
      simp [depositFirst, hinv, isPayout, ih this]
    · rcases escrow_invoke ha hocc with ⟨rfl, _⟩ | ⟨_, hh, _⟩ | ⟨_, hh, _⟩
      · have hinv : invoked rq = some deposit := by simp [invoked, hocc, deposit]
        simp [depositFirst, hinv]
      · exact (notHeld hh).elim
      · exact (notHeld hh).elim
    · exact (escrow_frozen hocc (.inr rfl) ha).elim
    · exact (escrow_frozen hocc (.inl rfl) ha).elim

/-! ## The package: built, checked, printed, and the refusal names -/

theorem escrow_methods : escrow.methods = ["deposit", "refund", "release"] := by decide +kernel

theorem escrow_indices :
    escrow.methods[deposit]? = some "deposit" ∧ escrow.methods[refund]? = some "refund" ∧
      escrow.methods[release]? = some "release" := by decide +kernel

theorem escrow_laws : escrow.laws = ["escrow"] := by decide +kernel

theorem escrow_checks : (escrow.checkWith [] matches .ok ()) = true := by decide +kernel

theorem escrow_prints : (Print.package escrow).isSome = true := by decide +kernel

theorem escrow_encodes : (Wire.encodePackage escrow).isSome = true := by decide +kernel

/-- What `install` carries decodes to exactly the package (LANG's canonical package codec). -/
theorem escrow_decodes : ∃ b, Wire.encodePackage escrow = some b ∧ Wire.decodePackage b = .ok escrow := by
  cases e : Wire.encodePackage escrow with
  | none => have h := escrow_encodes; rw [e] at h; simp at h
  | some b => exact ⟨b, rfl, Wire.decodePackage_eq_ok_iff.mpr e⟩

/-- Every method has exactly one call slot, of a transfer: by its signature (which
`escrow_checks` holds its body to), the calls row is `{c0}` and nothing else. -/
theorem escrow_slots :
    ["deposit", "refund", "release"].all (fun ℓ =>
      decide (((match escrow.iface with | .record r => Row.find? ℓ r | _ => none).bind
        (methodSig escrow.state escrow.rels)).map (fun x : Sig => x.calls) = some [T])) = true := by
  decide +kernel

theorem escrow_body : escrow.body = .record bodyFields := rfl

theorem escrow_field : Row.find? "escrow" bodyFields = some law := rfl

/-- **The receiver's run is the meaning**: `runLaw` admitting field `escrow` of a loaded body equal
to the package's (how `Program.judgeOne` runs it) gives `Admits … law`, the premise of every law
theorem above. -/
theorem escrow_judge_admits {g : Nat} {o n r : Data} (hg : lib[g]? = some escrow.body)
    (h : runLaw lib (.get (.ref g) "escrow") o n r = .ok (.ok ())) : Admits lib law r n o :=
  Std.runLaw_ref_admits (fs := bodyFields) hg escrow_field h

/-- The text a member installs reads back, by `Lang.Read`, as exactly the package (LANG-29's
`readPackage_checked` over `escrow_checks`). -/
theorem escrow_text_reads : ∃ s, Print.package escrow = some s ∧ Read.readPackage s = .ok escrow := by
  have hc : escrow.checkWith [] = .ok () := by
    have := escrow_checks
    split at this
    · assumption
    · cases this
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp escrow_prints
  exact ⟨s, hs, Print.readPackage_checked (by simp) hc hs⟩

/-! ### The refusal names, on the package body -/

/-- Who signs, relative to the terms of `termsD`. -/
private inductive Role | depositor | arbiter | beneficiary | stranger
  deriving DecidableEq

private def Role.all : List Role := [.depositor, .arbiter, .beneficiary, .stranger]

private def Role.bytes : Role → ByteArray
  | .depositor => "d".toUTF8 | .arbiter => "a".toUTF8 | .beneficiary => "b".toUTF8
  | .stranger => "s".toUTF8

private def termsD (p : Label) : Data := stateOf 5 "a".toUTF8 "x".toUTF8 "b".toUTF8 "d".toUTF8 "n".toUTF8 p

private def occD : Option Nat → Label → Data
  | some m, _ => .inj "invoke" (.nat m)
  | none, ℓ => if ℓ = "relaw" ∨ ℓ = "adopt" then .inj ℓ (.bytes .empty) else .inj ℓ (.record [])

private def rqD (who : Role) (occ : Data) : Data :=
  .record [("agent", .digest who.bytes), ("notBefore", .nat 0), ("occasion", occ),
    ("principal", .digest "o".toUTF8), ("self", .digest "e".toUTF8), ("validUntil", .nat 0)]

/-- The verdict is `ok` (`s = "ok"`) or a refusal whose reason is exactly `s`. -/
private def verdictIs (s : String) : Except Fault (Except ByteArray Unit) → Bool
  | .ok (.ok ()) => s == "ok"
  | .ok (.error b) => b == s.toUTF8
  | _ => false

/-- The law as `runLaw` runs it (the receiver's runner, under `lawTicks`, extracting the verdict). -/
private def lawOn (rq n o : Data) : Except Fault (Except ByteArray Unit) := runLaw [] law o n rq

/-- The spec of the law's verdict, by name, in Lean. -/
private def expected (p q : Label) (m : Nat) (who : Role) : String :=
  if p = "released" ∨ p = "refunded" then "settled"
  else if m = deposit then
    if p ≠ "open" then "notOpen" else if who ≠ .depositor then "notParty"
    else if q ≠ "held" then "badPhase" else "ok"
  else if m = refund ∨ m = release then
    if p ≠ "held" then "notHeld"
    else if who ≠ .arbiter ∧ who ≠ (if m = refund then .beneficiary else .depositor) then "notParty"
    else if q ≠ (if m = refund then "refunded" else "released") then "badPhase" else "ok"
  else "noMethod"

/-- **The names on the wire**: every phase pair, method index 0..3 and signer role, `runLaw`'s
verdict is `expected`; a birth or adoption is `ok` exactly at `open`, else `notOpen`; a write
or law change is `frozen`. -/
theorem escrow_verdicts :
    (∀ p ∈ phaseLabels, ∀ q ∈ phaseLabels, ∀ m ∈ [0, 1, 2, 3], ∀ who ∈ Role.all,
      verdictIs (expected p q m who) (lawOn (rqD who (occD (some m) "")) (termsD q) (termsD p)) = true) ∧
    (∀ p ∈ phaseLabels, ∀ ℓ ∈ ["birth", "adopt"],
      verdictIs (if p = "open" then "ok" else "notOpen") (lawOn (rqD .stranger (occD none ℓ)) (termsD p) (termsD p)) = true) ∧
    (∀ p ∈ phaseLabels, ∀ q ∈ phaseLabels, ∀ ℓ ∈ ["write", "relaw"],
      verdictIs "frozen" (lawOn (rqD .depositor (occD none ℓ)) (termsD q) (termsD p)) = true) := by
  decide +kernel

end Nanodregg.Ledger.Proofs

namespace Nanodregg.Ledger.Proofs

open Nanodregg.Lang
open Nanodregg.Ledger.Escrow

theorem ok_of_matches {x : Except Fault (Except ByteArray Unit)} (h : (x matches .ok (.ok ())) = true) :
    x = .ok (.ok ()) := by
  match x, h with
  | .ok (.ok ()), _ => rfl

/-- **The law admits something**: a birth at `open`, the depositor's deposit, the beneficiary's
refund and the arbiter's release are each `Admits` (via `runLaw_admits`), so no law theorem above
holds by an unsatisfiable premise. -/
theorem escrow_admits :
    Std.Admits [] law (rqD .stranger (occD none "birth")) (termsD "open") (termsD "open") ∧
    Std.Admits [] law (rqD .depositor (occD (some deposit) "")) (termsD "held") (termsD "open") ∧
    Std.Admits [] law (rqD .beneficiary (occD (some refund) "")) (termsD "refunded") (termsD "held") ∧
    Std.Admits [] law (rqD .arbiter (occD (some release) "")) (termsD "released") (termsD "held") := by
  refine ⟨Std.runLaw_admits (ok_of_matches ?_), Std.runLaw_admits (ok_of_matches ?_),
    Std.runLaw_admits (ok_of_matches ?_), Std.runLaw_admits (ok_of_matches ?_)⟩ <;> decide +kernel

end Nanodregg.Ledger.Proofs
