/-
# Lang.Proofs.StdChain — each stdlib law over a history, as an instance of the lift (LANG-65)

`Lang.Proofs.Std` reads ONE admitted step of each stdlib law back to facts (its 16 law × occasion
theorems; their statements are unchanged). `Lang.Proofs.Chain` lifts once. Here each law's
per-step theorems are the arguments of a scheme:

* invariants (`chain_invariant`): `bounded_reached` (the field stays a natural at most `max`),
  `quorum_mask_reached` (the approvals stay a mask over the members), `windowed_count_reached`
  (the count stays at most `limit`), `machine_reached` (the field only reaches states reachable
  from `initial` along the edges, `Reach`);
* a potential (`chain_sum`): `windowed_per_epoch`, the induction `windowed_counts` promised: along
  any chain with no birth, at most `limit` steps land in one epoch and change the guarded field;
* every step (`chain_each`, `chain_always`): `ownerSigns_every`, `allowlist_every`,
  `quorum_relaws_every`, `quorum_commits_every`, `windowed_epochs_every`.

Teeth: `bounded_chain` (a two-step chain exists, so no scheme here holds by an empty premise),
`bounded_relaw_unkept` (without `LawKeeps` a relaw would carry `bounded` past its bound: the law
admits it), `fault_law` (a law the checker accepts at `lawTy` faults: the arm
`Receiver.fault_never_admits` speaks for is live).
-/
import Lang.Proofs.Chain
import Lang.Check

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

variable {lib : List Term}

/-! ## Invariants -/

/-- **`bounded`, over a history**: from a state where `f` is a natural at most `max`, every state
the chain reaches has it so (`bounded_spec` on a birth, adoption, write or invoke; a relaw keeps
the state). -/
theorem bounded_reached {S : Ty} {f : Label} {max : Nat} {o : Data} {steps : List (Data × Data)}
    (h : Chain (Step lib (bounded S f max)) o steps) (h0 : ∃ m, o.field f = some (.nat m) ∧ m ≤ max) :
    ∀ s ∈ steps, ∃ m, s.2.field f = some (.nat m) ∧ m ≤ max := by
  refine chain_invariant (fun d => ∃ m, d.field f = some (.nat m) ∧ m ≤ max) (fun rq n o hs ho => ?_) h h0
  obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf5_occasion hs.1
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · exact bounded_spec hs.1 hocc (.inr (.inr ⟨x, rfl⟩))
  · exact bounded_spec hs.1 hocc (.inr (.inl ⟨x, rfl⟩))
  · exact bounded_spec hs.1 hocc (.inl (.inr ⟨x, rfl⟩))
  · rw [hs.2 _ _ hocc (.inl rfl)]; exact ho
  · exact bounded_spec hs.1 hocc (.inl (.inl ⟨x, rfl⟩))

private theorem pow2_pos : ∀ k, 0 < pow2 k
  | 0 => by simp [pow2]
  | k + 1 => by have := pow2_pos k; simp only [pow2]; omega

/-- **`quorum`, over a history**: every state the chain reaches holds its approvals as a mask over
the members (`quorum_birth_empty`, `quorum_adopt_fresh`, `quorum_change`; a relaw keeps the
state), from a state that does. -/
theorem quorum_mask_reached {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (quorumLaw S T ms k g)) o steps)
    (h0 : ∃ b, o.field "approvals" = some (.nat b) ∧ b < pow2 ms.length) :
    ∀ s ∈ steps, ∃ b, s.2.field "approvals" = some (.nat b) ∧ b < pow2 ms.length := by
  refine chain_invariant (fun d => ∃ b, d.field "approvals" = some (.nat b) ∧ b < pow2 ms.length)
    (fun rq n o hs ho => ?_) h h0
  obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf5_occasion hs.1
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, quorum_adopt_fresh hs.1 hocc, pow2_pos _⟩
  · exact ⟨0, quorum_birth_empty hs.1 hocc, pow2_pos _⟩
  · exact (quorum_change hs.1 hocc (.inr rfl)).2.1
  · rw [hs.2 _ _ hocc (.inl rfl)]; exact ho
  · exact (quorum_change hs.1 hocc (.inl rfl)).2.1

/-- **`windowed`, over a history**: every state the chain reaches has a count at most `limit`
(`windowed_fresh`, `windowed_counts`; a relaw keeps the state), from a state that does. -/
theorem windowed_count_reached {S T : Ty} {W limit : Nat} {g : Label} {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (windowedLaw S T W limit g)) o steps)
    (h0 : ∃ c, o.field "count" = some (.nat c) ∧ c ≤ limit) :
    ∀ s ∈ steps, ∃ c, s.2.field "count" = some (.nat c) ∧ c ≤ limit := by
  refine chain_invariant (fun d => ∃ c, d.field "count" = some (.nat c) ∧ c ≤ limit)
    (fun rq n o hs ho => ?_) h h0
  obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf5_occasion hs.1
  have hc : ∀ ℓ', ℓ' = "write" ∨ ℓ' = "invoke" → rq.field "occasion" = some (.inj ℓ' x) →
      ∃ c, n.field "count" = some (.nat c) ∧ c ≤ limit := by
    intro ℓ' hl ho'
    obtain ⟨c, _, hcn, _, hcase⟩ := windowed_counts hs.1 ho' hl
    rcases hcase with ⟨_, _, _, _, _, _, hle⟩ | ⟨_, _, _, _, _, _, hle⟩
    · exact ⟨c, hcn, hle⟩
    · exact ⟨c, hcn, hle⟩
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, windowed_fresh hs.1 hocc (.inr rfl), Nat.zero_le _⟩
  · exact ⟨0, windowed_fresh hs.1 hocc (.inl rfl), Nat.zero_le _⟩
  · exact hc _ (.inr rfl) hocc
  · rw [hs.2 _ _ hocc (.inl rfl)]; exact ho
  · exact hc _ (.inl rfl) hocc

/-- The states a machine reaches from `initial` along its edges. -/
inductive Reach (edges : List (Label × Nat × Label)) (initial : Label) : Label → Prop
  | start : Reach edges initial initial
  | edge {a b : Label} {m : Nat} : Reach edges initial a → (a, m, b) ∈ edges → Reach edges initial b

/-- **A machine, over a history**: from a state at a reachable state, every state the chain
reaches is at a state reachable from `initial` along the edges (`machine_birth`, `machine_adopt`,
`machine_invoke`; `machine_write_refused` and `machine_relaw_refused` leave no other step). -/
theorem machine_reached {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {o : Data} {steps : List (Data × Data)}
    (h : Chain (Step lib (machineLaw S f states initial edges)) o steps)
    (h0 : ∃ a y, o.field f = some (.inj a y) ∧ Reach edges initial a) :
    ∀ s ∈ steps, ∃ b y, s.2.field f = some (.inj b y) ∧ Reach edges initial b := by
  refine chain_invariant (fun d => ∃ a y, d.field f = some (.inj a y) ∧ Reach edges initial a)
    (fun rq n o hs ho => ?_) h h0
  obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf5_occasion hs.1
  rcases hℓ with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨y, hy⟩ := machine_adopt hs.1 hocc
    exact ⟨initial, y, hy, .start⟩
  · obtain ⟨y, hy⟩ := machine_birth hs.1 hocc
    exact ⟨initial, y, hy, .start⟩
  · obtain ⟨a, m, b, he, -, ⟨y, hya⟩, ⟨y', hyb⟩⟩ := machine_invoke hs.1 hocc
    obtain ⟨a', z, hz, hr⟩ := ho
    rw [hz] at hya
    injection hya with hya
    injection hya with ha
    subst ha
    exact ⟨b, y', hyb, .edge hr he⟩
  · exact (machine_relaw_refused hocc hs.1).elim
  · exact (machine_write_refused hocc hs.1).elim

/-! ## A potential: at most `limit` changes per epoch -/

/-- `windowed`'s potential at epoch `e`: 0 before `e`, the count (capped at `limit`) at `e`, and
`limit` after `e` or on a state with no epoch. -/
private def epochPot (e limit : Nat) (d : Data) : Nat :=
  match d.field "epoch" with
  | some (.nat ep) =>
    if ep < e then 0 else if ep = e then
      (match d.field "count" with | some (.nat c) => min c limit | _ => limit) else limit
  | _ => limit

private theorem epochPot_le (e limit : Nat) (d : Data) : epochPot e limit d ≤ limit := by
  unfold epochPot
  split
  · split
    · exact Nat.zero_le _
    · split
      · split
        · exact Nat.min_le_right _ _
        · exact Nat.le_refl _
      · exact Nat.le_refl _
  · exact Nat.le_refl _

open Classical in
/-- **At most `limit` changes per epoch** (the induction `windowed_counts` promised): along any
chain of `windowed` steps with no birth, from any state, at most `limit` steps land in epoch `e`
(their new state's epoch) and change the guarded field `g` (from the state before them). An epoch
never goes back (`windowed_counts`), a relaw or adoption keeps the state, and the count rises by
one per change inside an epoch: the potential is the count at `e`. The birth is excluded because a
`Chain` does not know an object is born once (KERNEL's history does). -/
theorem windowed_per_epoch {S T : Ty} {W limit : Nat} {g : Label} (e : Nat) {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (windowedLaw S T W limit g)) o steps)
    (hnb : ∀ s ∈ steps, ∀ x, s.1.field "occasion" ≠ some (.inj "birth" x)) :
    (((o :: steps.map Prod.snd).zip steps).map fun x =>
      if x.2.2.field "epoch" = some (.nat e) ∧ x.2.2.field g ≠ x.1.field g then 1 else 0).sum ≤ limit := by
  have hstep : ∀ rq n o, Step lib (windowedLaw S T W limit g) rq n o → (rq, n) ∈ steps →
      (if n.field "epoch" = some (.nat e) ∧ n.field g ≠ o.field g then 1 else 0) + epochPot e limit o ≤
        epochPot e limit n := by
    intro rq n o hs hm
    obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf5_occasion hs.1
    have keep : n = o → (if n.field "epoch" = some (.nat e) ∧ n.field g ≠ o.field g then 1 else 0) +
        epochPot e limit o ≤ epochPot e limit n := by
      rintro rfl
      simp
    have change : ℓ = "write" ∨ ℓ = "invoke" → (if n.field "epoch" = some (.nat e) ∧ n.field g ≠ o.field g
        then 1 else 0) + epochPot e limit o ≤ epochPot e limit n := by
      intro hl
      obtain ⟨c, inc, hcn, hinc, hcase⟩ := windowed_counts hs.1 hocc hl
      rcases hcase with ⟨ep, c0, hoe, hne, hoc, rfl, hle⟩ | ⟨ep, ep', hoe, hne, hlt, rfl, hle⟩
      · rcases hinc with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ <;>
          simp only [epochPot, hoe, hne, hcn, hoc, Option.some.injEq, Data.nat.injEq] <;>
          (repeat' split) <;> first | omega | (simp_all; done) | (simp_all; omega)
      · rcases hinc with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ <;>
          simp only [epochPot, hoe, hne, hcn, Option.some.injEq, Data.nat.injEq] <;>
          (repeat' split) <;> first | omega | (simp_all; done) | (simp_all; omega)
    rcases hℓ with rfl | rfl | rfl | rfl | rfl
    · exact keep (hs.2 _ _ hocc (.inr rfl))
    · exact (hnb (rq, n) hm x hocc).elim
    · exact change (.inr rfl)
    · exact keep (hs.2 _ _ hocc (.inl rfl))
    · exact change (.inl rfl)
  exact Nat.le_trans (Nat.le_add_right _ _)
    (chain_sum (epochPot e limit) (fun _ n o => if n.field "epoch" = some (.nat e) ∧ n.field g ≠ o.field g then 1 else 0)
      limit h hstep (fun s _ => epochPot_le e limit s.2) (epochPot_le e limit o))

/-! ## Every step -/

/-- **`ownerSigns`, over a history**: every step was signed by its principal (`ownerSigns_spec`). -/
theorem ownerSigns_every {S : Ty} {o : Data} {steps : List (Data × Data)} (h : Chain (Step lib (ownerSigns S)) o steps) :
    ∀ s ∈ steps, ∃ sg, s.1.field "agent" = some (.digest sg) ∧ s.1.field "principal" = some (.digest sg) :=
  chain_each (fun rq _ => ∃ sg, rq.field "agent" = some (.digest sg) ∧ rq.field "principal" = some (.digest sg))
    (fun _ _ _ hs => by
      obtain ⟨ℓ, x, hocc, -⟩ := lawOf5_occasion hs.1
      exact ownerSigns_spec hs.1 hocc) h

/-- **`allowlist`, over a history**: every step was signed by a listed member (`allowlist_spec`). -/
theorem allowlist_every {ids : List ByteArray} {S : Ty} {o : Data} {steps : List (Data × Data)}
    (h : Chain (Step lib (allowlistLaw S ids)) o steps) :
    ∀ s ∈ steps, ∃ m ∈ ids, s.1.field "agent" = some (.digest m) :=
  chain_each (fun rq _ => ∃ m ∈ ids, rq.field "agent" = some (.digest m))
    (fun _ _ _ hs => by
      obtain ⟨ℓ, x, hocc, -⟩ := lawOf5_occasion hs.1
      exact allowlist_spec hs.1 hocc) h

/-- **`quorum`'s law changes, over a history**: every relaw step was by a member, with `k`
approvals in the state before it of exactly the incoming laws (`quorum_relaw_needs_k`). -/
theorem quorum_relaws_every {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (quorumLaw S T ms k g)) o steps) :
    ∀ o' rq n, (o', (rq, n)) ∈ (o :: steps.map Prod.snd).zip steps → ∀ x,
      rq.field "occasion" = some (.inj "relaw" x) →
      (∃ m ∈ ms, rq.field "agent" = some (.digest m)) ∧
      (∃ a, o'.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a ms.length) ∧
      ∃ s, o'.field "proposal" = some (.inj "laws" (.bytes s)) ∧ x = .bytes s :=
  chain_always _ (fun _ _ _ hs _ ho => quorum_relaw_needs_k hs.1 ho) h

/-- **`quorum`'s commits, over a history**: every write or invoke step that changed the guarded
field set it to what the proposal in the state before it named, with `k` approvals there, and
reset them (`quorum_change_needs_k`). -/
theorem quorum_commits_every {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (quorumLaw S T ms k g)) o steps) :
    ∀ o' rq n, (o', (rq, n)) ∈ (o :: steps.map Prod.snd).zip steps → ∀ ℓ x,
      rq.field "occasion" = some (.inj ℓ x) → (ℓ = "write" ∨ ℓ = "invoke") → n.field g ≠ o'.field g →
      ∃ ng, n.field g = some ng ∧
        (∃ a, o'.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a ms.length) ∧
        o'.field "proposal" = some (.inj "set" ng) ∧ n.field "approvals" = some (.nat 0) :=
  chain_always _ (fun _ _ _ hs _ _ ho hl hchg => quorum_change_needs_k hs.1 ho hl hchg) h

/-- **`windowed`'s epochs, over a history**: every step other than a relaw was signed for a window
inside one epoch, and its new state records that epoch (`windowed_lands_in_epoch`). -/
theorem windowed_epochs_every {S T : Ty} {W limit : Nat} {g : Label} {o : Data}
    {steps : List (Data × Data)} (h : Chain (Step lib (windowedLaw S T W limit g)) o steps) :
    ∀ s ∈ steps, ∀ ℓ x, s.1.field "occasion" = some (.inj ℓ x) → ℓ ≠ "relaw" →
      ∃ nb vu, s.1.field "notBefore" = some (.nat nb) ∧ s.1.field "validUntil" = some (.nat vu) ∧
        vu / W = nb / W ∧ s.2.field "epoch" = some (.nat (nb / W)) :=
  chain_each (fun rq n => ∀ ℓ x, rq.field "occasion" = some (.inj ℓ x) → ℓ ≠ "relaw" →
      ∃ nb vu, rq.field "notBefore" = some (.nat nb) ∧ rq.field "validUntil" = some (.nat vu) ∧
        vu / W = nb / W ∧ n.field "epoch" = some (.nat (nb / W)))
    (fun _ _ _ hs ℓ x ho hr => by
    obtain ⟨ℓ', x', ho', hℓ⟩ := lawOf5_occasion hs.1
    rw [ho] at ho'
    injection ho' with ho'
    injection ho' with hℓℓ
    subst hℓℓ
    refine windowed_lands_in_epoch hs.1 ho ?_
    rcases hℓ with h | h | h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr (.inr h))
    · exact (hr h).elim
    · exact .inr (.inr (.inl h))) h

/-! ## Teeth -/

private def b (s : String) : ByteArray := s.toUTF8

private def rqOn (occ : Data) : Data :=
  .record [("agent", .digest (b "a")), ("notBefore", .nat 0), ("occasion", occ),
    ("principal", .digest (b "a")), ("self", .digest (b "e")), ("validUntil", .nat 0)]

private def OS : Ty := .record [("total", .nat)]
private def os (total : Nat) : Data := .record [("total", .nat total)]

private theorem ok_of_matches {x : Except Fault (Except ByteArray Unit)} (h : (x matches .ok (.ok ())) = true) :
    x = .ok (.ok ()) := by
  match x, h with
  | .ok (.ok ()), _ => rfl

private theorem keeps_of {ℓ : Label} {y n o : Data} (hℓ : ℓ ≠ "relaw" ∧ ℓ ≠ "adopt") :
    LawKeeps (rqOn (.inj ℓ y)) n o := by
  intro ℓ' x ho hl
  have : (rqOn (.inj ℓ y)).field "occasion" = some (.inj ℓ y) := rfl
  rw [this] at ho
  injection ho with ho
  injection ho with ho
  subst ho
  rcases hl with rfl | rfl
  · exact (hℓ.1 rfl).elim
  · exact (hℓ.2 rfl).elim

/-- **A chain exists**: `bounded total ≤ 100` admits a birth at 0 and then a write to 100, so the
schemes' premise is met by a real two-step history. -/
theorem bounded_chain :
    Chain (Step [] (bounded OS "total" 100)) (os 0)
      [(rqOn (.inj "birth" (.record [])), os 0), (rqOn (.inj "write" (.record [])), os 100)] :=
  .cons ⟨runLaw_admits (ok_of_matches (by decide +kernel)), keeps_of (by decide)⟩
    (.cons ⟨runLaw_admits (ok_of_matches (by decide +kernel)), keeps_of (by decide)⟩ (.nil _))

/-- **`LawKeeps` is load-bearing**: `bounded total ≤ 100` admits a relaw whose new state holds 500
(its relaw arm is `ok`), so without the kernel's "a law change keeps the state" `bounded_reached`
would be false. -/
theorem bounded_relaw_unkept :
    Admits [] (bounded OS "total" 100) (rqOn (.inj "relaw" (.bytes (b "L")))) (os 500) (os 5) ∧
      ¬ ∃ m, (os 500).field "total" = some (.nat m) ∧ m ≤ 100 := by
  refine ⟨runLaw_admits (ok_of_matches (by decide +kernel)), ?_⟩
  rintro ⟨m, hm, hle⟩
  have : (os 500).field "total" = some (.nat 500) := rfl
  rw [this] at hm
  injection hm with hm
  injection hm with hm
  omega

private def faultLaw : Term :=
  .lam (.record []) (.lam (.record []) (.lam reqTy
    (.ite (.prim .eq (.prim .sub (.nat 0) (.nat 1)) (.nat 0)) okT okT)))

/-- **The fault arm is live on a checked law**: a law the checker accepts at `lawTy` whose run
faults (`0 - 1` underflows), so `Receiver.fault_never_admits`' premise is met by a law an install
check passes, and `runLaw_never_stuck` leaves this arm open by design. -/
theorem fault_law :
    check [] faultLaw (lawTy (.record [])) = true ∧
      (match runLaw [] faultLaw (.record []) (.record []) (rqOn (.inj "write" (.record []))) with
        | .error .underflow => true
        | _ => false) = true := by
  decide +kernel

end Nanodregg.Lang.Std
