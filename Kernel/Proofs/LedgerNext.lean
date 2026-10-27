/-
# Kernel.Proofs.LedgerNext — a counted right's ledger reads back what it spent (KERNEL-30)

KERNEL-60's counted rights (`enroll`, `transfer`, `credit`) are spent through one append-only
ledger per kind in the grant (`ledgerLeft`, `spendAt`): what is left is the LAST entry among the
slots `base … base + ledgerSpendsMax`, and a spend writes the remainder at index `led.length`. That
write reads back as the new last entry only when the ledger's keys are exactly
`base, base + 1, …, base + length - 1`. With a gap the write lands below the last key, `getLast?`
keeps reading the old entry, and the cap never falls. Proved here:

* `GrantContiguous cell` (each counted ledger's keys are `List.range' base length`) and
  `LedgerContiguous E w` (every live grant is). `genesis_ledgerContiguous`; `step_ledgerContiguous`:
  every derive-then-admit step keeps it, given `CellsCanon`; `submit_ledgerContiguous`;
  `honest_ledgerContiguous` (an honest folded log keeps both). Births: only `grant` bears a grant, and its
  ledgers are contiguous (`derive_born_grant`; one entry per counted kind, at its base, inside
  `grantSlots_contiguous`). Writes: `grant_turn_cell`.
* `grant_turn_cell` (the totality at the World, from `effect_at_grant`): a derived, admitted turn
  keeps a live grant, retires it, or appends ONE entry `left - u` at `base + i` of one ledger: the
  turn's act at a cell is ONE effect's (`actFor` takes the first). That this act is the turn's ONLY
  spend of the grant is `sealTurn`'s `duplicateEffect` (effects name distinct cells; without it a
  second spend would be silently dropped): `effect_reads_back` uses it in general, and
  `two_spends_refused` shows one instance.
* `ledgerLeft_append`: over a canonical cell with a contiguous ledger, that append reads back as
  `(i + 1, left - u)`, every other ledger unchanged. So `grant_turn_ledger`: a turn leaves what is
  left of every ledger of a live grant as it was, or lowers one ledger by exactly the `u` it spent.
  `spend_reads_back` (a signed transfer through `g`), `credit_reads_back`, and
  `spend_reads_back_dispatched` (a transfer the walk dispatched at any depth: `u` is its amount).

Tooth: `gap_never_falls`: a transfer ledger holding `transferBase` and `transferBase + 4` is not
contiguous; two spends of its whole 10 are each admitted against what it reads as left, write keys
the cell does not hold (so `appendOnly` admits them), and leave it reading 10 left: two spends of
10 each admitted against a cap of 10. `gap_world_not_contiguous`: no World holding that cell live is `LedgerContiguous`.
-/
import Kernel.Proofs.InvokeTree
import Kernel.Proofs.WriteNext
import Kernel.Proofs.Ledger

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## Contiguous ledgers -/

/-- **A grant's counted ledgers are contiguous**: at each counted base, the keys `ledgerLeft` reads
are `base, base + 1, …`, as many as there are (none, for a kind the grant does not carry). -/
def GrantContiguous (cell : Cell) : Prop :=
  ∀ base, LedgerBase base →
    (cell.slots.filter fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax).map Prod.fst =
      List.range' base (cell.slots.filter fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax).length

/-- **Every live grant's ledgers are contiguous.** -/
def LedgerContiguous (E : Env D) (w : World D) : Prop :=
  ∀ id cell, w.live E id = some cell → cell.kind = kindGrant → GrantContiguous cell

/-! ## Slots -/

theorem countOf_countBytes (n : Nat) : countOf (countBytes n) = some (n % 2 ^ 64) := floorOf_bytes n

theorem countOf_lt {b : ByteArray} {n : Nat} (h : countOf b = some n) : n < 2 ^ 64 := floorOf_lt h

/-- A `set` at a key above every ledger key, inside the ledger's range, appends to the ledger. -/
theorem filter_set_top {base k : Nat} {v : ByteArray} (hk1 : base ≤ k) (hk2 : k ≤ base + ledgerSpendsMax) :
    ∀ {s : Slots}, s.Pairwise (fun a b => a.1 < b.1) →
      (∀ p ∈ s, base ≤ p.1 → p.1 ≤ base + ledgerSpendsMax → p.1 < k) →
      (Slots.set k v s).filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) =
        s.filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) ++ [(k, v)]
  | [], _, _ => by simp [Slots.set, hk1, hk2]
  | (k', v') :: rest, hs, hlt => by
      have h1 := (List.pairwise_cons.mp hs).1
      have h2 := (List.pairwise_cons.mp hs).2
      have hP : (decide (base ≤ k) && decide (k ≤ base + ledgerSpendsMax)) = true := by simp [hk1, hk2]
      simp only [Slots.set]
      by_cases hlt' : k < k'
      · rw [if_pos hlt']
        have hnil : ∀ q ∈ (k', v') :: rest, ¬ (base ≤ q.1 ∧ q.1 ≤ base + ledgerSpendsMax) := by
          intro q hq ⟨a, b⟩
          have := hlt q hq a b
          rcases List.mem_cons.mp hq with rfl | hq
          · exact absurd this (by simp only; omega)
          · have := h1 q hq; simp only at this; omega
        have hf : ((k', v') :: rest).filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) = [] :=
          List.filter_eq_nil_iff.mpr fun q hq => by simpa using hnil q hq
        rw [List.filter_cons_of_pos
          (p := fun p : Nat × ByteArray => decide (base ≤ p.1) && decide (p.1 ≤ base + ledgerSpendsMax)) hP, hf]
        rfl
      · rw [if_neg hlt']
        by_cases heq : k = k'
        · subst heq
          exact absurd (hlt _ (List.mem_cons_self ..) hk1 hk2) (by simp)
        · rw [if_neg heq]
          have ih := filter_set_top hk1 hk2 (s := rest) (v := v) h2 (fun p hp => hlt p (List.mem_cons_of_mem _ hp))
          rw [List.filter_cons, List.filter_cons]
          split <;> simp [ih]

/-- A `set` at a key outside a ledger's range leaves that ledger. -/
theorem filter_set_out {base k : Nat} {v : ByteArray} (hk : ¬ (base ≤ k ∧ k ≤ base + ledgerSpendsMax)) :
    ∀ s : Slots, (Slots.set k v s).filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) =
      s.filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax)
  | [] => by
      simp only [Slots.set]
      exact List.filter_eq_nil_iff.mpr fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simpa using hk
  | (k', v') :: rest => by
      have hK : (decide (base ≤ k) && decide (k ≤ base + ledgerSpendsMax)) = false := by
        simpa using hk
      simp only [Slots.set]
      by_cases hlt : k < k'
      · rw [if_pos hlt]
        simp only [List.filter_cons]
        simp [hK]
      · rw [if_neg hlt]
        by_cases heq : k = k'
        · subst heq
          rw [if_pos rfl]
          simp only [List.filter_cons]
          simp [hK]
        · rw [if_neg heq, List.filter_cons, List.filter_cons, filter_set_out hk rest]

omit [Ord D] [DecidableEq D] in
/-- What `ledgerLeft` read: the next index is the ledger's length, and what is left a `u64`'s. -/
theorem ledgerLeft_ok {base i left : Nat} {g : D} {cell : Cell}
    (h : ledgerLeft base g cell = .ok (i, left)) :
    i = (cell.slots.filter fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax).length ∧ left < 2 ^ 64 := by
  simp only [ledgerLeft] at h
  split at h
  · cases h
  · split at h
    · rename_i n hn
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, countOf_lt hn⟩
    · cases h

/-- The ranges of the three ledgers are disjoint, and each lies inside the slot keys. -/
theorem ledgerBase_disjoint {b b' k : Nat} (hb : LedgerBase b) (hb' : LedgerBase b') (hne : b' ≠ b)
    (hk : b ≤ k ∧ k ≤ b + ledgerSpendsMax) : ¬ (b' ≤ k ∧ k ≤ b' + ledgerSpendsMax) := by
  unfold LedgerBase at hb hb'
  simp only [enrollBase, transferBase, creditBase, ledgerSpendsMax, enrollMax] at hb hb' hk ⊢
  omega

omit [Ord D] [DecidableEq D] in
/-- **A spend reads back** (the slot half): over a canonical cell whose ledger at `base` is
contiguous, appending `left - u` at the index `ledgerLeft` named leaves the ledger reading
`(i + 1, left - u)`, still contiguous, and every other ledger as it was. -/
theorem ledgerLeft_append {base i left u : Nat} {g : D} {cell : Cell} (hb : LedgerBase base)
    (hcan : Slots.ascending cell.slots = true) (hcon : GrantContiguous cell)
    (hl : ledgerLeft base g cell = .ok (i, left)) (hi : i ≤ ledgerSpendsMax) (hu : u ≤ left) :
    let cell' := { cell with slots := cell.slots.set (base + i) (countBytes (left - u)) }
    ledgerLeft base g cell' = .ok (i + 1, left - u) ∧
      (∀ b, LedgerBase b → b ≠ base → ledgerLeft b g cell' = ledgerLeft b g cell) ∧
      Slots.ascending cell'.slots = true ∧ GrantContiguous cell' := by
  intro cell'
  obtain ⟨hi', hlt⟩ := ledgerLeft_ok hl
  have hc := hcon base hb
  have hpw := (ascending_iff _).mp hcan
  have htop : (cell.slots.set (base + i) (countBytes (left - u))).filter
      (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) =
      cell.slots.filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) ++
        [(base + i, countBytes (left - u))] := by
    refine filter_set_top (by omega) (by omega) hpw (fun p hp h1 h2 => ?_)
    have hm : p.1 ∈ (cell.slots.filter fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax).map Prod.fst :=
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, by simp [h1, h2]⟩)
    rw [hc, List.mem_range'_1] at hm
    omega
  have hout : ∀ b, LedgerBase b → b ≠ base →
      (cell.slots.set (base + i) (countBytes (left - u))).filter
        (fun p => b ≤ p.1 && p.1 ≤ b + ledgerSpendsMax) =
      cell.slots.filter (fun p => b ≤ p.1 && p.1 ≤ b + ledgerSpendsMax) := fun b hb' hne =>
    filter_set_out (ledgerBase_disjoint hb hb' hne ⟨by omega, by omega⟩) _
  have hmod : (left - u) % 2 ^ 64 = left - u := Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, fun b hb' hne => ?_, ?_, fun b hb' => ?_⟩
  · show ledgerLeft base g { cell with slots := _ } = _
    simp only [ledgerLeft]
    rw [htop, List.getLast?_concat]
    simp only [countOf_countBytes, hmod, List.length_append, List.length_singleton, hi']
  · show ledgerLeft b g { cell with slots := _ } = ledgerLeft b g cell
    simp only [ledgerLeft]
    rw [hout b hb' hne]
  · exact (ascending_iff _).mpr (set_pairwise hpw)
  · show List.map Prod.fst ((cell.slots.set _ _).filter _) = List.range' b (List.length ((cell.slots.set _ _).filter _))
    by_cases hbb : b = base
    · subst hbb
      rw [htop, List.map_append, hc, List.length_append, List.length_singleton, ← hi', List.range'_concat]
      simp [hi']
    · rw [hout b hb' hbb]
      exact hcon b hb'

/-! ## Births: one entry per ledger, at its base -/

omit [Ord D] [DecidableEq D] in
/-- A cell whose every key inside a ledger's range IS that ledger's base has contiguous ledgers. -/
theorem grantContiguous_of_keys {cell : Cell} (hs : Slots.ascending cell.slots = true)
    (hk : ∀ p ∈ cell.slots, ∀ base, LedgerBase base → base ≤ p.1 → p.1 ≤ base + ledgerSpendsMax → p.1 = base) :
    GrantContiguous cell := by
  intro base hb
  have hall : ∀ p ∈ cell.slots.filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax), p.1 = base := by
    intro p hp
    obtain ⟨hp, hq⟩ := List.mem_filter.mp hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hk p hp base hb hq.1 hq.2
  have hpw := ((ascending_iff _).mp hs).filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax)
  generalize cell.slots.filter (fun p => base ≤ p.1 && p.1 ≤ base + ledgerSpendsMax) = F at hall hpw ⊢
  match F, hall, hpw with
  | [], _, _ => rfl
  | [a], hall, _ => simp [hall a (List.mem_singleton_self _)]
  | a :: b :: _, hall, hpw =>
      have := (List.pairwise_cons.mp hpw).1 b (List.mem_cons_self ..)
      rw [hall a (List.mem_cons_self ..), hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..))] at this
      omega

omit [Ord D] [DecidableEq D] in
theorem mem_slotsOf {p : Nat × ByteArray} :
    ∀ (ps : List (Nat × ByteArray)) (s0 : Slots), p ∈ ps.foldl (fun s q => s.set q.1 q.2) s0 → p ∈ s0 ∨ p ∈ ps
  | [], _, h => .inl h
  | q :: rest, s0, h => by
      rcases mem_slotsOf rest _ h with h | h
      · rcases mem_set h with rfl | h
        · exact .inr (List.mem_cons_self ..)
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

omit [Ord D] [DecidableEq D] in
/-- A grant cell built from header slots below 16 and `rightSlots`: one entry per counted kind, at
its base, so its ledgers are contiguous. -/
theorem grantSlots_contiguous {k : Nat} {dsc : Discipline} {hdr : List (Nat × ByteArray)} {rights : List Right}
    (hh : ∀ q ∈ hdr, q.1 < 16) :
    GrantContiguous { kind := k, discipline := dsc, slots := slotsOf (hdr ++ rightSlots rights) } := by
  refine grantContiguous_of_keys (slotsOf_ascending _) (fun p hp base hb h1 h2 => ?_)
  rcases mem_slotsOf _ [] hp with hp | hp
  · simp at hp
  rcases List.mem_append.mp hp with hp | hp
  · have := hh p hp
    unfold LedgerBase at hb
    simp only [enrollBase, transferBase, creditBase] at hb
    omega
  · have hkey : (∃ r, p.1 = rightKey r) ∨ p.1 = enrollBase ∨ p.1 = transferBase ∨ p.1 = creditBase := by
      unfold rightSlots at hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
        exact .inl ⟨r, rfl⟩
      · simp only [List.mem_append] at hp
        right
        rcases hp with (hp | hp) | hp <;> split at hp <;> simp at hp <;> simp [hp]
    unfold LedgerBase at hb
    rcases hkey with ⟨r, hr⟩ | hr
    · cases r <;> simp only [rightKey] at hr <;>
        simp only [enrollBase, transferBase, creditBase, invokeBase, ledgerSpendsMax, enrollMax] at hr hb h1 h2 ⊢ <;>
        omega
    · simp only [enrollBase, transferBase, creditBase, ledgerSpendsMax, enrollMax] at hr hb h1 h2 ⊢
      omega

omit [Ord D] in
/-- **Every grant a derivation bears has contiguous ledgers**, anywhere in a call's tree: only
`grant` bears a grant cell, and its counted rights' slots are one entry per kind at its base. -/
theorem derive_born_grant {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {d : Draft D}
    (h : derive X look rv c = .ok d) : ∀ p ∈ d.creates, p.2.kind = kindGrant → GrantContiguous p.2 := by
  have notGrant : ∀ (cell : Cell) (base : Nat), cell.kind ≠ kindGrant →
      ∀ p ∈ bornAt X c base [cell], p.2.kind = kindGrant → GrantContiguous p.2 := by
    intro cell base hk p hp hpk
    have := mem_bornAt_cell hp
    simp only [List.mem_singleton] at this
    rw [this] at hpk; exact absurd hpk hk
  refine derive_all (P := fun d => ∀ p ∈ d.creates, p.2.kind = kindGrant → GrantContiguous p.2) ?_ ?_ ?_ h
  · intro a b ha hb p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp
    · exact hb p hp
  · intro _ _ _ _ p hp; simp at hp
  · intro sub wk actor caller b r hb h
    cases b with
    | invoke => simp [Body.isInvoke] at hb
    | enroll key next origin join via =>
        have hd := stepped_draft h
        simp only [enroll, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        intro p hp hpk
        simp only [List.mem_singleton] at hp
        subst hp
        simp [kindMember, kindGrant] at hpk
    | rotate key next =>
        have hd := stepped_draft h
        simp only [rotate, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | install pkg =>
        have hd := stepped_draft h
        simp only [install, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨⟨⟩, _, hr⟩ := hd
        rw [← hr]
        exact notGrant _ _ (by simp [kindPackage, kindGrant])
    | create pkg laws state =>
        have hd := stepped_draft h
        simp only [create, except_bind_ok, pure, Except.pure] at hd
        obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, hr⟩ := hd
        have hc : r.1.creates = bornAt X c wk.born [objectCell X actor pkg laws state] := by
          cases pkg <;>
          · simp only [except_bind_ok, Except.ok.injEq] at hr
            obtain ⟨_, _, hr⟩ := hr
            rw [← hr]
        rw [hc]
        exact notGrant _ _ (by simp [objectCell, kindObject, kindGrant])
    | createOf pkg laws state =>
        have hd := stepped_draft h
        intro x hx hk
        rcases createOf_kind hd x hx with h' | h' <;> rw [h'] at hk <;>
          simp [kindObject, kindPackage, kindGrant] at hk
    | write obj edits via =>
        have hd := stepped_draft h
        simp only [write, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | law obj laws via =>
        have hd := stepped_draft h
        simp only [law, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, _, _, ⟨⟩, _, ⟨⟩, _, hr⟩ := hd
        rw [← hr]
        simp
    | grant target grantee rights parent =>
        have hd := stepped_draft h
        simp only [grant, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        intro x hx _
        have := mem_bornAt_cell hx
        simp only [List.mem_singleton] at this
        rw [this]
        refine grantSlots_contiguous (fun q hq => ?_)
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with (rfl | rfl | rfl) | hq
        · simp [grantTarget]
        · simp [grantGrantee]
        · simp [grantIssuer]
        · cases parent <;> simp at hq
          subst hq; simp [grantParent]
    | retire x =>
        have hd := stepped_draft h
        simp only [retire, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, hr⟩ := hd
        rw [← hr]
        simp
    | issue cap =>
        have hd := stepped_draft h
        simp only [issue, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨⟨⟩, _, hr⟩ := hd
        rw [← hr]
        exact notGrant _ _ (by simp [accountCell, kindAccount, kindGrant])
    | account asset owner =>
        have hd := stepped_draft h
        simp only [account, pure, Except.pure, Except.ok.injEq] at hd
        rw [← hd]
        intro p hp hk
        simp only [List.mem_singleton] at hp
        rw [hp] at hk
        simp [accountCell, kindAccount, kindGrant] at hk
    | transfer src dst amount via once =>
        have hd := stepped_draft h
        simp only [transfer, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        simp
    | credit well acct amount via =>
        have hd := stepped_draft h
        simp only [credit, except_bind_ok, pure, Except.pure, Except.ok.injEq] at hd
        obtain ⟨_, _, _, _, _, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, ⟨⟩, _, _, _, hr⟩ := hd
        rw [← hr]
        simp

/-- **Genesis has contiguous ledgers**: each founder's root grant holds one enrolment entry. -/
theorem genesis_ledgerContiguous (X : Ctx D) (name nonce : ByteArray) (allowance : Nat)
    (founders : List (ByteArray × D)) (auth : Authority) :
    LedgerContiguous X.env (genesisWorld X name nonce allowance founders auth) := by
  intro id cell hl hk
  rcases mem_genesisEntries (genesis_live hl) with hm | ⟨-, he⟩
  case inr =>
    injection he with he _
    subst he
    simp [authorityCell, kindAuthority, kindGrant] at hk
  obtain ⟨p, _, ⟨_, he⟩ | ⟨_, he⟩⟩ := mem_founderEntries hm
  · injection he with he _
    subst he
    simp [founderMember, kindMember, kindGrant] at hk
  · injection he with he _
    subst he
    refine grantSlots_contiguous (fun q hq => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simp [grantTarget]
    · simp [grantGrantee]
    · simp [grantIssuer]

/-! ## A turn at a grant -/

section Turn
variable [Std.TransOrd D] [Std.LawfulEqOrd D]

/-- **A retired touch, forward**: an admitted turn that retires a touched cell leaves nothing live
there. -/
theorem admit_retired {E : Env D} {w w' : World D} {t : Turn D} {x : Touch D}
    (h : World.admit E w t = .ok w') (hx : x ∈ t.touches) (ha : x.act = .retire) : w'.live E x.cell = none := by
  obtain ⟨posts, hk, rfl⟩ := admit_ok h
  obtain ⟨raw, hm, hposts⟩ := hk.touches
  obtain ⟨r, hr⟩ := mapEx_each hm x hx
  have hr' := hr
  unfold touchCheck at hr'
  simp only [except_bind_ok, ha] at hr'
  obtain ⟨⟨⟩, _, hr'⟩ := hr'
  rcases hc : w.entry E x.cell with _ | ⟨cell, v⟩ | _
  · rw [hc] at hr'; simp at hr'
  · rw [hc] at hr'
    simp only [except_bind_ok, pure, Except.pure, Except.ok.injEq] at hr'
    obtain ⟨⟨⟩, _, hre⟩ := hr'
    rw [← hre] at hr
    have hin := mapEx_result_mem hm hx hr
    have hpost : (⟨x.cell, .tomb, counterWeight + cell.weight, flowsOf (some cell) none⟩ : Post D) ∈ posts := by
      rw [hposts]; simpa [List.reduceOption, List.mem_filterMap] using hin
    have hshape := hk.shape
    unfold checkShape at hshape
    simp only [except_bind_ok] at hshape
    obtain ⟨⟨⟩, hnt, _⟩ := hshape
    have hnodup : ((posts.map Post.pair).map Prod.fst).Nodup := by
      rw [List.map_map]
      have : (Prod.fst ∘ Post.pair : Post D → D) = Post.cell := rfl
      rw [this, hposts]
      exact (posts_sublist t.touches raw hm).nodup (noDup_nodup hnt)
    have hcr := hk.creates
    unfold checkCreates at hcr
    simp only [except_bind_ok] at hcr
    obtain ⟨⟨⟩, _, ⟨⟩, _, ⟨⟩, hnbt, _⟩ := hcr
    have hnb : x.cell ∉ (bornEntries t).map Prod.fst := by
      intro hm'
      unfold bornEntries at hm'
      rw [List.map_map] at hm'
      have : (Prod.fst ∘ fun p : D × Cell => (p.1, Entry.live p.2 0)) = Prod.fst := rfl
      rw [this] at hm'
      exact (List.nodup_append.mp (noDup_nodup hnbt)).2.2 _ (List.mem_map_of_mem hx) _ hm' rfl
    unfold World.live World.entry
    rw [show (commit E w t posts).trie = commitTrie E w t posts from rfl, commitTrie_cell,
      insertAll_get_of_not_mem hnb,
      insertAll_get_of_mem hnodup (List.mem_map_of_mem (f := Post.pair) hpost)]
  · rw [hc] at hr'; simp at hr'

/-- **The totality at a grant, at the World.** A signed call derived from `w` and admitted to `w'`,
and a grant live in `w`: the turn retired it, kept it, or appended ONE entry to ONE of its ledgers,
`left - u` at the index `i` that `ledgerLeft` read, `0 < u ≤ left`. The cases are exhaustive
because every effect at a cell the pins read as a grant is a retirement or a `spendAt` append
(`effect_at_grant`) and the turn's act at the grant is ONE effect's (`actFor` takes the first).
That it is the turn's only spend of the grant is `duplicateEffect`'s, used by the read-backs
(`effect_reads_back`). -/
theorem grant_turn_cell {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {g : D} {cell : Cell}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') (hl : w.live X.env g = some cell)
    (hk : cell.kind = kindGrant) :
    w'.live X.env g = none ∨ w'.live X.env g = some cell ∨
      ∃ base i left u, LedgerBase base ∧ ledgerLeft base g cell = .ok (i, left) ∧ 0 < u ∧ u ≤ left ∧
        i ≤ ledgerSpendsMax ∧
        w'.live X.env g = some { cell with slots := cell.slots.set (base + i) (countBytes (left - u)) } := by
  obtain ⟨-, hw⟩ := receive_ok_with hr
  obtain ⟨-, d, _k, hd, hs⟩ := receiveWith_sealed hw
  replace hd := derive_of_withTicks hd
  rw [derive_eq] at hd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body with
  | error e => rw [hR] at hd; cases hd
  | ok R =>
  rw [hR] at hd
  simp only [Except.map, Except.ok.injEq] at hd
  subst hd
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  obtain ⟨posts, hck, -⟩ := admit_ok ha
  cases hf : R.1.effects.find? (fun e => decide (e.1 = g)) with
  | none =>
      right; left
      have hframe := admit_frame (c := g) ha (fun x hx hxc => by
        rw [htouch] at hx
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
        simp only at hxc ⊢
        rw [hxc]; unfold actFor; rw [hf]) (live_not_created hck hl)
      unfold World.live; rw [hframe]; exact hl
  | some e =>
      have he := List.mem_of_find?_eq_some hf
      have heg : e.1 = g := by simpa using List.find?_some hf
      obtain ⟨q, hq, hqe⟩ := hpins e he
      have hrk : readKind (pinned X.env w c.unsigned.pins) e.1 kindGrant = .ok cell := by
        have hany : (c.unsigned.pins.any fun p => decide (p.1 = e.1)) = true :=
          List.any_eq_true.mpr ⟨q, hq, by simpa using hqe⟩
        rw [heg] at hany ⊢
        simp [readKind, pinned, hany, hl, hk]
      have hact : actFor R.1.effects g = e.2 := by
        unfold actFor; rw [hf]
      have hx : ({ cell := q.1, seen := q.2, act := actFor R.1.effects q.1 } : Touch D) ∈ t.touches := by
        rw [htouch]; exact List.mem_map_of_mem hq
      rw [hqe, heg, hact] at hx
      rcases effect_at_grant hR he hrk with hret | ⟨base, i, left, u, hb, hll, hu0, hu, hi, hw⟩
      · exact .inl (admit_retired ha hx hret)
      · rw [heg] at hll
        obtain ⟨cell1, post, hc1, hp, hl'⟩ := admit_written ha hx hw
        simp only at hc1 hp hl'
        rw [hl] at hc1
        cases hc1
        refine .inr (.inr ⟨base, i, left, u, hb, hll, hu0, hu, hi, ?_⟩)
        rw [hl', postWrite_eq hp]
        rfl

/-- **What is left at a grant, after a turn** (the read-back, for every turn). A signed call derived
from `w` and admitted to `w'`, over a World whose cells are canonical and whose grants' ledgers are
contiguous, and a grant live in `w`: the turn retired it, or it is a grant in `w'` whose every ledger
reads what it read, or ONE ledger read `(i, left)` and now reads `(i + 1, left - u)`, `0 < u ≤ left`,
every other ledger unchanged (one, by `grant_turn_cell`'s `duplicateEffect`). So what is left only
falls, by exactly what each turn spent. -/
theorem grant_turn_ledger {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {g : D} {cell : Cell}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hl : w.live X.env g = some cell) (hk : cell.kind = kindGrant) :
    w'.live X.env g = none ∨
      ∃ cell', w'.live X.env g = some cell' ∧ cell'.kind = kindGrant ∧
        ((∀ b, LedgerBase b → ledgerLeft b g cell' = ledgerLeft b g cell) ∨
          ∃ base i left u, LedgerBase base ∧ ledgerLeft base g cell = .ok (i, left) ∧ 0 < u ∧ u ≤ left ∧
            ledgerLeft base g cell' = .ok (i + 1, left - u) ∧
            ∀ b, LedgerBase b → b ≠ base → ledgerLeft b g cell' = ledgerLeft b g cell) := by
  rcases grant_turn_cell hr ha hl hk with hn | hs | ⟨base, i, left, u, hb, hll, hu0, hu, hi, hw'⟩
  · exact .inl hn
  · exact .inr ⟨cell, hs, hk, .inl fun _ _ => rfl⟩
  · obtain ⟨h1, h2, -, -⟩ := ledgerLeft_append hb (hcan g cell hl) (hlc g cell hl hk) hll hi hu
    exact .inr ⟨_, hw', hk, .inr ⟨base, i, left, u, hb, hll, hu0, hu, h1, h2⟩⟩

/-! ## The invariant, along every honest step -/

/-- **Derive-then-admit keeps every grant's ledgers contiguous** (given canonical cells). -/
theorem step_ledgerContiguous {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w') : LedgerContiguous X.env w' := by
  intro id c' hl hk
  rcases admit_live ha hl with hb | ⟨cell, hold, hc'⟩
  · obtain ⟨d, hd, hcr⟩ := receiveWith_born (receive_ok_with hr).2
    rw [hcr] at hb
    exact derive_born_grant hd _ hb hk
  · have hk0 : cell.kind = kindGrant := by
      rcases hc' with rfl | ⟨ops, hp⟩
      · exact hk
      · rw [← (postWrite_keeps hp).1]; exact hk
    rcases grant_turn_cell hr ha hold hk0 with hn | hs | ⟨base, i, left, u, hb, hll, -, hu, hi, hw'⟩
    · rw [hn] at hl; cases hl
    · rw [← Option.some.inj (hs.symm.trans hl)]; exact hlc id cell hold hk0
    · rw [← Option.some.inj (hw'.symm.trans hl)]
      exact (ledgerLeft_append hb (hcan id cell hold) (hlc id cell hold hk0) hll hi hu).2.2.2

/-- **The Host keeps every grant's ledgers contiguous**: every committed submission. -/
theorem submit_ledgerContiguous {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (h : submit X w c = .ok (t, w')) : LedgerContiguous X.env w' := by
  obtain ⟨_, hr, ha⟩ := submit_ok h
  exact step_ledgerContiguous hcan hlc hr ha

/-- **Every honest folded log keeps every grant's ledgers contiguous**, canonical cells carried
along: so every World a follower reaches from genesis (`genesis_cellsCanon`,
`genesis_ledgerContiguous`). -/
theorem honest_ledgerContiguous {X : Ctx D} :
    ∀ {w w' : World D} {l : List (Step D)}, CellsCanon X.env w → LedgerContiguous X.env w →
      World.fold X.env w l = .ok w' → Honest X w l → CellsCanon X.env w' ∧ LedgerContiguous X.env w'
  | w, w', [], hcan, hlc, hf, _ => by
      simp only [World.fold, Except.ok.injEq] at hf; subst hf; exact ⟨hcan, hlc⟩
  | w, w', .refusal r :: rest, hcan, hlc, hf, hh => by
      obtain ⟨w₁, hs, -, hfr, hhr⟩ := fold_honest_cons hf hh
      have hrf : World.refuse X.env w r = .ok w₁ := hs
      exact honest_ledgerContiguous
        (fun id cell hl => hcan id cell ((refuse_live hrf id).symm.trans hl))
        (fun id cell hl => hlc id cell ((refuse_live hrf id).symm.trans hl)) hfr hhr
  | w, w', .turn t :: rest, hcan, hlc, hf, hh => by
      obtain ⟨w₁, hadm, ⟨c, -, hr, -⟩, hfr, hhr⟩ := fold_honest_cons hf hh
      exact honest_ledgerContiguous (admit_cellsCanon hcan hadm)
        (step_ledgerContiguous hcan hlc hr hadm) hfr hhr


/-! ## A spend reads back its amount -/

/-- A write the call's tree derived is THE act at its cell (`duplicateEffect`: effects name distinct
cells), so the admitted World holds there what `postWrite` makes of the cell the turn observed. -/
private theorem effect_written {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {cr : List (D × Cell)} {efs : List (D × Act)} {ns : List D} {rs : List (RowSlot D × RowAct)}
    {k : Nat} (hs : sealTurn X c cr efs ns rs k = .ok t) (ha : World.admit X.env w t = .ok w')
    {k : D} {ops : List Op} (he : (k, Act.write ops) ∈ efs) :
    ∃ cell post, w.live X.env k = some cell ∧ postWrite k cell ops = .ok post ∧ w'.live X.env k = some post := by
  obtain ⟨-, -, htouch, -, -, -, -, -, -, hpins⟩ := sealTurn_ok hs
  have hnd := firstDup_none (sealTurn_firstDup hs)
  obtain ⟨q, hq, hqe⟩ := hpins _ he
  have hx : ({ cell := q.1, seen := q.2, act := actFor efs q.1 } : Touch D) ∈ t.touches := by
    rw [htouch]; exact List.mem_map_of_mem hq
  have hqe' : q.1 = k := hqe
  rw [hqe', actFor_of_nodup hnd he] at hx
  exact admit_written ha hx rfl

/-- An append the call's tree derived at a grant is THE act at it (`duplicateEffect`), and reads back
as `(i + 1, left - u)`. -/
private theorem effect_reads_back {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D}
    {cr : List (D × Cell)} {efs : List (D × Act)} {ns : List D} {rs : List (RowSlot D × RowAct)}
    {k : Nat} (hs : sealTurn X c cr efs ns rs k = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    {g : D} {gc : Cell} {base i left u : Nat} (hb : LedgerBase base)
    (hg : readKind (pinned X.env w c.unsigned.pins) g kindGrant = .ok gc) (hll : ledgerLeft base g gc = .ok (i, left))
    (hi : i ≤ ledgerSpendsMax) (hu : u ≤ left)
    (he : (g, Act.write [.set (base + i) (countBytes (left - u))]) ∈ efs) :
    ∃ gc', w.live X.env g = some gc ∧ w'.live X.env g = some gc' ∧ ledgerLeft base g gc' = .ok (i + 1, left - u) := by
  obtain ⟨cell1, post, hc1, hp, hl'⟩ := effect_written hs ha he
  have hlg := pinned_live (readKind_ok hg).1
  have hkg := (readKind_ok hg).2
  obtain rfl : gc = cell1 := Option.some.inj (hlg.symm.trans hc1)
  refine ⟨_, hlg, hl', ?_⟩
  rw [postWrite_eq hp]
  exact (ledgerLeft_append hb (hcan g gc hlg) (hlc g gc hlg hkg) hll hi hu).1

omit [Std.TransOrd D] [Std.LawfulEqOrd D] in
/-- The signed call's top Draft and its seal, from a derivation. -/
private theorem receive_top {X : Ctx D} {w : World D} {c : Call D} {t : Turn D}
    (hr : receive X w c = .ok t) :
    ∃ R, dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
        (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
        ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body = .ok R ∧
      sealTurn X c R.1.creates R.1.effects R.1.nullifiers R.1.rows (poolOf c.unsigned.body - R.2.pool) = .ok t := by
  obtain ⟨-, hw⟩ := receive_ok_with hr
  obtain ⟨-, d, k, hdd, hs⟩ := receiveWith_sealed hw
  unfold deriveWithTicks at hdd
  cases hR : dispatch X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c
      (tree X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c Bounds.callDepthMax)
      ⟨[], poolOf c.unsigned.body, 0⟩ c.unsigned.member none c.unsigned.body with
  | error e => rw [hR] at hdd; cases hdd
  | ok R =>
      rw [hR] at hdd
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hdd
      obtain ⟨rfl, rfl⟩ := hdd
      exact ⟨R, rfl, hs⟩

/-- **A transfer through a grant reads back its amount, at any depth** (LEDGER-7's link). A signed
call derived from `w` and admitted to `w'`, over canonical cells and contiguous ledgers, whose walk
dispatched a transfer through `g` (the signed one, or one an object's run called): `g`'s transfer
ledger read `(i, left)` with `amount ≤ left`, and now reads `(i + 1, left - amount)`. -/
theorem spend_reads_back_dispatched {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {n : Nat}
    {wk : Walk D} {actor : D} {caller : Option D} {srcR dstR : AcctRef D} {amount : Nat} {g : D} {once : Option ByteArray}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hd : Dispatched X w c n wk actor caller (.transfer srcR dstR amount (some g) once)) :
    ∃ gc gc' i left, w.live X.env g = some gc ∧ ledgerLeft transferBase g gc = .ok (i, left) ∧
      amount ≤ left ∧ w'.live X.env g = some gc' ∧ ledgerLeft transferBase g gc' = .ok (i + 1, left - amount) := by
  obtain ⟨R, hR, hs⟩ := receive_top hr
  obtain ⟨r, hr', l₁, l₂, hl⟩ := dispatched_ok hR hd
  simp only [dispatch] at hr'
  have hdr := stepped_draft hr'
  generalize r.1 = d at hdr hl
  obtain ⟨_, _, _, _, _, spend, -, -, -, -, hpos, -, -, -, hsp, rfl⟩ := transfer_ok hdr
  rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
  · cases h0
  · cases hg'
    obtain ⟨i, left, hll, hu, hc⟩ := spendAt_ok hsa
    rcases hc with ⟨h0, -⟩ | ⟨-, hi, rfl⟩
    · omega
    · have he : (g, Act.write [.set (transferBase + i) (countBytes (left - amount))]) ∈ R.1.effects := by
        rw [hl]; simp
      obtain ⟨gc', hlg, hl', hback⟩ := effect_reads_back hs ha hcan hlc (.inr (.inl rfl)) hgc hll hi hu he
      exact ⟨gc, gc', i, left, hlg, hll, hu, hl', hback⟩

/-- **A signed transfer through a grant reads back its amount**: `spend_reads_back_dispatched` at the
walk's root. -/
theorem spend_reads_back {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {srcR dstR : AcctRef D}
    {amount : Nat} {g : D} {once : Option ByteArray}
    (hb : c.unsigned.body = .transfer srcR dstR amount (some g) once)
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w) :
    ∃ gc gc' i left, w.live X.env g = some gc ∧ ledgerLeft transferBase g gc = .ok (i, left) ∧
      amount ≤ left ∧ w'.live X.env g = some gc' ∧ ledgerLeft transferBase g gc' = .ok (i + 1, left - amount) := by
  have hroot := Dispatched.root (X := X) (w := w) (c := c)
  rw [hb] at hroot
  exact spend_reads_back_dispatched hr ha hcan hlc hroot

/-- **A credit line through a grant reads back its amount, at any depth**: the credit ledger's twin
of `spend_reads_back_dispatched`. -/
theorem credit_reads_back_dispatched {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {n : Nat}
    {wk : Walk D} {actor : D} {caller : Option D} {well : D} {acctR : AcctRef D} {amount : Nat} {g : D}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w)
    (hd : Dispatched X w c n wk actor caller (.credit well acctR amount (some g))) :
    ∃ gc gc' i left, w.live X.env g = some gc ∧ ledgerLeft creditBase g gc = .ok (i, left) ∧
      amount ≤ left ∧ w'.live X.env g = some gc' ∧ ledgerLeft creditBase g gc' = .ok (i + 1, left - amount) := by
  obtain ⟨R, hR, hs⟩ := receive_top hr
  obtain ⟨r, hr', l₁, l₂, hl⟩ := dispatched_ok hR hd
  simp only [dispatch] at hr'
  have hdr := stepped_draft hr'
  generalize r.1 = d at hdr hl
  obtain ⟨_, _, _, _, _, spend, -, -, -, -, -, hpos, -, -, -, hsp, rfl⟩ := credit_ok hdr
  rcases spendVia_ok hsp with ⟨h0, -⟩ | ⟨g', gc, hg', hgc, hsa⟩
  · cases h0
  · cases hg'
    obtain ⟨i, left, hll, hu, hc⟩ := spendAt_ok hsa
    rcases hc with ⟨h0, -⟩ | ⟨-, hi, rfl⟩
    · omega
    · have he : (g, Act.write [.set (creditBase + i) (countBytes (left - amount))]) ∈ R.1.effects := by
        rw [hl]; simp
      obtain ⟨gc', hlg, hl', hback⟩ := effect_reads_back hs ha hcan hlc (.inr (.inr rfl)) hgc hll hi hu he
      exact ⟨gc, gc', i, left, hlg, hll, hu, hl', hback⟩

/-- **A transfer moves exactly its amount, at any depth** (the balance half of `transfer_exact`, for a
transfer the walk dispatched: the signed one, or one an object's run called). A signed call derived
from `w` and admitted to `w'`: the source account's value falls by `amount` and the destination's
rises by it, each keeping its denomination and floor. Each write is THE act at its cell
(`duplicateEffect`), so no other receiver of the same tree moved either balance in this turn. -/
theorem transfer_reads_back_dispatched {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {n : Nat}
    {wk : Walk D} {actor : D} {caller : Option D} {srcR dstR : AcctRef D} {amount : Nat} {via : Option D} {once : Option ByteArray}
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hd : Dispatched X w c n wk actor caller (.transfer srcR dstR amount via once)) :
    ∃ sv dv, (w.live X.env (srcR.resolve X)).bind Value.ofCell = some sv ∧
      (w.live X.env (dstR.resolve X)).bind Value.ofCell = some dv ∧
      (w'.live X.env (srcR.resolve X)).bind Value.ofCell = some { sv with balance := sv.balance - amount } ∧
      (w'.live X.env (dstR.resolve X)).bind Value.ofCell = some { dv with balance := dv.balance + amount } := by
  obtain ⟨R, hR, hs⟩ := receive_top hr
  obtain ⟨r, hr', l₁, l₂, hl⟩ := dispatched_ok hR hd
  simp only [dispatch] at hr'
  have hdr := stepped_draft hr'
  generalize r.1 = d at hdr hl
  obtain ⟨scell, sv, dcell, dv, _, _, hsr, hdr', -, -, -, -, hfs, hfd, -, rfl⟩ := transfer_ok hdr
  obtain ⟨-, hsr, -⟩ := readRef_ok hsr
  obtain ⟨-, hdr', -⟩ := readRef_ok hdr'
  obtain ⟨hks, hvs⟩ := readAccount_ok hsr
  obtain ⟨hkd, hvd⟩ := readAccount_ok hdr'
  have hls := pinned_live (readKind_ok hks).1
  have hld := pinned_live (readKind_ok hkd).1
  have hes : (srcR.resolve X, Act.write [.set Value.balanceKey (Value.balanceBytes (sv.balance - amount))]) ∈
      R.1.effects := by rw [hl]; simp [setBalance]
  have hed : (dstR.resolve X, Act.write [.set Value.balanceKey (Value.balanceBytes (dv.balance + amount))]) ∈
      R.1.effects := by rw [hl]; simp [setBalance]
  obtain ⟨c1, p1, hc1, hw1, hl1⟩ := effect_written hs ha hes
  obtain ⟨c2, p2, hc2, hw2, hl2⟩ := effect_written hs ha hed
  rw [hls] at hc1; cases hc1
  rw [hld] at hc2; cases hc2
  refine ⟨sv, dv, by rw [hls]; exact hvs, by rw [hld]; exact hvd, ?_, ?_⟩
  · rw [hl1, postWrite_eq hw1]; exact ofCell_setBalance hvs hfs
  · rw [hl2, postWrite_eq hw2]; exact ofCell_setBalance hvd hfd

/-- **A signed credit line through a grant reads back its amount.** -/
theorem credit_reads_back {X : Ctx D} {w w' : World D} {c : Call D} {t : Turn D} {well : D}
    {acctR : AcctRef D} {amount : Nat} {g : D}
    (hb : c.unsigned.body = .credit well acctR amount (some g))
    (hr : receive X w c = .ok t) (ha : World.admit X.env w t = .ok w')
    (hcan : CellsCanon X.env w) (hlc : LedgerContiguous X.env w) :
    ∃ gc gc' i left, w.live X.env g = some gc ∧ ledgerLeft creditBase g gc = .ok (i, left) ∧
      amount ≤ left ∧ w'.live X.env g = some gc' ∧ ledgerLeft creditBase g gc' = .ok (i + 1, left - amount) := by
  have hroot := Dispatched.root (X := X) (w := w) (c := c)
  rw [hb] at hroot
  exact credit_reads_back_dispatched hr ha hcan hlc hroot

end Turn

/-! ## Teeth -/

/-- Two spends of one grant (5) in one call's effects: both read the same ledger, so both write its
next key. -/
private def twoSpends : List (Nat × Act) :=
  [(5, .write [.set transferBase (countBytes 7)]), (5, .write [.set transferBase (countBytes 4)])]

/-- **One append per turn is the seal's, not an accident.** Two spends of one grant in one call
tree: the act `actFor` would hand the grant is the FIRST (the second spend silently dropped), and
`sealTurn`'s `effectsPinned` refuses the pair `duplicateEffect`, so `grant_turn_cell`'s single
append is exhaustive. -/
theorem two_spends_refused :
    actFor twoSpends 5 = .write [.set transferBase (countBytes 7)] ∧
      effectsPinned [(5, 5)] twoSpends = .error (.duplicateEffect 5) :=
  ⟨rfl, rfl⟩

/-- A grant whose transfer ledger has a gap: entries at `transferBase` and `transferBase + 4`. -/
private def gapCell : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := [(transferBase, countBytes 10), (transferBase + 4, countBytes 10)] }

/-- **With a gap, the cap never falls** (`LedgerContiguous` is load-bearing). The ledger reads 2
entries, 10 left; a spend of all 10 is within it and writes `transferBase + 2`, a key the cell does
not hold (so `appendOnly` admits it); the ledger then reads 3 entries, STILL 10 left (its last key
is `transferBase + 4`); a second spend of 10 writes `transferBase + 3`, also absent; and the ledger
reads 10 left again: two spends of 10, each admitted against a cap of 10. -/
theorem gap_never_falls :
    ¬ GrantContiguous gapCell ∧
      spendAt (D := Nat) transferBase 0 gapCell 10 (.transferSpent 0) =
        .ok (some (0, .write [.set (transferBase + 2) (countBytes 0)])) ∧
      gapCell.slots.get (transferBase + 2) = none ∧
      spendAt (D := Nat) transferBase 0
          { gapCell with slots := gapCell.slots.set (transferBase + 2) (countBytes 0) } 10 (.transferSpent 0) =
        .ok (some (0, .write [.set (transferBase + 3) (countBytes 0)])) ∧
      (gapCell.slots.set (transferBase + 2) (countBytes 0)).get (transferBase + 3) = none ∧
      ledgerLeft (D := Nat) transferBase 0
          { gapCell with
            slots := (gapCell.slots.set (transferBase + 2) (countBytes 0)).set (transferBase + 3) (countBytes 0) } =
        .ok (4, 10) :=
  ⟨fun h => absurd (h transferBase (.inr (.inl rfl))) (by decide), rfl, rfl, rfl, rfl, rfl⟩

/-- **No World holding a gapped grant is `LedgerContiguous`.** -/
theorem gap_world_not_contiguous {E : Env D} {w : World D} {g : D} (h : w.live E g = some gapCell) :
    ¬ LedgerContiguous E w :=
  fun hc => gap_never_falls.1 (hc g gapCell h rfl)

end Nanodregg.Kernel.Receive
