/-
# Lang.Proofs.StdQuorum — what a quorum commit means over its history

`quorum_change_needs_k` reads one admitted change: a commit of the guarded field needs `k ≤ popcount`
of the approvals mask in the state before it, and that state's proposal is `set` of the new value.
A mask is a number. What a reader of a quorum wants is people: `k` distinct members, each of whom
signed an admitted approval of exactly the proposal that was committed, before the commit.

`quorum_commit_attested` proves that over every history of the law (`Chain (Step lib (quorumLaw …))`)
from a state with no approvals (what a birth and an adoption leave: `quorum_birth_empty`,
`quorum_adopt_fresh`), for distinct members. The proof is one invariant (`Attested`): every bit set
in the approvals of a reached state was set by an approval step of that bit's member, over the
proposal the state holds. A proposal change and a commit reset the approvals; a no-op keeps both
fields; an approval sets one unset bit and is its own witness; a relaw keeps the state.
-/
import Lang.Proofs.StdChain

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

variable {lib : List Term}

theorem pow2_eq (i : Nat) : pow2 i = 2 ^ i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow2, ih, Nat.pow_succ, Nat.mul_comm]

/-- Setting an unset bit `i` changes bit `i` to one and no other bit. -/
theorem bit_add_pow2 {a i j : Nat} (h : a / pow2 i % 2 = 0) :
    (a + pow2 i) / pow2 j % 2 = if j = i then 1 else a / pow2 j % 2 := by
  rw [pow2_eq] at h
  rw [pow2_eq, pow2_eq]
  rcases Nat.lt_trichotomy j i with hj | rfl | hj
  · have hs : 2 ^ i = 2 ^ j * 2 ^ (i - j) := by rw [← Nat.pow_add]; congr 1; omega
    have he : 2 ^ (i - j) % 2 = 0 := by
      obtain ⟨d, hd⟩ : ∃ d, i - j = d + 1 := ⟨i - j - 1, by omega⟩
      rw [hd, Nat.pow_succ]; simp
    rw [if_neg (by omega), hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    omega
  · rw [if_pos rfl, Nat.add_div_right _ (Nat.two_pow_pos _)]
    omega
  · have hs : 2 ^ j = 2 ^ i * (2 * 2 ^ (j - i - 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
    rw [if_neg (by omega), hs, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ (Nat.two_pow_pos _)]
    have : (a / 2 ^ i + 1) / 2 = a / 2 ^ i / 2 := by omega
    rw [this]

/-- `popcountNat` counts the set bits. -/
theorem popcount_foldl (a : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc i => acc + a / pow2 i % 2) acc = acc + (l.filter (fun i => a / pow2 i % 2 == 1)).length
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, popcount_foldl a l, List.filter_cons]
    have : a / pow2 x % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hx : a / pow2 x % 2 = 1
    · simp [hx]; omega
    · have h0 : a / pow2 x % 2 = 0 := by omega
      simp [h0]

/-- The members whose bits are set in `a`, in member order. -/
def setMembers (ms : List ByteArray) (a : Nat) : List ByteArray :=
  (ms.zipIdx.filter (fun p => a / pow2 p.2 % 2 == 1)).map Prod.fst

theorem setMembers_sublist (ms : List ByteArray) (a : Nat) : (setMembers ms a).Sublist ms := by
  have h1 : (ms.zipIdx.filter (fun p : ByteArray × Nat => a / pow2 p.2 % 2 == 1)).Sublist ms.zipIdx :=
    List.filter_sublist
  have := h1.map Prod.fst
  simpa [setMembers, List.zipIdx_map_fst] using this

theorem setMembers_length (ms : List ByteArray) (a : Nat) :
    (setMembers ms a).length = popcountNat a ms.length := by
  have hs : ms.zipIdx.map Prod.snd = List.range ms.length := by
    rw [List.zipIdx_map_snd, List.range_eq_range']
  have hf := congrArg List.length
    (List.filter_map (f := Prod.snd) (p := fun i => a / pow2 i % 2 == 1) (l := ms.zipIdx))
  rw [hs, List.length_map] at hf
  simp only [setMembers, List.length_map, popcountNat, popcount_foldl, Nat.zero_add, hf]
  rfl

theorem mem_setMembers {ms : List ByteArray} {a : Nat} {m : ByteArray} (h : m ∈ setMembers ms a) :
    ∃ i, ms[i]? = some m ∧ a / pow2 i % 2 = 1 := by
  simp only [setMembers, List.mem_map, List.mem_filter] at h
  obtain ⟨⟨m', i⟩, ⟨hm, hb⟩, rfl⟩ := h
  exact ⟨i, List.mem_zipIdx_iff_getElem?.1 hm, by simpa using hb⟩

/-- Step `(o', (rq, n))` is member `m`'s approval of proposal `P`: a write or invoke signed by `m`
that keeps the proposal at `P` and sets `m`'s own bit, which was unset. -/
def Approves (ms : List ByteArray) (m : ByteArray) (P : Data) (t : Data × Data × Data) : Prop :=
  (∃ ℓ x, t.2.1.field "occasion" = some (.inj ℓ x) ∧ (ℓ = "write" ∨ ℓ = "invoke")) ∧
  t.2.1.field "agent" = some (.digest m) ∧
  t.1.field "proposal" = some P ∧ t.2.2.field "proposal" = some P ∧
  ∃ i a, ms[i]? = some m ∧ t.1.field "approvals" = some (.nat a) ∧ a / pow2 i % 2 = 0 ∧
    t.2.2.field "approvals" = some (.nat (a + pow2 i))

/-- Every set bit of `s`'s approvals is attested in `H` by its member's approval of `s`'s proposal. -/
def Attested (ms : List ByteArray) (H : List (Data × Data × Data)) (s : Data) : Prop :=
  ∀ a, s.field "approvals" = some (.nat a) → ∀ i m, ms[i]? = some m → a / pow2 i % 2 = 1 →
    ∀ P, s.field "proposal" = some P → ∃ t ∈ H, Approves ms m P t

theorem attested_zero {ms : List ByteArray} {H : List (Data × Data × Data)} {s : Data}
    (h : s.field "approvals" = some (.nat 0)) : Attested ms H s := by
  intro a ha i m _ hb
  rw [h] at ha; cases ha
  simp at hb

theorem attested_mono {ms : List ByteArray} {H : List (Data × Data × Data)} {s : Data}
    (X : List (Data × Data × Data)) (h : Attested ms H s) : Attested ms (H ++ X) s := by
  intro a ha i m hm hb P hP
  obtain ⟨t, ht, hA⟩ := h a ha i m hm hb P hP
  exact ⟨t, List.mem_append_left _ ht, hA⟩

/-- One step of the law keeps the invariant, the step itself joining the history. -/
theorem attested_step {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label}
    {H : List (Data × Data × Data)} {rq n o : Data}
    (hs : Step lib (quorumLaw S T ms k g) rq n o) (h : Attested ms H o) :
    Attested ms (H ++ [(o, (rq, n))]) n := by
  obtain ⟨ℓ, x, hocc, hℓ⟩ := lawOf6_occasion hs.1
  have hchange : ℓ = "write" ∨ ℓ = "invoke" → Attested ms (H ++ [(o, (rq, n))]) n := by
    intro hl
    obtain ⟨-, -, ng, og, hn, ho, hcase⟩ := quorum_change hs.1 hocc hl
    rcases hcase with ⟨-, -, -, h0⟩ | ⟨-, np, op, hnp, hop, hc⟩
    · exact attested_zero h0
    rcases hc with ⟨-, h0⟩ | ⟨he, a, hna, hoa⟩ | ⟨he, i, m, a, hmi, hag, hoa, hbit, hna⟩
    · exact attested_zero h0
    · subst he
      intro a' ha' j m' hm' hb P hP
      rw [hna] at ha'; cases ha'
      rw [hnp] at hP; cases hP
      exact attested_mono _ h a hoa j m' hm' hb _ hop
    · subst he
      intro a' ha' j m' hm' hb P hP
      rw [hna] at ha'; cases ha'
      rw [hnp] at hP; cases hP
      rw [bit_add_pow2 hbit] at hb
      by_cases hji : j = i
      · subst hji
        rw [hmi] at hm'; cases hm'
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          ⟨ℓ, x, hocc, hl⟩, hag, hop, hnp, j, a, hmi, hoa, hbit, hna⟩
      · rw [if_neg hji] at hb
        exact attested_mono _ h a hoa j m' hm' hb _ hop
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact attested_zero (quorum_adopt_fresh hs.1 hocc)
  · exact attested_zero (quorum_birth_empty hs.1 hocc)
  · exact hchange (.inr rfl)
  · rw [hs.2 _ _ hocc (.inl rfl)]; exact attested_mono _ h
  · exact (quorum_retire_refused hocc hs.1).elim
  · exact hchange (.inl rfl)

theorem commit_attested_go {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} (hms : ms.Nodup)
    {o : Data} {steps : List (Data × Data)} (h : Chain (Step lib (quorumLaw S T ms k g)) o steps) :
    ∀ (H pre post : List (Data × Data × Data)) (o' rq n : Data), Attested ms H o →
      (o :: steps.map Prod.snd).zip steps = pre ++ (o', (rq, n)) :: post →
      (∃ ℓ x, rq.field "occasion" = some (.inj ℓ x) ∧ (ℓ = "write" ∨ ℓ = "invoke")) →
      n.field g ≠ o'.field g →
      ∃ ng, n.field g = some ng ∧ o'.field "proposal" = some (.inj "set" ng) ∧
        ∃ M : List ByteArray, M.Nodup ∧ M.Sublist ms ∧ k ≤ M.length ∧
          ∀ m ∈ M, ∃ t ∈ H ++ pre, Approves ms m (.inj "set" ng) t := by
  induction h with
  | nil => intro H pre post o' rq n _ hz; cases pre <;> simp at hz
  | @cons o rq₀ n₀ rest hs _ ih =>
    intro H pre post o' rq n hH hz hocc hchg
    simp only [List.map_cons, List.zip_cons_cons] at hz
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hz
      obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := hz
      obtain ⟨ℓ, x, ho, hl⟩ := hocc
      obtain ⟨ng, hn, ⟨a, ha, hk⟩, hp, -⟩ := quorum_change_needs_k hs.1 ho hl hchg
      refine ⟨ng, hn, hp, setMembers ms a, hms.sublist (setMembers_sublist ms a),
        setMembers_sublist ms a, by rw [setMembers_length]; exact hk, fun m hm => ?_⟩
      obtain ⟨i, hmi, hb⟩ := mem_setMembers hm
      obtain ⟨t, ht, hA⟩ := hH a ha i m hmi hb _ hp
      exact ⟨t, by simpa using ht, hA⟩
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hz
      obtain ⟨rfl, hz'⟩ := hz
      obtain ⟨ng, hn, hp, M, hnd, hsub, hk, hM⟩ :=
        ih (H ++ [(o, (rq₀, n₀))]) pre' post o' rq n (attested_step hs hH) hz' hocc hchg
      refine ⟨ng, hn, hp, M, hnd, hsub, hk, fun m hm => ?_⟩
      obtain ⟨t, ht, hA⟩ := hM m hm
      exact ⟨t, by simpa using ht, hA⟩

/-- **What a quorum commit means.** Along any history of `quorumLaw S T ms k g` from a state with no
approvals, over distinct members: every admitted write or invoke that changes the guarded field `g`
sets it to a value `ng` the state before it proposed (`set ng`), and at least `k` distinct members
(a sublist of `ms`) each signed, in an earlier step of the same history, an approval of exactly
`set ng` (their own unset bit set, the proposal kept at `set ng`). -/
theorem quorum_commit_attested {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} (hms : ms.Nodup)
    {o : Data} {steps : List (Data × Data)} (h : Chain (Step lib (quorumLaw S T ms k g)) o steps)
    (h0 : o.field "approvals" = some (.nat 0))
    {pre post : List (Data × Data × Data)} {o' rq n : Data}
    (hz : (o :: steps.map Prod.snd).zip steps = pre ++ (o', (rq, n)) :: post)
    (hocc : ∃ ℓ x, rq.field "occasion" = some (.inj ℓ x) ∧ (ℓ = "write" ∨ ℓ = "invoke"))
    (hchg : n.field g ≠ o'.field g) :
    ∃ ng, n.field g = some ng ∧ o'.field "proposal" = some (.inj "set" ng) ∧
      ∃ M : List ByteArray, M.Nodup ∧ M.Sublist ms ∧ k ≤ M.length ∧
        ∀ m ∈ M, ∃ t ∈ pre, Approves ms m (.inj "set" ng) t := by
  simpa using commit_attested_go hms h [] pre post o' rq n (attested_zero h0) hz hocc hchg

end Nanodregg.Lang.Std
