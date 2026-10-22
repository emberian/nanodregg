/-
# Lang.Proofs.StdFits — every stdlib law at its cap has a text the reader reads

The reader's fuel counts nesting only (`Read.depthMax`), and a list holds at most `Read.listMax`
elements. A stdlib law's long parts are chains one level deep per item (`anyOf` over members, ids or
edges; `popcount` over mask bits), so a law's depth grows with its parameter, and each generator
caps it (`Std.membersMax`, `Std.idsMax`, `Std.edgesMax`). The theorems here bound the printed form:
`quorumLaw_prints`, `allowlistLaw_prints`, `machineLaw_prints` give the depth as a function of the
parameter and of the state type's own depth, and `quorum_text`, `allowlist_text`, `machine_text`
say that whatever the CHECKED generator emits over a state type a package can carry has a text (`Print.term` is `some`), so the round trip `readTerm_term` applies to it.

The constructor bounds (`Prints`, `prints_ite`, …) are `Lang.Proofs.Prints`; the Std combinator
lemmas here compose them.
-/
import Lang.Proofs.Prints
import Lang.Proofs.Row
import Lang.Std
import Lang.Proofs.Std
import Lang.Proofs.Print

namespace Nanodregg.Lang.Print

open Read (listMax depthMax)
open Wire (labelOk)

/-! ## The stdlib's pieces -/

open Std

theorem verdictTy_prints : TyPrints 4 verdictTy :=
  ⟨_, (Option.some_get (by decide : (tySx verdictTy).isSome = true)).symm, by decide, by decide⟩

theorem reqTy_prints : TyPrints 6 reqTy :=
  ⟨_, (Option.some_get (by decide : (tySx reqTy).isSome = true)).symm, by decide, by decide⟩

theorem okT_prints (k : Nat) : Prints 5 k okT :=
  prints_inj verdictTy_prints (by decide) ((prints_record (N := 1) (fs := []) arms_nil (by decide)).mono (by omega))

theorem refusedT_prints (k : Nat) (w : String) : Prints 5 k (refusedT w) :=
  prints_inj verdictTy_prints (by decide) ((prints_bytes k _).mono (by omega))

theorem guard_prints {N k : Nat} {c r : Term} (w : String) (hc : Prints N k c) (hr : Prints N k r) (h4 : 5 ≤ N) :
    Prints (N + 1) k (guard c w r) :=
  prints_ite hc hr ((refusedT_prints k w).mono h4)

theorem guards_prints {N k : Nat} : ∀ {l : List (Term × String)} {r : Term}, (∀ p ∈ l, Prints N k p.1) →
    Prints N k r → 5 ≤ N → Prints (N + l.length) k (guards l r)
  | [], r, _, hr, _ => by simpa [guards] using hr
  | (c, w) :: l, r, hl, hr, h4 => by
    have ih := guards_prints (l := l) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hr h4
    have hc := (hl (c, w) (List.mem_cons_self ..)).mono (M := N + l.length) (by omega)
    simp only [guards, List.length_cons]
    exact (guard_prints w hc ih (by omega)).mono (by omega)

theorem allOf_prints {N k : Nat} {l : List (Term × String)} (hl : ∀ p ∈ l, Prints N k p.1) (h4 : 5 ≤ N) :
    Prints (N + l.length) k (allOf l) :=
  guards_prints hl ((okT_prints k).mono h4) h4

theorem allOf1_prints {N k : Nat} {c : Term} {w : String} (hc : Prints N k c) (h4 : 5 ≤ N) :
    Prints (N + 1) k (allOf [(c, w)]) :=
  allOf_prints (by simpa using hc) h4

theorem andT_prints {N k : Nat} {a b : Term} (ha : Prints N k a) (hb : Prints N k b) : Prints (N + 1) k (andT a b) :=
  prints_ite ha hb ((prints_bool k false).mono ha.pos)

theorem notT_prints {N k : Nat} {a : Term} (ha : Prints N k a) : Prints (N + 1) k (notT a) :=
  prints_ite ha ((prints_bool k false).mono ha.pos) ((prints_bool k true).mono ha.pos)

theorem anyOf_prints {N k : Nat} : ∀ {l : List Term}, (∀ c ∈ l, Prints N k c) → 1 ≤ N →
    Prints (N + l.length) k (anyOf l)
  | [], _, h1 => (prints_bool k false).mono (by simpa using h1)
  | c :: l, hl, h1 => by
    have ih := anyOf_prints (l := l) (fun c hc => hl c (List.mem_cons_of_mem _ hc)) h1
    have hc := (hl c (List.mem_cons_self ..)).mono (M := N + l.length) (by omega)
    simp only [anyOf, List.length_cons]
    exact (prints_ite hc ((prints_bool k true).mono (by omega)) ih).mono (by omega)

theorem oldF_prints {a : At} {k : Nat} {f : Label} (hk : a.depth + 3 ≤ k) (hf : labelOk f = true) :
    Prints 2 k (a.oldF f) := prints_get (t := .var (a.depth + 2)) (prints_var (by omega)) hf

theorem newF_prints {a : At} {k : Nat} {f : Label} (hk : a.depth + 3 ≤ k) (hf : labelOk f = true) :
    Prints 2 k (a.newF f) := prints_get (t := .var (a.depth + 1)) (prints_var (by omega)) hf

theorem reqF_prints {a : At} {k : Nat} {f : Label} (hk : a.depth + 3 ≤ k) (hf : labelOk f = true) :
    Prints 2 k (a.reqF f) := prints_get (t := .var a.depth) (prints_var (by omega)) hf

theorem payload_prints {a : At} {k : Nat} (hk : a.depth + 3 ≤ k) : Prints 1 k a.payload :=
  prints_var (i := a.depth - 1) (by omega)

theorem eqAt_prints {N k : Nat} {x y : Term} (T : Ty) (hx : Prints N k x) (hy : Prints N k y) :
    Prints (N + 1) k (eqAt T x y) := by
  unfold eqAt; split
  · exact prints_prim _ hx hy
  · split
    · exact prints_prim _ hx hy
    · exact prints_prim _ hx hy

theorem bit_prints {N k : Nat} {t : Term} (i : Nat) (ht : Prints N k t) : Prints (N + 2) k (bit t i) :=
  prints_prim .mod (prints_prim .div ht ((prints_nat k _).mono ht.pos)) ((prints_nat k _).mono (by have := ht.pos; omega))

theorem foldl_add_prints {N P k : Nat} {t : Term} (ht : Prints N k t) :
    ∀ (l : List Nat) {acc : Term}, Prints P k acc →
    Prints (max P (N + 2) + l.length) k (l.foldl (fun acc i => .prim .add acc (bit t i)) acc)
  | [], acc, h => h.mono (by simp only [List.length_nil]; omega)
  | i :: l, acc, h => by
    have step : Prints (max P (N + 2) + 1) k (.prim .add acc (bit t i)) :=
      prints_prim .add (h.mono (by omega)) ((bit_prints i ht).mono (by omega))
    have := foldl_add_prints ht l step
    simp only [List.foldl_cons, List.length_cons]
    exact this.mono (by omega)

theorem popcount_prints {N k : Nat} {t : Term} (cnt : Nat) (ht : Prints N k t) :
    Prints (N + 2 + cnt) k (popcount t cnt) := by
  unfold popcount
  exact (foldl_add_prints ht (List.range cnt) (prints_nat k 0)).mono (by simp only [List.length_range]; omega)

/-- The printer's view of a row label list: every label of a sorted unit row over `xs` is one of `xs`. -/
theorem mem_sort_units {xs : List Label} {x : Label} {u : Unit} (h : (x, u) ∈ Row.sort (xs.map fun s => (s, ()))) :
    x ∈ xs := by
  have := (Row.sort_perm _).mem_iff.1 h
  simpa using this

theorem isState_prints {k : Nat} {t : Term} {states : List Label} (s : Label) (ht : Prints 2 k t)
    (hst : ∀ x ∈ states, labelOk x = true) (hlen : states.length ≤ Wire.rowMax) :
    Prints 3 k (isState states t s) := by
  unfold isState
  refine prints_case (N := 1) ht ?_ ?_
  · intro p hp
    obtain ⟨⟨x, u⟩, hx, rfl⟩ := List.mem_map.1 hp
    exact ⟨hst x (mem_sort_units hx), prints_bool _ _⟩
  · simp only [List.length_map, Row.length_sort, listMax_eq]
    simp only [Wire.rowMax] at hlen; omega

/-! ## The law skeleton -/

theorem lawOf5_prints {M N : Nat} {S : Ty} {birth adopt relaw write invoke : At → Term} (hS : TyPrints M S)
    (hb : Prints N 4 (birth ⟨1⟩)) (ha : Prints N 4 (adopt ⟨1⟩)) (hr : Prints N 4 (relaw ⟨1⟩))
    (hw : Prints N 4 (write ⟨1⟩)) (hi : Prints N 4 (invoke ⟨1⟩)) :
    Prints (max (M + 2) (max 9 (N + 5))) 0 (lawOf5 S birth adopt relaw write invoke) := by
  have hcase : Prints (N + 2) 3 (lawCase5 birth adopt relaw write invoke) := by
    refine prints_case ((prints_get (prints_var (k := 3) (i := 0) (by omega)) (by decide)).mono
      (by have := hb.pos; omega)) ?_ (by simp [listMax_eq])
    exact arms_cons ⟨show labelOk "adopt" = true by decide, ha⟩ (arms_cons ⟨show labelOk "birth" = true by decide, hb⟩
      (arms_cons ⟨show labelOk "invoke" = true by decide, hi⟩ (arms_cons ⟨show labelOk "relaw" = true by decide, hr⟩
      (arms_cons ⟨show labelOk "write" = true by decide, hw⟩ arms_nil))))
  have hN := hb.pos
  have h2 : Prints (max 6 (N + 2) + 1) 2 (.lam reqTy (lawCase5 birth adopt relaw write invoke)) :=
    prints_lam (reqTy_prints.mono (by omega)) (hcase.mono (by omega))
  have h1 : Prints (max (M + 1) (max 7 (N + 3) + 1)) 1 (.lam S (.lam reqTy (lawCase5 birth adopt relaw write invoke))) :=
    (prints_lam (k := 1) (hS.mono (M := max M (max 7 (N + 3))) (by omega)) (h2.mono (by omega))).mono (by omega)
  exact (prints_lam (k := 0) (hS.mono (M := max (M + 1) (max 8 (N + 4))) (by omega)) (h1.mono (by omega))).mono (by omega)

theorem lawOf_prints {M N : Nat} {S : Ty} {birth adopt relaw change : At → Term} (hS : TyPrints M S)
    (hb : Prints N 4 (birth ⟨1⟩)) (ha : Prints N 4 (adopt ⟨1⟩)) (hr : Prints N 4 (relaw ⟨1⟩))
    (hc : Prints N 4 (change ⟨1⟩)) :
    Prints (max (M + 2) (max 9 (N + 5))) 0 (lawOf S birth adopt relaw change) :=
  lawOf5_prints hS hb ha hr hc hc

/-! ## The laws -/

/-- An allowlist's text is nested `n + 11` deep (`n` ids), or its state type's depth plus 2. -/
theorem allowlistLaw_prints {M : Nat} {S : Ty} (ids : List ByteArray) (hS : TyPrints M S) :
    Prints (max (M + 2) (ids.length + 11)) 0 (allowlistLaw S ids) := by
  have hl : Prints (5 + ids.length) 4
      (anyOf (ids.map fun i => .prim .deq ((⟨1⟩ : At).reqF "agent") (.digest i))) := by
    have := anyOf_prints (N := 5) (k := 4)
      (l := ids.map fun i => .prim .deq ((⟨1⟩ : At).reqF "agent") (.digest i)) ?_ (by omega)
    · simpa [Nat.add_comm] using this
    · intro c hc
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc
      exact (prints_prim .deq (reqF_prints (by decide) (by decide)) (prints_digest 4 i)).mono (by omega)
  have hc := allOf1_prints (w := "not on the allowlist") hl (by omega)
  unfold allowlistLaw
  exact (lawOf_prints hS hc hc hc hc).mono (by omega)

/-- A machine's text is nested `e + 11` deep (`e` edges), or its state type's depth plus 2. -/
theorem machineLaw_prints {M : Nat} {S : Ty} {f : Label} {states : List Label} {initial : Label}
    (edges : List (Label × Nat × Label)) (hS : TyPrints M S) (hf : labelOk f = true)
    (hst : ∀ x ∈ states, labelOk x = true) (hlen : states.length ≤ Wire.rowMax) :
    Prints (max (M + 2) (edges.length + 11)) 0 (machineLaw S f states initial edges) := by
  have hstart : Prints (6 + edges.length) 4
      (allOf [(isState states ((⟨1⟩ : At).newF f) initial, s!"{f} does not start at {initial}")]) :=
    (allOf1_prints ((isState_prints initial (newF_prints (by decide) hf) hst hlen).mono (M := 5) (by omega))
      (by omega)).mono (by omega)
  have hinv : Prints (6 + edges.length) 4
      (allOf [(anyOf (edges.map fun (x, m, y) =>
        andT (.prim .eq (⟨1⟩ : At).payload (natT m))
          (andT (isState states ((⟨1⟩ : At).oldF f) x) (isState states ((⟨1⟩ : At).newF f) y))), "no edge")]) := by
    have hany := anyOf_prints (N := 5) (k := 4) (l := edges.map fun (x, m, y) =>
        andT (.prim .eq (⟨1⟩ : At).payload (natT m))
          (andT (isState states ((⟨1⟩ : At).oldF f) x) (isState states ((⟨1⟩ : At).newF f) y))) ?_ (by omega)
    · exact (allOf1_prints (w := "no edge") hany (by omega)).mono (by simp; omega)
    · intro c hc
      obtain ⟨⟨x, m, y⟩, _, rfl⟩ := List.mem_map.1 hc
      exact andT_prints ((prints_prim .eq (payload_prints (by decide)) (prints_nat 4 m)).mono (by omega))
        (andT_prints (isState_prints x (oldF_prints (by decide) hf) hst hlen)
          (isState_prints y (newF_prints (by decide) hf) hst hlen))
  have hfrozen : Prints (6 + edges.length) 4 (refusedT "a machine changes only by its methods") :=
    (refusedT_prints 4 _).mono (by omega)
  unfold machineLaw
  exact (lawOf5_prints hS hstart hstart hfrozen hfrozen hinv).mono (by omega)

theorem all1 {P : Term × String → Prop} {a : Term × String} (ha : P a) : ∀ p ∈ [a], P p := by simpa using ha

theorem all2 {P : Term × String → Prop} {a b : Term × String} (ha : P a) (hb : P b) : ∀ p ∈ [a, b], P p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨ha, hb⟩

theorem all3 {P : Term × String → Prop} {a b c : Term × String} (ha : P a) (hb : P b) (hc : P c) :
    ∀ p ∈ [a, b, c], P p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨ha, hb, hc⟩

theorem isMember_prints (members : List ByteArray) : Prints (3 + members.length) 4 (isMember members ⟨1⟩) := by
  unfold isMember
  have := anyOf_prints (N := 3) (k := 4) (l := members.map fun m => .prim .deq ((⟨1⟩ : At).reqF "agent") (.digest m))
    (fun c hc => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 hc
      exact prints_prim .deq (reqF_prints (by decide) (by decide)) (prints_digest 4 m)) (by omega)
  simpa using this

theorem approvalBy_prints (m : ByteArray) (i : Nat) : Prints 6 4 (approvalBy ⟨1⟩ m i) := by
  unfold approvalBy
  have hold : Prints 2 4 ((⟨1⟩ : At).oldF "approvals") := oldF_prints (by decide) (by decide)
  have hnew : Prints 2 4 ((⟨1⟩ : At).newF "approvals") := newF_prints (by decide) (by decide)
  refine andT_prints ((prints_prim .eq (bit_prints i hold) ((prints_nat 4 0).mono (by omega))).mono (by omega)) ?_
  refine andT_prints ?_ ((prints_prim .deq (reqF_prints (by decide) (by decide)) (prints_digest 4 m)).mono (by omega))
  exact (prints_prim .eq (hnew.mono (M := 3) (by omega))
    (prints_prim .add hold ((prints_nat 4 _).mono (by omega)))).mono (by omega)

theorem sameProposal_prints (T : Ty) :
    Prints 6 4 (sameProposal T ⟨1⟩ (fun b => b.newF "proposal") (fun b => b.oldF "proposal")) := by
  unfold sameProposal
  have hq : Prints 3 5 ((At.under ⟨1⟩).oldF "proposal") := (oldF_prints (by decide) (by decide)).mono (by omega)
  have v0 : Prints 1 6 (.var 0) := prints_var (by omega)
  have v1 : Prints 1 6 (.var 1) := prints_var (by omega)
  have inner1 : Prints 4 5 (.case ((At.under ⟨1⟩).oldF "proposal")
      [("laws", .prim .beq (.var 0) (.var 1)), ("set", .bool false)]) :=
    prints_case hq (arms_cons ⟨labelOk_fst (by decide), prints_prim .beq v0 v1⟩
      (arms_cons ⟨labelOk_fst (by decide), (prints_bool 6 false).mono (by omega)⟩ arms_nil)) (by simp [listMax_eq])
  have inner2 : Prints 4 5 (.case ((At.under ⟨1⟩).oldF "proposal")
      [("laws", .bool false), ("set", eqAt T (.var 0) (.var 1))]) :=
    prints_case hq (arms_cons ⟨labelOk_fst (by decide), (prints_bool 6 false).mono (by omega)⟩
      (arms_cons ⟨labelOk_fst (by decide), eqAt_prints T v0 v1⟩ arms_nil)) (by simp [listMax_eq])
  exact prints_case ((newF_prints (by decide) (by decide)).mono (by omega))
    (arms_cons ⟨labelOk_fst (by decide), inner1⟩ (arms_cons ⟨labelOk_fst (by decide), inner2⟩ arms_nil)) (by simp [listMax_eq])

theorem proposedSet_prints (T : Ty) {g : Label} (hg : labelOk g = true) : Prints 5 4 (proposedSet T g ⟨1⟩) := by
  unfold proposedSet
  exact prints_case ((oldF_prints (by decide) (by decide)).mono (by omega))
    (arms_cons ⟨labelOk_fst (by decide), (prints_bool 5 false).mono (by omega)⟩
      (arms_cons ⟨labelOk_fst (by decide), (eqAt_prints T ((prints_var (by omega)).mono (M := 2) (by omega))
        (newF_prints (a := At.under ⟨1⟩) (by decide) hg))⟩ arms_nil)) (by simp [listMax_eq])

theorem proposedLaws_prints : Prints 5 4 (proposedLaws ⟨1⟩) := by
  unfold proposedLaws
  exact prints_case ((oldF_prints (by decide) (by decide)).mono (by omega))
    (arms_cons ⟨labelOk_fst (by decide), (prints_prim .beq ((prints_var (by omega)).mono (M := 2) (by omega))
        ((payload_prints (a := At.under ⟨1⟩) (by decide)).mono (by omega))).mono (by omega)⟩
      (arms_cons ⟨labelOk_fst (by decide), (prints_bool 5 false).mono (by omega)⟩ arms_nil)) (by simp [listMax_eq])

/-- A quorum's text is nested `n + 17` deep (`n` members), or its state type's depth plus 2. -/
theorem quorumLaw_prints {M : Nat} {S : Ty} (T : Ty) (members : List ByteArray) (k : Nat) {g : Label}
    (hS : TyPrints M S) (hg : labelOk g = true) :
    Prints (max (M + 2) (members.length + 17)) 0 (quorumLaw S T members k g) := by
  have n1 := isMember_prints members
  have hquor : Prints (5 + members.length) 4
      (.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length)) :=
    (prints_prim .le ((prints_nat 4 k).mono (M := 4 + members.length) (by omega))
      ((popcount_prints members.length (oldF_prints (by decide) (by decide))).mono (by omega))).mono (by omega)
  have hreset : Prints 3 4 (.prim .eq ((⟨1⟩ : At).newF "approvals") (natT 0)) :=
    prints_prim .eq (newF_prints (by decide) (by decide)) ((prints_nat 4 0).mono (by omega))
  have hfresh : Prints (12 + members.length) 4 (allOf [(.prim .eq ((⟨1⟩ : At).newF "approvals") (natT 0),
      "approvals at birth")]) :=
    (allOf1_prints (hreset.mono (M := 5) (by omega)) (by omega)).mono (by omega)
  have hrelaw : Prints (12 + members.length) 4
      (guards [(isMember members ⟨1⟩, "not a member")]
        (allOf [(.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
          (proposedLaws ⟨1⟩, "not the proposal")])) := by
    have hall := allOf_prints (N := 5 + members.length)
      (l := [(.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
          (proposedLaws ⟨1⟩, "not the proposal")])
      (all2 hquor (proposedLaws_prints.mono (by omega))) (by omega)
    exact (guards_prints (N := 7 + members.length) (all1 (n1.mono (by omega))) (hall.mono (by simp; omega))
      (by omega)).mono (by simp; omega)
  have happ : Prints (7 + members.length) 4
      (guard (anyOf (members.zipIdx.map fun (m, i) => approvalBy ⟨1⟩ m i)) "not an approval" okT) := by
    have hany := anyOf_prints (N := 6) (k := 4) (l := members.zipIdx.map fun (m, i) => approvalBy ⟨1⟩ m i)
      (fun c hc => by
        obtain ⟨⟨m, i⟩, _, rfl⟩ := List.mem_map.1 hc
        exact approvalBy_prints m i) (by omega)
    simp only [List.length_map, List.length_zipIdx] at hany
    exact (guard_prints _ (hany.mono (M := 6 + members.length) (by omega)) ((okT_prints 4).mono (by omega)) (by omega)).mono (by omega)
  have hchange : Prints (12 + members.length) 4
      (guards [(isMember members ⟨1⟩, "not a member"),
            (.prim .lt ((⟨1⟩ : At).newF "approvals") (natT (pow2 members.length)), "approvals out of range")]
        (.ite (notT (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)))
          (allOf [(.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
            (proposedSet T g ⟨1⟩, "not the proposal"),
            (.prim .eq ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals not reset")])
          (.ite (notT (sameProposal T ⟨1⟩ (fun b => b.newF "proposal") (fun b => b.oldF "proposal")))
            (allOf [(.prim .eq ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals not reset")])
            (.ite (.prim .eq ((⟨1⟩ : At).newF "approvals") ((⟨1⟩ : At).oldF "approvals")) okT
              (guard (anyOf (members.zipIdx.map fun (m, i) => approvalBy ⟨1⟩ m i)) "not an approval" okT))))) := by
    have hcommit := allOf_prints (N := 5 + members.length)
      (l := [(.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") members.length), "no quorum"),
            (proposedSet T g ⟨1⟩, "not the proposal"),
            (.prim .eq ((⟨1⟩ : At).newF "approvals") (natT 0), "approvals not reset")])
      (all3 hquor ((proposedSet_prints T hg).mono (by omega)) (hreset.mono (by omega))) (by omega)
    have hne : Prints 4 4 (notT (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g))) :=
      notT_prints (eqAt_prints T (newF_prints (by decide) hg) (oldF_prints (by decide) hg))
    have hsp := notT_prints (sameProposal_prints T)
    have hrs := allOf1_prints (w := "approvals not reset") (hreset.mono (M := 5) (by omega)) (by omega)
    have heq : Prints 3 4 (.prim .eq ((⟨1⟩ : At).newF "approvals") ((⟨1⟩ : At).oldF "approvals")) :=
      prints_prim .eq (newF_prints (by decide) (by decide)) (oldF_prints (by decide) (by decide))
    have h3 := prints_ite (heq.mono (M := 7 + members.length) (by omega)) ((okT_prints 4).mono (by omega)) happ
    have h2 := prints_ite (hsp.mono (M := 8 + members.length) (by omega)) (hrs.mono (by omega)) (h3.mono (by omega))
    have h1 := prints_ite (hne.mono (M := 9 + members.length) (by omega)) (hcommit.mono (by simp; omega)) (h2.mono (by omega))
    have hlt : Prints 3 4 (.prim .lt ((⟨1⟩ : At).newF "approvals") (natT (pow2 members.length))) :=
      prints_prim .lt (newF_prints (by decide) (by decide)) ((prints_nat 4 _).mono (by omega))
    exact (guards_prints (N := 10 + members.length) (all2 (n1.mono (by omega)) (hlt.mono (by omega))) (h1.mono (by omega))
      (by omega)).mono (by simp; omega)
  unfold quorumLaw
  exact (lawOf_prints hS hfresh hfresh hrelaw hchange).mono (by omega)

/-! ## The checked generators' output has a text, and it reads back

A state type nested at most `Read.depthMax - 2` deep leaves every capped law within `Read.depthMax`
(the deepest is `max depthMax (cap + 17)`). Every state type a wire-valid package
carries is that shallow (`Lang.Proofs.PrintWire.state_prints`). The `_reads` forms add the install
check's premise (the law checks) and conclude the whole round trip, by `readTerm_checked`. -/

theorem reads_of_text {t : Term} {T : Ty} (ht : (term t).isSome = true) (hc : inferE [] [] t (Ω := []) = .ok T) :
    ∃ s, term t = some s ∧ Read.readTerm s = .ok t :=
  ⟨(term t).get ht, (Option.some_get ht).symm, readTerm_checked (by simp) hc (Option.some_get ht).symm⟩

theorem quorum_text {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {t : Term}
    (h : quorum S T ms k g = .ok t) (hS : TyPrints (depthMax - 2) S) (hg : labelOk g = true) : (term t).isSome = true := by
  obtain ⟨rfl, -, -, -, hn⟩ := Std.quorum_ok h
  exact term_isSome (quorumLaw_prints T ms k hS hg) (by simp only [membersMax] at hn; simp only [depthMax, Wire.depthMax]; omega)

theorem quorum_reads {S T U : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {t : Term}
    (h : quorum S T ms k g = .ok t) (hS : TyPrints (depthMax - 2) S) (hg : labelOk g = true) (hc : inferE [] [] t (Ω := []) = .ok U) :
    ∃ s, term t = some s ∧ Read.readTerm s = .ok t :=
  reads_of_text (quorum_text h hS hg) hc

theorem allowlist_text {S : Ty} {ids : List ByteArray} {t : Term} (h : allowlist S ids = .ok t)
    (hS : TyPrints (depthMax - 2) S) : (term t).isSome = true := by
  obtain ⟨rfl, hn⟩ := Std.allowlist_ok h
  exact term_isSome (allowlistLaw_prints ids hS) (by simp only [idsMax] at hn; simp only [depthMax, Wire.depthMax]; omega)

theorem allowlist_reads {S U : Ty} {ids : List ByteArray} {t : Term} (h : allowlist S ids = .ok t)
    (hS : TyPrints (depthMax - 2) S) (hc : inferE [] [] t (Ω := []) = .ok U) : ∃ s, term t = some s ∧ Read.readTerm s = .ok t :=
  reads_of_text (allowlist_text h hS) hc

theorem machine_text {S : Ty} {f : Label} {states : List Label} {initial : Label} {methods : List Label}
    {edges : List (Label × Label × Label)} {t : Term} (h : machine S f states initial methods edges = .ok t)
    (hS : TyPrints (depthMax - 2) S) (hf : labelOk f = true) (hst : ∀ x ∈ states, labelOk x = true) :
    (term t).isSome = true := by
  obtain ⟨es, rfl, hlen, he, hs, -⟩ := Std.machine_ok h
  exact term_isSome (machineLaw_prints es hS hf hst hs) (by simp only [edgesMax] at he; simp only [depthMax, Wire.depthMax]; omega)

theorem machine_reads {S U : Ty} {f : Label} {states : List Label} {initial : Label} {methods : List Label}
    {edges : List (Label × Label × Label)} {t : Term} (h : machine S f states initial methods edges = .ok t)
    (hS : TyPrints (depthMax - 2) S) (hf : labelOk f = true) (hst : ∀ x ∈ states, labelOk x = true)
    (hc : inferE [] [] t (Ω := []) = .ok U) : ∃ s, term t = some s ∧ Read.readTerm s = .ok t :=
  reads_of_text (machine_text h hS hf hst) hc

/-! ## Teeth: the premises hold at every cap, and the caps carry the weight -/

private def QS : Ty := .record [("approvals", .nat), ("proposal", proposalTy .nat), ("total", .nat)]
private def ids (n : Nat) : List ByteArray := (List.range n).map fun i => ⟨#[UInt8.ofNat (i / 256), UInt8.ofNat i]⟩

theorem QS_prints : TyPrints (depthMax - 2) QS :=
  ⟨_, (Option.some_get (by decide : (tySx QS).isSome = true)).symm, by decide, by decide⟩

/-- A quorum of `membersMax` members has a text (`quorum_text`'s premises met at the cap). -/
theorem quorum_at_cap_text :
    (term (quorumLaw QS .nat (ids membersMax) 1 "total")).isSome = true :=
  quorum_text (S := QS) (T := .nat) (ms := ids membersMax) (k := 1) (g := "total") (by rfl) QS_prints (by decide)

/-- An allowlist of `idsMax` ids has a text. -/
theorem allowlist_at_cap_text : (term (allowlistLaw QS (ids idsMax))).isSome = true :=
  allowlist_text (S := QS) (ids := ids idsMax)
    (by simp only [allowlist, ids, List.length_map, List.length_range, Nat.le_refl, decide_true]; rfl) QS_prints

/-- Past the reader's depth there is no text: an allowlist of 1100 ids (what `idsMax` refuses). -/
theorem allowlist_past_cap_no_text : (term (allowlistLaw QS (ids 1100))).isNone = true := by decide +kernel

private def MS : Ty := .record [("phase", stateTy ["a", "b"])]
private def capEdges : List (Label × Label × Label) := (List.range edgesMax).map fun _ => ("a", "start", "b")

theorem MS_prints : TyPrints (depthMax - 2) MS :=
  ⟨_, (Option.some_get (by decide : (tySx MS).isSome = true)).symm, by decide, by decide⟩

/-- `machine` accepts `edgesMax` edges, and what it emits there has a text. -/
theorem machine_at_cap_accepted : (machine MS "phase" ["a", "b"] "a" ["start"] capEdges).toBool = true := by
  decide +kernel

theorem machine_at_cap_text {t : Term} (h : machine MS "phase" ["a", "b"] "a" ["start"] capEdges = .ok t) :
    (term t).isSome = true :=
  machine_text h MS_prints (by decide) (by decide)

/-- The `_reads` premise is met at the cap: the allowlist of `idsMax` ids checks, so its text reads
back to exactly the law. -/
theorem allowlist_at_cap_infers : (inferE [] [] (allowlistLaw QS (ids idsMax)) (Ω := [])).toOption = some (lawTy QS) := by
  decide +kernel

theorem allowlist_at_cap_checks : inferE [] [] (allowlistLaw QS (ids idsMax)) (Ω := []) = .ok (lawTy QS) := by
  have h := allowlist_at_cap_infers
  revert h
  cases inferE [] [] (allowlistLaw QS (ids idsMax)) (Ω := []) <;> simp [Except.toOption]

theorem allowlist_at_cap_reads :
    ∃ s, term (allowlistLaw QS (ids idsMax)) = some s ∧ Read.readTerm s = .ok (allowlistLaw QS (ids idsMax)) :=
  allowlist_reads (S := QS) (ids := ids idsMax)
    (by simp only [allowlist, ids, List.length_map, List.length_range, Nat.le_refl, decide_true]; rfl)
    QS_prints allowlist_at_cap_checks

end Nanodregg.Lang.Print
