/-
# Lang.Proofs.Prints — the printer's equations as depth and width bounds

`Prints N k t`: `t` prints under `k` binders as a form nested at most `N` deep (`Print.need`, what
the reader's fuel counts) with no list longer than `Read.listMax` (`Print.width`). `TyPrints N T`
is the same for a type. One lemma per constructor (`prints_ite`, `prints_case`, `typrints_record`,
…) reads the printer's equation as a bound; `Lang.Proofs.StdFits` composes them over the stdlib's
generators, `Lang.Proofs.PrintWire` over every term the wire carries.
-/
import Lang.Proofs.PrintParse

namespace Nanodregg.Lang.Print

open Read (listMax depthMax)
open Wire (labelOk)

/-- `t` prints under `k` binders, nested at most `N` deep, no list longer than `Read.listMax`. -/
def Prints (N k : Nat) (t : Term) : Prop := ∃ x, termSx k t = some x ∧ need x ≤ N ∧ width x ≤ listMax

/-- `T` prints, nested at most `N` deep, no list longer than `Read.listMax`. -/
def TyPrints (N : Nat) (T : Ty) : Prop := ∃ x, tySx T = some x ∧ need x ≤ N ∧ width x ≤ listMax

theorem listMax_eq : listMax = 258 := rfl

theorem Prints.mono {N M k : Nat} {t : Term} (h : Prints N k t) (hNM : N ≤ M) : Prints M k t :=
  let ⟨x, hx, hn, hw⟩ := h; ⟨x, hx, by omega, hw⟩

theorem TyPrints.mono {N M : Nat} {T : Ty} (h : TyPrints N T) (hNM : N ≤ M) : TyPrints M T :=
  let ⟨x, hx, hn, hw⟩ := h; ⟨x, hx, by omega, hw⟩

theorem Prints.pos {N k : Nat} {t : Term} (h : Prints N k t) : 1 ≤ N :=
  let ⟨x, _, hn, _⟩ := h; by have := need_pos x; omega

theorem TyPrints.pos {N : Nat} {T : Ty} (h : TyPrints N T) : 1 ≤ N :=
  let ⟨x, _, hn, _⟩ := h; by have := need_pos x; omega

/-! ## The printer's equations as bounds -/

theorem prints_var {i k : Nat} (h : i < k) : Prints 1 k (.var i) :=
  ⟨atom (name (k - 1 - i)), by simp [termSx, h], by simp [need, atom], by simp [width, atom]⟩

theorem prints_nat (k n : Nat) : Prints 1 k (.nat n) :=
  ⟨atom (Nat.repr n), by simp [termSx], by simp [need, atom], by simp [width, atom]⟩

theorem prints_bool (k : Nat) (b : Bool) : Prints 1 k (.bool b) :=
  ⟨atom (if b then "true" else "false"), by simp [termSx], by simp [need, atom], by simp [width, atom]⟩

theorem prints_bytes (k : Nat) (s : ByteArray) : Prints 1 k (.bytes s) := by
  refine ⟨bytesSx s, by simp [termSx], ?_, ?_⟩ <;>
  · unfold bytesSx; split
    · split <;> simp [need, width, atom]
    · simp [need, width, atom]

theorem prints_digest (k : Nat) (s : ByteArray) : Prints 2 k (.digest s) :=
  ⟨list [atom "digest", digestSx s], by simp [termSx], by simp [need, needs, list, atom, digestSx],
    by simp [width, widths, list, atom, digestSx, listMax_eq]⟩

theorem prints_refuse {N k : Nat} {T : Ty} (w : ByteArray) (hT : TyPrints N T) :
    Prints (N + 1) k (.refuse T w) := by
  obtain ⟨xT, hxT, hnT, hwT⟩ := hT
  obtain ⟨xw, hxw, hnw, hww⟩ := prints_bytes k w
  simp only [termSx, Option.some.injEq] at hxw
  subst hxw
  refine ⟨list [atom "refuse", xT, bytesSx w], by simp [termSx, hxT], ?_, ?_⟩
  · have := need_pos xT
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwT hww ⊢; omega

theorem prints_get {N k : Nat} {t : Term} {ℓ : Label} (ht : Prints N k t) (hl : labelOk ℓ = true) :
    Prints (N + 1) k (.get t ℓ) := by
  obtain ⟨x, hx, hn, hw⟩ := ht
  refine ⟨list [atom ".", x, atom ℓ], by simp [termSx, hx, label, hl], ?_, ?_⟩
  · have := need_pos x
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hw ⊢; omega

theorem prints_prim {N k : Nat} {a b : Term} (o : Prim) (ha : Prints N k a) (hb : Prints N k b) :
    Prints (N + 1) k (.prim o a b) := by
  obtain ⟨xa, hxa, hna, hwa⟩ := ha
  obtain ⟨xb, hxb, hnb, hwb⟩ := hb
  refine ⟨list [atom (primWord o), xa, xb], by simp [termSx, hxa, hxb], ?_, ?_⟩
  · have := need_pos xa
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwa hwb ⊢; omega

theorem prints_ite {N k : Nat} {c a b : Term} (hc : Prints N k c) (ha : Prints N k a) (hb : Prints N k b) :
    Prints (N + 1) k (.ite c a b) := by
  obtain ⟨xc, hxc, hnc, hwc⟩ := hc
  obtain ⟨xa, hxa, hna, hwa⟩ := ha
  obtain ⟨xb, hxb, hnb, hwb⟩ := hb
  refine ⟨list [atom "if", xc, xa, xb], by simp [termSx, hxc, hxa, hxb], ?_, ?_⟩
  · have := need_pos xc
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwc hwa hwb ⊢; omega

theorem prints_lam {N k : Nat} {A : Ty} {b : Term} (hA : TyPrints N A) (hb : Prints N (k + 1) b) :
    Prints (N + 1) k (.lam A b) := by
  obtain ⟨xA, hxA, hnA, hwA⟩ := hA
  obtain ⟨xb, hxb, hnb, hwb⟩ := hb
  refine ⟨list [atom "lam", atom (name k), xA, xb], by simp [termSx, hxA, hxb], ?_, ?_⟩
  · have := need_pos xb
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwA hwb ⊢; omega

theorem prints_inj {N k : Nat} {T : Ty} {ℓ : Label} {t : Term} (hT : TyPrints N T) (hl : labelOk ℓ = true)
    (ht : Prints N k t) : Prints (N + 1) k (.inj T ℓ t) := by
  obtain ⟨xT, hxT, hnT, hwT⟩ := hT
  obtain ⟨xt, hxt, hnt, hwt⟩ := ht
  refine ⟨list [atom "inj", xT, atom ℓ, xt], by simp [termSx, hxT, hxt, label, hl], ?_, ?_⟩
  · have := need_pos xt
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwT hwt ⊢; omega

theorem armsSx_prints {N k : Nat} : ∀ {arms : List (Label × Term)},
    (∀ p ∈ arms, labelOk p.1 = true ∧ Prints N (k + 1) p.2) →
    ∃ xs, armsSx k arms = some xs ∧ needs xs ≤ N + 1 ∧ widths xs ≤ listMax ∧ xs.length = arms.length
  | [], _ => ⟨[], rfl, by simp [needs], by simp [widths], rfl⟩
  | (ℓ, t) :: arms, h => by
    obtain ⟨hl, xt, hxt, hnt, hwt⟩ := h (ℓ, t) (List.mem_cons_self ..)
    obtain ⟨xs, hxs, hns, hws, hlen⟩ := armsSx_prints (arms := arms) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨list [atom ℓ, atom (name k), xt] :: xs, by simp [armsSx, hxt, hxs, label, hl], ?_, ?_, by simp [hlen]⟩
    · have := need_pos xt
      simp only [need, needs, list, atom] at hns ⊢; omega
    · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwt hws ⊢; omega

theorem prints_case {N k : Nat} {t : Term} {arms : List (Label × Term)} (ht : Prints (N + 1) k t)
    (harms : ∀ p ∈ arms, labelOk p.1 = true ∧ Prints N (k + 1) p.2) (hlen : arms.length + 2 ≤ listMax) :
    Prints (N + 2) k (.case t arms) := by
  obtain ⟨xt, hxt, hnt, hwt⟩ := ht
  obtain ⟨xs, hxs, hns, hws, hl⟩ := armsSx_prints harms
  refine ⟨list (atom "case" :: xt :: xs), by simp [termSx, hxt, hxs], ?_, ?_⟩
  · simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, hl] at hwt hws ⊢; omega

theorem fieldsSx_prints {N k : Nat} : ∀ {fs : List (Label × Term)},
    (∀ p ∈ fs, labelOk p.1 = true ∧ Prints N k p.2) →
    ∃ xs, fieldsSx k fs = some xs ∧ needs xs ≤ N + 1 ∧ widths xs ≤ listMax ∧ xs.length = fs.length
  | [], _ => ⟨[], rfl, by simp [needs], by simp [widths], rfl⟩
  | (ℓ, t) :: fs, h => by
    obtain ⟨hl, xt, hxt, hnt, hwt⟩ := h (ℓ, t) (List.mem_cons_self ..)
    obtain ⟨xs, hxs, hns, hws, hlen⟩ := fieldsSx_prints (fs := fs) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨list [atom ℓ, xt] :: xs, by simp [fieldsSx, hxt, hxs, label, hl], ?_, ?_, by simp [hlen]⟩
    · have := need_pos xt
      simp only [need, needs, list, atom] at hns ⊢; omega
    · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwt hws ⊢; omega

theorem prints_record {N k : Nat} {fs : List (Label × Term)}
    (hfs : ∀ p ∈ fs, labelOk p.1 = true ∧ Prints N k p.2) (hlen : fs.length + 1 ≤ listMax) :
    Prints (N + 2) k (.record fs) := by
  obtain ⟨xs, hxs, hns, hws, hl⟩ := fieldsSx_prints hfs
  refine ⟨list (atom "record" :: xs), by simp [termSx, hxs], ?_, ?_⟩
  · simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, hl] at hws ⊢; omega

theorem prints_ref (k i : Nat) : Prints 2 k (.ref i) :=
  ⟨list [atom "ref", atom (Nat.repr i)], by simp [termSx], by simp [need, needs, list, atom],
    by simp [width, widths, list, atom, listMax_eq]⟩

theorem prints_app {N k : Nat} {f a : Term} (hf : Prints N k f) (ha : Prints N k a) :
    Prints (N + 1) k (.app f a) := by
  obtain ⟨xf, hxf, hnf, hwf⟩ := hf
  obtain ⟨xa, hxa, hna, hwa⟩ := ha
  refine ⟨list [xf, xa], by simp [termSx, hxf, hxa], ?_, ?_⟩
  · simp only [need, needs, list]; omega
  · simp only [width, widths, list, List.length_cons, List.length_nil, listMax_eq] at hwf hwa ⊢; omega

theorem prints_fix {N k : Nat} {t : Term} (ht : Prints N k t) : Prints (N + 1) k (.fix t) := by
  obtain ⟨x, hx, hn, hw⟩ := ht
  refine ⟨list [atom "fix", x], by simp [termSx, hx], ?_, ?_⟩
  · have := need_pos x
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hw ⊢; omega

theorem prints_extend {N k : Nat} {t : Term} {fs : List (Label × Term)} (ht : Prints (N + 1) k t)
    (hfs : ∀ p ∈ fs, labelOk p.1 = true ∧ Prints N k p.2) (hlen : fs.length + 2 ≤ listMax) :
    Prints (N + 2) k (.extend t fs) := by
  obtain ⟨xt, hxt, hnt, hwt⟩ := ht
  obtain ⟨xs, hxs, hns, hws, hl⟩ := fieldsSx_prints hfs
  refine ⟨list (atom "extend" :: xt :: xs), by simp [termSx, hxt, hxs], ?_, ?_⟩
  · simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, hl] at hwt hws ⊢; omega

theorem typrints_atom (T : Ty) (h : T = .nat ∨ T = .bool ∨ T = .bytes ∨ T = .digest) : TyPrints 1 T := by
  rcases h with rfl | rfl | rfl | rfl <;>
  exact ⟨_, rfl, by simp [need, atom], by simp [width, atom]⟩

theorem typrints_fn {N : Nat} {a b : Ty} (ha : TyPrints N a) (hb : TyPrints N b) : TyPrints (N + 1) (.fn a b) := by
  obtain ⟨xa, hxa, hna, hwa⟩ := ha
  obtain ⟨xb, hxb, hnb, hwb⟩ := hb
  refine ⟨list [atom "->", xa, xb], by simp [tySx, hxa, hxb], ?_, ?_⟩
  · have := need_pos xa
    simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwa hwb ⊢; omega

theorem rowSx_prints {N : Nat} : ∀ {r : List (Label × Ty)}, (∀ p ∈ r, labelOk p.1 = true ∧ TyPrints N p.2) →
    ∃ xs, rowSx r = some xs ∧ needs xs ≤ N + 1 ∧ widths xs ≤ listMax ∧ xs.length = r.length
  | [], _ => ⟨[], rfl, by simp [needs], by simp [widths], rfl⟩
  | (ℓ, t) :: r, h => by
    obtain ⟨hl, xt, hxt, hnt, hwt⟩ := h (ℓ, t) (List.mem_cons_self ..)
    obtain ⟨xs, hxs, hns, hws, hlen⟩ := rowSx_prints (r := r) (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨list [atom ℓ, xt] :: xs, by simp [rowSx, hxt, hxs, label, hl], ?_, ?_, by simp [hlen]⟩
    · have := need_pos xt
      simp only [need, needs, list, atom] at hns ⊢; omega
    · simp only [width, widths, list, atom, List.length_cons, List.length_nil, listMax_eq] at hwt hws ⊢; omega

theorem typrints_record {N : Nat} {r : List (Label × Ty)} (h : ∀ p ∈ r, labelOk p.1 = true ∧ TyPrints N p.2)
    (hlen : r.length + 1 ≤ listMax) : TyPrints (N + 2) (.record r) := by
  obtain ⟨xs, hxs, hns, hws, hl⟩ := rowSx_prints h
  refine ⟨list (atom "rec" :: xs), by simp [tySx, hxs], ?_, ?_⟩
  · simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, hl] at hws ⊢; omega

theorem typrints_sum {N : Nat} {r : List (Label × Ty)} (h : ∀ p ∈ r, labelOk p.1 = true ∧ TyPrints N p.2)
    (hlen : r.length + 1 ≤ listMax) : TyPrints (N + 2) (.sum r) := by
  obtain ⟨xs, hxs, hns, hws, hl⟩ := rowSx_prints h
  refine ⟨list (atom "sum" :: xs), by simp [tySx, hxs], ?_, ?_⟩
  · simp only [need, needs, list, atom]; omega
  · simp only [width, widths, list, atom, List.length_cons, hl] at hws ⊢; omega

theorem term_isSome {N : Nat} {t : Term} (h : Prints N 0 t) (hN : N ≤ depthMax) : (term t).isSome = true := by
  obtain ⟨x, hx, hn, hw⟩ := h
  have hn' : need x ≤ depthMax := by omega
  simp [term, hx, fits, fitsB, hn', hw]

theorem labelOk_fst {ℓ : Label} {t : Term} (h : labelOk ℓ = true) : labelOk (ℓ, t).fst = true := h

theorem arms_cons {P : Label × Term → Prop} {p : Label × Term} {l : List (Label × Term)} (h1 : P p)
    (h2 : ∀ q ∈ l, P q) : ∀ q ∈ p :: l, P q := List.forall_mem_cons.2 ⟨h1, h2⟩

theorem arms_nil {P : Label × Term → Prop} : ∀ q ∈ ([] : List (Label × Term)), P q := by simp

end Nanodregg.Lang.Print
