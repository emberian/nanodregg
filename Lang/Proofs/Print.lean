/-
# Lang.Proofs.Print — reading the printed text gives back what was printed

The round trip, for every value the printer gives a text (`some`):
* `readTy_ty`: a canonical type (`Ty.wf`) reads back from `Print.ty`;
* `readTerm_term`: a canonical closed term (`Canon`: ascending rows, `wf` annotations) reads back
  from `Print.term`, and `readTerm_checked`: every closed term that checks is canonical;
* `readData_data`: data conforming to a canonical type reads back from `Print.data` at that type;
* `readPackage_package` / `readPackage_checked`: a package the install check accepts (over canonical
  import interfaces) reads back from `Print.package` as exactly that package.
The parser half is `Lang.Proofs.PrintParse`. Elaboration is proved over any form `Same` as the
printed one (`ty_tySx`, `term_termSx`, `dataAt_dataSx`), since the parser assigns real offsets.
The printed forms are `Ok` (`tySx_ok`, `termSx_ok`, `dataSx_ok`): every label passes `labelOk`, a
bound variable is `x<depth>`, and bytes are a quote-free string or `#hex`.
`hex_injective`: distinct byte strings print distinct hex (what HOSTING's grain directory names rest on).
-/
import Lang.Proofs.PrintParse
import Lang.Proofs.Canon
import Lang.Proofs.Data
import Lang.Proofs.Check
import Std.Data.String.ToNat

import Lang.Proofs.Load

namespace Nanodregg.Lang.Print

open Read
open Wire (labelOk)

/-! ## Part 2: elaboration of a printed form -/

theorem same_atom {p : Nat} {s : String} {y : SExp} (h : Same (.atom p s) y) : ∃ q, y = .atom q s := by
  cases h; exact ⟨_, rfl⟩

theorem same_str {p : Nat} {s : String} {y : SExp} (h : Same (.str p s) y) : ∃ q, y = .str q s := by
  cases h; exact ⟨_, rfl⟩

theorem same_list {p : Nat} {xs : List SExp} {y : SExp} (h : Same (.list p xs) y) :
    ∃ q ys, y = .list q ys ∧ SameL xs ys := by
  cases h; exact ⟨_, _, rfl, by assumption⟩

theorem sameL_cons {x : SExp} {xs l : List SExp} (h : SameL (x :: xs) l) :
    ∃ y ys, l = y :: ys ∧ Same x y ∧ SameL xs ys := by
  cases h; exact ⟨_, _, rfl, by assumption, by assumption⟩

theorem sameL_nil {l : List SExp} (h : SameL [] l) : l = [] := by cases h; rfl

theorem label_some {ℓ : String} {x : SExp} (h : label ℓ = some x) : x = atom ℓ ∧ labelOk ℓ = true := by
  unfold label at h; split at h <;> simp_all

mutual
theorem ty_tySx : ∀ (T : Ty) (d : Nat) {x y : SExp}, tySx T = some x → Same x y → need x ≤ d →
    T.wf = true → Read.ty d y = .ok T
  | .nat, d, x, y, h, hs, hn, _ => by
    simp only [tySx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [Read.ty]
  | .bool, d, x, y, h, hs, hn, _ => by
    simp only [tySx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [Read.ty]
  | .bytes, d, x, y, h, hs, hn, _ => by
    simp only [tySx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [Read.ty]
  | .digest, d, x, y, h, hs, hn, _ => by
    simp only [tySx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [Read.ty]
  | .fn a b, d, x, y, h, hs, hn, hwf => by
    simp only [tySx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [Read.ty, ty_tySx a d ha h1 (by omega) hwf.1, ty_tySx b d hb h2 (by omega) hwf.2]
      rfl
  | .record row, d, x, y, h, hs, hn, hwf => by
    simp only [tySx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hr, rfl⟩ := h
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hrow⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp only [Read.ty, tyRow_rowSx row d hr hrow (by omega) hwf.2]
      simp only [bind, Except.bind, pure, Except.pure, Row.sort_of_ascending hwf.1]
  | .sum row, d, x, y, h, hs, hn, hwf => by
    simp only [tySx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hr, rfl⟩ := h
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hrow⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp only [Read.ty, tyRow_rowSx row d hr hrow (by omega) hwf.2]
      simp only [bind, Except.bind, pure, Except.pure, Row.sort_of_ascending hwf.1]

theorem tyRow_rowSx : ∀ (row : List (Label × Ty)) (d : Nat) {xs ys : List SExp}, rowSx row = some xs →
    SameL xs ys → needs xs ≤ d → Ty.rowWf row = true → Read.entries (fun t => Read.ty d t) ys = .ok row
  | [], d, xs, ys, h, hs, _, _ => by
    simp only [rowSx, Option.some.injEq] at h; subst h
    cases sameL_nil hs
    simp [Read.entries]
  | (ℓ, t) :: row, d, xs, ys, h, hs, hn, hwf => by
    simp only [rowSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, ht, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    simp only [Ty.rowWf, Bool.and_eq_true] at hwf
    obtain ⟨e, ys, rfl, he, hrest⟩ := sameL_cons hs
    obtain ⟨q, es, rfl, hes⟩ := same_list he
    obtain ⟨e0, es, rfl, h0, hes⟩ := sameL_cons hes
    obtain ⟨e1, es, rfl, h1, hes⟩ := sameL_cons hes
    cases sameL_nil hes
    obtain ⟨r, rfl⟩ := same_atom h0
    simp only [need, needs, list, atom] at hn
    simp [Read.entries, ty_tySx t d ht h1 (by omega) hwf.1, tyRow_rowSx row d hr hrest (by omega) hwf.2]
    rfl
end

/-! ## Bytes and numerals -/

theorem hexVal_hexDigit : ∀ n, n < 16 → hexVal (hexDigit n) = some n := by decide

theorem unhex_hex : ∀ (l : List UInt8) (acc : ByteArray),
    unhex acc (l.foldr (fun x cs => hexDigit (x.toNat / 16) :: hexDigit (x.toNat % 16) :: cs) []) =
      some ⟨acc.data ++ l.toArray⟩
  | [], acc => by simp [unhex]
  | x :: l, acc => by
    have h1 := hexVal_hexDigit (x.toNat / 16) (by have := x.toNat_lt; omega)
    have h2 := hexVal_hexDigit (x.toNat % 16) (by omega)
    simp only [List.foldr_cons, unhex, h1, h2, bind, Option.bind_some]
    rw [unhex_hex l]
    have e : UInt8.ofNat (x.toNat / 16 * 16 + x.toNat % 16) = x := by
      rw [Nat.mul_comm, Nat.div_add_mod]; exact UInt8.ofNat_toNat
    simp [e, ByteArray.push]

theorem hexBytes_hex (b : ByteArray) : hexBytes? ("#" ++ hex b) = some b := by
  simp only [hexBytes?, hex, hexChars, String.toList_append, String.toList_ofList]
  rw [show "#".toList = ['#'] from rfl, List.singleton_append]
  simp only
  rw [← Array.foldr_toList, unhex_hex]
  simp

theorem fromUTF8_toUTF8 {b : ByteArray} {t : String} (h : String.fromUTF8? b = some t) : t.toUTF8 = b := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

/-- What printed bytes are: a quote-free string of plain characters holding the same bytes, or
`#hex` of them. -/
theorem bytesSx_cases (b : ByteArray) :
    (∃ t, bytesSx b = .str 0 t ∧ t.toUTF8 = b ∧ '"' ∉ t.toList ∧ ∀ c ∈ t.toList, plainChar c = true) ∨
      bytesSx b = atom ("#" ++ hex b) := by
  unfold bytesSx
  split
  · rename_i t ht
    split
    · rename_i hq
      have hall := List.all_eq_true.1 hq
      refine .inl ⟨t, rfl, fromUTF8_toUTF8 ht, fun hm => ?_, hall⟩
      have := hall _ hm
      simp [plainChar] at this
    · exact .inr rfl
  · exact .inr rfl

theorem toNat_repr (n : Nat) : (Nat.repr n).toNat? = some n := Nat.toNat?_repr n

/-! ## Data -/

theorem rowConforms_labels : ∀ {fs : List (Label × Data)} {row : List (Label × Ty)},
    RowConforms fs row → fs.map Prod.fst = row.map Prod.fst
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [rowConforms_labels h]

mutual
theorem dataAt_dataSx : ∀ (v : Data) (T : Ty) (d : Nat) {x y : SExp}, dataSx v = some x → Same x y →
    need x ≤ d → Conforms v T → T.wf = true → dataAt d T y = .ok v
  | .nat n, _, d, x, y, h, hs, hn, .nat hlt, _ => by
    simp only [dataSx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [dataAt, scalarAt, hlt]
  | .bool b, _, d, x, y, h, hs, hn, .bool, _ => by
    simp only [dataSx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => cases b <;> simp [dataAt, scalarAt]
  | .bytes b, _, d, x, y, h, hs, hn, .bytes hle, _ => by
    simp only [dataSx, Option.some.injEq] at h; subst h
    cases d with
    | zero => have := need_pos (bytesSx b); omega
    | succ d =>
      rcases bytesSx_cases b with ⟨t, e, ht, _⟩ | e <;> rw [e] at hs
      · obtain ⟨q, rfl⟩ := same_str hs
        subst ht
        simp_all [dataAt, scalarAt]
      · obtain ⟨q, rfl⟩ := same_atom hs
        simp [dataAt, scalarAt, hexBytes_hex, hle]
  | .digest b, _, d, x, y, h, hs, hn, .digest hle, _ => by
    simp only [dataSx, digestSx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => simp [dataAt, scalarAt, hexBytes_hex, hle]
  | .record fs, _, d, x, y, h, hs, hn, .record hrow, hwf => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hfs⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      obtain ⟨ps, hps, hlab, hrun⟩ := dataRow_dataFieldsSx fs _ d q hxs hfs (by omega) hrow hwf.2
      have hasc : Row.ascending ps = true := by
        rw [Row.ascending_of_labels (ys := fs) hlab, Row.ascending_of_labels (rowConforms_labels hrow)]
        exact hwf.1
      simp only [dataAt, hps, bind, Except.bind, Row.sort_of_ascending hasc, hrun, pure, Except.pure]
  | .inj ℓ v, _, d, x, y, h, hs, hn, .inj hf hv, hwf => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hxv, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    simp only [Ty.wf, Bool.and_eq_true] at hwf
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [dataAt, hf, dataAt_dataSx v _ d hxv h1 (by omega) hv (rowWf_find hwf.2 hf)]
      rfl

theorem dataRow_dataFieldsSx : ∀ (fs : List (Label × Data)) (row : List (Label × Ty)) (d p : Nat)
    {xs ys : List SExp}, dataFieldsSx fs = some xs → SameL xs ys → needs xs ≤ d →
    RowConforms fs row → Ty.rowWf row = true →
    ∃ ps, dataFields ys = .ok ps ∧ ps.map Prod.fst = fs.map Prod.fst ∧
      dataRowWith (fun A v => dataAt d A v) p row ps = .ok fs
  | [], _, d, p, xs, ys, h, hs, _, .nil, _ => by
    simp only [dataFieldsSx, Option.some.injEq] at h; subst h
    cases sameL_nil hs
    exact ⟨[], by simp [dataFields], rfl, by simp [dataRowWith]⟩
  | (ℓ, v) :: fs, (_, A) :: row, d, p, xs, ys, h, hs, hn, .cons hv hrow, hwf => by
    simp only [dataFieldsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hxv, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    simp only [Ty.rowWf, Bool.and_eq_true] at hwf
    obtain ⟨e, ys, rfl, he, hrest⟩ := sameL_cons hs
    obtain ⟨q, es, rfl, hes⟩ := same_list he
    obtain ⟨e0, es, rfl, h0, hes⟩ := sameL_cons hes
    obtain ⟨e1, es, rfl, h1, hes⟩ := sameL_cons hes
    cases sameL_nil hes
    obtain ⟨r, rfl⟩ := same_atom h0
    simp only [need, needs, list, atom] at hn
    obtain ⟨ps, hps, hlab, hrun⟩ := dataRow_dataFieldsSx fs row d p hr hrest (by omega) hrow hwf.2
    refine ⟨(ℓ, e1) :: ps, ?_, by simp [hlab], ?_⟩
    · simp [dataFields, hps]; rfl
    · simp [dataRowWith, dataAt_dataSx v A d hxv h1 (by omega) hv hwf.1, hrun]; rfl
end

/-! ## Terms -/

mutual
/-- Every row in the term is canonical (strictly ascending labels) and every annotation is `wf`:
what `Read` produces, since it sorts every row it reads. -/
inductive Canon : Term → Prop
  | var {i : Nat} : Canon (.var i)
  | lam {A : Ty} {b : Term} : A.wf = true → Canon b → Canon (.lam A b)
  | app {f a : Term} : Canon f → Canon a → Canon (.app f a)
  | fix {t : Term} : Canon t → Canon (.fix t)
  | nat {n : Nat} : Canon (.nat n)
  | bool {b : Bool} : Canon (.bool b)
  | bytes {s : ByteArray} : Canon (.bytes s)
  | digest {s : ByteArray} : Canon (.digest s)
  | prim {p : Prim} {a b : Term} : Canon a → Canon b → Canon (.prim p a b)
  | record {fs : List (Label × Term)} : Row.ascending fs = true → CanonRow fs → Canon (.record fs)
  | get {t : Term} {ℓ : Label} : Canon t → Canon (.get t ℓ)
  | extend {t : Term} {fs : List (Label × Term)} : Canon t → Row.ascending fs = true → CanonRow fs →
      Canon (.extend t fs)
  | inj {T : Ty} {ℓ : Label} {t : Term} : T.wf = true → Canon t → Canon (.inj T ℓ t)
  | case {t : Term} {arms : List (Label × Term)} : Canon t → Row.ascending arms = true → CanonRow arms →
      Canon (.case t arms)
  | ite {c a b : Term} : Canon c → Canon a → Canon b → Canon (.ite c a b)
  | ref {i : Nat} : Canon (.ref i)
  | refuse {T : Ty} {w : ByteArray} : T.wf = true → Canon (.refuse T w)

  | hole {n : Nat} {σ : List Term} : CanonList σ → Canon (.hole n σ)

inductive CanonList : List Term → Prop
  | nil : CanonList []
  | cons {t : Term} {ts : List Term} : Canon t → CanonList ts → CanonList (t :: ts)

inductive CanonRow : List (Label × Term) → Prop
  | nil : CanonRow []
  | cons {ℓ : Label} {t : Term} {r : List (Label × Term)} : Canon t → CanonRow r → CanonRow ((ℓ, t) :: r)
end

theorem name_toList (m : Nat) : (name m).toList = 'x' :: (Nat.repr m).toList := by
  simp [name, String.toList_append]

theorem ne_of_head {a b : String} {c e : Char} (ha : a.toList.head? = some c) (hb : b.toList.head? = some e)
    (h : c ≠ e) : a ≠ b := by
  rintro rfl; rw [ha] at hb; exact h (Option.some.inj hb)

theorem repr_head (n : Nat) : ∃ c, (Nat.repr n).toList.head? = some c ∧ c.isDigit = true := by
  have hne := (String.isNat_iff.mp (Nat.isNat_repr n)).1
  rw [Nat.toList_repr]
  match h : Nat.toDigits 10 n with
  | [] =>
    exfalso; apply hne
    rw [← String.ofList_toList (s := Nat.repr n), Nat.toList_repr, h]
  | c :: _ => exact ⟨c, rfl, Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide)
      (by rw [h]; exact List.mem_cons_self ..)⟩

theorem toNat_none {s : String} {c : Char} (hc : c ∈ s.toList) (hd : c.isDigit = false) (hu : c ≠ '_') :
    s.toNat? = none := by
  apply String.toNat?_eq_none
  cases h : s.isNat with
  | false => rfl
  | true =>
    rcases (String.isNat_iff.mp h).2.1 c hc with h' | h' <;> simp_all

theorem name_toNat (m : Nat) : (name m).toNat? = none :=
  toNat_none (c := 'x') (by rw [name_toList]; exact List.mem_cons_self ..) (by decide) (by decide)

theorem name_hex (m : Nat) : hexBytes? (name m) = none := by
  simp [hexBytes?, name_toList]

theorem name_ne {m : Nat} {s : String} (h : s.toList.head? ≠ some 'x') : name m ≠ s := by
  intro e; apply h; rw [← e, name_toList]; rfl

/-- A printed binder name is never reserved, so the reader accepts it as a binder. -/
theorem isLiteral_name (m : Nat) : isLiteral (name m) = false := by
  have h1 : name m ≠ "true" := name_ne (by simp)
  have h2 : name m ≠ "false" := name_ne (by simp)
  simp [isLiteral, h1, h2, name_toNat, name_hex]

theorem isReserved_name (m : Nat) : isReserved (name m) = false := by
  have hk : ∀ w ∈ keywords, name m ≠ w := by
    intro w hw
    simp only [keywords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact name_ne (by simp)
  have hp : primOf (name m) = none := by
    unfold primOf; split <;> first | rfl | (rename_i h; exact absurd h (name_ne (by simp)))
  simp only [isReserved, isLiteral_name, hp, Option.isSome_none, Bool.or_false, Bool.false_or]
  simpa using fun h => hk _ h rfl

theorem binder_name (p m : Nat) : binder p (name m) = .ok () := by simp [binder, isReserved_name]

theorem mapM_cons_ok {f : SExp → P Term} {a : SExp} {as : List SExp} {r : List Term}
    (h : (a :: as).mapM f = .ok r) : ∃ t ts, f a = .ok t ∧ as.mapM f = .ok ts ∧ r = t :: ts := by
  rw [List.mapM_cons] at h
  cases hf : f a with
  | error e => simp [hf, bind, Except.bind] at h
  | ok t =>
    cases hl : as.mapM f with
    | error e => simp [hf, hl, bind, Except.bind] at h
    | ok ts =>
      simp only [hf, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨t, ts, rfl, rfl, h.symm⟩

/-- `keywords` covers `term`'s head words: a list headed by a bound name that is not reserved, with
any arguments, reads as that variable applied to them, never as a form. A form added to `term`
whose word is not in `keywords` makes this theorem false. -/
theorem term_unreserved_head {d : Nat} {sc : List String} {p q i : Nat} {w : String}
    (hw : isReserved w = false) (hi : indexOf w sc = some i) :
    ∀ {args : List SExp} {targs : List Term}, args.mapM (fun a => Read.term d sc a) = .ok targs →
    args ≠ [] → Read.term (d + 1) sc (.list p (.atom q w :: args)) = .ok (appAll (.var i) targs) := by
  have hw' := hw
  simp only [isReserved, Bool.or_eq_false_iff] at hw'
  obtain ⟨⟨hl, hk⟩, hp⟩ := hw'
  have hk2 : w ∉ keywords := fun h => by simp [h] at hk
  have hp2 : primOf w = none := by cases h : primOf w <;> simp_all
  simp only [keywords, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk2
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ := hk2
  simp only [isLiteral, Bool.or_eq_false_iff, decide_eq_false_iff_not, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hl
  obtain ⟨⟨⟨ht, hf⟩, hn⟩, hh⟩ := hl
  clear hw hk hp
  intro args targs hm hne
  cases d with
  | zero =>
    match args, hm with
    | [], _ => exact absurd rfl hne
    | a :: _, hm => simp [List.mapM_cons, Read.term, bind, Except.bind] at hm
  | succ d =>
  match args, hm with
  | [], _ => exact absurd rfl hne
  | [a], hm =>
    simp [Read.term, hn, hh, hi, hm, k2, k4, k6, k7, k9, k11, k12]; rfl
  | [a, b], hm =>
    obtain ⟨ta, ts, ha, hm1, h1⟩ := mapM_cons_ok hm
    obtain ⟨tb, ts2, hb, hm2, h2⟩ := mapM_cons_ok hm1
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hm2
    subst h1 h2 hm2
    simp [Read.term, appAll, hn, hh, hi, ha, hb, hp2, k5, k14]; rfl
  | a :: b :: c :: rest, hm =>
    simp [Read.term, hn, hh, hi, hm, k1, k2, k3, k6, k7, k8, k9, k10]; rfl

theorem name_injective {a b : Nat} (h : name a = name b) : a = b := by
  have : (Nat.repr a).toList = (Nat.repr b).toList := by
    have := congrArg String.toList h
    rw [name_toList, name_toList] at this
    exact List.cons.inj this |>.2
  have e : Nat.repr a = Nat.repr b := String.toList_inj.mp this
  have := Nat.toNat?_repr a
  rw [e, Nat.toNat?_repr] at this
  exact (Option.some.inj this).symm

theorem indexOf_name : ∀ (k i : Nat), i < k →
    indexOf (name (k - 1 - i)) (List.map name (List.range k)).reverse = some i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, h => by
    rw [← List.map_reverse, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons]
    simp only [indexOf]
    cases i with
    | zero => simp
    | succ i =>
      have hne : name (k + 1 - 1 - (i + 1)) ≠ name k := fun e => by have := name_injective e; omega
      rw [if_neg hne, show k + 1 - 1 - (i + 1) = k - 1 - i by omega, List.map_reverse, indexOf_name k i (by omega)]
      rfl

theorem scope_succ (k : Nat) :
    name k :: (List.map name (List.range k)).reverse = (List.map name (List.range (k + 1))).reverse := by
  simp [List.range_succ]

theorem term_name (d : Nat) (sc : List String) (q m i : Nat) (h : indexOf (name m) sc = some i) :
    Read.term (d + 1) sc (.atom q (name m)) = .ok (.var i) := by
  have h1 : name m ≠ "true" := name_ne (by simp)
  have h2 : name m ≠ "false" := name_ne (by simp)
  have h3 := name_toNat m
  have h4 := name_hex m
  simp [Read.term, *]

theorem repr_ne {n : Nat} {s : String} {c : Char} (hs : s.toList.head? = some c) (hc : c.isDigit = false) :
    Nat.repr n ≠ s := by
  obtain ⟨e, he, hd⟩ := repr_head n
  exact ne_of_head he hs (fun h => by subst h; simp_all)

theorem term_repr (d : Nat) (sc : List String) (q n : Nat) :
    Read.term (d + 1) sc (.atom q (Nat.repr n)) = .ok (.nat n) := by
  have h1 : Nat.repr n ≠ "true" := repr_ne (c := 't') (by simp) (by decide)
  have h2 : Nat.repr n ≠ "false" := repr_ne (c := 'f') (by simp) (by decide)
  simp [Read.term, *]

theorem hexAtom_toList (b : ByteArray) : ("#" ++ hex b).toList = '#' :: hexChars b := by
  simp [hex, String.toList_append]

theorem term_hex (d : Nat) (sc : List String) (q : Nat) (b : ByteArray) :
    Read.term (d + 1) sc (.atom q ("#" ++ hex b)) = .ok (.bytes b) := by
  have h3 : ("#" ++ hex b).toNat? = none :=
    toNat_none (c := '#') (by rw [hexAtom_toList]; exact List.mem_cons_self ..) (by decide) (by decide)
  have h1 : "#" ++ hex b ≠ "true" := ne_of_head (c := '#') (e := 't') (by simp) (by simp) (by decide)
  have h2 : "#" ++ hex b ≠ "false" := ne_of_head (c := '#') (e := 'f') (by simp) (by simp) (by decide)
  have h4 := hexBytes_hex b
  simp [Read.term, *]

/-- A printed term in head position is never a keyword that a two-element form could start with. -/
theorem head_not_kw {k : Nat} {f : Term} {F Y : SExp} (h : termSx k f = some F) (hs : Same F Y) :
    ∀ q s, Y = .atom q s → s ≠ "fn" ∧ s ≠ "fix" ∧ s ≠ "record" ∧ s ≠ "extend" ∧ s ≠ "case" ∧ s ≠ "ref" ∧
      s ≠ "digest" := by
  intro q s hY
  subst hY
  cases f with
  | var i =>
    simp only [termSx] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      cases hs
      exact ⟨name_ne (by simp), name_ne (by simp), name_ne (by simp), name_ne (by simp), name_ne (by simp),
        name_ne (by simp), name_ne (by simp)⟩
    · cases h
  | nat n =>
    simp only [termSx, Option.some.injEq] at h; subst h
    cases hs
    exact ⟨repr_ne (c := 'f') (by simp) (by decide), repr_ne (c := 'f') (by simp) (by decide),
      repr_ne (c := 'r') (by simp) (by decide), repr_ne (c := 'e') (by simp) (by decide),
      repr_ne (c := 'c') (by simp) (by decide), repr_ne (c := 'r') (by simp) (by decide),
      repr_ne (c := 'd') (by simp) (by decide)⟩
  | bool b =>
    simp only [termSx, Option.some.injEq] at h; subst h
    cases hs
    cases b <;> simp
  | bytes b =>
    simp only [termSx, Option.some.injEq] at h; subst h
    rcases bytesSx_cases b with ⟨t, e, _⟩ | e <;> rw [e] at hs
    · cases hs
    · cases hs
      have hd (w : String) (c : Char) (hw : w.toList.head? = some c) (hc : c ≠ '#') : "#" ++ hex b ≠ w :=
        ne_of_head (by simp) hw (fun e => hc e.symm)
      exact ⟨hd _ 'f' (by simp) (by decide), hd _ 'f' (by simp) (by decide), hd _ 'r' (by simp) (by decide),
        hd _ 'e' (by simp) (by decide), hd _ 'c' (by simp) (by decide), hd _ 'r' (by simp) (by decide),
        hd _ 'd' (by simp) (by decide)⟩
  | lam _ _ | app _ _ | fix _ | prim _ _ _ | record _ | get _ _ | extend _ _ | inj _ _ _ | case _ _
  | ite _ _ _ | ref _ | digest _ | refuse _ _ | hole _ _ =>
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    first
    | (obtain ⟨_, _, rfl⟩ := h; cases hs)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; cases hs)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; cases hs)
    | (obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h; cases hs)
    | (subst h; cases hs)

theorem term_app {d : Nat} {sc : List String} {p : Nat} {Y1 Y2 : SExp} {f a : Term}
    (hkw : ∀ q s, Y1 = .atom q s → s ≠ "fn" ∧ s ≠ "fix" ∧ s ≠ "record" ∧ s ≠ "extend" ∧ s ≠ "case" ∧ s ≠ "ref" ∧
      s ≠ "digest")
    (h1 : Read.term d sc Y1 = .ok f) (h2 : Read.term d sc Y2 = .ok a) :
    Read.term (d + 1) sc (.list p [Y1, Y2]) = .ok (.app f a) := by
  cases Y1 with
  | atom q s =>
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hkw q s rfl
    simp [Read.term, appAll, h1, h2, k1, k2, k3, k4, k5, k6, k7]
    rfl
  | str q s =>
    simp [Read.term, appAll, h1, h2]
    rfl
  | list q xs =>
    simp [Read.term, appAll, h1, h2]
    rfl

mutual
theorem term_termSx : ∀ (t : Term) (k d : Nat) {x y : SExp}, termSx k t = some x → Same x y →
    need x ≤ d → Canon t → Read.term d (List.map name (List.range k)).reverse y = .ok t
  | .var i, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx] at h
    split at h
    · rename_i hi
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨q, rfl⟩ := same_atom hs
      cases d with
      | zero => simp [need, atom] at hn
      | succ d => exact term_name d _ q _ i (indexOf_name k i hi)
    · cases h
  | .nat n, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => exact term_repr d _ q n
  | .bool b, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx, Option.some.injEq] at h; subst h
    obtain ⟨q, rfl⟩ := same_atom hs
    cases d with
    | zero => simp [need, atom] at hn
    | succ d => cases b <;> simp [Read.term]
  | .bytes b, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx, Option.some.injEq] at h; subst h
    cases d with
    | zero => have := need_pos (bytesSx b); omega
    | succ d =>
      rcases bytesSx_cases b with ⟨t, e, ht, _⟩ | e <;> rw [e] at hs
      · obtain ⟨q, rfl⟩ := same_str hs
        subst ht
        simp [Read.term]
      · obtain ⟨q, rfl⟩ := same_atom hs
        exact term_hex d _ q b
  | .digest b, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx, digestSx, Option.some.injEq] at h; subst h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h1
    cases d with
    | zero => simp [need, list] at hn
    | succ d => simp [Read.term, hexBytes_hex]
  | .ref i, k, d, x, y, h, hs, hn, _ => by
    simp only [termSx, Option.some.injEq] at h; subst h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h1
    cases d with
    | zero => simp [need, list] at hn
    | succ d => simp [Read.term]
  | .refuse T w, k, d, x, y, h, hs, hn, .refuse hT => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xT, hxT, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      have eT := ty_tySx T d hxT h1 (by omega) hT
      rcases bytesSx_cases w with ⟨t, e, ht, _⟩ | e <;> rw [e] at h2
      · obtain ⟨q', rfl⟩ := same_str h2
        subst ht
        simp [Read.term, eT]; rfl
      · obtain ⟨q', rfl⟩ := same_atom h2
        simp [Read.term, eT, hexBytes_hex]; rfl
  | .lam A b, k, d, x, y, h, hs, hn, .lam hA hb => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, ha, xb, hxb, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    obtain ⟨y3, ys, rfl, h3, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h1
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      have eb := term_termSx b (k + 1) d hxb h3 (by omega) hb
      rw [← scope_succ] at eb
      simp [Read.term, ty_tySx A d ha h2 (by omega) hA, eb, binder_name]
      rfl
  | .app f a, k, d, x, y, h, hs, hn, .app hf ha => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xf, hxf, xa, hxa, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    match d with
    | 0 => simp only [need, needs, list] at hn; omega
    | d + 1 =>
      simp only [need, needs, list] at hn
      exact term_app (head_not_kw hxf h1) (term_termSx f k d hxf h1 (by omega) hf)
        (term_termSx a k d hxa h2 (by omega) ha)
  | .fix t, k, d, x, y, h, hs, hn, .fix ht => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, hxt, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [Read.term, term_termSx t k d hxt h1 (by omega) ht]
      rfl
  | .prim o a b, k, d, x, y, h, hs, hn, .prim ha hb => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, hxa, xb, hxb, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      have e1 := term_termSx a k d hxa h1 (by omega) ha
      have e2 := term_termSx b k d hxb h2 (by omega) hb
      cases o <;> simp [Read.term, primWord, primOf, e1, e2] <;> rfl
  | .get t ℓ, k, d, x, y, h, hs, hn, .get ht => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, hxt, xl, hl', rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl'
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h2
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [Read.term, term_termSx t k d hxt h1 (by omega) ht]
      rfl
  | .inj T ℓ t, k, d, x, y, h, hs, hn, .inj hT ht => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xT, hxT, xl, hl', xt, hxt, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl'
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    obtain ⟨y3, ys, rfl, h3, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h2
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [Read.term, ty_tySx T d hxT h1 (by omega) hT, term_termSx t k d hxt h3 (by omega) ht]
      rfl
  | .ite c a b, k, d, x, y, h, hs, hn, .ite hc ha hb => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xc, hxc, xa, hxa, xb, hxb, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    obtain ⟨y3, ys, rfl, h3, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp [Read.term, term_termSx c k d hxc h1 (by omega) hc, term_termSx a k d hxa h2 (by omega) ha,
        term_termSx b k d hxb h3 (by omega) hb]
      rfl
  | .record fs, k, d, x, y, h, hs, hn, .record hasc hfs => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hrow⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp only [Read.term, fields_fieldsSx fs k d hxs hrow (by omega) hfs]
      simp only [bind, Except.bind, pure, Except.pure, Row.sort_of_ascending hasc]
  | .extend t fs, k, d, x, y, h, hs, hn, .extend ht hasc hfs => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, hxt, xs, hxs, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hrow⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp only [Read.term, term_termSx t k d hxt h1 (by omega) ht, fields_fieldsSx fs k d hxs hrow (by omega) hfs]
      simp only [bind, Except.bind, pure, Except.pure, Row.sort_of_ascending hasc]
  | .case t arms, k, d, x, y, h, hs, hn, .case ht hasc harms => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, hxt, xs, hxs, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hrow⟩ := sameL_cons hl
    obtain ⟨r, rfl⟩ := same_atom h0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      simp only [Read.term, term_termSx t k d hxt h1 (by omega) ht, arms_armsSx arms k d hxs hrow (by omega) harms]
      simp only [bind, Except.bind, pure, Except.pure, Row.sort_of_ascending hasc]
  | .hole n σ, k, d, x, y, h, hs, hn, .hole hσ => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    obtain ⟨q, ys, rfl, hl⟩ := same_list hs
    obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hl
    obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hl
    obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hl
    cases sameL_nil hl
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h1
    obtain ⟨q', zs, rfl, hz⟩ := same_list h2
    obtain ⟨z0, zs, rfl, hz0, hrest⟩ := sameL_cons hz
    obtain ⟨r'', rfl⟩ := same_atom hz0
    cases d with
    | zero => simp [need, list] at hn
    | succ d =>
      simp only [need, needs, list, atom] at hn
      have ht := terms_termsSx σ k d hxs hrest (by omega) hσ
      simp only [Read.term, Nat.toNat?_repr, ht, bind, Except.bind, pure, Except.pure]

theorem terms_termsSx : ∀ (ts : List Term) (k d : Nat) {xs ys : List SExp}, termsSx k ts = some xs →
    SameL xs ys → needs xs ≤ d → CanonList ts →
      ys.mapM (fun y => Read.term d (List.map name (List.range k)).reverse y) = .ok ts
  | [], k, d, xs, ys, h, hs, _, .nil => by
      simp only [termsSx, Option.some.injEq] at h
      subst xs
      cases sameL_nil hs
      rfl
  | t :: ts, k, d, xs, ys, h, hs, hn, .cons ht hts => by
      simp only [termsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨xt, hxt, xr, hxr, rfl⟩ := h
      obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
      simp only [needs] at hn
      simp [List.mapM_cons, term_termSx t k d hxt hy (by omega) ht,
        terms_termsSx ts k d hxr hrest (by omega) hts]
      rfl

theorem fields_fieldsSx : ∀ (fs : List (Label × Term)) (k d : Nat) {xs ys : List SExp}, fieldsSx k fs = some xs →
    SameL xs ys → needs xs ≤ d → CanonRow fs → Read.entries (fun e => Read.term d (List.map name (List.range k)).reverse e) ys = .ok fs
  | [], k, d, xs, ys, h, hs, _, _ => by
    simp only [fieldsSx, Option.some.injEq] at h; subst h
    cases sameL_nil hs
    simp [Read.entries]
  | (ℓ, t) :: fs, k, d, xs, ys, h, hs, hn, .cons ht hfs => by
    simp only [fieldsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, hxt, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    obtain ⟨e, ys, rfl, he, hrest⟩ := sameL_cons hs
    obtain ⟨q, es, rfl, hes⟩ := same_list he
    obtain ⟨e0, es, rfl, h0, hes⟩ := sameL_cons hes
    obtain ⟨e1, es, rfl, h1, hes⟩ := sameL_cons hes
    cases sameL_nil hes
    obtain ⟨r, rfl⟩ := same_atom h0
    simp only [need, needs, list, atom] at hn
    simp [Read.entries, term_termSx t k d hxt h1 (by omega) ht, fields_fieldsSx fs k d hr hrest (by omega) hfs]
    rfl

theorem arms_armsSx : ∀ (arms : List (Label × Term)) (k d : Nat) {xs ys : List SExp}, armsSx k arms = some xs →
    SameL xs ys → needs xs ≤ d → CanonRow arms → Read.arms (fun x b => Read.term d (x :: (List.map name (List.range k)).reverse) b) ys = .ok arms
  | [], k, d, xs, ys, h, hs, _, _ => by
    simp only [armsSx, Option.some.injEq] at h; subst h
    cases sameL_nil hs
    simp [Read.arms]
  | (ℓ, t) :: arms, k, d, xs, ys, h, hs, hn, .cons ht harms => by
    simp only [armsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, hxt, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    obtain ⟨e, ys, rfl, he, hrest⟩ := sameL_cons hs
    obtain ⟨q, es, rfl, hes⟩ := same_list he
    obtain ⟨e0, es, rfl, h0, hes⟩ := sameL_cons hes
    obtain ⟨e1, es, rfl, h1, hes⟩ := sameL_cons hes
    obtain ⟨e2, es, rfl, h2, hes⟩ := sameL_cons hes
    cases sameL_nil hes
    obtain ⟨r, rfl⟩ := same_atom h0
    obtain ⟨r', rfl⟩ := same_atom h1
    simp only [need, needs, list, atom] at hn
    have et := term_termSx t (k + 1) d hxt h2 (by omega) ht
    rw [← scope_succ] at et
    simp [Read.arms, et, arms_armsSx arms k d hr hrest (by omega) harms, binder_name]
    rfl
end

/-! ## Part 3: what the printer prints is `Ok` -/

theorem lit_ok (s : String) (h1 : s.toList ≠ []) (h2 : s.toList.all (fun c => !isDelim c) = true) : Ok (atom s) :=
  .atom h1 (fun c hc => by simpa using List.all_eq_true.mp h2 c hc)

theorem label_ok {ℓ : String} {x : SExp} (h : label ℓ = some x) : Ok x := by
  obtain ⟨rfl, hl⟩ := label_some h
  unfold Wire.labelOk labelAtom at hl
  simp only [Bool.and_eq_true, List.isEmpty_eq_false_iff, List.all_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hl
  exact .atom hl.1.1 hl.1.2

theorem digit_not_delim {c : Char} (h : c.isDigit = true ∨ c = '_') : isDelim c = false := by
  cases hc : isDelim c with
  | false => rfl
  | true =>
    simp only [isDelim, Char.isWhitespace, Bool.or_eq_true, decide_eq_true_eq, or_assoc] at hc
    rcases h with h | rfl
    · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases hc with e | e | e | e | e | e | e | e <;> subst e <;> revert h <;> decide
    · revert hc; decide

theorem repr_ok (n : Nat) : Ok (atom (Nat.repr n)) := by
  have h := String.isNat_iff.mp (Nat.isNat_repr n)
  exact .atom (fun e => h.1 (by rw [← String.ofList_toList (s := Nat.repr n), e]))
    (fun c hc => digit_not_delim (h.2.1 c hc))

theorem name_ok (m : Nat) : Ok (atom (name m)) := by
  have h := String.isNat_iff.mp (Nat.isNat_repr m)
  refine .atom (by rw [name_toList]; simp) (fun c hc => ?_)
  rw [name_toList] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  · exact digit_not_delim (h.2.1 c hc)

theorem hexDigit_not_delim : ∀ n, n < 16 → isDelim (hexDigit n) = false := by decide

/-- Every character of `hexChars b` is one hex digit. -/
theorem hexChars_digit {b : ByteArray} {c : Char} (h : c ∈ hexChars b) : ∃ n, n < 16 ∧ c = hexDigit n := by
  simp only [hexChars] at h
  rw [← Array.foldr_toList] at h
  generalize b.data.toList = l at h
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.foldr_cons, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨_, by have := x.toNat_lt; omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · exact ih h

theorem mem_hexChars {b : ByteArray} {c : Char} (h : c ∈ hexChars b) : isDelim c = false := by
  obtain ⟨n, hn, rfl⟩ := hexChars_digit h
  exact hexDigit_not_delim n hn

theorem hexDigit_lower : ∀ n, n < 16 → ('0' ≤ hexDigit n ∧ hexDigit n ≤ '9') ∨ ('a' ≤ hexDigit n ∧ hexDigit n ≤ 'f') := by
  decide

/-- Hex is lowercase `0-9a-f` only, so case folding is the identity on it: two hex names that a
case-insensitive file system identifies are equal (with `hex_injective`, name the same bytes). -/
theorem hexChars_lower {b : ByteArray} {c : Char} (h : c ∈ hexChars b) :
    ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') := by
  obtain ⟨n, hn, rfl⟩ := hexChars_digit h
  exact hexDigit_lower n hn

theorem hexAtom_ok (b : ByteArray) : Ok (atom ("#" ++ hex b)) := by
  refine .atom (by simp) (fun c hc => ?_)
  rw [hexAtom_toList] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  · exact mem_hexChars hc

theorem bytesSx_ok (b : ByteArray) : Ok (bytesSx b) := by
  rcases bytesSx_cases b with ⟨t, e, _, hq, -⟩ | e <;> rw [e]
  · exact .str hq
  · exact hexAtom_ok b

theorem kw_ok (s : String) (h : s.toList ≠ [] ∧ s.toList.all (fun c => !isDelim c) = true := by decide) :
    Ok (atom s) := lit_ok s h.1 h.2

mutual
theorem tySx_ok : ∀ (T : Ty) {x : SExp}, tySx T = some x → Ok x
  | .nat, _, h | .bool, _, h | .bytes, _, h | .digest, _, h => by
    simp only [tySx, Option.some.injEq] at h; subst h; exact kw_ok _
  | .fn a b, _, h => by
    simp only [tySx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (tySx_ok a ha) (.cons (tySx_ok b hb) .nil)))
  | .record r, _, h | .sum r, _, h => by
    simp only [tySx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hr, rfl⟩ := h
    exact .list (.cons (kw_ok _) (rowSx_ok r hr))

theorem rowSx_ok : ∀ (r : List (Label × Ty)) {xs : List SExp}, rowSx r = some xs → OkL xs
  | [], _, h => by simp only [rowSx, Option.some.injEq] at h; subst h; exact .nil
  | (ℓ, t) :: r, _, h => by
    simp only [rowSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, ht, xr, hr, rfl⟩ := h
    exact .cons (.list (.cons (label_ok hl) (.cons (tySx_ok t ht) .nil))) (rowSx_ok r hr)
end

mutual
theorem termSx_ok : ∀ (t : Term) (k : Nat) {x : SExp}, termSx k t = some x → Ok x
  | .var i, k, _, h => by
    simp only [termSx] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact name_ok _
    · cases h
  | .nat n, _, _, h => by simp only [termSx, Option.some.injEq] at h; subst h; exact repr_ok n
  | .bool b, _, _, h => by simp only [termSx, Option.some.injEq] at h; subst h; cases b <;> exact kw_ok _
  | .bytes b, _, _, h => by simp only [termSx, Option.some.injEq] at h; subst h; exact bytesSx_ok b
  | .digest b, _, _, h => by
    simp only [termSx, digestSx, Option.some.injEq] at h; subst h
    exact .list (.cons (kw_ok _) (.cons (hexAtom_ok b) .nil))
  | .ref i, _, _, h => by
    simp only [termSx, Option.some.injEq] at h; subst h
    exact .list (.cons (kw_ok _) (.cons (repr_ok i) .nil))
  | .refuse T w, _, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xT, hT, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (tySx_ok T hT) (.cons (bytesSx_ok w) .nil)))
  | .lam A b, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (name_ok k) (.cons (tySx_ok A ha) (.cons (termSx_ok b _ hb) .nil))))
  | .app f a, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xf, hf, xa, ha, rfl⟩ := h
    exact .list (.cons (termSx_ok f _ hf) (.cons (termSx_ok a _ ha) .nil))
  | .fix t, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, ht, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (termSx_ok t _ ht) .nil))
  | .prim o a b, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xa, ha, xb, hb, rfl⟩ := h
    have : Ok (atom (primWord o)) := by cases o <;> exact kw_ok _
    exact .list (.cons this (.cons (termSx_ok a _ ha) (.cons (termSx_ok b _ hb) .nil)))
  | .record fs, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    exact .list (.cons (kw_ok _) (fieldsSx_ok fs k hxs))
  | .get t ℓ, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, ht, xl, hl, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (termSx_ok t _ ht) (.cons (label_ok hl) .nil)))
  | .extend t fs, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, ht, xs, hxs, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (termSx_ok t _ ht) (fieldsSx_ok fs k hxs)))
  | .inj T ℓ t, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xT, hT, xl, hl, xt, ht, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (tySx_ok T hT) (.cons (label_ok hl) (.cons (termSx_ok t _ ht) .nil))))
  | .case t arms, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xt, ht, xs, hxs, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (termSx_ok t _ ht) (armsSx_ok arms k hxs)))
  | .ite c a b, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xc, hc, xa, ha, xb, hb, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (termSx_ok c _ hc) (.cons (termSx_ok a _ ha) (.cons (termSx_ok b _ hb) .nil))))
  | .hole n σ, k, _, h => by
    simp only [termSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hx, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (repr_ok n)
      (.cons (.list (.cons (kw_ok _) (termsSx_ok σ k hx))) .nil)))

theorem termsSx_ok : ∀ (ts : List Term) (k : Nat) {xs : List SExp}, termsSx k ts = some xs → OkL xs
  | [], _, _, h => by simp only [termsSx, Option.some.injEq] at h; subst h; exact .nil
  | t :: ts, k, _, h => by
      simp only [termsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨xt, ht, xs, hs, rfl⟩ := h
      exact .cons (termSx_ok t k ht) (termsSx_ok ts k hs)

theorem fieldsSx_ok : ∀ (fs : List (Label × Term)) (k : Nat) {xs : List SExp}, fieldsSx k fs = some xs → OkL xs
  | [], _, _, h => by simp only [fieldsSx, Option.some.injEq] at h; subst h; exact .nil
  | (ℓ, t) :: fs, k, _, h => by
    simp only [fieldsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, ht, xr, hr, rfl⟩ := h
    exact .cons (.list (.cons (label_ok hl) (.cons (termSx_ok t _ ht) .nil))) (fieldsSx_ok fs k hr)

theorem armsSx_ok : ∀ (arms : List (Label × Term)) (k : Nat) {xs : List SExp}, armsSx k arms = some xs → OkL xs
  | [], _, _, h => by simp only [armsSx, Option.some.injEq] at h; subst h; exact .nil
  | (ℓ, t) :: arms, k, _, h => by
    simp only [armsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xt, ht, xr, hr, rfl⟩ := h
    exact .cons (.list (.cons (label_ok hl) (.cons (name_ok k) (.cons (termSx_ok t _ ht) .nil)))) (armsSx_ok arms k hr)
end

mutual
theorem dataSx_ok : ∀ (v : Data) {x : SExp}, dataSx v = some x → Ok x
  | .nat n, _, h => by simp only [dataSx, Option.some.injEq] at h; subst h; exact repr_ok n
  | .bool b, _, h => by simp only [dataSx, Option.some.injEq] at h; subst h; cases b <;> exact kw_ok _
  | .bytes b, _, h => by simp only [dataSx, Option.some.injEq] at h; subst h; exact bytesSx_ok b
  | .digest b, _, h => by simp only [dataSx, digestSx, Option.some.injEq] at h; subst h; exact hexAtom_ok b
  | .record fs, _, h => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xs, hxs, rfl⟩ := h
    exact .list (.cons (kw_ok _) (dataFieldsSx_ok fs hxs))
  | .inj ℓ v, _, h => by
    simp only [dataSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hv, rfl⟩ := h
    exact .list (.cons (label_ok hl) (.cons (dataSx_ok v hv) .nil))

theorem dataFieldsSx_ok : ∀ (fs : List (Label × Data)) {xs : List SExp}, dataFieldsSx fs = some xs → OkL xs
  | [], _, h => by simp only [dataFieldsSx, Option.some.injEq] at h; subst h; exact .nil
  | (ℓ, v) :: fs, _, h => by
    simp only [dataFieldsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xv, hv, xr, hr, rfl⟩ := h
    exact .cons (.list (.cons (label_ok hl) (.cons (dataSx_ok v hv) .nil))) (dataFieldsSx_ok fs hr)
end

/-! ## The round trip -/

theorem fitsB_iff {x : SExp} : fitsB x = true ↔ need x ≤ depthMax ∧ width x ≤ listMax := by
  simp [fitsB]

theorem fits_some {x : SExp} {s : String} (h : fits x = some s) :
    need x ≤ depthMax ∧ width x ≤ listMax ∧ s = text x := by
  unfold fits at h; split at h
  · rename_i hf; simp only [Option.some.injEq] at h; exact ⟨(fitsB_iff.mp hf).1, (fitsB_iff.mp hf).2, h.symm⟩
  · cases h

theorem scope_zero : (List.map name (List.range 0)).reverse = [] := rfl

/-- A canonical type reads back from its text. -/
theorem readTy_ty {T : Ty} {s : String} (hwf : T.wf = true) (h : ty T = some s) : readTy s = .ok T := by
  simp only [ty, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hf⟩ := h
  obtain ⟨hn, hw, rfl⟩ := fits_some hf
  obtain ⟨y, hy, hs⟩ := parse_text (tySx_ok T hx) hn hw
  simp only [readTy, hy, bind, Except.bind]
  exact ty_tySx T depthMax hx hs hn hwf

/-- A canonical closed term reads back from its text. -/
theorem readTerm_term {t : Term} {s : String} (hc : Canon t) (h : term t = some s) : readTerm s = .ok t := by
  simp only [term, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hf⟩ := h
  obtain ⟨hn, hw, rfl⟩ := fits_some hf
  obtain ⟨y, hy, hs⟩ := parse_text (termSx_ok t 0 hx) hn hw
  simp only [readTerm, hy, bind, Except.bind]
  have := term_termSx t 0 depthMax hx hs hn hc
  rwa [scope_zero] at this

/-- Data of a canonical data type reads back from its text, at that type. -/
theorem readData_data {v : Data} {T : Ty} {s : String} (hc : Conforms v T) (hwf : T.wf = true)
    (h : data v = some s) : readData T s = .ok v := by
  simp only [data, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, hf⟩ := h
  obtain ⟨hn, hw, rfl⟩ := fits_some hf
  obtain ⟨y, hy, hs⟩ := parse_text (dataSx_ok v hx) hn hw
  simp only [readData, hy, bind, Except.bind]
  exact dataAt_dataSx v T depthMax hx hs hn hc hwf

theorem unhex_hexChars (b : ByteArray) : unhex .empty (hexChars b) = some b := by
  simp only [hexChars]
  rw [← Array.foldr_toList, unhex_hex]
  simp

/-- Distinct byte strings print distinct hex: `Read.unhex` inverts `hexChars`. -/
theorem hexChars_injective {a b : ByteArray} (h : hexChars a = hexChars b) : a = b := by
  have e := unhex_hexChars a
  rw [h, unhex_hexChars] at e
  exact (Option.some.inj e).symm

theorem hex_injective {a b : ByteArray} (h : hex a = hex b) : a = b :=
  hexChars_injective (by simpa [hex] using congrArg String.toList h)

theorem mapM_imports {f : SExp → P ByteArray} (hf : ∀ q i, f (.str q (hex i)) = .ok i) :
    ∀ (is : List ByteArray) {ys : List SExp}, SameL (is.map fun i => .str 0 (hex i)) ys → ys.mapM f = .ok is
  | [], _, hs => by cases sameL_nil hs; rfl
  | i :: is, _, hs => by
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    obtain ⟨q, rfl⟩ := same_str hy
    simp [List.mapM_cons, hf, mapM_imports hf is hrest]
    rfl

theorem labels_mapM : ∀ (ls : List Label) {xs ys : List SExp}, ls.mapM label = some xs → SameL xs ys →
    Read.labels ys = .ok ls
  | [], _, _, h, hs => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h
    cases sameL_nil hs; rfl
  | ℓ :: ls, _, _, h, hs => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    obtain ⟨q, rfl⟩ := same_atom hy
    simp [Read.labels, labels_mapM ls hr hrest]
    rfl

theorem labels_ok : ∀ (ls : List Label) {xs : List SExp}, ls.mapM label = some xs → OkL xs
  | [], _, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | ℓ :: ls, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xr, hr, rfl⟩ := h
    exact .cons (label_ok hl) (labels_ok ls hr)

theorem imports_ok : ∀ (is : List ByteArray), OkL (is.map fun i => .str 0 (hex i))
  | [] => .nil
  | i :: is => .cons (.str fun h => by have := mem_hexChars (b := i) (c := '"') (by simpa [hex] using h); simp [isDelim] at this) (imports_ok is)

/-! ## Relations (LANG-49): each prints as `Read.rel` reads it -/

theorem optLabelSx_ok : ∀ (o : Option Label) {xs : List SExp}, optLabelSx o = some xs → OkL xs
  | none, _, h => by simp only [optLabelSx, Option.some.injEq] at h; subst h; exact .nil
  | some ℓ, _, h => by
    simp only [optLabelSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact .cons (label_ok hx) .nil

theorem optLabel_read (p : Nat) : ∀ (o : Option Label) {xs ys : List SExp}, optLabelSx o = some xs →
    SameL xs ys → Read.optLabel p ys = .ok o
  | none, _, _, h, hs => by
    simp only [optLabelSx, Option.some.injEq] at h; subst h; cases sameL_nil hs; rfl
  | some ℓ, _, _, h, hs => by
    simp only [optLabelSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hx
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    cases sameL_nil hrest
    obtain ⟨q, rfl⟩ := same_atom hy
    rfl

theorem keyFields_ok : ∀ (key : List (Label × Ty)) {xs : List SExp},
    key.mapM (fun f => do pure (list [← label f.1, ← tySx f.2])) = some xs → OkL xs
  | [], _, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | f :: key, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, ⟨xl, hl, xt, ht, rfl⟩, xr, hr, rfl⟩ := h
    exact .cons (.list (.cons (label_ok hl) (.cons (tySx_ok _ ht) .nil))) (keyFields_ok key hr)

theorem keyFields_read : ∀ (key : List (Label × Ty)) {xs ys : List SExp},
    key.mapM (fun f => do pure (list [← label f.1, ← tySx f.2])) = some xs → SameL xs ys →
    needs xs ≤ depthMax → key.all (fun f => f.2.wf) = true → Read.keyFields ys = .ok key
  | [], _, _, h, hs, _, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases sameL_nil hs; rfl
  | f :: key, _, _, h, hs, hn, hw => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, ⟨xl, hl, xt, ht, rfl⟩, xr, hr, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    simp only [List.all_cons, Bool.and_eq_true] at hw
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    obtain ⟨q, z, rfl, g⟩ := same_list hy
    obtain ⟨w1, z, rfl, k1, g⟩ := sameL_cons g
    obtain ⟨w2, z, rfl, k2, g⟩ := sameL_cons g
    cases sameL_nil g
    obtain ⟨r1, rfl⟩ := same_atom k1
    simp only [need, needs, list, atom] at hn
    have eT := ty_tySx f.2 depthMax ht k2 (by omega) hw.1
    have eR := keyFields_read key hr hrest (by omega) hw.2
    simp [Read.keyFields, eT, eR]
    rfl

theorem needs_le_of_mem : ∀ {xs : List SExp} {x : SExp}, x ∈ xs → need x ≤ needs xs
  | _ :: _, _, .head _ => by simp only [needs]; omega
  | _ :: _, _, .tail _ h => by have := needs_le_of_mem h; simp only [needs]; omega

theorem need_lt_list {p : Nat} {xs : List SExp} {x : SExp} (h : x ∈ xs) : need x < need (.list p xs) := by
  have := needs_le_of_mem h; simp only [need]; omega

/-- A relation's types are canonical: its key fields' and its value's (what `Read.ty` returns). -/
private def relWf (r : Label × RelDecl) : Bool := r.2.val.wf && r.2.key.all (fun f => f.2.wf)

theorem relSx_ok {r : Label × RelDecl} {x : SExp} (h : relSx r = some x) : Ok x := by
  simp only [relSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨xl, hl, xk, hk, xv, hv, xs, hsu, xg, hg, xh, hh, rfl⟩ := h
  exact .list (.cons (label_ok hl) (.cons (.list (.cons (kw_ok _) (keyFields_ok _ hk)))
    (.cons (.list (.cons (kw_ok _) (.cons (tySx_ok _ hv) .nil)))
    (.cons (.list (.cons (kw_ok _) (.cons (repr_ok _) .nil)))
    (.cons (.list (.cons (kw_ok _) (optLabelSx_ok _ hsu)))
    (.cons (.list (.cons (kw_ok _) (.cons (repr_ok _) .nil)))
    (.cons (.list (.cons (kw_ok _) (.cons (by split <;> exact kw_ok _) .nil)))
    (.cons (.list (.cons (kw_ok _) (optLabelSx_ok _ hg)))
    (.cons (.list (.cons (kw_ok _) (optLabelSx_ok _ hh))) .nil)))))))))

theorem rel_relSx {r : Label × RelDecl} {x y : SExp} (h : relSx r = some x) (hs : Same x y)
    (hn : need x ≤ depthMax) (hw : relWf r = true) : Read.rel y = .ok r := by
  obtain ⟨ℓ, ⟨key, val, limit, sum, cap, retract, guard, holds⟩⟩ := r
  simp only [relWf, Bool.and_eq_true] at hw
  simp only [relSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨xl, hl, xk, hk, xv, hv, xs, hsu, xg, hg, xh, hh, rfl⟩ := h
  obtain ⟨rfl, -⟩ := label_some hl
  obtain ⟨q, z, rfl, g⟩ := same_list hs
  obtain ⟨y0, z, rfl, h0, g⟩ := sameL_cons g
  obtain ⟨y1, z, rfl, h1, g⟩ := sameL_cons g
  obtain ⟨y2, z, rfl, h2, g⟩ := sameL_cons g
  obtain ⟨y3, z, rfl, h3, g⟩ := sameL_cons g
  obtain ⟨y4, z, rfl, h4, g⟩ := sameL_cons g
  obtain ⟨y5, z, rfl, h5, g⟩ := sameL_cons g
  obtain ⟨y6, z, rfl, h6, g⟩ := sameL_cons g
  obtain ⟨y7, z, rfl, h7, g⟩ := sameL_cons g
  obtain ⟨y8, z, rfl, h8, g⟩ := sameL_cons g
  cases sameL_nil g
  obtain ⟨r0, rfl⟩ := same_atom h0
  -- key
  obtain ⟨q1, z1, rfl, g1⟩ := same_list h1
  obtain ⟨w1, z1, rfl, k1, t1⟩ := sameL_cons g1
  obtain ⟨r1, rfl⟩ := same_atom k1
  -- val
  obtain ⟨q2, z2, rfl, g2⟩ := same_list h2
  obtain ⟨w2, z2, rfl, k2, g2⟩ := sameL_cons g2
  obtain ⟨v2, z2, rfl, m2, g2⟩ := sameL_cons g2
  cases sameL_nil g2
  obtain ⟨r2, rfl⟩ := same_atom k2
  -- limit
  obtain ⟨q3, z3, rfl, g3⟩ := same_list h3
  obtain ⟨w3, z3, rfl, k3, g3⟩ := sameL_cons g3
  obtain ⟨v3, z3, rfl, m3, g3⟩ := sameL_cons g3
  cases sameL_nil g3
  obtain ⟨r3, rfl⟩ := same_atom k3
  obtain ⟨s3, rfl⟩ := same_atom m3
  -- sum
  obtain ⟨q4, z4, rfl, g4⟩ := same_list h4
  obtain ⟨w4, z4, rfl, k4, t4⟩ := sameL_cons g4
  obtain ⟨r4, rfl⟩ := same_atom k4
  -- cap
  obtain ⟨q5, z5, rfl, g5⟩ := same_list h5
  obtain ⟨w5, z5, rfl, k5, g5⟩ := sameL_cons g5
  obtain ⟨v5, z5, rfl, m5, g5⟩ := sameL_cons g5
  cases sameL_nil g5
  obtain ⟨r5, rfl⟩ := same_atom k5
  obtain ⟨s5, rfl⟩ := same_atom m5
  -- retract
  obtain ⟨q6, z6, rfl, g6⟩ := same_list h6
  obtain ⟨w6, z6, rfl, k6, g6⟩ := sameL_cons g6
  obtain ⟨v6, z6, rfl, m6, g6⟩ := sameL_cons g6
  cases sameL_nil g6
  obtain ⟨r6, rfl⟩ := same_atom k6
  -- guard
  obtain ⟨q7, z7, rfl, g7⟩ := same_list h7
  obtain ⟨w7, z7, rfl, k7, t7⟩ := sameL_cons g7
  obtain ⟨r7, rfl⟩ := same_atom k7
  -- holds
  obtain ⟨q8, z8, rfl, g8⟩ := same_list h8
  obtain ⟨w8, z8, rfl, k8, t8⟩ := sameL_cons g8
  obtain ⟨r8, rfl⟩ := same_atom k8
  simp only [need, needs, list, atom] at hn
  have eK := keyFields_read key hk t1 (by omega) hw.2
  have eV := ty_tySx val depthMax hv m2 (by omega) hw.1
  have eS := optLabel_read q sum hsu t4
  have eG := optLabel_read q guard hg t7
  have eH := optLabel_read q holds hh t8
  cases retract <;>
  · obtain ⟨s6, rfl⟩ := same_atom m6
    simp [Read.rel, eK, eV, eS, eG, eH]
    rfl

theorem rels_ok : ∀ (rs : List (Label × RelDecl)) {xs : List SExp}, rs.mapM relSx = some xs → OkL xs
  | [], _, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | r :: rs, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    exact .cons (relSx_ok hx) (rels_ok rs hr)

theorem rels_mapM : ∀ (rs : List (Label × RelDecl)) {xs ys : List SExp}, rs.mapM relSx = some xs →
    SameL xs ys → needs xs ≤ depthMax → rs.all relWf = true → ys.mapM Read.rel = .ok rs
  | [], _, _, h, hs, _, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases sameL_nil hs; rfl
  | r :: rs, _, _, h, hs, hn, hw => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at hw
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    simp only [needs] at hn
    have e1 := rel_relSx hx hy (by omega) hw.1
    have e2 := rels_mapM rs hr hrest (by omega) hw.2
    simp [List.mapM_cons, e1, e2]
    rfl

/-! ## The doc (LANG-60): printed as `Read.doc` reads it -/

theorem docChar_eq : Bounds.docChar = plainChar := rfl

/-- A doc `Bounds.docOk` admits prints as a `"text"` holding exactly its bytes (never `#hex`). -/
theorem bytesSx_doc {w : ByteArray} (h : Bounds.docOk w = true) : ∃ t, bytesSx w = .str 0 t ∧ t.toUTF8 = w := by
  simp only [Bounds.docOk, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold bytesSx
  split
  · rename_i t ht
    simp only [ht] at h
    have h' : t.toList.all plainChar = true := h
    simp only [h', if_true]
    exact ⟨t, rfl, fromUTF8_toUTF8 ht⟩
  · rename_i ht
    simp [ht] at h

/-- What it prints as: a quote-free string of plain characters (`bytesSx_cases`'s left case). -/
theorem bytesSx_doc_plain {w : ByteArray} (h : Bounds.docOk w = true) :
    ∃ t, bytesSx w = .str 0 t ∧ t.toUTF8 = w ∧ '"' ∉ t.toList ∧ ∀ c ∈ t.toList, plainChar c = true := by
  obtain ⟨t, e, -⟩ := bytesSx_doc h
  rcases bytesSx_cases w with hl | e'
  · exact hl
  · rw [e] at e'; simp [atom] at e'

theorem docSx_ok {w : ByteArray} {x : SExp} (h : docSx w = some x) : Ok x := by
  unfold docSx at h
  split at h
  · cases h
    split
    · exact .list (.cons (kw_ok _) .nil)
    · exact .list (.cons (kw_ok _) (.cons (bytesSx_ok w) .nil))
  · cases h

theorem eq_empty_of_isEmpty {w : ByteArray} (h : w.isEmpty = true) : w = .empty := by
  rcases w with ⟨d⟩
  simp [ByteArray.isEmpty, ByteArray.size] at h
  simp [h]; rfl

/-- **A printed doc reads back as itself.** -/
theorem doc_read {w : ByteArray} {x y : SExp} (h : docSx w = some x) (hs : Same x y) :
    ∃ q r ds, y = .list q (.atom r "doc" :: ds) ∧ Read.doc q ds = .ok w := by
  unfold docSx at h
  split at h
  · rename_i hd
    cases h
    obtain ⟨q, zs, rfl, hz⟩ := same_list hs
    obtain ⟨z0, ds, rfl, h0, hds⟩ := sameL_cons hz
    obtain ⟨r, rfl⟩ := same_atom h0
    refine ⟨q, r, ds, rfl, ?_⟩
    by_cases he : w.isEmpty = true
    · rw [if_pos he] at hds
      cases sameL_nil hds
      rw [eq_empty_of_isEmpty he]; rfl
    · rw [if_neg he] at hds
      obtain ⟨t, ht, htw⟩ := bytesSx_doc hd
      rw [ht] at hds
      obtain ⟨z, zs, rfl, hz1, hnil⟩ := sameL_cons hds
      cases sameL_nil hnil
      obtain ⟨q', rfl⟩ := same_str hz1
      have he' : w.isEmpty = false := by simpa using he
      simp only [Read.doc, htw, hd, he', Bool.not_false, Bool.and_self, if_true]
  · cases h

/-! ## The grades (LANG-89): `(effects (ℓ N) …)` printed as `Read.effect` reads it -/

theorem effectSx_ok {e : Label × Effect} {x : SExp} (h : effectSx e = some x) : Ok x := by
  obtain ⟨ℓ, moves, produces⟩ := e
  cases produces with
  | none =>
    simp only [effectSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, rfl⟩ := h
    exact .list (.cons (label_ok hl) (.cons (repr_ok _) .nil))
  | some I =>
    simp only [effectSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xi, hi, rfl⟩ := h
    exact .list (.cons (label_ok hl) (.cons (repr_ok _) (.cons (tySx_ok I hi) .nil)))

/-- A grade reads back; a produced interface reads back when it is well-formed and the form is within
the reader's depth. -/
theorem effect_read {e : Label × Effect} {x y : SExp} (h : effectSx e = some x) (hs : Same x y)
    (hn : need x ≤ depthMax) (hw : e.2.produces.all Ty.wf = true) :
    Read.effect y = .ok e := by
  obtain ⟨ℓ, moves, produces⟩ := e
  cases produces with
  | none =>
    simp only [effectSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    obtain ⟨q, ys, rfl, hys⟩ := same_list hs
    obtain ⟨y1, ys, rfl, h1, hys⟩ := sameL_cons hys
    obtain ⟨y2, ys, rfl, h2, hys⟩ := sameL_cons hys
    cases sameL_nil hys
    obtain ⟨q1, rfl⟩ := same_atom h1
    obtain ⟨q2, rfl⟩ := same_atom h2
    simp only [Read.effect, toNat_repr]
  | some I =>
    simp only [effectSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xl, hl, xi, hi, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hl
    simp only [Option.all_some] at hw
    have hni : need xi ≤ depthMax :=
      Nat.le_trans (Nat.le_of_lt (need_lt_list (by simp))) hn
    obtain ⟨q, ys, rfl, hys⟩ := same_list hs
    obtain ⟨y1, ys, rfl, h1, hys⟩ := sameL_cons hys
    obtain ⟨y2, ys, rfl, h2, hys⟩ := sameL_cons hys
    obtain ⟨y3, ys, rfl, h3, hys⟩ := sameL_cons hys
    cases sameL_nil hys
    obtain ⟨q1, rfl⟩ := same_atom h1
    obtain ⟨q2, rfl⟩ := same_atom h2
    simp only [Read.effect, toNat_repr, ty_tySx I depthMax hi h3 hni hw, bind, Except.bind, pure, Except.pure]

theorem effects_ok : ∀ (es : List (Label × Effect)) {xs : List SExp}, es.mapM effectSx = some xs → OkL xs
  | [], _, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | e :: es, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    exact .cons (effectSx_ok hx) (effects_ok es hr)

theorem effects_mapM : ∀ (es : List (Label × Effect)) {xs ys : List SExp}, es.mapM effectSx = some xs →
    SameL xs ys → (∀ x ∈ xs, need x ≤ depthMax) → es.all (fun e => e.2.produces.all Ty.wf) = true →
    ys.mapM Read.effect = .ok es
  | [], _, _, h, hs, _, _ => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases sameL_nil hs; rfl
  | e :: es, _, _, h, hs, hn, hw => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp [List.mapM_cons, effect_read hx hy (hn x (by simp)) hw.1,
      effects_mapM es hr hrest (fun x hx => hn x (by simp [hx])) hw.2]
    rfl

/-! ## Claims (LANG-93): each prints as `Read.claim` reads it -/

theorem claimSx_ok {c : Claim} {x : SExp} (h : claimSx c = some x) : Ok x := by
  cases c with
  | keeps inv law =>
    simp only [claimSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xi, hi, xl, hl, rfl⟩ := h
    exact .list (.cons (kw_ok _) (.cons (label_ok hi) (.cons (label_ok hl) .nil)))

theorem claims_ok : ∀ (cs : List Claim) {xs : List SExp}, cs.mapM claimSx = some xs → OkL xs
  | [], _, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | c :: cs, _, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    exact .cons (claimSx_ok hx) (claims_ok cs hr)

theorem claim_claimSx {c : Claim} {x y : SExp} (h : claimSx c = some x) (hs : Same x y) :
    Read.claim y = .ok c := by
  cases c with
  | keeps inv law =>
    simp only [claimSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨xi, hi, xl, hl, rfl⟩ := h
    obtain ⟨rfl, -⟩ := label_some hi
    obtain ⟨rfl, -⟩ := label_some hl
    obtain ⟨q, zs, rfl, hz⟩ := same_list hs
    obtain ⟨y0, zs, rfl, h0, hz⟩ := sameL_cons hz
    obtain ⟨y1, zs, rfl, h1, hz⟩ := sameL_cons hz
    obtain ⟨y2, zs, rfl, h2, hz⟩ := sameL_cons hz
    cases sameL_nil hz
    obtain ⟨q0, rfl⟩ := same_atom h0
    obtain ⟨q1, rfl⟩ := same_atom h1
    obtain ⟨q2, rfl⟩ := same_atom h2
    rfl

theorem claims_mapM : ∀ (cs : List Claim) {xs ys : List SExp}, cs.mapM claimSx = some xs → SameL xs ys →
    ys.mapM Read.claim = .ok cs
  | [], _, _, h, hs => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; cases sameL_nil hs; rfl
  | c :: cs, _, _, h, hs => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xr, hr, rfl⟩ := h
    obtain ⟨y, ys, rfl, hy, hrest⟩ := sameL_cons hs
    simp [List.mapM_cons, claim_claimSx hx hy, claims_mapM cs hr hrest]
    rfl

theorem sameL_append : ∀ {xs cl zs : List SExp}, SameL (xs ++ cl) zs →
    ∃ ys ws, zs = ys ++ ws ∧ SameL xs ys ∧ SameL cl ws
  | [], _, zs, h => ⟨[], zs, rfl, .nil, h⟩
  | _ :: xs, cl, _, h => by
    obtain ⟨y, zs, rfl, hy, hrest⟩ := sameL_cons h
    obtain ⟨ys, ws, rfl, h1, h2⟩ := sameL_append hrest
    exact ⟨y :: ys, ws, rfl, .cons hy h1, h2⟩

theorem okL_append : ∀ {xs ys : List SExp}, OkL xs → OkL ys → OkL (xs ++ ys)
  | [], _, _, h => h
  | _ :: _, _, .cons hx hxs, h => .cons hx (okL_append hxs h)

/-- An optional section of `packageText`: absent exactly when its list is empty, else one `(kw …)`
form over the printed entries. -/
theorem optSection_eq {α : Type} {l : List α} {f : α → Option SExp} {kw : String} {T : List SExp}
    (h : optSection kw f l = some T) :
    (l = [] ∧ T = []) ∨ (∃ xs, l.mapM f = some xs ∧ T = [list (atom kw :: xs)]) := by
  unfold optSection at h
  by_cases hl : l.isEmpty
  · left
    simp only [hl, if_true, Option.some.injEq] at h
    exact ⟨List.isEmpty_iff.mp hl, h.symm⟩
  · right
    simp only [hl, Bool.false_eq_true, if_false] at h
    cases hm : l.mapM f with
    | none => simp [hm, bind] at h
    | some xs =>
      simp only [hm, bind, Option.bind_some, pure, Option.some.injEq] at h
      exact ⟨xs, rfl, h.symm⟩

/- A package whose body is canonical and whose state, interface and relation types are canonical
reads back from its text: `Read.readPackage` returns exactly the package that was printed. -/
/-- Printing the package sections produces valid s-expressions even for
noncanonical types; canonicality is needed for literal semantic roundtrip. -/
theorem sectionsSx_ok {p : Package} {xs : List SExp} (h : sectionsSx p = some xs) :
    OkL (atom "package" :: xs) := by
  simp only [sectionsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨xD, hD, xS, hS, xI, hI, xm, hm, xl, hlw, xR, hR, xB, hB, rfl⟩ := h
  exact .cons (kw_ok _) (.cons (.list (.cons (kw_ok _) (imports_ok _))) (.cons (docSx_ok hD)
    (.cons (.list (.cons (kw_ok _) (.cons (tySx_ok _ hS) .nil)))
    (.cons (.list (.cons (kw_ok _) (.cons (tySx_ok _ hI) .nil)))
    (.cons (.list (.cons (kw_ok _) (labels_ok _ hm)))
    (.cons (.list (.cons (kw_ok _) (labels_ok _ hlw)))
    (.cons (.list (.cons (kw_ok _) (rels_ok _ hR)))
    (.cons (.list (.cons (kw_ok _) (.cons (termSx_ok _ 0 hB) .nil))) .nil))))))))

/-- The eight printed sections, laid out at the head of any form (the optional sections follow),
read back as `Read.packageBase` of the package without its optional sections. -/
private theorem packageBase_reads {p : Package} {xs : List SExp} (hs : p.state.wf = true) (hi : p.iface.wf = true)
    (hr : p.rels.all relWf = true) (hb : Canon p.body) (hxs : sectionsSx p = some xs)
    (hn : ∀ x ∈ xs, need x < depthMax) {ys : List SExp} (hsame : SameL xs ys) (q q0 : Nat) :
    ∃ y1 y2 y3 y4 y5 y6 y7 y8, ys = [y1, y2, y3, y4, y5, y6, y7, y8] ∧
      Read.packageBase (.list q [.atom q0 "package", y1, y2, y3, y4, y5, y6, y7, y8]) =
        .ok { p with holes := [], effects := [], claims := [] } := by
  simp only [sectionsSx, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hxs
  obtain ⟨xD, hD, xS, hS, xI, hI, xm, hm, xl, hlw, xR, hR, xB, hB, rfl⟩ := hxs
  obtain ⟨y1, ys, rfl, h1, hl⟩ := sameL_cons hsame
  obtain ⟨yD, ys, rfl, hD', hlD⟩ := sameL_cons hl
  obtain ⟨qd, rd, ds, rfl, eD⟩ := doc_read hD hD'
  obtain ⟨y2, ys, rfl, h2, hl⟩ := sameL_cons hlD
  obtain ⟨y3, ys, rfl, h3, hl⟩ := sameL_cons hl
  obtain ⟨y4, ys, rfl, h4, hl⟩ := sameL_cons hl
  obtain ⟨y5, ys, rfl, h5, hl⟩ := sameL_cons hl
  obtain ⟨y6, ys, rfl, h6, hl⟩ := sameL_cons hl
  obtain ⟨y7, ys, rfl, h7, hl⟩ := sameL_cons hl
  cases sameL_nil hl
  -- imports
  obtain ⟨q1, z1, rfl, g1⟩ := same_list h1
  obtain ⟨w1, z1, rfl, k1, t1⟩ := sameL_cons g1
  obtain ⟨r1, rfl⟩ := same_atom k1
  -- state, iface, body
  obtain ⟨q2, z2, rfl, g2⟩ := same_list h2
  obtain ⟨w2, z2, rfl, k2, g2⟩ := sameL_cons g2
  obtain ⟨v2, z2, rfl, m2, g2⟩ := sameL_cons g2
  cases sameL_nil g2
  obtain ⟨r2, rfl⟩ := same_atom k2
  obtain ⟨q3, z3, rfl, g3⟩ := same_list h3
  obtain ⟨w3, z3, rfl, k3, g3⟩ := sameL_cons g3
  obtain ⟨v3, z3, rfl, m3, g3⟩ := sameL_cons g3
  cases sameL_nil g3
  obtain ⟨r3, rfl⟩ := same_atom k3
  obtain ⟨q7, z7, rfl, g7⟩ := same_list h7
  obtain ⟨w7, z7, rfl, k7, g7⟩ := sameL_cons g7
  obtain ⟨v7, z7, rfl, m7, g7⟩ := sameL_cons g7
  cases sameL_nil g7
  obtain ⟨r7, rfl⟩ := same_atom k7
  -- methods, laws
  obtain ⟨q4, z4, rfl, g4⟩ := same_list h4
  obtain ⟨w4, z4, rfl, k4, t4⟩ := sameL_cons g4
  obtain ⟨r4, rfl⟩ := same_atom k4
  obtain ⟨q5, z5, rfl, g5⟩ := same_list h5
  obtain ⟨w5, z5, rfl, k5, t5⟩ := sameL_cons g5
  obtain ⟨r5, rfl⟩ := same_atom k5
  -- rels
  obtain ⟨q6, z6, rfl, g6⟩ := same_list h6
  obtain ⟨w6, z6, rfl, k6, t6⟩ := sameL_cons g6
  obtain ⟨r6, rfl⟩ := same_atom k6
  have bS : need xS ≤ depthMax :=
    Nat.le_of_lt (Nat.lt_trans (need_lt_list (p := 0) (xs := [atom "state", xS]) (by simp)) (hn _ (by simp [list])))
  have bI : need xI ≤ depthMax :=
    Nat.le_of_lt (Nat.lt_trans (need_lt_list (p := 0) (xs := [atom "iface", xI]) (by simp)) (hn _ (by simp [list])))
  have bB : need xB ≤ depthMax :=
    Nat.le_of_lt (Nat.lt_trans (need_lt_list (p := 0) (xs := [atom "body", xB]) (by simp)) (hn _ (by simp [list])))
  have bR : needs xR ≤ depthMax := by
    have h1 : needs xR < need (list (atom "rels" :: xR)) := by
      unfold list; simp only [need, needs]; omega
    exact Nat.le_of_lt (Nat.lt_trans h1 (hn _ (by simp [list])))
  have eS := ty_tySx p.state depthMax hS m2 bS hs
  have eI := ty_tySx p.iface depthMax hI m3 bI hi
  have eB := term_termSx p.body 0 depthMax hB m7 bB hb
  rw [scope_zero] at eB
  have eM := labels_mapM p.methods hm t4
  have eL := labels_mapM p.laws hlw t5
  have eR := rels_mapM p.rels hR t6 bR hr
  refine ⟨_, _, _, _, _, _, _, _, rfl, ?_⟩
  simp only [Read.packageBase, eD, eS, eI, eB, eM, eL, eR]
  rw [mapM_imports ?hf p.imports t1]
  · rfl
  · intro q i; simp [hex, unhex_hexChars]

theorem readPackage_closedText {p : Package} {s : String} (hs : p.state.wf = true) (hi : p.iface.wf = true)
    (hr : p.rels.all relWf = true) (hb : Canon p.body) (he : p.holes = [])
    (hpw : p.effects.all (fun e => e.2.produces.all Ty.wf) = true)
    (h : packageText p = some s) : Read.readPackage s = .ok p := by
  unfold packageText at h
  generalize hE : optSection "effects" effectSx p.effects = mE at h
  generalize hC : optSection "claims" claimSx p.claims = mC at h
  cases mE with
  | none => simp [bind] at h
  | some E =>
  cases mC with
  | none => simp [bind] at h
  | some C =>
  simp only [he, List.isEmpty_nil, if_true, bind, Option.bind_eq_some_iff, Option.bind_some] at h
  obtain ⟨xs, hxs, h⟩ := h
  simp only [List.append_nil] at h
  split at h
  · rename_i hf
    obtain ⟨hn, hw⟩ := fitsB_iff.mp hf
    simp only [pure, Option.some.injEq] at h; subst h
    have hxn : ∀ x ∈ xs, need x < depthMax := fun x hx =>
      Nat.lt_of_lt_of_le (need_lt_list (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hx)))) hn
    have hokx : OkL xs := by cases sectionsSx_ok hxs; assumption
    rcases optSection_eq hE with ⟨hpe, rfl⟩ | ⟨xE, hmE, rfl⟩ <;>
      rcases optSection_eq hC with ⟨hpc, rfl⟩ | ⟨xC, hmC, rfl⟩
    · -- neither section
      simp only [List.append_nil] at hn hw ⊢
      obtain ⟨ys, hy, hsame⟩ := parse_layout (sep := ['\n', ' ', ' ']) ⟨by decide, by decide⟩ (sectionsSx_ok hxs) hn hw
      simp only [Read.readPackage, hy, bind, Except.bind]
      obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hsame
      obtain ⟨r0, rfl⟩ := same_atom h0
      obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, rfl, hbase⟩ :=
        packageBase_reads hs hi hr hb hxs (fun x hx => Nat.lt_of_lt_of_le (need_lt_list (List.mem_cons_of_mem _ hx)) hn) hl 0 r0
      have hp : { p with holes := [], effects := [], claims := [] } = p := by
        obtain ⟨⟩ := p; simp only at he hpe hpc; subst he hpe hpc; rfl
      simp only [Read.package, hbase, hp]
    all_goals
      first
      | (have hok : OkL (atom "package" :: (xs ++ [list (atom "claims" :: xC)])) :=
          .cons (kw_ok _) (okL_append hokx (.cons (.list (.cons (kw_ok _) (claims_ok _ hmC))) .nil))
         simp only [List.append_nil] at hn hw ⊢
         obtain ⟨ys, hy, hsame⟩ := parse_layout (sep := ['\n', ' ', ' ']) ⟨by decide, by decide⟩ hok hn hw
         simp only [Read.readPackage, hy, bind, Except.bind]
         obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hsame
         obtain ⟨r0, rfl⟩ := same_atom h0
         obtain ⟨ys8, ws, rfl, h8, hT⟩ := sameL_append hl
         obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, rfl, hbase⟩ := packageBase_reads hs hi hr hb hxs hxn h8 0 r0
         obtain ⟨yc, ws, rfl, hyc, hw0⟩ := sameL_cons hT
         cases sameL_nil hw0
         obtain ⟨qc, zc, rfl, gc⟩ := same_list hyc
         obtain ⟨wc, zc, rfl, kc, tc⟩ := sameL_cons gc
         obtain ⟨rc, rfl⟩ := same_atom kc
         have eC := claims_mapM p.claims hmC tc
         have hp : { ({ p with holes := [], effects := [], claims := [] } : Package) with claims := p.claims } = p := by
           obtain ⟨⟩ := p; simp only at he hpe; subst he hpe; rfl
         simp only [List.cons_append, List.nil_append, Read.package, hbase, eC, bind, Except.bind, pure, Except.pure, hp])
      | (have hok : OkL (atom "package" :: (xs ++ [list (atom "effects" :: xE)])) :=
          .cons (kw_ok _) (okL_append hokx (.cons (.list (.cons (kw_ok _) (effects_ok _ hmE))) .nil))
         simp only [List.append_nil] at hn hw ⊢
         obtain ⟨ys, hy, hsame⟩ := parse_layout (sep := ['\n', ' ', ' ']) ⟨by decide, by decide⟩ hok hn hw
         simp only [Read.readPackage, hy, bind, Except.bind]
         obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hsame
         obtain ⟨r0, rfl⟩ := same_atom h0
         obtain ⟨ys8, ws, rfl, h8, hT⟩ := sameL_append hl
         obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, rfl, hbase⟩ := packageBase_reads hs hi hr hb hxs hxn h8 0 r0
         obtain ⟨ye, ws, rfl, hye, hw0⟩ := sameL_cons hT
         cases sameL_nil hw0
         obtain ⟨qe, ze, rfl, ge⟩ := same_list hye
         obtain ⟨we, ze, rfl, ke, te⟩ := sameL_cons ge
         obtain ⟨re, rfl⟩ := same_atom ke
         have eE := effects_mapM p.effects hmE te (fun x hx => by
           have h1 : need x < need (list (atom "effects" :: xE)) := need_lt_list (List.mem_cons_of_mem _ hx)
           have h2 : need (list (atom "effects" :: xE)) <
               need (list (atom "package" :: (xs ++ [list (atom "effects" :: xE)]))) := need_lt_list (by simp)
           omega) hpw
         have hp : { ({ p with holes := [], effects := [], claims := [] } : Package) with effects := p.effects } = p := by
           obtain ⟨⟩ := p; simp only at he hpc; subst he hpc; rfl
         simp only [List.cons_append, List.nil_append, Read.package, hbase, eE, bind, Except.bind, pure, Except.pure, hp])
      | (have hok : OkL (atom "package" :: (xs ++ [list (atom "effects" :: xE)] ++ [list (atom "claims" :: xC)])) :=
          .cons (kw_ok _) (okL_append (okL_append hokx (.cons (.list (.cons (kw_ok _) (effects_ok _ hmE))) .nil))
            (.cons (.list (.cons (kw_ok _) (claims_ok _ hmC))) .nil))
         obtain ⟨ys, hy, hsame⟩ := parse_layout (sep := ['\n', ' ', ' ']) ⟨by decide, by decide⟩ hok hn hw
         simp only [Read.readPackage, hy, bind, Except.bind]
         obtain ⟨y0, ys, rfl, h0, hl⟩ := sameL_cons hsame
         obtain ⟨r0, rfl⟩ := same_atom h0
         rw [List.append_assoc] at hl
         obtain ⟨ys8, ws, rfl, h8, hT⟩ := sameL_append hl
         obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, rfl, hbase⟩ := packageBase_reads hs hi hr hb hxs hxn h8 0 r0
         obtain ⟨ye, ws, rfl, hye, hw0⟩ := sameL_cons hT
         obtain ⟨yc, ws, rfl, hyc, hw1⟩ := sameL_cons hw0
         cases sameL_nil hw1
         obtain ⟨qe, ze, rfl, ge⟩ := same_list hye
         obtain ⟨we, ze, rfl, ke, te⟩ := sameL_cons ge
         obtain ⟨re, rfl⟩ := same_atom ke
         obtain ⟨qc, zc, rfl, gc⟩ := same_list hyc
         obtain ⟨wc, zc, rfl, kc, tc⟩ := sameL_cons gc
         obtain ⟨rc, rfl⟩ := same_atom kc
         have eE := effects_mapM p.effects hmE te (fun x hx => by
           have h1 : need x < need (list (atom "effects" :: xE)) := need_lt_list (List.mem_cons_of_mem _ hx)
           have h2 : need (list (atom "effects" :: xE)) <
               need (list (atom "package" :: (xs ++ [list (atom "effects" :: xE)] ++ [list (atom "claims" :: xC)]))) :=
             need_lt_list (by simp)
           omega) hpw
         have eC := claims_mapM p.claims hmC tc
         have hp : { ({ p with holes := [], effects := [], claims := [] } : Package) with effects := p.effects, claims := p.claims } = p := by
           obtain ⟨⟩ := p; simp only at he; subst he; rfl
         simp only [List.cons_append, List.nil_append, Read.package, hbase, eE, eC, bind, Except.bind, pure, Except.pure, hp])
  · cases h

theorem readPackage_package {p : Package} {s : String} (hs : p.state.wf = true) (hi : p.iface.wf = true)
    (hr : p.rels.all relWf = true) (hb : Canon p.body)
    (hpw : p.effects.all (fun e => e.2.produces.all Ty.wf) = true)
    (h : package p = some s) : Read.readPackage s = .ok p := by
  unfold package at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨text, ht, h⟩ := h
  split at h
  · rename_i hempty
    have he : p.holes = [] := List.isEmpty_iff.mp hempty
    cases h
    exact readPackage_closedText hs hi hr hb he hpw ht
  · unfold contextualText at h
    split at h
    · split at h
      · rename_i he
        subst he
        cases h
        assumption
      · cases h
    · cases h

/-! ## Every checked term is canonical, so every checked term and package reads back -/

theorem armsTy_labels {Δ : List Ty} : ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
    ArmsTy Δ Γ arms r B → arms.map Prod.fst = r.map Prod.fst
  | _, _, _, _, .one _ => rfl
  | _, _, _, _, .cons _ h _ => by simp [armsTy_labels h]

mutual
theorem hasType_canon {Δ : List Ty} (hΔ : ∀ A ∈ Δ, A.wf = true) :
    ∀ {Γ : List Ty} {t : Term} {T : Ty}, (∀ A ∈ Γ, A.wf = true) → HasType Δ Γ t T → Canon t
  | _, _, _, _, .var _ => .var
  | _, _, _, hΓ, .lam hA hb => .lam hA (hasType_canon hΔ (cons_wf hA hΓ) hb)
  | _, _, _, hΓ, .app hf ha => .app (hasType_canon hΔ hΓ hf) (hasType_canon hΔ hΓ ha)
  | _, _, _, hΓ, .fix ht => .fix (hasType_canon hΔ hΓ ht)
  | _, _, _, _, .nat _ => .nat
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .bytes _ => .bytes
  | _, _, _, _, .digest _ => .digest
  | _, _, _, hΓ, .prim ha hb => .prim (hasType_canon hΔ hΓ ha) (hasType_canon hΔ hΓ hb)
  | _, _, _, hΓ, .record hasc hfs => .record hasc (fieldsTy_canon hΔ hΓ hfs)
  | _, _, _, hΓ, .get ht _ => .get (hasType_canon hΔ hΓ ht)
  | _, _, _, hΓ, .extend ht hasc hfs => .extend (hasType_canon hΔ hΓ ht) hasc (fieldsTy_canon hΔ hΓ hfs)
  | _, _, _, hΓ, .inj hw _ ht => .inj hw (hasType_canon hΔ hΓ ht)
  | _, _, _, hΓ, .case ht ha => by
    have hw := hasType_wf hΔ hΓ ht
    simp only [Ty.wf, Bool.and_eq_true] at hw
    exact .case (hasType_canon hΔ hΓ ht) ((Row.ascending_of_labels (armsTy_labels ha)) ▸ hw.1)
      (armsTy_canon hΔ hΓ hw.2 ha)
  | _, _, _, hΓ, .ite hc ha hb => .ite (hasType_canon hΔ hΓ hc) (hasType_canon hΔ hΓ ha) (hasType_canon hΔ hΓ hb)
  | _, _, _, _, .ref _ => .ref
  | _, _, _, _, .refuse hw _ => .refuse hw

theorem fieldsTy_canon {Δ : List Ty} (hΔ : ∀ A ∈ Δ, A.wf = true) :
    ∀ {Γ : List Ty} {fs : List (Label × Term)} {r : List (Label × Ty)},
      (∀ A ∈ Γ, A.wf = true) → FieldsTy Δ Γ fs r → CanonRow fs
  | _, _, _, _, .nil => .nil
  | _, _, _, hΓ, .cons ht hfs => .cons (hasType_canon hΔ hΓ ht) (fieldsTy_canon hΔ hΓ hfs)

theorem armsTy_canon {Δ : List Ty} (hΔ : ∀ A ∈ Δ, A.wf = true) :
    ∀ {Γ : List Ty} {arms : List (Label × Term)} {r : List (Label × Ty)} {B : Ty},
      (∀ A ∈ Γ, A.wf = true) → Ty.rowWf r = true → ArmsTy Δ Γ arms r B → CanonRow arms
  | _, _, _, _, hΓ, hr, .one hb => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hr
    exact .cons (hasType_canon hΔ (cons_wf hr.1 hΓ) hb) .nil
  | _, _, _, _, hΓ, hr, .cons hb ha _ => by
    simp only [Ty.rowWf, Bool.and_eq_true] at hr
    exact .cons (hasType_canon hΔ (cons_wf hr.1 hΓ) hb) (armsTy_canon hΔ hΓ hr.2 ha)
end

/-- A closed term that checks reads back from its text. -/
theorem readTerm_checked {Δ : List Ty} {t : Term} {T : Ty} {s : String} (hΔ : ∀ A ∈ Δ, A.wf = true)
    (hc : inferE Δ [] t (Ω := []) = .ok T) (h : term t = some s) : readTerm s = .ok t :=
  readTerm_term (hasType_canon hΔ (by simp) (inferE_sound hc)) h

theorem checkShape_wf {p : Package} (h : p.checkShape = .ok ()) : p.state.wf = true ∧ p.iface.wf = true := by
  unfold Package.checkShape at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.pure, pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals
    rename_i hr hi
    refine ⟨?_, by simpa using hi⟩
    have hr : isRecordData p.state = true := by simpa using hr
    revert hr
    cases p.state <;> simp [isRecordData]
    intro h _; exact h

theorem rowWf_iff : ∀ r : List (Label × Ty), Ty.rowWf r = true ↔ ∀ f ∈ r, f.2.wf = true
  | [] => by simp [Ty.rowWf]
  | (ℓ, t) :: r => by simp [Ty.rowWf, rowWf_iff r]

theorem relWf_of {ℓ : Label} {d : RelDecl} (hk : (keyTy d).wf = true) (hv : d.val.wf = true) :
    relWf (ℓ, d) = true := by
  simp only [keyTy, Ty.wf, Bool.and_eq_true] at hk
  have hall := (rowWf_iff _).mp hk.2
  simp only [relWf, hv, Bool.true_and, List.all_eq_true]
  intro f hf
  exact hall f ((Row.sort_perm d.key).mem_iff.mpr hf)

/-- The install check's relation clause makes every relation's types canonical: its value's
(`badRel`) and its key fields' (`relKey`: the key record, its fields sorted, is canonical). -/
theorem checkRel_wf {S : Ty} {row : List (Label × Ty)} {r : Label × RelDecl}
    (h : checkRel S row r = .ok ()) : relWf r = true := by
  obtain ⟨ℓ, d⟩ := r
  unfold checkRel at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first | cases h | skip
  all_goals exact relWf_of (by simp_all) (by simp_all)

theorem checkRels_wf {S : Ty} {row : List (Label × Ty)} {rels : List (Label × RelDecl)}
    (h : checkRels S row rels = .ok ()) : rels.all relWf = true := by
  unfold checkRels at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i v hfor
  cases v
  rw [List.all_eq_true]
  refine forIn_yield_ok _ _ _ (fun r u s hs => ?_) hfor
  split at hs
  · cases hs
  · rename_i hc; cases hs; exact ⟨rfl, checkRel_wf hc⟩

theorem checkFields_rels {p : Package} (h : p.checkFields = .ok ()) : p.rels.all relWf = true := by
  unfold Package.checkFields at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hr; exact checkRels_wf hr
  · cases h

/-- The install check's grade clause makes every interface a method declares it produces a
well-formed record (`badProduces`, LANG-103). -/
theorem checkEffects_produces_wf {p : Package} {row : List (Label × Ty)} (h : checkEffects p row = .ok ()) :
    p.effects.all (fun e => e.2.produces.all Ty.wf) = true := by
  unfold checkEffects at h
  repeat' split at h
  all_goals first | cases h | skip
  rename_i hnone
  rw [List.all_eq_true]
  intro e he
  have hn := List.find?_eq_none.mp hnone e he
  cases hp : e.2.produces with
  | none => rfl
  | some I =>
    rw [hp] at hn
    simp at hn
    simp only [Option.all_some]
    cases I <;> simp_all [producesOk]

theorem checkFields_produces_wf {p : Package} (h : p.checkFields = .ok ()) :
    p.effects.all (fun e => e.2.produces.all Ty.wf) = true := by
  unfold Package.checkFields at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i he; exact checkEffects_produces_wf he
  · cases h

/-- A package the install check accepts reads back from its text (over canonical import
interfaces; `Package.checkShape` checks the package's own types). -/
theorem readPackage_checked {ifaces : List Ty} {p : Package} {s : String} (hΔ : ∀ A ∈ ifaces, A.wf = true)
    (hc : p.checkWith ifaces = .ok ()) (h : package p = some s) : Read.readPackage s = .ok p := by
  have hfields := (checkWith_checked hc).2
  unfold Package.checkWith at hc
  split at hc
  · cases hc
  · cases hc
  · rename_i hshape hbody
    obtain ⟨hS, hI⟩ := checkShape_wf hshape
    unfold checkE at hbody
    split at hbody
    · rename_i T hT
      split at hbody
      · rename_i heq
        subst heq
        exact readPackage_package hS hI (checkFields_rels hfields) (hasType_canon hΔ (by simp) (inferE_sound hT))
          (checkFields_produces_wf hfields) h
      · cases hbody
    · cases hbody

end Nanodregg.Lang.Print
