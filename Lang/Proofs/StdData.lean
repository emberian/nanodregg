/- Meaning of generated structural equality over canonical first-order data. -/
import Lang.StdData
import Lang.Proofs.Meaning
import Lang.Proofs.Data
import Lang.Proofs.Canon

namespace Nanodregg.Lang.Std

private theorem eqData_apply {lib : List Term} {env : Env} {T : Ty}
    {x y : Term} {d e : Data} {b : Bool}
    (hx : BigStep lib env x (.ok d.toVal))
    (hy : BigStep lib env y (.ok e.toVal))
    (hb : BigStep lib (e.toVal :: d.toVal :: env) (eqDataBody T) (.ok (.bool b))) :
    BigStep lib env (eqData T x y) (.ok (.bool b)) :=
  .app (.app .lam hx .lam) hy hb

private theorem data_get {lib : List Term} {env : Env} {i : Nat}
    {ds : List (Label × Data)} {l : Label} {d : Data}
    (hi : env[i]? = some (Data.record ds).toVal) (hf : Row.find? l ds = some d) :
    BigStep lib env (.get (.var i) l) (.ok d.toVal) := by
  apply BigStep.get (.var hi)
  apply Sel.field (t := .var 0) (env := [d.toVal]) _ (.var rfl)
  clear hi
  induction ds with
  | nil => simp [Row.find?] at hf
  | cons p ds ih =>
    rcases p with ⟨k, e⟩
    simp only [Data.rowToVal, Row.find?] at hf ⊢
    split at hf <;> simp_all

private theorem conform_find {ds : List (Label × Data)} {r : List (Label × Ty)}
    (hd : RowConforms ds r) {l : Label} {T : Ty} (hf : Row.find? l r = some T) :
    ∃ d, Row.find? l ds = some d ∧ Conforms d T := by
  induction r generalizing ds with
  | nil => simp [Row.find?] at hf
  | cons p r ih =>
    rcases p with ⟨k, A⟩
    cases hd with
    | cons h hr =>
      simp only [Row.find?] at hf ⊢
      split at hf
      · rename_i he; cases hf; exact ⟨_, by simp [he], h⟩
      · rename_i he; simpa [he] using ih hr hf
  
private theorem canon_find {r : List (Label × Ty)} (ha : Row.ascending r = true)
    {l : Label} {T : Ty} (hm : (l, T) ∈ r) : Row.find? l r = some T := by
  induction r with
  | nil => cases hm
  | cons p r ih =>
    rcases p with ⟨k, A⟩
    obtain ⟨hlt, ht⟩ := Row.ascending_cons_iff.mp ha
    rcases List.mem_cons.mp hm with he | htail
    · cases he; simp [Row.find?]
    · have hn : l ≠ k := by
        intro he; subst he
        exact (String.lt_irrefl _ (hlt (l, T) htail))
      simpa [Row.find?, hn] using ih ht htail

private theorem conform_ext {ds es : List (Label × Data)} {r : List (Label × Ty)}
    (hd : RowConforms ds r) (he : RowConforms es r) (ha : Row.ascending r = true)
    (hh : ∀ l T, (l, T) ∈ r → Row.find? l ds = Row.find? l es) : ds = es := by
  induction r generalizing ds es with
  | nil => cases hd; cases he; rfl
  | cons p r ih =>
    rcases p with ⟨k, A⟩
    cases hd with
    | cons hd hr =>
     cases he with
     | cons he hs =>
        have hhead := hh k A (by simp)
        simp only [Row.find?, if_true, Option.some.injEq] at hhead
        subst hhead
        have ht := Row.ascending_cons_iff.mp ha
        have htail := ih hr hs ht.2 (by
          intro l T hm
          have hn : l ≠ k := by
            intro h; subst h; exact String.lt_irrefl _ (ht.1 (l, T) hm)
          simpa [Row.find?, hn] using hh l T (List.mem_cons_of_mem _ hm))
        rw [htail]
  
private theorem find_map {α β : Type} (f : Label → α → β) {l : Label} :
    ∀ {r : List (Label × α)} {a : α}, Row.find? l r = some a →
      Row.find? l (r.map fun p => (p.1, f p.1 p.2)) = some (f l a)
  | [], _, h => by simp [Row.find?] at h
  | (k, t) :: r, a, h => by
    simp only [Row.find?, List.map_cons] at h ⊢
    split at h
    · rename_i he; subst he; cases h; simp
    · rename_i he; simpa [he] using find_map f h

private theorem find_mem {α : Type} {l : Label} {a : α} :
    ∀ {r : List (Label × α)}, Row.find? l r = some a → (l, a) ∈ r
  | [], h => by simp [Row.find?] at h
  | (k, t) :: r, h => by
    simp only [Row.find?] at h
    split at h
    · rename_i he; subst he; cases h; simp
    · exact List.mem_cons_of_mem _ (find_mem h)

private theorem fields_meaning {lib : List Term} {env : Env}
    {ds es : List (Label × Data)} :
    ∀ r : List (Label × Ty),
      (∀ l T, (l, T) ∈ r → ∃ d e b,
        Row.find? l ds = some d ∧ Row.find? l es = some e ∧
        BigStep lib (e.toVal :: d.toVal :: (Data.record es).toVal :: (Data.record ds).toVal :: env)
          (eqDataBody T) (.ok (.bool b)) ∧ (b = true ↔ d = e)) →
      ∃ b, BigStep lib ((Data.record es).toVal :: (Data.record ds).toVal :: env)
        (eqDataFields r) (.ok (.bool b)) ∧
        (b = true ↔ ∀ l T, (l, T) ∈ r → Row.find? l ds = Row.find? l es)
  | [], _ => ⟨true, by rw [eqDataFields]; exact .bool, by simp⟩
  | (l, T) :: r, hh => by
    obtain ⟨d, e, b, hd, he, hb, hi⟩ := hh l T (by simp)
    obtain ⟨c, hc, hj⟩ := fields_meaning r (fun k U hm => hh k U (List.mem_cons_of_mem _ hm))
    have hcomp := eqData_apply (data_get (i := 1) rfl hd) (data_get (i := 0) rfl he) hb
    refine ⟨b && c, ?_, ?_⟩
    · rw [eqDataFields]
      cases b
      · exact .iteF hcomp .bool
      · exact .iteT hcomp hc
    · simp only [Bool.and_eq_true, hi, hj]
      constructor
      · rintro ⟨hde, ht⟩ k U hm
        rcases List.mem_cons.mp hm with h | hm
        · cases h; simpa [hd, he] using congrArg some hde
        · exact ht k U hm
      · intro h
        refine ⟨?_, fun k U hm => h k U (List.mem_cons_of_mem _ hm)⟩
        have hh := h l T (by simp)
        simpa [hd, he] using hh

/-- The generated body terminates with the mathematical equality result on any
two conforming values of a canonical type. This includes both unequal values
and equal values, rather than assuming that a comparison already returned. -/
theorem eqDataBody_meaning (T : Ty) {lib : List Term} {env : Env}
    {d e : Data} (hw : T.wf = true) (hd : Conforms d T) (he : Conforms e T) :
    ∃ b, BigStep lib (e.toVal :: d.toVal :: env) (eqDataBody T) (.ok (.bool b)) ∧
      (b = true ↔ d = e) := by
  cases hT : T <;> rw [hT] at hw hd he
  case nat =>
    cases hd with | nat hn =>
      cases he with | nat hm =>
        rename_i n m
        refine ⟨decide (n = m), ?_, by simp⟩
        rw [eqDataBody]
        exact BigStep.prim (p := .eq) (x := .nat n) (y := .nat m)
          (a := .var 1) (b := .var 0) (env := (Data.nat m).toVal :: (Data.nat n).toVal :: env)
          (.var rfl) (.var rfl) (by simp [primEval])
  case bytes =>
    cases hd with | bytes hn =>
      cases he with | bytes hm =>
        rename_i n m
        refine ⟨decide (n = m), ?_, by simp⟩
        rw [eqDataBody]
        exact BigStep.prim (p := .beq) (x := .bytes n) (y := .bytes m)
          (a := .var 1) (b := .var 0) (env := (Data.bytes m).toVal :: (Data.bytes n).toVal :: env)
          (.var rfl) (.var rfl) (by simp [primEval])
  case digest =>
    cases hd with | digest hn =>
      cases he with | digest hm =>
        rename_i n m
        refine ⟨decide (n = m), ?_, by simp⟩
        rw [eqDataBody]
        exact BigStep.prim (p := .deq) (x := .digest n) (y := .digest m)
          (a := .var 1) (b := .var 0) (env := (Data.digest m).toVal :: (Data.digest n).toVal :: env)
          (.var rfl) (.var rfl) (by simp [primEval])
  case bool =>
    cases hd; cases he
    rename_i n m
    cases n <;> cases m
    · exact ⟨true, by rw [eqDataBody]; exact .iteF (.var rfl) (.iteF (.var rfl) .bool), by simp⟩
    · exact ⟨false, by rw [eqDataBody]; exact .iteF (.var rfl) (.iteT (.var rfl) .bool), by simp⟩
    · exact ⟨false, by rw [eqDataBody]; exact .iteT (.var rfl) (.var rfl), by simp⟩
    · exact ⟨true, by rw [eqDataBody]; exact .iteT (.var rfl) (.var rfl), by simp⟩
  case fn A B => cases hd
  case record r =>
    cases hd with | record hd =>
      cases he with | record he =>
        rename_i ds es
        have hw' : Row.ascending r = true ∧ Ty.rowWf r = true := by simpa only [Ty.wf, Bool.and_eq_true] using hw
        obtain ⟨b, hb, hi⟩ := fields_meaning (lib := lib) (env := env) (ds := ds) (es := es) r (by
          intro l U hm
          have hf := canon_find hw'.1 hm
          obtain ⟨x, hx, hxt⟩ := conform_find hd hf
          obtain ⟨y, hy, hyt⟩ := conform_find he hf
          obtain ⟨b, hb, hi⟩ := eqDataBody_meaning U (rowWf_iff.mp hw'.2 (l, U) hm) hxt hyt
          exact ⟨x, y, b, hx, hy, hb, hi⟩)
        refine ⟨b, by rw [eqDataBody]; exact hb, ?_⟩
        rw [hi]
        constructor
        · intro h; exact congrArg Data.record (conform_ext hd he hw'.1 h)
        · intro h; cases h; intro l U hm; rfl
  case sum r =>
    cases hd with | inj hf hd =>
      cases he with | inj hg he =>
        rename_i l A x k B y
        have hw' : Row.ascending r = true ∧ Ty.rowWf r = true := by simpa only [Ty.wf, Bool.and_eq_true] using hw
        by_cases hl : l = k
        · subst k
          have hAB : A = B := Option.some.inj (hf.symm.trans hg)
          subst B
          obtain ⟨b, hb, hi⟩ := eqDataBody_meaning A (rowWf_find hw'.2 hf) hd he
          refine ⟨b, ?_, by simpa using hi⟩
          rw [eqDataBody]
          rw [List.attach_map_val (l := r) (f := fun (p : Label × Ty) => (p.1, Term.case (.var 1)
            (r.map fun q => (q.1, if p.1 = q.1 then Term.app (.app (.lam p.2 (.lam p.2 (eqDataBody p.2))) (.var 1)) (.var 0) else .bool false))))]
          apply BigStep.case (ℓ := l) (w := x.toVal) (BigStep.var (i := 1) rfl)
          · exact find_map (fun l A => Term.case (.var 1)
              (r.map fun q => (q.1, if l = q.1 then
                Term.app (.app (.lam A (.lam A (eqDataBody A))) (.var 1)) (.var 0)
                else .bool false))) hf
          apply BigStep.case (ℓ := l) (w := y.toVal) (BigStep.var (i := 1) rfl)
          · exact find_map (fun k _ => if l = k then eqData A (.var 1) (.var 0) else .bool false) hf
          simp only [↓reduceIte]
          exact eqData_apply (.var rfl) (.var rfl) hb
        · refine ⟨false, ?_, by simp [hl]⟩
          rw [eqDataBody]
          rw [List.attach_map_val (l := r) (f := fun (p : Label × Ty) => (p.1, Term.case (.var 1)
            (r.map fun q => (q.1, if p.1 = q.1 then Term.app (.app (.lam p.2 (.lam p.2 (eqDataBody p.2))) (.var 1)) (.var 0) else .bool false))))]
          apply BigStep.case (ℓ := l) (w := x.toVal) (BigStep.var (i := 1) rfl)
          · exact find_map (fun l A => Term.case (.var 1)
              (r.map fun q => (q.1, if l = q.1 then
                Term.app (.app (.lam A (.lam A (eqDataBody A))) (.var 1)) (.var 0)
                else .bool false))) hf
          apply BigStep.case (ℓ := k) (w := y.toVal) (BigStep.var (i := 1) rfl)
          · exact find_map (fun k _ => if l = k then eqData A (.var 1) (.var 0) else .bool false) hg
          simp only [if_neg hl]
          exact .bool
termination_by sizeOf T
decreasing_by
  all_goals first
    | (have h := List.sizeOf_lt_of_mem hm; simp_all; omega)
    | (have h := List.sizeOf_lt_of_mem (find_mem hf); simp_all; omega)

/-- Structural comparison returns true exactly for equal data. Operand meanings
tie the result to the actual input terms; canonical types exclude hidden
duplicate record fields. No existing Std theorem is changed. -/
theorem eqData_true {lib : List Term} {env : Env} {T : Ty} {x y : Term}
    {dx dy : Data} {b : Bool} (hw : T.wf = true)
    (hx : BigStep lib env x (.ok dx.toVal)) (hy : BigStep lib env y (.ok dy.toVal))
    (h : BigStep lib env (eqData T x y) (.ok (.bool b)))
    (hdx : Conforms dx T) (hdy : Conforms dy T) : b = true ↔ dx = dy := by
  obtain ⟨c, hc, hi⟩ := eqDataBody_meaning T hw hdx hdy
  have he := bigStep_deterministic h (eqData_apply hx hy hc)
  cases he
  exact hi


end Nanodregg.Lang.Std
