/-
# Lang.Proofs.Quote — the quoter writes the encoder's bytes (LANG-87)

`quotePackage_sound`: under an environment where every parameter term evaluates to a scalar of its
declared type (`Params`), the term `Lang.Quote.quotePackage ps buf p` means `b ++ B` whenever `buf`
means `b` and `Wire.encodePackage (fillPackage vals p) = some B` fits in a byte value — so a nano
generator written with the quoter installs exactly the package its Lean specification writes at
the parameters' values, and the specification's theorems are about what the kernel checked.

The proof is one induction over the template (`quoteTerm_sound`, mutual with the field and term
lists) in which every case is the same step: a node's bytes are its frame, then its children's,
and `Appends` composes (`Appends.comp`). `putD_frame` says the frame the quoter writes IS the
prefix `Tree.putD` writes; `putD_of_fits` lets a closed subtree written at `depthMax` stand for
the same subtree written at the depth the enclosing node leaves it; the four parameter writers
are `appends_nat`/`appends_bytes`/`appends_digest`/`appends_bool`.
-/
import Lang.Quote
import Lang.Proofs.BigStep
import Codec.Proofs.Tree
import Lang.Proofs.Wire
import Lang.Proofs.Receiver

namespace Nanodregg.Lang.Quote

open Nanodregg.Codec Nanodregg.Lang.Wire

/-! ## Trees: fits and putD -/

theorem fits_zero (max : Nat) (t : Tree) : t.fits max 0 = false := by cases t; rfl

theorem fits_succ {max d : Nat} {tag : UInt8} {p : ByteArray} {cs : List Tree} :
    (Tree.node tag p cs).fits max (d + 1) = true ↔
      p.size ≤ max ∧ cs.length ≤ max ∧ ∀ c ∈ cs, c.fits max d = true := by
  simp [Tree.fits, List.all_eq_true, and_assoc]

/-- A tree that fits at `n` is written the same at every depth from `n` up. -/
theorem putD_of_fits {max : Nat} : ∀ {n m : Nat} {t : Tree} (buf : ByteArray),
    t.fits max n = true → n ≤ m → Tree.putD m t buf = Tree.putD n t buf
  | 0, _, t, _, h, _ => by rw [fits_zero] at h; cases h
  | n + 1, m, .node tag p cs, buf, h, hnm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨-, -, hk⟩ := fits_succ.mp h
    simp only [Tree.putD]
    have : ∀ (l : List Tree), (∀ c ∈ l, c.fits max n = true) → ∀ out,
        l.foldl (fun o c => Tree.putD m c o) out = l.foldl (fun o c => Tree.putD n c o) out := by
      intro l hl
      induction l with
      | nil => intro out; rfl
      | cons c l ih =>
        intro out
        simp only [List.foldl_cons]
        rw [putD_of_fits out (hl c (by simp)) (by omega), ih (fun c hc => hl c (by simp [hc]))]
    exact this cs hk _

/-- The quoter's frame is the prefix `putD` writes before a node's children. -/
theorem putD_frame (m : Nat) (tag : UInt8) (p : ByteArray) (cs : List Tree) :
    Tree.putD (m + 1) (.node tag p cs) ByteArray.empty = frame tag p cs.length ++ Tree.kidsBytes m cs := by
  rw [Tree.putD_node]; rfl

theorem treeBytes_eq {n : Nat} {t : Tree} (h : t.fits nodeMax n = true) (hn : n ≤ depthMax) :
    treeBytes t = Tree.putD n t ByteArray.empty := putD_of_fits _ h hn

theorem fieldsTree_length (fs : List (Label × Term)) : (fieldsTree fs).length = fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [fieldsTree, ih]

theorem termsTree_length (ts : List Term) : (termsTree ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [termsTree, ih]

theorem fillFields_length (vals : List Val) (d : Nat) (fs : List (Label × Term)) :
    (Term.fillFields vals d fs).length = fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => obtain ⟨ℓ, t⟩ := f; simp [Term.fillFields, ih]

theorem fillTerms_length (vals : List Val) (d : Nat) (ts : List Term) :
    (Term.fillTerms vals d ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.fillTerms, ih]

/-! ## Filling a closed term changes nothing -/

mutual
theorem fill_closed (vals : List Val) : ∀ (t : Term) (d : Nat), Term.closedAt d t = true → t.fill vals d = t
  | .var i, d, h => by
    simp only [Term.closedAt, decide_eq_true_eq] at h
    simp [Term.fill, h]
  | .lam A b, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fill_closed vals b (d + 1) h]
  | .app f a, d, h => by
    simp only [Term.closedAt, Bool.and_eq_true] at h
    simp [Term.fill, fill_closed vals f d h.1, fill_closed vals a d h.2]
  | .fix t, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fill_closed vals t d h]
  | .nat _, _, _ | .bool _, _, _ | .bytes _, _, _ | .digest _, _, _ | .ref _, _, _ | .refuse _ _, _, _ => rfl
  | .prim p a b, d, h => by
    simp only [Term.closedAt, Bool.and_eq_true] at h
    simp [Term.fill, fill_closed vals a d h.1, fill_closed vals b d h.2]
  | .record fs, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fillFields_closed vals fs d h]
  | .get t ℓ, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fill_closed vals t d h]
  | .extend t fs, d, h => by
    simp only [Term.closedAt, Bool.and_eq_true] at h
    simp [Term.fill, fill_closed vals t d h.1, fillFields_closed vals fs d h.2]
  | .inj A ℓ t, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fill_closed vals t d h]
  | .case t arms, d, h => by
    simp only [Term.closedAt, Bool.and_eq_true] at h
    simp [Term.fill, fill_closed vals t d h.1, fillFields_closed vals arms (d + 1) h.2]
  | .ite c a b, d, h => by
    simp only [Term.closedAt, Bool.and_eq_true] at h
    simp [Term.fill, fill_closed vals c d h.1.1, fill_closed vals a d h.1.2, fill_closed vals b d h.2]
  | .hole n σ, d, h => by simp only [Term.closedAt] at h; simp [Term.fill, fillTerms_closed vals σ d h]

theorem fillFields_closed (vals : List Val) : ∀ (fs : List (Label × Term)) (d : Nat),
    Term.closedFields d fs = true → Term.fillFields vals d fs = fs
  | [], _, _ => rfl
  | (ℓ, t) :: fs, d, h => by
    simp only [Term.closedFields, Bool.and_eq_true] at h
    simp [Term.fillFields, fill_closed vals t d h.1, fillFields_closed vals fs d h.2]

theorem fillTerms_closed (vals : List Val) : ∀ (ts : List Term) (d : Nat),
    Term.closedTerms d ts = true → Term.fillTerms vals d ts = ts
  | [], _, _ => rfl
  | t :: ts, d, h => by
    simp only [Term.closedTerms, Bool.and_eq_true] at h
    simp [Term.fillTerms, fill_closed vals t d h.1, fillTerms_closed vals ts d h.2]
end

/-! ## Appending: what a quoted fragment means -/

variable {lib : List Term} {env : Env}

/-- `q` appends exactly `bs`: for every buffer term meaning `b` with `b ++ bs` within `bytesMax`,
`q buf` means `b ++ bs`. -/
def Appends (lib : List Term) (env : Env) (q : Term → Term) (bs : ByteArray) : Prop :=
  ∀ buf b, BigStep lib env buf (.ok (.bytes b)) → (b ++ bs).size ≤ Bounds.bytesMax →
    BigStep lib env (q buf) (.ok (.bytes (b ++ bs)))

theorem appends_lit (x : ByteArray) : Appends lib env (fun buf => lit buf x) x := by
  intro buf b hb hs
  have hle : b.size + x.size ≤ Bounds.bytesMax := by simpa [ByteArray.size_append] using hs
  have h := BigStep.prim (p := .cat) hb (BigStep.bytes (s := x)) (by simp [primEval, hle])
  simpa [primEval, hle] using h

theorem Appends.comp {q₁ q₂ : Term → Term} {x y : ByteArray} (h₁ : Appends lib env q₁ x)
    (h₂ : Appends lib env q₂ y) : Appends lib env (fun buf => q₂ (q₁ buf)) (x ++ y) := by
  intro buf b hb hs
  have hs₁ : (b ++ x).size ≤ Bounds.bytesMax := by simp only [ByteArray.size_append] at hs ⊢; omega
  have := h₂ (q₁ buf) (b ++ x) (h₁ buf b hb hs₁) (by rwa [ByteArray.append_assoc])
  rwa [ByteArray.append_assoc] at this

theorem Appends.id : Appends lib env (fun buf => buf) ByteArray.empty := by
  intro buf b hb _; simpa [ByteArray.append_empty] using hb

theorem Appends.congr {q q' : Term → Term} {x y : ByteArray} (h : Appends lib env q x)
    (hq : ∀ buf, q' buf = q buf) (hxy : y = x) : Appends lib env q' y := by
  subst hxy; intro buf b hb hs; rw [hq]; exact h buf b hb hs

/-- The three payload writers append the codec's bytes of their right operand. -/
theorem appends_u64be {x : Term} {n : Nat} (hx : BigStep lib env x (.ok (.nat n))) :
    Appends lib env (fun buf => .prim .u64be buf x) (Stream.u64be.bytes (UInt64.ofNat n)) := by
  intro buf b hb hs
  have hput := Stream.u64be_lawful.put_eq (UInt64.ofNat n) b
  have hev : primEval .u64be (.bytes b) (.nat n) = .ok (.bytes (b ++ Stream.u64be.bytes (UInt64.ofNat n))) := by
    simp only [primEval, appended, hput, hs, if_true]
  have h := BigStep.prim (p := .u64be) hb hx (by rw [hev]; simp)
  rwa [hev] at h

theorem appends_sized {x : Term} {s : ByteArray} (hx : BigStep lib env x (.ok (.bytes s))) :
    Appends lib env (fun buf => .prim .sized buf x) (Stream.varint.bytes s.size ++ s) := by
  intro buf b hb hs
  have hput : Stream.putVarint s.size b ++ s = b ++ (Stream.varint.bytes s.size ++ s) := by
    rw [Stream.putVarint_eq, ByteArray.append_assoc]; rfl
  have hev : primEval .sized (.bytes b) (.bytes s) = .ok (.bytes (b ++ (Stream.varint.bytes s.size ++ s))) := by
    simp only [primEval, appended, hput, hs, if_true]
  have h := BigStep.prim (p := .sized) hb hx (by rw [hev]; simp)
  rwa [hev] at h

theorem appends_dsized {x : Term} {s : ByteArray} (hx : BigStep lib env x (.ok (.digest s))) :
    Appends lib env (fun buf => .prim .dsized buf x) (Stream.varint.bytes s.size ++ s) := by
  intro buf b hb hs
  have hput : Stream.putVarint s.size b ++ s = b ++ (Stream.varint.bytes s.size ++ s) := by
    rw [Stream.putVarint_eq, ByteArray.append_assoc]; rfl
  have hev : primEval .dsized (.bytes b) (.digest s) = .ok (.bytes (b ++ (Stream.varint.bytes s.size ++ s))) := by
    simp only [primEval, appended, hput, hs, if_true]
  have h := BigStep.prim (p := .dsized) hb hx (by rw [hev]; simp)
  rwa [hev] at h

/-! ## Parameters -/

/-- A scalar of the declared type. -/
def Scalar : Ty → Val → Prop
  | .nat, .nat _ | .bool, .bool _ | .bytes, .bytes _ | .digest, .digest _ => True
  | _, _ => False

def ParamAt (lib : List Term) (env : Env) : Option Param → Option Val → Prop
  | none, none => True
  | some q, some v => BigStep lib env q.fetch (.ok v) ∧ Scalar q.ty v
  | _, _ => False

/-- Each parameter term means the matching value, a scalar of the declared type; the lists agree
in length. -/
def Params (lib : List Term) (env : Env) (ps : List Param) (vals : List Val) : Prop :=
  ∀ j : Nat, ParamAt lib env ps[j]? vals[j]?

theorem Params.at {ps : List Param} {vals : List Val} (h : Params lib env ps vals) (j : Nat) :
    ParamAt lib env ps[j]? vals[j]? := h j

/-- A parameter's literal node, written at run time, is the node of its value's literal. -/
theorem appends_param {i : Nat} {q : Param} {v : Val} {m : Nat} (hq : BigStep lib env q.fetch (.ok v))
    (hs : Scalar q.ty v) (hfit : (termTree ((v.lit?).getD (.var i))).fits nodeMax (m + 1) = true) :
    Appends lib env (fun buf => param buf i (some q))
      (Tree.putD (m + 1) (termTree ((v.lit?).getD (.var i))) ByteArray.empty) := by
  obtain ⟨T, x⟩ := q
  cases T <;> cases v <;> simp only [Scalar] at hs
  · -- nat
    rename_i n
    simp only [Val.lit?, Option.getD, termTree, param]
    rw [putD_frame, Tree.kidsBytes_nil, ByteArray.append_empty]
    have := ((appends_lit (head 4 8)).comp (appends_u64be hq)).comp (appends_lit (tail 0))
    refine this.congr (fun _ => rfl) ?_
    simp only [frame, head, tail, u64Bytes, Stream.u64be_size, List.length_nil, ByteArray.append_assoc]
  · -- bool
    rename_i v
    simp only [Val.lit?, Option.getD, termTree, param]
    rw [putD_frame, Tree.kidsBytes_nil, ByteArray.append_empty]
    intro buf b hb hsz
    cases v
    · exact BigStep.iteF hq (appends_lit _ buf b hb hsz)
    · exact BigStep.iteT hq (appends_lit _ buf b hb hsz)
  · -- bytes
    rename_i s
    simp only [Val.lit?, Option.getD, termTree, param]
    rw [putD_frame, Tree.kidsBytes_nil, ByteArray.append_empty]
    have := ((appends_lit (Stream.u8.bytes 6)).comp (appends_sized hq)).comp (appends_lit (tail 0))
    refine this.congr (fun _ => rfl) ?_
    simp only [frame, head, tail, List.length_nil, ByteArray.append_assoc]
  · -- digest
    rename_i s
    simp only [Val.lit?, Option.getD, termTree, param]
    rw [putD_frame, Tree.kidsBytes_nil, ByteArray.append_empty]
    have := ((appends_lit (Stream.u8.bytes 16)).comp (appends_dsized hq)).comp (appends_lit (tail 0))
    refine this.congr (fun _ => rfl) ?_
    simp only [frame, head, tail, List.length_nil, ByteArray.append_assoc]

/-! ## The quoter writes the encoder's bytes -/

/-- A closed subtree quoted as one literal fragment: the bytes `putD` writes at any depth it fits. -/
theorem appends_closed {n : Nat} {t : Tree} (h : t.fits nodeMax n = true) (hn : n ≤ depthMax) :
    Appends lib env (fun buf => lit buf (treeBytes t)) (Tree.putD n t ByteArray.empty) := by
  rw [← treeBytes_eq h hn]; exact appends_lit _

mutual
theorem quoteTerm_sound {ps : List Param} {vals : List Val} (hps : Params lib env ps vals) :
    ∀ (t : Term) (d n : Nat), n ≤ depthMax → (termTree (t.fill vals d)).fits nodeMax n = true →
      Appends lib env (fun buf => quoteTerm ps d buf t) (Tree.putD n (termTree (t.fill vals d)) ByteArray.empty)
  | .var i, d, n, hn, hfit => by
    by_cases hi : i < d
    · simp only [Term.fill, hi, if_true] at hfit ⊢
      simp only [quoteTerm, hi, if_true]
      exact appends_closed hfit hn
    · simp only [Term.fill, hi, if_false] at hfit ⊢
      simp only [quoteTerm, hi, if_false]
      have hp := hps.at (i - d)
      revert hp hfit
      cases hv : vals[i - d]? <;> cases hq : ps[i - d]? <;> intro hfit hp <;> simp only [ParamAt] at hp <;>
        dsimp only at hfit ⊢
      · exact appends_closed hfit hn
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
          cases n with
          | zero => rw [fits_zero] at hfit; cases hfit
          | succ m => exact ⟨m, rfl⟩
        exact appends_param hp.1 hp.2 hfit
  | .lam A b, d, n, hn, hfit => by
    by_cases hc : Term.closedAt (d + 1) b
    · have := fill_closed vals (.lam A b) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      rw [← treeBytes_eq (hk _ (by simp)) (by omega)]
      have hb := quoteTerm_sound hps b (d + 1) m (by omega) (hk _ (by simp))
      refine ((appends_lit _).comp hb).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc, ByteArray.append_empty]
  | .app f a, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d (.app f a)
    · have := fill_closed vals (.app f a) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      have hf := quoteTerm_sound hps f d m (by omega) (hk _ (by simp))
      have ha := quoteTerm_sound hps a d m (by omega) (hk _ (by simp))
      refine (((appends_lit _).comp hf).comp ha).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc, ByteArray.append_empty]
  | .fix t, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d t
    · have := fill_closed vals (.fix t) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      have ht := quoteTerm_sound hps t d m (by omega) (hk _ (by simp))
      refine ((appends_lit _).comp ht).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_empty]
  | .nat k, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .bool v, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .bytes s, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .digest s, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .ref i, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .refuse T w, d, n, hn, hfit => by simp only [Term.fill] at hfit ⊢; exact appends_closed hfit hn
  | .prim p a b, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d (.prim p a b)
    · have := fill_closed vals (.prim p a b) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      have ha := quoteTerm_sound hps a d m (by omega) (hk _ (by simp))
      have hb := quoteTerm_sound hps b d m (by omega) (hk _ (by simp))
      refine (((appends_lit _).comp ha).comp hb).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc, ByteArray.append_empty]
  | .record fs, d, n, hn, hfit => by
    by_cases hc : Term.closedFields d fs
    · have := fill_closed vals (.record fs) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, fieldsTree_length, fillFields_length]
      exact (appends_lit _).comp (quoteFields_sound hps fs d m (by omega) hk)
  | .get t ℓ, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d t
    · have := fill_closed vals (.get t ℓ) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      have ht := quoteTerm_sound hps t d m (by omega) (hk _ (by simp))
      refine ((appends_lit _).comp ht).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_empty]
  | .extend t fs, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d (.extend t fs)
    · have := fill_closed vals (.extend t fs) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, List.length_cons, fieldsTree_length, fillFields_length]
      have ht := quoteTerm_sound hps t d m (by omega) (hk _ (by simp))
      have hfs := quoteFields_sound hps fs d m (by omega) (fun c hc => hk c (by simp [hc]))
      refine (((appends_lit _).comp ht).comp hfs).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc]
  | .inj A ℓ t, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d t
    · have := fill_closed vals (.inj A ℓ t) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      rw [← treeBytes_eq (hk _ (by simp)) (by omega)]
      have ht := quoteTerm_sound hps t d m (by omega) (hk _ (by simp))
      refine ((appends_lit _).comp ht).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc, ByteArray.append_empty]
  | .case t arms, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d (.case t arms)
    · have := fill_closed vals (.case t arms) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, List.length_cons, fieldsTree_length, fillFields_length]
      have ht := quoteTerm_sound hps t d m (by omega) (hk _ (by simp))
      have hfs := quoteFields_sound hps arms (d + 1) m (by omega) (fun c hc => hk c (by simp [hc]))
      refine (((appends_lit _).comp ht).comp hfs).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc]
  | .ite c a b, d, n, hn, hfit => by
    by_cases hc : Term.closedAt d (.ite c a b)
    · have := fill_closed vals (.ite c a b) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      simp only [List.length_cons, List.length_nil]
      have hc' := quoteTerm_sound hps c d m (by omega) (hk _ (by simp))
      have ha := quoteTerm_sound hps a d m (by omega) (hk _ (by simp))
      have hb := quoteTerm_sound hps b d m (by omega) (hk _ (by simp))
      refine ((((appends_lit _).comp hc').comp ha).comp hb).congr (fun _ => rfl) ?_
      simp only [ByteArray.append_assoc, ByteArray.append_empty]
  | .hole k σ, d, n, hn, hfit => by
    by_cases hc : Term.closedTerms d σ
    · have := fill_closed vals (.hole k σ) d hc
      rw [this] at hfit ⊢
      simp only [quoteTerm, hc, if_true]
      exact appends_closed hfit hn
    · simp only [quoteTerm, hc]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => rw [fits_zero] at hfit; cases hfit
        | succ m => exact ⟨m, rfl⟩
      simp only [Term.fill, termTree] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame, termsTree_length, fillTerms_length]
      exact (appends_lit _).comp (quoteTerms_sound hps σ d m (by omega) hk)

theorem quoteFields_sound {ps : List Param} {vals : List Val} (hps : Params lib env ps vals) :
    ∀ (fs : List (Label × Term)) (d n : Nat), n ≤ depthMax →
      (∀ c ∈ fieldsTree (Term.fillFields vals d fs), c.fits nodeMax n = true) →
      Appends lib env (fun buf => quoteFields ps d buf fs)
        (Tree.kidsBytes n (fieldsTree (Term.fillFields vals d fs)))
  | [], _, _, _, _ => by simp only [Term.fillFields, fieldsTree, Tree.kidsBytes_nil, quoteFields]; exact Appends.id
  | (ℓ, t) :: fs, d, n, hn, hk => by
    simp only [Term.fillFields, fieldsTree, quoteFields] at hk ⊢
    rw [Tree.kidsBytes_cons]
    have hnode := hk (Tree.node 15 ℓ.toUTF8 [termTree (t.fill vals d)]) (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      cases n with
      | zero => rw [fits_zero] at hnode; cases hnode
      | succ m => exact ⟨m, rfl⟩
    obtain ⟨-, -, hk1⟩ := fits_succ.mp hnode
    rw [putD_frame, Tree.kidsBytes_cons, Tree.kidsBytes_nil]
    simp only [List.length_cons, List.length_nil]
    have ht := quoteTerm_sound hps t d m (by omega) (hk1 _ (by simp))
    have hrest := quoteFields_sound hps fs d (m + 1) hn (fun c hc => hk c (by simp [hc]))
    refine (((appends_lit _).comp ht).comp hrest).congr (fun _ => rfl) ?_
    simp only [ByteArray.append_assoc, ByteArray.append_empty]

theorem quoteTerms_sound {ps : List Param} {vals : List Val} (hps : Params lib env ps vals) :
    ∀ (ts : List Term) (d n : Nat), n ≤ depthMax →
      (∀ c ∈ termsTree (Term.fillTerms vals d ts), c.fits nodeMax n = true) →
      Appends lib env (fun buf => quoteTerms ps d buf ts)
        (Tree.kidsBytes n (termsTree (Term.fillTerms vals d ts)))
  | [], _, _, _, _ => by simp only [Term.fillTerms, termsTree, Tree.kidsBytes_nil, quoteTerms]; exact Appends.id
  | t :: ts, d, n, hn, hk => by
    simp only [Term.fillTerms, termsTree, quoteTerms] at hk ⊢
    rw [Tree.kidsBytes_cons]
    have ht := quoteTerm_sound hps t d n hn (hk _ (by simp))
    have hrest := quoteTerms_sound hps ts d n hn (fun c hc => hk c (by simp [hc]))
    exact ht.comp hrest
end

/-! ## The package -/

theorem depthMax_succ : depthMax = 1023 + 1 := rfl

/-- **The quoter writes the encoder's bytes.** When the filled package has bytes `B`, the quoted
package appends exactly `B`. -/
theorem quotePackage_sound {ps : List Param} {vals : List Val} (hps : Params lib env ps vals)
    {p : Package} {B : ByteArray} (hB : encodePackage (fillPackage vals p) = some B) :
    Appends lib env (fun buf => quotePackage ps buf p) B := by
  unfold encodePackage at hB
  split at hB
  · split at hB
    · rename_i hfit
      cases hB
      have hpf : packageFit (fillPackage vals p) = ⟨packageTree (fillPackage vals p), hfit⟩ := by
        simp [packageFit, hfit]
      have hbytes : packageCodec.bytes (fillPackage vals p) =
          ByteArray.mk #[Bounds.packageWireVersion] ++
            Tree.putD depthMax (packageTree (fillPackage vals p)) ByteArray.empty := by
        show packageStream.bytes ((), packageFit (fillPackage vals p)) = _
        rw [hpf, packageStream_bytes]; rfl
      rw [hbytes]
      simp only [packageTree, fillPackage] at hfit ⊢
      rw [depthMax_succ] at hfit ⊢
      obtain ⟨-, -, hk⟩ := fits_succ.mp hfit
      rw [putD_frame]
      simp only [Tree.kidsBytes_cons, Tree.kidsBytes_nil]
      have hbody := quoteTerm_sound hps p.body 0 1023 (by decide) (hk _ (by simp))
      have lit1 := treeBytes_eq (hk (.node 0 .empty (p.imports.map fun d => .node 0 d [])) (by simp)) (by decide)
      have lit2 := treeBytes_eq (hk (tyTree p.state) (by simp)) (by decide)
      have lit3 := treeBytes_eq (hk (tyTree p.iface) (by simp)) (by decide)
      have lit4 := treeBytes_eq (hk (.node 1 .empty (p.methods.map labelLeaf)) (by simp)) (by decide)
      have lit5 := treeBytes_eq (hk (.node 1 .empty (p.laws.map labelLeaf)) (by simp)) (by decide)
      have lit6 := treeBytes_eq (hk (.node 2 .empty (p.rels.map relTree)) (by simp)) (by decide)
      have lit7 := treeBytes_eq (hk (.node 0 p.doc []) (by simp)) (by decide)
      have lit8 := treeBytes_eq (hk (.node 3 .empty (p.holes.map holeROMTree)) (by simp)) (by decide)
      have lit9 := treeBytes_eq (hk (.node 4 .empty (p.effects.map effectTree)) (by simp)) (by decide)
      rw [← lit1, ← lit2, ← lit3, ← lit4, ← lit5, ← lit6, ← lit7, ← lit8, ← lit9]
      refine (((appends_lit (sectionsBefore p)).comp hbody).comp (appends_lit (sectionsAfter p))).congr
        (fun _ => rfl) ?_
      simp only [sectionsBefore, sectionsAfter, List.length_cons, List.length_nil, ByteArray.append_assoc,
        ByteArray.append_empty]
    · cases hB
  · cases hB

/-! ## The quoter names no closure package: the receiver runs it unrelocated -/

theorem noRef_lit {buf : Term} (h : NoRef buf) (x : ByteArray) : NoRef (lit buf x) := by
  simp only [lit, NoRef]; exact ⟨h, trivial⟩

theorem noRef_param {buf : Term} (hb : NoRef buf) {i : Nat} {q : Option Param}
    (hq : ∀ p, q = some p → NoRef p.fetch) : NoRef (param buf i q) := by
  match q with
  | none => exact noRef_lit hb _
  | some ⟨T, x⟩ =>
    have hx : NoRef x := hq ⟨T, x⟩ rfl
    cases T <;> simp only [param, lit, NoRef] <;>
      first
        | exact ⟨hb, trivial⟩
        | exact ⟨⟨⟨hb, trivial⟩, hx⟩, trivial⟩
        | exact ⟨hx, ⟨hb, trivial⟩, ⟨hb, trivial⟩⟩

mutual
theorem noRef_quoteTerm {ps : List Param} (hps : ∀ q ∈ ps, NoRef q.fetch) :
    ∀ (t : Term) (d : Nat) (buf : Term), NoRef buf → NoRef (quoteTerm ps d buf t)
  | .var i, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_param hb fun p hp => hps p (List.mem_of_getElem? hp)
  | .lam A b, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps b (d + 1) _ (noRef_lit hb _)
  | .app f a, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps a d _ (noRef_quoteTerm hps f d _ (noRef_lit hb _))
  | .fix t, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps t d _ (noRef_lit hb _)
  | .nat _, _, buf, hb | .bool _, _, buf, hb | .bytes _, _, buf, hb | .digest _, _, buf, hb
  | .ref _, _, buf, hb | .refuse _ _, _, buf, hb => noRef_lit hb _
  | .prim p a b, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps b d _ (noRef_quoteTerm hps a d _ (noRef_lit hb _))
  | .record fs, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteFields hps fs d _ (noRef_lit hb _)
  | .get t ℓ, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps t d _ (noRef_lit hb _)
  | .extend t fs, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteFields hps fs d _ (noRef_quoteTerm hps t d _ (noRef_lit hb _))
  | .inj A ℓ t, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps t d _ (noRef_lit hb _)
  | .case t arms, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteFields hps arms (d + 1) _ (noRef_quoteTerm hps t d _ (noRef_lit hb _))
  | .ite c a b, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerm hps b d _ (noRef_quoteTerm hps a d _ (noRef_quoteTerm hps c d _ (noRef_lit hb _)))
  | .hole n σ, d, buf, hb => by
    simp only [quoteTerm]; split
    · exact noRef_lit hb _
    · exact noRef_quoteTerms hps σ d _ (noRef_lit hb _)

theorem noRef_quoteFields {ps : List Param} (hps : ∀ q ∈ ps, NoRef q.fetch) :
    ∀ (fs : List (Label × Term)) (d : Nat) (buf : Term), NoRef buf → NoRef (quoteFields ps d buf fs)
  | [], _, _, hb => hb
  | (_, t) :: fs, d, _, hb =>
    noRef_quoteFields hps fs d _ (noRef_quoteTerm hps t d _ (noRef_lit hb _))

theorem noRef_quoteTerms {ps : List Param} (hps : ∀ q ∈ ps, NoRef q.fetch) :
    ∀ (ts : List Term) (d : Nat) (buf : Term), NoRef buf → NoRef (quoteTerms ps d buf ts)
  | [], _, _, hb => hb
  | t :: ts, d, _, hb => noRef_quoteTerms hps ts d _ (noRef_quoteTerm hps t d _ hb)
end

theorem noRef_quotePackage {ps : List Param} (hps : ∀ q ∈ ps, NoRef q.fetch) {buf : Term} (hb : NoRef buf)
    (p : Package) : NoRef (quotePackage ps buf p) :=
  noRef_lit (noRef_quoteTerm hps p.body 0 _ (noRef_lit hb _)) _

end Nanodregg.Lang.Quote
