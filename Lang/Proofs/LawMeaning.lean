/-
# Lang.Proofs.LawMeaning — the relational meaning of contextual law bodies

The `Law*` semantics of contextual law bodies (`law_bigStep_back`, `lawTerm_fill`), consumed by `Lang.Proofs.LawReceiver`.
-/
import Lang.Proofs.Extract
import Lang.Proofs.LiveClosed

namespace Nanodregg.Lang

/-! ## From `Lang.Proofs.Contextual.LawMeaning` -/
section

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/- Unresolved law preparation preserves reference-free meaning, including dormant holes. -/
mutual
inductive LawTerm : Term → Term → Prop
  | var {i} : LawTerm (.var i) (.var i)
  | lam {A b b'} : LawTerm b b' → LawTerm (.lam A b) (.lam A b')
  | app {f f' a a'} : LawTerm f f' → LawTerm a a' → LawTerm (.app f a) (.app f' a')
  | fix {t t'} : LawTerm t t' → LawTerm (.fix t) (.fix t')
  | nat {n} : LawTerm (.nat n) (.nat n)
  | bool {b} : LawTerm (.bool b) (.bool b)
  | bytes {b} : LawTerm (.bytes b) (.bytes b)
  | digest {b} : LawTerm (.digest b) (.digest b)
  | prim {p a a' b b'} : LawTerm a a' → LawTerm b b' → LawTerm (.prim p a b) (.prim p a' b')
  | record {fs fs'} : LawTerms fs fs' → LawTerm (.record fs) (.record fs')
  | get {t t' l} : LawTerm t t' → LawTerm (.get t l) (.get t' l)
  | extend {t t' fs fs'} : LawTerm t t' → LawTerms fs fs' → LawTerm (.extend t fs) (.extend t' fs')
  | inj {A l t t'} : LawTerm t t' → LawTerm (.inj A l t) (.inj A l t')
  | case {t t' fs fs'} : LawTerm t t' → LawTerms fs fs' → LawTerm (.case t fs) (.case t' fs')
  | ite {c c' a a' b b'} : LawTerm c c' → LawTerm a a' → LawTerm b b' → LawTerm (.ite c a b) (.ite c' a' b')
  | refuse {A w} : LawTerm (.refuse A w) (.refuse A w)
  | hole {n ts ts'} : LawTerm (.hole n ts) (.hole n ts')
  | blocked {n ts A} : LawTerm (.hole n ts) (.refuse A "holeUnresolved".toUTF8)
inductive LawTerms : List (Label × Term) → List (Label × Term) → Prop
  | nil : LawTerms [] []
  | cons {l t t' ts ts'} : LawTerm t t' → LawTerms ts ts' → LawTerms ((l,t)::ts) ((l,t')::ts')
end

mutual
inductive LawVal : Val → Val → Prop
  | nat {n} : LawVal (.nat n) (.nat n)
  | bool {b} : LawVal (.bool b) (.bool b)
  | bytes {b} : LawVal (.bytes b) (.bytes b)
  | digest {b} : LawVal (.digest b) (.digest b)
  | clo {b b' e e'} : LawTerm b b' → LawEnv e e' → LawVal (.clo b e) (.clo b' e')
  | knot {b b' e e'} : LawTerm b b' → LawEnv e e' → LawVal (.knot b e) (.knot b' e')
  | record {fs fs'} : LawFields fs fs' → LawVal (.record fs) (.record fs')
  | inj {l v v'} : LawVal v v' → LawVal (.inj l v) (.inj l v')
inductive LawEnv : Env → Env → Prop
  | nil : LawEnv [] []
  | cons {v v' e e'} : LawVal v v' → LawEnv e e' → LawEnv (v::e) (v'::e')
inductive LawFields : List (Label × (Term × Env)) → List (Label × (Term × Env)) → Prop
  | nil : LawFields [] []
  | cons {l t t' e e' fs fs'} : LawTerm t t' → LawEnv e e' → LawFields fs fs' →
      LawFields ((l,t,e)::fs) ((l,t',e')::fs')
end
inductive LawResult : Except Fault Val → Except Fault Val → Prop
  | ok {v v'} : LawVal v v' → LawResult (.ok v) (.ok v')
  | error {e} : LawResult (.error e) (.error e)

theorem LawEnv.get {e e' : Env} (h : LawEnv e e') {i : Nat} {v' : Val}
    (hv : e'[i]? = some v') : ∃ v, e[i]? = some v ∧ LawVal v v' := by
  cases h with
  | nil => simp at hv
  | cons hx he =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst v'; exact ⟨_, rfl, hx⟩
    | succ i => exact he.get hv

theorem LawTerms.find {fs fs'} (h : LawTerms fs fs') {l t'}
    (hf : Row.find? l fs' = some t') : ∃ t, Row.find? l fs = some t ∧ LawTerm t t' := by
  cases h with
  | nil => cases hf
  | @cons k t u ts us ht hs =>
    simp only [Row.find?] at hf ⊢
    split at hf
    · rename_i hk; rw [if_pos hk]; cases hf; exact ⟨_, rfl, ht⟩
    · rename_i hk; rw [if_neg hk]; exact hs.find hf

theorem LawFields.find {fs fs'} (h : LawFields fs fs') {l t' e'}
    (hf : Row.find? l fs' = some (t',e')) :
    ∃ t e, Row.find? l fs = some (t,e) ∧ LawTerm t t' ∧ LawEnv e e' := by
  cases h with
  | nil => cases hf
  | @cons k t u e f ts us ht he hs =>
    simp only [Row.find?] at hf ⊢
    split at hf
    · rename_i hk; rw [if_pos hk]; cases hf; exact ⟨_, _, rfl, ht, he⟩
    · rename_i hk; rw [if_neg hk]; exact hs.find hf

theorem LawTerms.suspend {fs fs' e e'} (h : LawTerms fs fs') (he : LawEnv e e') :
    LawFields (suspend e fs) (suspend e' fs') := by
  cases h with
  | nil => exact .nil
  | cons ht hs => exact .cons ht he (hs.suspend he)

theorem LawFields.put {fs fs' t t' e e'} (hf : LawFields fs fs') (ht : LawTerm t t')
    (he : LawEnv e e') (l : Label) :
    LawFields (Row.put l (t,e) fs) (Row.put l (t',e') fs') := by
  cases hf with
  | nil => exact .cons ht he .nil
  | cons hu henv hf =>
    simp only [Row.put]
    split
    · exact .cons ht he (.cons hu henv hf)
    · split
      · exact .cons ht he hf
      · exact .cons hu henv (hf.put ht he l)

theorem LawFields.merge : ∀ {gs gs'}, LawFields gs gs' → ∀ {fs fs'}, LawFields fs fs' →
    LawFields (Row.merge fs gs) (Row.merge fs' gs') := by
  intro gs gs' hg fs fs' hf
  cases hg with
  | nil => exact hf
  | cons ht he hg => exact LawFields.merge hg (hf.put ht he _)

theorem LawVal.prim {p x x' y y'} (hx : LawVal x x') (hy : LawVal y y') :
    LawResult (primEval p x y) (primEval p x' y') := by
  cases hx <;> cases hy <;> cases p <;> simp only [primEval, natResult]
  all_goals repeat' split
  all_goals first | exact .error | exact .ok .nat | exact .ok .bool | exact .ok .bytes | exact .ok .digest

theorem LawResult.not_stuck {a b} (h : LawResult a b) (hb : b ≠ .error .stuck) : a ≠ .error .stuck := by
  intro ha
  rw [ha] at h
  cases h
  exact hb rfl

mutual
theorem law_bigStep_back {lib lib' : List Term} :
    ∀ {e' t' r'}, BigStep lib' e' t' r' → ∀ {e t}, LawEnv e e' → LawTerm t t' →
      ∃ r, BigStep lib e t r ∧ LawResult r r'
  | _, _, _, .var hv, _, _, he, ht => by
    cases ht
    obtain ⟨v, hv, hr⟩ := he.get hv
    exact ⟨_, .var hv, .ok hr⟩
  | _, _, _, .lam, _, _, he, ht => by cases ht with | lam hb => exact ⟨_, .lam, .ok (.clo hb he)⟩
  | _, _, _, .app hf ha hb, _, _, he, ht => by
    cases ht with
    | app htf hta =>
      obtain ⟨_, hf, hr⟩ := law_bigStep_back hf he htf
      cases hr with | ok hv => cases hv with | clo htb henv =>
        obtain ⟨_, ha, hr⟩ := law_bigStep_back ha he hta
        cases hr with | ok hw =>
          obtain ⟨r, hb, hr⟩ := law_bigStep_back hb (.cons hw henv) htb
          exact ⟨r, .app hf ha hb, hr⟩
  | _, _, _, .appF hf, _, _, he, ht => by
    cases ht with | app htf _ =>
      obtain ⟨_, hf, hr⟩ := law_bigStep_back hf he htf
      cases hr; exact ⟨_, .appF hf, .error⟩
  | _, _, _, .appA hf ha, _, _, he, ht => by
    cases ht with | app htf hta =>
      obtain ⟨_, hf, hr⟩ := law_bigStep_back hf he htf
      cases hr with | ok _ =>
        obtain ⟨_, ha, hr⟩ := law_bigStep_back ha he hta
        cases hr; exact ⟨_, .appA hf ha, .error⟩
  | _, _, _, .fix hf, _, _, he, ht => by
    cases ht with | fix ht =>
      obtain ⟨_, hf, hr⟩ := law_bigStep_back hf he ht
      cases hr with | ok hv => cases hv with | clo hb henv =>
        exact ⟨_, .fix hf, .ok (.knot hb henv)⟩
  | _, _, _, .fixE hf, _, _, he, ht => by
    cases ht with | fix ht =>
      obtain ⟨_, hf, hr⟩ := law_bigStep_back hf he ht
      cases hr; exact ⟨_, .fixE hf, .error⟩
  | _, _, _, .nat, _, _, _, ht => by cases ht; exact ⟨_, .nat, .ok .nat⟩
  | _, _, _, .bool, _, _, _, ht => by cases ht; exact ⟨_, .bool, .ok .bool⟩
  | _, _, _, .bytes, _, _, _, ht => by cases ht; exact ⟨_, .bytes, .ok .bytes⟩
  | _, _, _, .digest, _, _, _, ht => by cases ht; exact ⟨_, .digest, .ok .digest⟩
  | _, _, _, .refuse, _, _, _, ht => by
    cases ht
    · exact ⟨_, .refuse, .error⟩
    · exact ⟨_, .hole, .error⟩
  | _, _, _, .hole, _, _, _, ht => by cases ht; exact ⟨_, .hole, .error⟩
  | _, _, _, .prim ha hb hn, _, _, he, ht => by
    cases ht with | @prim p a a1 b b1 hta htb =>
      obtain ⟨_, ha, hr⟩ := law_bigStep_back ha he hta
      cases hr with | ok hx =>
        obtain ⟨_, hb, hr⟩ := law_bigStep_back hb he htb
        cases hr with | ok hy =>
          exact ⟨_, .prim ha hb ((LawVal.prim hx hy).not_stuck hn), LawVal.prim hx hy⟩
  | _, _, _, .primL ha, _, _, he, ht => by
    cases ht with | prim hta _ =>
      obtain ⟨_, ha, hr⟩ := law_bigStep_back ha he hta
      cases hr; exact ⟨_, .primL ha, .error⟩
  | _, _, _, .primR ha hb, _, _, he, ht => by
    cases ht with | @prim p a a1 b b1 hta htb =>
      obtain ⟨_, ha, hr⟩ := law_bigStep_back ha he hta
      cases hr with | ok _ =>
        obtain ⟨_, hb, hr⟩ := law_bigStep_back hb he htb
        cases hr; exact ⟨_, .primR ha hb, .error⟩
  | _, _, _, .record, _, _, he, ht => by
    cases ht with | record hf => exact ⟨_, .record, .ok (.record (hf.suspend he))⟩
  | _, _, _, .get hs hf, _, _, he, ht => by
    cases ht with | get ht =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr with | ok hv =>
        obtain ⟨r, hf, hr⟩ := law_sel_back hf hv
        exact ⟨r, .get hs hf, hr⟩
  | _, _, _, .getE hs, _, _, he, ht => by
    cases ht with | get ht =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr; exact ⟨_, .getE hs, .error⟩
  | _, _, _, .extend hs hf, _, _, he, ht => by
    cases ht with | extend ht hfs =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr with | ok hv =>
        obtain ⟨r, hf, hr⟩ := law_ext_back hf hv hfs he
        exact ⟨r, .extend hs hf, hr⟩
  | _, _, _, .extendE hs, _, _, he, ht => by
    cases ht with | extend ht _ =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr; exact ⟨_, .extendE hs, .error⟩
  | _, _, _, .inj hs, _, _, he, ht => by
    cases ht with | inj ht =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr with | ok hv => exact ⟨_, .inj hs, .ok (.inj hv)⟩
  | _, _, _, .injE hs, _, _, he, ht => by
    cases ht with | inj ht =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr; exact ⟨_, .injE hs, .error⟩
  | _, _, _, .case hs hf hb, _, _, he, ht => by
    cases ht with | case ht hfs =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr with | ok hv => cases hv with | inj hv =>
        obtain ⟨b, hfind, hbody⟩ := hfs.find hf
        obtain ⟨r, hb, hr⟩ := law_bigStep_back hb (.cons hv he) hbody
        exact ⟨r, .case hs hfind hb, hr⟩
  | _, _, _, .caseE hs, _, _, he, ht => by
    cases ht with | case ht _ =>
      obtain ⟨_, hs, hr⟩ := law_bigStep_back hs he ht
      cases hr; exact ⟨_, .caseE hs, .error⟩
  | _, _, _, .iteT hc hb, _, _, he, ht => by
    cases ht with | ite htc htb _ =>
      obtain ⟨_, hc, hr⟩ := law_bigStep_back hc he htc
      cases hr with | ok hv =>
       cases hv
       obtain ⟨r, hb, hr⟩ := law_bigStep_back hb he htb
       exact ⟨r, .iteT hc hb, hr⟩
  | _, _, _, .iteF hc hb, _, _, he, ht => by
    cases ht with | ite htc _ htb =>
      obtain ⟨_, hc, hr⟩ := law_bigStep_back hc he htc
      cases hr with | ok hv =>
       cases hv
       obtain ⟨r, hb, hr⟩ := law_bigStep_back hb he htb
       exact ⟨r, .iteF hc hb, hr⟩
  | _, _, _, .iteE hc, _, _, he, ht => by
    cases ht with | ite htc _ _ =>
      obtain ⟨_, hc, hr⟩ := law_bigStep_back hc he htc
      cases hr; exact ⟨_, .iteE hc, .error⟩
  | _, _, _, .ref _ _, _, _, _, ht => by cases ht

theorem law_sel_back {lib lib' : List Term} :
    ∀ {v' l r'}, Sel lib' v' l r' → ∀ {v}, LawVal v v' →
      ∃ r, Sel lib v l r ∧ LawResult r r'
  | _, _, _, .field hf hb, _, hv => by
    cases hv with | record hfs =>
      obtain ⟨t, e, hf, ht, he⟩ := hfs.find hf
      obtain ⟨r, hb, hr⟩ := law_bigStep_back hb he ht
      exact ⟨r, .field hf hb, hr⟩
  | _, _, _, .knot hb hs, _, hv => by
    cases hv with | knot ht he =>
      obtain ⟨_, hb, hr⟩ := law_bigStep_back hb (.cons (.knot ht he) he) ht
      cases hr with | ok hv =>
        obtain ⟨r, hs, hr⟩ := law_sel_back hs hv
        exact ⟨r, .knot hb hs, hr⟩
  | _, _, _, .knotE hb, _, hv => by
    cases hv with | knot ht he =>
      obtain ⟨_, hb, hr⟩ := law_bigStep_back hb (.cons (.knot ht he) he) ht
      cases hr; exact ⟨_, .knotE hb, .error⟩

theorem law_ext_back {lib lib' : List Term} :
    ∀ {v' fs' e' r'}, Ext lib' v' fs' e' r' → ∀ {v fs e}, LawVal v v' → LawTerms fs fs' → LawEnv e e' →
      ∃ r, Ext lib v fs e r ∧ LawResult r r'
  | _, _, _, _, .record, _, _, _, hv, hf, he => by
    cases hv with | record hg => exact ⟨_, .record, .ok (.record ((hf.suspend he).merge hg))⟩
  | _, _, _, _, .knot hb hs, _, _, _, hv, hf, he => by
    cases hv with | knot ht henv =>
      obtain ⟨_, hb, hr⟩ := law_bigStep_back hb (.cons (.knot ht henv) henv) ht
      cases hr with | ok hv =>
        obtain ⟨r, hs, hr⟩ := law_ext_back hs hv hf he
        exact ⟨r, .knot hb hs, hr⟩
  | _, _, _, _, .knotE hb, _, _, _, hv, _, _ => by
    cases hv with | knot ht he =>
      obtain ⟨_, hb, hr⟩ := law_bigStep_back hb (.cons (.knot ht he) he) ht
      cases hr; exact ⟨_, .knotE hb, .error⟩
end


mutual
theorem LawTerm.same : ∀ {t}, NoRef t → LawTerm t t
  | .var _, _ => .var
  | .nat _, _ => .nat
  | .bool _, _ => .bool
  | .bytes _, _ => .bytes
  | .digest _, _ => .digest
  | .refuse _ _, _ => .refuse
  | .lam _ _, h => .lam (LawTerm.same h)
  | .fix _, h => .fix (LawTerm.same h)
  | .get _ _, h => .get (LawTerm.same h)
  | .inj _ _ _, h => .inj (LawTerm.same h)
  | .app _ _, h => .app (LawTerm.same h.1) (LawTerm.same h.2)
  | .prim _ _ _, h => .prim (LawTerm.same h.1) (LawTerm.same h.2)
  | .record _, h => .record (LawTerms.same h)
  | .extend _ _, h => .extend (LawTerm.same h.1) (LawTerms.same h.2)
  | .case _ _, h => .case (LawTerm.same h.1) (LawTerms.same h.2)
  | .ite _ _ _, h => .ite (LawTerm.same h.1) (LawTerm.same h.2.1) (LawTerm.same h.2.2)
  | .hole _ _, _ => .hole
  | .ref _, h => False.elim h
theorem LawTerms.same : ∀ {fs}, NoRefRow fs → LawTerms fs fs
  | [], _ => .nil
  | _ :: _, h => .cons (LawTerm.same h.1) (LawTerms.same h.2)
end

mutual
theorem LawVal.data : ∀ d : Data, LawVal d.toVal d.toVal
  | .nat _ => .nat
  | .bool _ => .bool
  | .bytes _ => .bytes
  | .digest _ => .digest
  | .inj _ d => .inj (LawVal.data d)
  | .record fs => .record (LawFields.data fs)
theorem LawFields.data : ∀ fs : List (Label × Data), LawFields (Data.rowToVal fs) (Data.rowToVal fs)
  | [] => .nil
  | (_,d) :: fs => .cons .var (.cons (LawVal.data d) .nil) (LawFields.data fs)
end

mutual
theorem lawTerm_fill (σ : Nat → Option Term)
    (hs : ∀ n v, σ n = some v → ∃ A, v = .refuse A "holeUnresolved".toUTF8) :
    ∀ {t}, NoRef t → LawTerm t (Term.fillRefs σ t)
  | .var _, _ => .var
  | .nat _, _ => .nat
  | .bool _, _ => .bool
  | .bytes _, _ => .bytes
  | .digest _, _ => .digest
  | .refuse _ _, _ => .refuse
  | .lam _ _, h => .lam (lawTerm_fill σ hs h)
  | .fix _, h => .fix (lawTerm_fill σ hs h)
  | .get _ _, h => .get (lawTerm_fill σ hs h)
  | .inj _ _ _, h => .inj (lawTerm_fill σ hs h)
  | .app _ _, h => .app (lawTerm_fill σ hs h.1) (lawTerm_fill σ hs h.2)
  | .prim _ _ _, h => .prim (lawTerm_fill σ hs h.1) (lawTerm_fill σ hs h.2)
  | .record _, h => .record (lawTerms_fill σ hs h)
  | .extend _ _, h => .extend (lawTerm_fill σ hs h.1) (lawTerms_fill σ hs h.2)
  | .case _ _, h => .case (lawTerm_fill σ hs h.1) (lawTerms_fill σ hs h.2)
  | .ite _ _ _, h => .ite (lawTerm_fill σ hs h.1) (lawTerm_fill σ hs h.2.1) (lawTerm_fill σ hs h.2.2)
  | .ref _, h => False.elim h
  | .hole n ts, _ => by
    cases hv : σ n with
    | none => simp only [Term.fillRefs, hv]; exact .hole
    | some v =>
      obtain ⟨A, rfl⟩ := hs n v hv
      simp only [Term.fillRefs, hv, Term.substList, Term.substVar]
      exact .blocked
theorem lawTerms_fill (σ : Nat → Option Term)
    (hs : ∀ n v, σ n = some v → ∃ A, v = .refuse A "holeUnresolved".toUTF8) :
    ∀ {fs}, NoRefRow fs → LawTerms fs (Term.fillRefsRow σ fs)
  | [], _ => .nil
  | _ :: _, h => .cons (lawTerm_fill σ hs h.1) (lawTerms_fill σ hs h.2)
end

mutual
theorem LawTerm.relocate_right {t u} (h : LawTerm t u) (f : Nat → Nat) : LawTerm t (u.relocate f) := by
  cases h with
  | var => exact .var
  | nat => exact .nat
  | bool => exact .bool
  | bytes => exact .bytes
  | digest => exact .digest
  | refuse => exact .refuse
  | blocked => exact .blocked
  | hole => exact .hole
  | lam h => exact .lam (h.relocate_right f)
  | fix h => exact .fix (h.relocate_right f)
  | get h => exact .get (h.relocate_right f)
  | inj h => exact .inj (h.relocate_right f)
  | record h => exact .record (h.relocate_right f)
  | app h k => exact .app (h.relocate_right f) (k.relocate_right f)
  | prim h k => exact .prim (h.relocate_right f) (k.relocate_right f)
  | extend h k => exact .extend (h.relocate_right f) (k.relocate_right f)
  | case h k => exact .case (h.relocate_right f) (k.relocate_right f)
  | ite h k j => exact .ite (h.relocate_right f) (k.relocate_right f) (j.relocate_right f)
theorem LawTerms.relocate_right {ts us} (h : LawTerms ts us) (f : Nat → Nat) :
    LawTerms ts (Term.relocateRow f us) := by
  cases h with
  | nil => exact .nil
  | cons h k => exact .cons (h.relocate_right f) (k.relocate_right f)
end

theorem find_fillRefsRow (σ : Nat → Option Term) (l : Label) :
    ∀ fs, Row.find? l (Term.fillRefsRow σ fs) =
      (Row.find? l fs).map (Term.fillRefs σ)
  | [] => rfl
  | (k,t)::fs => by
    simp only [Term.fillRefsRow, Row.find?]
    split <;> simp_all [find_fillRefsRow σ l fs]

/-- A prepared record retains each law field with only unresolved-hole refusals inserted. -/
theorem unresolvedBody_field {p : Package} {fs : List (Label × Term)} {b : Term}
    (hb : p.body = .record fs) (hp : unresolvedBody p = .ok b) :
    ∃ fs', b = .record fs' ∧ ∀ l t, Row.find? l fs = some t → NoRef t →
      ∃ t', Row.find? l fs' = some t' ∧ LawTerm t t' := by
  unfold unresolvedBody at hp
  split at hp
  · cases hp
    exact ⟨fs, hb, fun l t hf ht => ⟨t, hf, LawTerm.same ht⟩⟩
  · split at hp
    · cases hp
    rename_i t ht
    cases hp
    unfold Term.fillBounded at ht
    repeat' split at ht
    all_goals first | (cases ht; done) | skip
    cases ht
    rw [hb]
    refine ⟨_, rfl, fun l t hf ht => ?_⟩
    refine ⟨Term.fillRefs (fun n =>
      ((holeSignature p.holes).find? (fun d => d.name == n)).map
        (fun d => .refuse d.ty "holeUnresolved".toUTF8)) t, ?_, ?_⟩
    · rw [find_fillRefsRow, hf]; rfl
    · apply lawTerm_fill _ ?_ ht
      intro n v hv
      simp only [Option.map_eq_some_iff] at hv
      obtain ⟨d, _, rfl⟩ := hv
      exact ⟨d.ty, rfl⟩

end

end Nanodregg.Lang
