/-
# Lang.Proofs.Claim — a law in certifying shape means its claim (LANG-83)

* `guardedBy_sound`: a term `Term.guardedBy I k r` means `inj "ok" _` only when `I` applied to the
  value at index `k` meant `true`, or the term read a `relaw` occasion at index `r` (`GuardedOk`).
* `keeps_step`: a law in shape that ADMITS (`Std.Admits`) a request whose occasion is not a `relaw`
  leaves a state that keeps the invariant (`Keeps`).
* `chain_keeps`: along a `Std.Chain` of the law's steps (`Std.Step`: it admits, and a relaw or an
  adoption keeps the state), every state keeps the invariant once the first does. THE LIFT
  (`Kernel.Proofs.Logic.History.object_history_chain`) produces exactly such a chain from a World's
  history around an object, so this is the term half of INTEGRITY's claim clause (DESIGN-PCC §4).
* `keeps_guarded`, `isLaw_keeps`, `noRef_keeps`: `Std.keeps` is in shape, and has the shape the lift wants.
* `checkFields_claim`, `install_claims` (LANG-93): what the install check admitted BEARS every claim it
  carries: the body is a record literal holding the invariant and the law as literals, and the law is
  in certifying shape (`checkClaim_keeps`); so the carried sentence is exactly what `keeps_step` and
  `chain_keeps` are about, and KERNEL-73 (`Kernel.Proofs.Logic.Claims`) lifts it to the World.
-/
import Lang.Claim
import Lang.Proofs.Chain
import Lang.Proofs.Receiver
import Lang.Proofs.LiveHoles

namespace Nanodregg.Lang

variable {lib : List Term}

/-- The invariant's body `ib` (`var 0` the state) holds of `n`, stated as `Std.Admits` is: over some
closure environment (`ib` is typed `bool` under `[S]` at install, so it reads only `var 0`). -/
def Keeps (lib : List Term) (ib : Term) (n : Data) : Prop :=
  ∃ env, BigStep lib (n.toVal :: env) ib (.ok (.bool true))

/-- What a guarded `ok` means: the invariant held of the value at `k`, or a `relaw` was read at `r`. -/
def GuardedOk (lib : List Term) (ib : Term) (k r : Nat) (env : Env) : Prop :=
  (∃ x, env[k]? = some x ∧ ∃ env', BigStep lib (x :: env') ib (.ok (.bool true))) ∨
  (∃ x, BigStep lib env (.get (.var r) "occasion") (.ok (.inj "relaw" x)))

/-- One binder out: what held at `k + 1`, `r + 1` under `w :: env` holds at `k`, `r` under `env`. -/
theorem guardedOk_cons {ib : Term} {k r : Nat} {w : Val} {env : Env}
    (h : GuardedOk lib ib (k + 1) (r + 1) (w :: env)) : GuardedOk lib ib k r env := by
  rcases h with ⟨x, hx, env', hib⟩ | ⟨x, hx⟩
  · exact .inl ⟨x, by simpa using hx, env', hib⟩
  · refine .inr ⟨x, ?_⟩
    cases hx with
    | get ht hs =>
      obtain ⟨v, hv, he⟩ := bigStep_var_inv ht
      cases he
      exact .get (.var (by simpa using hv)) hs

mutual
/-- **The checker is sound.** A term in certifying shape means `ok` only through a guarded leaf. -/
theorem guardedBy_sound {S : Ty} {ib : Term} : ∀ {t : Term} {k r : Nat} {env : Env} {w : Val},
    Term.guardedBy (.lam S ib) k r t = true → BigStep lib env t (.ok (.inj "ok" w)) →
      GuardedOk lib ib k r env
  | .ite c a b, k, r, env, w, hg, h => by
      simp only [Term.guardedBy, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
      rcases bigStep_ite_ok h with ⟨hc, ha⟩ | ⟨-, hb⟩
      · rcases hg.1 with rfl | hga
        · obtain ⟨body, cenv, x, hf, hx, hbody⟩ := bigStep_app_ok hc
          cases hf
          exact .inl ⟨x, bigStep_var_ok hx, env, hbody⟩
        · exact guardedBy_sound hga ha
      · exact guardedBy_sound hg.2 hb
  | .case s arms, k, r, env, w, hg, h => by
      simp only [Term.guardedBy] at hg
      obtain ⟨ℓ, x, body, hs, hf, hb⟩ := bigStep_case_ok h
      rcases guardedArms_sound hg hf hb with ⟨hocc, rfl⟩ | hok
      · rw [beq_iff_eq] at hocc; subst hocc
        exact .inr ⟨x, hs⟩
      · exact guardedOk_cons hok
  | .inj _ ℓ t, k, r, env, w, hg, h => by
      obtain ⟨w', -, hv⟩ := bigStep_inj_ok h
      simp only [Term.guardedBy, bne_iff_ne, ne_eq] at hg
      cases hv; exact absurd rfl hg
  | .refuse _ _, _, _, _, _, _, h => by cases h
  | .var _, _, _, _, _, hg, _ | .lam _ _, _, _, _, _, hg, _ | .app _ _, _, _, _, _, hg, _
  | .fix _, _, _, _, _, hg, _ | .nat _, _, _, _, _, hg, _ | .bool _, _, _, _, _, hg, _
  | .bytes _, _, _, _, _, hg, _ | .digest _, _, _, _, _, hg, _ | .prim _ _ _, _, _, _, _, hg, _
  | .record _, _, _, _, _, hg, _ | .get _ _, _, _, _, _, hg, _ | .extend _ _, _, _, _, _, hg, _
  | .ref _, _, _, _, _, hg, _ | .hole _ _, _, _, _, _, hg, _ => by simp [Term.guardedBy] at hg

/-- The arm a case ran is guarded, or is the `relaw` arm of a case on the occasion. -/
theorem guardedArms_sound {S : Ty} {ib : Term} : ∀ {arms : List (Label × Term)} {k r : Nat} {occ : Bool}
    {ℓ : Label} {body : Term} {env : Env} {w : Val},
    Term.guardedArms (.lam S ib) k r occ arms = true → Row.find? ℓ arms = some body →
    BigStep lib env body (.ok (.inj "ok" w)) →
      (occ = true ∧ ℓ = "relaw") ∨ GuardedOk lib ib k r env
  | [], _, _, _, _, _, _, _, _, hf, _ => by simp [Row.find?] at hf
  | (ℓ', b') :: arms, k, r, occ, ℓ, body, env, w, hg, hf, hb => by
      simp only [Term.guardedArms, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
      by_cases hℓ : ℓ = ℓ'
      · subst hℓ
        have hbody : body = b' := by simpa [Row.find?] using hf.symm
        subst hbody
        rcases hg.1 with ⟨hocc, rfl⟩ | hgb
        · exact .inl ⟨hocc, rfl⟩
        · exact .inr (guardedBy_sound hgb hb)
      · have hf' : Row.find? ℓ arms = some body := by simpa [Row.find?, hℓ] using hf
        exact guardedArms_sound hg.2 hf' hb
end

/-- **A law in shape that admits keeps the invariant**, on every occasion but a `relaw`. -/
theorem keeps_step {S : Ty} {ib b : Term} {rq n o : Data}
    (hg : Term.guardedBy (.lam S ib) 1 0 b = true)
    (h : Std.Admits lib (.lam S (.lam S (.lam reqTy b))) rq n o)
    (hrel : ∀ x, rq.field "occasion" ≠ some (.inj "relaw" x)) : Keeps lib ib n := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [Std.lawBody] at hb
  rcases guardedBy_sound hg hb with ⟨x, hx, env', hib⟩ | ⟨x, hx⟩
  · simp at hx; subst hx; exact ⟨env', hib⟩
  · obtain ⟨y, hy, hv⟩ := bigStep_getVar (d := rq) (by simp) hx
    obtain ⟨y', rfl, -⟩ := Data.toVal_inj hv.symm
    exact absurd hy (hrel y')

/-- **Along the law's history every state keeps the invariant**, once the first does: a `relaw` keeps
the state (`Std.LawKeeps`), every other admitted step is `keeps_step`. -/
theorem chain_keeps {S : Ty} {ib b : Term} (hg : Term.guardedBy (.lam S ib) 1 0 b = true) :
    ∀ {o : Data} {steps : List (Data × Data)}, Keeps lib ib o →
      Std.Chain (Std.Step lib (.lam S (.lam S (.lam reqTy b)))) o steps → ∀ s ∈ steps, Keeps lib ib s.2
  | _, [], _, _, _, hs => nomatch hs
  | _, (rq, n) :: _, h0, .cons ⟨hadm, hkeep⟩ hch, s, hs => by
      have hn : Keeps lib ib n := by
        by_cases hr : ∃ x, rq.field "occasion" = some (.inj "relaw" x)
        · obtain ⟨x, hx⟩ := hr
          rw [hkeep "relaw" x hx (.inl rfl)]; exact h0
        · exact keeps_step hg hadm (fun x hx => hr ⟨x, hx⟩)
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hn
      · exact chain_keeps hg hn hch s hs

/-! ## `Std.keeps` is in shape -/

theorem keeps_guarded (S : Ty) (ib : Term) :
    Term.guardedBy (.lam S ib) 1 0 (Std.lawBody (Std.keeps S (.lam S ib))) = true := by
  simp [Std.keeps, Std.lawOf, Std.lawCase, Std.lawCase6, Std.lawBody, Std.guard, Std.okT, Std.refusedT,
    Term.guardedBy, Term.guardedArms, Std.At.new]

theorem isLaw_keeps (S : Ty) (inv : Term) : IsLaw (Std.keeps S inv) := ⟨_, _, _, _, rfl⟩

theorem noRef_keeps (S : Ty) {inv : Term} (h : NoRef inv) : NoRef (Std.keeps S inv) := by
  have hc : NoRef (Std.guard (.app inv (Std.At.new ⟨1⟩)) "invariant" Std.okT) := by
    simp only [Std.guard, NoRef, Std.At.new]
    exact ⟨⟨h, trivial⟩, NoRefStd.okT_, NoRefStd.refusedT_⟩
  exact NoRefStd.lawOf_ hc hc NoRefStd.okT_ hc hc

/-! ## The install layer (LANG-93): what the check admitted bears the claim -/

/-- The witness `checkClaim` walked for a `keeps` claim it admitted: the law is one of the package's,
the invariant an interface field at `fn S bool`, the body a record literal holding the invariant as
`lam S ib` and the law as `lam S (lam S (lam reqTy b))`, and `b` in certifying shape. -/
theorem checkClaim_keeps {S : Ty} {row : List (Label × Ty)} {laws : List Label} {body : Term}
    {inv law : Label} (h : checkClaim S row laws body (.keeps inv law) = .ok ()) :
    law ∈ laws ∧ Row.find? inv row = some (.fn S .bool) ∧
      ∃ fs ib b, body = .record fs ∧ Row.find? inv fs = some (.lam S ib) ∧
        Row.find? law fs = some (.lam S (.lam S (.lam reqTy b))) ∧ Term.guardedBy (.lam S ib) 1 0 b = true := by
  simp only [checkClaim] at h
  by_cases h1 : law ∉ laws
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : Row.find? inv row ≠ some (.fn S .bool)
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  split at h
  · rename_i fs
    split at h
    · rename_i A ib B C Q b hi hl
      by_cases h3 : A = S ∧ B = S ∧ C = S ∧ Q = reqTy
      · rw [if_pos h3] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h3
        split at h
        · rename_i hg
          exact ⟨by simpa using h1, by simpa using h2, fs, ib, b, rfl, hi, hl, hg⟩
        · cases h
      · rw [if_neg h3] at h; cases h
    · cases h
  · cases h

theorem checkClaims_mem {S : Ty} {row : List (Label × Ty)} {laws : List Label} {body : Term} :
    ∀ {cs : List Claim}, checkClaims S row laws body cs = .ok () → ∀ c ∈ cs, checkClaim S row laws body c = .ok ()
  | [], _, _, hc => by simp at hc
  | c :: cs, h, c', hc => by
    simp only [checkClaims, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i u hu
      cases u
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hu
      · exact checkClaims_mem h c' hc

/-- **The field check bears every claim**: a package whose `checkFields` admits carries, for each
`keeps inv law` it claims, the witness `checkClaim_keeps` names, at the package's own state type. -/
theorem checkFields_claim {p : Package} (h : p.checkFields = .ok ()) {inv law : Label}
    (hc : Claim.keeps inv law ∈ p.claims) :
    law ∈ p.laws ∧ Row.find? inv (recordRow p.iface) = some (.fn p.state .bool) ∧
      ∃ fs ib b, p.body = .record fs ∧ Row.find? inv fs = some (.lam p.state ib) ∧
        Row.find? law fs = some (.lam p.state (.lam p.state (.lam reqTy b))) ∧
        Term.guardedBy (.lam p.state ib) 1 0 b = true := by
  unfold Package.checkFields at h
  split at h
  · rename_i row hrow
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · rw [hrow]; exact checkClaim_keeps (checkClaims_mem h _ hc)
  · simp at h

/-- The install check admits only a package whose field check admits: install's own admission of
the package (`admitContextual`, LANG-78) keeps the closure invariant, which holds `checkFields`. -/
theorem checkInstall_fields {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} {p : Package} (h : checkInstall digestOf look b = .ok ())
    (hd : Wire.decodePackage b = .ok p) : p.checkFields = .ok () := by
  have hpw : Wire.packageWire p = true := by
    obtain ⟨b', hb⟩ : ∃ b', Wire.encodePackage p = some b' := ⟨_, Wire.decodePackage_eq_ok_iff.mp hd⟩
    unfold Wire.encodePackage at hb
    split at hb
    · assumption
    · simp at hb
  unfold checkInstall at h
  simp only [bind, Except.bind, pure, Except.pure, hd] at h
  cases hl : loadAllContextual digestOf look (closureDepthMax - 1) p.imports ⟨[], [], []⟩ with
  | error e => simp [hl] at h
  | ok x =>
  obtain ⟨L, gis⟩ := x
  simp only [hl] at h
  cases ha : admitContextual digestOf (fun _ => unresolvedBody) b p L gis with
  | error e => simp [ha] at h
  | ok y =>
  obtain ⟨L', g⟩ := y
  have hinv := (loadAllUsing_inv digestOf look _ (fun hi hw ha => admitContextual_inv hi hw ha)
    _ _ _ Inv.empty hl).1
  obtain ⟨hinv', -, hpk⟩ := admitContextual_inv hinv hpw ha
  exact (hinv'.2.2.2 L.pkgs.length p (by simp [hpk])).2.1

/-- **An installed package bears its claims** (DESIGN-PCC §3.3(b)): bytes the install check admits
decode to a package that carries, for each `keeps inv law` it claims, a body in certifying shape for
it. With `keeps_step`/`chain_keeps` that makes the claim a sentence about every admitted step of the
law; KERNEL-73 composes it with THE LIFT. -/
theorem install_claims {D : Type} {digestOf : ByteArray → Option D} {look : Kernel.Receive.Pinned D}
    {b : ByteArray} {p : Package} (h : checkInstall digestOf look b = .ok ())
    (hd : Wire.decodePackage b = .ok p) {inv law : Label} (hc : Claim.keeps inv law ∈ p.claims) :
    law ∈ p.laws ∧ Row.find? inv (recordRow p.iface) = some (.fn p.state .bool) ∧
      ∃ fs ib b', p.body = .record fs ∧ Row.find? inv fs = some (.lam p.state ib) ∧
        Row.find? law fs = some (.lam p.state (.lam p.state (.lam reqTy b'))) ∧
        Term.guardedBy (.lam p.state ib) 1 0 b' = true :=
  checkFields_claim (checkInstall_fields h hd) hc

end Nanodregg.Lang
