/-
# Lang.Proofs.Std — what each stdlib law means, over the reference semantics

Every theorem here reads an ADMITTED law (its body has the meaning `ok`) back to a fact about the
old state, the new state and the request, as data. They are proved compositionally from the
combinators' inversion lemmas (`guard_ok`, `allOf_ok`, `anyOf_true`, `lawCase_arm`), never by
evaluating a generated term. The environment is `req :: new :: old :: E` for an arbitrary `E`, so a
statement covers both the closed term a test runs and the package field the receiver selects.
-/
import Lang.Std
import Lang.Proofs.StdData
import Lang.Law
import Lang.Proofs.Meaning
import Lang.Proofs.Agree

namespace Nanodregg.Lang.Std

open Nanodregg.Lang

variable {lib : List Term} {env : Env}

/-! ## The combinators -/

theorem okT_value {w : Val} (h : BigStep lib env okT (.ok w)) : w = .inj "ok" (.record []) := by
  obtain ⟨u, hu, rfl⟩ := bigStep_inj_ok h
  cases hu; rfl

theorem refusedT_not_ok {why : String} {w : Val} :
    ¬ BigStep lib env (refusedT why) (.ok (.inj "ok" w)) := by
  intro h
  obtain ⟨u, _, hv⟩ := bigStep_inj_ok h
  simp at hv

theorem guard_ok {c rest : Term} {why : String} {w : Val}
    (h : BigStep lib env (guard c why rest) (.ok (.inj "ok" w))) :
    BigStep lib env c (.ok (.bool true)) ∧ BigStep lib env rest (.ok (.inj "ok" w)) := by
  rcases bigStep_ite_ok h with ⟨hc, hr⟩ | ⟨_, hr⟩
  · exact ⟨hc, hr⟩
  · exact (refusedT_not_ok hr).elim

theorem guards_ok {w : Val} : ∀ {l : List (Term × String)} {rest : Term},
    BigStep lib env (guards l rest) (.ok (.inj "ok" w)) →
      (∀ p ∈ l, BigStep lib env p.1 (.ok (.bool true))) ∧ BigStep lib env rest (.ok (.inj "ok" w))
  | [], _, h => ⟨by simp, h⟩
  | (c, why) :: l, rest, h => by
    obtain ⟨hc, hr⟩ := guard_ok (c := c) (why := why) h
    obtain ⟨hl, hrest⟩ := guards_ok hr
    refine ⟨?_, hrest⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hc
    · exact hl p hp

theorem allOf_ok {l : List (Term × String)} {w : Val}
    (h : BigStep lib env (allOf l) (.ok (.inj "ok" w))) :
    ∀ p ∈ l, BigStep lib env p.1 (.ok (.bool true)) :=
  (guards_ok h).1

theorem anyOf_true : ∀ {cs : List Term}, BigStep lib env (anyOf cs) (.ok (.bool true)) →
    ∃ c ∈ cs, BigStep lib env c (.ok (.bool true))
  | [], h => by cases bigStep_bool_inv h
  | c :: cs, h => by
    rcases bigStep_ite_ok h with ⟨hc, _⟩ | ⟨_, hr⟩
    · exact ⟨c, List.mem_cons_self .., hc⟩
    · obtain ⟨c', hc', h'⟩ := anyOf_true hr
      exact ⟨c', List.mem_cons_of_mem _ hc', h'⟩

theorem andT_true {a b : Term} (h : BigStep lib env (andT a b) (.ok (.bool true))) :
    BigStep lib env a (.ok (.bool true)) ∧ BigStep lib env b (.ok (.bool true)) := by
  rcases bigStep_ite_ok h with ⟨ha, hb⟩ | ⟨_, hf⟩
  · exact ⟨ha, hb⟩
  · cases bigStep_bool_inv hf

theorem notT_true {a : Term} (h : BigStep lib env (notT a) (.ok (.bool true))) :
    BigStep lib env a (.ok (.bool false)) := by
  rcases bigStep_ite_ok h with ⟨_, hf⟩ | ⟨ha, _⟩
  · cases bigStep_bool_inv hf
  · exact ha

theorem notT_false {a : Term} (h : BigStep lib env (notT a) (.ok (.bool false))) :
    BigStep lib env a (.ok (.bool true)) := by
  rcases bigStep_ite_ok h with ⟨ha, _⟩ | ⟨_, ht⟩
  · exact ha
  · cases bigStep_bool_inv ht

/-! ## Primitive conditions on data fields -/

theorem primEval_le_true {x y : Val} (h : primEval .le x y = .ok (.bool true)) :
    ∃ a b, x = .nat a ∧ y = .nat b ∧ a ≤ b := by
  cases x <;> cases y <;> simp [primEval] at h ⊢; exact h

theorem primEval_lt_true {x y : Val} (h : primEval .lt x y = .ok (.bool true)) :
    ∃ a b, x = .nat a ∧ y = .nat b ∧ a < b := by
  cases x <;> cases y <;> simp [primEval] at h ⊢; exact h

theorem primEval_eq_bool {x y : Val} {b : Bool} (h : primEval .eq x y = .ok (.bool b)) :
    ∃ m n, x = .nat m ∧ y = .nat n ∧ decide (m = n) = b := by
  cases x <;> cases y <;> simp [primEval] at h ⊢; exact h

theorem primEval_beq_bool {x y : Val} {b : Bool} (h : primEval .beq x y = .ok (.bool b)) :
    ∃ s t, x = .bytes s ∧ y = .bytes t ∧ decide (s = t) = b := by
  cases x <;> cases y <;> simp [primEval] at h ⊢; exact h

theorem primEval_deq_bool {x y : Val} {b : Bool} (h : primEval .deq x y = .ok (.bool b)) :
    ∃ s t, x = .digest s ∧ y = .digest t ∧ decide (s = t) = b := by
  cases x <;> cases y <;> simp [primEval] at h ⊢; exact h

/-- The value of a selected field, as data: `get (var i) f` with `d` bound at `i`. -/
theorem getVar_nat {i : Nat} {d : Data} {f : Label} {m : Nat} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.get (.var i) f) (.ok (.nat m))) : d.field f = some (.nat m) := by
  obtain ⟨x, hx, hv⟩ := bigStep_getVar hi h
  rw [Data.toVal_nat hv.symm] at hx; exact hx

theorem getVar_bytes {i : Nat} {d : Data} {f : Label} {s : ByteArray} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.get (.var i) f) (.ok (.bytes s))) : d.field f = some (.bytes s) := by
  obtain ⟨x, hx, hv⟩ := bigStep_getVar hi h
  rw [Data.toVal_bytes hv.symm] at hx; exact hx

theorem getVar_digest {i : Nat} {d : Data} {f : Label} {s : ByteArray} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.get (.var i) f) (.ok (.digest s))) : d.field f = some (.digest s) := by
  obtain ⟨x, hx, hv⟩ := bigStep_getVar hi h
  rw [Data.toVal_digest hv.symm] at hx; exact hx

/-! ## The law skeleton -/

/-- An admitted `lawCase6` ran the arm of the request's occasion, on its payload. -/
theorem lawCase6_arm {b ad rl rt wr iv : At → Term} {rq : Data} {ℓ : Label} {x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj ℓ x))
    (h : BigStep lib env (lawCase6 b ad rl rt wr iv) (.ok v)) :
    ∃ body, Row.find? ℓ [("adopt", ad ⟨1⟩), ("birth", b ⟨1⟩), ("invoke", iv ⟨1⟩), ("relaw", rl ⟨1⟩),
      ("retire", rt ⟨1⟩), ("write", wr ⟨1⟩)] = some body ∧
      BigStep lib (x.toVal :: env) body (.ok v) := by
  obtain ⟨ℓ', w, body, hs, hf, hb⟩ := bigStep_case_ok h
  obtain ⟨y, hy, hv⟩ := bigStep_getVar hr hs
  rw [ho] at hy; cases hy
  obtain ⟨y', hy', hw⟩ := Data.toVal_inj hv.symm
  cases hy'; subst hw
  exact ⟨body, hf, hb⟩

theorem lawCase_arm {b ad rl rt c : At → Term} {rq : Data} {ℓ : Label} {x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj ℓ x))
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    ∃ body, Row.find? ℓ [("adopt", ad ⟨1⟩), ("birth", b ⟨1⟩), ("invoke", c ⟨1⟩), ("relaw", rl ⟨1⟩),
      ("retire", rt ⟨1⟩), ("write", c ⟨1⟩)] = some body ∧
      BigStep lib (x.toVal :: env) body (.ok v) :=
  lawCase6_arm hr ho h

/-- Which arm the change clause is: a write or an invoke. -/
def IsChange (o : Data) : Prop := (∃ x, o = .inj "write" x) ∨ (∃ x, o = .inj "invoke" x)

theorem lawCase_change {b ad rl rt c : At → Term} {rq occ : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some occ) (hc : IsChange occ)
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    ∃ x : Data, BigStep lib (x.toVal :: env) (c ⟨1⟩) (.ok v) := by
  rcases hc with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
    simp [Row.find?] at hf; subst hf; exact ⟨x, hb⟩
  · obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
    simp [Row.find?] at hf; subst hf; exact ⟨x, hb⟩

theorem lawCase_birth {b ad rl rt c : At → Term} {rq x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj "birth" x))
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    BigStep lib (x.toVal :: env) (b ⟨1⟩) (.ok v) := by
  obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
  simp [Row.find?] at hf; subst hf; exact hb

theorem lawCase_relaw {b ad rl rt c : At → Term} {rq x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj "relaw" x))
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    BigStep lib (x.toVal :: env) (rl ⟨1⟩) (.ok v) := by
  obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
  simp [Row.find?] at hf; subst hf; exact hb

theorem lawCase_adopt {b ad rl rt c : At → Term} {rq x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj "adopt" x))
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    BigStep lib (x.toVal :: env) (ad ⟨1⟩) (.ok v) := by
  obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
  simp [Row.find?] at hf; subst hf; exact hb

theorem lawCase_retire {b ad rl rt c : At → Term} {rq x : Data} {v : Val}
    (hr : env[0]? = some rq.toVal) (ho : rq.field "occasion" = some (.inj "retire" x))
    (h : BigStep lib env (lawCase b ad rl rt c) (.ok v)) :
    BigStep lib (x.toVal :: env) (rt ⟨1⟩) (.ok v) := by
  obtain ⟨body, hf, hb⟩ := lawCase_arm hr ho h
  simp [Row.find?] at hf; subst hf; exact hb

/-! ## The laws -/

/-- Law `t` ADMITS `o → n` under request `rq`: its body means `ok` with the request, new and old
states bound above some closure environment. `runLaw_admits` (a closed term, as a test runs it)
and `runLaw_ref_admits` (a package field, as the receiver runs it) produce exactly this. -/
def Admits (lib : List Term) (t : Term) (rq n o : Data) : Prop :=
  ∃ cenv w, BigStep lib (rq.toVal :: n.toVal :: o.toVal :: cenv) (lawBody t) (.ok (.inj "ok" w))

/-- `bounded S f max`: in every admitted birth, adoption, write and invoke, the NEW value of `f` is a
natural at most `max` (so the law cannot be added over a state that already breaks it). -/
theorem bounded_spec {S : Ty} {f : Label} {max : Nat} {rq n o occ : Data}
    (h : Admits lib (bounded S f max) rq n o)
    (ho : rq.field "occasion" = some occ)
    (hc : IsChange occ ∨ (∃ x, occ = .inj "birth" x) ∨ ∃ x, occ = .inj "adopt" x) :
    ∃ m, n.field f = some (.nat m) ∧ m ≤ max := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [bounded, boundedWith, lawOf, lawBody] at hb
  have key : ∀ x : Data, BigStep lib (x.toVal :: LawEnv rq n o cenv)
      (allOf [(.prim .le ((⟨1⟩ : At).newF f) (natT max), s!"{f} over the bound")]) (.ok (.inj "ok" w)) →
      ∃ m, n.field f = some (.nat m) ∧ m ≤ max := by
    intro x hx
    have hle := allOf_ok hx _ (List.mem_singleton_self _)
    obtain ⟨a, b, ha, hb, hp⟩ := bigStep_prim_ok hle
    obtain ⟨a', b', rfl, rfl, hab⟩ := primEval_le_true hp
    cases bigStep_nat_inv hb
    exact ⟨a', getVar_nat (d := n) (i := 2) rfl ha, hab⟩
  rcases hc with hc | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨x, hx⟩ := lawCase_change rfl ho hc hb
    exact key x hx
  · exact key x (lawCase_birth rfl ho hb)
  · exact key x (lawCase_adopt rfl ho hb)

/-! ## Scalars: equality of data through equality of values -/

/-- A natural, a byte string or a digest. -/
def Scalar (v : Val) : Prop := (∃ m, v = .nat m) ∨ (∃ s, v = .bytes s) ∨ (∃ s, v = .digest s)

theorem toVal_scalar_inj {x y : Data} (hs : Scalar x.toVal) (h : x.toVal = y.toVal) : x = y := by
  rcases hs with ⟨m, hm⟩ | ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [Data.toVal_nat hm, Data.toVal_nat (h.symm.trans hm)]
  · rw [Data.toVal_bytes hs, Data.toVal_bytes (h.symm.trans hs)]
  · rw [Data.toVal_digest hs, Data.toVal_digest (h.symm.trans hs)]

/-- `eqAt T a b` means a boolean that compares two scalars. -/
theorem eqAt_bool {T : Ty} {a b : Term} {bo : Bool} (h : BigStep lib env (eqAt T a b) (.ok (.bool bo))) :
    ∃ x y, BigStep lib env a (.ok x) ∧ BigStep lib env b (.ok y) ∧ Scalar x ∧ (x = y ↔ bo = true) := by
  unfold eqAt at h
  split at h
  · obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
    obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_beq_bool hp
    refine ⟨_, _, ha, hb, .inr (.inl ⟨s, rfl⟩), ?_⟩
    rw [← hd]; simp
  · split at h
    · obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
      obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_deq_bool hp
      refine ⟨_, _, ha, hb, .inr (.inr ⟨s, rfl⟩), ?_⟩
      rw [← hd]; simp
    obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
    obtain ⟨m, n, rfl, rfl, hd⟩ := primEval_eq_bool hp
    refine ⟨_, _, ha, hb, .inl ⟨m, rfl⟩, ?_⟩
    rw [← hd]; simp

/-- `eqAt` of two selected fields: the fields exist, and are equal exactly when it says `true`. -/
theorem eqAt_fields {T : Ty} {i j : Nat} {d e : Data} {f g : Label} {bo : Bool}
    (hi : env[i]? = some d.toVal) (hj : env[j]? = some e.toVal)
    (h : BigStep lib env (eqAt T (.get (.var i) f) (.get (.var j) g)) (.ok (.bool bo))) :
    ∃ x y, d.field f = some x ∧ e.field g = some y ∧ (x = y ↔ bo = true) := by
  obtain ⟨vx, vy, ha, hb, hs, hiff⟩ := eqAt_bool h
  obtain ⟨x, hx, rfl⟩ := bigStep_getVar hi ha
  obtain ⟨y, hy, rfl⟩ := bigStep_getVar hj hb
  refine ⟨x, y, hx, hy, ?_⟩
  rw [← hiff]
  exact ⟨fun h => h ▸ rfl, toVal_scalar_inj hs⟩

/-- A `beq` of a selected field with a literal: the field is exactly those bytes. -/
theorem beq_field_lit {i : Nat} {d : Data} {f : Label} {m : ByteArray} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.prim .beq (.get (.var i) f) (.bytes m)) (.ok (.bool true))) :
    d.field f = some (.bytes m) := by
  obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
  obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_beq_bool hp
  cases bigStep_bytes_inv hb
  simp at hd; subst hd
  exact getVar_bytes hi ha

/-- A `beq` of two selected fields: both are the same bytes. -/
theorem beq_fields {i j : Nat} {d e : Data} {f g : Label} (hi : env[i]? = some d.toVal)
    (hj : env[j]? = some e.toVal)
    (h : BigStep lib env (.prim .beq (.get (.var i) f) (.get (.var j) g)) (.ok (.bool true))) :
    ∃ s, d.field f = some (.bytes s) ∧ e.field g = some (.bytes s) := by
  obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
  obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_beq_bool hp
  simp at hd; subst hd
  exact ⟨s, getVar_bytes hi ha, getVar_bytes hj hb⟩

/-- A `deq` of a selected field with an id literal: the field is exactly that digest. -/
theorem deq_field_lit {i : Nat} {d : Data} {f : Label} {m : ByteArray} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.prim .deq (.get (.var i) f) (.digest m)) (.ok (.bool true))) :
    d.field f = some (.digest m) := by
  obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
  obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_deq_bool hp
  cases bigStep_digest_inv hb
  simp at hd; subst hd
  exact getVar_digest hi ha

/-- A `deq` of two selected fields: both are the same digest. -/
theorem deq_fields {i j : Nat} {d e : Data} {f g : Label} (hi : env[i]? = some d.toVal)
    (hj : env[j]? = some e.toVal)
    (h : BigStep lib env (.prim .deq (.get (.var i) f) (.get (.var j) g)) (.ok (.bool true))) :
    ∃ s, d.field f = some (.digest s) ∧ e.field g = some (.digest s) := by
  obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
  obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_deq_bool hp
  simp at hd; subst hd
  exact ⟨s, getVar_digest hi ha, getVar_digest hj hb⟩

/-- `eq` of a selected natural field with a literal. -/
theorem eq_field_lit {i : Nat} {d : Data} {f : Label} {k : Nat} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.prim .eq (.get (.var i) f) (natT k)) (.ok (.bool true))) :
    d.field f = some (.nat k) := by
  obtain ⟨x, y, ha, hb, hp⟩ := bigStep_prim_ok h
  obtain ⟨m, n, rfl, rfl, hd⟩ := primEval_eq_bool hp
  cases bigStep_nat_inv hb
  simp at hd; subst hd
  exact getVar_nat hi ha

/-! ## Authority -/

theorem find_const {α : Type} {ℓ : Label} {t b : α} :
    ∀ {l : List (Label × α)}, (∀ p ∈ l, p.2 = t) → Row.find? ℓ l = some b → b = t
  | [], _, h => by simp [Row.find?] at h
  | (k, a) :: l, hall, h => by
    simp only [Row.find?] at h
    split at h
    · cases h; exact hall _ (List.mem_cons_self ..)
    · exact find_const (fun p hp => hall p (List.mem_cons_of_mem _ hp)) h

/-- `ownerSigns`: in every admitted act the signer IS the principal (so no delegate acted through
a grant; with KERNEL-25's owner gate, the principal is the owner). -/
theorem ownerSigns_spec {S : Ty} {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (ownerSigns S) rq n o) (ho : rq.field "occasion" = some (.inj ℓ x)) :
    ∃ s, rq.field "agent" = some (.digest s) ∧ rq.field "principal" = some (.digest s) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [ownerSigns, lawOf, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase_arm rfl ho hb
  have hc := find_const (t := allOf [(.prim .deq ((⟨1⟩ : At).reqF "agent") ((⟨1⟩ : At).reqF "principal"),
      "not signed by the owner")]) (by simp) hf
  subst hc
  exact deq_fields (d := rq) (e := rq) rfl rfl (allOf_ok hbody _ (List.mem_singleton_self _))

theorem isListed {ids : List ByteArray} {a : At} {rq : Data} (hr : env[a.depth]? = some rq.toVal)
    (h : BigStep lib env (anyOf (ids.map fun i => .prim .deq (a.reqF "agent") (.digest i))) (.ok (.bool true))) :
    ∃ m ∈ ids, rq.field "agent" = some (.digest m) := by
  obtain ⟨c, hc, hct⟩ := anyOf_true h
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
  exact ⟨m, hm, deq_field_lit hr hct⟩

/-- `allowlistLaw`: every admitted act, of every occasion, is signed by a listed member. -/
theorem allowlist_spec {ids : List ByteArray} {S : Ty} {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (allowlistLaw S ids) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) :
    ∃ m ∈ ids, rq.field "agent" = some (.digest m) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [allowlistLaw, lawOf, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase_arm rfl ho hb
  have hc := find_const (t := allOf [(anyOf (ids.map fun i => .prim .deq ((⟨1⟩ : At).reqF "agent") (.digest i)),
      "not on the allowlist")]) (by simp) hf
  subst hc
  exact isListed (a := ⟨1⟩) rfl (allOf_ok hbody _ (List.mem_singleton_self _))

/-! ## Quorum -/

theorem primEval_add_ok {x y v : Val} (h : primEval .add x y = .ok v) :
    ∃ a b, x = .nat a ∧ y = .nat b ∧ v = .nat (a + b) := by
  cases x <;> cases y <;> simp [primEval, natResult] at h ⊢
  split at h <;> simp at h; exact h.symm

theorem primEval_div_ok {x y v : Val} (h : primEval .div x y = .ok v) :
    ∃ a b, x = .nat a ∧ y = .nat b ∧ v = .nat (a / b) := by
  cases x <;> cases y <;> simp [primEval] at h ⊢
  split at h <;> simp at h; exact h.symm

theorem primEval_mod_ok {x y v : Val} (h : primEval .mod x y = .ok v) :
    ∃ a b, x = .nat a ∧ y = .nat b ∧ v = .nat (a % b) := by
  cases x <;> cases y <;> simp [primEval] at h ⊢
  split at h <;> simp at h; exact h.symm

/-- `bit t i` of a natural field means that field's bit `i`. -/
theorem bit_field {i j : Nat} {d : Data} {f : Label} {v : Val} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (bit (.get (.var i) f) j) (.ok v)) :
    ∃ a, d.field f = some (.nat a) ∧ v = .nat (a / pow2 j % 2) := by
  obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok h
  obtain ⟨p, q, rfl, rfl, rfl⟩ := primEval_mod_ok hp
  cases bigStep_nat_inv hy
  obtain ⟨x', y', hx', hy', hp'⟩ := bigStep_prim_ok hx
  obtain ⟨a, b, rfl, rfl, hv⟩ := primEval_div_ok hp'
  cases bigStep_nat_inv hy'
  cases hv
  exact ⟨a, getVar_nat hi hx', rfl⟩

theorem popcount_fold {i : Nat} {d : Data} {f : Label} (hi : env[i]? = some d.toVal) :
    ∀ (l : List Nat) (acc : Term) {p : Nat},
      BigStep lib env (l.foldl (fun acc j => .prim .add acc (bit (.get (.var i) f) j)) acc) (.ok (.nat p)) →
      ∃ q, BigStep lib env acc (.ok (.nat q)) ∧
        (∀ a, d.field f = some (.nat a) → p = l.foldl (fun s j => s + a / pow2 j % 2) q) ∧
        (l ≠ [] → ∃ a, d.field f = some (.nat a))
  | [], acc, p, h => ⟨p, h, fun _ _ => rfl, fun h => (h rfl).elim⟩
  | j :: l, acc, p, h => by
    obtain ⟨q', hq', hl, _⟩ := popcount_fold hi l _ h
    obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok hq'
    obtain ⟨u, b, rfl, rfl, hv⟩ := primEval_add_ok hp
    cases hv
    obtain ⟨a, ha, hb⟩ := bit_field hi hy
    cases hb
    refine ⟨u, hx, fun a' ha' => ?_, fun _ => ⟨a, ha⟩⟩
    rw [ha] at ha'; cases ha'
    simp only [List.foldl]; exact hl a ha

/-- `popcount` of a natural field over `cnt > 0` bits means `popcountNat` of it. -/
theorem popcount_field {i cnt : Nat} {d : Data} {f : Label} {p : Nat} (hi : env[i]? = some d.toVal)
    (hc : 0 < cnt) (h : BigStep lib env (popcount (.get (.var i) f) cnt) (.ok (.nat p))) :
    ∃ a, d.field f = some (.nat a) ∧ p = popcountNat a cnt := by
  obtain ⟨q, hq, hl, hne⟩ := popcount_fold hi (List.range cnt) (natT 0) h
  cases bigStep_nat_inv hq
  obtain ⟨a, ha⟩ := hne (by simp [List.range_eq_nil]; omega)
  exact ⟨a, ha, hl a ha⟩

/-- Selecting an injection-valued field and casing on it: the field is that injection. -/
theorem case_field {i : Nat} {d : Data} {f : Label} {arms : List (Label × Term)} {v : Val}
    (hi : env[i]? = some d.toVal) (h : BigStep lib env (.case (.get (.var i) f) arms) (.ok v)) :
    ∃ ℓ y body, d.field f = some (.inj ℓ y) ∧ Row.find? ℓ arms = some body ∧
      BigStep lib (y.toVal :: env) body (.ok v) := by
  obtain ⟨ℓ, w, body, hs, hf, hb⟩ := bigStep_case_ok h
  obtain ⟨x, hx, hv⟩ := bigStep_getVar hi hs
  obtain ⟨y, rfl, rfl⟩ := Data.toVal_inj hv.symm
  exact ⟨ℓ, y, body, hx, hf, hb⟩

/-- Two-armed rows: which arm a `find?` chose. -/
theorem find_two {α : Type} {ℓ : Label} {a b c : α} (h : Row.find? ℓ [("laws", a), ("set", b)] = some c) :
    (ℓ = "laws" ∧ c = a) ∨ (ℓ = "set" ∧ c = b) := by
  simp only [Row.find?] at h
  split at h
  · cases h; exact .inl ⟨by assumption, rfl⟩
  · split at h
    · cases h; exact .inr ⟨by assumption, rfl⟩
    · cases h

/-- The meaning of `sameProposal` on the new and old `proposal` fields: both exist, and the
boolean says exactly whether they are equal. -/
theorem sameProposal_bool {T : Ty} {x rq n o : Data} {E : Env} {bo : Bool}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E)
      (sameProposal T ⟨1⟩ (fun b => b.newF "proposal") (fun b => b.oldF "proposal")) (.ok (.bool bo))) :
    ∃ np op, n.field "proposal" = some np ∧ o.field "proposal" = some op ∧ (np = op ↔ bo = true) := by
  obtain ⟨ℓ1, y1, body1, h1, hf1, hb1⟩ := case_field (d := n) (i := 2) rfl h
  rcases find_two hf1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨ℓ2, y2, body2, h2, hf2, hb2⟩ := case_field (d := o) (i := 4) rfl hb1
    rcases find_two hf2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok hb2
      obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_beq_bool hp
      have hu' := bigStep_var_ok hu; have hv' := bigStep_var_ok hv
      simp at hu' hv'
      refine ⟨_, _, h1, h2, ?_⟩
      rw [Data.toVal_bytes hu', Data.toVal_bytes hv', ← hd]
      simp [eq_comm]
    · cases bigStep_bool_inv hb2; exact ⟨_, _, h1, h2, by simp⟩
  · obtain ⟨ℓ2, y2, body2, h2, hf2, hb2⟩ := case_field (d := o) (i := 4) rfl hb1
    rcases find_two hf2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases bigStep_bool_inv hb2; exact ⟨_, _, h1, h2, by simp⟩
    · obtain ⟨u, v, hu, hv, hs, hiff⟩ := eqAt_bool hb2
      have hu' := bigStep_var_ok hu; have hv' := bigStep_var_ok hv
      simp at hu' hv'; subst hu' hv'
      refine ⟨_, _, h1, h2, ?_⟩
      rw [← hiff]
      constructor
      · intro h; cases h; rfl
      · intro h; rw [toVal_scalar_inj hs h]

/-- `proposedSet`: the old proposal is `set` of the new value of `guarded`. -/
theorem proposedSet_true {T : Ty} {g : Label} {x rq n o : Data} {E : Env}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E) (proposedSet T g ⟨1⟩) (.ok (.bool true))) :
    ∃ y, o.field "proposal" = some (.inj "set" y) ∧ n.field g = some y := by
  obtain ⟨ℓ, y, body, h1, hf, hb⟩ := case_field (d := o) (i := 3) rfl h
  rcases find_two hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases bigStep_bool_inv hb
  · obtain ⟨u, v, hu, hv, hs, hiff⟩ := eqAt_bool hb
    have hu' := bigStep_var_ok hu; simp at hu'; subst hu'
    obtain ⟨z, hz, rfl⟩ := bigStep_getVar (d := n) (i := 3) rfl hv
    exact ⟨y, h1, by rw [hz, toVal_scalar_inj hs (hiff.2 rfl)]⟩

/-- `proposedLaws`: the old proposal is `laws` of exactly the incoming laws' bytes. -/
theorem proposedLaws_true {x rq n o : Data} {E : Env}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E) (proposedLaws ⟨1⟩) (.ok (.bool true))) :
    ∃ s, o.field "proposal" = some (.inj "laws" (.bytes s)) ∧ x = .bytes s := by
  obtain ⟨ℓ, y, body, h1, hf, hb⟩ := case_field (d := o) (i := 3) rfl h
  rcases find_two hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok hb
    obtain ⟨s, t, rfl, rfl, hd⟩ := primEval_beq_bool hp
    have hu' := bigStep_var_ok hu; have hv' := bigStep_var_ok hv
    simp [At.under] at hu' hv'
    simp at hd; subst hd
    rw [Data.toVal_bytes hu'] at h1
    exact ⟨s, h1, Data.toVal_bytes hv'⟩
  · cases bigStep_bool_inv hb

/-- `approvalBy a m i`: member `m` signed, bit `i` of the old approvals was unset, and the new
approvals add exactly that bit. -/
theorem approvalBy_true {m : ByteArray} {i : Nat} {x rq n o : Data} {E : Env}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E) (approvalBy ⟨1⟩ m i) (.ok (.bool true))) :
    rq.field "agent" = some (.digest m) ∧ ∃ a, o.field "approvals" = some (.nat a) ∧
      a / pow2 i % 2 = 0 ∧ n.field "approvals" = some (.nat (a + pow2 i)) := by
  obtain ⟨h1, h23⟩ := andT_true h
  obtain ⟨h2, h3⟩ := andT_true h23
  refine ⟨deq_field_lit (d := rq) (i := 1) rfl h3, ?_⟩
  obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok h1
  obtain ⟨b, z, rfl, rfl, hd⟩ := primEval_eq_bool hp
  cases bigStep_nat_inv hv
  simp at hd; subst hd
  obtain ⟨a, ha, hb⟩ := bit_field (d := o) (i := 3) rfl hu
  simp only [Val.nat.injEq] at hb
  obtain ⟨u', v', hu', hv', hp'⟩ := bigStep_prim_ok h2
  obtain ⟨c, e, rfl, rfl, hd'⟩ := primEval_eq_bool hp'
  simp at hd'; subst hd'
  obtain ⟨x1, y1, hx1, hy1, hp1⟩ := bigStep_prim_ok hv'
  obtain ⟨a1, b1, rfl, rfl, hv1⟩ := primEval_add_ok hp1
  cases bigStep_nat_inv hy1
  have ha1 := getVar_nat (d := o) (i := 3) rfl hx1
  rw [ha] at ha1; cases ha1
  cases hv1
  exact ⟨a, ha, hb.symm, getVar_nat (d := n) (i := 2) rfl hu'⟩

theorem le_lit_field {i : Nat} {d : Data} {f : Label} {k : Nat} {t : Term} (hi : env[i]? = some d.toVal)
    (ht : t = .get (.var i) f) (h : BigStep lib env (.prim .lt t (natT k)) (.ok (.bool true))) :
    ∃ a, d.field f = some (.nat a) ∧ a < k := by
  subst ht
  obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok h
  obtain ⟨a, b, rfl, rfl, hab⟩ := primEval_lt_true hp
  cases bigStep_nat_inv hy
  exact ⟨a, getVar_nat hi hx, hab⟩

/-- Two natural fields compared `true` by `eq`: they are the same natural. -/
theorem eq_fields_true {i j : Nat} {d e : Data} {f g : Label} (hi : env[i]? = some d.toVal)
    (hj : env[j]? = some e.toVal)
    (h : BigStep lib env (.prim .eq (.get (.var i) f) (.get (.var j) g)) (.ok (.bool true))) :
    ∃ m, d.field f = some (.nat m) ∧ e.field g = some (.nat m) := by
  obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok h
  obtain ⟨a, b, rfl, rfl, hd⟩ := primEval_eq_bool hp
  simp at hd; subst hd
  exact ⟨a, getVar_nat hi hx, getVar_nat hj hy⟩

/-- The quorum's threshold at clause depth 1: `k` set bits among the old approvals. -/
theorem quorate_true {k cnt : Nat} {x rq n o : Data} {E : Env} (hc : 0 < cnt)
    (h : BigStep lib (x.toVal :: LawEnv rq n o E)
      (.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") cnt)) (.ok (.bool true))) :
    ∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a cnt := by
  obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok h
  obtain ⟨a, b, rfl, rfl, hab⟩ := primEval_le_true hp
  cases bigStep_nat_inv hu
  obtain ⟨c, hc', rfl⟩ := popcount_field (d := o) (i := 3) rfl hc hv
  exact ⟨c, hc', hab⟩

theorem member_true {ms : List ByteArray} {x rq n o : Data} {E : Env}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E) (isMember ms ⟨1⟩) (.ok (.bool true))) :
    ∃ m ∈ ms, rq.field "agent" = some (.digest m) :=
  isListed (a := ⟨1⟩) rfl h

/-- **Quorum at birth**: an admitted birth starts with no approvals. -/
theorem quorum_birth_empty {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {rq n o x : Data}
   
    (h : Admits lib (quorumLaw S T ms k g) rq n o)
    (ho : rq.field "occasion" = some (.inj "birth" x)) :
    n.field "approvals" = some (.nat 0) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [quorumLaw, lawOf, lawBody] at hb
  have hc := allOf_ok (lawCase_birth rfl ho hb) _ (List.mem_singleton_self _)
  exact eq_field_lit (d := n) (i := 2) rfl hc

/-- **Quorum at a relaw**: an admitted replacement of the laws is by a member, with `k` approvals
of a proposal to replace them by EXACTLY the incoming laws. -/
theorem quorum_relaw_needs_k {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {rq n o x : Data}
   
    (h : Admits lib (quorumLaw S T ms k g) rq n o)
    (ho : rq.field "occasion" = some (.inj "relaw" x)) :
    (∃ m ∈ ms, rq.field "agent" = some (.digest m)) ∧
    (∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a ms.length) ∧
    ∃ s, o.field "proposal" = some (.inj "laws" (.bytes s)) ∧ x = .bytes s := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [quorumLaw, lawOf, lawBody] at hb
  obtain ⟨hg, hr⟩ := guards_ok (lawCase_relaw rfl ho hb)
  have hm := member_true (hg _ (List.mem_singleton_self _))
  have hpos : 0 < ms.length := by
    obtain ⟨m, hm', _⟩ := hm; exact List.length_pos_of_mem hm'
  exact ⟨hm, quorate_true hpos (allOf_ok hr _ (List.mem_cons_self ..)),
    proposedLaws_true (allOf_ok hr _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

/-- **Quorum at its adoption is fresh**: the quorum can be added over a state only if that state
holds no approvals, so every approval it ever counts is one it judged (`quorum_change`'s approve
case). Approvals written under the previous laws would prove nothing about the members. -/
theorem quorum_adopt_fresh {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {rq n o x : Data}
    (h : Admits lib (quorumLaw S T ms k g) rq n o)
    (ho : rq.field "occasion" = some (.inj "adopt" x)) :
    n.field "approvals" = some (.nat 0) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [quorumLaw, lawOf, lawBody] at hb
  have hc := allOf_ok (lawCase_adopt rfl ho hb) _ (List.mem_singleton_self _)
  exact eq_field_lit (d := n) (i := 2) rfl hc

/-- **A quorum admits no retirement**: a quorum object is not ended by one signer; the quorum may
relaw it first (`quorum_relaw_needs_k`) to laws that admit one. -/
theorem quorum_retire_refused {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {rq n o x : Data}
    (ho : rq.field "occasion" = some (.inj "retire" x)) :
    ¬ Admits lib (quorumLaw S T ms k g) rq n o := by
  rintro ⟨cenv, w, hb⟩
  simp only [quorumLaw, lawOf, lawBody] at hb
  exact refusedT_not_ok (lawCase_retire rfl ho hb)

/-- **Quorum on a change** (a write or an invoke): the act is by a member, the new approvals are a
mask over the members, and it is exactly one of
* a COMMIT: the guarded field changes, to the value the old proposal named, with `k` approvals,
  and the approvals reset;
* a PROPOSAL: the guarded field is kept, the proposal changes, and the approvals reset;
* a NO-OP on what the law watches: field, proposal and approvals all kept;
* an APPROVAL: field and proposal kept, and the signer, member `i`, adds its own bit `i`, which
  was unset. -/
theorem quorum_change {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {rq n o x : Data}
    {ℓ : Label}
    (h : Admits lib (quorumLaw S T ms k g) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hl : ℓ = "write" ∨ ℓ = "invoke") :
    (∃ m ∈ ms, rq.field "agent" = some (.digest m)) ∧
    (∃ b, n.field "approvals" = some (.nat b) ∧ b < pow2 ms.length) ∧
    ∃ ng og, n.field g = some ng ∧ o.field g = some og ∧
      ((ng ≠ og ∧ (∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a ms.length) ∧
          o.field "proposal" = some (.inj "set" ng) ∧ n.field "approvals" = some (.nat 0)) ∨
       (ng = og ∧ ∃ np op, n.field "proposal" = some np ∧ o.field "proposal" = some op ∧
          ((np ≠ op ∧ n.field "approvals" = some (.nat 0)) ∨
           (np = op ∧ ∃ a, n.field "approvals" = some (.nat a) ∧ o.field "approvals" = some (.nat a)) ∨
           (np = op ∧ ∃ i m a, ms[i]? = some m ∧ rq.field "agent" = some (.digest m) ∧
              o.field "approvals" = some (.nat a) ∧ a / pow2 i % 2 = 0 ∧
              n.field "approvals" = some (.nat (a + pow2 i)))))) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [quorumLaw, lawOf, lawBody] at hb
  obtain ⟨y, hy⟩ := lawCase_change rfl ho
    (by rcases hl with rfl | rfl; exact .inl ⟨x, rfl⟩; exact .inr ⟨x, rfl⟩) hb
  obtain ⟨hg, hrest⟩ := guards_ok hy
  have hm := member_true (hg _ (List.mem_cons_self ..))
  have hrange := le_lit_field (d := n) (i := 2) rfl rfl
    (hg _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine ⟨hm, hrange, ?_⟩
  rcases bigStep_ite_ok hrest with ⟨hc1, hcommit⟩ | ⟨hc1, hnot⟩
  · obtain ⟨ng, og, hn, ho', hiff⟩ := eqAt_fields (d := n) (e := o) rfl rfl (notT_true hc1)
    have hpos : 0 < ms.length := by
      obtain ⟨m, hm', _⟩ := hm; exact List.length_pos_of_mem hm'
    have hq := quorate_true hpos (allOf_ok hcommit _ (List.mem_cons_self ..))
    obtain ⟨y', hp, hy'⟩ := proposedSet_true
      (allOf_ok hcommit _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hreset := eq_field_lit (d := n) (i := 2) rfl
      (allOf_ok hcommit _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    rw [hn] at hy'; cases hy'
    exact ⟨ng, og, hn, ho', .inl ⟨fun he => by simpa using hiff.1 he, hq, hp, hreset⟩⟩
  · obtain ⟨ng, og, hn, ho', hiff⟩ := eqAt_fields (d := n) (e := o) rfl rfl (notT_false hc1)
    have hng := hiff.2 rfl
    refine ⟨ng, og, hn, ho', .inr ⟨hng, ?_⟩⟩
    rcases bigStep_ite_ok hnot with ⟨hs, hprop⟩ | ⟨hs, hnext⟩
    · obtain ⟨np, op, hnp, hop, hpiff⟩ := sameProposal_bool (notT_true hs)
      have hreset := eq_field_lit (d := n) (i := 2) rfl (allOf_ok hprop _ (List.mem_singleton_self _))
      exact ⟨np, op, hnp, hop, .inl ⟨fun he => by simpa using hpiff.1 he, hreset⟩⟩
    · obtain ⟨np, op, hnp, hop, hpiff⟩ := sameProposal_bool (notT_false hs)
      have hsame := hpiff.2 rfl
      refine ⟨np, op, hnp, hop, .inr ?_⟩
      rcases bigStep_ite_ok hnext with ⟨he, _⟩ | ⟨_, hguard⟩
      · exact .inl ⟨hsame, eq_fields_true (d := n) (e := o) rfl rfl he⟩
      · obtain ⟨hany, _⟩ := guard_ok hguard
        obtain ⟨c, hc, hct⟩ := anyOf_true hany
        obtain ⟨⟨m, i⟩, hmi, rfl⟩ := List.mem_map.1 hc
        obtain ⟨hagent, a, ha, hbit, hnew⟩ := approvalBy_true hct
        exact .inr ⟨hsame, i, m, a, List.mem_zipIdx_iff_getElem?.1 hmi, hagent, ha, hbit, hnew⟩

/-- **The commit needs k** (the assembly's `quorum_change_needs_k`): an admitted write or invoke
that changes the guarded field sets it to exactly what the old proposal named, with at least `k`
of the members' approvals, and resets them. -/
theorem quorum_change_needs_k {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label}
    {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (quorumLaw S T ms k g) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hl : ℓ = "write" ∨ ℓ = "invoke")
    (hchg : n.field g ≠ o.field g) :
    ∃ ng, n.field g = some ng ∧
      (∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ popcountNat a ms.length) ∧
      o.field "proposal" = some (.inj "set" ng) ∧ n.field "approvals" = some (.nat 0) := by
  obtain ⟨_, _, ng, og, hn, ho', hcase⟩ := quorum_change h ho hl
  rcases hcase with ⟨_, hq, hp, hr⟩ | ⟨he, _⟩
  · exact ⟨ng, hn, hq, hp, hr⟩
  · exact (hchg (by rw [hn, ho', he])).elim

/-! ## Windowed -/

/-- A natural field of the request divided by a literal. -/
theorem div_req_field {i W v : Nat} {d : Data} {f : Label} (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (.prim .div (.get (.var i) f) (natT W)) (.ok (.nat v))) :
    ∃ a, d.field f = some (.nat a) ∧ v = a / W := by
  obtain ⟨x, y, hx, hy, hp⟩ := bigStep_prim_ok h
  obtain ⟨a, b, rfl, rfl, hv⟩ := primEval_div_ok hp
  cases bigStep_nat_inv hy
  cases hv
  exact ⟨a, getVar_nat hi hx, rfl⟩

/-- The window facts at clause depth 1: the call's window lies in one epoch of width `W`, and the
new state's epoch is it. -/
theorem inOneEpoch_true {W : Nat} {x rq n o : Data} {E : Env}
    (h1 : BigStep lib (x.toVal :: LawEnv rq n o E)
      (.prim .eq (.prim .div ((⟨1⟩ : At).reqF "validUntil") (natT W)) (.prim .div ((⟨1⟩ : At).reqF "notBefore") (natT W)))
      (.ok (.bool true)))
    (h2 : BigStep lib (x.toVal :: LawEnv rq n o E)
      (.prim .eq ((⟨1⟩ : At).newF "epoch") (.prim .div ((⟨1⟩ : At).reqF "notBefore") (natT W)))
      (.ok (.bool true))) :
    ∃ nb vu, rq.field "notBefore" = some (.nat nb) ∧ rq.field "validUntil" = some (.nat vu) ∧
      vu / W = nb / W ∧ n.field "epoch" = some (.nat (nb / W)) := by
  obtain ⟨x1, y1, hx1, hy1, hp1⟩ := bigStep_prim_ok h1
  obtain ⟨a, b, rfl, rfl, hd1⟩ := primEval_eq_bool hp1
  simp at hd1; subst hd1
  obtain ⟨vu, hvu, rfl⟩ := div_req_field (d := rq) (i := 1) rfl hx1
  obtain ⟨nb, hnb, he⟩ := div_req_field (d := rq) (i := 1) rfl hy1
  obtain ⟨x2, y2, hx2, hy2, hp2⟩ := bigStep_prim_ok h2
  obtain ⟨c, e, rfl, rfl, hd2⟩ := primEval_eq_bool hp2
  simp at hd2; subst hd2
  obtain ⟨nb', hnb', he'⟩ := div_req_field (d := rq) (i := 1) rfl hy2
  rw [hnb] at hnb'; cases hnb'
  exact ⟨nb, vu, hnb, hvu, he, by rw [← he']; exact getVar_nat (d := n) (i := 2) rfl hx2⟩

/-- What `windowed`'s increment means: `0` when the guarded field is kept, `1` when it changes. -/
theorem inc_val {T : Ty} {g : Label} {v : Nat} {x rq n o : Data} {E : Env}
    (h : BigStep lib (x.toVal :: LawEnv rq n o E)
      (.ite (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)) (natT 0) (natT 1)) (.ok (.nat v))) :
    (v = 0 ∧ n.field g = o.field g ∧ (n.field g).isSome) ∨ (v = 1 ∧ n.field g ≠ o.field g) := by
  rcases bigStep_ite_ok h with ⟨hc, hv⟩ | ⟨hc, hv⟩
  · cases bigStep_nat_inv hv
    obtain ⟨a, b, ha, hb, hiff⟩ := eqAt_fields (d := n) (e := o) rfl rfl hc
    exact .inl ⟨rfl, by rw [ha, hb, hiff.2 rfl], by simp [ha]⟩
  · cases bigStep_nat_inv hv
    obtain ⟨a, b, ha, hb, hiff⟩ := eqAt_fields (d := n) (e := o) rfl rfl hc
    exact .inr ⟨rfl, by rw [ha, hb]; intro he; simpa using hiff.1 (Option.some.inj he)⟩

/-- **Windowed lands in the call's epoch** (the assembly's `windowed_lands_in_epoch`): an admitted
birth, adoption, write or invoke was signed for a window inside one epoch of width `W`, and the new state's
epoch is that epoch. Since `World.admit` lands the Turn at a height inside the signed window, the
Turn lands in the epoch the state records. -/
theorem windowed_lands_in_epoch {S T : Ty} {W limit : Nat} {g : Label} {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (windowedLaw S T W limit g) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x))
    (hl : ℓ = "birth" ∨ ℓ = "adopt" ∨ ℓ = "write" ∨ ℓ = "invoke") :
    ∃ nb vu, rq.field "notBefore" = some (.nat nb) ∧ rq.field "validUntil" = some (.nat vu) ∧
      vu / W = nb / W ∧ n.field "epoch" = some (.nat (nb / W)) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [windowedLaw, lawOf, lawBody] at hb
  rcases hl with rfl | rfl | hl
  · obtain ⟨hg, _⟩ := guards_ok (lawCase_birth rfl ho hb)
    exact inOneEpoch_true (hg _ (List.mem_cons_self ..)) (hg _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · obtain ⟨hg, _⟩ := guards_ok (lawCase_adopt rfl ho hb)
    exact inOneEpoch_true (hg _ (List.mem_cons_self ..)) (hg _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · obtain ⟨y, hy⟩ := lawCase_change rfl ho
      (by rcases hl with rfl | rfl; exact .inl ⟨x, rfl⟩; exact .inr ⟨x, rfl⟩) hb
    obtain ⟨hg, _⟩ := guards_ok hy
    exact inOneEpoch_true (hg _ (List.mem_cons_self ..)) (hg _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- **Windowed starts at zero**: an admitted birth or adoption has `count = 0`, the base case of
"at most `limit` changes per epoch" (`windowed_counts` is its step). -/
theorem windowed_fresh {S T : Ty} {W limit : Nat} {g : Label} {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (windowedLaw S T W limit g) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hl : ℓ = "birth" ∨ ℓ = "adopt") :
    n.field "count" = some (.nat 0) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [windowedLaw, lawOf, lawBody] at hb
  rcases hl with rfl | rfl
  · obtain ⟨_, hr⟩ := guards_ok (lawCase_birth rfl ho hb)
    exact eq_field_lit (d := n) (i := 2) rfl (allOf_ok hr _ (List.mem_singleton_self _))
  · obtain ⟨_, hr⟩ := guards_ok (lawCase_adopt rfl ho hb)
    exact eq_field_lit (d := n) (i := 2) rfl (allOf_ok hr _ (List.mem_singleton_self _))

/-- **Windowed counts**: in an admitted write or invoke, the new `count` is the old one plus one
for a change of `guarded` (and at most `limit`) within the old epoch, or restarts at that one
change in a later epoch, at most `limit` either way. A per-STEP fact: "at most `limit` changes
per epoch" is its induction over a history, with KERNEL's admission landing each Turn inside its
signed window: `Lang.Proofs.StdChain.windowed_per_epoch`. -/
theorem windowed_counts {S T : Ty} {W limit : Nat} {g : Label} {rq n o x : Data} {ℓ : Label}
    (h : Admits lib (windowedLaw S T W limit g) rq n o)
    (ho : rq.field "occasion" = some (.inj ℓ x)) (hl : ℓ = "write" ∨ ℓ = "invoke") :
    ∃ c inc, n.field "count" = some (.nat c) ∧
      ((inc = 0 ∧ n.field g = o.field g) ∨ (inc = 1 ∧ n.field g ≠ o.field g)) ∧
      ((∃ e c0, o.field "epoch" = some (.nat e) ∧ n.field "epoch" = some (.nat e) ∧
          o.field "count" = some (.nat c0) ∧ c = c0 + inc ∧ c ≤ limit) ∨
       (∃ e e', o.field "epoch" = some (.nat e) ∧ n.field "epoch" = some (.nat e') ∧ e < e' ∧ c = inc ∧
          c ≤ limit)) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [windowedLaw, lawOf, lawBody] at hb
  obtain ⟨y, hy⟩ := lawCase_change rfl ho
    (by rcases hl with rfl | rfl; exact .inl ⟨x, rfl⟩; exact .inr ⟨x, rfl⟩) hb
  obtain ⟨_, hrest⟩ := guards_ok hy
  have hinc : ∀ v, BigStep lib (y.toVal :: LawEnv rq n o cenv)
      (.ite (eqAt T ((⟨1⟩ : At).newF g) ((⟨1⟩ : At).oldF g)) (natT 0) (natT 1)) (.ok (.nat v)) →
      (v = 0 ∧ n.field g = o.field g) ∨ (v = 1 ∧ n.field g ≠ o.field g) := fun v hv =>
    (inc_val hv).elim (fun h => .inl ⟨h.1, h.2.1⟩) .inr
  rcases bigStep_ite_ok hrest with ⟨he, hsame⟩ | ⟨_, hnext⟩
  · obtain ⟨e, hne, hoe⟩ := eq_fields_true (d := n) (e := o) rfl rfl he
    have h1 := allOf_ok hsame _ (List.mem_cons_self ..)
    have h2 := allOf_ok hsame _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok h1
    obtain ⟨c, s', rfl, rfl, hd⟩ := primEval_eq_bool hp
    simp at hd; subst hd
    obtain ⟨x1, y1, hx1, hy1, hp1⟩ := bigStep_prim_ok hv
    obtain ⟨c0, i, rfl, rfl, hv1⟩ := primEval_add_ok hp1
    cases hv1
    obtain ⟨u2, v2, hu2, hv2, hp2⟩ := bigStep_prim_ok h2
    obtain ⟨c', l', rfl, rfl, hle⟩ := primEval_le_true hp2
    cases bigStep_nat_inv hv2
    have hc := getVar_nat (d := n) (i := 2) rfl hu
    have hc' := getVar_nat (d := n) (i := 2) rfl hu2
    rw [hc] at hc'; cases hc'
    exact ⟨_, i, hc, hinc i hy1,
      .inl ⟨e, c0, hoe, hne, getVar_nat (d := o) (i := 3) rfl hx1, rfl, hle⟩⟩
  · have h1 := allOf_ok hnext _ (List.mem_cons_self ..)
    have h2 := allOf_ok hnext _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := allOf_ok hnext _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok h1
    obtain ⟨e, e', rfl, rfl, hlt⟩ := primEval_lt_true hp
    obtain ⟨u2, v2, hu2, hv2, hp2⟩ := bigStep_prim_ok h2
    obtain ⟨c, i, rfl, rfl, hd⟩ := primEval_eq_bool hp2
    simp at hd; subst hd
    obtain ⟨u3, v3, hu3, hv3, hp3⟩ := bigStep_prim_ok h3
    obtain ⟨c', l', rfl, rfl, hle⟩ := primEval_le_true hp3
    cases bigStep_nat_inv hv3
    have hc := getVar_nat (d := n) (i := 2) rfl hu2
    have hc' := getVar_nat (d := n) (i := 2) rfl hu3
    rw [hc] at hc'; cases hc'
    exact ⟨c, c, hc, hinc c hv2,
      .inr ⟨e, e', getVar_nat (d := o) (i := 3) rfl hu, getVar_nat (d := n) (i := 2) rfl hv, hlt, rfl, hle⟩⟩

/-! ## The runner: what `runLaw` admitting means -/

/-- Applying a term whose meaning is the closure of `λ new. λ req. b` runs `b` with the request,
new and old values bound above the closure's environment. -/
theorem applyAt_of_fn {f b : Term} {B C : Ty} {c0 : Env} {rv nv ov : Val} {E : Env} {v : Val}
    (hf : BigStep lib (rv :: nv :: ov :: E) f (.ok (.clo (.lam B (.lam C b)) c0)))
    (h : BigStep lib (rv :: nv :: ov :: E) (applyAt f) (.ok v)) :
    BigStep lib (rv :: nv :: ov :: c0) b (.ok v) := by
  obtain ⟨b3, c3, w3, h3f, h3a, h3b⟩ := bigStep_app_ok h
  obtain ⟨b2, c2, w2, h2f, h2a, h2b⟩ := bigStep_app_ok h3f
  obtain ⟨b1, c1, w1, h1f, h1a, h1b⟩ := bigStep_app_ok h2f
  cases bigStep_deterministic hf h1f
  have hv1 := bigStep_var_ok h1a; simp at hv1; subst hv1
  cases h1b
  have hv2 := bigStep_var_ok h2a; simp at hv2; subst hv2
  cases h2b
  have hv3 := bigStep_var_ok h3a; simp at hv3; subst hv3
  exact h3b

theorem find_suspend {ℓ : Label} {t : Term} {e : Env} :
    ∀ {fs : List (Label × Term)}, Row.find? ℓ fs = some t → Row.find? ℓ (suspend e fs) = some (t, e)
  | [], h => by simp [Row.find?] at h
  | (k, u) :: fs, h => by
    simp only [suspend, List.map, Row.find?] at h ⊢
    split at h
    · cases h; rw [if_pos (by assumption)]
    · rw [if_neg (by assumption)]; exact find_suspend h

/-- Extracting at a sum type yields an injection only from an injection with that label. -/
theorem extract_sum_inj {m : Machine} {row : List (Label × Ty)} {fuel : Nat} {v : Val} {ℓ : Label}
    {d : Data} {f : Nat} (h : m.extract (.sum row) fuel v = .ok (.inj ℓ d, f)) : ∃ w, v = .inj ℓ w := by
  cases v with
  | inj ℓ' w =>
    simp only [Machine.extract] at h
    split at h
    · simp at h; obtain ⟨⟨rfl, _⟩, _⟩ := h; exact ⟨w, rfl⟩
    · cases h
  | _ => simp [Machine.extract] at h

/-- An admitting run of a law whose meaning is the closure `clo (λ new. λ req. b) c0` gives its
body's `ok` meaning. -/
theorem runLaw_ok_body {t b : Term} {B C : Ty} {c0 : Env} {o n r : Data}
    (hf : BigStep lib [r.toVal, n.toVal, o.toVal] t (.ok (.clo (.lam B (.lam C b)) c0)))
    (h : runLaw lib t o n r = .ok (.ok ())) :
    ∃ cenv w, BigStep lib (r.toVal :: n.toVal :: o.toVal :: cenv) b (.ok (.inj "ok" w)) := by
  unfold runLaw at h
  split at h
  · cases h
  · rename_i v used hrun
    split at h
    · rename_i d f hx
      obtain ⟨w, rfl⟩ := extract_sum_inj hx
      exact ⟨_, w, applyAt_of_fn hf (run_bigStep hrun)⟩
    all_goals simp at h

/-- **A test's run is the meaning.** `runLaw` admitting a closed stdlib law (`λ λ λ b`) means the
law admits, in the sense every spec theorem here assumes. -/
theorem runLaw_admits {A B C : Ty} {b : Term} {o n r : Data}
    (h : runLaw lib (.lam A (.lam B (.lam C b))) o n r = .ok (.ok ())) :
    Admits lib (.lam A (.lam B (.lam C b))) r n o :=
  runLaw_ok_body .lam h

/-- **The receiver's run is the meaning.** `runLaw` admitting field `ℓ` of the closure body `g`
(how `Program.judgeOne` runs a law), where that body is a record literal whose field `ℓ` is a
`λ λ λ` law, means that law admits. -/
theorem runLaw_ref_admits {g : Nat} {fs : List (Label × Term)} {ℓ : Label} {A B C : Ty} {b : Term}
    {o n r : Data} (hg : lib[g]? = some (.record fs)) (hℓ : Row.find? ℓ fs = some (.lam A (.lam B (.lam C b))))
    (h : runLaw lib (.get (.ref g) ℓ) o n r = .ok (.ok ())) :
    Admits lib (.lam A (.lam B (.lam C b))) r n o :=
  runLaw_ok_body (.get (.ref hg .record) (.field (find_suspend hℓ) .lam)) h

/-! ## Machines -/

theorem find_isState {ℓ s : Label} {body : Term} :
    ∀ {L : List (Label × Unit)}, Row.find? ℓ (L.map fun (x, _) => (x, Term.bool (decide (x = s)))) = some body →
      body = .bool (decide (ℓ = s))
  | [], h => by simp [Row.find?] at h
  | (k, _) :: L, h => by
    simp only [List.map, Row.find?] at h
    split at h
    · rename_i hk; cases h; subst hk; rfl
    · exact find_isState h

/-- `isState states (get (var i) f) s` means the field is the state `s`. -/
theorem isState_true {states : List Label} {i : Nat} {d : Data} {f s : Label}
    (hi : env[i]? = some d.toVal)
    (h : BigStep lib env (isState states (.get (.var i) f) s) (.ok (.bool true))) :
    ∃ y, d.field f = some (.inj s y) := by
  obtain ⟨ℓ, y, body, hd, hf, hb⟩ := case_field hi h
  have := find_isState hf; subst this
  have hv := bigStep_bool_inv hb
  simp at hv; subst hv
  exact ⟨y, hd⟩

/-- **A machine starts at its initial state.** -/
theorem machine_birth {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (h : Admits lib (machineLaw S f states initial edges) rq n o)
    (ho : rq.field "occasion" = some (.inj "birth" x)) : ∃ y, n.field f = some (.inj initial y) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  exact isState_true (d := n) (i := 2) rfl (allOf_ok hbody _ (List.mem_singleton_self _))

/-- **A machine is adopted only at its initial state**: added over an existing state, the field must
already be `initial`, as at a birth. -/
theorem machine_adopt {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (h : Admits lib (machineLaw S f states initial edges) rq n o)
    (ho : rq.field "occasion" = some (.inj "adopt" x)) : ∃ y, n.field f = some (.inj initial y) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  exact isState_true (d := n) (i := 2) rfl (allOf_ok hbody _ (List.mem_singleton_self _))

/-- **A machine moves only along an edge, by that edge's method.** An admitted invoke of method
`m` (the occasion's payload) moved `f` from `a` to `b` with `(a, m, b)` an edge. -/
theorem machine_invoke {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (h : Admits lib (machineLaw S f states initial edges) rq n o)
    (ho : rq.field "occasion" = some (.inj "invoke" x)) :
    ∃ a m b, (a, m, b) ∈ edges ∧ x = .nat m ∧ (∃ y, o.field f = some (.inj a y)) ∧
      ∃ y, n.field f = some (.inj b y) := by
  obtain ⟨cenv, w, hb⟩ := h
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  obtain ⟨c, hc, hct⟩ := anyOf_true (allOf_ok hbody _ (List.mem_singleton_self _))
  obtain ⟨⟨a, m, b⟩, he, rfl⟩ := List.mem_map.1 hc
  obtain ⟨hm, hab⟩ := andT_true hct
  obtain ⟨ha, hb'⟩ := andT_true hab
  obtain ⟨u, v, hu, hv, hp⟩ := bigStep_prim_ok hm
  obtain ⟨k, k', rfl, rfl, hd⟩ := primEval_eq_bool hp
  cases bigStep_nat_inv hv
  simp at hd; subst hd
  have hx := bigStep_var_ok hu
  simp at hx
  exact ⟨a, k, b, he, Data.toVal_nat hx, isState_true (d := o) (i := 3) rfl ha,
    isState_true (d := n) (i := 2) rfl hb'⟩

/-- **A machine admits no write.** -/
theorem machine_write_refused {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (ho : rq.field "occasion" = some (.inj "write" x)) :
    ¬ Admits lib (machineLaw S f states initial edges) rq n o := by
  rintro ⟨cenv, w, hb⟩
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  exact refusedT_not_ok hbody

/-- **A machine admits no replacement of laws.** -/
theorem machine_relaw_refused {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (ho : rq.field "occasion" = some (.inj "relaw" x)) :
    ¬ Admits lib (machineLaw S f states initial edges) rq n o := by
  rintro ⟨cenv, w, hb⟩
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  exact refusedT_not_ok hbody

/-- **A machine admits no retirement**: a machine object is permanent. -/
theorem machine_retire_refused {S : Ty} {f : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)} {rq n o x : Data}
    (ho : rq.field "occasion" = some (.inj "retire" x)) :
    ¬ Admits lib (machineLaw S f states initial edges) rq n o := by
  rintro ⟨cenv, w, hb⟩
  simp only [machineLaw, lawOf6, lawBody] at hb
  obtain ⟨body, hf, hbody⟩ := lawCase6_arm rfl ho hb
  simp [Row.find?] at hf; subst hf
  exact refusedT_not_ok hbody

/-! ## The checked generators -/

theorem need_ok {c : Bool} {e : StdRefusal} (h : need c e = .ok ()) : c = true := by
  unfold need at h; split at h <;> simp_all

/-- What `quorum` accepting its parameters guarantees: the law is `quorumLaw` (what every quorum
theorem is about) over DISTINCT members with `1 ≤ k ≤ members`, so every approval bit belongs to a distinct member. -/
theorem quorum_ok {S T : Ty} {ms : List ByteArray} {k : Nat} {g : Label} {t : Term}
    (h : quorum S T ms k g = .ok t) :
    t = quorumLaw S T ms k g ∧ ms.Nodup ∧ 1 ≤ k ∧ k ≤ ms.length ∧ ms.length ≤ membersMax := by
  unfold quorum need at h
  by_cases h1 : ms.length ≤ membersMax
  · by_cases h2 : ms.Nodup
    · by_cases h3 : 1 ≤ k ∧ k ≤ ms.length
      · simp only [h1, h2, h3, decide_true, Bool.and_self, if_true] at h
        exact ⟨(Except.ok.inj h).symm, h2, h3.1, h3.2, h1⟩
      · simp only [h1, h2, decide_true, if_true] at h
        rw [if_neg (by simpa using h3)] at h
        cases h
    · simp only [h1, decide_true, if_true] at h
      rw [if_neg (by simpa using h2)] at h
      cases h
  · rw [if_neg (by simpa using h1)] at h
    cases h

theorem allowlist_ok {S : Ty} {ids : List ByteArray} {t : Term} (h : allowlist S ids = .ok t) :
    t = allowlistLaw S ids ∧ ids.length ≤ idsMax := by
  unfold allowlist need at h
  by_cases h1 : ids.length ≤ idsMax
  · simp only [h1, decide_true, if_true] at h
    exact ⟨(Except.ok.inj h).symm, h1⟩
  · rw [if_neg (by simpa using h1)] at h
    cases h

theorem mapM_length {α β ε : Type} {f : α → Except ε β} : ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
    r.length = l.length
  | [], r, h => by simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hf : f a with
    | error e => simp [hf, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [hf, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hf, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [mapM_length hl]

/-- What `machine` accepting its parameters guarantees: the law is `machineLaw` over resolved edges,
one per named edge, at most `edgesMax` of them, over at most `Wire.rowMax` distinct states. -/
theorem machine_ok {S : Ty} {f : Label} {states : List Label} {initial : Label} {methods : List Label}
    {edges : List (Label × Label × Label)} {t : Term} (h : machine S f states initial methods edges = .ok t) :
    ∃ es, t = machineLaw S f states initial es ∧ es.length = edges.length ∧ edges.length ≤ edgesMax ∧
      states.length ≤ Wire.rowMax ∧ states.Nodup := by
  unfold machine need at h
  by_cases h1 : states.Nodup
  · by_cases h2 : states.length ≤ Wire.rowMax
    · by_cases h3 : edges.length ≤ edgesMax
      · by_cases h4 : states.contains initial = true
        · simp only [h1, h2, h3, h4, decide_true, if_true, bind, Except.bind, pure, Except.pure] at h
          cases he : resolveEdges states methods edges with
          | error e => rw [he] at h; cases h
          | ok es =>
            rw [he] at h
            exact ⟨es, (Except.ok.inj h).symm, mapM_length he, h3, h2, h1⟩
        · simp only [h1, h2, h3, decide_true, if_true, bind, Except.bind] at h
          rw [if_neg h4] at h; cases h
      · simp only [h1, h2, decide_true, if_true, bind, Except.bind] at h
        rw [if_neg (by simpa using h3)] at h; cases h
    · simp only [h1, decide_true, if_true, bind, Except.bind] at h
      rw [if_neg (by simpa using h2)] at h; cases h
  · rw [if_neg (by simpa using h1)] at h; cases h

/-- What `stepTo` accepting its parameters guarantees: the method is `stepLaw` at the method's index
over the resolved edges, and no two of them leave one state by one method. -/
theorem stepTo_ok {S : Ty} {f : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} (h : stepTo S f states methods m edges = .ok t) :
    ∃ i es, methodIndex methods m = some i ∧ resolveEdges states methods edges = .ok es ∧
      (es.map fun (x, k, _) => (x, k)).Nodup ∧ t = stepLaw S f states i es := by
  unfold stepTo need at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  rename_i i hi _ es hes _ _ hnd
  refine ⟨i, es, hi, hes, ?_, (Except.ok.inj h).symm⟩
  split at hnd
  · exact of_decide_eq_true ‹_›
  · cases hnd

/-- With no two edges leaving a state by one method, the edge `stepLaw` looks up from state `x` by
method `k` is THE declared edge: every declared edge is the one taken. -/
theorem find_edge_of_nodup : ∀ {es : List (Label × Nat × Label)} {x y : Label} {k : Nat},
    (es.map fun (a, j, _) => (a, j)).Nodup → (x, k, y) ∈ es →
    es.find? (fun (a, j, _) => a = x && j = k) = some (x, k, y)
  | [], _, _, _, _, h => by simp at h
  | (a, j, b) :: es, x, y, k, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · have hne : ¬ (a = x ∧ j = k) := by
        rintro ⟨rfl, rfl⟩
        exact hnd.1 ⟨(a, j, y), h, rfl⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_edge_of_nodup hnd.2 h

/-- **`stepTo` takes every edge it declares** (LANG-43): for a method `stepTo` generates, every
resolved edge `(x, i, y)` of its own method index is where its target lookup (`stepTarget`, the one
`stepLaw` uses) moves `x`. So
the machine law (`machineLaw`, which admits a move along any declared edge) and the generated method
agree, and the law admits no move that the generated methods cannot make. -/
theorem stepTo_takes_every_edge {S : Ty} {f : Label} {states methods : List Label} {m : Label}
    {edges : List (Label × Label × Label)} {t : Term} (h : stepTo S f states methods m edges = .ok t) :
    ∃ i es, methodIndex methods m = some i ∧ resolveEdges states methods edges = .ok es ∧
      t = stepLaw S f states i es ∧
      ∀ x y, (x, i, y) ∈ es → stepTarget es i x = y := by
  obtain ⟨i, es, hi, hes, hnd, rfl⟩ := stepTo_ok h
  exact ⟨i, es, hi, hes, rfl, fun x y hm => by simp [stepTarget, find_edge_of_nodup hnd hm]⟩

theorem windowed_ok {S T : Ty} {W limit : Nat} {g : Label} {t : Term}
    (h : windowed S T W limit g = .ok t) : t = windowedLaw S T W limit g ∧ 0 < W := by
  unfold windowed need at h
  by_cases h1 : 0 < W
  · simp only [h1, decide_true, if_true] at h
    exact ⟨(Except.ok.inj h).symm, h1⟩
  · rw [if_neg (by simpa using h1)] at h
    cases h

end Nanodregg.Lang.Std
