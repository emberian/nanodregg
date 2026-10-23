/-
# Lang.Proofs.Receiver — the receiver admitting a stdlib package means its laws' specs

`Lang.Proofs.Std` proves what each stdlib law means when it ADMITS (`Admits`, over `BigStep`). This
module closes the chain from the deployed judge to those statements (LANG-20's named gap):
1. `judgeOne_ok`: `judgeOne` admitting means the closure loaded, both states read at the package's
   state type, and `runLaw` admitted every law label of the package;
2. `load_top`: the closure loaded for a package holds, at the index `load` returns, exactly that
   package, its body relocated (imports or not);
3. `relocate_noRef`: relocation is the identity on a term with no `ref` (`NoRef`), and every stdlib
   law is one (`noRef_quorumLaw`, `noRef_windowedLaw`, `noRef_machineLaw`, `noRef_bounded`,
   `noRef_allowlist`, `noRef_ownerSigns`);
4. `find_of_mem_nodup` + `Row.sort_perm`: a `pkgOf` body's field `ℓ` is the generator's term.
`judgeOne_admits` composes them for any package, a law as loaded (relocated into the closure);
`judgeOne_pkgOf_admits` is its `pkgOf` instance, with distinct labels derived from the receiver's
own load (`load_checked`, `pkgOf_labels_nodup`) and every stdlib law its own relocation. `judgeOne_quorum_change`, `judgeOne_quorum_relaw` and
`judgeOne_machine_invoke` are the spec theorems restated about the receiver's run. They are no longer
about a test's closed term, and "the receiver admitting a Std package means its spec" is now a
theorem instead of a hypothesis.

What is still assumed: the pinned cell holds the package (`readPackage … = .ok`; a cell holding its
bytes does, `readPackage_installed`), and the digest decodes back (`digestOf (bytesOf law) = some
law`, the lawful `Ctx`, LANG-46). A law inherited through a layer's `extend (ref 0)` is not a field
of the layer's own body, so `judgeOne_admits` reaches it only at the super package.
-/
import Lang.Proofs.Std
import Lang.Proofs.Load

namespace Nanodregg.Lang

open Nanodregg.Kernel.Receive

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

theorem judgeOne_ok {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D}
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ∃ L g p o n, load digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩ = .ok (L, g) ∧
      L.pkgs[g]? = some p ∧ readState digestOf (recordRow p.state) old = .ok o ∧
      readState digestOf (recordRow p.state) new = .ok n ∧
      ∀ ℓ ∈ p.laws, runLaw L.lib (.get (.ref g) ℓ) o n (reqData bytesOf r) = .ok (.ok ()) := by
  unfold judgeOne judgeOneWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i v hload
      obtain ⟨L, g⟩ := v
      split at h
      · rename_i p hp
        split at h
        · rename_i o ho
          split at h
          · rename_i n hn
            split at h
            · cases h
            · rename_i u hfor
              refine ⟨L, g, p, o, n, hload, hp, ho, hn, ?_⟩
              refine forIn_yield_ok _ _ _ (fun ℓ u s hs => ?_) hfor
              split at hs <;> simp_all
          · cases h
        · cases h
      · cases h
  · cases h

/-- **A faulting law never admits** (the polarity tooth, PROOF-ENGINEERING Q3: sp over the law).
If law `ℓ` of the package the closure loads faults on the states the judge reads (`runLaw … =
.error f`: ticks, stack, an arithmetic fault; `runLaw_never_stuck` shows that arm is live and is
never `stuck`), the judge refuses the transition. `Admits` is a derivation TO `ok`, and a fault is
none, so a fault is never read as admittance. The tooth: `Std.fault_law` (Lang.Proofs.StdChain) is a law
the checker accepts at `lawTy` whose run faults. -/
theorem fault_never_admits {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D}
    {L : Loaded} {g : Nat} {p : Package} {ℓ : Label} {od nd : Data} {f : Fault}
    (hload : load digestOf look closureDepthMax (bytesOf law) ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p) (hl : ℓ ∈ p.laws)
    (hold : readState digestOf (recordRow p.state) old = .ok od)
    (hnew : readState digestOf (recordRow p.state) new = .ok nd)
    (hf : runLaw L.lib (.get (.ref g) ℓ) od nd (reqData bytesOf r) = .error f) :
    judgeOne bytesOf digestOf look law old new r ≠ .ok () := by
  intro h
  obtain ⟨L', g', p', o', n', hload', hp', ho', hn', hall⟩ := judgeOne_ok bytesOf digestOf h
  rw [hload] at hload'
  cases hload'
  rw [hp] at hp'
  cases hp'
  rw [hold] at ho'
  cases ho'
  rw [hnew] at hn'
  cases hn'
  have hℓ := hall ℓ hl
  rw [hf] at hℓ
  cases hℓ

/-! ## Link 2: a package with no imports loads as itself, at index 0 -/

/-- **What the receiver loads is what the cell holds**: a closure loaded for `law` has, at the index
`load` returns, exactly the package `readPackage` reads from `law`'s cell (imports or not), with its
body relocated. So the readers that resolve on `readPackage`'s copy (`argsOf`, `seedOf`, LANG-22)
and the run that resolves on `load`'s agree on methods, interface and state: they are one package. -/
theorem load_top {look : Pinned D} {law : D} {p : Package} {fuel : Nat} {L : Loaded} {g : Nat}
    (hid : digestOf (bytesOf law) = some law) (hp : readPackage look law = .ok p)
    (h : load digestOf look (fuel + 1) (bytesOf law) ⟨[], [], []⟩ = .ok (L, g)) :
    L.pkgs[g]? = some p ∧ ∃ f, L.lib[g]? = some (p.body.relocate f) := by
  unfold load loadUsing at h
  simp only [indexIn, idOf, hid, hp] at h
  split at h
  · cases h
  · rename_i acc' gis hall
    obtain ⟨⟨hids, hlib, _, _⟩, _, _⟩ := loadAll_inv digestOf look fuel p.imports _ Inv.empty hall
    unfold admitPackage at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, fun i => gis.getD i 0, ?_⟩
          · simp [hids]
          · simp [← hlib, hids]

end

/-! ## Link 3: relocation is the identity on a term with no `ref` -/

mutual
/-- `t` mentions no closure package: relocation cannot change it. -/
def NoRef : Term → Prop
  | .ref _ => False
  | .hole _ σ => NoRefList σ
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .refuse _ _ => True
  | .lam _ b => NoRef b
  | .app f a => NoRef f ∧ NoRef a
  | .fix t => NoRef t
  | .prim _ a b => NoRef a ∧ NoRef b
  | .record fs => NoRefRow fs
  | .get t _ => NoRef t
  | .extend t fs => NoRef t ∧ NoRefRow fs
  | .inj _ _ t => NoRef t
  | .case t fs => NoRef t ∧ NoRefRow fs
  | .ite c a b => NoRef c ∧ NoRef a ∧ NoRef b

def NoRefList : List Term → Prop
  | [] => True
  | t :: ts => NoRef t ∧ NoRefList ts

def NoRefRow : List (Label × Term) → Prop
  | [] => True
  | (_, t) :: fs => NoRef t ∧ NoRefRow fs
end

mutual
theorem relocate_noRef (f : Nat → Nat) : ∀ t : Term, NoRef t → t.relocate f = t
  | .var _, _ | .nat _, _ | .bool _, _ | .bytes _, _ | .digest _, _ | .refuse _ _, _ => rfl
  | .ref _, h => h.elim
  | .lam _ b, h => by simp [Term.relocate, relocate_noRef f b h]
  | .app g a, h => by simp [Term.relocate, relocate_noRef f g h.1, relocate_noRef f a h.2]
  | .fix t, h => by simp [Term.relocate, relocate_noRef f t h]
  | .prim _ a b, h => by simp [Term.relocate, relocate_noRef f a h.1, relocate_noRef f b h.2]
  | .record fs, h => by simp [Term.relocate, relocateRow_noRef f fs h]
  | .get t _, h => by simp [Term.relocate, relocate_noRef f t h]
  | .extend t fs, h => by simp [Term.relocate, relocate_noRef f t h.1, relocateRow_noRef f fs h.2]
  | .inj _ _ t, h => by simp [Term.relocate, relocate_noRef f t h]
  | .case t fs, h => by simp [Term.relocate, relocate_noRef f t h.1, relocateRow_noRef f fs h.2]
  | .ite c a b, h => by
    simp [Term.relocate, relocate_noRef f c h.1, relocate_noRef f a h.2.1, relocate_noRef f b h.2.2]
  | .hole n σ, h => by simp [Term.relocate, relocateList_noRef f σ h]

theorem relocateList_noRef (f : Nat → Nat) : ∀ ts : List Term, NoRefList ts →
    Term.relocateList f ts = ts
  | [], _ => rfl
  | t :: ts, h => by simp [Term.relocateList, relocate_noRef f t h.1, relocateList_noRef f ts h.2]

theorem relocateRow_noRef (f : Nat → Nat) : ∀ fs : List (Label × Term), NoRefRow fs →
    Term.relocateRow f fs = fs
  | [], _ => rfl
  | (_, t) :: fs, h => by simp [Term.relocateRow, relocate_noRef f t h.1, relocateRow_noRef f fs h.2]
end

theorem find_relocateRow (f : Nat → Nat) (ℓ : Label) : ∀ fs : List (Label × Term),
    Row.find? ℓ (Term.relocateRow f fs) = (Row.find? ℓ fs).map (Term.relocate f)
  | [] => rfl
  | (k, t) :: fs => by
    simp only [Term.relocateRow, Row.find?]
    split
    · rfl
    · exact find_relocateRow f ℓ fs

/-! ## Link 4: a `pkgOf` body's field `ℓ` is the generator's term -/

theorem find_of_mem_nodup {α : Type} {ℓ : Label} {t : α} : ∀ {ys : List (Label × α)},
    (ys.map (·.1)).Nodup → (ℓ, t) ∈ ys → Row.find? ℓ ys = some t
  | [], _, h => by cases h
  | (k, a) :: ys, hnd, h => by
    simp only [List.map, List.nodup_cons, List.mem_map] at hnd
    simp only [Row.find?]
    rcases List.mem_cons.1 h with he | h
    · cases he; simp
    · have hk : ℓ ≠ k := fun e => hnd.1 ⟨(ℓ, t), h, e⟩
      simp only [hk, if_false]
      exact find_of_mem_nodup hnd.2 h


/-! ## Every stdlib law mentions no closure package -/

attribute [local simp] NoRef NoRefRow Std.At.reqF Std.At.newF Std.At.oldF Std.At.old Std.At.new
  Std.At.req Std.At.payload Std.At.under Std.natT

namespace NoRefStd
open Std


theorem row_iff : ∀ {fs : List (Label × Term)}, NoRefRow fs ↔ ∀ e ∈ fs, NoRef e.2
  | [] => by simp
  | (_, t) :: fs => by simp [row_iff]

theorem all_nil : ∀ p ∈ ([] : List (Term × String)), NoRef p.1 := fun _ h => nomatch h
theorem all_cons {c : Term} {w : String} {l : List (Term × String)} (hc : NoRef c)
    (hl : ∀ p ∈ l, NoRef p.1) : ∀ p ∈ (c, w) :: l, NoRef p.1 := fun p hp => by
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hc
  · exact hl p hp

theorem okT_ : NoRef okT := by simp [okT]
theorem refusedT_ {w : String} : NoRef (refusedT w) := by simp [refusedT]

theorem guards_ : ∀ {l : List (Term × String)} {t : Term}, (∀ p ∈ l, NoRef p.1) → NoRef t →
    NoRef (guards l t)
  | [], _, _, ht => ht
  | (c, w) :: l, t, hl, ht => by
    simp only [guards, Std.guard, NoRef]
    exact ⟨hl _ (List.mem_cons_self ..), guards_ (fun p hp => hl p (List.mem_cons_of_mem _ hp)) ht,
      refusedT_⟩

theorem allOf_ {l : List (Term × String)} (hl : ∀ p ∈ l, NoRef p.1) : NoRef (allOf l) :=
  guards_ hl okT_

theorem anyOf_ : ∀ {cs : List Term}, (∀ c ∈ cs, NoRef c) → NoRef (anyOf cs)
  | [], _ => by simp [anyOf]
  | c :: cs, h => by
    simp only [anyOf, NoRef]
    exact ⟨h c (List.mem_cons_self ..), trivial, anyOf_ fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem andT_ {a b : Term} (ha : NoRef a) (hb : NoRef b) : NoRef (andT a b) := ⟨ha, hb, trivial⟩
theorem notT_ {a : Term} (ha : NoRef a) : NoRef (notT a) := ⟨ha, trivial, trivial⟩
theorem eqAt_ {T : Ty} {a b : Term} (ha : NoRef a) (hb : NoRef b) : NoRef (eqAt T a b) := by
  unfold eqAt; split
  · exact ⟨ha, hb⟩
  · split <;> exact ⟨ha, hb⟩
theorem bit_ {t : Term} {i : Nat} (ht : NoRef t) : NoRef (bit t i) := ⟨⟨ht, trivial⟩, trivial⟩

theorem popcount_ {t : Term} {cnt : Nat} (ht : NoRef t) : NoRef (popcount t cnt) := by
  unfold popcount
  suffices ∀ (l : List Nat) (acc : Term), NoRef acc →
      NoRef (l.foldl (fun acc i => .prim .add acc (bit t i)) acc) from this _ _ trivial
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons i l ih => exact fun acc h => ih _ ⟨h, bit_ ht⟩

theorem at_ (a : At) : NoRef a.old ∧ NoRef a.new ∧ NoRef a.req ∧ NoRef a.payload :=
  ⟨trivial, trivial, trivial, trivial⟩

theorem lawOf_ {S : Ty} {b ad rl c : At → Term} (hb : NoRef (b ⟨1⟩)) (had : NoRef (ad ⟨1⟩))
    (hrl : NoRef (rl ⟨1⟩)) (hc : NoRef (c ⟨1⟩)) : NoRef (lawOf S b ad rl c) := by
  simp only [lawOf, lawCase, lawCase5, NoRef, NoRefRow]
  exact ⟨trivial, had, hb, hc, hrl, hc, trivial⟩

theorem lawOf5_ {S : Ty} {b ad rl wr iv : At → Term} (hb : NoRef (b ⟨1⟩)) (had : NoRef (ad ⟨1⟩))
    (hrl : NoRef (rl ⟨1⟩)) (hwr : NoRef (wr ⟨1⟩)) (hiv : NoRef (iv ⟨1⟩)) :
    NoRef (lawOf5 S b ad rl wr iv) := by
  simp only [lawOf5, lawCase5, NoRef, NoRefRow]
  exact ⟨trivial, had, hb, hiv, hrl, hwr, trivial⟩

end NoRefStd

open Std NoRefStd in
theorem noRef_ownerSigns (S : Ty) : NoRef (ownerSigns S) := by
  have : NoRef (allOf [(.prim .deq ((⟨1⟩ : At).reqF "agent") ((⟨1⟩ : At).reqF "principal"),
      "not signed by the owner")]) := allOf_ (by simp)
  exact lawOf_ this this this this

open Std NoRefStd in
theorem noRef_allowlist (S : Ty) (ids : List ByteArray) : NoRef (allowlistLaw S ids) := by
  have : NoRef (allOf [(anyOf (ids.map fun i => .prim .deq ((⟨1⟩ : At).reqF "agent") (.digest i)),
      "not on the allowlist")]) := allOf_ (by
        simp only [List.mem_singleton, forall_eq]
        exact anyOf_ (by simp))
  exact lawOf_ this this this this

open Std NoRefStd in
theorem noRef_bounded (S : Ty) (f : Label) (max : Nat) : NoRef (bounded S f max) := by
  have : NoRef (allOf [(.prim .le ((⟨1⟩ : At).newF f) (natT max), s!"{f} over {max}")]) :=
    allOf_ (by simp)
  exact lawOf_ this this okT_ this

open Std NoRefStd in
theorem noRef_quorumLaw (S T : Ty) (ms : List ByteArray) (k : Nat) (g : Label) :
    NoRef (quorumLaw S T ms k g) := by
  have hmem : NoRef (isMember ms ⟨1⟩) := anyOf_ (by simp)
  have hq : NoRef (Term.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") ms.length)) :=
    ⟨trivial, popcount_ trivial⟩
  have hpl : NoRef (proposedLaws ⟨1⟩) := by simp [proposedLaws]
  have hps : NoRef (proposedSet T g ⟨1⟩) := by
    simp only [proposedSet, NoRef, NoRefRow]; exact ⟨trivial, trivial, eqAt_ trivial trivial, trivial⟩
  have hsp : NoRef (sameProposal T ⟨1⟩ (fun b => b.newF "proposal") (fun b => b.oldF "proposal")) := by
    simp only [sameProposal, NoRef, NoRefRow]
    exact ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩, trivial, trivial⟩,
      ⟨trivial, trivial, eqAt_ trivial trivial, trivial⟩, trivial⟩
  have hap : ∀ (m : ByteArray) (i : Nat), NoRef (approvalBy ⟨1⟩ m i) := fun m i =>
    andT_ ⟨bit_ trivial, trivial⟩ (andT_ ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial⟩)
  have hrelaw : NoRef (guards [(isMember ms ⟨1⟩, "not a member")]
      (allOf [(Term.prim .le (natT k) (popcount ((⟨1⟩ : At).oldF "approvals") ms.length), "no quorum"),
        (proposedLaws ⟨1⟩, "not the proposal")])) :=
    guards_ (all_cons hmem all_nil) (allOf_ (all_cons hq (all_cons hpl all_nil)))
  unfold quorumLaw
  try simp only []
  refine lawOf_ (allOf_ (by simp)) (allOf_ (by simp)) hrelaw ?_
  refine guards_ (all_cons hmem (all_cons ⟨trivial, trivial⟩ all_nil)) ?_
  refine ⟨notT_ (eqAt_ trivial trivial), ?_, ?_⟩
  · exact allOf_ (all_cons hq (all_cons hps (all_cons ⟨trivial, trivial⟩ all_nil)))
  · refine ⟨notT_ hsp, allOf_ (by simp), ⟨trivial, trivial⟩, okT_, ?_⟩
    refine ⟨anyOf_ ?_, okT_, refusedT_⟩
    simp only [List.mem_map]
    rintro c ⟨⟨m, i⟩, _, rfl⟩
    exact hap m i

open Std NoRefStd in
theorem noRef_windowedLaw (S T : Ty) (W limit : Nat) (g : Label) : NoRef (windowedLaw S T W limit g) := by
  unfold windowedLaw
  try simp only []
  refine lawOf_ ?_ ?_ okT_ ?_
  · exact guards_ (by simp) (allOf_ (by simp))
  · exact guards_ (by simp) (allOf_ (by simp))
  · refine guards_ (by simp) ⟨⟨trivial, trivial⟩, allOf_ ?_, allOf_ ?_⟩
    · exact all_cons ⟨trivial, trivial, ⟨eqAt_ trivial trivial, trivial, trivial⟩⟩
        (all_cons ⟨trivial, trivial⟩ all_nil)
    · exact all_cons ⟨trivial, trivial⟩ (all_cons ⟨trivial, eqAt_ trivial trivial, trivial, trivial⟩
        (all_cons ⟨trivial, trivial⟩ all_nil))

open Std NoRefStd in
theorem noRef_isState (states : List Label) {t : Term} (ht : NoRef t) (s : Label) :
    NoRef (isState states t s) := by
  refine ⟨ht, row_iff.2 ?_⟩
  simp only [List.mem_map]
  rintro e ⟨_, _, rfl⟩
  trivial

open Std NoRefStd in
theorem noRef_machineLaw (S : Ty) (f : Label) (states : List Label) (initial : Label)
    (edges : List (Label × Nat × Label)) : NoRef (machineLaw S f states initial edges) := by
  unfold machineLaw
  try simp only []
  have hs : NoRef (allOf [(isState states ((⟨1⟩ : At).newF f) initial, s!"{f} does not start at {initial}")]) :=
    allOf_ (by simpa using noRef_isState states (t := (⟨1⟩ : At).newF f) (by simp) initial)
  refine lawOf5_ hs hs refusedT_ refusedT_ (allOf_ ?_)
  simp only [List.mem_singleton, forall_eq]
  refine anyOf_ ?_
  simp only [List.mem_map]
  rintro c ⟨⟨x, m, y⟩, _, rfl⟩
  exact andT_ ⟨trivial, trivial⟩ (andT_ (noRef_isState states (t := (⟨1⟩ : At).oldF f) (by simp) x)
    (noRef_isState states (t := (⟨1⟩ : At).newF f) (by simp) y))


/-! ## The chain: the receiver admitting a `pkgOf` package means each law admitted -/

/-- A law term of the shape the receiver's run reads (`runLaw_ref_admits`): `λ old. λ new. λ req. b`. -/
def IsLaw (t : Term) : Prop := ∃ A B C b, t = .lam A (.lam B (.lam C b))

theorem isLaw_lawOf {S : Ty} {b ad rl c : Std.At → Term} : IsLaw (Std.lawOf S b ad rl c) :=
  ⟨_, _, _, _, rfl⟩
theorem isLaw_lawOf5 {S : Ty} {b ad rl wr iv : Std.At → Term} : IsLaw (Std.lawOf5 S b ad rl wr iv) :=
  ⟨_, _, _, _, rfl⟩

/-! ## The leftovers of LANG-4's vacuity read (LANG-55)

`judgeOne_admits`: the receiver admitting means the laws' meaning for ANY package, imports or not
(`load_top`), each law as loaded; `judgeOne_pkgOf_admits` is now its `pkgOf` instance and no longer
assumes distinct labels: the receiver's load re-ran the install check (`load_checked`), whose
canonical interface has them (`pkgOf_labels_nodup`). `readPackage_installed`: a package cell holding a package's bytes
reads as that package (the codec is canonical, `decodePackage_eq_ok_iff`). -/

/-- In a strictly ascending row every later label is above the head's. -/
theorem ascending_head_lt {α : Type} {k : Label} {a : α} :
    ∀ {r : List (Label × α)}, Row.ascending ((k, a) :: r) = true → ∀ e ∈ r, k < e.1
  | [], _, e, he => by simp at he
  | (k2, b) :: r, h, e, he => by
    have h' : decide (k < k2) = true ∧ Row.ascending ((k2, b) :: r) = true := by
      simpa [Row.ascending] using h
    have hlt : k < k2 := of_decide_eq_true h'.1
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hlt
    · exact String.lt_trans hlt (ascending_head_lt h'.2 e he)

/-- A strictly ascending row has distinct labels. -/
theorem ascending_labels_nodup {α : Type} : ∀ {r : List (Label × α)}, Row.ascending r = true → (r.map (·.1)).Nodup
  | [], _ => by simp
  | (k, a) :: r, h => by
    have hr : Row.ascending r = true := by
      cases r with
      | nil => rfl
      | cons c r => simpa [Row.ascending] using (by simpa [Row.ascending] using h : _ ∧ _).2
    refine List.nodup_cons.2 ⟨?_, ascending_labels_nodup hr⟩
    intro hm
    obtain ⟨e, he, hek⟩ := List.mem_map.1 hm
    have := ascending_head_lt h e he
    rw [hek] at this
    exact String.lt_irrefl _ this

/-- **The distinct-labels premise is the install check's.** A `pkgOf` package whose interface is
well formed (`checkShape` refuses `ifaceNotRecord` otherwise) has distinct law and method labels. -/
theorem pkgOf_labels_nodup {S : Ty} {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    (h : (Std.pkgOf S laws methods).checkShape = .ok ()) : (laws.map (·.1) ++ methods.map (·.1)).Nodup := by
  have hwf : (Std.pkgOf S laws methods).iface.wf = true := by
    unfold Package.checkShape at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (cases h; done) | skip
    all_goals simp_all
  simp only [Std.pkgOf, Ty.wf, Bool.and_eq_true] at hwf
  have hnd := ascending_labels_nodup hwf.1
  refine (List.Perm.nodup_iff ?_).1 hnd
  refine ((Row.sort_perm _).map _).trans ?_
  simp only [List.map_append, List.map_map]
  refine List.Perm.append ?_ ?_
  · have := (Row.sort_perm (Row.sort laws)).map (fun (y : Label × Term) => y.1)
    simpa [Function.comp_def] using ((Row.sort_perm laws).map (fun (y : Label × Term) => y.1))
  · simpa [Function.comp_def] using ((Row.sort_perm methods).map (fun (y : Label × Ty × List Ty × Term) => y.1))

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- **A package cell reads as the package whose bytes it holds** (`install` writes
`encodePackage p` to slot 0 of a package cell, in ROM). -/
theorem readPackage_installed {look : Pinned D} {law : D} {cell : Kernel.Cell} {b : ByteArray} {p : Package}
    (hc : readKind look law kindPackage = .ok cell) (hs : cell.slots.get 0 = some b)
    (he : Wire.encodePackage p = some b) (hr : cell.discipline = .rom) : readPackage look law = .ok p :=
  readPackage_ok.mpr ⟨cell, b, hc, hr, hs, Wire.decodePackage_eq_ok_iff.2 he⟩

/-- **The receiver's verdict is the laws' meaning, for any package.** If `judgeOne` admits
`old → new` under `r` for the package `p` the pinned cell holds (with imports or not), then the
states read at `p`'s state type, and every law label of `p` whose body field `t` has a law's shape
`Admits` the transition as loaded: `t` relocated into the closure (`f`, one relocation for the
package). A law naming no closure package is its own relocation (`relocate_noRef`). -/
theorem judgeOne_admits {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D} {p : Package}
    {fs : List (Label × Term)}
    (hid : digestOf (bytesOf law) = some law) (hp : readPackage look law = .ok p) (hb : p.body = .record fs)
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ∃ o n lib f, readState digestOf (recordRow p.state) old = .ok o ∧
      readState digestOf (recordRow p.state) new = .ok n ∧
      ∀ ℓ ∈ p.laws, ∀ t, Row.find? ℓ fs = some t → IsLaw t →
        Std.Admits lib (t.relocate f) (reqData bytesOf r) n o := by
  obtain ⟨L, g, p', o, n, hload, hpg, ho, hn, hall⟩ := judgeOne_ok bytesOf digestOf h
  obtain ⟨hpg', f, hlib⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hload
  rw [hpg'] at hpg
  cases hpg
  refine ⟨o, n, L.lib, f, ho, hn, fun ℓ hℓ t hf hlaw => ?_⟩
  obtain ⟨A, B, C, b, rfl⟩ := hlaw
  refine Std.runLaw_ref_admits (g := g) (fs := Term.relocateRow f fs) ?_ ?_ (hall ℓ hℓ)
  · rw [hlib, hb]; rfl
  · rw [find_relocateRow, hf]; rfl

end

section
variable {D : Type} (bytesOf : D → ByteArray) (digestOf : ByteArray → Option D)

/-- **The receiver's verdict is the laws' meaning.** If `judgeOne` (the receiver's judge of one law
package) admits `old → new` under `r`, and the pinned package is a stdlib `pkgOf S laws methods`
then the old and new states read at `S`, and EVERY law of the package
that mentions no closure package and has a law's shape `Admits` that transition, with the request
as the receiver built it. Each `Std` spec theorem (`quorum_change`, `machine_invoke`, …) then applies
to the deployed run, not only to a test's closed term. -/
theorem judgeOne_pkgOf_admits {S : Ty} {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D}
    (hid : digestOf (bytesOf law) = some law)
    (hp : readPackage look law = .ok (Std.pkgOf S laws methods))
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ∃ o n, readState digestOf (recordRow S) old = .ok o ∧ readState digestOf (recordRow S) new = .ok n ∧
      ∀ x ∈ laws, NoRef x.2 → IsLaw x.2 → ∃ lib, Std.Admits lib x.2 (reqData bytesOf r) n o := by
  -- distinct labels: the receiver's own load re-ran the install check (`load_checked`)
  have hnd : (laws.map (·.1) ++ methods.map (·.1)).Nodup := by
    obtain ⟨L, g, p', _, _, hload, hpg, -⟩ := judgeOne_ok bytesOf digestOf h
    obtain ⟨hpg', -⟩ := load_top bytesOf digestOf (fuel := closureDepthMax - 1) hid hp hload
    rw [hpg'] at hpg
    cases hpg
    exact pkgOf_labels_nodup (load_checked hload g _ hpg').1
  let xs := Row.sort laws ++ (Row.sort methods).map (fun (l, _, _, t) => (l, t))
  obtain ⟨o, n, lib, f, ho, hn, hall⟩ := judgeOne_admits bytesOf digestOf (fs := Row.sort xs) hid hp rfl h
  refine ⟨o, n, ho, hn, fun x hx hfree hlaw => ?_⟩
  obtain ⟨ℓ, t⟩ := x
  simp only at hfree hlaw
  have hsl : (ℓ, t) ∈ Row.sort laws := (Row.sort_perm laws).mem_iff.2 hx
  have hmem : ℓ ∈ (Std.pkgOf S laws methods).laws := by
    simp only [Std.pkgOf, List.mem_map]
    exact ⟨_, hsl, rfl⟩
  have hxs : (xs.map (·.1)).Perm (laws.map (·.1) ++ methods.map (·.1)) := by
    simp only [xs, List.map_append, List.map_map]
    refine List.Perm.append ((Row.sort_perm laws).map _) ?_
    have := (Row.sort_perm methods).map (fun (y : Label × Ty × List Ty × Term) => y.1)
    simpa [Function.comp_def] using this
  have hfind : Row.find? ℓ (Row.sort xs) = some t :=
    find_of_mem_nodup (((Row.sort_perm xs).map _).trans hxs |>.nodup_iff.2 hnd)
      ((Row.sort_perm xs).mem_iff.2 (List.mem_append_left _ hsl))
  have := hall ℓ hmem t hfind hlaw
  rw [relocate_noRef _ _ hfree] at this
  exact ⟨lib, this⟩

theorem reqData_agent (r : Req D) :
    (reqData bytesOf r).field "agent" = some (.digest (bytesOf r.agent)) := by
  simp [reqData, Data.field, Row.find?]

theorem reqData_occasion (r : Req D) :
    (reqData bytesOf r).field "occasion" = some (occasionData bytesOf r.occasion) := by
  simp [reqData, Data.field, Row.find?]

/-- **A quorum package, as the receiver runs it**: a write or invoke the receiver admits on an
object of a `pkgOf` package carrying the CHECKED `quorum`'s law (so the members are distinct and
`1 ≤ k ≤ members`, `Std.quorum_ok`) is by a member and is one of commit / propose /
approve / no-op (`Std.quorum_change`), on the states the receiver read. -/
theorem judgeOne_quorum_change {S T : Ty} {ms : List ByteArray} {k : Nat} {g ℓq : Label}
    {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D}
    (hid : digestOf (bytesOf law) = some law)
    (hp : readPackage look law = .ok (Std.pkgOf S laws methods))
    {t : Term} (hqc : Std.quorum S T ms k g = .ok t) (hq : (ℓq, t) ∈ laws)
    (hocc : r.occasion = .write ∨ ∃ m, r.occasion = .invoke m)
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ms.Nodup ∧ 1 ≤ k ∧ k ≤ ms.length ∧
    ∃ o n, readState digestOf (recordRow S) old = .ok o ∧ readState digestOf (recordRow S) new = .ok n ∧
      (∃ m ∈ ms, (reqData bytesOf r).field "agent" = some (.digest m)) ∧
      (∃ b, n.field "approvals" = some (.nat b) ∧ b < Std.pow2 ms.length) ∧
      ∃ ng og, n.field g = some ng ∧ o.field g = some og ∧
        ((ng ≠ og ∧ (∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ Std.popcountNat a ms.length) ∧
            o.field "proposal" = some (.inj "set" ng) ∧ n.field "approvals" = some (.nat 0)) ∨
         (ng = og ∧ ∃ np op, n.field "proposal" = some np ∧ o.field "proposal" = some op ∧
            ((np ≠ op ∧ n.field "approvals" = some (.nat 0)) ∨
             (np = op ∧ ∃ a, n.field "approvals" = some (.nat a) ∧ o.field "approvals" = some (.nat a)) ∨
             (np = op ∧ ∃ i m a, ms[i]? = some m ∧ (reqData bytesOf r).field "agent" = some (.digest m) ∧
                o.field "approvals" = some (.nat a) ∧ a / Std.pow2 i % 2 = 0 ∧
                n.field "approvals" = some (.nat (a + Std.pow2 i)))))) := by
  obtain ⟨rfl, hms, hk1, hk2, _⟩ := Std.quorum_ok hqc
  obtain ⟨o, n, ho, hn, hall⟩ := judgeOne_pkgOf_admits bytesOf digestOf hid hp h
  obtain ⟨lib, ha⟩ := hall _ hq (noRef_quorumLaw S T ms k g) isLaw_lawOf
  have hro := reqData_occasion bytesOf r
  refine ⟨hms, hk1, hk2, o, n, ho, hn, ?_⟩
  rcases hocc with he | ⟨m, he⟩ <;> rw [he] at hro <;> simp only [occasionData] at hro
  · exact Std.quorum_change ha hro (.inl rfl)
  · exact Std.quorum_change ha hro (.inr rfl)

/-- **A quorum package's relaw, as the receiver runs it**: replacing the laws of an object under
`quorumLaw` needs a member and `k` approvals in the old state of a proposal of EXACTLY the incoming
ids' bytes (`Std.quorum_relaw_needs_k`). -/
theorem judgeOne_quorum_relaw {S T : Ty} {ms : List ByteArray} {k : Nat} {g ℓq : Label}
    {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D} {ls : List D}
    (hid : digestOf (bytesOf law) = some law)
    (hp : readPackage look law = .ok (Std.pkgOf S laws methods))
    {t : Term} (hqc : Std.quorum S T ms k g = .ok t) (hq : (ℓq, t) ∈ laws)
    (hocc : r.occasion = .relaw ls)
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ms.Nodup ∧ 1 ≤ k ∧ k ≤ ms.length ∧ ∃ o, readState digestOf (recordRow S) old = .ok o ∧
      (∃ m ∈ ms, (reqData bytesOf r).field "agent" = some (.digest m)) ∧
      (∃ a, o.field "approvals" = some (.nat a) ∧ k ≤ Std.popcountNat a ms.length) ∧
      o.field "proposal" = some (.inj "laws" (.bytes (ls.foldl (fun acc l => acc ++ bytesOf l) .empty))) := by
  obtain ⟨rfl, hms, hk1, hk2, _⟩ := Std.quorum_ok hqc
  obtain ⟨o, n, ho, _, hall⟩ := judgeOne_pkgOf_admits bytesOf digestOf hid hp h
  obtain ⟨lib, ha⟩ := hall _ hq (noRef_quorumLaw S T ms k g) isLaw_lawOf
  have hro := reqData_occasion bytesOf r
  rw [hocc] at hro; simp only [occasionData] at hro
  obtain ⟨hm, hk, sb, hs, hx⟩ := Std.quorum_relaw_needs_k ha hro
  cases hx
  exact ⟨hms, hk1, hk2, o, ho, hm, hk, hs⟩

/-- **A machine package, as the receiver runs it** (HOSTING's grain lifecycle is one): an invoke
of method `m` the receiver admits moved the machine field along an edge `(a, m, b)`. -/
theorem judgeOne_machine_invoke {S : Ty} {f ℓm : Label} {states : List Label} {initial : Label}
    {edges : List (Label × Nat × Label)}
    {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    {look : Pinned D} {law : D} {old new : Kernel.Slots} {r : Req D} {m : Nat}
    (hid : digestOf (bytesOf law) = some law)
    (hp : readPackage look law = .ok (Std.pkgOf S laws methods))
    (hq : (ℓm, Std.machineLaw S f states initial edges) ∈ laws)
    (hocc : r.occasion = .invoke m)
    (h : judgeOne bytesOf digestOf look law old new r = .ok ()) :
    ∃ o n, readState digestOf (recordRow S) old = .ok o ∧ readState digestOf (recordRow S) new = .ok n ∧
      ∃ a b, (a, m, b) ∈ edges ∧ (∃ y, o.field f = some (.inj a y)) ∧ ∃ y, n.field f = some (.inj b y) := by
  obtain ⟨o, n, ho, hn, hall⟩ := judgeOne_pkgOf_admits bytesOf digestOf hid hp h
  obtain ⟨lib, ha⟩ := hall _ hq (noRef_machineLaw S f states initial edges) isLaw_lawOf5
  have hro := reqData_occasion bytesOf r
  rw [hocc] at hro; simp only [occasionData] at hro
  obtain ⟨a, m', b, he, hx, hoa, hnb⟩ := Std.machine_invoke ha hro
  cases hx
  exact ⟨o, n, ho, hn, a, b, he, hoa, hnb⟩

end

/-! ## Machine edges name the method the kernel runs -/

theorem methodIndex_go : ∀ {ls : List Label} {m : Label} {j i : Nat}, Std.methodIndex.go m ls j = some i →
    j ≤ i ∧ ls[i - j]? = some m
  | [], _, _, _, h => by simp [Std.methodIndex.go] at h
  | x :: ls, m, j, i, h => by
    simp only [Std.methodIndex.go] at h
    split at h
    · rename_i hx; cases h; simp [hx]
    · obtain ⟨hle, hget⟩ := methodIndex_go h
      refine ⟨by omega, ?_⟩
      have : i - j = (i - (j + 1)) + 1 := by omega
      rw [this]; simpa using hget

/-- **An edge's method label is the method the kernel's index runs**: `Std.machine`/`stepTo`
resolve a method label to index `i` (`methodIndex`), and `pkgOf`'s method list, which the kernel's
`invoke` indexes, has that label at `i`. So `judgeOne_machine_invoke`'s index is the edge's method
by name. -/
theorem methodIndex_pkgOf {S : Ty} {laws : List (Label × Term)} {methods : List (Label × Ty × List Ty × Term)}
    {m : Label} {i : Nat} (h : Std.methodIndex (methods.map (·.1)) m = some i) :
    (Std.pkgOf S laws methods).methods[i]? = some m := by
  unfold Std.methodIndex at h
  obtain ⟨_, hget⟩ := methodIndex_go h
  simp only [Nat.sub_zero] at hget
  have hl : (Row.sort (((methods.map (·.1)).map fun x => (x, ())))).map (·.1) =
      (Row.sort methods).map (·.1) := by
    have := Row.sort_map (fun (z : Label × Ty × List Ty × Term) => (z.1, ())) (fun _ => rfl) methods
    rw [List.map_map]
    simp only [Function.comp_def] at this ⊢
    rw [← this, List.map_map]
    rfl
  rw [hl] at hget
  exact hget

/-! ## Teeth for LANG-55 -/

/-- The install check refuses a `pkgOf` with a repeated label (so `pkgOf_labels_nodup`'s premise
is not met by every package) and accepts one with distinct labels (so it is met by some). -/
theorem checkShape_refuses_repeated_label :
    ((Std.pkgOf (.record []) [("a", Std.ownerSigns (.record [])), ("a", Std.ownerSigns (.record []))] []).checkShape
      matches .error _) = true := by decide +kernel
theorem checkShape_accepts_distinct_labels :
    ((Std.pkgOf (.record []) [("a", Std.ownerSigns (.record [])), ("b", Std.ownerSigns (.record []))] []).checkShape
      matches .ok _) = true := by decide +kernel

end Nanodregg.Lang
