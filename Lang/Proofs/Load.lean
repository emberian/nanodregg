/-
# Lang.Proofs.Load — a loaded closure is a well-typed library

`load` (re-checking each package, decisions/lang.md LANG-16) only ever builds closures that satisfy
`LibTy` for the interfaces of their packages (`load_libTy`). With `checked_never_stuck` this says the
deployed `Program.run` and `Program.judge` run their bodies in a typed library: no closure a receiver
loads can make a method or a law reach `stuck`, whatever the cells held.
-/
import Lang.Program
import Lang.Proofs.Relocate
import Lang.Proofs.RunTy
import Lang.Proofs.Check
import Lang.Proofs.Sound
import Lang.Proofs.Wire

namespace Nanodregg.Lang

open Nanodregg.Kernel.Receive

/-- The closure invariant: ids, bodies and packages line up, every body has its package's interface
type in the closure, and every package passed its shape and field checks (so its state is a record
and its methods and laws are interface fields at their shapes), and every package is one the wire
carries (it was decoded). -/
def Inv (L : Loaded) : Prop :=
  L.ids.length = L.pkgs.length ∧ L.lib.length = L.pkgs.length ∧
  (∀ (i : Nat) (t : Term) (P : Package), L.lib[i]? = some t → L.pkgs[i]? = some P →
    HasType (Loaded.ifaces L) [] t P.iface) ∧
  ∀ (i : Nat) (P : Package), L.pkgs[i]? = some P →
    P.checkShape = .ok () ∧ P.checkFields = .ok () ∧ Wire.packageWire P = true

theorem Inv.empty : Inv ⟨[], [], []⟩ := ⟨rfl, rfl, by simp, by simp⟩

mutual
theorem relocate_id : ∀ t : Term, t.relocate (fun i => i) = t
  | .var _ | .nat _ | .bool _ | .bytes _ | .digest _ | .ref _ | .refuse _ _ => rfl
  | .lam _ b => by simp [Term.relocate, relocate_id b]
  | .app f a => by simp [Term.relocate, relocate_id f, relocate_id a]
  | .fix t => by simp [Term.relocate, relocate_id t]
  | .prim _ a b => by simp [Term.relocate, relocate_id a, relocate_id b]
  | .record fs => by simp [Term.relocate, relocateRow_id fs]
  | .get t _ => by simp [Term.relocate, relocate_id t]
  | .extend t fs => by simp [Term.relocate, relocate_id t, relocateRow_id fs]
  | .inj _ _ t => by simp [Term.relocate, relocate_id t]
  | .case t fs => by simp [Term.relocate, relocate_id t, relocateRow_id fs]
  | .ite c a b => by simp [Term.relocate, relocate_id c, relocate_id a, relocate_id b]
  | .hole n σ => by simp [Term.relocate, relocateList_id σ]

theorem relocateList_id : ∀ ts : List Term, Term.relocateList (fun i => i) ts = ts
  | [] => rfl
  | t :: ts => by simp [Term.relocateList, relocate_id t, relocateList_id ts]

theorem relocateRow_id : ∀ fs : List (Label × Term), Term.relocateRow (fun i => i) fs = fs
  | [] => rfl
  | (_, t) :: fs => by simp [Term.relocateRow, relocate_id t, relocateRow_id fs]
end

/-- Typing survives appending to the library's types. -/
theorem HasType.weaken {Δ : List Ty} (m : List Ty) {t : Term} {T : Ty}
    (h : HasType Δ [] t T) : HasType (Δ ++ m) [] t T := by
  have := relocate_typed (Δ' := Δ ++ m) (f := fun i => i)
    (fun i A hA => by simp [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hA).1, hA]) h
  rwa [relocate_id] at this

theorem ifacesAt_spec {pkgs : List Package} :
    ∀ {gs : List Nat} {ifs : List Ty}, ifacesAt pkgs gs = some ifs →
      ∀ (i : Nat) (A : Ty), ifs[i]? = some A → (pkgs.map (·.iface))[gs.getD i 0]? = some A
  | [], ifs, h, i, A, hA => by simp [ifacesAt] at h; subst h; simp at hA
  | g :: gs, ifs, h, i, A, hA => by
    simp only [ifacesAt] at h
    split at h
    · rename_i P r hP hr
      cases h
      cases i with
      | zero => simp at hA ⊢; subst hA; simp [hP]
      | succ i => simpa using ifacesAt_spec hr i A (by simpa using hA)
    · simp at h

theorem ifacesAt_bounded {pkgs : List Package} :
    ∀ {gs : List Nat} {ifs : List Ty}, ifacesAt pkgs gs = some ifs → ifs.length = gs.length
  | [], _, h => by simp [ifacesAt] at h; subst h; rfl
  | g :: gs, ifs, h => by
    simp only [ifacesAt] at h
    split at h
    · rename_i P r _ hr; cases h; simp [ifacesAt_bounded hr]
    · simp at h

theorem checkWith_typed {ifs : List Ty} {p : Package} (h : p.checkWith ifs = .ok ()) :
    HasType ifs [] p.body p.iface := by
  unfold Package.checkWith at h
  split at h
  · simp at h
  · simp at h
  · rename_i hc; exact checkE_ok_iff.mp hc

theorem checkWith_checked {ifs : List Ty} {p : Package} (h : p.checkWith ifs = .ok ()) :
    p.checkShape = .ok () ∧ p.checkFields = .ok () := by
  unfold Package.checkWith at h
  split at h
  · simp at h
  · simp at h
  · rename_i hs _
    split at h
    · cases h
    · split at h
      · cases h
      · exact ⟨hs, h⟩

theorem checkWith_closed {ifs : List Ty} {p : Package} (h : p.checkWith ifs = .ok ()) :
    p.holes = [] ∧ ∀ T ∈ ifs, T.wf = true := by
  unfold Package.checkWith at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  constructor
  · simpa using ‹(!p.holes.isEmpty) ≠ true›
  · have hi : ifs.all Ty.wf = true := by simpa using ‹(!ifs.all Ty.wf) ≠ true›
    exact List.all_eq_true.mp hi

theorem indexIn_lt {b : ByteArray} : ∀ {ids : List ByteArray} {i : Nat}, indexIn b ids = some i →
    i < ids.length
  | [], _, h => by simp [indexIn] at h
  | x :: xs, i, h => by
    simp only [indexIn] at h
    split at h
    · cases h; simp
    · cases e : indexIn b xs with
      | none => simp [e] at h
      | some j => simp [e] at h; subst h; have := indexIn_lt e; simp; omega

theorem getElem?_append_of_some {α : Type} {l m : List α} {k : Nat} {a : α}
    (h : l[k]? = some a) : (l ++ m)[k]? = some a := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h

/-- **What a package read is**: the cell at the id is a package cell, ROM, and its slot 0 decodes to
the package. -/
theorem readPackage_ok {D : Type} {look : Pinned D} {id : D} {p : Package} :
    readPackage look id = .ok p ↔ ∃ cell b, readKind look id kindPackage = .ok cell ∧
      cell.discipline = .rom ∧ cell.slots.get 0 = some b ∧ Wire.decodePackage b = .ok p := by
  unfold readPackage
  cases hk : readKind look id kindPackage with
  | error e => simp [bind, Except.bind]
  | ok cell =>
    by_cases hr : cell.discipline = .rom
    · cases hs : cell.slots.get 0 with
      | none => simp [bind, Except.bind, hr, hs, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
      | some b =>
        cases hd : Wire.decodePackage b <;>
          simp [bind, Except.bind, hr, hs, hd, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    · simp [bind, Except.bind, hr]

/-- A package read from a cell is one the wire carries. -/
theorem readPackage_wire {D : Type} {look : Pinned D} {id : D} {p : Package}
    (h : readPackage look id = .ok p) : Wire.packageWire p = true := by
  obtain ⟨-, b, -, -, -, hd⟩ := readPackage_ok.mp h
  obtain ⟨b', hb⟩ : ∃ b', Wire.encodePackage p = some b' := ⟨_, Wire.decodePackage_eq_ok_iff.mp hd⟩
  unfold Wire.encodePackage at hb
  split at hb
  · assumption
  · simp at hb

theorem admitPackage_inv {D : Type} {digestOf : ByteArray → Option D} {idb : ByteArray} {p : Package} {acc L : Loaded}
    {gis : List Nat} {g : Nat} (hi : Inv acc) (hpw : Wire.packageWire p = true)
    (h : admitPackage digestOf idb p acc gis = .ok (L, g)) :
    Inv L ∧ g < L.pkgs.length ∧ L.pkgs = acc.pkgs ++ [p] := by
  obtain ⟨hids, hlib, hty, hck⟩ := hi
  unfold admitPackage at h
  split at h
  · simp at h
  · rename_i ifs hifs
    split at h
    · simp at h
    · rename_i hc
      split at h
      · simp at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hΔ : Loaded.ifaces ⟨acc.ids ++ [idb], acc.lib ++ [p.body.relocate fun i => gis.getD i 0],
          acc.pkgs ++ [p]⟩ = Loaded.ifaces acc ++ [p.iface] := by simp [Loaded.ifaces]
      refine ⟨⟨by simp [hids], by simp [hlib], ?_, ?_⟩, by simp [hids], rfl⟩
      rotate_left
      · intro i P hP
        simp only at hP
        by_cases lt : i < acc.pkgs.length
        · rw [List.getElem?_append_left lt] at hP; exact hck i P hP
        · rw [List.getElem?_append_right (by omega)] at hP
          have e1 : i - acc.pkgs.length = 0 := by
            cases h' : i - acc.pkgs.length with
            | zero => rfl
            | succ k => rw [h'] at hP; simp at hP
          rw [e1] at hP; simp at hP; subst hP
          exact ⟨(checkWith_checked hc).1, (checkWith_checked hc).2, hpw⟩
      intro i t P ht hP
      rw [hΔ]
      simp only at ht hP
      by_cases lt : i < acc.lib.length
      · rw [List.getElem?_append_left lt] at ht
        rw [List.getElem?_append_left (by omega)] at hP
        exact (hty i t P ht hP).weaken _
      · rw [List.getElem?_append_right (by omega)] at ht
        rw [List.getElem?_append_right (by omega)] at hP
        have e1 : i - acc.lib.length = 0 := by
          cases h' : i - acc.lib.length with
          | zero => rfl
          | succ k => rw [h'] at ht; simp at ht
        rw [e1] at ht; rw [hlib] at e1; rw [e1] at hP
        simp at ht hP; subst ht; subst hP
        have hb := checkWith_typed hc
        exact relocate_typed (fun i A hA => getElem?_append_of_some (ifacesAt_spec hifs i A hA)) hb

section
variable {D : Type} (digestOf : ByteArray → Option D) (rc : ReceiptCheck) (look : Pinned D)

mutual
theorem load_inv (fuel : Nat) (idb : ByteArray) (acc : Loaded) {L : Loaded} {g : Nat}
    (hi : Inv acc) (h : load digestOf look fuel idb acc = .ok (L, g)) :
    Inv L ∧ g < L.pkgs.length ∧ ∃ ext, L.pkgs = acc.pkgs ++ ext := by
  unfold load loadUsing at h
  split at h
  · rename_i i hidx
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, hi.1 ▸ indexIn_lt hidx, [], by simp⟩
  · split at h
    · simp at h
    · rename_i fuel
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i p hrp
          split at h
          · simp at h
          · rename_i acc' gis hall
            obtain ⟨hi', _, ext, hext⟩ := loadAll_inv fuel p.imports acc hi hall
            obtain ⟨hL, hg, hp⟩ := admitPackage_inv hi' (readPackage_wire hrp) h
            exact ⟨hL, hg, ext ++ [p], by rw [hp, hext, List.append_assoc]⟩
termination_by (fuel, 0)

theorem loadAll_inv (fuel : Nat) (ds : List ByteArray) (acc : Loaded) {L : Loaded}
    {gs : List Nat} (hi : Inv acc) (h : loadAll digestOf look fuel ds acc = .ok (L, gs)) :
    Inv L ∧ (∀ g ∈ gs, g < L.pkgs.length) ∧ ∃ ext, L.pkgs = acc.pkgs ++ ext := by
  unfold loadAll loadAllUsing at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hi, by simp, [], by simp⟩
  · rename_i d ds
    split at h
    · simp at h
    · rename_i acc1 g1 h1
      split at h
      · simp at h
      · rename_i acc2 gs2 h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hi1, hg1, e1, he1⟩ := load_inv fuel d acc hi h1
        obtain ⟨hi2, hg2, e2, he2⟩ := loadAll_inv fuel ds acc1 hi1 h2
        refine ⟨hi2, ?_, e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · rw [he2]; simp; omega
        · exact hg2 g hg
termination_by (fuel, ds.length + 1)
end

end

/-- Every package of a loaded closure passed its install checks again at load. -/
theorem load_checked {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D}
    {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat}
    (h : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g)) :
    ∀ (i : Nat) (P : Package), L.pkgs[i]? = some P →
      P.checkShape = .ok () ∧ P.checkFields = .ok () ∧ Wire.packageWire P = true :=
  (load_inv digestOf look fuel idb _ Inv.empty h).1.2.2.2

/-- Every closure a receiver loads is a well-typed library for its packages' interfaces. -/
theorem load_libTy {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D}
    {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat}
    (h : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g)) :
    LibTy (Loaded.ifaces L) L.lib ∧ g < L.pkgs.length := by
  obtain ⟨⟨_, hlib, hty, _⟩, hg, _⟩ := load_inv digestOf look fuel idb _ Inv.empty h
  refine ⟨fun i T hT => ?_, hg⟩
  simp only [Loaded.ifaces, List.getElem?_map, Option.map_eq_some_iff] at hT
  obtain ⟨P, hP, rfl⟩ := hT
  have hi : i < L.lib.length := by rw [hlib]; exact (List.getElem?_eq_some_iff.mp hP).1
  exact ⟨L.lib[i], List.getElem?_eq_getElem hi, hty i _ P (List.getElem?_eq_getElem hi) hP⟩

theorem callSlotOf_spec {t T : Ty} (h : callSlotOf t = some T) : t = optTy T := by
  unfold callSlotOf at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem mapM_callSlotOf : ∀ {row : List (Label × Ty)} {ks : List Ty},
    row.mapM (fun e => callSlotOf e.2) = some ks → row.map Prod.snd = ks.map optTy
  | [], ks, h => by simp at h; subst h; rfl
  | (l, t) :: row, ks, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨T, hT, ks', hks', rfl⟩ := h
    simp [callSlotOf_spec hT, mapM_callSlotOf hks']

theorem zip_map_fst_snd {α β : Type} : ∀ (l : List (α × β)), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | (a, b) :: l => by simp [zip_map_fst_snd l]

/-- A calls row is the row of its call types, and has at most `callsMax` slots. -/
theorem callSlotsOf_spec {row : List (Label × Ty)} {ks : List Ty} (h : callSlotsOf row = some ks) :
    row = (slotLabels "c" ks.length).zip (ks.map optTy) ∧ ks.length ≤ Kernel.Bounds.callsMax := by
  unfold callSlotsOf at h
  split at h
  · rename_i hc
    have hs := mapM_callSlotOf h
    have hlen : row.length = ks.length := by
      have := congrArg List.length hs; simpa using this
    refine ⟨?_, hlen ▸ hc.1⟩
    rw [← hlen, ← hc.2, ← hs]
    exact (zip_map_fst_snd row).symm
  · cases h

theorem editSlotsOf_spec {rels : List (Label × RelDecl)} {row : List (Label × Ty)} {es : Nat}
    (h : editSlotsOf rels row = some es) :
    row = (slotLabels "e" es).map (fun l => (l, optTy (editTy rels))) ∧ es ≤ editsMax := by
  unfold editSlotsOf at h
  split at h
  · rename_i hc; cases h; exact ⟨hc.2, hc.1⟩
  · cases h

theorem readsOf_spec {rels : List (Label × RelDecl)} {R : Ty} {rs : List (Label × RelRead)}
    (h : readsOf rels R = some rs) : readsTy rels rs = R := by
  unfold readsOf at h
  split at h
  · split at h
    · split at h
      · rename_i hR; cases h; exact hR
      · cases h
    · cases h
  · cases h

/-- A rows record reads back exactly (PROT-6): its own reads and its peer reads are the ones it spells. -/
theorem rowsOf_spec {rels : List (Label × RelDecl)} {R : Ty} {rs ps : List (Label × RelRead)}
    (h : rowsOf rels R = some (rs, ps)) : rowsTy rels rs ps = R := by
  unfold rowsOf at h
  split at h
  · rename_i row
    split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨rs', hr, rfl, rfl⟩ := h
      simpa [rowsTy] using readsOf_spec hr
    · split at h
      · split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hc.2
        · cases h
      · cases h
  · cases h

/-- **The type IS the declaration** (LANG-49, PROT-6): a method field's signature reads back exactly
the type it was read from, its rows argument (its own reads, and its peer reads `methodPeer`), call
slots and edit slots included. -/
theorem methodSig_spec {S : Ty} {rels : List (Label × RelDecl)} {t : Ty} {sg : Sig}
    (h : methodSig S rels t = some sg) :
    t = methodTy S sg.arg sg.calls (rowsTy rels sg.reads (methodPeer rels t)) (editTy rels) sg.edits ∧
      sg.calls.length ≤ Kernel.Bounds.callsMax ∧ sg.edits ≤ editsMax := by
  unfold methodSig at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, _⟩ := hc
      split at h
      · rename_i ks es rs ps hks hes hrs
        split at h
        · cases h
          obtain ⟨hrow, hlen⟩ := callSlotsOf_spec hks
          obtain ⟨herow, hes'⟩ := editSlotsOf_spec hes
          have hR := rowsOf_spec hrs
          refine ⟨?_, hlen, hes'⟩
          subst hrow herow hR
          simp only [methodPeer, hrs, Option.map_some, Option.getD_some]
          rfl
        · cases h
      · cases h
    · cases h
  · cases h

theorem methodArg_spec {S : Ty} {rels : List (Label × RelDecl)} {t A : Ty} (h : methodArg S rels t = some A) :
    ∃ ks rs ps es, t = methodTy S A ks (rowsTy rels rs ps) (editTy rels) es := by
  unfold methodArg at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨sg, hs, rfl⟩ := h
  exact ⟨sg.calls, sg.reads, _, sg.edits, (methodSig_spec hs).1⟩

/-- The peer reads a resolved method declares are its type's (`methodPeer`). -/
theorem Package.peerReads_of {p : Package} {ℓ : Label} {mty : Ty}
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) : p.peerReads ℓ = methodPeer p.rels mty := by
  simp [Package.peerReads, hm]

theorem recordRow_find {T : Ty} {ℓ : Label} {t : Ty} (h : Row.find? ℓ (recordRow T) = some t) :
    ∃ row, T = .record row ∧ Row.find? ℓ row = some t := by
  cases T <;> simp_all [recordRow, Row.find?]

/-- A method of a loaded package, applied to a state, arguments and a request of the right types,
runs in the loaded closure without ever reaching `stuck`: it ends with a result of the package's
`resultTy` (the calls it makes, its row edits and the new state), or a named budget/arithmetic fault. (That the values decoded from the cells HAVE those
types is `decodeData_conforms`/`readState_conforms`; `Lang.Proofs.Invoke` composes them.) -/
theorem method_run_sound {D : Type} {digestOf : ByteArray → Option D} {look : Pinned D}
    {fuel : Nat} {idb : ByteArray} {L : Loaded} {g : Nat} {p : Package} {ℓ : Label} {mty : Ty}
    {sg : Sig} {sv av rv wv : Val} {ticks : Nat}
    (hload : load digestOf look fuel idb ⟨[], [], []⟩ = .ok (L, g))
    (hp : L.pkgs[g]? = some p)
    (hm : Row.find? ℓ (recordRow p.iface) = some mty) (hA : methodSig p.state p.rels mty = some sg)
    (hs : ValTy (Loaded.ifaces L) sv p.state) (ha : ValTy (Loaded.ifaces L) av sg.arg)
    (hr : ValTy (Loaded.ifaces L) rv reqTy)
    (hw : ValTy (Loaded.ifaces L) wv (rowsTy p.rels sg.reads (methodPeer p.rels mty))) :
    RunOK (Loaded.ifaces L) (resultTy p.state sg.calls (editTy p.rels) sg.edits)
      (run L.lib Bounds.stackMax ticks 0 (State.init (apply4 g ℓ) [rv, av, sv, wv])) := by
  obtain ⟨hlib, _⟩ := load_libTy hload
  obtain ⟨row, hrow, hfind⟩ := recordRow_find hm
  have hmt := (methodSig_spec hA).1
  generalize methodPeer p.rels mty = ps at hw hmt
  subst hmt
  have href : HasType (Loaded.ifaces L) [reqTy, sg.arg, p.state, rowsTy p.rels sg.reads ps] (.ref g)
      (.record row) :=
    .ref (by rw [← hrow]; simp [Loaded.ifaces, hp])
  have ht : HasType (Loaded.ifaces L) [reqTy, sg.arg, p.state, rowsTy p.rels sg.reads ps] (apply4 g ℓ)
      (resultTy p.state sg.calls (editTy p.rels) sg.edits) :=
    .app (.app (.app (.app (.get href hfind) (.var rfl)) (.var rfl)) (.var rfl)) (.var rfl)
  exact run_sound hlib _ _ _ (.eval (.cons hr (.cons ha (.cons hs (.cons hw .nil)))) ht .nil)

/-- **What a run starts from** (LANG-41): `runSetup` admits exactly when the request is in bounds,
the closure loads, the method resolves, the state reads at its row and the arguments decode at their
type with every digest accepted; the setup is then those values. -/
theorem runSetupWith_spec {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {rc : ReceiptCheck}
    {loader : Pinned D → Nat → ByteArray → Loaded → Except (Refusal D) (Loaded × Nat)}
    {charge : Loaded → Nat}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {S : RunSetup}
    (h : runSetupWith bytesOf digestOf rc loader charge look rv pkg state method args r = .ok S) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (ℓ : Label) (sg : Sig) (sd ad wd : Data),
      reqOk bytesOf r = true ∧
      loader look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧
      readState digestOf (recordRow p.state) state = .ok sd ∧
      Wire.decodeData sg.arg args = .ok ad ∧ digestsOk digestOf ad.digests = true ∧
      methodReads bytesOf digestOf rc look pkg p.rels rv r.self ad sg.reads (p.peerReads ℓ) = .ok wd ∧
      S = { lib := L.lib, pkgs := L.pkgs.length, g, rels := p.rels, label := ℓ, row := recordRow p.state,
            ty := resultTy p.state sg.calls (editTy p.rels) sg.edits, calls := sg.calls, state := sd, args := ad,
            reads := wd, term := apply4 g ℓ, env := [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal], preparation := charge L } := by
  unfold runSetupWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨_, _, _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

theorem runSetup_spec {D : Type} {bytesOf : D → ByteArray} {digestOf : ByteArray → Option D}
    {rc : ReceiptCheck}
    {look : Pinned D} {rv : RowView D} {pkg : D} {state : Kernel.Slots} {method : Nat} {args : ByteArray}
    {r : Req D} {S : RunSetup}
    (h : runSetup bytesOf digestOf rc look rv pkg state method args r = .ok S) :
    ∃ (L : Loaded) (g : Nat) (p : Package) (ℓ : Label) (sg : Sig) (sd ad wd : Data),
      reqOk bytesOf r = true ∧
      load digestOf look closureDepthMax (bytesOf pkg) ⟨[], [], []⟩ = .ok (L, g) ∧ L.pkgs[g]? = some p ∧
      resolveMethod (D := D) p method = .ok (ℓ, sg) ∧
      readState digestOf (recordRow p.state) state = .ok sd ∧
      Wire.decodeData sg.arg args = .ok ad ∧ digestsOk digestOf ad.digests = true ∧
      methodReads bytesOf digestOf rc look pkg p.rels rv r.self ad sg.reads (p.peerReads ℓ) = .ok wd ∧
      S = { lib := L.lib, pkgs := L.pkgs.length, g, rels := p.rels, label := ℓ, row := recordRow p.state,
            ty := resultTy p.state sg.calls (editTy p.rels) sg.edits, calls := sg.calls, state := sd, args := ad,
            reads := wd, term := apply4 g ℓ, env := [(reqData bytesOf r).toVal, ad.toVal, sd.toVal, wd.toVal] } := by
  unfold runSetup runSetupWith at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨_, _, _, _, _, _, _, _, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩

end Nanodregg.Lang
