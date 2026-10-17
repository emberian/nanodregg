/-
# Hosting.Proofs.Allowance — the allowance package computes its two methods, has a text, and is read
only from the operator's own objects

The method theorems are the kernel running LANG's machine (`Lang.eval`) on the package BODY, applied
as `Lang.Program` applies a method (state at `var 2`, argument at `var 1`, request at `var 0`), over
a state whose every field is distinct, for both values of `revoked`, so a method that copies the
wrong field, or writes a constant, is caught.
-/
import Hosting.Allowance
import Lang.Print
import Lang.Read
import Lang.Eval
import Lang.Proofs.Print
import Kernel.Receive.Authority
import Kernel.Proofs.Rooted
import Lang.Proofs.Data
import Lang.Program
import Hosting.Proofs.Frame
import Kernel.Proofs.Cells
import Kernel.Proofs.Trie
import Hosting.Loop
import Host.Tail
import Host.Record

namespace Nanodregg.Hosting.Proofs.Allowance

open Nanodregg.Lang Nanodregg.Kernel Nanodregg.Hosting Nanodregg.Hosting.Allow

/-- The package passes LANG's install check with no imports. -/
theorem allowance_checks : (allowance.checkWith [] matches .ok ()) = true := by decide +kernel

/-- No law; the methods, in KERNEL's index order, are `revoke` then `set`. -/
theorem allowance_shape :
    allowance.laws = [] ∧ allowance.methods = ["revoke", "set"] ∧
      allowance.methods[revokeIndex]? = some "revoke" ∧ allowance.methods[setIndex]? = some "set" := by
  decide +kernel

private def fuel : Nat := 1000

private def stD (revoked : Bool) : Data :=
  .record [("cap", .nat 11), ("keySlot", .nat 12), ("maxTokens", .nat 13), ("microPerKTok", .nat 14),
    ("model", .bytes "mm".toUTF8), ("resident", .bytes "rr".toUTF8), ("revoked", .bool revoked),
    ("windowMs", .nat 15)]

private def argD : Data :=
  .record [("cap", .nat 21), ("keySlot", .nat 22), ("maxTokens", .nat 23), ("microPerKTok", .nat 24),
    ("windowMs", .nat 25)]

private def rqD : Data :=
  .record [("agent", .digest .empty), ("notBefore", .nat 0), ("occasion", .inj "invoke" (.nat 0)),
    ("principal", .digest .empty), ("self", .digest .empty), ("validUntil", .nat 0)]

private def resultOf (m : Label) : Term :=
  .app (.app (.app (.get allowance.body m) (.var 2)) (.var 1)) (.var 0)

/-- Field `f` of the state half of method `m`'s result. -/
private def fieldOf (m : Label) (arg : Data) (st : Data) (f : Label) : Outcome :=
  eval [] fuel (.get (.get (resultOf m) "state") f) [rqD.toVal, arg.toVal, st.toVal]

/-- The calls half of method `m`'s result. -/
private def callsOf (m : Label) (arg : Data) (st : Data) : Outcome :=
  eval [] fuel (.get (resultOf m) "calls") [rqD.toVal, arg.toVal, st.toVal]

private def emptyIs : Outcome → Bool
  | .value (.record []) _ => true
  | _ => false

private def valIs : Data → Outcome → Bool
  | .nat n, .value (.nat m) _ => n == m
  | .bool b, .value (.bool c) _ => b == c
  | .bytes x, .value (.bytes y) _ => x == y
  | _, _ => false

private def get (d : Data) (f : Label) : Data :=
  match d with
  | .record fs => (fs.find? (·.1 == f)).map (·.2) |>.getD (.nat 0)
  | _ => .nat 0

/-- `revoke` sets `revoked` and keeps every other field; `set` takes the settable fields from its
argument and keeps `model`, `resident` and `revoked` (so a revoked allowance stays revoked). -/
theorem methods_write :
    ∀ rv ∈ [true, false], ∀ f ∈ fields.map (·.1),
      valIs (if f = "revoked" then .bool true else get (stD rv) f) (fieldOf "revoke" (.record []) (stD rv) f) &&
      valIs (if settable.contains f then get argD f else get (stD rv) f) (fieldOf "set" argD (stD rv) f) := by
  decide +kernel

/-- Neither method makes a call (LANG-33): each declares no call slot, and its calls half evaluates
to the empty record. -/
theorem methods_no_calls :
    ((match allowance.iface with | .record r => Row.find? "revoke" r | _ => none).bind
        (methodSig allowance.state) = some (unit, []) ∧
      (match allowance.iface with | .record r => Row.find? "set" r | _ => none).bind
        (methodSig allowance.state) = some (setTy, [])) ∧
    ∀ rv ∈ [true, false], (emptyIs (callsOf "revoke" (.record []) (stD rv)) && emptyIs (callsOf "set" argD (stD rv))) = true := by
  decide +kernel

/-- The package prints: `Print.package` gives it a text. -/
theorem allowance_prints : (Print.package allowance).isSome = true := by decide +kernel

/-- The text the operator installs reads back, by `Lang.Read`, as exactly the package. -/
theorem allowance_text_reads : ∃ s, Print.package allowance = some s ∧ Read.readPackage s = .ok allowance := by
  have hc : allowance.checkWith [] = .ok () := by
    have h := allowance_checks
    split at h
    · assumption
    · cases h
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp allowance_prints
  exact ⟨s, hs, Print.readPackage_checked (by simp) hc hs⟩

/-- The package has wire bytes (what `install` carries and `allowanceId` digests). -/
theorem allowance_encodes : (Wire.encodePackage allowance).isSome = true := by decide +kernel

/-! ## Read only from the operator's own, unrevoked objects -/

private theorem opt_beq {o : Option ByteArray} {b : ByteArray} (h : (o == some b) = true) : o = some b := by
  cases o with
  | none => cases h
  | some a =>
    cases a with | mk x => cases b with | mk y =>
    have : (x == y) = true := h
    simp only [beq_iff_eq] at this
    rw [this]

/-- What `allowanceOf` accepts: an object of the allowance package, owned by `operator`, whose
`revoked` reads `false`. -/
theorem allowanceOf_sound {pkgId operator : ByteArray} {c : Cell} {x : ByteArray × Broker.Allowance}
    (h : allowanceOf pkgId operator c = some x) :
    c.kind = Receive.kindObject ∧ c.slots.get Receive.slotPackage = some pkgId ∧
      c.slots.get Receive.slotOwner = some operator ∧ boolAt c.slots 6 = some false := by
  unfold allowanceOf at h
  dsimp only at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨hk, hp⟩, ho⟩ := hg
    refine ⟨hk, opt_beq hp, opt_beq ho, ?_⟩
    split at h
    · assumption
    · cases h
  · cases h

private theorem ba_self (x : ByteArray) : (x == x) = true := by
  cases x with | mk y => show (y == y) = true; simp

/-- The object KERNEL creates from a seed (its owner `owner`, its package `p`, no extra law) reads
back as exactly the allowance it was seeded with, named by the resident's directory name, for every
allowance whose fields LANG can carry. -/
theorem seed_reads {D : Type} (X : Receive.Ctx D) (owner p : D) {r : ByteArray} {a : Broker.Allowance}
    {s : Kernel.Slots} (h : seed r a = some s) :
    allowanceOf (X.env.bytes p) (X.env.bytes owner) (Receive.objectCell X owner (some p) [] s) =
      some (Controller.dirOf r, a) := by
  simp only [seed, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, rfl⟩ := h
  have d0 := Wire.decodeData_eq_ok_iff.mpr h0
  have d1 := Wire.decodeData_eq_ok_iff.mpr h1
  have d2 := Wire.decodeData_eq_ok_iff.mpr h2
  have d3 := Wire.decodeData_eq_ok_iff.mpr h3
  have d4 := Wire.decodeData_eq_ok_iff.mpr h4
  have d5 := Wire.decodeData_eq_ok_iff.mpr h5
  have d6 := Wire.decodeData_eq_ok_iff.mpr h6
  have d7 := Wire.decodeData_eq_ok_iff.mpr h7
  simp [allowanceOf, natAt, Allow.bytesAt, boolAt, Receive.objectCell, Receive.slotsOf, Receive.lawSlots,
    slotAt, Receive.stateBase, Receive.slotPackage, Receive.slotOwner, slots_get_set_eq,
    slots_get_set_ne, d0, d1, d2, d3, d4, d5, d6, d7, ba_self]

/-- The seed is the state LANG reads: `Lang.readState` over the package's own state row gives, at
each label, exactly that field of the allowance (so `seed`'s slot order is the state type's, and no
two fields can be swapped between what LANG and the broker read). -/
theorem seed_state {D : Type} (digestOf : ByteArray → Option D) {r : ByteArray} {a : Broker.Allowance}
    {s : Kernel.Slots} (h : seed r a = some s) :
    Lang.readState digestOf fields s = .ok (.record [("cap", .nat a.cap), ("keySlot", .nat a.keySlot),
      ("maxTokens", .nat a.maxTokens), ("microPerKTok", .nat a.microPerKTok), ("model", .bytes a.model),
      ("resident", .bytes r), ("revoked", .bool false), ("windowMs", .nat a.windowMs)]) := by
  simp only [seed, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7, rfl⟩ := h
  simp [Lang.readState, Lang.readState.go, Lang.digestsOk, Data.digests, fields, slotAt, Receive.stateBase, Kernel.Slots.get, List.lookup,
    Wire.decodeData_eq_ok_iff.mpr h0, Wire.decodeData_eq_ok_iff.mpr h1, Wire.decodeData_eq_ok_iff.mpr h2,
    Wire.decodeData_eq_ok_iff.mpr h3, Wire.decodeData_eq_ok_iff.mpr h4, Wire.decodeData_eq_ok_iff.mpr h5,
    Wire.decodeData_eq_ok_iff.mpr h6, Wire.decodeData_eq_ok_iff.mpr h7]

private def pid : ByteArray := "P".toUTF8
private def op : ByteArray := "O".toUTF8
private def alw : Broker.Allowance := ⟨"claude-m".toUTF8, 7, 1000, 60000, 5000, 100⟩
private def rid : ByteArray := ⟨#[0xab, 0x01]⟩

private def cellOf (pkg owner : ByteArray) (s : Kernel.Slots) : Cell :=
  { kind := Receive.kindObject, discipline := .ram,
    slots := Receive.slotsOf ([(Receive.slotPackage, pkg), (Receive.slotOwner, owner)] ++ s) }

private def readsAs (want : Option (ByteArray × Broker.Allowance)) (pkg owner : ByteArray)
    (s : Option Kernel.Slots) : Bool :=
  match s with
  | some s => allowanceOf pid op (cellOf pkg owner s) == want
  | none => false

/-- The seed reads back as the allowance it was built from, named by the resident's hex; another
owner's object, another package's object and a revoked one read as nothing. -/
theorem seed_teeth :
    readsAs (some ("ab01".toUTF8, alw)) pid op (seed rid alw) = true ∧
    readsAs none pid "Q".toUTF8 (seed rid alw) = true ∧
    readsAs none "Z".toUTF8 op (seed rid alw) = true ∧
    readsAs none pid op ((seed rid alw).bind fun s =>
      (Wire.encodeData .bool (.bool true)).map fun b => s.set (slotAt 6) b) = true := by
  decide +kernel

/-! ## Following the World: the broker's allowances are the World's -/

section Follow
variable {D : Type} [Ord D] [DecidableEq D]

theorem mem_update {E : Env D} {pkgId op : ByteArray} {w : World D}
    {cur : List (D × (ByteArray × Broker.Allowance))} {ids : List D} {i : D} {x : ByteArray × Broker.Allowance} :
    (i, x) ∈ update E pkgId op w cur ids ↔
      ((i, x) ∈ cur ∧ i ∉ ids) ∨ (i ∈ ids ∧ readAt E pkgId op w i = some x) := by
  simp only [update, List.mem_append, List.mem_filter, List.mem_filterMap, List.mem_eraseDups,
    Option.map_eq_some_iff, Prod.mk.injEq, Bool.not_eq_true']
  constructor
  · rintro (h | ⟨j, hj, y, hy, rfl, rfl⟩)
    · exact .inl ⟨h.1, by simpa using h.2⟩
    · exact .inr ⟨hj, hy⟩
  · rintro (h | ⟨hj, hy⟩)
    · exact .inl ⟨h.1, by simpa using h.2⟩
    · exact .inr ⟨i, hj, x, hy, rfl, rfl⟩

/-- Round 0: over ids `ids` from nothing, the bindings are exactly the readable allowances among them. -/
theorem update_start {E : Env D} {pkgId op : ByteArray} {w : World D} {ids : List D} (i : D)
    (x : ByteArray × Broker.Allowance) :
    (i, x) ∈ update E pkgId op w [] ids ↔ i ∈ ids ∧ readAt E pkgId op w i = some x := by
  rw [mem_update]; simp

/-- A batch `ts` folds `w` to `w'`: if `cur` held exactly the readable allowances of `w`, then
`update` over the batch's touched ids (what `hosting-broker` passes) holds exactly those of `w'`.
An id no Turn touched keeps its World entry (`fold_frame`), so keeping its binding is right. -/
theorem update_tracks {E : Env D} {pkgId op : ByteArray} {w w' : World D} {ts : List (Turn D)}
    {cur : List (D × (ByteArray × Broker.Allowance))}
    (hc : ∀ i x, (i, x) ∈ cur ↔ readAt E pkgId op w i = some x)
    (h : World.fold E w ts = .ok w') :
    ∀ i x, (i, x) ∈ update E pkgId op w' cur (Controller.touchedIds ts) ↔ readAt E pkgId op w' i = some x := by
  intro i x
  rw [mem_update]
  by_cases hi : i ∈ Controller.touchedIds ts
  · simp [hi]
  · have hr : readAt E pkgId op w' i = readAt E pkgId op w i := by
      unfold Allow.readAt World.live
      rw [Proofs.fold_frame h hi]
    simp [hi, hr, hc]

/-- `absorb` is `update` over the batch's touched ids: what the broker holds after a catch-up is
exactly the World's. -/
theorem absorb_tracks {E : Env D} {pkgId op : ByteArray} {w w' : World D} {ts : List (Turn D)}
    {cur : List (D × (ByteArray × Broker.Allowance))}
    (hc : ∀ i x, (i, x) ∈ cur ↔ readAt E pkgId op w i = some x)
    (h : World.fold E w ts = .ok w') :
    ∀ i x, (i, x) ∈ absorb E pkgId op w' cur ts ↔ readAt E pkgId op w' i = some x :=
  update_tracks hc h

/-- Round 0 misses nothing: in a canonical World (`World.Canon`, kept by every admitted Turn,
`fold_canon`), every live cell's id is in `Loop.allIds`. -/
theorem allIds_complete {E : Env D} {w : World D} (hw : w.Canon E) {i : D} {c : Cell}
    (h : w.live E i = some c) : i ∈ Loop.allIds w := by
  unfold World.live World.entry at h
  split at h
  · rename_i e he
    split at he
    · rename_i hg
      have hm := (Trie.mem_toList (trieSpec E) 0 w.trie hw.1 (.cell i) _).mpr hg
      simp only [Loop.allIds, World.cellIds, List.mem_filterMap]
      exact ⟨_, hm, rfl⟩
    · cases he
  · cases h

/-- So round 0 over `Loop.allIds` holds exactly the World's readable allowances. -/
theorem start_tracks {E : Env D} {pkgId op : ByteArray} {w : World D} (hw : w.Canon E) :
    ∀ i x, (i, x) ∈ update E pkgId op w [] (Loop.allIds w) ↔ readAt E pkgId op w i = some x := by
  intro i x
  rw [update_start]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    unfold Allow.readAt at h
    cases hl : w.live E i with
    | none => rw [hl] at h; cases h
    | some c => exact allIds_complete hw hl

/-! ### The tail's World is the fold of the Turns it reports -/

theorem runRooted_fold {E : Env D} {root : World D → D × D} :
    ∀ {i : Nat} {w w' : World D} {ps : List (Turn D × (D × D))},
      Nanodregg.Host.Record.runRooted (World.admit E) root i w ps = .ok w' → World.fold E w (ps.map (·.1)) = .ok w'
  | _, w, w', [], h => by simp [Nanodregg.Host.Record.runRooted] at h; subst h; simp [World.fold]
  | i, w, w', (t, r) :: rest, h => by
    simp only [Nanodregg.Host.Record.runRooted] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      split at h
      · exact fold_cons_ok.mpr ⟨w₁, h₁, runRooted_fold h⟩
      · cases h

theorem stepTurns_fold {E : Env D} {dc : Codec.Stream D} {root : World D → D × D} {w w' : World D}
    {r : ByteArray} {ps : List (Turn D × (D × D))}
    (h : Nanodregg.Host.Record.stepTurns dc (World.admit E) root w r = .ok (w', ps)) :
    World.fold E w (ps.map (·.1)) = .ok w' := by
  unfold Nanodregg.Host.Record.stepTurns at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact runRooted_fold hr

theorem absorbRecords_fold {E : Env D} {F' : Type}
    {step : World D → ByteArray → Except F' (World D × List (Turn D × (D × D)))}
    (hs : ∀ w r w' ps, step w r = .ok (w', ps) → World.fold E w (ps.map (·.1)) = .ok w') :
    ∀ {w w' : World D} {os os' : Array (List (Turn D × (D × D)))} {i : Nat} {rs : List ByteArray},
      Nanodregg.Host.absorbRecords step w os i rs = .ok (w', os') →
      ∃ new, os'.toList = os.toList ++ new ∧ World.fold E w (new.flatten.map (·.1)) = .ok w'
  | w, w', os, os', i, [], h => by
    simp [Nanodregg.Host.absorbRecords] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, by simp [World.fold]⟩
  | w, w', os, os', i, r :: rs, h => by
    simp only [Nanodregg.Host.absorbRecords] at h
    split at h
    · rename_i w₁ o h₁
      obtain ⟨new, hn, hf⟩ := absorbRecords_fold hs h
      refine ⟨o :: new, by simp [hn], ?_⟩
      simp only [List.flatten_cons, List.map_append]
      exact fold_append.mpr ⟨w₁, hs _ _ _ _ h₁, hf⟩
    · cases h

/-- One `Tail.next` step's pure half: the World the tail reaches is `World.fold` of exactly the
Turns it reports (`outs.toList.flatten.map Prod.fst`, what `hosting-broker`'s catch-up collects). -/
theorem tail_absorb_fold {E : Env D} {dc : Codec.Stream D} {root : World D → D × D} {s : Nanodregg.Host.Log.Sealer}
    {rm : Nat} {t t' : Nanodregg.Host.Tail (World D)} {log : ByteArray} {capped : Bool}
    {outs : Array (List (Turn D × (D × D)))}
    (h : Nanodregg.Host.Tail.absorb s rm (Nanodregg.Host.Record.stepTurns dc (World.admit E) root) t log capped = .ok (t', outs)) :
    World.fold E t.world (outs.toList.flatten.map Prod.fst) = .ok t'.world := by
  unfold Nanodregg.Host.Tail.absorb at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i w os hab
        split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨new, hn, hf⟩ := absorbRecords_fold (fun _ _ _ _ hh => stepTurns_fold hh) hab
          simpa [hn] using hf

end Follow

end Nanodregg.Hosting.Proofs.Allowance
