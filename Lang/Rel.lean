/-
# Lang.Rel — a method's rows as data, and its edits as the kernel's row acts (LANG-49)

A relation's key is fixed-width data; its BYTES are the data encoding of its fields in declared
order (`keyWire`: positional labels `k0 …`, so the existing data codec, whose record is the
product of its fields, writes them), and a range's prefix is the encoding of the first fields. A
row's value bytes are the data encoding at the relation's value type; its `amt` is the value's
declared sum column (0 without one), a kernel field beside the bytes, so the kernel never parses
Lang data.

`readsData` builds a method's rows argument from the `RowView` (only the caller's pinned rows
and signed ranges under the object's own relations: law 5 by construction); `editsOf` reads the
edits row a method returned into row acts under the object.
-/
import Kernel.Receive.Call
import Lang.Package
import Lang.Wire.Data

namespace Nanodregg.Lang

open Nanodregg.Kernel
open Nanodregg.Kernel.Receive

/-- The key's first `m` declared fields at positional labels `k0 …` (at most `keyFieldsMax`
fields, so the labels ascend): the type its bytes are written at. -/
def keyWireTy (d : RelDecl) (m : Nat) : Ty :=
  .record ((d.key.take m).zipIdx.map fun p => ("k" ++ toString p.2, p.1.2))

/-- A key record (labels ascending) as data at `keyWireTy d d.key.length`. -/
def keyToWire (d : RelDecl) (key : Data) : Option Data :=
  (d.key.zipIdx.mapM fun p => (key.field p.1.1).map fun v => ("k" ++ toString p.2, v)).map .record

/-- A key's bytes (`none`: not a key of the relation). -/
def keyBytes (d : RelDecl) (key : Data) : Option ByteArray :=
  (keyToWire d key).bind (Wire.encodeData (keyWireTy d d.key.length))

/-- The bytes of a key's first `m` declared fields, as a range's prefix (PROTOCOL-51): the key
wire at `m` fields of `v`'s fields of those labels (`preBytes_full`: at every field, `keyBytes`). -/
def preBytes (d : RelDecl) (m : Nat) (v : Data) : Option ByteArray :=
  ((d.key.take m).zipIdx.mapM fun p => (v.field p.1.1).map fun x => ("k" ++ toString p.2, x)).bind
    fun fs => Wire.encodeData (keyWireTy d m) (.record fs)

/-- The first `m` fields read back from their bytes, as a record with the declared labels sorted. -/
def keyOf (d : RelDecl) (m : Nat) (b : ByteArray) : Except String Data :=
  match Wire.decodeData (keyWireTy d m) b with
  | .ok (.record fs) =>
    .ok (.record (Row.sort ((d.key.take m).zip fs |>.map fun p => (p.1.1, p.2.2))))
  | .ok _ => .error "key: not a record"
  | .error e => .error s!"key: {repr e}"

mutual
/-- The order a key field's values list in (LANG-57): a natural by value, `false` before `true`, a
digest shorter first and then bytewise, an enumeration by its arm (a canonical sum's arms ascend, so
by label), a record field by field in row order. `Lang.Proofs.KeyOrder.keyBytes_compare`: this is the
order of the key's BYTES, so it is the order a range read lists rows in. -/
def keyCmp : Ty → Data → Data → Ordering
  | .nat, .nat a, .nat b => compare a b
  | .bool, .bool a, .bool b => compare a b
  | .digest, .digest a, .digest b => (compare a.size b.size).then (compare a.data b.data)
  | .sum r, .inj a _, .inj b _ => compare (r.findIdx (·.1 == a)) (r.findIdx (·.1 == b))
  | .record r, .record fs, .record gs => keyRowCmp r fs gs
  | _, _, _ => .eq

def keyRowCmp : List (Label × Ty) → List (Label × Data) → List (Label × Data) → Ordering
  | (_, t) :: r, (_, a) :: fs, (_, b) :: gs => (keyCmp t a b).then (keyRowCmp r fs gs)
  | _, _, _ => .eq
end

/-- Two keys of a relation in its DECLARED order: field by field in the order the relation declares
them, each by `keyCmp` (LANG-57). -/
def keyOrder : List (Label × Ty) → Data → Data → Ordering
  | [], _, _ => .eq
  | (ℓ, t) :: r, k, k' =>
    match k.field ℓ, k'.field ℓ with
    | some a, some b => (keyCmp t a b).then (keyOrder r k k')
    | _, _ => .eq

/-- A row value's sum column (0 without one). -/
def amtOf (d : RelDecl) (v : Data) : Nat :=
  match d.sum with
  | none => 0
  | some f =>
    match v.field f with
    | some (.nat n) => n
    | _ => 0

/-- The data of an optional value. -/
def optD : Option Data → Data
  | none => .inj "none" (.record [])
  | some d => .inj "some" d

/-- `n` option slots labelled `c0 …` holding `xs` in order, the rest empty. -/
def slotsD (c : String) (n : Nat) (xs : List Data) : List (Label × Data) :=
  (slotLabels c n).zipIdx.map fun p => (p.1, optD xs[p.2]?)

/-- The index of a relation by label. -/
def relIndex (rels : List (Label × RelDecl)) (ℓ : Label) : Option Nat := rels.findIdx? (·.1 = ℓ)

section
variable {D : Type} (digestOf : ByteArray → Option D)

/-- Data entering a run: every digest in it a digest of the World (LANG-38). -/
def checked (what : String) (d : Data) : Except (Refusal D) Data :=
  if d.digests.all fun b => (digestOf b).isSome then .ok d else .error (.program s!"{what}: not a digest")

def liftS {α : Type} (what : String) : Except String α → Except (Refusal D) α
  | .ok a => .ok a
  | .error e => .error (.program s!"{what}: {e}")

/-- A row's value bytes read at the relation's value type. -/
def valOf (d : RelDecl) (what : String) (b : ByteArray) : Except (Refusal D) Data :=
  match Wire.decodeData d.val b with
  | .ok v => checked digestOf what v
  | .error e => .error (.program s!"{what}: value {repr e}")

/-- A range read's rows as data (LANG-49): each row's key read back at every key field (`keyOf`)
and its value at the relation's value type (`valOf`), both `checked`, in the listing's order. The
one conversion: a method's range slots (`relReads`) and a member's `read OBJ REL K` (PROTOCOL-51). -/
def rangeRowData (ℓ : Label) (d : RelDecl) (rows : List (RowSlot D × RowLeaf)) :
    Except (Refusal D) (List Data) :=
  rows.mapM fun r => do
    match r with
    | (.row key, .row _ v _) =>
      let kd ← checked digestOf s!"rows: {ℓ}: key" (← liftS s!"rows: {ℓ}" (keyOf d d.key.length key.k))
      pure (Data.record [("key", kd), ("val", ← valOf digestOf d s!"rows: {ℓ}" v)])
    | _ => throw (.program s!"rows: {ℓ}: not a row")

/-- One relation's reads: the caller's pins under it in pin order (at most `x.points`, else
refused), and its one signed range, if the method declares one (its `most` at most the method's
slots; exactly one signed range, else refused). -/
def relReads (rv : RowView D) (self : D) (i : Nat) (ℓ : Label) (d : RelDecl) (x : RelRead) :
    Except (Refusal D) Data := do
  let pts := rv.points self i
  unless pts.length ≤ x.points do throw (.program s!"rows: {ℓ}: {pts.length} pins past {x.points} slots")
  let ps ← pts.mapM fun p => do
    let key ← checked digestOf s!"rows: {ℓ}: key" (← liftS s!"rows: {ℓ}" (keyOf d d.key.length p.1))
    let val ← match p.2 with
      | none => pure none
      | some (.row _ v _) => some <$> valOf digestOf d s!"rows: {ℓ}" v
      | some (.head ..) => throw (.program s!"rows: {ℓ}: not a row")
    pure (Data.record [("key", key), ("val", optD val)])
  let range ← match x.range with
    | none => pure []
    | some (m, k) => do
      match ← rv.ranges self i with
      | [(pre, most, rows)] =>
        unless most ≤ k do throw (.program s!"rows: {ℓ}: range of {most} past {k} slots")
        let p ← checked digestOf s!"rows: {ℓ}: prefix" (← liftS s!"rows: {ℓ}: prefix" (keyOf d m pre))
        let rs ← rangeRowData digestOf ℓ d rows
        pure [("range", Data.record [("pre", p), ("rows", .record (slotsD "r" k rs))])]
      | [] => throw (.program s!"rows: {ℓ}: no signed range")
      | _ => throw (.program s!"rows: {ℓ}: two signed ranges")
  pure (.record (slotsD "p" x.points ps ++ range))

/-- A method's rows argument: for each relation it reads, `relReads`. -/
def readsData (rels : List (Label × RelDecl)) (rv : RowView D) (self : D) (rs : List (Label × RelRead)) :
    Except (Refusal D) Data := do
  let fs ← rs.mapM fun r => do
    let some i := relIndex rels r.1 | throw (.program s!"rows: no relation {r.1}")
    let some d := Row.find? r.1 rels | throw (.program s!"rows: no relation {r.1}")
    pure (r.1, ← relReads digestOf rv self i r.1 d r.2)
  pure (.record fs)

end

/-- One edit a method returned: its relation (index and declaration), the edit as the relation's
guard sees it (at `relEditTy`), and the kernel's row slot and act. -/
structure Edit (D : Type) where
  rel : Nat
  label : Label
  decl : RelDecl
  data : Data
  slot : RowSlot D
  act : RowAct

/-- The row act of one relation edit under `self`. -/
def editOf {D : Type} (rels : List (Label × RelDecl)) (self : D) (slot : Label) : Data → Except (Refusal D) (Edit D)
  | .inj ℓ e => do
    let some i := relIndex rels ℓ | throw (.program s!"edits: {slot}: no relation {ℓ}")
    let some d := Row.find? ℓ rels | throw (.program s!"edits: {slot}: no relation {ℓ}")
    let keyAt (key : Data) : Except (Refusal D) (RowSlot D) :=
      match keyBytes d key with
      | some k => .ok (.row ⟨self, i, k⟩)
      | none => .error (.program s!"edits: {slot}: key bytes")
    let valAt (v : Data) : Except (Refusal D) ByteArray :=
      match Wire.encodeData d.val v with
      | some b => .ok b
      | none => .error (.program s!"edits: {slot}: value bytes")
    match e with
    | .inj "insert" (.record [("key", key), ("val", v)]) =>
        pure ⟨i, ℓ, d, e, ← keyAt key, .insert (amtOf d v) (← valAt v)⟩
    | .inj "upsert" (.record [("key", key), ("val", v)]) =>
        pure ⟨i, ℓ, d, e, ← keyAt key, .upsert (amtOf d v) (← valAt v)⟩
    | .inj "retract" (.record [("key", key)]) =>
        if d.retract then pure ⟨i, ℓ, d, e, ← keyAt key, .retract⟩
        else throw (.program s!"edits: {slot}: {ℓ} is insert-only")
    | _ => throw (.program s!"edits: {slot}: not an edit")
  | _ => .error (.program s!"edits: {slot}: not an edit")

/-- The edits in the edits row a method returned, in slot order, `none` skipped. -/
def editsOf {D : Type} (rels : List (Label × RelDecl)) (self : D) : Data → Except (Refusal D) (List (Edit D))
  | .record fs => go fs
  | _ => .error (.program "edits: not a record")
where
  go : List (Label × Data) → Except (Refusal D) (List (Edit D))
    | [] => .ok []
    | (ℓ, o) :: fs =>
      match o with
      | .inj "none" (.record []) => go fs
      | .inj "some" e => do
        let x ← editOf rels self ℓ e
        pure (x :: (← go fs))
      | _ => .error (.program s!"edits: {ℓ}: not an option")

/-! ## What a guard sees (LANG-59): the edit, and the row now at the slot the caller pinned -/

/-- The pin under an edit's row slot: the caller's pin at its relation with its key bytes. -/
def pinAt {D : Type} (rv : RowView D) (self : D) (e : Edit D) : Option (ByteArray × Option RowLeaf) :=
  (rv.points self e.rel).find? fun p => decide (p.1 = e.slot.keyBytes)

/-- The old row a guard sees, at `optTy` of the relation's value type: the value of the row now at
the slot the caller pinned (the receiver's `RowView`, so a stale pin shows the current row; `valOf`,
the conversion `relReads` uses), `none` for a pinned-absent slot or for an insert with no pin. An upsert or retract with no pin has no old row: refused `rowUnpinned` with the receiver's
own parent, relation and key (`rowTouchesOf`'s refusal), so a caller that derives its pins from
refusals learns the row whatever the guard would say. -/
def guardOld {D : Type} (digestOf : ByteArray → Option D) (rv : RowView D) (self : D) (e : Edit D) :
    Except (Refusal D) Data :=
  match pinAt rv self e with
  | some (_, none) => .ok (optD none)
  | some (_, some (.row _ v _)) => (valOf digestOf e.decl s!"old: {e.label}" v).map fun x => optD (some x)
  | some (_, some (.head ..)) => .error (.program s!"old: {e.label}: not a row")
  | none =>
    if e.act.unpinned then .ok (optD none)
    else .error (.rowUnpinned e.slot.under.1 e.slot.under.2 e.slot.keyBytes)

/-- A guard's input, at `guardInTy`: the edit's data and its old row. -/
def guardIn (edit old : Data) : Data := .record [("edit", edit), ("old", old)]

end Nanodregg.Lang
