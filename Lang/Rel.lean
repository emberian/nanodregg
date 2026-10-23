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

/-- Kernel cell `g` is LIVE in the caller's pinned view (E1): pinned, and neither a tombstone nor
absent (KERNEL-54's three pin domains). Never "at a version" (KERNEL-60).

C9 (LANG-75.2): a method's live read (`cellLive` at `pinned`) and the calls that run returns
(`spendVia` included) are the same Turn: `receive` takes one `pinned` view and `invoke` runs and derives
under it. That is the pin check plus one Turn; it is not a certificate the kernel consumes. In P8 the
checked cell is the provider grant and the spent cell is `cap`. Across Turns nothing is shared: the
journey row "P8.2s two-Turn split" records that the second Turn re-reads the cell and refuses. -/
def cellLive {D : Type} (look : Kernel.Receive.Pinned D) (g : D) : Bool :=
  match look g with
  | .ok (some _) => true
  | _ => false

/-- The kernel cell a cell-keyed relation's key names (`RelDecl.cellKeyed`): its one digest field. -/
def keyCell : Data → Option ByteArray
  | .record [(_, .digest b)] => some b
  | _ => none

/-- What a receipt read shows (E5, `seenTy`): a foreign World's committed call, its height, turn
digest and transaction id. -/
structure Seen where
  height : Nat
  turn : ByteArray
  tx : ByteArray
  deriving DecidableEq, Repr

/-- What the check shows fits the language's data (`seenTy`): a natural height, two digests. -/
def seenFits (s : Seen) : Bool :=
  decide (s.height < Bounds.natLimit) && decide (s.turn.size ≤ Bounds.digestBytesMax) &&
    decide (s.tx.size ≤ Bounds.digestBytesMax)

def seenData (s : Seen) : Data :=
  .record [("height", .nat s.height), ("turn", .digest s.turn), ("tx", .digest s.tx)]

/-- How a run checks a receipt (E5): the head object's cell and the receipt's bytes, to what it
shows, or the refusal's NAME. LANG declares it; PROTOCOL instantiates it (`Protocol.Foreign.check`,
`Receipt.check` against the head), the deployed `Host.Deployed.X` passes it. -/
abbrev ReceiptCheck := Kernel.Cell → ByteArray → Except String Seen

/-- The check of a program that verifies no receipt: every receipt read refuses `noReceipts`. -/
def noReceipts : ReceiptCheck := fun _ _ => .error "noReceipts"

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

/-- One pinned point read back: its key (`keyOf`, `checked`) and the row's value if the pin holds a
row (`valOf`); a head under a point is refused. -/
def readPoint (ℓ : Label) (d : RelDecl) (p : ByteArray × Option RowLeaf) :
    Except (Refusal D) (Data × Option Data) := do
  let key ← checked digestOf s!"rows: {ℓ}: key" (← liftS s!"rows: {ℓ}" (keyOf d d.key.length p.1))
  let val ← match p.2 with
    | none => pure none
    | some (.row _ v _) => some <$> valOf digestOf d s!"rows: {ℓ}" v
    | some (.head ..) => throw (.program s!"rows: {ℓ}: not a row")
  pure (key, val)

/-- THE receipt check of one read key (E5): the head object the key names, read through the
caller's pinned view (an unpinned cell is the kernel's `unpinned`; a retired one, `headDead`: how the
owner revokes a trust anchor), the method's `receipt` argument checked against it by the run's
`ReceiptCheck` (its refusal's name is the run's), and what it shows, entering only as the
language's data (law 4: `seenFits`, its digests digests of the World, LANG-38). A point and a range
row of a `(receipt)` read both take their column from here. -/
def receiptSeen (rc : ReceiptCheck) (look : Pinned D) (ℓ : Label) (args : Data) (k : Data) :
    Except (Refusal D) (D × Seen) :=
  match keyCell k with
  | none => .error (.program s!"rows: {ℓ}: not cell-keyed")
  | some b =>
    match digestOf b with
    | none => .error (.program s!"rows: {ℓ}: key: not a digest")
    | some g =>
      match look g with
      | .error e => .error e
      | .ok none => .error (.program "headDead")
      | .ok (some c) =>
        match args.field "receipt" with
        | some (.bytes rb) =>
          match rc c rb with
          | .ok s =>
            if seenFits s && (seenData s).digests.all (fun b => (digestOf b).isSome) then .ok (g, s)
            else .error (.program "receiptBounds")
          | .error why => .error (.program why)
        | _ => .error (.program "receiptRead")

/-- A point's record: its key and value; on a live read (E1, LANG-75.1) also whether the kernel
cell its key names is LIVE in the caller's pinned view. An unpinned cell is the kernel's own
`unpinned` refusal, by name. On a receipt read (E5) also the column `receiptSeen` shows. -/
def pointData (rc : ReceiptCheck) (look : Pinned D) (ℓ : Label) (live receipt : Bool) (args : Data)
    (kv : Data × Option Data) : Except (Refusal D) Data :=
  if receipt then
    match receiptSeen digestOf rc look ℓ args kv.1 with
    | .error e => .error e
    | .ok (g, s) =>
      .ok (.record ([("key", kv.1)] ++ (if live then [("live", .bool (cellLive look g))] else []) ++
        [("receipt", seenData s), ("val", optD kv.2)]))
  else if live then
    match keyCell kv.1 with
    | none => .error (.program s!"rows: {ℓ}: not cell-keyed")
    | some b =>
      match digestOf b with
      | none => .error (.program s!"rows: {ℓ}: key: not a digest")
      | some g =>
        match look g with
        | .error e => .error e
        | .ok _ => .ok (.record [("key", kv.1), ("live", .bool (cellLive look g)), ("val", optD kv.2)])
  else .ok (.record [("key", kv.1), ("val", optD kv.2)])

/-- A listed row of a `(receipt)` range read: its key, its column (`receiptSeen`), its value. -/
def receiptRow (rc : ReceiptCheck) (look : Pinned D) (ℓ : Label) (args : Data) : Data → Except (Refusal D) Data
  | .record [("key", k), ("val", v)] =>
    match receiptSeen digestOf rc look ℓ args k with
    | .error e => .error e
    | .ok (_, s) => .ok (.record [("key", k), ("receipt", seenData s), ("val", v)])
  | _ => .error (.program s!"rows: {ℓ}: not a row")

/-- A range read's rows, each with its column on a receipt read (E5), else as listed. -/
def receiptRows (rc : ReceiptCheck) (look : Pinned D) (ℓ : Label) (args : Data) (receipt : Bool)
    (rs : List Data) : Except (Refusal D) (List Data) :=
  if receipt then rs.mapM (receiptRow digestOf rc look ℓ args) else .ok rs

/-- One relation's reads: the caller's pins under it in pin order (at most `x.points`, else
refused), and its one signed range, if the method declares one (its `most` at most the method's
slots; exactly one signed range, else refused: none signed is `rangeUnpinned`, naming the relation). -/
def relReads (rc : ReceiptCheck) (look : Pinned D) (rv : RowView D) (self : D) (i : Nat) (ℓ : Label) (d : RelDecl)
    (x : RelRead) (args : Data) : Except (Refusal D) Data := do
  let pts := rv.points self i
  unless pts.length ≤ x.points do throw (.program s!"rows: {ℓ}: {pts.length} pins past {x.points} slots")
  let ps ← pts.mapM fun p => do pointData digestOf rc look ℓ x.live x.receipt args (← readPoint digestOf ℓ d p)
  let range ← match x.range with
    | none => pure []
    | some (m, k) => do
      match ← rv.ranges self i with
      | [(pre, most, rows)] =>
        unless most ≤ k do throw (.program s!"rows: {ℓ}: range of {most} past {k} slots")
        let p ← checked digestOf s!"rows: {ℓ}: prefix" (← liftS s!"rows: {ℓ}: prefix" (keyOf d m pre))
        let rs ← rangeRowData digestOf ℓ d rows
        let rs ← receiptRows digestOf rc look ℓ args x.receipt rs
        pure [("range", Data.record [("pre", p), ("rows", .record (slotsD "r" k rs))])]
      -- no range signed: the structured refusal, naming the relation (LANG-22 agreed, item 4)
      | [] => throw (.rangeUnpinned self i)
      | _ => throw (.program s!"rows: {ℓ}: two signed ranges")
  pure (.record (slotsD "p" x.points ps ++ range))

/-- A method's rows argument: for each relation it reads, `relReads`. -/
def readsData (rc : ReceiptCheck) (look : Pinned D) (rels : List (Label × RelDecl)) (rv : RowView D) (self : D)
    (rs : List (Label × RelRead)) (args : Data) :
    Except (Refusal D) Data := do
  let fs ← rs.mapM fun r => do
    let some i := relIndex rels r.1 | throw (.program s!"rows: no relation {r.1}")
    let some d := Row.find? r.1 rels | throw (.program s!"rows: no relation {r.1}")
    pure (r.1, ← relReads digestOf rc look rv self i r.1 d r.2 args)
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
