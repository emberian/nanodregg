import Codec.Raw
import Kernel.World
import Kernel.Receive.Call

/-!
# Codec.Kernel — the canonical bytes of KERNEL's values

One codec per kernel type, built from the one Stream family. Each is generic in the digest's own
codec `dc : Stream D` (the deployed 32-byte digest, or a simulation's toy digest). Kernel types carry
plain `Nat`, `List` and `ByteArray` with bounds checked in `World.admit`. So each codec is lawful on
the values within those bounds (`Codec.Proofs.Kernel`): every admitted Turn has exactly one spelling,
and every decoded value is within bounds.

Layouts (all integers little-endian, every count a u32, every byte string `u32 len ‖ bytes`):
* `Op`: tag 0 ‖ key u32 ‖ value, or tag 1 ‖ key u32.
* `Cell`: kind u32 ‖ discipline u8 ‖ slots (count ‖ (key u32 ‖ value)*).
* `Act`: tag 0 (keep), tag 1 ‖ ops, or tag 2 (retire). `Touch`: cell ‖ seen ‖ act.
* `Turn`: txId ‖ notBefore u64 ‖ validUntil u64 ‖ touches ‖ creates (id ‖ cell each, D5) ‖ nullifiers ‖ charge u64 ‖
  event ‖ rows ‖ ranges.
* Rows (KERNEL-46/48): `RowSlot` as `rowKeyBytes` (parent ‖ rel u8 ‖ kind u8 [‖ u8 len ‖ key]); `RowLeaf` as
  `rowLeafBytes`; `RowAct`: a tag ‖ its fields; `RowTouch`: slot ‖ option seen ‖ act; `RangeRead`: parent ‖ rel u8 ‖
  u8 len ‖ prefix ‖ most u64 ‖ seen.
* `Call`: unsigned ‖ signature. `Unsigned`: member ‖ key ‖ notBefore ‖ validUntil ‖ pins ‖ maxCharge ‖
  body. `Body`: a tag (its constructor's index) ‖ its fields.
-/

namespace Nanodregg.Codec.Kernel

open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Codec.Stream

variable {D : Type}

/-! ## Bounds of the wire (KERNEL's bounds where they exist) -/

/-- A list or byte string inside a signed call: the call is one event, so nothing in it exceeds
`Bounds.eventBytesMax`. -/
def callMax : Nat := Bounds.eventBytesMax

/-! ## Cells -/

def discipline : Stream Discipline :=
  refine "kernel/discipline" u8
    (fun t => if t = 0 then some .rom else if t = 1 then some .appendOnly else if t = 2 then some .ram
      else if t = 3 then some .value else none)
    (fun | .rom => 0 | .appendOnly => 1 | .ram => 2 | .value => 3)

abbrev OpF : Fin 2 → Type
  | 0 => Nat × ByteArray
  | 1 => Nat

def opWire : (s : Fin 2) → Stream (OpF s)
  | 0 => product nat32 (rawBytes Bounds.valueBytesMax)
  | 1 => nat32

def op : Stream Op :=
  refine "kernel/op" (choice 2 opWire)
    (fun | ⟨0, (k, v)⟩ => some (.set k v) | ⟨1, k⟩ => some (.erase k))
    (fun | .set k v => ⟨0, (k, v)⟩ | .erase k => ⟨1, k⟩)

def slots : Stream Slots :=
  rawList Bounds.slotsPerCellMax (product nat32 (rawBytes Bounds.valueBytesMax))

def cell : Stream Cell :=
  refine "kernel/cell" (product nat32 (product discipline slots))
    (fun (k, d, s) => some ⟨k, d, s⟩) (fun c => (c.kind, c.discipline, c.slots))

/-! ## Touches -/

abbrev ActF : Fin 3 → Type
  | 0 => Unit
  | 1 => List Op
  | 2 => Unit

def actWire : (s : Fin 3) → Stream (ActF s)
  | 0 => unit
  | 1 => rawList Bounds.opsPerWriteMax op
  | 2 => unit

def act : Stream Act :=
  refine "kernel/act" (choice 3 actWire)
    (fun | ⟨0, ()⟩ => some .keep | ⟨1, ops⟩ => some (.write ops) | ⟨2, ()⟩ => some .retire)
    (fun | .keep => ⟨0, ()⟩ | .write ops => ⟨1, ops⟩ | .retire => ⟨2, ()⟩)

def touch (dc : Stream D) : Stream (Touch D) :=
  refine "kernel/touch" (product dc (product dc act))
    (fun (c, s, a) => some ⟨c, s, a⟩) (fun x => (x.cell, x.seen, x.act))

/-! ## Rows (KERNEL-46/48): keys and leaves spelled as the kernel spells them

`rowKey` writes exactly `rowKeyBytes` and `rowLeaf` exactly `rowLeafBytes`
(`Codec.Proofs.Rows.rowKeyBytes_eq`, `rowLeafBytes_eq`), so the bytes a rows trie routes and hashes
by are the bytes of a lawful codec: each is injective on its domain and reads back. -/

abbrev RowKindF : Fin 2 → Type
  | 0 => Unit
  | 1 => ByteArray

def rowKindWire : (s : Fin 2) → Stream (RowKindF s)
  | 0 => unit
  | 1 => bytes8 Bounds.keyBytesMax

/-- A rows key, as `rowKeyBytes`: the parent, the relation (one byte), the kind (0 a head, 1 a row),
and a row's key (its length byte, then its bytes, at most `Bounds.keyBytesMax`). -/
def rowKey (dc : Stream D) : Stream (RowSlot D) :=
  refine "kernel/row-key" (product dc (product nat8 (choice 2 rowKindWire)))
    (fun | (p, rel, ⟨0, ()⟩) => some (.head p rel) | (p, rel, ⟨1, k⟩) => some (.row ⟨p, rel, k⟩))
    (fun | .head p rel => (p, rel, ⟨0, ()⟩) | .row key => (key.parent, key.rel, ⟨1, key.k⟩))

abbrev RowLeafF : Fin 2 → Type
  | 0 => Nat × Nat × Nat × Nat × Nat × Bool
  | 1 => Nat × ByteArray

def rowLeafWire : (s : Fin 2) → Stream (RowLeafF s)
  | 0 => product nat64 (product nat64 (product nat64 (product nat64 (product nat64 bool))))
  | 1 => product nat64 (rawBytes Bounds.valueBytesMax)

/-- A rows leaf, as `rowLeafBytes`: a head (0) with its count, sum, limit, cap and width (u64 each)
and its retract flag; a row (1) with its `amt` (u64) and its value (u32 length, at most
`Bounds.valueBytesMax`). -/
def rowLeaf : Stream RowLeaf :=
  refine "kernel/row-leaf" (choice 2 rowLeafWire)
    (fun | ⟨0, (c, s, l, k, w, r)⟩ => some (.head c s l k w r) | ⟨1, (a, v)⟩ => some (.row a v))
    (fun | .head c s l k w r => ⟨0, (c, s, l, k, w, r)⟩ | .row a v => ⟨1, (a, v)⟩)

abbrev RowActF : Fin 5 → Type
  | 0 => Unit
  | 1 => Nat × ByteArray
  | 2 => Nat × ByteArray
  | 3 => Unit
  | 4 => Nat × Nat × Nat × Bool

def rowActWire : (s : Fin 5) → Stream (RowActF s)
  | 0 => unit
  | 1 => product nat64 (rawBytes Bounds.valueBytesMax)
  | 2 => product nat64 (rawBytes Bounds.valueBytesMax)
  | 3 => unit
  | 4 => product nat64 (product nat64 (product nat64 bool))

/-- A row act, tagged by its constructor's index: keep, insert amt v, upsert amt v, retract,
declare limit cap width retract. -/
def rowAct : Stream RowAct :=
  refine "kernel/row-act" (choice 5 rowActWire)
    (fun
      | ⟨0, ()⟩ => some .keep
      | ⟨1, (a, v)⟩ => some (.insert a v)
      | ⟨2, (a, v)⟩ => some (.upsert a v)
      | ⟨3, ()⟩ => some .retract
      | ⟨4, (l, c, w, r)⟩ => some (.declare l c w r))
    (fun
      | .keep => ⟨0, ()⟩
      | .insert a v => ⟨1, (a, v)⟩
      | .upsert a v => ⟨2, (a, v)⟩
      | .retract => ⟨3, ()⟩
      | .declare l c w r => ⟨4, (l, c, w, r)⟩)

/-- A row touch: the slot, the row pin the signer saw (if any), the act. -/
def rowTouch (dc : Stream D) : Stream (RowTouch D) :=
  refine "kernel/row-touch" (product (rowKey dc) (product (option dc) rowAct))
    (fun (s, p, a) => some ⟨s, p, a⟩) (fun x => (x.slot, x.seen, x.act))

/-- A range read: the parent, the relation (one byte), the key prefix (a length byte, then at most
`Bounds.keyBytesMax` bytes), `most` (u64), the range pin. -/
def rangeRead (dc : Stream D) : Stream (RangeRead D) :=
  refine "kernel/range-read" (product dc (product nat8 (product (bytes8 Bounds.keyBytesMax) (product nat64 dc))))
    (fun (p, rel, pre, m, s) => some ⟨p, rel, pre, m, s⟩) (fun q => (q.parent, q.rel, q.pre, q.most, q.seen))

/-- What a range pin hashes, as data: the parent, the relation, the width, the prefix, and each
listed row's key with its leaf digest. -/
abbrev RangePinWire (D : Type) := D × Nat × Nat × ByteArray × List (RowSlot D × D)

/-- The range pin's hash input, as `rangePinBytes` spells it: `rowsPrefix` (the parent, the
relation, the row kind byte 1, the width), the prefix (a length byte), and the listing (a u32 count,
then each row's key and leaf digest), at most `Bounds.rowsPerRelationMax` rows. The kind byte is read
as the one byte `oneOf #[1]` admits; every other byte is refused `badTag`. -/
def rangePinWire (dc : Stream D) : Stream (RangePinWire D) :=
  refine "kernel/range-pin"
    (product dc (product nat8 (product (oneOf #[1]) (product nat8 (product (bytes8 Bounds.keyBytesMax)
      (rawList Bounds.rowsPerRelationMax (product (rowKey dc) dc)))))))
    (fun (p, rel, _, w, pre, l) => some (p, rel, w, pre, l))
    (fun (p, rel, w, pre, l) => (p, rel, ⟨1, by simp⟩, w, pre, l))

/-! ## Turns -/

def turn (dc : Stream D) : Stream (Turn D) :=
  refine "kernel/turn"
    (product dc (product nat64 (product nat64 (product (rawList Bounds.touchesMax (touch dc))
      (product (rawList Bounds.createsMax (product dc cell)) (product (rawList Bounds.nullifiersMax dc)
        (product nat64 (product (rawBytes Bounds.eventBytesMax)
          (product (rawList Bounds.rowsMax (rowTouch dc)) (rawList Bounds.rangesMax (rangeRead dc)))))))))))
    (fun (tx, nb, vu, ts, cs, ns, ch, ev, rs, qs) => some ⟨tx, nb, vu, ts, cs, ns, ch, ev, rs, qs⟩)
    (fun t => (t.txId, t.notBefore, t.validUntil, t.touches, t.creates, t.nullifiers, t.charge, t.event, t.rows,
      t.ranges))

/-! ## Calls -/

def right : Stream Right :=
  refine "kernel/right" (choice 4 (F := fun s => match s with | 2 => Nat | 3 => Nat | _ => Unit)
      (fun s => match s with | 0 => unit | 1 => unit | 2 => nat64 | 3 => nat64))
    (fun | ⟨0, ()⟩ => some .observe | ⟨1, ()⟩ => some .mutate | ⟨2, m⟩ => some (.invoke m)
         | ⟨3, n⟩ => some (.enroll n))
    (fun | .observe => ⟨0, ()⟩ | .mutate => ⟨1, ()⟩ | .invoke m => ⟨2, m⟩ | .enroll n => ⟨3, n⟩)

abbrev AcctRefF (D : Type) : Fin 2 → Type
  | 0 => D
  | 1 => D × D

def acctRefWire (dc : Stream D) : (s : Fin 2) → Stream (AcctRefF D s)
  | 0 => dc
  | 1 => product dc dc

/-- An account reference (LEDGER-7): tag 0 a well by its denomination, tag 1 owner ‖ asset. -/
def acctRef (dc : Stream D) : Stream (AcctRef D) :=
  refine "kernel/acct-ref" (choice 2 (acctRefWire dc))
    (fun | ⟨0, a⟩ => some (.well a) | ⟨1, (o, a)⟩ => some (.of o a))
    (fun | .well a => ⟨0, a⟩ | .of o a => ⟨1, (o, a)⟩)

abbrev BodyF (D : Type) : Fin 13 → Type
  | 0 => ByteArray × D × ByteArray × D
  | 1 => ByteArray × D
  | 2 => ByteArray
  | 3 => Option D × List D × Slots
  | 4 => D × List (Nat × Option ByteArray) × Option D
  | 5 => D × List D × Option D
  | 6 => D × Nat × ByteArray × Nat × Option D
  | 7 => D × D × List Right × Option D
  | 8 => D
  | 9 => Nat
  | 10 => D × D
  | 11 => AcctRef D × AcctRef D × Nat × Option D × Option ByteArray
  | 12 => D × AcctRef D × Nat × Option D

def bodyWire (dc : Stream D) : (s : Fin 13) → Stream (BodyF D s)
  | 0 => product (rawBytes callMax) (product dc (product (rawBytes callMax) dc))
  | 1 => product (rawBytes callMax) dc
  | 2 => rawBytes callMax
  | 3 => product (option dc) (product (rawList callMax dc) slots)
  | 4 => product dc (product (rawList callMax (product nat32 (option (rawBytes Bounds.valueBytesMax))))
      (option dc))
  | 5 => product dc (product (rawList callMax dc) (option dc))
  | 6 => product dc (product nat64 (product (rawBytes callMax) (product nat64 (option dc))))
  | 7 => product dc (product dc (product (rawList callMax right) (option dc)))
  | 8 => dc
  | 9 => nat64
  | 10 => product dc dc
  | 11 => product (acctRef dc) (product (acctRef dc) (product nat64 (product (option dc) (option (rawBytes callMax)))))
  | 12 => product dc (product (acctRef dc) (product nat64 (option dc)))

def body (dc : Stream D) : Stream (Body D) :=
  refine "kernel/body" (choice 13 (bodyWire dc))
    (fun
      | ⟨0, (k, n, p, v)⟩ => some (.enroll k n p v)
      | ⟨1, (k, n)⟩ => some (.rotate k n)
      | ⟨2, p⟩ => some (.install p)
      | ⟨3, (p, ls, s)⟩ => some (.create p ls s)
      | ⟨4, (o, es, v)⟩ => some (.write o es v)
      | ⟨5, (o, ls, v)⟩ => some (.law o ls v)
      | ⟨6, (o, m, a, b, v)⟩ => some (.invoke o m a b v)
      | ⟨7, (t, g, r, p)⟩ => some (.grant t g r p)
      | ⟨8, g⟩ => some (.revoke g)
      | ⟨9, cap⟩ => some (.issue cap)
      | ⟨10, (a, o)⟩ => some (.account a o)
      | ⟨11, (s, d, n, v, o)⟩ => some (.transfer s d n v o)
      | ⟨12, (w, a, n, v)⟩ => some (.credit w a n v))
    (fun
      | .enroll k n p v => ⟨0, (k, n, p, v)⟩
      | .rotate k n => ⟨1, (k, n)⟩
      | .install p => ⟨2, p⟩
      | .create p ls s => ⟨3, (p, ls, s)⟩
      | .write o es v => ⟨4, (o, es, v)⟩
      | .law o ls v => ⟨5, (o, ls, v)⟩
      | .invoke o m a b v => ⟨6, (o, m, a, b, v)⟩
      | .grant t g r p => ⟨7, (t, g, r, p)⟩
      | .revoke g => ⟨8, g⟩
      | .issue cap => ⟨9, cap⟩
      | .account a o => ⟨10, (a, o)⟩
      | .transfer s d n v o => ⟨11, (s, d, n, v, o)⟩
      | .credit w a n v => ⟨12, (w, a, n, v)⟩)

def unsigned (dc : Stream D) : Stream (Unsigned D) :=
  refine "kernel/unsigned"
    (product dc (product dc (product (rawBytes callMax) (product nat64 (product nat64
      (product (rawList callMax (product dc dc)) (product nat64 (product (body dc)
        (product (rawList callMax (product (rowKey dc) dc)) (rawList callMax (rangeRead dc)))))))))))
    (fun (wo, m, k, nb, vu, ps, mc, b, rp, rq) => some ⟨wo, m, k, nb, vu, ps, mc, b, rp, rq⟩)
    (fun u => (u.world, u.member, u.key, u.notBefore, u.validUntil, u.pins, u.maxCharge, u.body, u.rowPins,
      u.ranges))

def call (dc : Stream D) : Stream (Call D) :=
  refine "kernel/call" (product (unsigned dc) (rawBytes callMax))
    (fun (u, s) => some ⟨u, s⟩) (fun c => (c.unsigned, c.signature))

/-! ## What KERNEL's `Env` and `Ctx` take -/

def cellBytes (c : Cell) : ByteArray := cell.bytes c
def turnBytes (dc : Stream D) (t : Turn D) : ByteArray := (turn dc).bytes t
def unsignedBytes (dc : Stream D) (u : Unsigned D) : ByteArray := (unsigned dc).bytes u
def callBytes (dc : Stream D) (c : Call D) : ByteArray := (call dc).bytes c

/-- A logged event read back as the call it is, refused by name otherwise. -/
def readCall (dc : Stream D) (b : ByteArray) : Except Refusal (Call D) := (call dc).decode b

/-- `readCall` as `Ctx.decodeCall` takes it. -/
def decodeCall (dc : Stream D) (b : ByteArray) : Option (Call D) :=
  match readCall dc b with
  | .ok c => some c
  | .error _ => none

end Nanodregg.Codec.Kernel
