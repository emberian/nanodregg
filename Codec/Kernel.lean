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
* `Turn`: txId ‖ notBefore u64 ‖ validUntil u64 ‖ touches ‖ creates (id ‖ cell each, D5) ‖ nullifiers ‖ charge u64 ‖ event.
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

/-! ## Turns -/

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

def turn (dc : Stream D) : Stream (Turn D) :=
  refine "kernel/turn"
    (product dc (product nat64 (product nat64 (product (rawList Bounds.touchesMax (touch dc))
      (product (rawList Bounds.createsMax (product dc cell)) (product (rawList Bounds.nullifiersMax dc)
        (product nat64 (rawBytes Bounds.eventBytesMax))))))))
    (fun (tx, nb, vu, ts, cs, ns, ch, ev) => some ⟨tx, nb, vu, ts, cs, ns, ch, ev⟩)
    (fun t => (t.txId, t.notBefore, t.validUntil, t.touches, t.creates, t.nullifiers, t.charge, t.event))

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
  refine "kernel/unsigned/v2"
    (product dc (product dc (product (rawBytes callMax) (product nat64 (product nat64
      (product (rawList callMax (product dc dc)) (product nat64 (body dc))))))))
    (fun (wo, m, k, nb, vu, ps, mc, b) => some ⟨wo, m, k, nb, vu, ps, mc, b⟩)
    (fun u => (u.world, u.member, u.key, u.notBefore, u.validUntil, u.pins, u.maxCharge, u.body))

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
