# proposals/codec.md — CODEC's interface, as committed (BUILD-CODEC, 2026-10-16)

Everything below is on main unless it is marked NEXT. Signatures are copied from the source, not
paraphrased.

## Committed (Codec/Refusal.lean, Codec/Digest.lean, Codec/Stream.lean, Codec/Proofs/Stream.lean)

```lean
namespace Nanodregg.Codec

inductive Refusal
  | truncated (offset need : Nat) | trailing (offset : Nat) | pastBound (offset limit got : Nat)
  | badTag (offset : Nat) (tag : UInt8) | wrongFrame (offset : Nat) | rejected (offset : Nat) (name : String)

structure Digest where
  bytes : ByteArray
  size_eq : bytes.size = 32
-- DecidableEq, Hashable, Ord (lexicographic), Repr; Digest.ofBytes? : ByteArray → Option Digest;
-- Digest.bit (d) (k : Fin 256) : Bool (MSB of byte 0 first); Digest.byte; Digest.toHex; Digest.zero

abbrev Bytes (max : Nat) := { b : ByteArray // b.size ≤ max }
abbrev Bounded (max : Nat) (α : Type) := { a : Array α // a.size ≤ max }

structure Stream (α : Type) where
  shape : Shape
  put : α → ByteArray → ByteArray                       -- append v's bytes to buf
  get : ByteArray → Nat → Except Refusal (α × Nat)      -- read one value at an offset

Stream.bytes  (c : Stream α) (v : α) : ByteArray        -- = c.put v .empty
Stream.decode (c : Stream α) (b : ByteArray) : Except Refusal α   -- exactly one value; else .trailing

Stream.unit : Stream Unit          Stream.u8  : Stream UInt8
Stream.u32  : Stream UInt32        Stream.u64 : Stream UInt64          -- little-endian
Stream.digest : Stream Digest                                          -- 32 raw bytes
Stream.bytesOf (max : Nat) (_ : max < 2^32 := by decide) : Stream (Bytes max)   -- u32 length ‖ bytes
Stream.option  (c : Stream α) : Stream (Option α)                      -- 0 | 1 ‖ v
Stream.product (a : Stream α) (c : Stream β) : Stream (α × β)
Stream.sum     (a : Stream α) (c : Stream β) : Stream (α ⊕ β)          -- 0 ‖ a | 1 ‖ b
Stream.array (max : Nat) (c : Stream α) (_ : max < 2^32 := by decide) : Stream (Bounded max α)
Stream.refine (name : String) (c : Stream α) (accept : α → Option β) (back : β → α) : Stream β
Stream.bool : Stream Bool                                              -- 0 | 1, else .rejected
Stream.framed (tag : Digest) (c : Stream α) : Stream α                 -- tag's 32 bytes ‖ v

-- Codec.Proofs.Stream
def OccursAt (b : ByteArray) (i : Nat) (w : ByteArray) : Prop :=
  i + w.size ≤ b.size ∧ b.extract i (i + w.size) = w
structure Lawful (c : Stream α) : Prop where
  put_eq : ∀ v buf, c.put v buf = buf ++ c.bytes v
  get_of_occurs : ∀ v b i, OccursAt b i (c.bytes v) → c.get b i = .ok (v, i + (c.bytes v).size)
  occurs_of_get : ∀ {b i v j}, c.get b i = .ok (v, j) → j = i + (c.bytes v).size ∧ OccursAt b i (c.bytes v)
theorem decode_eq_ok_iff (hc : Lawful c) : c.decode b = .ok v ↔ b = c.bytes v
theorem decode_bytes (hc : Lawful c) (v) : c.decode (c.bytes v) = .ok v
theorem eq_bytes_of_decode (hc : Lawful c) : c.decode b = .ok v → b = c.bytes v
theorem bytes_injective (hc : Lawful c) : c.bytes v = c.bytes w → v = w
-- unit_lawful u8_lawful u32_lawful u64_lawful digest_lawful bool_lawful (bytesOf_lawful max fits)
-- (option_lawful hc) (product_lawful ha hc) (sum_lawful ha hc) (array_lawful hc max fits)
-- (framed_lawful hc tag) (refine_lawful hc name accept_back back_accept)
```

How to write a codec for a structure: build it from `product`/`refine`, and prove Lawful by composing
the combinator theorems. For example, a 3-field record is `refine "T" (product a (product b c)) (fun
(x, y, z) => some ⟨x, y, z⟩) (fun t => (t.1, t.2, t.3))`, with `accept_back`/`back_accept` by
`rfl`/`cases`. An enum is `refine "E" u8 ofTag? toTag`.

For HOST: `u32le`/`u64le` are `Stream.u32`/`Stream.u64` (`(u32.bytes v)` is 4 bytes LE). Host/Log's
private `le32` (HOST-5) can be deleted.

## NEXT (in this order)

```lean
-- Codec/Hash.lean
def Hash.cshake256 (domain : String) (msg : ByteArray) : Digest
def Hash.kmac256 (key : Digest) (domain : String) (msg : ByteArray) : Digest   -- HOST's Sealer.tag
-- Codec/Tag.lean
def Tag.of (label : String) (c : Stream α) : Digest      -- cshake256 "nanodregg/tag" (label ‖ shape bytes)
-- Codec/Deployed.lean (imports Kernel; nothing in Kernel imports it)
def turn  : Stream (Kernel.Turn Digest)      theorem turn_lawful  : Lawful turn
def cell  : Stream Kernel.Cell               theorem cell_lawful  : Lawful cell
def delta : Stream Kernel.Delta              -- HOST-8: touched cells + system cell against a base
def env   : Kernel.Env Digest                -- hash := cshake256, bytes := Digest.bytes, turnBytes, cellBytes
```
