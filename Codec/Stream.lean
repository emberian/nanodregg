import Codec.Refusal
import Codec.Digest

/-! # Stream — the one codec family

A `Stream α` writes a value by appending its bytes to a buffer and reads one
value at an offset of a `ByteArray`, returning the offset after it. It never
copies its input to decode, never forms a `List UInt8`, and never re-encodes to
check itself: canonicity (`Codec.Stream.Lawful`, in `Codec.StreamLaws`) is a
theorem about each combinator, proved once.

Every codec carries its `Shape`. A tag is the hash of a label and a shape
(`Codec.Tag`), so a codec whose structure changes gets a new tag without anyone
editing a literal.

Integers are fixed width, big-endian. Lengths and counts are `u32` and every
variable-size value carries its bound in its type (`Bytes max`, `Bounded max α`):
a value past its bound cannot be built, so it cannot be written, and a length
past the bound is refused by name before anything is read. -/

namespace Nanodregg.Codec

/-- The structure of a codec, as data. -/
inductive Shape where
  | unit
  | u8
  | u32
  | u64
  | digest
  | bytes (max : Nat)
  | option (s : Shape)
  | product (a b : Shape)
  | sum (a b : Shape)
  | array (max : Nat) (s : Shape)
  /-- A refinement: same bytes as `s`, fewer accepted values. `name` must change
  whenever the accepted set changes; the shape cannot see inside a function. -/
  | refine (name : String) (s : Shape)
  | framed (tag : Digest) (s : Shape)
  deriving DecidableEq, Repr

/-- A byte string of at most `max` bytes. -/
abbrev Bytes (max : Nat) := { b : ByteArray // b.size ≤ max }

/-- An array of at most `max` elements. -/
abbrev Bounded (max : Nat) (α : Type) := { a : Array α // a.size ≤ max }

/-- A codec: `put v buf` appends `v`'s bytes to `buf`; `get b i` reads one value
starting at offset `i` and returns it with the offset just past it. -/
structure Stream (α : Type) where
  shape : Shape
  put : α → ByteArray → ByteArray
  get : ByteArray → Nat → Except Refusal (α × Nat)

namespace Stream

variable {α β : Type}

/-- The bytes of one value. -/
def bytes (c : Stream α) (v : α) : ByteArray := c.put v ByteArray.empty

/-- Decode a whole input: exactly one value, nothing after it. -/
def decode (c : Stream α) (b : ByteArray) : Except Refusal α :=
  match c.get b 0 with
  | .ok (v, j) => if j = b.size then .ok v else .error (.trailing j)
  | .error e => .error e

/-! ## Primitives -/

/-- The empty encoding of the one value of `Unit`. -/
def unit : Stream Unit where
  shape := .unit
  put _ buf := buf
  get b i := if i ≤ b.size then .ok ((), i) else .error (.truncated i 0)

def u8 : Stream UInt8 where
  shape := .u8
  put v buf := buf.push v
  get b i := if h : i < b.size then .ok (b[i], i + 1) else .error (.truncated i 1)

/-- The `UInt32` whose big-endian bytes are `a b c d`. -/
@[inline] def ofBE32 (a b c d : UInt8) : UInt32 :=
  ((a.toUInt32 * 256 + b.toUInt32) * 256 + c.toUInt32) * 256 + d.toUInt32

/-- The `UInt64` whose big-endian bytes are `a … h`. -/
@[inline] def ofBE64 (a b c d e f g h : UInt8) : UInt64 :=
  ((((((a.toUInt64 * 256 + b.toUInt64) * 256 + c.toUInt64) * 256 + d.toUInt64) * 256
    + e.toUInt64) * 256 + f.toUInt64) * 256 + g.toUInt64) * 256 + h.toUInt64

/-- Four bytes, big-endian. -/
def u32 : Stream UInt32 where
  shape := .u32
  put v buf :=
    (((buf.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8
  get b i :=
    if h : i + 4 ≤ b.size then
      .ok (ofBE32 b[i] b[i+1] b[i+2] b[i+3], i + 4)
    else .error (.truncated i 4)

/-- Eight bytes, big-endian. -/
def u64 : Stream UInt64 where
  shape := .u64
  put v buf :=
    (((((((buf.push (v >>> 56).toUInt8).push (v >>> 48).toUInt8).push (v >>> 40).toUInt8).push
      (v >>> 32).toUInt8).push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push
      (v >>> 8).toUInt8).push v.toUInt8
  get b i :=
    if h : i + 8 ≤ b.size then
      .ok (ofBE64 b[i] b[i+1] b[i+2] b[i+3] b[i+4] b[i+5] b[i+6] b[i+7], i + 8)
    else .error (.truncated i 8)

/-- A digest: its 32 bytes, raw. -/
def digest : Stream Digest where
  shape := .digest
  put d buf := buf ++ d.bytes
  get b i :=
    if h : i + 32 ≤ b.size then
      .ok (⟨b.extract i (i + 32), by simp [ByteArray.size_extract]; omega⟩, i + 32)
    else .error (.truncated i 32)

/-- A byte string of at most `max` bytes: its `u32` length, then its bytes. -/
def bytesOf (max : Nat) (_fits : max < 2 ^ 32 := by decide) : Stream (Bytes max) where
  shape := .bytes max
  put v buf := u32.put (UInt32.ofNat v.val.size) buf ++ v.val
  get b i :=
    match u32.get b i with
    | .error e => .error e
    | .ok (n, j) =>
      if hn : n.toNat ≤ max then
        if h : j + n.toNat ≤ b.size then
          .ok (⟨b.extract j (j + n.toNat), by simp [ByteArray.size_extract]; omega⟩, j + n.toNat)
        else .error (.truncated j n.toNat)
      else .error (.pastBound i max n.toNat)

/-! ## Combinators -/

/-- Tag byte 0 for none, 1 then the value for some. -/
def option (c : Stream α) : Stream (Option α) where
  shape := .option c.shape
  put
    | none, buf => buf.push 0
    | some v, buf => c.put v (buf.push 1)
  get b i :=
    match u8.get b i with
    | .error e => .error e
    | .ok (0, j) => .ok (none, j)
    | .ok (1, j) => match c.get b j with
      | .ok (v, k) => .ok (some v, k)
      | .error e => .error e
    | .ok (t, _) => .error (.badTag i t)

/-- One value after the other; no delimiter (each side knows its own end). -/
def product (a : Stream α) (c : Stream β) : Stream (α × β) where
  shape := .product a.shape c.shape
  put v buf := c.put v.2 (a.put v.1 buf)
  get b i :=
    match a.get b i with
    | .error e => .error e
    | .ok (x, j) => match c.get b j with
      | .ok (y, k) => .ok ((x, y), k)
      | .error e => .error e

/-- Tag byte 0 then the left value, or 1 then the right value. -/
def sum (a : Stream α) (c : Stream β) : Stream (α ⊕ β) where
  shape := .sum a.shape c.shape
  put
    | .inl v, buf => a.put v (buf.push 0)
    | .inr v, buf => c.put v (buf.push 1)
  get b i :=
    match u8.get b i with
    | .error e => .error e
    | .ok (0, j) => match a.get b j with
      | .ok (v, k) => .ok (.inl v, k)
      | .error e => .error e
    | .ok (1, j) => match c.get b j with
      | .ok (v, k) => .ok (.inr v, k)
      | .error e => .error e
    | .ok (t, _) => .error (.badTag i t)

/-- Read exactly `n` values starting at `i`, pushing onto `acc`. Structural in `n`. -/
def getMany (c : Stream α) (b : ByteArray) : Nat → Nat → Array α → Except Refusal (Array α × Nat)
  | 0, i, acc => .ok (acc, i)
  | n + 1, i, acc =>
    match c.get b i with
    | .ok (v, j) => getMany c b n j (acc.push v)
    | .error e => .error e

/-- At most `max` values: their `u32` count, then each value. -/
def array (max : Nat) (c : Stream α) (_fits : max < 2 ^ 32 := by decide) : Stream (Bounded max α) where
  shape := .array max c.shape
  put v buf := v.val.foldl (fun out x => c.put x out) (u32.put (UInt32.ofNat v.val.size) buf)
  get b i :=
    match u32.get b i with
    | .error e => .error e
    | .ok (n, j) =>
      if n.toNat ≤ max then
        match getMany c b n.toNat j (Array.emptyWithCapacity n.toNat) with
        | .ok (a, k) =>
          if h : a.size ≤ max then .ok (⟨a, h⟩, k) else .error (.pastBound i max a.size)
        | .error e => .error e
      else .error (.pastBound i max n.toNat)

/-- The values of `c` that `accept` admits, viewed as `β`. `back` writes a `β` as the
`α` it came from. The `Lawful` proof requires `accept (back y) = some y` and
`accept x = some y → back y = x`: one spelling per value. -/
def refine (name : String) (c : Stream α) (accept : α → Option β) (back : β → α) : Stream β where
  shape := .refine name c.shape
  put v buf := c.put (back v) buf
  get b i :=
    match c.get b i with
    | .error e => .error e
    | .ok (x, j) => match accept x with
      | some y => .ok (y, j)
      | none => .error (.rejected i name)

/-- `false` is 0, `true` is 1; every other byte is refused. -/
def bool : Stream Bool :=
  refine "bool" u8 (fun x => if x = 0 then some false else if x = 1 then some true else none)
    (fun v => if v then 1 else 0)

/-- `tag`'s 32 bytes, then the value. Any other 32 bytes are refused as `wrongFrame`. -/
def framed (tag : Digest) (c : Stream α) : Stream α where
  shape := .framed tag c.shape
  put v buf := c.put v (buf ++ tag.bytes)
  get b i :=
    if i + 32 ≤ b.size then
      if b.extract i (i + 32) = tag.bytes then c.get b (i + 32) else .error (.wrongFrame i)
    else .error (.truncated i 32)

end Stream
end Nanodregg.Codec
