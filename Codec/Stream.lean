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

Integers are fixed width, little-endian. Lengths and counts are `u32` and every
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
  /-- LEB128, shortest form, below 2^32 (`Codec.Varint`). -/
  | varint
  | digest
  | bytes (max : Nat)
  | option (s : Shape)
  | product (a b : Shape)
  | sum (a b : Shape)
  | array (max : Nat) (s : Shape)
  /-- A refinement: same bytes as `s`, fewer accepted values. The shape cannot see inside its
  functions: what pins them is the refinement's lawfulness theorem (`Census.Refines`) and its codec
  vectors (`gates/codec-vectors.tsv`), and a change of meaning under the same bytes changes `name`
  (CODEC-28). -/
  | refine (name : String) (s : Shape)
  | framed (tag : Digest) (s : Shape)
  /-- One tag byte, then the shape that tag selects. -/
  | tagged (cases : List (UInt8 × Shape))
  /-- `Codec.Tree`: nodes of a tag, a payload of at most `max` bytes, at most `max` children, nested at
  most `depth` levels. -/
  | tree (max depth : Nat)
  /-- One byte from an enumerated set. -/
  | oneOf (codes : Array UInt8)
  /-- `s`, whose whole encoding is at most `limit` bytes. -/
  | within (limit : Nat) (s : Shape)
  /-- A byte string of at most `max` bytes behind a ONE-byte length (`Codec.Raw.bytes8`, `max < 256`): a
  rows key's bytes, a range prefix (KERNEL-46's `rowKeyBytes`). -/
  | bytes8 (max : Nat)
  /-- Two bytes, little-endian (`Codec.Raw.nat16`): a trie node's branching bit on a proof's path
  (KERNEL-49). -/
  | u16
  /-- Eight bytes, BIG-endian (`Stream.u64be`): a Lang datum's natural, so a relation key's bytes compare as its
  numbers (LANG-57). -/
  | u64be
  deriving Repr

/-- A byte string of at most `max` bytes. -/
abbrev Bytes (max : Nat) := { b : ByteArray // b.size ≤ max }

/-- An array of at most `max` elements. -/
abbrev Bounded (max : Nat) (α : Type) := { a : Array α // a.size ≤ max }

/-- A codec: `put v buf` appends `v`'s bytes to `buf`; `get b i` reads one value
starting at offset `i` and returns it with the offset just past it. -/
structure Stream (α : Type) where
  shape : Shape
  /-- The number of bytes `put` appends, computed without encoding. -/
  size : α → Nat
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
  size _ := 0
  put _ buf := buf
  get b i := if i ≤ b.size then .ok ((), i) else .error (.truncated i 0)

def u8 : Stream UInt8 where
  shape := .u8
  size _ := 1
  put v buf := buf.push v
  get b i := if h : i < b.size then .ok (b[i], i + 1) else .error (.truncated i 1)

/-- The `UInt32` whose little-endian bytes are `a b c d` (`a` least significant). -/
@[inline] def ofLE32 (a b c d : UInt8) : UInt32 :=
  ((d.toUInt32 * 256 + c.toUInt32) * 256 + b.toUInt32) * 256 + a.toUInt32

/-- The `UInt64` whose little-endian bytes are `a … h` (`a` least significant). -/
@[inline] def ofLE64 (a b c d e f g h : UInt8) : UInt64 :=
  ((((((h.toUInt64 * 256 + g.toUInt64) * 256 + f.toUInt64) * 256 + e.toUInt64) * 256
    + d.toUInt64) * 256 + c.toUInt64) * 256 + b.toUInt64) * 256 + a.toUInt64

/-- Four bytes, little-endian. -/
def u32 : Stream UInt32 where
  shape := .u32
  size _ := 4
  put v buf :=
    (((buf.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8
  get b i :=
    if h : i + 4 ≤ b.size then
      .ok (ofLE32 b[i] b[i+1] b[i+2] b[i+3], i + 4)
    else .error (.truncated i 4)

/-- Eight bytes, little-endian. -/
def u64 : Stream UInt64 where
  shape := .u64
  size _ := 8
  put v buf :=
    (((((((buf.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push
      (v >>> 24).toUInt8).push (v >>> 32).toUInt8).push (v >>> 40).toUInt8).push
      (v >>> 48).toUInt8).push (v >>> 56).toUInt8
  get b i :=
    if h : i + 8 ≤ b.size then
      .ok (ofLE64 b[i] b[i+1] b[i+2] b[i+3] b[i+4] b[i+5] b[i+6] b[i+7], i + 8)
    else .error (.truncated i 8)

/-- A 64-bit number as eight bytes, most significant first (LANG-57: a Lang datum's natural, so the
bytes of two keys compare as the numbers do). -/
def u64be : Stream UInt64 where
  shape := .u64be
  size _ := 8
  put v buf :=
    (((((((buf.push (v >>> 56).toUInt8).push (v >>> 48).toUInt8).push (v >>> 40).toUInt8).push
      (v >>> 32).toUInt8).push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push
      (v >>> 8).toUInt8).push v.toUInt8
  get b i :=
    if h : i + 8 ≤ b.size then
      .ok (ofLE64 b[i+7] b[i+6] b[i+5] b[i+4] b[i+3] b[i+2] b[i+1] b[i], i + 8)
    else .error (.truncated i 8)

/-- A digest: its 32 bytes, raw. -/
def digest : Stream Digest where
  shape := .digest
  size _ := 32
  put d buf := buf ++ d.bytes
  get b i :=
    if h : i + 32 ≤ b.size then
      .ok (⟨b.extract i (i + 32), by simp [ByteArray.size_extract]; omega⟩, i + 32)
    else .error (.truncated i 32)

/-- A byte string of at most `max` bytes: its `u32` length, then its bytes. -/
def bytesOf (max : Nat) (_fits : max < 2 ^ 32 := by decide) : Stream (Bytes max) where
  shape := .bytes max
  size v := 4 + v.val.size
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
  size
    | none => 1
    | some v => 1 + c.size v
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
  size v := a.size v.1 + c.size v.2
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
  size
    | .inl v => 1 + a.size v
    | .inr v => 1 + c.size v
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

/-- The bytes of a sequence of values, one after the other (the spec of `array`'s body). -/
def manyBytes (c : Stream α) (l : List α) : ByteArray := l.foldl (fun out x => c.put x out) ByteArray.empty

/-- At most `max` values: their `u32` count, then each value. -/
def array (max : Nat) (c : Stream α) (_fits : max < 2 ^ 32 := by decide) : Stream (Bounded max α) where
  shape := .array max c.shape
  size v := v.val.foldl (fun n x => n + c.size x) 4
  put v buf := v.val.foldl (fun out x => c.put x out) (u32.put (UInt32.ofNat v.val.size) buf)
  get b i :=
    match u32.get b i with
    | .error e => .error e
    | .ok (n, j) =>
      if n.toNat ≤ max then
        -- the count is the input's claim: reserve no more than the bytes left could hold
        match getMany c b n.toNat j (Array.emptyWithCapacity (min n.toNat (b.size - j))) with
        | .ok (a, k) =>
          if h : a.size ≤ max then .ok (⟨a, h⟩, k) else .error (.pastBound i max a.size)
        | .error e => .error e
      else .error (.pastBound i max n.toNat)

/-- The values of `c` that `accept` admits, viewed as `β`. `back` writes a `β` as the
`α` it came from. The `Lawful` proof requires `accept (back y) = some y` and
`accept x = some y → back y = x`: one spelling per value. -/
def refine (name : String) (c : Stream α) (accept : α → Option β) (back : β → α) : Stream β where
  shape := .refine name c.shape
  size v := c.size (back v)
  put v buf := c.put (back v) buf
  get b i :=
    match c.get b i with
    | .error e => .error e
    | .ok (x, j) => match accept x with
      | some y => .ok (y, j)
      | none => .error (.rejected i name)

/-- Eight bytes, little-endian two's complement: `u64` of the `Int64`'s bit pattern. Every 8-byte
input is one value, so the refinement refuses nothing (`i64_lawful`). -/
def i64 : Stream Int64 := refine "i64" u64 (fun x => some x.toInt64) Int64.toUInt64

/-- A byte from `codes`; any other byte is refused as `badTag`. -/
def oneOf (codes : Array UInt8) : Stream { b : UInt8 // codes.contains b = true } where
  shape := .oneOf codes
  size _ := 1
  put v buf := buf.push v.val
  get b i :=
    match u8.get b i with
    | .error e => .error e
    | .ok (t, j) => if h : codes.contains t = true then .ok (⟨t, h⟩, j) else .error (.badTag i t)

/-- The values of `c` whose whole encoding is at most `limit` bytes; a longer one is refused as
`pastBound` (a total bound over fields that are each bounded separately). -/
def within (limit : Nat) (c : Stream α) : Stream { v : α // c.size v ≤ limit } where
  shape := .within limit c.shape
  size v := c.size v.val
  put v buf := c.put v.val buf
  get b i :=
    match c.get b i with
    | .error e => .error e
    | .ok (v, j) => if h : c.size v ≤ limit then .ok (⟨v, h⟩, j) else .error (.pastBound i limit (j - i))

/-- `false` is 0, `true` is 1; every other byte is refused. -/
def bool : Stream Bool :=
  refine "bool" u8 (fun x => if x = 0 then some false else if x = 1 then some true else none)
    (fun v => if v then 1 else 0)

/-- `tag`'s 32 bytes, then the value. Any other 32 bytes are refused as `wrongFrame`. -/
def framed (tag : Digest) (c : Stream α) : Stream α where
  shape := .framed tag c.shape
  size v := 32 + c.size v
  put v buf := c.put v (buf ++ tag.bytes)
  get b i :=
    if i + 32 ≤ b.size then
      if b.extract i (i + 32) = tag.bytes then c.get b (i + 32) else .error (.wrongFrame i)
    else .error (.truncated i 32)

/-- One of several cases: its tag byte `code s`, then that case's value. `ofCode?` is the inverse of
`code`; a byte it does not know is refused as `badTag`. `all` lists the cases for the shape. -/
def tagged {σ : Type} {F : σ → Type} (all : List σ) (code : σ → UInt8) (ofCode? : UInt8 → Option σ)
    (c : (s : σ) → Stream (F s)) : Stream ((s : σ) × F s) where
  shape := .tagged (all.map fun s => (code s, (c s).shape))
  size v := 1 + (c v.1).size v.2
  put v buf := (c v.1).put v.2 (buf.push (code v.1))
  get b i :=
    match u8.get b i with
    | .error e => .error e
    | .ok (t, j) => match ofCode? t with
      | none => .error (.badTag i t)
      | some s => match (c s).get b j with
        | .ok (v, k) => .ok (⟨s, v⟩, k)
        | .error e => .error e

def finCode {n : Nat} (s : Fin n) : UInt8 := UInt8.ofNat s.val

def finOf? (n : Nat) (t : UInt8) : Option (Fin n) := if h : t.toNat < n then some ⟨t.toNat, h⟩ else none

/-- One of `n` cases, tagged by its index (one byte, for `n ≤ 256`). -/
def choice (n : Nat) {F : Fin n → Type} (c : (s : Fin n) → Stream (F s)) : Stream ((s : Fin n) × F s) :=
  tagged (List.finRange n) finCode (finOf? n) c

end Stream
end Nanodregg.Codec
