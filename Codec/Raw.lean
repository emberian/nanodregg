import Codec.Stream

/-!
# Raw — codecs over unbounded types, canonical on a domain

KERNEL's types carry plain `Nat`, `List` and `ByteArray` and check their bounds in `World.admit`
(`checkBounds`), not in the types. These codecs write any value, but read only values in their
domain: `nat64` reads naturals below 2^64, `rawBytes max` byte strings of at most `max` bytes, and
`rawList max c` lists of at most `max` elements of `c`'s domain. They are lawful ON that domain
(`Codec.Proofs.Raw`, `LawfulOn`): every value in the domain round-trips, and every value read is in the
domain and was spelled exactly one way. Outside the domain, `put` truncates, and nothing ever reads
such a value back.
-/

namespace Nanodregg.Codec.Stream

variable {α : Type}

/-- A natural as eight little-endian bytes (canonical below 2^64). -/
def nat64 : Stream Nat where
  shape := .u64
  size _ := 8
  put n buf := u64.put (UInt64.ofNat n) buf
  get b i :=
    match u64.get b i with
    | .ok (v, j) => .ok (v.toNat, j)
    | .error e => .error e

/-- A natural as four little-endian bytes (canonical below 2^32). -/
def nat32 : Stream Nat where
  shape := .u32
  size _ := 4
  put n buf := u32.put (UInt32.ofNat n) buf
  get b i :=
    match u32.get b i with
    | .ok (v, j) => .ok (v.toNat, j)
    | .error e => .error e

/-- `u32 len ‖ bytes`, at most `max` bytes (canonical for `max < 2^32`). -/
def rawBytes (max : Nat) : Stream ByteArray where
  shape := .bytes max
  size v := 4 + v.size
  put v buf := u32.put (UInt32.ofNat v.size) buf ++ v
  get b i :=
    match u32.get b i with
    | .error e => .error e
    | .ok (n, j) =>
      if n.toNat ≤ max then
        if j + n.toNat ≤ b.size then .ok (b.extract j (j + n.toNat), j + n.toNat)
        else .error (.truncated j n.toNat)
      else .error (.pastBound i max n.toNat)

/-- `u32 count ‖ value*`, at most `max` values. -/
def rawList (max : Nat) (c : Stream α) : Stream (List α) where
  shape := .array max c.shape
  size l := l.foldl (fun n x => n + c.size x) 4
  put l buf := l.foldl (fun out x => c.put x out) (u32.put (UInt32.ofNat l.length) buf)
  get b i :=
    match u32.get b i with
    | .error e => .error e
    | .ok (n, j) =>
      if n.toNat ≤ max then
        match getMany c b n.toNat j (Array.emptyWithCapacity n.toNat) with
        | .ok (a, k) => .ok (a.toList, k)
        | .error e => .error e
      else .error (.pastBound i max n.toNat)

end Nanodregg.Codec.Stream
