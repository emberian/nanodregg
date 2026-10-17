/-!
# Codec.Path — a sandbox path: clean components, joined by `/`

A path relative to an operator's root is a list of components; on the wire it is ONE byte string,
the components joined by `/` (47), so the Rust side hands exactly those bytes to the sandbox and
assembles nothing (law 2). A component is CLEAN: nonempty, at most `componentMax` bytes, not `.`
or `..`, and free of the `forbidden` bytes (`/` and NUL). Over clean components the join is
injective and `split` inverts it (`Codec.Proofs.Path`), so the wire spelling is canonical.

`clean`, `join` and `split` index the bytes directly (no `List UInt8`, law 3) and are structural on
the size, so they reduce in the kernel: a `decide` over a literal path checks. The Rust emitter
prints the same rule from `componentMax`, `forbidden` and `reserved`.
-/
namespace Nanodregg.Codec.Path

/-- The longest component, in bytes. -/
def componentMax : Nat := 64

/-- The separator. -/
def sep : UInt8 := 47

/-- NUL. -/
def nul : UInt8 := 0

/-- The bytes no component may contain: the separator and NUL. -/
def forbidden (b : UInt8) : Bool := b == sep || b == nul

/-- No byte of `c` from index `i` on, for `n` more bytes, is forbidden. -/
def freeFrom (c : ByteArray) (i : Nat) : (n : Nat) → Bool
  | 0 => true
  | n + 1 => (if h : i < c.size then !forbidden c[i] else true) && freeFrom c (i + 1) n

/-- Do `c` and `w` agree on `n` bytes from index `i`? -/
def agreeFrom (c w : ByteArray) (i : Nat) : (n : Nat) → Bool
  | 0 => true
  | n + 1 => (if h : i < c.size then if h' : i < w.size then c[i] == w[i] else false else false) &&
      agreeFrom c w (i + 1) n

/-- Is `c` exactly the bytes `w`? -/
def isWord (c w : ByteArray) : Bool := c.size == w.size && agreeFrom c w 0 w.size

/-- The components that name directories themselves: `.` and `..`. -/
def dot : ByteArray := ⟨#[46]⟩
def dotdot : ByteArray := ⟨#[46, 46]⟩

/-- One clean component. -/
def clean (c : ByteArray) : Bool :=
  c.size != 0 && c.size ≤ componentMax && !isWord c dot && !isWord c dotdot && freeFrom c 0 c.size

/-- The components, joined by the separator. -/
def join : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | [c] => c
  | c :: cs => c ++ ByteArray.mk #[sep] ++ join cs

/-- The components of `b` from a segment starting at `start`, scanning `i` with `n` bytes left. -/
def splitFrom (b : ByteArray) (start i : Nat) : (n : Nat) → List ByteArray
  | 0 => [b.extract start i]
  | n + 1 =>
      if (if h : i < b.size then b[i] == sep else false) then b.extract start i :: splitFrom b (i + 1) (i + 1) n
      else splitFrom b start (i + 1) n

/-- The components of a joined path; the empty string is the empty path. -/
def split (b : ByteArray) : List ByteArray :=
  if b.size = 0 then [] else splitFrom b 0 0 b.size

/-- A path whose every component is clean and whose joined bytes fit `max`. -/
def fits (max : Nat) (p : List ByteArray) : Bool := p.all clean && decide ((join p).size ≤ max)

end Nanodregg.Codec.Path
