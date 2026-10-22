/-
# Lang.Bounds — the static bounds of the language (law 4)

Every value a program can build is bounded: a natural is below `2^64`, a byte string fits one
kernel slot. An arithmetic result outside a bound is a named fault (`Lang.Fault`), never a wrap and
never an unbounded allocation. A bound on a value is not a bound on the work of one tick: a byte
string may be 64 KiB, so a primitive that walks one is charged a tick per `wordBytes` it walks
(`Lang.primTicks`, LANG-64).
-/
import Kernel.Bounds

namespace Nanodregg.Lang.Bounds

/-- Naturals are below `2^64`. -/
def natLimit : Nat := 18446744073709551616

/-- A byte string fits one kernel slot value. -/
def bytesMax : Nat := Kernel.Bounds.valueBytesMax

/-- A digest is at most 32 bytes: the deployed digest is 32, the Sim's 8. Whether bytes of that
size ARE a digest is the World's `digestOf`, asked where an id enters a run (LANG-38). -/
def digestBytesMax : Nat := 32

/-- The bytes one tick may walk (LANG-64): a primitive that reads or writes `n` operand bytes is
charged `⌈n / wordBytes⌉` ticks, at least one (`Lang.primTicks`), so a run walks at most
`wordBytes` primitive operand bytes per tick it is charged (`Lang.Proofs.Cost.walked_le`). -/
def wordBytes : Nat := 32

/-- A contextual hole's ROM lists at most this many candidate codes (`HoleROM.check`, LANG-P7). -/
def holeCandidatesMax : Nat := 64

/-- A package declares at most this many contextual holes (`Package.checkContextual`, LANG-P7). -/
def holeSignatureMax : Nat := 16

/-- The guard allowance of one contextual hole (LANG-P7): the ticks its selection guard may run
(`runHoleGuard`'s fuel), and so the preparation charged per declared hole (`Package.holeCharge`). One
allowance, two uses; not `reasonMax`/`docMax`, which are other facts that happen to be 256 too. -/
def holeGuardFuel : Nat := 256

/-- The machine's stack bound. A consensus constant, not part of a budget: two executors given
different tick budgets agree on every final outcome (`Lang.Proofs.Run.run_agree`) only because
they share this bound. -/
def stackMax : Nat := 4096

/-- A refusal's name (`Term.refuse`, LANG-51): at most this many bytes, printable UTF-8 (no control
character), so the name a program wrote is exactly the name every reader shows, on one line. -/
def reasonMax : Nat := 256

def reasonOk (w : ByteArray) : Bool :=
  decide (w.size ≤ reasonMax) &&
    match String.fromUTF8? w with
    | some s => s.toList.all fun c => 32 ≤ c.toNat && c.toNat ≠ 127
    | none => false

/-- A character a package's doc may hold: printable (no control character, so the doc is one line) and
not `"` (so the one printer writes it as `"text"`, never `#hex`). The same test as `Print.plainChar`
(`Lang.Proofs.Print.docChar_eq`). -/
def docChar (c : Char) : Bool := decide (32 ≤ c.toNat) && c.toNat != 127 && c != '"'

/-- A package's doc (LANG-60): at most this many bytes. What a describe prints on its `doc` line. -/
def docMax : Nat := 256

/-- A doc a package may carry: at most `docMax` bytes of UTF-8 doc characters. The empty doc is one. -/
def docOk (w : ByteArray) : Bool :=
  decide (w.size ≤ docMax) &&
    match String.fromUTF8? w with
    | some s => s.toList.all docChar
    | none => false

/-- The package wire's version (LANG-60): the first byte of every package's bytes. Bumped by every
`lang!` that changes what package bytes mean, so a package written at another version is refused
`lang/package-version/5` by name, never read as a different package. The package codec's label is
`lang/package/N` at version N (`Lang.Proofs.Wire.packageCodec_label`), so the bump moves the vectors'
tag too. 3: LANG-60 (a doc, and this byte); the unversioned wires before it were `lang/package` and
`lang/package/2` (LANG-59), each a node-0 tree whose first byte is 0, which no version may be. 4: the
contextual ROM section (d7989d9). 5: a ROM pin may name a kernel CELL (`SupportPin.cell`, E1, LANG-75.1). -/
def packageWireVersion : UInt8 := 5

end Nanodregg.Lang.Bounds
