/-
# Lang.StdGen — a generator: a package whose method installs a package (DESIGN-META, LANG-86)

A GENERATOR is an ordinary package with a method whose calls row holds one `install` slot
(`installSlot`, the `install` arm of `callTy`, KERNEL-75): the method computes package bytes and
returns `install b`; the kernel's tree derives that call as the object, runs `checkInstall` on `b`
exactly as it does for a member's `install`, and bears the ROM cell `romIdOf b`. "Install a generated
package" is then a nested call of a Turn, re-derived by every follower, and the Turn is the receipt
of the generation: its journal row names the generator object and the argument, and the package
cell's id is the content digest of what the method returned.

This module holds rung 0 of the design (DESIGN-META §1.3): the CONSTANT generator `generatorOf b`,
whose `generate` returns `install b` for a fixed `b`. `headGenerator` is `Std.headPackage` as an
installed object: its one method installs exactly `headPackageBytes`, so the cell a generation bears
is `Protocol.Foreign.headPackageId` (`Lang.Journey.Gen` GN1 checks the two ids equal). What the
generator's run returns is `generate_run_sound` (`Lang.Proofs.StdGen`). Rung 1 (parameters spliced
into the package tree) needs the codec's framing as primitives and is a package-wire flag day
(DESIGN-META §3).
-/
import Lang.StdHead

namespace Nanodregg.Lang.Std

/-- The one call slot of a generator: `install`. -/
def installSlot : Ty := callOf ["install"]

/-- A generator keeps nothing. -/
def genStateTy : Ty := .record []

/-- `some (install b)` in the generator's slot. -/
def installT (b : ByteArray) : Term :=
  someCallT installSlot (.inj installSlot "install" (.record [("pkg", .bytes b)]))

/-- `generate`: `λ rows state arg req. {calls = {c0 = some (install b)}, edits = {}, state = state}`
(the state at `var 2`, as `methodOf` binds it); its type is `methodTy genStateTy (rec {}) [installSlot]`. -/
def generateMethod (b : ByteArray) : Term :=
  .lam (.record []) (.lam genStateTy (.lam (.record []) (.lam reqTy
    (resultT (callsT [installT b]) (.var 2)))))

/-- The constant generator of the package bytes `b`: one method, `generate` (index 0), no laws. -/
def generatorOf (b : ByteArray) (doc : String) : Package :=
  { pkgOf genStateTy [] [("generate", .record [], [installSlot], generateMethod b)] with doc := doc.toUTF8 }

/-- The bytes `Std.headPackage` installs as (`Protocol.Foreign.headPackageBytes` is this value, and
`headPackageId` its cell's id). -/
def headPackageBytes : ByteArray := (Wire.encodePackage headPackage).getD .empty

/-- `Std.head` as an installed object: the generator whose one method installs `headPackage`. -/
def headGenerator : Package :=
  generatorOf headPackageBytes
    "installs Std.head (a foreign World's head, keyed by steps, E5): the cell it bears is headPackageId"

end Nanodregg.Lang.Std
