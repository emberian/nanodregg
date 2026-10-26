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
generator's run returns is `generate_run_sound` (`Lang.Proofs.StdGen`).

Rung 1 (LANG-87): the TEMPLATE generator. `boundedGenerator r f` takes `generate {max : nat}` and
installs `boundedPackage r f max` — a record state `r` under the law `bounded` (`f ≤ max`) with a
`set` method — for the `max` of its argument: its method is `Lang.Quote.quotePackage` over the
template `boundedPackageWith r f (var 4)`, whose one free variable is the bound at the law
clause's depth, written at run time by the `u64be` payload writer from `get arg "max"`.
`generate_bounded_sound` (`Lang.Proofs.StdGen`): the run returns `install` of exactly
`encodePackage (boundedPackage r f max)` — the nano generator IS the Lean generator at the
receipt's argument, byte for byte, so the law's theorem `bounded_spec` is about what the kernel
checked and installed.
-/
import Lang.StdHead
import Lang.Quote

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

/-! ## Rung 1: a template generator (LANG-87) -/

/-- `some (install {pkg = t})` in the generator's slot, the package bytes a term. -/
def installOf (t : Term) : Term :=
  someCallT installSlot (.inj installSlot "install" (.record [("pkg", t)]))

/-- `set`: `λ rows state arg req. {calls = {}, edits = {}, state = arg}`, the state record `r`'s
fields copied from the argument (`r` in canonical order, as a record type is). -/
def setMethod (r : List (Label × Ty)) : Term :=
  .lam (.record []) (.lam (.record r) (.lam (.record r) (.lam reqTy
    (resultT (callsT []) (.record (r.map fun (ℓ, _) => (ℓ, .get (.var 1) ℓ)))))))

/-- The template of `boundedPackage`: state `rec r`, the law `bounded` (field `f` at most `maxT`,
a term at the law clause's depth), the method `set`; rows in canonical order (`bounded` < `set`). -/
def boundedPackageWith (r : List (Label × Ty)) (f : Label) (maxT : Term) : Package :=
  { imports := [], state := .record r,
    iface := .record [("bounded", lawTy (.record r)), ("set", methodTy (.record r) (.record r))],
    body := .record [("bounded", boundedWith (.record r) f maxT), ("set", setMethod r)],
    methods := ["set"], laws := ["bounded"] }

/-- A record state `r` whose natural field `f` is at most `max`, written whole by `set`: the package
the template generator installs at `max`. -/
def boundedPackage (r : List (Label × Ty)) (f : Label) (max : Nat) : Package :=
  boundedPackageWith r f (natT max)

/-- The generator's one parameter: `max`, its argument's field, a natural. -/
def maxParam : Quote.Param := ⟨.nat, .get (.var 1) "max"⟩

/-- The argument of `generate`: `rec {max : nat}`. -/
def maxArgTy : Ty := .record [("max", .nat)]

/-- `generate`: `λ rows state arg req. {calls = {c0 = some (install {pkg = QUOTED})}, edits = {},
state = state}` where QUOTED writes `boundedPackageWith r f (var 4)`'s bytes with the free `var 4`
(the bound, under the law's three binders and the arm's) taken from `arg.max`. -/
def boundedGenerateMethod (r : List (Label × Ty)) (f : Label) : Term :=
  .lam (.record []) (.lam genStateTy (.lam maxArgTy (.lam reqTy
    (resultT (callsT [installOf
      (Quote.quotePackage [maxParam] (.bytes .empty) (boundedPackageWith r f (.var 4)))]) (.var 2)))))

/-- The template generator: `generate {max}` installs `boundedPackage r f max`. -/
def boundedGenerator (r : List (Label × Ty)) (f : Label) : Package :=
  { pkgOf genStateTy [] [("generate", maxArgTy, [installSlot], boundedGenerateMethod r f)] with
    doc := s!"installs a {f}-bounded record at the bound its argument names".toUTF8 }

end Nanodregg.Lang.Std
