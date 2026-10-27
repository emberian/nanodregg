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

/-! ## Template generators, in general (LANG-88.1) -/

/-- `generate`: `λ rows state arg req. {calls = {c0 = some (install {pkg = QUOTED})}, edits = {},
state = state}` where QUOTED writes the template `p`'s bytes with its free variables taken from the
parameters `ps` (terms over this environment: `arg` at `var 1`, `req` at `var 0`). -/
def templateMethod (A : Ty) (ps : List Quote.Param) (p : Package) : Term :=
  .lam (.record []) (.lam genStateTy (.lam A (.lam reqTy
    (resultT (callsT [installOf (Quote.quotePackage ps (.bytes .empty) p)]) (.var 2)))))

/-- A TEMPLATE GENERATOR: one method `generate : A`, no state, no laws, whose run installs the
template `p` filled at the parameters' values (`generate_template_sound`). -/
def templateGenerator (A : Ty) (ps : List Quote.Param) (p : Package) (doc : String) : Package :=
  { pkgOf genStateTy [] [("generate", A, [installSlot], templateMethod A ps p)] with doc := doc.toUTF8 }

/-- The bounded generator: `generate {max}` installs `boundedPackage r f max` — the template at the
bound, under the law's three binders and the arm's, taken from `arg.max`. -/
def boundedGenerator (r : List (Label × Ty)) (f : Label) : Package :=
  templateGenerator maxArgTy [maxParam] (boundedPackageWith r f (.var 4))
    s!"installs a {f}-bounded record at the bound its argument names"

/-! ## A generator whose output names its invoker (LANG-88): authority by naming, from the receipt -/

/-- The template of `ownedPackage`: state `rec r` under the one-member allowlist `owner` (the
member a term at the clause's depth), with `set`; rows in canonical order (`owner` < `set`). -/
def ownedPackageWith (r : List (Label × Ty)) (idT : Term) : Package :=
  { imports := [], state := .record r,
    iface := .record [("owner", lawTy (.record r)), ("set", methodTy (.record r) (.record r))],
    body := .record [("owner", allowlistWith (.record r) idT), ("set", setMethod r)],
    methods := ["set"], laws := ["owner"] }

/-- A record state `r` that only the member `i` may create, change or re-law, written whole by
`set`: what `ownerGenerator` installs for the member who invoked it. -/
def ownedPackage (r : List (Label × Ty)) (i : ByteArray) : Package := ownedPackageWith r (.digest i)

/-- The generator's one parameter: its invoker, `req.agent` — a digest the generator holds without
any argument, written into the law by `dsized`. -/
def agentParam : Quote.Param := ⟨.digest, .get (.var 0) "agent"⟩

/-- The generator whose output names its invoker: `generate {}` installs `ownedPackage r (the
signer's id)` — the template at `req.agent`. The receipt (the Turn's signer) is the only input; a
member who generates gets a package only they may use, and the package's text says who, by id. -/
def ownerGenerator (r : List (Label × Ty)) : Package :=
  templateGenerator (.record []) [agentParam] (ownedPackageWith r (.var 4))
    "installs a record only its generating member may use: the allowlist names the invoker"

/-! ## Generate AND instantiate in one Turn (LANG-96, KERNEL-77): `createOf` -/

/-- `some (createOf {pkg = PKG, state = STATE})` in the creator's slot, both terms. -/
def createOfT (T : Ty) (pkgT stateT : Term) : Term :=
  someCallT (createOfSlot T) (.inj (createOfSlot T) "createOf" (.record [("pkg", pkgT), ("state", stateT)]))

/-- `make`: `λ rows state arg req. {calls = {c0 = some (createOf {pkg = QUOTED, state = INIT})},
edits = {}, state = state}` where QUOTED writes the template `p`'s bytes at the parameters `ps` (as
`templateMethod`'s does) and INIT is the new object's state, a term over the same environment
(`arg` at `var 1`, `req` at `var 0`) of the template's state type. -/
def creatorMethod (A : Ty) (ps : List Quote.Param) (p : Package) (init : Term) : Term :=
  .lam (.record []) (.lam genStateTy (.lam A (.lam reqTy
    (resultT (callsT [createOfT p.state (Quote.quotePackage ps (.bytes .empty) p) init]) (.var 2)))))

/-- A TEMPLATE CREATOR: one method `make : A`, no state, no laws, whose run makes, in the invoking
Turn, an object owned by the invoker of the template `p` filled at the parameters' values, at the
state `init` means (`make_template_sound`); the kernel installs the filled package first when the
World does not hold it. A member says "make me one at these parameters" once. -/
def templateCreator (A : Ty) (ps : List Quote.Param) (p : Package) (init : Term) (doc : String) : Package :=
  { pkgOf genStateTy [] [("make", A, [createOfSlot p.state], creatorMethod A ps p init)] with doc := doc.toUTF8 }

/-- The bounded creator: `make {max}` makes the invoker an object of `boundedPackage {f : nat} f
max` at `f = init` (the law judges the birth: an `init` past `max` is refused by the law's name). -/
def boundedCreator (f : Label) (init : Nat) : Package :=
  templateCreator maxArgTy [maxParam] (boundedPackageWith [(f, .nat)] f (.var 4)) (.record [(f, natT init)])
    s!"makes its invoker a {f}-bounded record at the bound its argument names, in one Turn"

/-! ## A quorum-gated generator (LANG-99): a package is installed only on a quorum's commit

The first composition of a generator with the kernel's laws-by-act. The generator object's state is a
quorum's (`Std.quorum` over the field `generated`, the bound last generated): `propose {v}` and
`approve {bit}` are the quorum's own acts; `generate {}` reads the proposal `set v`, writes
`generated := v` and `approvals := 0`, and installs the bounded template at `v`, in one Turn. The
quorum law judges that state change as a COMMIT (k of n approvals of exactly `v`), so the install —
in the same Turn, which fails whole — happens only when the quorum says so. `generate` refuses by
name a `laws` proposal (`notSet`) and a `v` equal to `generated` (`notProposed`: a write that leaves
`generated` unchanged is the quorum's no-op, which needs no approvals, so installing there would
install without a quorum). -/

/-- The quorum generator's state: the quorum's `approvals` and `proposal`, and `generated`. -/
def quorumGenRow : List (Label × Ty) := [("approvals", .nat), ("generated", .nat), ("proposal", proposalTy .nat)]

def quorumGenStateTy : Ty := .record quorumGenRow

/-- `approve {bit}`: `approvals := approvals + bit` (the law admits only the signer's own unset bit). -/
def approveGenMethod : Term :=
  methodOf quorumGenStateTy (.record [("bit", .nat)])
    [("approvals", .prim .add (.get (.var 2) "approvals") (.get (.var 1) "bit")),
     ("generated", .get (.var 2) "generated"), ("proposal", .get (.var 2) "proposal")]

/-- `propose {v}`: `proposal := set v`, `approvals := 0` (the quorum's propose arm). -/
def proposeGenMethod : Term :=
  methodOf quorumGenStateTy (.record [("v", .nat)])
    [("approvals", natT 0), ("generated", .get (.var 2) "generated"),
     ("proposal", .inj (proposalTy .nat) "set" (.get (.var 1) "v"))]

/-- What `generate` returns. -/
def quorumGenResultTy : Ty := resultTy quorumGenStateTy [installSlot]

/-- `generate {}`: `case state.proposal` — `laws` refuses `notSet`; `set v` refuses `notProposed` when
`v` is the bound already generated, and otherwise returns `install` of the template `p` at `v` (the
parameter the case binds, `var 0`) with `generated := v`, `approvals := 0`. -/
def quorumGenerateMethod (p : Package) : Term :=
  .lam (.record []) (.lam quorumGenStateTy (.lam (.record []) (.lam reqTy
    (.case (.get (.var 2) "proposal")
      [("laws", .refuse quorumGenResultTy "notSet".toUTF8),
       ("set", .ite (.prim .eq (.var 0) (.get (.var 3) "generated")) (.refuse quorumGenResultTy "notProposed".toUTF8)
          (resultT (callsT [installOf (Quote.quotePackage [⟨.nat, .var 0⟩] (.bytes .empty) p)])
            (.record [("approvals", natT 0), ("generated", .var 0), ("proposal", .get (.var 3) "proposal")])))]))))

/-- The quorum generator's package, unchecked: what the theorems are about. Its law is `quorumLaw`
at `members` and `k` as given; `quorumGenerator` is the constructor that checks them. -/
def quorumGeneratorOf (r : List (Label × Ty)) (f : Label) (members : List ByteArray) (k : Nat) : Package :=
  { imports := [], state := quorumGenStateTy,
    iface := .record [("approve", methodTy quorumGenStateTy (.record [("bit", .nat)])),
      ("generate", methodTy quorumGenStateTy (.record []) [installSlot]),
      ("propose", methodTy quorumGenStateTy (.record [("v", .nat)])), ("quorum", lawTy quorumGenStateTy)],
    body := .record [("approve", approveGenMethod),
      ("generate", quorumGenerateMethod (boundedPackageWith r f (.var 4))),
      ("propose", proposeGenMethod), ("quorum", quorumLaw quorumGenStateTy .nat members k "generated")],
    methods := ["approve", "generate", "propose"], laws := ["quorum"],
    doc := s!"installs a {f}-bounded record at a bound {k} of its members approved".toUTF8 }

/-- The QUORUM GENERATOR of `boundedPackage r f`: members `members`, threshold `k`. Its object's
`generate` installs the bounded package at a bound `k` distinct members approved, and at no other
(`quorumGenerator_installs_attested`, `Lang.Proofs.StdGen`). The members and threshold are checked as
`quorum` checks them: a repeated member (`duplicateMember`) would cast two bits, and `k = 0`
(`badThreshold`) would install with no approval at all. -/
def quorumGenerator (r : List (Label × Ty)) (f : Label) (members : List ByteArray) (k : Nat) :
    Except StdRefusal Package :=
  (quorum quorumGenStateTy .nat members k "generated").map fun _ => quorumGeneratorOf r f members k

end Nanodregg.Lang.Std
