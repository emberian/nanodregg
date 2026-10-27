/-
# Lang.Journey.Claims — §LK: a claim's certifying shape, checked as install checks it (LANG-92 L1, LANG-93 L2)

L1 (`claimSession`): the checker `Term.guardedBy` run as a function on laws over `Owned`'s state
`{owner, total}` with the invariant `le100 = λ s. s.total ≤ 100` (DESIGN-PCC §8).

* LK1 a hand-written law in certifying shape (every `ok` under `app le100 new`) checks, and so does
  `Std.keeps S le100`.
* LK2 a law whose `write` arm admits without the test does not check (an unguarded `ok`).
* LK3 a law that returns a verdict it read from its state is not in shape (nothing but a literal `inj`
  may be an `ok`).
* LK4 the journey's own `bounded` tests `new.total ≤ 100` INLINE, not as `app le100 new`: not in shape
  until the renaming lemma lands (DESIGN-PCC §3.4); it is the row that measures that gap.

L2 (`claimRows`): the claim CARRIED by the package (`Package.claims`, the wire's tenth child, the text's
`(claims …)` section) and refused at install through the receivers, under the honest program and under
the plant `skip-claims` (`Mode.skipClaims`: the install check drops the claims before checking, DESIGN-PCC
§4's `uncheckedInstallKernel`).

* LK0 `Kept` (`Owned` with `le100` an interface field, `bounded` in shape, claiming `keeps le100 bounded`)
  prints with a `(claims (keeps le100 bounded))` section and reads back to the same package; the section
  is optional: the text without it reads to the package with no claims; a claim is in the id: the two
  packages have different bytes.
* LK0b the surface declaration `(claim keeps INV LAW)` lowers to `Package.claims`; CappedTally claiming
  `keeps decider decider` is refused `claimNotInvariant decider` by the check (`decider` is a law).
* LK5 install `Kept`: admitted; create at `{owner = A, total = 0}`: admitted; `set 50`: admitted, the
  cell reads 50; `set 101`: refused `lawDenied bounded: over 100`, the cell still reads 50 (the claim's
  inhabitant: B4 is true of this object).
* LK6 `Kept` with `bounded := leaky` (the `write` arm admits without the test): refused
  `program claimUnproved bounded`. PLANT skip-claims: ADMITTED.
* LK7 `Kept` with `bounded` written through a helper lambda (`app (lam _ (var 0)) boundedKeeps`, typed at
  `lawTy S` but no literal to walk): refused `claimShape bounded`. PLANT: ADMITTED.
* LK8 a claim naming the method `set` as its law: refused `claimNotLaw set`; LK8b a claim naming the state
  field `owner` as its invariant: refused `claimNotInvariant owner`. PLANT: both ADMITTED.
* LK9 `Kept`'s bytes at the previous wire version: refused `lang/package-version/N` by name at install.
-/
import Lang.Journey
import Lang.Journey.Kept
import Lang.Claim

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- A law that returns whatever verdict its new state holds at `flag`. -/
def readsVerdict : Term := law3 (.get (.var 1) "flag")

/-- `boundedKeeps` through a helper lambda: the same law at the same type, with no literal to walk. -/
def helped : Term := .app (.lam (lawTy S) (.var 0)) boundedKeeps

def claimSession : Run :=
  let X := ctxWith langProgram
  let r : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let chk (t : Term) : Bool := Term.guardedBy le100 1 0 (Std.lawBody t)
  let r := note r s!"LK1 a law in certifying shape checks: {chk boundedKeeps}; Std.keeps S le100 checks: {chk (Std.keeps S le100)}"
    (chk boundedKeeps && chk (Std.keeps S le100))
  let r := note r s!"LK2 a law whose write arm admits without the test does not check: {chk leaky}" (!chk leaky)
  let r := note r s!"LK3 a law that returns a verdict read from its state is not in shape: {chk readsVerdict}" (!chk readsVerdict)
  let r := note r s!"LK4 the journey's bounded (inline test) is not in shape yet (DESIGN-PCC §3.4): {chk bounded}" (!chk bounded)
  r

/-! ## L2: the carried claim, through the receivers -/

/-- The text reads back as exactly `q`. -/
def readsTo (text : String) (q : Package) : Bool :=
  match Read.readPackage text with
  | .ok p => p == q
  | .error _ => false

/-- A refusal by name at install: `program "<name> <label>"`. -/
def installRefused (v name : String) : Bool :=
  v.startsWith "refused program" && (v.splitOn name).length > 1

/-- The claim rows through the receivers, under `mode` (`.honest`, or the plant `.skipClaims`). -/
def claimRows (mode : Mode) : Run := Id.run do
  let prog := mode.program
  let X := ctxWith prog
  let fk : List (ByteArray × ByteArray) := [("lk-a".toUTF8, "lk-a-next".toUTF8)]
  let g ← match genesis X Sim.worldName (Sim.nonceOf 11) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) Authority.none with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"LK genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let tag := if mode = .skipClaims then "PLANT skip-claims: " else ""
  -- LK0 the text and the wire
  let some kb := Wire.encodePackage kept | return note r "LK0 Kept has no bytes" false
  let some text := Print.package kept | return note r "LK0 Kept has no text" false
  let sec := "\n  (claims (keeps le100 bounded))"
  let without := text.replace sec ""
  let plain : Package := { kept with claims := [] }
  if mode = .honest then
    r := note r s!"LK0 Kept prints with a claims section ({text.length} chars, {kb.size} bytes) and reads back; the section is optional (the text without it reads to the package with no claims); the claim is in the id (different bytes)"
      ((text.splitOn sec).length > 1 && readsTo text kept && without != text &&
        readsTo without plain && Wire.encodePackage plain != some kb)
    let surface := cappedTallySurface.replace "(law decider" "(claim keeps decider decider)\n  (law decider"
    let (lowered, verdict) := match Surface.readPackage surface with
      | .ok p => (p.claims == [.keeps "decider" "decider"], match p.checkWith [] with
          | .error e => e.wire
          | .ok () => "ok")
      | .error e => (false, e.text surface)
    r := note r s!"LK0b the surface declaration (claim keeps decider decider) lowers to Package.claims: {lowered}; the check refuses it: {verdict}"
      (lowered && verdict == "claimNotInvariant decider")
  -- LK5 the inhabitant
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install kb))
  r := note r1 s!"{tag}LK5 A installs Kept (claims keeps le100 bounded): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LK5 no package id" false
  let some ownerBytes := Wire.encodeData .digest (.digest (Sim.dc.bytes a.id)) | return note r "LK5 no owner bytes" false
  let some n0 := nat64 0 | return note r "LK5 no bytes for 0" false
  let some n50 := nat64 50 | return note r "LK5 no bytes for 50" false
  let some n101 := nat64 101 | return note r "LK5 no bytes for 101" false
  let seed : Slots := [(stateBase, ownerBytes), (stateBase + 1, n0)]
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed))
  r := note r2 s!"{tag}LK5b A creates an object of Kept at total 0: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "LK5 no object id" false
  let (r3, v3, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n50 10000 none))
  r := note r3 s!"{tag}LK5c A set 50: {v3}, total = {totalOf Sim.env r3.st.host obj}" (v3 == "admitted" && totalOf Sim.env r3.st.host obj == some 50)
  let (r4, v4, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n101 10000 none))
  r := note r4 s!"{tag}LK5d A set 101: {v4}, total = {totalOf Sim.env r4.st.host obj}"
    (deniedWith v4 "bounded: over 100" && totalOf Sim.env r4.st.host obj == some 50)
  -- LK6–LK8 the refusals, each a flip under the plant
  let refusals : List (String × Package × String) :=
    [("LK6 Kept with bounded := leaky (the write arm admits without the test)", keptWith leaky [.keeps "le100" "bounded"], "claimUnproved bounded"),
     ("LK7 Kept with bounded through a helper lambda (no literal to walk)", keptWith helped [.keeps "le100" "bounded"], "claimShape bounded"),
     ("LK8 Kept claiming keeps le100 set (a method, not a law)", keptWith boundedKeeps [.keeps "le100" "set"], "claimNotLaw set"),
     ("LK8b Kept claiming keeps owner bounded (a state field, not an interface field)", keptWith boundedKeeps [.keeps "owner" "bounded"], "claimNotInvariant owner")]
  for (what, p, name) in refusals do
    let some pb := Wire.encodePackage p | return note r s!"{what}: no bytes" false
    let (rx, vx, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
    if mode = .skipClaims then
      r := note rx s!"{tag}{what} must now be ADMITTED: {vx}" (vx == "admitted")
    else
      r := note rx s!"{what}: {vx}" (installRefused vx name)
  -- LK9 the version
  if mode = .honest then
    let prev := kb.set! 0 (Bounds.packageWireVersion - 1)
    let (r9, v9, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install prev))
    r := note r9 s!"LK9 A installs Kept's bytes at version {Bounds.packageWireVersion - 1}: {v9}"
      (installRefused v9 s!"lang/package-version/{Bounds.packageWireVersion.toNat}")
  r

initialize register { name := "claims", run := pure claimSession }
initialize register { name := "claims-l2", run := pure (claimRows .honest) }
initialize register { name := "claims-l2-skip-claims", run := pure (claimRows .skipClaims) }

end Nanodregg.Lang.Journey
