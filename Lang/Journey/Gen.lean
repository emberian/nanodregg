/-
# Lang.Journey.Gen — §GN: a generator installs a package through the real receivers (LANG-86, KERNEL-75)

One World of the Sim. Every row is a call through `Receive.submit` with `Lang.program` as the
kernel's `Program` (the deployed receipt check at the Sim's parameters, as `Lang.Journey.Head`).

* GN0 B installs `Std.headGenerator` (a package whose one method returns `install` of
  `Std.headPackage`'s bytes) and creates a generator object G of it.
* GN1 B invokes `G.generate`: admitted; the Turn bears exactly one cell, a package cell whose id is
  `Protocol.Foreign.headPackageId` — the generated package is `Std.head` byte for byte, as one digest;
  `Std.headPackageBytes` is the bytes Protocol's constant names.
* GN2 the generated package runs: B creates a head object of THAT id and posts an honest advance.
* GN3 B generates again: refused `idTaken` (a ROM cell is its content; generation is idempotent up
  to refusal).
* GN4 the floor of `tree_package_checked`: a generator whose bytes are not a package is refused by
  name at the nested install (`program decode …`), and the World is unchanged.
* GN5 a generator of a package that does not check (a method its interface lacks) is refused
  `program noMethod …` at the nested install.
* GN6 (LANG-87, rung 1) B installs the TEMPLATE generator `Std.boundedGenerator {n : nat} n` and
  generates at 100: the Turn bears one package cell whose id is the content id of
  `encodePackage (Std.boundedPackage {n : nat} n 100)` — the nano generator wrote the Lean
  generator's bytes at the receipt's argument (`generate_bounded_sound`, run).
* GN7 the generated package runs: B creates an object O of THAT id with n = 0 and sets n = 50.
* GN8 the generated law holds at the generated bound: n = 101 is refused `lawDenied bounded: n over
  the bound` by name.
* GN9 (LANG-88) B installs `Std.ownerGenerator {n : nat}`, a generator with NO argument whose output
  names its INVOKER, and generates: the Turn bears the cell of `encodePackage (ownedPackage {n : nat}
  B)` — the package's allowlist is B's id, read from the generating Turn's request
  (`generate_owner_sound`, run).
* GN10 B creates an object O of it and sets n = 7: admitted (B is on the list).
* GN11 B grants A invoke on O; A sets n = 9 through the grant: refused `lawDenied owner: not on the
  allowlist` — the package B generated admits B by name and no one else.
-/
import Lang.Journey.Head
import Lang.StdGen

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The empty record's bytes: `generate`'s argument. -/
def genArg : Option ByteArray := Wire.encodeData (.record []) (.record [])

/-- The first cell a Turn bore, if it bore one. -/
def bornOf (t : Option (Turn D)) : Option D := t.bind fun t => (createdIds t).head?

def genRows (r0 : Run) (b a : Sim.Member) : Run := Id.run do
  let prog := headProgram
  let mut r := r0
  -- a generator object of package `p`, installed and created by B: its package id and object id
  let generator (r : Run) (name : String) (p : Package) : Run × String × Option (D × D) :=
    match Wire.encodePackage p with
    | none => (r, s!"{name}: the generator has no bytes", none)
    | some gb =>
      let (r1, v1, t1) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.install gb))
      match bornOf t1 with
      | none => (r1, s!"{name}: install the generator: {v1}", none)
      | some gpkg =>
        let (r2, v2, t2) := go prog r1 (Sim.signed r1.st b b.key (Sim.S.pinsFor r1.st.host [b.id, gpkg])
          (.create (some gpkg) [] []))
        match bornOf t2 with
        | none => (r2, s!"{name}: create the generator object: {v2}", none)
        | some G => (r2, s!"installed ({v1}, {gb.size} bytes) and created ({v2})", some (gpkg, G))
  let generate (r : Run) (gpkg G : D) : Run × String × Option (Turn D) :=
    match genArg with
    | none => (r, "no bytes", none)
    | some x =>
      go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, G, gpkg]) (.invoke G 0 x 1000000 none))
  -- GN0
  let (r1, v1, g?) := generator r "GN0" Std.headGenerator
  let some (gpkg, G) := g? | return note r1 s!"GN0 {v1}" false
  r := note r1 s!"GN0 B installs Std.headGenerator and creates a generator object G: {v1}" true
  -- GN1
  let (r2, v2, t2) := generate r gpkg G
  let born := (t2.map createdIds).getD []
  let hid := Protocol.Foreign.headPackageId Sim.env
  let sameBytes := Std.headPackageBytes == Protocol.Foreign.headPackageBytes
  r := note r2 s!"GN1 B invokes G.generate: {v2}; the Turn bears {born.length} cell(s), a package cell whose id is headPackageId: {born == [hid]}; Std.headPackageBytes is Protocol's constant: {sameBytes}"
    (v2 == "admitted" && born == [hid] && sameBytes)
  let w1 := r
  -- GN2 the generated package runs
  let worldA := hdDig 7
  let R1 := hdDig 101
  let R2 := hdDig 102
  -- each head with a chain (DESIGN-TRUST T2, LANG-95): the generated package is Std.head byte for byte
  let C1 := hdDig 201
  let C2 := hdDig 202
  let (r3, v3, t3) := match hdSeed C1 10 R1 20 worldA with
    | none => (r, "no seed bytes", none)
    | some seed => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, hid]) (.create (some hid) [] seed))
  let some H := bornOf t3 | return note r3 s!"GN2 B creates a head object of the generated package: {v3}" false
  let (r4, v4, _) := match hdAtArg C2 11 R2 21 with
    | none => (r3, "no bytes", none)
    | some x => go prog r3 (Sim.signed r3.st b b.key (Sim.S.pinsFor r3.st.host [b.id, H, hid]) (.invoke H 1 x 1000000 none))
  let held := (r4.st.host.live Sim.env H).bind (headView Sim.digestOf (hdDig hid))
  r := note r4 s!"GN2 B creates a head object H of the generated package ({v3}) and posts the advance \{height 11, steps 21} ({v4}); H holds it: {held == some (.at worldA C2 11 R2 21)}"
    (v3 == "admitted" && v4 == "admitted" && held == some (.at worldA C2 11 R2 21))
  -- GN3 idempotent up to refusal
  let (_, v5, _) := generate w1 gpkg G
  r := note r s!"GN3 B generates again: {v5}" ((v5.splitOn "idTaken").length > 1)
  -- GN4 the floor: bytes that are not a package
  let (r6, v6, g6?) := generator r "GN4" (Std.generatorOf ⟨#[7]⟩ "emits one byte")
  let some (gpkg6, G6) := g6? | return note r6 s!"GN4 {v6}" false
  let (r7, v7, t7) := generate r6 gpkg6 G6
  r := note r7 s!"GN4 a generator whose bytes are one byte, not a package ({v6}); generate: {v7}; nothing born: {t7.isNone}; the World unchanged: {r7.st.host.steps == r6.st.host.steps}"
    (programRefused v7 "decode" && t7.isNone && r7.st.host.steps == r6.st.host.steps)
  -- GN5 a package that does not check
  let bad : Package := { Std.headPackage with methods := ["nope"] }
  let (r8, v8, g8?) := generator r (s!"GN5") (Std.generatorOf ((Wire.encodePackage bad).getD .empty) "emits a package naming a method it lacks")
  let some (gpkg8, G8) := g8? | return note r8 s!"GN5 {v8}" false
  let (r9, v9, t9) := generate r8 gpkg8 G8
  r := note r9 s!"GN5 a generator of a package whose methods name a field it lacks ({v8}); generate: {v9}; nothing born: {t9.isNone}"
    (programRefused v9 "noMethod" && t9.isNone)
  -- GN6 the template generator (LANG-87): generate at 100
  let rty : List (Label × Ty) := [("n", .nat)]
  let (r10, v10, g10?) := generator r "GN6" (Std.boundedGenerator rty "n")
  let some (gpkg10, G10) := g10? | return note r10 s!"GN6 {v10}" false
  let expected := (Wire.encodePackage (Std.boundedPackage rty "n" 100)).getD .empty
  let eid := romIdOf Sim.env { kind := kindPackage, discipline := .rom, slots := [(0, expected)] }
  let (r11, v11, t11) := match Wire.encodeData Std.maxArgTy (.record [("max", .nat 100)]) with
    | none => (r10, "no argument bytes", none)
    | some x => go prog r10 (Sim.signed r10.st b b.key (Sim.S.pinsFor r10.st.host [b.id, G10, gpkg10])
        (.invoke G10 0 x 1000000 none))
  let born11 := (t11.map createdIds).getD []
  r := note r11 s!"GN6 B installs Std.boundedGenerator \{n : nat} n ({v10}) and generates at 100: {v11}; the Turn bears {born11.length} cell(s), a package cell whose id is the content id of encodePackage (boundedPackage \{n : nat} n 100) ({expected.size} bytes): {born11 == [eid]}"
    (v11 == "admitted" && born11 == [eid] && expected.size > 0)
  -- GN7 the generated package runs: an object at n = 0, set to 50
  let (r12, v12, t12) := match stateSlots (recordRow (.record rty)) [("n", .nat 0)] 0 with
    | none => (r, "no seed bytes", none)
    | some seed => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, eid]) (.create (some eid) [] seed))
  let some O := bornOf t12 | return note r12 s!"GN7 B creates an object of the generated package: {v12}" false
  let setArg (k : Nat) : Option ByteArray := Wire.encodeData (.record rty) (.record [("n", .nat k)])
  let setN (r : Run) (k : Nat) : Run × String × Option (Turn D) :=
    match setArg k with
    | none => (r, "no argument bytes", none)
    | some x => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, O, eid]) (.invoke O 0 x 1000000 none))
  let (r13, v13, _) := setN r12 50
  r := note r13 s!"GN7 B creates an object O of the generated package ({v12}) and sets n = 50: {v13}"
    (v12 == "admitted" && v13 == "admitted")
  -- GN8 the generated law at the generated bound
  let (r14, v14, _) := setN r 101
  r := note r14 s!"GN8 B sets n = 101: {v14}"
    (v14.startsWith "refused lawDenied" && (v14.splitOn "bounded: n over the bound").length > 1)
  -- GN9 the owner generator (LANG-88): no argument; the output names the invoker
  let (r15, v15, g15?) := generator r "GN9" (Std.ownerGenerator rty)
  let some (gpkg15, G15) := g15? | return note r15 s!"GN9 {v15}" false
  let owned := (Wire.encodePackage (Std.ownedPackage rty (Sim.dc.bytes b.id))).getD .empty
  let oid := romIdOf Sim.env { kind := kindPackage, discipline := .rom, slots := [(0, owned)] }
  let (r16, v16, t16) := generate r15 gpkg15 G15
  let born16 := (t16.map createdIds).getD []
  r := note r16 s!"GN9 B installs Std.ownerGenerator \{n : nat} ({v15}) and generates with no argument: {v16}; the Turn bears {born16.length} cell(s), the package cell of encodePackage (ownedPackage \{n : nat} B) ({owned.size} bytes), B's id read from the Turn's request: {born16 == [oid]}"
    (v16 == "admitted" && born16 == [oid] && owned.size > 0)
  -- GN10 B uses it
  let (r17, v17, t17) := match stateSlots (recordRow (.record rty)) [("n", .nat 0)] 0 with
    | none => (r, "no seed bytes", none)
    | some seed => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, oid]) (.create (some oid) [] seed))
  let some O2 := bornOf t17 | return note r17 s!"GN10 B creates an object of the generated package: {v17}" false
  let (r18, v18, _) := match setArg 7 with
    | none => (r17, "no argument bytes", none)
    | some x => go prog r17 (Sim.signed r17.st b b.key (Sim.S.pinsFor r17.st.host [b.id, O2, oid]) (.invoke O2 0 x 1000000 none))
  r := note r18 s!"GN10 B creates an object O of the generated package ({v17}) and sets n = 7: {v18}"
    (v17 == "admitted" && v18 == "admitted")
  -- GN11 A, granted, is not on the list
  let (r19, v19, t19) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, a.id, O2]) (.grant O2 a.id [.invoke 0] none))
  let some gr := bornOf t19 | return note r19 s!"GN11 B grants A invoke: {v19}" false
  let (r20, v20, _) := match setArg 9 with
    | none => (r19, "no argument bytes", none)
    | some x => go prog r19 (Sim.signed r19.st a a.key (Sim.S.pinsFor r19.st.host [a.id, O2, oid, gr]) (.invoke O2 0 x 1000000 (some gr)))
  r := note r20 s!"GN11 B grants A invoke on O ({v19}); A sets n = 9 through the grant: {v20}"
    (v19 == "admitted" && v20.startsWith "refused lawDenied" && (v20.splitOn "owner: not on the allowlist").length > 1)
  return r

/-- A fresh session for the GN rows. -/
def genSession : Run :=
  let X := ctxWith headProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  match genesis X Sim.worldName (Sim.nonceOf 13) 100000000
      [("gn-b".toUTF8, nextKeyDigest X "gn-b-next".toUTF8), ("gn-a".toUTF8, nextKeyDigest X "gn-a-next".toUTF8)] with
  | .error e => note empty s!"GN genesis: {e.name}" false
  | .ok g =>
    let m : Sim.Member := ⟨founderId X g.origin 0, "gn-b".toUTF8, "gn-b-next".toUTF8⟩
    let a : Sim.Member := ⟨founderId X g.origin 1, "gn-a".toUTF8, "gn-a-next".toUTF8⟩
    genRows { st := { rng := ⟨1⟩, host := g, members := [m, a] } } m a

end Nanodregg.Lang.Journey
