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
* GN12 (LANG-96, KERNEL-77: generate AND instantiate in one Turn) B installs `Std.boundedCreator n 0`
  and creates a creator object C; B makes at 200 (the package unpinned: the call installs): admitted, and the
  ONE Turn bears two cells — B's object first (owned by B, of the package id), then the package cell
  of `encodePackage (boundedPackage {n : nat} n 200)` (`make_bounded_sound`, run).
* GN13 the made object runs: B sets n = 150, admitted; n = 201 is refused `lawDenied bounded: n over
  the bound`.
* GN14 B grants A invoke on C. A makes at 100 without pinning the package (GN6 installed it): the
  call installs, and admission rejects `idTaken` (the receiver decides install-or-reuse from the
  signer's pins; a client's `derivePins` pins a live package it would bear); pinned live, admitted:
  the Turn bears ONE cell, A's object of GN6's package.
* GN15 the object is the SIGNER's, not the creator's nor its owner's: A sets n = 60, admitted; B sets
  it, refused by the owner check.
* GN16 a creator whose state its own law refuses (`boundedCreator n 500` at max 300): refused
  `lawDenied bounded` at the birth, and the Turn fails whole — the package is not installed either.
* GN17 a member signs `createOf` itself (no generator): the package of max 300 and B's object of it,
  one Turn.
* GN18 (LANG-99: a quorum-gated generator) B installs `Std.quorumGenerator {n : nat} n [B, A] 2` and
  creates Q at `{approvals 0, generated 0, proposal set 0}`; B generates: refused `notProposed` (the
  bound in force needs no quorum, so the generator installs nothing there).
* GN19 B proposes 400 and generates: refused `lawDenied quorum: no quorum` — the install sat in the
  same Turn as the commit the law refused, so nothing is born.
* GN20 B approves (bit 1), A through a grant approves (bit 2), B generates: admitted; the Turn bears
  exactly the package cell of `encodePackage (boundedPackage {n : nat} n 400)` (`generate_quorum_sound`,
  run) and Q's `generated` is 400 (`quorumGenerator_installs_attested`: the two approvals are the
  history's witnesses).
* GN21 the checked constructor: `Std.quorumGenerator` refuses `[B, B]` by name (`duplicateMember`: one
  member, two bits) and a threshold of 0 (`badThreshold`: an install with no approval at all).
* GN22 (LANG-103: the interface a method produces) a constant generator of `boundedPackage {n : nat} n
  500` whose `generate` declares it produces that package's interface: generate admitted, the package
  born.
* GN23 the same generator declaring an interface with one more method, `reset`: generate refused
  `produces generate: lacks reset` (`runMeasured_produces`), nothing born.
* GN24 a bounded package whose `set` (no install or createOf arm) declares it produces an interface:
  install refused `badProduces set`.
* GN25 (LANG-108) a creator WRITTEN IN SURFACE TEXT: a method with a `(createOf (rec (n nat)))` slot whose
  `done` returns `(createOf (pkg #bytes) (state (record (n 5))))`. B installs it, creates C, and makes: the
  ONE Turn bears B's object of the package id (owned by B) and then the package. The same text with an
  `install` slot is refused `callKind createOf` when it is read.
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
  -- GN12 the creator (LANG-96): generate AND instantiate in one Turn
  let pkgIdOf (m : Nat) : D × ByteArray :=
    let bytes := (Wire.encodePackage (Std.boundedPackage rty "n" m)).getD .empty
    (romIdOf Sim.env (packageCell bytes), bytes)
  let (eid200, bytes200) := pkgIdOf 200
  let (r21, v21, g21?) := generator r "GN12" (Std.boundedCreator "n" 0)
  let some (cpkg, C) := g21? | return note r21 s!"GN12 {v21}" false
  let make (r : Run) (m : Sim.Member) (max : Nat) (extra : List D) (via : Option D) : Run × String × Option (Turn D) :=
    match Wire.encodeData Std.maxArgTy (.record [("max", .nat max)]) with
    | none => (r, "no argument bytes", none)
    | some x => go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host ([m.id, C, cpkg] ++ extra))
        (.invoke C 0 x 1000000 via))
  let ownedBy (r : Run) (o : D) (m : Sim.Member) (pid : D) : Bool :=
    match r.st.host.live Sim.env o with
    | some cell => cell.slots.get slotOwner == some (Sim.env.bytes m.id) &&
        cell.slots.get slotPackage == some (Sim.env.bytes pid)
    | none => false
  let (r22, v22, t22) := make r21 b 200 [] none
  let born22 := (t22.map createdIds).getD []
  let some O3 := bornOf t22 | return note r22 s!"GN12 B makes at 200: {v22}" false
  r := note r22 s!"GN12 B installs Std.boundedCreator n 0 and creates C ({v21}); B makes at 200: {v22}; the ONE Turn bears {born22.length} cells: B's object of the package id, owned by B: {ownedBy r22 O3 b eid200}; then the package cell of encodePackage (boundedPackage \{n : nat} n 200) ({bytes200.size} bytes): {born22.getLast? == some eid200}"
    (v22 == "admitted" && born22.length == 2 && ownedBy r22 O3 b eid200 && born22.getLast? == some eid200 &&
      bytes200.size > 0)
  -- GN13 the made object runs under the generated law
  let setOn (r : Run) (m : Sim.Member) (o pid : D) (k : Nat) : Run × String × Option (Turn D) :=
    match setArg k with
    | none => (r, "no argument bytes", none)
    | some x => go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host [m.id, o, pid]) (.invoke o 0 x 1000000 none))
  let (r23, v23, _) := setOn r b O3 eid200 150
  let (r24, v24, _) := setOn r23 b O3 eid200 201
  r := note r24 s!"GN13 B sets n = 150: {v23}; n = 201: {v24}"
    (v23 == "admitted" && v24.startsWith "refused lawDenied" && (v24.splitOn "bounded: n over the bound").length > 1)
  -- GN14 A makes at 100: GN6's package exists; unpinned, then pinned
  let (r25, v25, t25) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, a.id, C]) (.grant C a.id [.invoke 0] none))
  let some gc := bornOf t25 | return note r25 s!"GN14 B grants A invoke on C: {v25}" false
  let (r26, v26, _) := make r25 a 100 [gc] (some gc)
  let (r27, v27, t27) := make r26 a 100 [gc, eid] (some gc)
  let born27 := (t27.map createdIds).getD []
  let some O4 := bornOf t27 | return note r27 s!"GN14 A makes at 100, pinned: {v27}" false
  r := note r27 s!"GN14 B grants A invoke on C ({v25}); A makes at 100 without pinning the package (so the call installs it): {v26}; pinned live (so the call reuses it): {v27}; the Turn bears {born27.length} cell, A's object of GN6's package: {ownedBy r27 O4 a eid}"
    (v25 == "admitted" && v26 == "rejected idTaken" && v27 == "admitted" && born27 == [O4] &&
      ownedBy r27 O4 a eid)
  -- GN15 the object is the signer's
  let (r28, v28, _) := setOn r a O4 eid 60
  let (r29, v29, _) := setOn r28 b O4 eid 61
  r := note r29 s!"GN15 A sets n = 60 on A's object: {v28}; B (who owns the creator) sets it, refused by the owner check (noGrant): {v29}"
    (v28 == "admitted" && v29.startsWith "refused noGrant")
  -- GN16 a creator whose state the law it writes refuses: nothing born, the package not installed
  let (eid300, bytes300) := pkgIdOf 300
  let (r30, v30, g30?) := generator r "GN16" (Std.boundedCreator "n" 500)
  let some (cpkg5, C5) := g30? | return note r30 s!"GN16 {v30}" false
  let (r31, v31, t31) := match Wire.encodeData Std.maxArgTy (.record [("max", .nat 300)]) with
    | none => (r30, "no argument bytes", none)
    | some x => go prog r30 (Sim.signed r30.st b b.key (Sim.S.pinsFor r30.st.host [b.id, C5, cpkg5])
        (.invoke C5 0 x 1000000 none))
  r := note r31 s!"GN16 B makes at 300 from a creator of n = 500: {v31}; nothing born: {t31.isNone}; the package not installed: {(r31.st.host.live Sim.env eid300).isNone}"
    (v31.startsWith "refused lawDenied" && (v31.splitOn "bounded: n over the bound").length > 1 && t31.isNone &&
      (r31.st.host.live Sim.env eid300).isNone)
  -- GN17 a member's own createOf
  let (r32, v32, t32) := match stateSlots (recordRow (.record rty)) [("n", .nat 0)] 0 with
    | none => (r, "no seed bytes", none)
    | some seed => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.createOf bytes300 [] seed))
  let born32 := (t32.map createdIds).getD []
  let some O5 := bornOf t32 | return note r32 s!"GN17 B signs createOf: {v32}" false
  r := note r32 s!"GN17 B signs createOf of the max-300 package itself: {v32}; the Turn bears B's object and the package: {born32 == [O5, eid300] && ownedBy r32 O5 b eid300}"
    (v32 == "admitted" && born32 == [O5, eid300] && ownedBy r32 O5 b eid300)
  -- GN18 the quorum generator (LANG-99)
  let (eid400, bytes400) := pkgIdOf 400
  let qg? := Std.quorumGenerator rty "n" [Sim.dc.bytes b.id, Sim.dc.bytes a.id] 2
  let .ok qg := qg? | return note r s!"GN18 the quorum generator of [B, A] at 2: refused" false
  let (r33, v33, t33) := match Wire.encodePackage qg with
    | none => (r, "no generator bytes", none)
    | some gb => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.install gb))
  let some qpkg := bornOf t33 | return note r33 s!"GN18 install the quorum generator: {v33}" false
  let qseed := stateSlots Std.quorumGenRow
    [("approvals", .nat 0), ("generated", .nat 0), ("proposal", .inj "set" (.nat 0))] 0
  let (r34, v34, t34) := match qseed with
    | none => (r33, "no seed bytes", none)
    | some seed => go prog r33 (Sim.signed r33.st b b.key (Sim.S.pinsFor r33.st.host [b.id, qpkg]) (.create (some qpkg) [] seed))
  let some Q := bornOf t34 | return note r34 s!"GN18 create Q: {v34}" false
  let onQ (r : Run) (m : Sim.Member) (method : Nat) (x : Option ByteArray) (extra : List D) (via : Option D) :
      Run × String × Option (Turn D) :=
    match x with
    | none => (r, "no argument bytes", none)
    | some x => go prog r (Sim.signed r.st m m.key (Sim.S.pinsFor r.st.host ([m.id, Q, qpkg] ++ extra)) (.invoke Q method x 1000000 via))
  let natArg1 (ℓ : Label) (n : Nat) := Wire.encodeData (.record [(ℓ, .nat)]) (.record [(ℓ, .nat n)])
  let (r35, v35, _) := onQ r34 b 1 genArg [] none
  r := note r35 s!"GN18 B installs the quorum generator of [B, A] at 2 ({v33}) and creates Q ({v34}); B generates at the bound in force: {v35}"
    (v33 == "admitted" && v34 == "admitted" && programRefused v35 "notProposed")
  -- GN19 a proposal without a quorum: the commit and its install refused together
  let (r36, v36, _) := onQ r b 2 (natArg1 "v" 400) [] none
  let (r37, v37, t37) := onQ r36 b 1 genArg [] none
  r := note r37 s!"GN19 B proposes 400 ({v36}) and generates: {v37}; nothing born: {t37.isNone}"
    (v36 == "admitted" && v37.startsWith "refused lawDenied" && (v37.splitOn "quorum: no quorum").length > 1 && t37.isNone)
  -- GN20 two approvals, then the generation
  let (r38, v38, t38) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, a.id, Q]) (.grant Q a.id [.invoke 0] none))
  let some gq := bornOf t38 | return note r38 s!"GN20 B grants A approve: {v38}" false
  let (r39, v39, _) := onQ r38 b 0 (natArg1 "bit" 1) [] none
  let (r40, v40, _) := onQ r39 a 0 (natArg1 "bit" 2) [gq] (some gq)
  let (r41, v41, t41) := onQ r40 b 1 genArg [] none
  let born41 := (t41.map createdIds).getD []
  let gen41 := (r41.st.host.live Sim.env Q).bind fun cell =>
    match readState Sim.digestOf Std.quorumGenRow cell.slots with
    | .ok d => d.field "generated"
    | .error _ => none
  r := note r41 s!"GN20 B approves ({v39}), A approves through a grant ({v40}), B generates: {v41}; the Turn bears exactly the package cell of encodePackage (boundedPackage \{n : nat} n 400) ({bytes400.size} bytes): {born41 == [eid400]}; Q's generated: {match gen41 with | some (.nat n) => toString n | _ => "?"}"
    (v38 == "admitted" && v39 == "admitted" && v40 == "admitted" && v41 == "admitted" && born41 == [eid400] &&
      (match gen41 with | some (.nat 400) => true | _ => false))
  -- GN21 the constructor checks the members and the threshold
  let refusedAs (x : Except Std.StdRefusal Package) : String :=
    match x with | .ok _ => "built" | .error e => s!"refused {e.name}"
  let v42 := refusedAs (Std.quorumGenerator rty "n" [Sim.dc.bytes b.id, Sim.dc.bytes b.id] 2)
  let v43 := refusedAs (Std.quorumGenerator rty "n" [Sim.dc.bytes b.id, Sim.dc.bytes a.id] 0)
  r := note r s!"GN21 the quorum generator of [B, B] at 2: {v42}; of [B, A] at 0: {v43}"
    (v42 == "refused duplicateMember" && v43 == "refused badThreshold")
  -- GN22 a generator that declares the interface it produces, and produces it (LANG-103)
  let p500 := Std.boundedPackage rty "n" 500
  let (eid500, bytes500) := pkgIdOf 500
  let I := p500.iface
  let producing (J : Ty) (doc : String) : Package :=
    { Std.generatorOf bytes500 doc with effects := [("generate", { produces := some J })] }
  let (r44, v44, g44?) := generator r "GN22" (producing I "installs the bound-500 package, of its own interface")
  let some (gpkg44, G44) := g44? | return note r44 s!"GN22 {v44}" false
  let (r45, v45, t45) := generate r44 gpkg44 G44
  let born45 := (t45.map createdIds).getD []
  r := note r45 s!"GN22 a generator declaring it produces the interface of boundedPackage n 500 ({v44}); generate: {v45}; the Turn bears that package: {born45 == [eid500]}"
    (v45 == "admitted" && born45 == [eid500])
  -- GN23 the declared interface has a method the output lacks
  let I' := match I with
    | .record row => Ty.record (Row.sort (("reset", (Row.find? "set" row).getD .nat) :: row))
    | t => t
  let (r46, v46, g46?) := generator r "GN23" (producing I' "claims to install a package with reset")
  let some (gpkg46, G46) := g46? | return note r46 s!"GN23 {v46}" false
  let (r47, v47, t47) := generate r46 gpkg46 G46
  r := note r47 s!"GN23 the same generator declaring an interface with reset ({v46}); generate: {v47}; nothing born: {t47.isNone}"
    (programRefused v47 "produces generate: lacks reset" && t47.isNone)
  -- GN24 a method that cannot install declares what it produces
  let notInstalling : Package := { Std.boundedPackage rty "n" 5 with effects := [("set", { produces := some I })] }
  let (r48, v48, _) := match Wire.encodePackage notInstalling with
    | none => (r, "no bytes", none)
    | some nb => go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.install nb))
  r := note r48 s!"GN24 a bounded package whose set declares it produces an interface: {v48}"
    (programRefused v48 "badProduces set")
  -- GN25 (LANG-108) a creator written in surface text: its method returns `createOf` and the object is born
  let (eid250, bytes250) := pkgIdOf 250
  let creatorText (kind : String) : String :=
    s!"(package (doc \"makes its invoker a bounded object\") (state (rec)) (method make (calls ({kind})) (done state (createOf (pkg #{Print.hex bytes250}) (state (record (n 5)))))))"
  let creatorOk := Surface.readPackage (creatorText "(createOf (rec (n nat)))")
  let creatorRefused := match Surface.readWith [] (creatorText "install") with
    | .error (.callKind _ k) => k == "createOf"
    | _ => false
  let (r49, v49, g49?) := match creatorOk with
    | .ok cp => generator r "GN25" cp
    | .error e => (r, s!"GN25 the creator text is refused: {e.name}", none)
  let some (cpkg6, C6) := g49? | return note r49 s!"GN25 {v49}" false
  let (r50, v50, t50) := go prog r49 (Sim.signed r49.st b b.key (Sim.S.pinsFor r49.st.host [b.id, C6, cpkg6])
    (.invoke C6 0 (genArg.getD .empty) 1000000 none))
  let born50 := (t50.map createdIds).getD []
  let some O6 := bornOf t50 | return note r50 s!"GN25 B makes: {v50}" false
  r := note r50 s!"GN25 a creator written as surface text (a slot `(createOf (rec (n nat)))`, an item `(createOf (pkg #bytes) (state (record (n 5))))`) is installed and created ({v49}); B makes: {v50}; the ONE Turn bears {born50.length} cells, B's object of the package id owned by B, then the package: {ownedBy r50 O6 b eid250 && born50.getLast? == some eid250}; the same text with an `install` slot is refused callKind createOf: {creatorRefused}"
    (v50 == "admitted" && born50.length == 2 && ownedBy r50 O6 b eid250 && born50.getLast? == some eid250 && creatorRefused)
  return r

/-- A fresh session for the GN rows. -/
def genSession : Run :=
  let X := ctxWith headProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  match genesis X Sim.worldName (Sim.nonceOf 13) 100000000
      [("gn-b".toUTF8, nextKeyDigest X "gn-b-next".toUTF8), ("gn-a".toUTF8, nextKeyDigest X "gn-a-next".toUTF8)]
      Authority.none with
  | .error e => note empty s!"GN genesis: {e.name}" false
  | .ok g =>
    let m : Sim.Member := ⟨founderId X g.origin 0, "gn-b".toUTF8, "gn-b-next".toUTF8⟩
    let a : Sim.Member := ⟨founderId X g.origin 1, "gn-a".toUTF8, "gn-a-next".toUTF8⟩
    genRows { st := { rng := ⟨1⟩, host := g, members := [m, a] } } m a

initialize register { name := "gen", run := pure genSession }

end Nanodregg.Lang.Journey
