/-
# Lang.Journey.Doc — the document: a section whose text is chosen among members' posts under a
justification the World can withdraw (DESIGN-CTX §4, S1; the charter's "documents" demonstration)

A SECTION is `Std.hole` at `V := bytes`: its candidates are texts POSTED by contributors (`propose`,
by anyone granted it), each justified by a support that names a kernel cell (the contributor's own
grant, read LIVE: LANG-75.1), chosen by the section's editor (`select`, the chooser), judged by the
clause (a text of at most 2000 bytes). A revoked contributor's text is withdrawn BY NAME on the next
judgment (`rejudge` records `suspended "support0 dead"`; a `select` of it is refused `support0 dead`),
and the editor selects another contributor's text: the document repairs, and nobody re-installs
anything. That is the slot of DESIGN-CTX §2.1 at its most legible, and the first contextual object
a member drives through `nd` (`client/tests/doc.rs`, over the SHIPPED texts).

The shipped texts (`world/doc/Section.lib0..2`, the helpers; `world/doc/Section`, the root linked by
the helpers' DEPLOYED ids, KERNEL's `romIdOf` under CODEC's deployed Env, what `nd install` prints)
are what this generator emits (`lang-journey --write world/doc`); row DC0 reads them from disk and
refuses a text that is not the generator's (one copy, as `world/resident/Bell`'s LB0). The Sim rows
DC1–DC9 run the section's life through `Receive.submit` on the generator's packages linked at the
Sim's ids (a Sim cell id is not a deployed digest, so the root text cannot install in the Sim; the
cargo row installs it for real).
-/
import Lang.Journey
import Lang.Resident

namespace Nanodregg.Lang.Journey.Doc
open Nanodregg.Kernel Nanodregg.Kernel.Receive Nanodregg.Lang.Journey

/-- A section's text is at most 2000 bytes (the Bell's bound on a ring's text). -/
def clause : Term := .lam Std.holeState (.lam .bytes (.prim .lenLe (.var 0) (.nat 2000)))

/-- The section generator: `Std.hole` at `bytes`. -/
def bundle : Except String Std.HoleBundle := (Std.hole .bytes clause).mapError (·.name)

/-- Where the shipped texts live, and their names in install order (the helpers, then the root). -/
def dir : System.FilePath := "world" / "doc"
def files : List String := ["Section.lib0", "Section.lib1", "Section.lib2", "Section"]

/-- The deployed id of a package's bytes: KERNEL's `romIdOf` under CODEC's deployed Env, the id
`nd install` prints and the root's `(imports …)` names (`Lang.Resident.checkPackageWith`'s). -/
def deployedId (bytes : ByteArray) :=
  romIdOf Codec.Deployed.env { kind := kindPackage, discipline := .rom, slots := [(0, bytes)] }

/-- The texts the generator emits, by file: each helper's, then the root's, linked by the helpers'
deployed ids. -/
def texts : Except String (List (String × String)) := do
  let b ← bundle
  let mut out : List (String × String) := []
  let mut ids : List ByteArray := []
  for (lib, i) in b.libraries.zipIdx do
    let some bytes := Wire.encodePackage lib | throw s!"helper {i} has no bytes"
    let some t := Print.package lib | throw s!"helper {i} is not printable"
    ids := ids ++ [(deployedId bytes).bytes]
    out := out ++ [(s!"Section.lib{i}", t)]
  let p ← (b.link ids).mapError (·.name)
  let some t := Print.package p | throw "the root is not printable"
  pure (out ++ [("Section", t)])

/-- `lang-journey --write DIR`: emit the texts (the one way `world/doc` is written). -/
def write (d : System.FilePath) : IO UInt32 := do
  match texts with
  | .error e => IO.eprintln s!"doc: {e}"; return 1
  | .ok ts =>
    IO.FS.createDirAll d
    for (f, t) in ts do
      IO.FS.writeFile (d / f) t
      IO.println s!"wrote {d / f} ({t.length} chars)"
    return 0

/-- The shipped texts, read from disk by name (`""` for a missing file, as the Bell's). -/
def readShipped : IO (List (String × String)) :=
  files.mapM fun (f : String) => do
    let t : String ← try IO.FS.readFile (dir / f) catch _ => pure ""
    pure (f, t)

/-! ## The section's life (DC rows) -/

def supportTy : Ty := Std.holeSupport
def proposeTy : Ty :=
  .record [("cand", .digest), ("s0", optTy supportTy), ("s1", optTy supportTy), ("value", .bytes)]

def supportOf (cell pin : ByteArray) : Data :=
  .inj "some" (.record [("cell", .digest cell), ("pin", .digest pin)])
def noSupport : Data := .inj "none" (.record [])

def proposeArg (cand : ByteArray) (s0 : Data) (text : String) : ByteArray :=
  argBytes proposeTy (.record [("cand", .digest cand), ("s0", s0), ("s1", noSupport), ("value", .bytes text.toUTF8)])
def candArg (cand : ByteArray) : ByteArray :=
  argBytes (.record [("cand", .digest)]) (.record [("cand", .digest cand)])
def postArg (cell pin : ByteArray) : ByteArray :=
  argBytes (.record [("cell", .digest), ("pin", .digest)]) (.record [("cell", .digest cell), ("pin", .digest pin)])

/-- The section's life through the receivers: install, create, a contributor's post selected, the
contributor revoked, the text withdrawn by name, another contributor's text selected. -/
def lifeRows (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let mut r := r0
  let bnd ← match bundle with
    | .ok x => pure x
    | .error e => return note r s!"DC1 generating the section: {e}" false
  -- DC1 the helpers, then the root linked at the Sim's ids
  let mut libIds : List D := []
  for lib in bnd.libraries do
    let some bytes := Wire.encodePackage lib | return note r "DC1 helper has no bytes" false
    let (rL, vL, tL) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rL s!"DC1 A installs a section helper ({bytes.size} bytes): {vL}" (vL == "admitted")
    let some id := tL.bind fun t => (createdIds t).head? | return note r "DC1 no helper id" false
    libIds := libIds ++ [id]
  let p ← match bnd.link (libIds.map Sim.dc.bytes) with
    | .ok p => pure p
    | .error e => return note r s!"DC1 linking the section: {e.name}" false
  let some pb := Wire.encodePackage p | return note r "DC1 the section has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host (a.id :: libIds)) (.install pb))
  r := note r1 s!"DC1 A installs the section ({pb.size} bytes; methods {p.methods}): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "DC1 no section package id" false
  let some dC := p.rels.lookup "candidates" | return note r "DC1 no candidates" false
  let some dF := p.rels.lookup "facts" | return note r "DC1 no facts" false
  let factsIndex := (p.rels.map (·.1)).idxOf "facts"
  -- DC2 A creates a section it edits (chooser and acceptor A; a text is at most 2000 bytes)
  let seedData : List (Label × Data) :=
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes a.id)), ("cap", .nat 2000),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000), ("selected", .inj "none" (.record []))]
  let some seed := stateSlots (recordRow p.state) seedData 0 | return note r "DC2 seed has no bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ libIds)) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"DC2 no section: {v2}" false
  r := note r2 s!"DC2 A creates the section (editor A): {v2}" (v2 == "admitted")
  let factKey (cell : ByteArray) : Data := .record [("cell", .digest cell)]
  let candKey (cand : ByteArray) : Data := .record [("cand", .digest cand)]
  let pinFact (w : World D) (cell : ByteArray) := hole_pinAt obj w factsIndex dF (factKey cell)
  let pinCand (w : World D) (cand : ByteArray) := hole_pinAt obj w 0 dC (candKey cand)
  let status (w : World D) (cand : ByteArray) := hole_statusOf w obj dC cand
  let textOf (w : World D) (cand : ByteArray) : Option String :=
    match (storyRow w obj 0 dC (candKey cand)).bind (·.field "value") with
    | some (.bytes t) => some (String.fromUTF8! t)
    | _ => none
  -- a contributor's grant: post (its support fact) and propose (its text)
  let contribute (r : Run) : Run × String × Option D :=
    let (rg, vg, tg) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj])
      (.grant obj b.id [.invoke (p.methods.idxOf "post"), .invoke (p.methods.idxOf "propose")] none))
    (rg, vg, tg.bind fun t => (createdIds t).head?)
  -- `cells`: the fact cells the call reads live (a support's grant, live or at its tombstone), pinned by the signer
  let call (r : Run) (m : Sim.Member) (via : Option D) (method : Label) (x : ByteArray)
      (rowPins : List (RowSlot D × D) := []) (cells : List D := []) : Call D :=
    signedAt r.st m (Sim.S.pinsFor r.st.host ([m.id, a.id, b.id, obj, pkg] ++ libIds ++ via.toList ++ cells))
      (.invoke obj (p.methods.idxOf method) x 100000 via) r.st.host.height (r.st.host.height + 1024) rowPins
  -- DC3 A grants B post and propose; B posts the fact of its grant and proposes its text under it
  let (r3, v3, g3) := contribute r
  let some gB := g3 | return note r3 s!"DC3 A grants B post and propose: {v3}" false
  r := note r3 s!"DC3 A grants B post and propose: {v3}" (v3 == "admitted")
  let gBb := Sim.dc.bytes gB
  let cB := Sim.dc.bytes b.id
  let (r4, v4, _) := go prog r (call r b (some gB) "post" (postArg gBb gBb))
  r := note r4 s!"DC4 B posts the fact of its grant (cell gB, pin gB): {v4}" (v4 == "admitted")
  let (r5, v5, _) := go prog r (call r b (some gB) "propose" (proposeArg cB (supportOf gBb gBb) "a light on the rock") (pinFact r.st.host gBb))
  r := note r5 s!"DC5 B proposes \"a light on the rock\" supported by its grant: {v5}; status {status r5.st.host cB}"
    (v5 == "admitted" && status r5.st.host cB == some "verified")
  -- DC6 A selects B's text: the section reads it
  let (r6, v6, _) := go prog r (call r a none "select" (candArg cB) (pinCand r.st.host cB ++ pinFact r.st.host gBb) [gB])
  r := note r6 s!"DC6 A selects B's text: {v6}; selected {hole_selectedOf Sim.env r6.st.host obj == some (some cB)}; text {textOf r6.st.host cB}"
    (v6 == "admitted" && hole_selectedOf Sim.env r6.st.host obj == some (some cB))
  -- DC7 A revokes B's grant: the justification is withdrawn; the next judgment says so by name
  let (r7, v7, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, gB]) (.revoke gB))
  r := note r7 s!"DC7 A revokes B's grant: {v7}" (v7 == "admitted")
  let (r8, v8, _) := go prog r (call r a none "rejudge" (candArg cB) (pinCand r.st.host cB ++ pinFact r.st.host gBb) [gB])
  r := note r8 s!"DC8 A rejudges B's text: {v8}; status {status r8.st.host cB}"
    (v8 == "admitted" && status r8.st.host cB == some "suspended \"support0 dead\"")
  let (_, v8b, _) := go prog r (call r a none "select" (candArg cB) (pinCand r.st.host cB ++ pinFact r.st.host gBb) [gB])
  r := note r s!"DC8b A selects the withdrawn text again: {v8b}" (refusedBy v8b "select" "support0 dead")
  -- DC9 B contributes again under a new grant; A selects the new text: the document repaired
  let (r9, v9, g9) := contribute r
  let some gB2 := g9 | return note r9 s!"DC9 A grants B again: {v9}" false
  r := note r9 s!"DC9 A grants B again: {v9}" (v9 == "admitted")
  let gB2b := Sim.dc.bytes gB2
  let cB2 := Sim.dc.bytes gB2
  let (r9a, v9a, _) := go prog r (call r b (some gB2) "post" (postArg gB2b gB2b))
  r := note r9a s!"DC9a B posts the fact of its new grant: {v9a}" (v9a == "admitted")
  let (r9b, v9b, _) := go prog r (call r b (some gB2) "propose" (proposeArg cB2 (supportOf gB2b gB2b) "a ship in the fog") (pinFact r.st.host gB2b))
  r := note r9b s!"DC9b B proposes \"a ship in the fog\" under the new grant: {v9b}; status {status r9b.st.host cB2}"
    (v9b == "admitted" && status r9b.st.host cB2 == some "verified")
  let (r9c, v9c, _) := go prog r (call r a none "select" (candArg cB2) (pinCand r.st.host cB2 ++ pinFact r.st.host gB2b) [gB2])
  r := note r9c s!"DC9c A selects the new text: {v9c}; selected {hole_selectedOf Sim.env r9c.st.host obj == some (some cB2)}; text {textOf r9c.st.host cB2}"
    (v9c == "admitted" && hole_selectedOf Sim.env r9c.st.host obj == some (some cB2))
  return r

/-- DC0: every shipped text is the generator's; then the life. -/
def session (shipped : List (String × String)) : Run :=
  let X := ctxWith langProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let r0 := match texts with
    | .error e => note empty s!"DC0 generating the section texts: {e}" false
    | .ok ts => ts.foldl (fun r (f, t) =>
        let got := (shipped.lookup f).getD ""
        note r s!"DC0 {dir / f} is the generator's text ({t.length} chars)" (got == t)) empty
  let fk := [("dc-a".toUTF8, "dc-a-next".toUTF8), ("dc-b".toUTF8, "dc-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 11) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
  | .error e => note r0 s!"DC1 genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    lifeRows { r0 with st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩)

end Nanodregg.Lang.Journey.Doc
