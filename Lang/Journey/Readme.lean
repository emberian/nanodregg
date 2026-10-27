/-
# Lang.Journey.Readme — §RM: the README's program, through the real receivers

The program README.md reads through section by section is the first code block of its "One program"
section: a counter whose step is a contextual hole, whose law judges each act, and whose `spawn`
method generates a package. It is a SURFACE text (`Lang.Surface`), and the session reads it FROM
README.md (`lake exe lang-journey` runs from the repository root), so the text the page shows is the
text that is lowered, checked, installed and run. The text names one cell, the grant `G` its candidate 1
cites, as `#G`; the session makes `G` first and writes its id there.

* RM0 the README's program block is read from README.md, and it is a surface text.
* RM1 B creates a data object and grants A `mutate` on it: the grant `G`.
* RM2 B installs the counter text: admitted (the install check admits the hole at its signature).
* RM3 B creates a counter `O` at `count 0`.
* RM4 B bumps before any selection: refused `holeSelectionAbsent 0` (the demanded hole is blocked).
* RM5 B chooses candidate 1; RM6 B bumps with `G` pinned: `count` is 10.
* RM7 B bumps without pinning `G`: refused `holeUnpinned cell:G`.
* RM8 B revokes `G`; RM9 B bumps with `G` pinned at its tombstone: refused `holeSupportDead 0 cell:G`,
  and `count` stays 10.
* RM10 B chooses candidate 0; RM11 B bumps: `count` is 11.
* RM12 B spawns at `n 7`: the Turn bears one package cell, the content id of the bytes `spawn`
  computed, which read as `(body (record (n 7)))`.
* RM13 B retires `O` at `count 11`: refused `lawDenied cap: not empty`.
* RM14 B creates a counter at `count 101`: refused `lawDenied cap: over 100` at its birth.
* RM15 `ob (check P)` admits the same text off the World, by install's own admission (LANG-105), with a
  deployed-width id for `G`.
* RM16 `ob (check P (view …))` resolves the hole on the five views RM4, RM6, RM7, RM9 and RM11 ran on,
  and answers what the World answered: the same refusal, by name and coordinate (the id of `G` aside,
  which differs between the Sim and the deployed width), or the candidate whose run the World admitted.
-/
import Lang.Journey.Gen
import Lang.Resident

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- Where the README is, from the repository root. -/
def readmePath : System.FilePath := "README.md"

/-- The README's program: the first code block of its "One program" section. -/
def programOf (readme : String) : Option String :=
  match readme.splitOn "\n## One program\n" with
  | [_, rest] =>
    match rest.splitOn "```" with
    | _ :: block :: _ => some block.trimAscii.toString
    | _ => none
  | _ => none

/-- The counter's text with `G`'s id written in. -/
def counterAt (text : String) (g : ByteArray) : String := text.replace "#G" ("#" ++ hexOf g)

/-- A refusal's text with an id written as `G`. -/
def withG (v : String) (g : ByteArray) : String := v.replace (hexOf g) "G"

def readmeRows (text : String) (r0 : Run) (b a : Sim.Member) : Run := Id.run do
  let prog := langProgram
  let mut r := r0
  let has (v w : String) : Bool := (v.splitOn w).length > 1
  -- RM1
  let (r1, v1, t1) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.create none [] []))
  let some d0 := bornOf t1 | return note r1 s!"RM1 B creates a data object: {v1}" false
  let (r1b, v1b, t1b) := go prog r1 (Sim.signed r1.st b b.key (Sim.S.pinsFor r1.st.host [b.id, a.id, d0])
    (.grant d0 a.id [.mutate] none))
  let some g := bornOf t1b | return note r1b s!"RM1 B grants A mutate: {v1b}" false
  r := note r1b s!"RM1 B creates a data object ({v1}) and grants A mutate on it: the grant G ({v1b})"
    (v1 == "admitted" && v1b == "admitted")
  let gb := Sim.dc.bytes g
  -- RM2
  let .ok p := Surface.readPackage (counterAt text gb) | return note r "RM2 the counter text reads" false
  let some bytes := Wire.encodePackage p | return note r "RM2 the counter has bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, g]) (.install bytes))
  let some pkg := bornOf t2 | return note r2 s!"RM2 B installs the counter: {v2}" false
  r := note r2 s!"RM2 B installs the counter ({bytes.size} bytes, one hole): {v2}" (v2 == "admitted")
  -- RM3
  let seed (n : Nat) := stateSlots (recordRow p.state) [("count", .nat n)] 0
  let some s0 := seed 0 | return note r "RM3 seed" false
  let (r3, v3, t3) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, pkg]) (.create (some pkg) [] s0))
  let some O := bornOf t3 | return note r3 s!"RM3 B creates a counter: {v3}" false
  r := note r3 s!"RM3 B creates a counter O at count 0: {v3}" (v3 == "admitted")
  let dChoice := (p.rels.head?.map (·.2)).getD default
  let choiceKey : Data := .record [("k", .nat 0)]
  let count (w : World D) := natSlotOf Sim.env w O 0
  let call (r : Run) (method : Label) (args : ByteArray) (cells : List D) : Call D :=
    signedAt r.st b (Sim.S.pinsFor r.st.host ([b.id, O, pkg] ++ cells))
      (.invoke O (p.methods.idxOf method) args 100000 none) r.st.host.height (r.st.host.height + 1024)
      (hole_pinAt O r.st.host 0 dChoice choiceKey)
  let none0 := argBytes (.record []) (.record [])
  let choose (i : Nat) := argBytes (.record [("i", .nat)]) (.record [("i", .nat i)])
  -- RM4
  let (_, v4, _) := go prog r (call r "bump" none0 [g])
  r := note r s!"RM4 B bumps before any selection: {v4}" (has v4 "holeSelectionAbsent 0")
  -- RM5, RM6
  let (r5, v5, _) := go prog r (call r "choose" (choose 1) [])
  r := note r5 s!"RM5 B chooses candidate 1: {v5}" (v5 == "admitted")
  let (r6, v6, _) := go prog r (call r "bump" none0 [g])
  r := note r6 s!"RM6 B bumps with G pinned: {v6}; count {count r6.st.host}" (v6 == "admitted" && count r6.st.host == some 10)
  -- RM7
  let (_, v7, _) := go prog r (call r "bump" none0 [])
  r := note r s!"RM7 B bumps without pinning G: {v7}" (has v7 s!"holeUnpinned cell:{hexOf gb}")
  -- RM8, RM9
  let (r8, v8, _) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, g]) (.retire g))
  r := note r8 s!"RM8 B revokes G: {v8}" (v8 == "admitted")
  let (_, v9, _) := go prog r (call r "bump" none0 [g])
  r := note r s!"RM9 B bumps with G pinned at its tombstone: {v9}; count {count r.st.host}"
    (has v9 s!"holeSupportDead 0 cell:{hexOf gb}" && count r.st.host == some 10)
  -- RM10, RM11
  let (r10, v10, _) := go prog r (call r "choose" (choose 0) [])
  r := note r10 s!"RM10 B chooses candidate 0: {v10}" (v10 == "admitted")
  let (r11, v11, _) := go prog r (call r "bump" none0 [g])
  r := note r11 s!"RM11 B bumps: {v11}; count {count r11.st.host}" (v11 == "admitted" && count r11.st.host == some 11)
  -- RM12
  let (r12, v12, t12) := go prog r (call r "spawn" (argBytes (.record [("n", .nat)]) (.record [("n", .nat 7)])) [])
  let born := (t12.map createdIds).getD []
  let generated := match Read.hexBytes? "#0a00000b00000004000004000106016e010000000800010f016e010408",
      Read.hexBytes? "#00010000010000020000000000030000040000050000" with
    | some pre, some suf => Codec.Stream.u64be.put (UInt64.ofNat 7) pre ++ suf
    | _, _ => .empty
  let gid := romIdOf Sim.env { kind := kindPackage, discipline := .rom, slots := [(0, generated)] }
  let reads := match Wire.decodePackage generated with
    | .ok q => (Print.package q).map (fun t => has t "(body (record (n 7)))") |>.getD false
    | .error _ => false
  r := note r12 s!"RM12 B spawns at n 7: {v12}; the Turn bears one package cell, the generated bytes' id: {born == [gid]}; they read as (body (record (n 7))): {reads}"
    (v12 == "admitted" && born == [gid] && reads)
  -- RM13
  let (_, v13, _) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, O, pkg]) (.retire O))
  r := note r s!"RM13 B retires O at count 11: {v13}" (has v13 "lawDenied" && has v13 "cap: not empty")
  -- RM14
  let some s101 := seed 101 | return note r "RM14 seed" false
  let (_, v14, _) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, pkg]) (.create (some pkg) [] s101))
  r := note r s!"RM14 B creates a counter at count 101: {v14}" (has v14 "lawDenied" && has v14 "cap: over 100")
  -- RM15, RM16: the same text off the World, by `ob`, with a deployed-width id for G
  let gd : ByteArray := ⟨(List.replicate 32 (0x47 : UInt8)).toArray⟩
  let P := counterAt text gd
  let ob (view : String) : String := (Lang.Resident.run s!"(check {P}{view})").line
  let a15 := ob ""
  r := note r s!"RM15 ob (check P): {a15}" (a15.startsWith "ok " && !has a15 "hole")
  let live := s!" (live #{hexOf gd})"
  let dead := s!" (dead #{hexOf gd})"
  let views : List (String × String × String) := [
    ("RM4", " (view (select step none))", withG v4 gb),
    ("RM7", " (view (select step 1))", withG v7 gb),
    ("RM6", s!" (view (select step 1){live})", "hole 0 candidate 1"),
    ("RM9", s!" (view (select step 1){dead})", withG v9 gb),
    ("RM11", " (view (select step 0))", "hole 0 candidate 0")]
  for (row, view, world) in views do
    let a := withG (ob view) gd
    -- a refusal: ob's refusal (after `refused `) is in the World's verdict; a resolution: ob names the
    -- candidate the World's admitted run took
    let same := if a.startsWith "refused " then has world (a.drop 8).toString
      else a.startsWith "ok " && a.endsWith world
    r := note r s!"RM16 ob (check P (view …)) as {row}: {a}" same
  -- RM17: a candidate or a guard of the wrong type is refused naming the line it is written on
  let lineOfFirst (t needle : String) : Nat := Surface.lineOf t (t.splitOn needle).head!.length
  let badCand := P.replace "(candidate 10 (cell #" "(candidate true (cell #"
  let a17 := (Lang.Resident.run s!"(check {badCand})").line
  let l17 := lineOfFirst badCand "(candidate true"
  r := note r s!"RM17 ob (check P) with candidate 1 written `true`: {a17}"
    (a17 == s!"refused holeCandidateType 0 1 line {l17}" && l17 > 1 && l17 == lineOfFirst P "(candidate 10" )
  let badGuard := P.replace "(candidate 1)" "(guard 3)\n    (candidate 1)"
  let a18 := (Lang.Resident.run s!"(check {badGuard})").line
  let l18 := lineOfFirst badGuard "(guard 3)"
  r := note r s!"RM18 ob (check P) with a guard written `3`: {a18}"
    (a18 == s!"refused holeGuardType 0 line {l18}" && l18 > 1)
  -- RM19: a body ill-typed at the hole signature names the line of the method it is written in
  let badBody := P.replace "(+ state.count (hole step))" "(+ state.count true)"
  let a19 := (Lang.Resident.run s!"(check {badBody})").line
  let l19 := lineOfFirst badBody "(+ state.count true)"
  r := note r s!"RM19 ob (check P) with the body of bump adding `true`: {a19}"
    (badBody != P && has a19 "refused holeBodyType" && l19 > 1 && a19.endsWith s!" line {l19}")
  return r

/-- A fresh session for the RM rows, over the README's program `text`. -/
def readmeSessionOf (text : String) : Run :=
  let X := ctxWith langProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  let surface := match Read.parse text with
    | .ok x => !Surface.isCore x
    | .error _ => false
  let empty := note empty s!"RM0 the README's program is read from {readmePath} ({text.length} chars), a surface text: {surface}"
    (!text.isEmpty && surface)
  match genesis X Sim.worldName (Sim.nonceOf 17) 100000000
      [("rm-b".toUTF8, nextKeyDigest X "rm-b-next".toUTF8), ("rm-a".toUTF8, nextKeyDigest X "rm-a-next".toUTF8)]
      Authority.none with
  | .error e => note empty s!"RM genesis: {e.name}" false
  | .ok g =>
    let b : Sim.Member := ⟨founderId X g.origin 0, "rm-b".toUTF8, "rm-b-next".toUTF8⟩
    let a : Sim.Member := ⟨founderId X g.origin 1, "rm-a".toUTF8, "rm-a-next".toUTF8⟩
    let r := readmeRows text { empty with st := { rng := ⟨1⟩, host := g, members := [b, a] } } b a
    r

/-- The session over README.md's own text. -/
def readmeSession : IO Run := do
  let readme ← try IO.FS.readFile readmePath catch _ => pure ""
  pure (readmeSessionOf ((programOf readme).getD ""))

initialize register { name := "readme", run := readmeSession }

end Nanodregg.Lang.Journey
