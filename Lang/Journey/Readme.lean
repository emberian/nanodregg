/-
# Lang.Journey.Readme — §RM: the README's program, through the real receivers

The program README.md reads through line by line is `counterText`: a counter whose step is a contextual
hole, whose law judges each act, and whose `spawn` method generates a package. Every row is a call
through `Receive.submit` with `Lang.program` as the kernel's `Program`, on one World of the Sim. The
text names one cell, the grant `G` its candidate 1 cites; the session makes `G` first and writes its
id into the text, so the text installed is the README's with `G` filled in.

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
-/
import Lang.Journey.Gen

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive

/-- The README's program; `GGGG` stands for the hex of the grant `G` candidate 1 cites. -/
def counterText : String := "(package
  (imports)
  (doc \"a counter whose step is chosen in context; it spawns parameter packages\")
  (state (rec (count nat)))
  (iface (rec
    (bump (-> (rec) (-> (rec (count nat)) (-> (rec) (-> (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)) (rec (calls (rec)) (edits (rec)) (state (rec (count nat)))))))))
    (cap (-> (rec (count nat)) (-> (rec (count nat)) (-> (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)) (sum (ok (rec)) (refused bytes))))))
    (choose (-> (rec) (-> (rec (count nat)) (-> (rec (i nat)) (-> (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)) (rec (calls (rec)) (edits (rec (e0 (sum (none (rec)) (some (sum (choice (sum (insert (rec (key (rec (k nat))) (val nat))) (upsert (rec (key (rec (k nat))) (val nat))))))))))) (state (rec (count nat)))))))))
    (spawn (-> (rec) (-> (rec (count nat)) (-> (rec (n nat)) (-> (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)) (rec (calls (rec (c0 (sum (none (rec)) (some (sum (install (rec (pkg bytes))))))))) (edits (rec)) (state (rec (count nat)))))))))))
  (methods bump choose spawn)
  (laws cap)
  (rels (choice (key (k nat)) (val nat) (limit 1) (sum) (cap 0) (retract false) (guard) (holds)))
  (body (record
    (bump (fn (rows (rec)) (state (rec (count nat))) (arg (rec)) (req (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)))
      (record (calls (record)) (edits (record))
        (state (record (count (+ (. state count) (hole 0 (subst)))))))))
    (cap (fn (old (rec (count nat))) (new (rec (count nat))) (req (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)))
      (let ok (sum (ok (rec)) (refused bytes)) (inj (sum (ok (rec)) (refused bytes)) ok (record))
      (let within (sum (ok (rec)) (refused bytes)) (if (<= (. new count) 100) ok (inj (sum (ok (rec)) (refused bytes)) refused \"over 100\"))
        (case (. req occasion)
          (adopt x within) (birth x within) (invoke m within)
          (relaw x (inj (sum (ok (rec)) (refused bytes)) refused \"frozen\"))
          (retire x (if (== (. old count) 0) ok (inj (sum (ok (rec)) (refused bytes)) refused \"not empty\")))
          (write x (inj (sum (ok (rec)) (refused bytes)) refused \"frozen\")))))))
    (choose (fn (rows (rec)) (state (rec (count nat))) (arg (rec (i nat))) (req (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)))
      (record (calls (record)) (state state)
        (edits (record (e0 (inj (sum (none (rec)) (some (sum (choice (sum (insert (rec (key (rec (k nat))) (val nat))) (upsert (rec (key (rec (k nat))) (val nat)))))))) some
          (inj (sum (choice (sum (insert (rec (key (rec (k nat))) (val nat))) (upsert (rec (key (rec (k nat))) (val nat)))))) choice (inj (sum (insert (rec (key (rec (k nat))) (val nat))) (upsert (rec (key (rec (k nat))) (val nat)))) upsert
            (record (key (record (k 0))) (val (. arg i))))))))))))
    (spawn (fn (rows (rec)) (state (rec (count nat))) (arg (rec (n nat))) (req (rec (agent digest) (caller (sum (none (rec)) (some digest))) (notBefore nat) (occasion (sum (adopt bytes) (birth (rec)) (invoke nat) (relaw bytes) (retire (rec)) (write (rec)))) (principal digest) (self digest) (validUntil nat)))
      (record (edits (record)) (state state)
        (calls (record (c0 (inj (sum (none (rec)) (some (sum (install (rec (pkg bytes)))))) some
          (inj (sum (install (rec (pkg bytes)))) install
            (record (pkg (cat (u64be #0a00000b00000004000004000106016e010000000800010f016e010408 (. arg n)) #00010000010000020000000000030000040000050000)))))))))))))
  (holes (hole 0 (context) (result nat) (selection 0 #0000000000000000) (hypotheses)
    (guard (structural) true)
    (code (candidate 1 (supports)) (candidate 10 (supports (cell #GGGG)))))))"

/-- The counter's text with `G`'s id written in. -/
def counterAt (g : ByteArray) : String := counterText.replace "GGGG" (hexOf g)

def readmeRows (r0 : Run) (b a : Sim.Member) : Run := Id.run do
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
  let .ok p := Surface.readPackage (counterAt gb) | return note r "RM2 the counter text reads" false
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
  return r

/-- A fresh session for the RM rows. -/
def readmeSession : Run :=
  let X := ctxWith langProgram
  let empty : Run := { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
  match genesis X Sim.worldName (Sim.nonceOf 17) 100000000
      [("rm-b".toUTF8, nextKeyDigest X "rm-b-next".toUTF8), ("rm-a".toUTF8, nextKeyDigest X "rm-a-next".toUTF8)]
      Authority.none with
  | .error e => note empty s!"RM genesis: {e.name}" false
  | .ok g =>
    let b : Sim.Member := ⟨founderId X g.origin 0, "rm-b".toUTF8, "rm-b-next".toUTF8⟩
    let a : Sim.Member := ⟨founderId X g.origin 1, "rm-a".toUTF8, "rm-a-next".toUTF8⟩
    readmeRows { st := { rng := ⟨1⟩, host := g, members := [b, a] } } b a

initialize register { name := "readme", run := pure readmeSession }

end Nanodregg.Lang.Journey
