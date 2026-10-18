/-
# Lang.Journey — the first law end to end: install → create → invoke through KERNEL's receivers

`lake exe lang-journey` drives the REAL receive path (`Receive.submit` = `receive` then
`World.admit`) with `Lang.program` as the kernel's `Program`, under the Sim's toy parameters
(UInt64 digest, FNV hash, toy signatures: memory "toy parameters in the real pipeline"). The
package `Owned` keeps `{owner : digest, total : nat}`; its method `set n` writes `total := n`; its
laws are `bounded` (`new.total ≤ 100`, else "over 100") and `ownerOnly` (the SIGNING member must be
the owner and the owner never changes). Rows:

* L0 the text form of `Owned` (`Lang.Read`, what a resident writes) reads to the same bytes.
* L0c `Lang.Print` gives `Owned` its text, which reads back to the same bytes; a non-atom label
  has no text; bytes that are not quote-free UTF-8 print as `#hex` and read back.
* L0d the reader's fuel counts nesting only: an allowlist at `Std.idsMax` ids prints and reads
  back; a list past `Read.listMax` is refused `tooLong`, a form past `Read.depthMax` `tooDeep`.
* L0e a binder named like a literal (`true`, `5`, `#ab`), a head word or a primitive is refused
  `reservedBinder`.
* L0f (LANG-31) one label rule, and the reader two levels past the wire: a package written as text
  with its body and interface nested to the wire's depth bound reads, checks, encodes, prints and
  reads back to the same bytes; one level deeper the reader refuses it `tooDeep`; a label with a
  space has no bytes.
* L1 founder A installs `Owned` (a ROM cell, id `romIdOf`) — admitted.
* L2 A creates an object owned by A, seed `{owner = A, total = 0}`, judged by both laws — admitted.
* L3 A invokes `set 50` — admitted; the object's `total` slot decodes to 50.
* L4 A invokes `set 101` — refused `lawDenied` by `bounded`, nothing written.
* L5 B invokes `set 7` through A's grant for method 0 (so the principal is A, the grant's root
  issuer) — refused `lawDenied` by `ownerOnly`, which checks the SIGNER: a law can be stricter than
  the principal.
* L6 a package whose body does not check at its interface — refused `program` at install.
* LI (LANG-35) install loads the import closure: `Mid` imports `Owned` and installs; `Top` imports
  `Mid`, and its install pinning only `Mid` is refused `unpinned` naming `Owned` (LI2: the check loads
  `Mid`'s own closure, so `Owned` must be pinned too); pinning both, it is admitted (LI3).
* L8 (ID-1) `Tally`'s law `fresh` cases on the occasion: a birth seeded with approvals is refused,
  a zero seed admitted.
* L8d/e the invoke's method index reaches the law: `fresh` closes method `b`, `a` passes.
* L9 (ID-1) `Frozen`, an extra law on a data object, refuses its own replacement; writes pass.
* L10 the relaw carries the incoming law ids: `OnlyTo [Frozen]` refuses a replacement by `[Tally]`
  and admits one by `[Frozen]`.
* L11 (KERNEL-27 `adopt`) `BirthOnly` admits a birth and refuses its adoption: an object may be
  born under it (L11b), and adding it to an existing object is refused (L11c) by the incoming law
  itself, which a birth-conflated occasion could not say. L11d: a relaw that KEEPS BirthOnly and adds
  Frozen is admitted, since only ADDED laws judge adopt (KERNEL-27).
* LD (LANG-38, a digest is a type) LD1: a Relay whose call names its callee by a bytes literal is
  refused `illTyped payload` at install; LD2: an allowlist naming a 3-byte id (not a Sim digest) is
  refused `notDigest` at install; LD3: a Relay seeded with `next = some #78797a` is refused at its
  birth, `state field next: not a digest`; LD4: an invoke whose argument `via` is not a digest is
  refused `arguments: not a digest`.
* LD5 (LANG-41, a run's ids came from where ids enter) `Caller`, holding and taking nothing, calls the
  signing member as an object: the kernel refuses it `wrongKind` (a member is not an object), so
  `callsOf` read the call.
* LT (LANG-45, NANO-VS-MINI §5) Mini's CappedTally ported by hand, as the text a resident writes:
  LT0 it reads (its size printed); LT1 install; LT2a a start at 1001 refused by `cap`; LT2 a start at 0
  with decider B; LT3 the grant; LT4 B replies 600 (required steps and ticks printed); LT5 B replies
  500, refused by `cap`; LT6 the owner replies, refused by `decider`; LT7 two answers signed over one
  view: the first admitted, the second `stale` (Mini's `add` deltas keep both); LT8 a tally that
  closes before the answer's window ends refuses it `closed` (Mini's `timedOut`, as a height).
* LS (LANG-47 → LANG-49) Mini's CoAuthor over relations (`proposals`, `authors`, `ballots`,
  `chapters`; a method that succeeds leaves the state unchanged, the law `react` refuses by `why`):
  LS0 it reads (sizes printed beside the list port's); LS1–LS3 install, start, grant; LS4/LS5 two
  proposals, LS5b a second by one author `keyTaken` (Mini's alreadyProposed); LS6 a vote (required
  steps, ticks and logged bytes printed), LS6b `keyTaken` (alreadyVoted), LS6c `unknown`; LS7
  `notAuthor`, LS7b the author's rewrite; LS8 a seal in the window `early`; LS9 the seal after it,
  over one signed range, makes the rewritten passage chapter 1; LS10 two proposals signed over one
  view both land, in both orders, to the same World; LS11 a vote and an edit of one proposal over one
  view: the second is `stale` (its pinned row moved). Plant skip-judge: LS6c is then ADMITTED.
* L7 the follower (`World.fold` from genesis) and the auditor reach the Host's World.
* PLANT skip-judge: the same rows against a program whose `judge` admits everything: L4 must be
  ADMITTED there (the row flips), proving the refusal in L4 came from the law, not from elsewhere. LT5 too: its
  refusal came from `cap`.
* PLANT erase-occasion: the same rows against a program whose judge is told every act is a write
  (the judge before ID-1): L8b, L8e, L9d, L10c and L11c must be ADMITTED there, so their refusals came
  from the occasion.
* PLANT raw-install: the install check before LANG-35, each import's interface read raw from its
  cell and its closure never loaded: LI2 must be ADMITTED there, so its refusal came from the loader.
  That mode stops after LI2: the plant runs the rows before LI and LI2, not the rows after.
* PLANT bytes-ids: the install check reads every bytes literal as an id (ids were bytes before
  LANG-38): LD1 must be ADMITTED there, so its refusal came from the type. PLANT skip-lits: the install
  check without its id-literal check: LD2 must be ADMITTED. PLANT total-digest: run and judge with a
  `digestOf` that accepts any bytes: LD3 and LD4b must be ADMITTED, so their refusals came from the
  boundary's digest check. Each of the three runs only the call rows up to its own.
* PLANT unlawful-codec: the method run by a program whose decoder refuses the founder's own id inside
  a lawful `Ctx` (`Lang.Proofs.Provenance.program_run_past_extraction`'s `hp` false there): LD5c must be refused by `callsOf`, by name,
  `calls: c0 obj: not a digest`. A request's ids are the one source no boundary check reads, so this
  is the only way to reach that refusal, and the second premise of
  `program_run_past_extraction` (the program decodes with the `Ctx`'s own codec) is not decoration.
* PLANT drop-range-row: the run is handed each signed range without its last row: LS9's seal is
  still ADMITTED (the kernel re-checks the signer's range pin, never what Lang was given) and chapter
  1 is the wrong passage (the dropped row was the winner), so the honest LS9 says the rows a method
  receives are exactly the keys under the pinned prefix. That mode runs only the LS rows.
* PLANT erase-payload: the occasion's payload is lost (a relaw names no laws, every invoke is
  method 0): L8e must be admitted and L10d refused, so the payload reaches the law.
-/
import Kernel.Sim
import Lang.Program
import Lang.Print
import Lang.Resident
import Lang.Std
import Lang.Sim.Need

namespace Nanodregg.Lang.Journey

open Nanodregg.Kernel Nanodregg.Kernel.Receive
abbrev D := Sim.D

def S : Ty := .record [("owner", .digest), ("total", .nat)]

def ok : Term := .inj verdictTy "ok" (.record [])
def refused (why : String) : Term := .inj verdictTy "refused" (.bytes why.toUTF8)

/-- Under `lam S (lam S (lam reqTy _))`: var 2 = old, var 1 = new, var 0 = req. -/
def law3 (body : Term) : Term := .lam S (.lam S (.lam reqTy body))

def bounded : Term :=
  law3 (.ite (.prim .le (.get (.var 1) "total") (.nat 100)) ok (refused "over 100"))

def ownerOnly : Term :=
  law3 (.ite (.prim .deq (.get (.var 0) "agent") (.get (.var 1) "owner"))
    (.ite (.prim .deq (.get (.var 2) "owner") (.get (.var 1) "owner")) ok (refused "owner changed"))
    (refused "not the owner"))

/-- `set state n req = {owner = state.owner, total = n}` -/
def setM : Term := Std.methodOf S .nat [("owner", .get (.var 2) "owner"), ("total", .var 1)]

def iface : Ty :=
  .record [("bounded", lawTy S), ("ownerOnly", lawTy S), ("set", methodTy S .nat)]

def owned : Package :=
  { imports := [], state := S, iface,
    body := .record [("bounded", bounded), ("ownerOnly", ownerOnly), ("set", setM)],
    methods := ["set"], laws := ["bounded", "ownerOnly"] }

/-- The Sim.same package with a body that does not check at its interface (`set` returns a nat). -/
def illTyped : Package :=
  { owned with body := .record [("bounded", bounded), ("ownerOnly", ownerOnly),
      ("set", .lam (.record []) (.lam S (.lam .nat (.lam reqTy (.var 1)))))] }

/-- The request type as the resident pastes it (printed from `reqTy`, so it is never restated). -/
def rq : String := Print.tyText reqTy (by decide +kernel)

/-- `Owned`'s method result type and its empty calls row, printed from `resultTy` and `callsT`. -/
def ownedRes : String := Print.tyText (resultTy S) (by decide +kernel)
def noCalls : String := Print.noCallsText

/-- `Owned`, as a resident writes it (Lang.Read): must read to exactly the package above. -/
def ownedText : String := s!"
(package (imports)
  (state (rec (owner digest) (total nat)))
  (iface (rec (set (-> (rec) (-> (rec (owner digest) (total nat))
                    (-> nat (-> {rq} {ownedRes})))))
              (bounded (-> (rec (owner digest) (total nat)) (-> (rec (owner digest) (total nat))
                (-> {rq}
                    (sum (ok (rec)) (refused bytes))))))
              (ownerOnly (-> (rec (owner digest) (total nat)) (-> (rec (owner digest) (total nat))
                (-> {rq}
                    (sum (ok (rec)) (refused bytes))))))))
  (methods set)
  (laws bounded ownerOnly)
  (rels)
  (body
    (record
      (set (fn (v (rec)) (s (rec (owner digest) (total nat))) (n nat)
               (r {rq})
             (record (calls {noCalls}) (edits (record)) (state (record (owner (. s owner)) (total n))))))
      (bounded (fn (old (rec (owner digest) (total nat))) (new (rec (owner digest) (total nat)))
                   (r {rq})
                 (if (<= (. new total) 100)
                     (inj (sum (ok (rec)) (refused bytes)) ok (record))
                     (inj (sum (ok (rec)) (refused bytes)) refused \"over 100\"))))
      (ownerOnly (fn (old (rec (owner digest) (total nat))) (new (rec (owner digest) (total nat)))
                     (r {rq})
                   (if (deq (. r agent) (. new owner))
                       (if (deq (. old owner) (. new owner))
                           (inj (sum (ok (rec)) (refused bytes)) ok (record))
                           (inj (sum (ok (rec)) (refused bytes)) refused \"owner changed\"))
                       (inj (sum (ok (rec)) (refused bytes)) refused \"not the owner\")))))))
"

/-! ### The occasion rows (ID-1): a law that knows which act it judges

`Tally` keeps `{approvals : nat, total : nat}`; its law `fresh` refuses a birth whose seed carries
approvals and admits every other act. `Frozen` is a law package over a data object whose law
refuses any replacement of the laws and admits every other act. Without the occasion both were
unwritable: `create` judges the seed as `old = new`, and `law` judges the unchanged state, so each
looked like a no-op write. -/

def T : Ty := .record [("approvals", .nat), ("total", .nat)]

/-- Under `case req.occasion`, inside an arm: var 3 = old, var 2 = new, var 1 = req, var 0 = the
arm's payload. -/
def tallyFresh : Term :=
  .lam T (.lam T (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", .ite (.prim .eq (.get (.var 2) "approvals") (.nat 0)) ok (refused "seeded")),
     ("invoke", .ite (.prim .eq (.var 0) (.nat 1)) (refused "method b is closed") ok),
     ("relaw", ok), ("write", ok)])))

/-- `set state n req = {approvals = state.approvals, total = n}`, as both methods `a` and `b`. -/
def tallySet : Term := Std.methodOf T .nat [("approvals", .get (.var 2) "approvals"), ("total", .var 1)]

def tally : Package :=
  { imports := [], state := T,
    iface := .record [("a", methodTy T .nat), ("b", methodTy T .nat), ("fresh", lawTy T)],
    body := .record [("a", tallySet), ("b", tallySet), ("fresh", tallyFresh)],
    methods := ["a", "b"], laws := ["fresh"] }

def frozenLaw : Term :=
  .lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", ok), ("invoke", ok), ("relaw", refused "laws are frozen"), ("write", ok)])))

def frozen : Package :=
  { imports := [], state := .record [], iface := .record [("frozen", lawTy (.record []))],
    body := .record [("frozen", frozenLaw)], methods := [], laws := ["frozen"] }

/-- A law that may govern an object from its birth but refuses to be added to one later. -/
def birthOnly : Package :=
  let law := Term.lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", refused "only at birth"), ("birth", ok), ("invoke", ok), ("relaw", ok), ("write", ok)])))
  { imports := [], state := .record [], iface := .record [("birthOnly", lawTy (.record []))],
    body := .record [("birthOnly", law)], methods := [], laws := ["birthOnly"] }

/-- A law package admitting a replacement of the laws only by exactly the ids whose bytes are `to`. -/
def onlyTo (to : ByteArray) : Package :=
  let law := Term.lam (.record []) (.lam (.record []) (.lam reqTy (.case (.get (.var 0) "occasion")
    [("adopt", ok), ("birth", ok), ("invoke", ok),
     ("relaw", .ite (.prim .beq (.var 0) (.bytes to)) ok (refused "not the agreed laws")), ("write", ok)])))
  { imports := [], state := .record [], iface := .record [("onlyTo", lawTy (.record []))],
    body := .record [("onlyTo", law)], methods := [], laws := ["onlyTo"] }

/-! ### Calls (LANG-23, KERNEL-28): a method's calls are derived as the object, at most
`callDepthMax` deep

`Relay` keeps `{hits : nat, me : digest, next : opt digest}`. Its method `go {rest, via}` counts the
hit, records `req.self` as `me`, and, when `next` is `some n`, invokes `n`'s method 0 through grant
`via` (a grant naming THIS object) with `rest` as the arguments: bytes it holds, forwarded whole
(LANG-23 (iii)), so the journey nests each level's encoded arguments inside the previous one. -/

def R : Ty := .record [("hits", .nat), ("me", .digest), ("next", optTy .digest)]
def RA : Ty := .record [("rest", .bytes), ("via", .digest)]

/-- `go`'s one call slot: an invoke, nothing else. -/
def K : Ty := callOf ["invoke"]

/-- `invoke obj 0 rest 1000 (some via)`, inside `next`'s `some` arm (the next object var 0, req var 1,
args var 2, state var 3). -/
def relayCallTo (obj : Term) : Term :=
  .inj K "invoke" (.record [("args", .get (.var 2) "rest"), ("budget", .nat 1000),
    ("method", .nat 0), ("obj", obj), ("via", .inj (optTy .digest) "some" (.get (.var 2) "via"))])

def relayCall : Term := relayCallTo (.var 0)

def relayGoWith (call : Term) : Term :=
  .lam (.record []) (.lam R (.lam RA (.lam reqTy (resultT
    (.case (.get (.var 2) "next") [("none", callsT [noCallT K]), ("some", callsT [someCallT K call])])
    (.record [("hits", .prim .add (.get (.var 2) "hits") (.nat 1)), ("me", .get (.var 0) "self"),
      ("next", .get (.var 2) "next")])))))

def relayGo : Term := relayGoWith relayCall

def relayWith (go : Term) : Package :=
  { imports := [], state := R, iface := .record [("go", methodTy R RA [K])],
    body := .record [("go", go)], methods := ["go"], laws := [] }

def relay : Package := relayWith relayGo

/-- LD1 (LANG-38): Relay naming its callee by a BYTES literal (eight bytes, a well-formed toy digest
as bytes): the call's `obj` is typed `digest`, so this is ill-typed at install. -/
def relayBytesId : Package := relayWith (relayGoWith (relayCallTo (.bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0]⟩)))

/-- LD2 (LANG-38): an allowlist naming a member by a digest literal of three bytes, which the Sim's
eight-byte digest codec refuses: install refuses it `notDigest`. -/
def badListed : Package :=
  { imports := [], state := .record [], iface := .record [("al", lawTy (.record []))],
    body := .record [("al", Std.allowlistLaw (.record []) [⟨#[120, 121, 122]⟩])], methods := [], laws := ["al"] }

/-- LD5 (LANG-41): `Caller` holds nothing and takes nothing; its method `go` makes one call, an
invoke of the SIGNING member (`req.agent`) as an object, through no grant. So the run's only id is
the request's own. -/
def CA : Ty := .record []

def callerGo : Term :=
  .lam (.record []) (.lam CA (.lam CA (.lam reqTy (resultT
    (callsT [someCallT K (.inj K "invoke" (.record [("args", .bytes .empty), ("budget", .nat 1000),
      ("method", .nat 0), ("obj", .get (.var 0) "agent"), ("via", .inj (optTy .digest) "none" (.record []))]))])
    (.var 2)))))

def caller : Package :=
  { imports := [], state := CA, iface := .record [("go", methodTy CA CA [K])],
    body := .record [("go", callerGo)], methods := ["go"], laws := [] }

/-- One call slot more than `callsMax`. -/
def nineLabels : List Label := slotLabels "c" (Kernel.Bounds.callsMax + 1)

def nineGo : Term :=
  .lam (.record []) (.lam R (.lam RA (.lam reqTy (resultT (callsT (nineLabels.map fun _ => noCallT K)) (.var 2)))))

def nineTy : Ty := methodTy R RA (nineLabels.map fun _ => K)

/-- A method whose calls row has one slot more than `callsMax`: its type is not a method's. -/
def nineCalls : Package :=
  { imports := [], state := R, iface := .record [("go", nineTy)],
    body := .record [("go", nineGo)], methods := ["go"], laws := [] }

/-- A u64 argument or slot (`none` past `2^64`). -/
def nat64 (n : Nat) : Option ByteArray := Wire.encodeData .nat (.nat n)

def ctxWith (prog : Program D) : Ctx D := Sim.ctxWith prog

def langProgram : Program D := Lang.program Sim.dc.bytes Sim.digestOf

/-- Plant 1: a program whose judge admits every write. -/
def skipJudge : Program D := { langProgram with judge := fun _ _ _ _ _ _ => .ok () }

/-- Plant 2: a program whose judge is told every act is a write (the judge before ID-1). -/
def eraseOccasion : Program D :=
  { langProgram with judge := fun look p ls o n r => langProgram.judge look p ls o n { r with occasion := .write } }

/-- Plant 3: the occasion's payload is lost (a relaw names no laws, every invoke is method 0). -/
def erasePayload : Program D :=
  { langProgram with judge := fun look p ls o n r =>
      let occasion : Occasion D := match r.occasion with
        | .relaw _ => .relaw [] | .adopt _ => .adopt [] | .invoke _ => .invoke 0 | o => o
      langProgram.judge look p ls o n { r with occasion } }

/-- Plant 4: the calls a method makes never reach the kernel (the glue before this day). -/
def dropCalls : Program D :=
  { langProgram with run := fun look rv p s m a r b => (langProgram.run look rv p s m a r b).map fun x => (x.1, [], x.2.2) }

/-- Plant 5: the install check before LANG-35: each import's interface read raw from its cell
(decoded, never re-checked), the import's own closure never loaded. -/
def rawInstall : Program D :=
  { langProgram with checkInstall := fun look b => do
      let p ← match Wire.decodePackage b with
        | .ok p => pure p
        | .error e => throw (.program (decodeText e))
      let ifaces ← p.imports.mapM fun d => do
        let id ← idOf Sim.digestOf d
        pure (← readPackage look id).iface
      match p.checkWith ifaces with
      | .ok () => pure ()
      | .error e => throw (.program e.wire) }

mutual
/-- Every bytes literal of a term as an id literal: the plant `bytesIds` (ids as bytes, before LANG-38).
It rewrites EVERY bytes literal, so it flips LD1 for the right reason only because `relayBytesId`'s
one bytes literal is the callee id: a fixture with a reason string would turn ill-typed under it. -/
def bytesAsDigest : Term → Term
  | .bytes s => .digest s
  | .lam A b => .lam A (bytesAsDigest b)
  | .app f a => .app (bytesAsDigest f) (bytesAsDigest a)
  | .fix t => .fix (bytesAsDigest t)
  | .prim p a b => .prim p (bytesAsDigest a) (bytesAsDigest b)
  | .record fs => .record (bytesAsDigestRow fs)
  | .get t ℓ => .get (bytesAsDigest t) ℓ
  | .extend t fs => .extend (bytesAsDigest t) (bytesAsDigestRow fs)
  | .inj T ℓ t => .inj T ℓ (bytesAsDigest t)
  | .case t fs => .case (bytesAsDigest t) (bytesAsDigestRow fs)
  | .ite c a b => .ite (bytesAsDigest c) (bytesAsDigest a) (bytesAsDigest b)
  | t => t

def bytesAsDigestRow : List (Label × Term) → List (Label × Term)
  | [] => []
  | (ℓ, t) :: fs => (ℓ, bytesAsDigest t) :: bytesAsDigestRow fs
end

/-- Plant 6: the install check reads a bytes literal where an id is expected (ids were bytes before
LANG-38): it checks the package with every bytes literal made an id literal. -/
def bytesIds : Program D :=
  { langProgram with checkInstall := fun look b => do
      let p ← match Wire.decodePackage b with
        | .ok p => pure p
        | .error e => throw (.program (decodeText e))
      match Wire.encodePackage { p with body := bytesAsDigest p.body } with
      | some b' => langProgram.checkInstall look b'
      | none => throw (.program "plant: no bytes") }

/-- Plant 7: the install check without its id-literal check (`checkLits`, LANG-38). -/
def skipLits : Program D :=
  { langProgram with checkInstall := fun look b => do
      let p ← match Wire.decodePackage b with
        | .ok p => pure p
        | .error e => throw (.program (decodeText e))
      let (L, gis) ← loadAll Sim.digestOf look (closureDepthMax - 1) p.imports ⟨[], [], []⟩
      let some ifaces := ifacesAt L.pkgs gis | throw (.program "closure")
      match p.checkWith ifaces with
      | .ok () => pure ()
      | .error e => throw (.program e.wire) }

/-- A digest decoder that accepts every byte string (a non-digest reads as the digest 0). -/
def totalDigestOf (b : ByteArray) : Option D := some ((Sim.digestOf b).getD 0)

/-- Plant 8: run and judge ask a `digestOf` that accepts any bytes, so the boundary's digest check
(`readState`, the arguments, LANG-38) never refuses; install is the deployed one. -/
def totalDigest : Program D :=
  let t := Lang.program Sim.dc.bytes totalDigestOf
  { langProgram with run := t.run, judge := t.judge }

/-- A digest decoder that refuses exactly member `x`'s own id: a World whose codec does not read
that id back. Plant 9 gives it to the program only, so the `Ctx` stays lawful and `program_run_past_extraction`'s `hp` is what fails. -/
def refusing (x : D) (b : ByteArray) : Option D := if b = Sim.dc.bytes x then none else Sim.digestOf b

/-- Plant 9: the method run under a World whose codec refuses member `x`'s id. A request's ids are
the one source no boundary check reads (they are the World's own), so a call naming `x` is the
first place the refusal can land: `callsOf`. Install and judge are the deployed ones. -/
def unlawfulCodec (x : D) : Program D :=
  { langProgram with run := (Lang.program Sim.dc.bytes (refusing x)).run }

/-- Plant 10: the run is handed each signed range without its last row (LS9). -/
def dropLastRow (rv : RowView D) : RowView D :=
  { points := rv.points
    ranges := fun parent rel => (rv.ranges parent rel).map fun qs => qs.map fun q => (q.1, q.2.1, q.2.2.dropLast) }

def dropRangeRow : Program D :=
  { langProgram with run := fun look rv p s m a r b => langProgram.run look (dropLastRow rv) p s m a r b }

/-- A package with nothing in it but its imports (LI). -/
def importer (imports : List ByteArray) : Package :=
  { imports, state := .record [], iface := .record [], body := .record [], methods := [], laws := [] }

/-- Which program the journey runs under. -/
inductive Mode
  | honest | skipJudge | eraseOccasion | erasePayload | dropCalls | rawInstall | bytesIds | skipLits
  | totalDigest | unlawfulCodec | dropRangeRow
  deriving DecidableEq

def Mode.program : Mode → Program D
  | .honest => langProgram
  | .skipJudge => Journey.skipJudge
  | .eraseOccasion => Journey.eraseOccasion
  | .erasePayload => Journey.erasePayload
  | .dropCalls => Journey.dropCalls
  | .rawInstall => Journey.rawInstall
  | .bytesIds => Journey.bytesIds
  | .skipLits => Journey.skipLits
  | .totalDigest => Journey.totalDigest
  -- its plant refuses the founder's own id, which `callRows` knows: it builds `unlawfulCodec a.id`
  | .unlawfulCodec => langProgram
  | .dropRangeRow => Journey.dropRangeRow

/-- A refusal by a law, with `why` in its reason. -/
def deniedWith (v why : String) : Bool := v.startsWith "refused lawDenied" && (v.splitOn why).length > 1

structure Run where
  st : Sim.State
  log : List String := []
  bad : Nat := 0

def note (r : Run) (line : String) (good : Bool) : Run :=
  { r with log := r.log ++ [s!"{if good then "ok  " else "FAIL"} {line}"], bad := r.bad + (if good then 0 else 1) }

/-- Submit on the Host path with program `prog`; the verdict's name. -/
def go (prog : Program D) (r : Run) (c : Call D) : Run × String × Option (Turn D) :=
  let X := ctxWith prog
  let st := r.st
  match Receive.submit X st.host c with
  | .error (.refused e) => ({ r with st }, s!"refused {Sim.nameOf e} {reprStr e}", none)
  | .error (.rejected e) => ({ r with st }, s!"rejected {Sim.nameOf e}", none)
  | .ok (t, w') => ({ r with st := { st with host := w', log := st.log ++ [.turn t] } }, "admitted", some t)

def totalOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat :=
  match w.live E obj with
  | some cell => match cell.slots.get (stateBase + 1) with
    | some b => match Wire.decodeData .nat b with
      | .ok (.nat n) => some n
      | _ => none
    | none => none
  | none => none

/-- A Relay object's state slot `i` (0 hits, 1 me, 2 next). -/
def slotOf (E : Kernel.Env D) (w : World D) (obj : D) (i : Nat) : Option ByteArray :=
  (w.live E obj).bind fun cell => cell.slots.get (stateBase + i)

def hitsOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat :=
  match (slotOf E w obj 0).map (Wire.decodeData .nat) with
  | some (.ok (.nat n)) => some n
  | _ => none

def meOf (E : Kernel.Env D) (w : World D) (obj : D) : Option ByteArray :=
  match (slotOf E w obj 1).map (Wire.decodeData .digest) with
  | some (.ok (.digest b)) => some b
  | _ => none

/-- `go`'s arguments: `rest` forwarded whole, `via` the grant the call goes through. -/
def relayArgs (rest via : ByteArray) : Option ByteArray :=
  Wire.encodeData RA (.record [("rest", .bytes rest), ("via", .digest via)])

/-- The arguments of a chain entered at the first of `grants` (grant `i` names object `i` on
object `i+1`): each level's arguments nest the next level's; the last object, which makes no call,
gets empty `rest` and `via = z` (an id: an argument typed `digest` must be one, LANG-38). -/
def chainArgs (z : ByteArray) : List ByteArray → Option ByteArray
  | [] => relayArgs .empty z
  | g :: gs => do relayArgs (← chainArgs z gs) g

/-- A Relay's `next` slot. -/
def nextSlot (next : Option ByteArray) : Option ByteArray :=
  Wire.encodeData (optTy .digest) (match next with
    | some n => .inj "some" (.digest n)
    | none => .inj "none" (.record []))

/-! ### LT: Mini's CappedTally over a relation (LANG-45 → LANG-49)

Mini `tests/objective-native/CappedTally.obend` at 2c27b08b (71 lines): a tally whose owner starts it
with a decider, whose decider answers with amounts within a patience, each answer an `add` DELTA the
kernel applies to the current view (so concurrent answers are all kept), under `cap: new.total <=
1000` and `grows: monotone(total)`. Since LANG-49 it is an INSERT-ONLY RELATION `answers` keyed
`{by, n}` whose head sums the `amount` column under a cap of 1000 (LANG-45's amendment): `grows` is
the relation's declaration (`retract false`), `cap` is the kernel's `relationCapped`, the total is
the head's sum. The guard `mine` refuses an answer filed under another member's name. Two answers
signed over one view are inserts at distinct keys, disjoint footprints: both land, in either order,
to the same rows (LT7, Mini's 630). -/

def tallyS : Ty := .record [("closes", .nat), ("decider", .digest)]
def tallyArg : Ty := .record [("amount", .nat), ("by", .digest), ("n", .nat)]
def answersDecl : RelDecl :=
  { key := [("by", .digest), ("n", .nat)], val := .record [("amount", .nat)], limit := 64,
    sum := some "amount", cap := 1000, retract := false, guard := some "mine" }
def tallyRels : List (Label × RelDecl) := [("answers", answersDecl)]
/-- A type as the resident writes it (printed, never restated). -/
def tyS (T : Ty) : String := (Print.ty T).getD "?"
def tallyStText : String := tyS tallyS
def tallyResText : String := tyS (resultTy tallyS [] (editTy tallyRels) 1)
def verdictText : String := "(sum (ok (rec)) (refused bytes))"
def tallyEditText : String := tyS (editTy tallyRels)
def tallyRelEditText : String := tyS (relEditTy answersDecl)
def tallyOptEditText : String := tyS (optTy (editTy tallyRels))

/-- CappedTally as a resident writes it. -/
def cappedTallyText : String := s!"
(package (imports)
  (state {tallyStText})
  (iface (rec (decider (-> {tallyStText} (-> {tallyStText} (-> {rq} {verdictText}))))
              (mine (-> {tallyStText} (-> {rq} (-> {tallyRelEditText} {verdictText}))))
              (reply (-> (rec) (-> {tallyStText} (-> {tyS tallyArg} (-> {rq} {tallyResText})))))))
  (methods reply)
  (laws decider)
  (rels (answers (key (by digest) (n nat)) (val (rec (amount nat))) (limit 64) (sum amount) (cap 1000)
                 (retract false) (guard mine)))
  (body
    (record
      (reply (fn (v (rec)) (s {tallyStText}) (a {tyS tallyArg}) (r {rq})
        (record (calls (record))
                (edits (record (e0 (inj {tallyOptEditText} some (inj {tallyEditText} answers
                  (inj {tallyRelEditText} insert (record (key (record (by (. a by)) (n (. a n))))
                                                         (val (record (amount (. a amount)))))))))))
                (state s))))
      (mine (fn (s {tallyStText}) (r {rq}) (e {tallyRelEditText})
        (case e
          (insert x (if (deq (. (. x key) by) (. r agent))
                        (inj {verdictText} ok (record))
                        (inj {verdictText} refused \"not yours\")))
          (upsert x (inj {verdictText} refused \"answers are final\")))))
      (decider (fn (old {tallyStText}) (new {tallyStText}) (r {rq})
        (case (. r occasion)
          (adopt x (inj {verdictText} ok (record)))
          (birth x (inj {verdictText} ok (record)))
          (invoke x
            (if (deq (. r agent) (. old decider))
                (if (<= (. r validUntil) (. old closes))
                    (inj {verdictText} ok (record))
                    (inj {verdictText} refused \"closed\"))
                (inj {verdictText} refused \"not the decider\")))
          (relaw x (inj {verdictText} ok (record)))
          (write x (inj {verdictText} ok (record)))))))))
"

/-- The required steps and machine ticks of an invoke on the Host's World, counted as THE BAR's row
counts them (`Protocol.Rows.Loopback.measureInvoke`): `Lang.Need.requiredOf` and `runMeasured`. -/
def measure (w : World D) (c : Call D) : Except String (Nat × Nat) :=
  let X := ctxWith langProgram
  match c.unsigned.body with
  | .invoke obj method args budget via =>
    let look := pinned X.env w c.unsigned.pins
    let rv := rowView X.env w c.unsigned
    let text : Receive.Refusal D → String := fun | .program s => s | e => e.name
    (do
      let (cell, p, r) ← invokeRun X look c c.unsigned.member obj method via
      let (_, _, _, ticks, _) ← Lang.runMeasured X.env.bytes X.digestOf look rv p (stateOf cell) method args r budget
      let req ← Lang.Need.requiredOf X.env.bytes X.digestOf look rv p (stateOf cell) method args r budget
      pure (req, ticks)).mapError text
  | _ => .error "not an invoke"

/-- A relation's head sum and count (the kernel's, `headOf`). -/
def headSum (w : World D) (obj : D) (rel : Nat) : Option Nat := (headOf Sim.env w.rows obj rel).map (·.2.1)
def headCount (w : World D) (obj : D) (rel : Nat) : Option Nat := (headOf Sim.env w.rows obj rel).map (·.1)

/-- A call signed by `m` with row pins and range reads (the Sim's `signed` has none). -/
def signedRows (st : Sim.State) (m : Sim.Member) (pins : List (D × D)) (rowPins : List (RowSlot D × D))
    (ranges : List (RangeRead D)) (body : Body D) : Call D :=
  let u : Unsigned D :=
    { world := st.host.origin, member := m.id, key := Sim.toy.pub m.key, notBefore := 0,
      validUntil := st.host.height + 1 + 100, pins, maxCharge := 1000000, body, rowPins, ranges }
  { unsigned := u, signature := Sim.toy.sign m.key (Sim.toy.ctx.callMessage u) }

/-- The LT rows: CappedTally through the real receivers. `b` is the decider. -/
def tallyRows (mode : Mode) (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let p ← match Read.readPackage cappedTallyText with
    | .ok p => pure p
    | .error e => return note r s!"LT0 read CappedTally: {e.text}" false
  let some pb := Wire.encodePackage p | return note r "LT0 CappedTally has no bytes" false
  let printed := (Print.package p).getD ""
  r := note r s!"LT0 CappedTally read from text: {cappedTallyText.length} chars, {(cappedTallyText.splitOn "\n").length - 2} lines; {pb.size} package bytes; printed {printed.length} chars" (printed != "" && p.rels == tallyRels)
  -- LT0b a key of bytes is not fixed-width: refused `relKey` at install
  let bad := { p with rels := [("answers", { answersDecl with key := [("by", .bytes), ("n", .nat)] })] }
  let some bb := Wire.encodePackage bad | return note r "LT0b no bytes" false
  let (_, v0b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install bb))
  r := note r s!"LT0b a tally keyed by bytes: {v0b}" (v0b.startsWith "refused program" && (v0b.splitOn "relKey answers").length > 1)
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LT1 A installs CappedTally: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LT1 no package id" false
  let some decB := Wire.encodeData .digest (.digest (Sim.dc.bytes b.id)) | return note r "LT no decider bytes" false
  -- a call's window ends `Sim.signed`'s 101 heights past the World: 200 leaves room, 50 does not (LT8)
  let closes := r.st.host.height + 200
  let some cl := nat64 closes | return note r "LT no closes bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg])
    (.create (some pkg) [] [(stateBase, cl), (stateBase + 1, decB)]))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "LT2 no object id" false
  r := note r2 s!"LT2 A starts a tally, decider B, closing at {closes}: {v2}; the head is born with it: sum {headSum r2.st.host obj 0}"
    (v2 == "admitted" && headSum r2.st.host obj 0 == some 0 && headCount r2.st.host obj 0 == some 0)
  let (rg, vg, tg) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0] none))
  r := note rg s!"LT3 A grants B invoke reply: {vg}" (vg == "admitted")
  let some gr := tg.bind fun t => (createdIds t).head? | return note r "LT3 no grant id" false
  let ans (by_ : Sim.Member) (n amt : Nat) : Option ByteArray :=
    Wire.encodeData tallyArg (.record [("amount", .nat amt), ("by", .digest (Sim.dc.bytes by_.id)), ("n", .nat n)])
  let some a600 := ans b 1 600 | return note r "LT no bytes" false
  let some a500 := ans b 2 500 | return note r "LT no bytes" false
  let some a10 := ans b 3 10 | return note r "LT no bytes" false
  let some a20 := ans b 4 20 | return note r "LT no bytes" false
  let some a10again := ans b 3 15 | return note r "LT no bytes" false
  let some aAsA := ans a 5 1 | return note r "LT no bytes" false
  let some aOwner := ans a 6 10 | return note r "LT no bytes" false
  let reply (m : Sim.Member) (args : ByteArray) (pins : List (D × D)) (via : Option D) : Call D :=
    Sim.signed r.st m m.key pins (.invoke obj 0 args 10000 via)
  let pinsB := Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]
  -- LT4 the decider answers 600: admitted, and measured as THE BAR measures an invoke
  let c4 := reply b a600 pinsB (some gr)
  let m4 := measure r.st.host c4
  let (r4, v4, _) := go prog r c4
  r := note r4 s!"LT4 B replies 600: {v4}, total {headSum r4.st.host obj 0}; required steps / ticks {match m4 with | .ok (q, t) => s!"{q} / {t}" | .error e => e}"
    (v4 == "admitted" && headSum r4.st.host obj 0 == some 600 && m4.isOk)
  -- LT5 600 + 500 is past the cap: the kernel's `relationCapped`, on the current head
  let (r5, v5, _) := go prog r (reply b a500 (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (some gr))
  r := note r5 s!"LT5 B replies 500: {v5}, total {headSum r5.st.host obj 0}"
    (v5.startsWith "rejected relationCapped" && headSum r5.st.host obj 0 == some 600)
  -- LT6 the owner is not the decider (Mini: the await names exactly one subject)
  let (r6, v6, _) := go prog r (reply a aOwner (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) none)
  r := { r6 with log := r.log, bad := r.bad }
  if mode = .skipJudge then
    return note r s!"PLANT skip-judge: LT6 A replies 10 must now be admitted: {v6}" (v6 == "admitted")
  r := note r s!"LT6 A replies 10: {v6}" (deniedWith v6 "decider: not the decider")
  -- LT6b the guard: B files an answer under A's name
  let (r6b, v6b, _) := go prog r (reply b aAsA (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (some gr))
  r := { r6b with log := r.log, bad := r.bad }
  r := note r s!"LT6b B files an answer as A: {v6b}" (deniedWith v6b "mine: not yours")
  -- LT7 two answers signed over the same view: both land, in both orders, to the same rows (Mini's 630)
  let pins7 := Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]
  let c7a := reply b a10 pins7 (some gr)
  let c7b := reply b a20 pins7 (some gr)
  let (q7b, w7b, _) := go prog r c7b
  let (q7ba, w7ba, _) := go prog q7b c7a
  let (r7a, v7a, _) := go prog r c7a
  r := note r7a s!"LT7a B replies 10: {v7a}" (v7a == "admitted")
  let (r7b, v7b, _) := go prog r c7b
  r := note r7b s!"LT7b B replies 20, signed over the same view as 10: {v7b}; total {headSum r7b.st.host obj 0} (Mini's 630)"
    (v7b == "admitted" && headSum r7b.st.host obj 0 == some 630 && headCount r7b.st.host obj 0 == some 3)
  r := note r s!"LT7c the other order (20 then 10): {w7b}, {w7ba}; the same rows root and cells root"
    (w7b == "admitted" && w7ba == "admitted" &&
      q7ba.st.host.rowsRoot Sim.env == r.st.host.rowsRoot Sim.env && q7ba.st.host.root Sim.env == r.st.host.root Sim.env)
  -- LT7d the same key again: an insert is a birth, `keyTaken` on the current World
  let (r7d, v7d, _) := go prog r (reply b a10again (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (some gr))
  r := note { r7d with log := r.log, bad := r.bad } s!"LT7d B replies again at key n=3: {v7d}" (v7d.startsWith "rejected keyTaken")
  -- LT8 patience: a tally closing before the answer's window ends refuses it (Mini's `timedOut`, as a height)
  let some cl8 := nat64 (r.st.host.height + 50) | return note r "LT8 no bytes" false
  let (r8, v8, t8) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg])
    (.create (some pkg) [] [(stateBase, cl8), (stateBase + 1, decB)]))
  r := note r8 s!"LT8a A starts a tally closing 50 heights on: {v8}" (v8 == "admitted")
  let some obj8 := t8.bind fun t => (createdIds t).head? | return note r "LT8 no object id" false
  let (r8g, v8g, t8g) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj8]) (.grant obj8 b.id [.invoke 0] none))
  r := note r8g s!"LT8b A grants B invoke reply: {v8g}" (v8g == "admitted")
  let some gr8 := t8g.bind fun t => (createdIds t).head? | return note r "LT8 no grant id" false
  let (r8c, v8c, _) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, obj8, pkg, gr8]) (.invoke obj8 0 a10 10000 (some gr8)))
  r := note r8c s!"LT8c B replies with a window 101 heights long: {v8c}" (deniedWith v8c "decider: closed")
  return r

/-! ### LS: Mini's CoAuthor over relations (LANG-47 → LANG-49)

Mini `world/story/CoAuthor.obend` at 2c27b08b (486 lines): a crowd writes a story one chapter a round;
any author proposes one passage and may edit it while the round is open, each elector votes once,
and after the window anyone seals the round: the most-voted proposal (ties to the earliest) becomes
the round's chapter, forever. Mini's three lists are RELATIONS under the story, all insert-only:
`proposals` keyed `{round, slot}`, `authors` `{round, author}` (a second proposal by one author is
an insert at a taken key, the kernel's `keyTaken`: Mini's `alreadyProposed`), `ballots`
`{round, voter}` (`alreadyVoted`, the same way) and `chapters` `{number}`. The state keeps only the
clock: the round, when it closes, the window, and `why`. A method that succeeds returns the state
UNCHANGED (it writes no cell, so acts over one view touch disjoint rows and commute: LS10); one that
refuses sets `why` and edits nothing, and the one law `react` refuses an invoke whose new `why` is not
empty, by it. `edit` and `vote` read the proposal the signer pinned (a point read) and upsert it;
`seal` reads the round's proposals as ONE signed range (the key's first field, the round, as the
prefix) and inserts the most-voted row (ties to the earliest slot, the walk a chain of `let`s) as the
round's chapter. Now is the signer's window: a round is open to an act whose window ends by `closes`,
and a seal must start after it. The hand port before relations (LANG-47: lists bounded to 4 slots,
a bitmask of who voted, a `version` the law compared) was 63,865 chars, 142 lines and 52,965
package bytes; LS0 prints this one's. -/

def coS : Ty := .record [("closes", .nat), ("round", .nat), ("why", .bytes), ("window", .nat)]
def passageTy : Ty := .record [("author", .digest), ("text", .bytes), ("votes", .nat)]
def slotTy : Ty := .record [("slot", .nat)]
def coRel (key : List (Label × Ty)) (val : Ty) : RelDecl :=
  { key, val, limit := 4096, sum := none, cap := 0, retract := false, guard := none }
def authorsDecl : RelDecl := coRel [("round", .nat), ("author", .digest)] slotTy
def ballotsDecl : RelDecl := coRel [("round", .nat), ("voter", .digest)] slotTy
def chaptersDecl : RelDecl := coRel [("number", .nat)] passageTy
def proposalsDecl : RelDecl := coRel [("round", .nat), ("slot", .nat)] passageTy
def coRels : List (Label × RelDecl) :=
  [("authors", authorsDecl), ("ballots", ballotsDecl), ("chapters", chaptersDecl), ("proposals", proposalsDecl)]
/-- `edit` and `vote` read one pinned proposal; `seal` the round's proposals, one range of 8. -/
def pinRead : List (Label × RelRead) := [("proposals", ⟨1, none⟩)]
def rangeRead : List (Label × RelRead) := [("proposals", ⟨0, some (1, 8)⟩)]
def proposeArg : Ty := .record [("slot", .nat), ("text", .bytes)]
def voteArg : Ty := .record [("slot", .nat)]
def coE : Ty := editTy coRels
def coMTy (R A : Ty) (es : Nat) : Ty := methodTy coS A [] R coE es
def coST : String := tyS coS
def coOE : String := tyS (optTy coE)
/-- One edit slot holding edit `arm` of relation `rel`. -/
def coEdit (rel : Label) (d : RelDecl) (arm key val : String) : String :=
  s!"(inj {coOE} some (inj {tyS coE} {rel} (inj {tyS (relEditTy d)} {arm} (record (key {key}) (val {val})))))"
def coNoEdit : String := s!"(inj {coOE} none (record))"
def coEdits (es : List String) : String :=
  "(record" ++ String.join (es.zipIdx.map fun p => s!" (e{p.2} {p.1})") ++ ")"
/-- A success: the edits, the state unchanged. -/
def coOk (es : List String) : String := s!"(record (calls (record)) (edits {coEdits es}) (state s))"
/-- `body` with `no`, the refusal by a reason: no edits, the state with `why` set. -/
def coNo (es : Nat) (body : String) : String :=
  s!"(let no (-> bytes {tyS (resultTy coS [] coE es)})
    (lam y bytes (record (calls (record)) (edits {coEdits (List.replicate es coNoEdit)}) (state (extend s (why y)))))
    {body})"
def coHead (R A : Ty) : String := s!"(fn (v {tyS R}) (s {coST}) (a {tyS A}) (r {rq})"
def coOpen : String := "(<= (. r validUntil) (. s closes))"
/-- `ok` with `p` the pinned proposal row and `q` its value, when it is this round's at `a.slot`. -/
def coPointed (ok : String) : String :=
  s!"(case (. (. v proposals) p0) (none x (no \"unknown\"))
      (some p (case (. p val) (none x (no \"unknown\"))
        (some q (if (if (== (. (. p key) round) (. s round)) (== (. (. p key) slot) (. a slot)) false)
          {ok} (no \"unknown\"))))))"

/-- `propose {slot, text}`: late, slot, else the passage and its author (`keyTaken`: proposed). -/
def coPropose : String :=
  s!"{coHead (.record []) proposeArg}
  {coNo 2 s!"(if {coOpen}
    (if (< (. a slot) 8)
      {coOk [coEdit "authors" authorsDecl "insert" "(record (author (. r agent)) (round (. s round)))" "(record (slot (. a slot)))",
             coEdit "proposals" proposalsDecl "insert" "(record (round (. s round)) (slot (. a slot)))"
               "(record (author (. r agent)) (text (. a text)) (votes 0))"]}
      (no \"slot\"))
    (no \"late\"))"})"

/-- `edit {slot, text}`: late, unknown, notAuthor, else the pinned passage rewritten. -/
def coEditM : String :=
  s!"{coHead (readsTy coRels pinRead) proposeArg}
  {coNo 1 s!"(if {coOpen}
    {coPointed s!"(if (deq (. q author) (. r agent))
      {coOk [coEdit "proposals" proposalsDecl "upsert" "(. p key)" "(extend q (text (. a text)))"]}
      (no \"notAuthor\"))"}
    (no \"late\"))"})"

/-- `vote {slot}`: late, unknown, else the ballot (`keyTaken`: voted) and the pinned passage's count. -/
def coVote : String :=
  s!"{coHead (readsTy coRels pinRead) voteArg}
  {coNo 2 s!"(if {coOpen}
    {coPointed (coOk [coEdit "ballots" ballotsDecl "insert" "(record (round (. s round)) (voter (. r agent)))" "(record (slot (. a slot)))",
                      coEdit "proposals" proposalsDecl "upsert" "(. p key)" "(extend q (votes (+ (. q votes) 1)))"])}
    (no \"late\"))"})"

/-- `seal {}`: early, round, empty, else the leader of the signed range (a row replaces it only with
strictly more votes, so a tie keeps the earlier slot) is the round's chapter and the next round opens. -/
def coSeal : String :=
  let rg := "(. (. v proposals) range)"
  let rowT := tyS (rowTy proposalsDecl)
  let better (cur : String) (i : Nat) :=
    s!"(case (. (. {rg} rows) r{i}) (none x {cur}) (some q (if (< (. (. {cur} val) votes) (. (. q val) votes)) q {cur})))"
  let done (w : String) :=
    s!"(record (calls (record))
      (edits {coEdits [coEdit "chapters" chaptersDecl "insert" "(record (number (. s round)))" s!"(. {w} val)"]})
      (state (extend s (closes (+ (. s closes) (. s window))) (round (+ (. s round) 1)))))"
  let rec chain : List Nat → String → String
    | [], cur => done cur
    | i :: is, cur => s!"(let b{i} {rowT} {better cur i}\n      {chain is s!"b{i}"})"
  s!"{coHead (readsTy coRels rangeRead) (.record [])}
  {coNo 1 s!"(if (<= (. r notBefore) (. s closes)) (no \"early\")
    (if (== (. (. {rg} pre) round) (. s round))
      (case (. (. {rg} rows) r0) (none x (no \"empty\"))
        (some b0 {chain [1, 2, 3, 4, 5, 6, 7] "b0"}))
      (no \"round\")))"})"

/-- The one law: an invoke whose new state names a reason is refused by it; only methods move a story. -/
def coLaw : String :=
  let ok := s!"(inj {verdictText} ok (record))"
  s!"(fn (old {coST}) (new {coST}) (r {rq})
  (case (. r occasion)
    (adopt x {ok})
    (birth x (if (beq (. new why) \"\") {ok} (inj {verdictText} refused \"seeded\")))
    (invoke m (if (beq (. new why) \"\") {ok} (inj {verdictText} refused (. new why))))
    (relaw x {ok})
    (write x (inj {verdictText} refused \"only its methods move a story\"))))"

def coRelText (ℓ : Label) (d : RelDecl) : String :=
  s!"({ℓ} (key{String.join (d.key.map fun f => s!" ({f.1} {tyS f.2})")}) (val {tyS d.val}) (limit {d.limit}) (sum) (cap 0) (retract false) (guard))"

/-- CoAuthor as a resident writes it. -/
def coAuthorText : String := s!"
(package (imports)
  (state {coST})
  (iface (rec (edit {tyS (coMTy (readsTy coRels pinRead) proposeArg 1)})
              (propose {tyS (coMTy (.record []) proposeArg 2)})
              (react (-> {coST} (-> {coST} (-> {rq} {verdictText}))))
              (seal {tyS (coMTy (readsTy coRels rangeRead) (.record []) 1)})
              (vote {tyS (coMTy (readsTy coRels pinRead) voteArg 2)})))
  (methods propose edit vote seal)
  (laws react)
  (rels {String.intercalate "\n        " (coRels.map fun r => coRelText r.1 r.2)})
  (body
    (record
      (propose {coPropose})
      (edit {coEditM})
      (vote {coVote})
      (seal {coSeal})
      (react {coLaw}))))
"

/-- A call signed by `m` with the window `[nb, vu]`, its row pins and its range reads (the Sim's
`signed` fixes `[0, height + 101]` and reads no rows). -/
def signedAt (st : Sim.State) (m : Sim.Member) (pins : List (D × D)) (body : Body D) (nb vu : Nat)
    (rowPins : List (RowSlot D × D) := []) (ranges : List (RangeRead D) := []) : Call D :=
  let u : Unsigned D :=
    { world := st.host.origin, member := m.id, key := Sim.toy.pub m.key, notBefore := nb,
      validUntil := vu, pins, maxCharge := 1000000, body, rowPins, ranges }
  { unsigned := u, signature := Sim.toy.sign m.key (Sim.toy.ctx.callMessage u) }

/-- The story's row of relation `rel` at `key`, read at the relation's value type. -/
def storyRow (w : World D) (obj : D) (rel : Nat) (d : RelDecl) (key : Data) : Option Data :=
  match keyBytes d key with
  | none => none
  | some k =>
    match rowAt Sim.env w.rows (.row ⟨obj, rel, k⟩) with
    | some (.row _ v) => (Wire.decodeData d.val v).toOption
    | _ => none

/-- A passage's text and votes. -/
def passageIs (d : Option Data) (txt : String) (votes : Nat) : Bool :=
  match d.bind (·.field "text"), d.bind (·.field "votes") with
  | some (.bytes t), some (.nat n) => t == txt.toUTF8 && n == votes
  | _, _ => false

/-- The LS rows: CoAuthor through the real receivers. `a` and `b` are authors and electors. -/
def storyRows (mode : Mode) (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let p ← match Read.readPackage coAuthorText with
    | .ok p => pure p
    | .error e => return note r s!"LS0 read CoAuthor: {e.text}" false
  let some pb := Wire.encodePackage p | return note r "LS0 CoAuthor has no bytes" false
  let printed := (Print.package p).getD ""
  r := note r s!"LS0 CoAuthor read from text: {coAuthorText.length} chars, {(coAuthorText.splitOn "\n").length - 2} lines; {pb.size} package bytes; printed {printed.length} chars (by hand over lists: 63865 chars, 142 lines, 52965 package bytes)"
    (printed != "" && p.rels == coRels)
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LS1 A installs CoAuthor: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LS1 no package id" false
  let closes := r.st.host.height + 12
  let seedText := s!"(record (closes {closes}) (round 1) (why \"\") (window 20))"
  let seed ← match Read.readData p.state seedText with
    | .ok (.record ds) => match stateSlots (recordRow p.state) ds 0 with
      | some s => pure s
      | none => return note r "LS2 seed has no bytes" false
    | .ok _ => return note r "LS2 seed is not a record" false
    | .error e => return note r s!"LS2 read seed: {e.text}" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 "LS2 no object id" false
  r := note r2 s!"LS2 A starts a story closing at {closes}: {v2}; its four relations are born empty"
    (v2 == "admitted" && [0, 1, 2, 3].all fun i => headCount r2.st.host obj i == some 0)
  -- every member acts through a grant on every method (KERNEL-25: invoke is the owner's, or granted)
  let (rg, vg, tg) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj])
    (.grant obj b.id [.invoke 0, .invoke 1, .invoke 2, .invoke 3] none))
  r := note rg s!"LS3 A grants B propose, edit, vote, seal: {vg}" (vg == "admitted")
  let some gr := tg.bind fun t => (createdIds t).head? | return note r "LS3 no grant id" false
  let args (T : Ty) (d : Data) : ByteArray := (Wire.encodeData T d).getD .empty
  let proposeA (i : Nat) (s : String) := args proposeArg (.record [("slot", .nat i), ("text", .bytes s.toUTF8)])
  let voteA (i : Nat) := args voteArg (.record [("slot", .nat i)])
  let noA := args (.record []) (.record [])
  let pinsOf (r : Run) (m : Sim.Member) := Sim.S.pinsFor r.st.host ([m.id, obj, pkg] ++ if m.id == b.id then [gr] else [])
  let viaOf (m : Sim.Member) : Option D := if m.id == b.id then some gr else none
  -- the proposal at `{round, slot}`, pinned at what the signer sees on `w`
  let pinP (w : World D) (round slot : Nat) : List (RowSlot D × D) :=
    match keyBytes proposalsDecl (.record [("round", .nat round), ("slot", .nat slot)]) with
    | some k => let s : RowSlot D := .row ⟨obj, 3, k⟩; [(s, rowPin Sim.env (rowAt Sim.env w.rows s))]
    | none => []
  -- the round's proposals as one range read, pinned at the listing the signer sees on `w`
  let rangeP (w : World D) (round : Nat) : List (RangeRead D) :=
    match Wire.encodeData (keyWireTy proposalsDecl 1) (.record [("k0", .nat round)]), headOf Sim.env w.rows obj 3 with
    | some pre, some (_, _, _, _, width, _) =>
      match rangeRows Sim.env w.rows obj 3 width pre 8 with
      | some l => [{ parent := obj, rel := 3, pre, most := 8, seen := rangePin Sim.env obj 3 width pre l }]
      | none => []
    | _, _ => []
  let call (r : Run) (m : Sim.Member) (method : Nat) (x : ByteArray) (nb vu : Nat)
      (rowPins : List (RowSlot D × D)) (ranges : List (RangeRead D)) : Call D :=
    signedAt r.st m (pinsOf r m) (.invoke obj method x 100000 (viaOf m)) nb vu rowPins ranges
  let cost (c : Call D) (w : World D) (t : Option (Turn D)) : String :=
    s!"required steps / ticks {match measure w c with | .ok (q, k) => s!"{q} / {k}" | .error e => e}; its turn logs {(t.map Turn.logWeight).getD 0} bytes"
  let passage (w : World D) (round slot : Nat) : Option Data :=
    storyRow w obj 3 proposalsDecl (.record [("round", .nat round), ("slot", .nat slot)])
  -- LS4/LS5 two proposals; a second by the same author is the kernel's `keyTaken` on `authors`
  let c4 := call r a 0 (proposeA 0 "a light on the rock") 0 closes [] []
  let (r4, v4, t4) := go prog r c4
  r := note r4 s!"LS4 A proposes \"a light on the rock\" at slot 0: {v4}; {cost c4 r.st.host t4}"
    (v4 == "admitted" && passageIs (passage r4.st.host 1 0) "a light on the rock" 0 && headCount r4.st.host obj 0 == some 1)
  let (r5, v5, _) := go prog r (call r b 0 (proposeA 1 "a ship in the fog") 0 closes [] [])
  r := note r5 s!"LS5 B proposes \"a ship in the fog\" at slot 1: {v5}" (v5 == "admitted")
  let (r5b, v5b, _) := go prog r (call r a 0 (proposeA 2 "another") 0 closes [] [])
  r := note { r5b with log := r.log, bad := r.bad } s!"LS5b A proposes again, at slot 2: {v5b} (Mini's alreadyProposed)" (v5b.startsWith "rejected keyTaken")
  -- LS6 votes: B for slot 1 (counted), B again (`keyTaken` on `ballots`), A for an empty slot (unknown)
  let c6 := call r b 2 (voteA 1) 0 closes (pinP r.st.host 1 1) []
  let (r6, v6, t6) := go prog r c6
  r := note r6 s!"LS6 B votes for slot 1: {v6}; {cost c6 r.st.host t6}"
    (v6 == "admitted" && passageIs (passage r6.st.host 1 1) "a ship in the fog" 1)
  let (r6b, v6b, _) := go prog r (call r b 2 (voteA 0) 0 closes (pinP r.st.host 1 0) [])
  r := note { r6b with log := r.log, bad := r.bad } s!"LS6b B votes again, for slot 0: {v6b} (Mini's alreadyVoted)" (v6b.startsWith "rejected keyTaken")
  let (r6c, v6c, _) := go prog r (call r a 2 (voteA 5) 0 closes (pinP r.st.host 1 5) [])
  if mode = .skipJudge then
    return note r6c s!"PLANT skip-judge: LS6c A's vote for the empty slot 5 must now be ADMITTED: {v6c}" (v6c == "admitted")
  r := note r6c s!"LS6c A votes for the empty slot 5: {v6c}" (deniedWith v6c "react: unknown")
  -- LS7 edits: A may not edit B's passage; B rewrites it
  let (r7, v7, _) := go prog r (call r a 1 (proposeA 1 "mine now") 0 closes (pinP r.st.host 1 1) [])
  r := note r7 s!"LS7 A edits B's passage: {v7}" (deniedWith v7 "react: notAuthor")
  let (r7b, v7b, _) := go prog r (call r b 1 (proposeA 1 "a ship in the mist") 0 closes (pinP r.st.host 1 1) [])
  r := note r7b s!"LS7b B rewrites its passage: {v7b}"
    (v7b == "admitted" && passageIs (passage r7b.st.host 1 1) "a ship in the mist" 1)
  -- LS8 a seal inside the window is early
  let (r8, v8, _) := go prog r (call r a 3 noA 0 (r.st.host.height + 50) [] (rangeP r.st.host 1))
  r := note r8 s!"LS8 A seals while the round is open: {v8}" (deniedWith v8 "react: early")
  -- the World moves past `closes` (lawless data objects, one turn each)
  for _ in [0:20] do
    if r.st.host.height ≤ closes then
      let (rp, _, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
      r := { rp with log := r.log, bad := r.bad }
  -- LS9 the seal over the round's one range: B's rewritten passage (1 vote, the LAST row) beats A's
  let hs := r.st.host.height
  let c9 := call r a 3 noA (closes + 1) (hs + 50) [] (rangeP r.st.host 1)
  let (r9, v9, t9) := go prog r c9
  let chapter := storyRow r9.st.host obj 2 chaptersDecl (.record [("number", .nat 1)])
  if mode = .dropRangeRow then
    return note r9 s!"PLANT drop-range-row: LS9 the seal is still admitted ({v9}) but chapter 1 is A's passage, the winner never seen"
      (v9 == "admitted" && passageIs chapter "a light on the rock" 0)
  r := note r9 s!"LS9 A seals after the window: {v9}; chapter 1 is B's rewritten passage with 1 vote: {passageIs chapter "a ship in the mist" 1}; {cost c9 r.st.host t9}"
    (v9 == "admitted" && passageIs chapter "a ship in the mist" 1 && headCount r9.st.host obj 2 == some 1)
  -- LS10 round two: two proposals signed over ONE view land, in both orders, to the same World
  let closes2 := closes + 20
  let c10a := call r a 0 (proposeA 0 "the keeper wakes") 0 closes2 [] []
  let c10b := call r b 0 (proposeA 1 "the lamp goes out") 0 closes2 [] []
  let (q10b, w10b, _) := go prog r c10b
  let (q10ba, w10ba, _) := go prog q10b c10a
  let (r10a, v10a, _) := go prog r c10a
  r := note r10a s!"LS10a A proposes in round two: {v10a}" (v10a == "admitted")
  let (r10b, v10b, _) := go prog r c10b
  r := note r10b s!"LS10b B proposes in round two, signed over the same view as A: {v10b}"
    (v10b == "admitted" && headCount r10b.st.host obj 3 == some 4)
  r := note r s!"LS10c the other order (B then A): {w10b}, {w10ba}; the same rows root and cells root"
    (w10b == "admitted" && w10ba == "admitted" &&
      q10ba.st.host.rowsRoot Sim.env == r.st.host.rowsRoot Sim.env && q10ba.st.host.root Sim.env == r.st.host.root Sim.env)
  -- LS11 a vote and an edit of the SAME proposal over one view: the pinned row moved, honestly stale
  let pin11 := pinP r.st.host 2 1
  let c11a := call r a 2 (voteA 1) 0 closes2 pin11 []
  let c11b := call r b 1 (proposeA 1 "the lamp burns") 0 closes2 pin11 []
  let (r11a, v11a, _) := go prog r c11a
  r := note r11a s!"LS11a A votes for B's round-two passage: {v11a}" (v11a == "admitted")
  let (r11b, v11b, _) := go prog r c11b
  r := note { r11b with log := r.log, bad := r.bad } s!"LS11b B edits it, signed over the same view as the vote: {v11b}"
    (v11b.startsWith "rejected stale" && passageIs (passage r.st.host 2 1) "the lamp goes out" 1)
  return r

/-- The install-closure rows (LI, LANG-35): `Top` imports `Mid` imports `Owned` (`pkg`). -/
def installRows (mode : Mode) (r0 : Run) (a : Sim.Member) (pkg : D) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let some midBytes := Wire.encodePackage (importer [Sim.dc.bytes pkg]) | return note r "LI Mid has no bytes" false
  let (ri1, vi1, ti1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.install midBytes))
  r := note ri1 s!"LI1 install Mid importing Owned: {vi1}" (vi1 == "admitted")
  let some mid := ti1.bind fun t => (createdIds t).head? | return note r "LI no Mid id" false
  let some topBytes := Wire.encodePackage (importer [Sim.dc.bytes mid]) | return note r "LI Top has no bytes" false
  let (ri2, vi2, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, mid]) (.install topBytes))
  if mode = .rawInstall then
    return note ri2 s!"PLANT raw-install: LI2 Top pinning only Mid must now be admitted: {vi2}" (vi2 == "admitted")
  r := note ri2 s!"LI2 install Top importing Mid, pinning only Mid: {vi2}" (vi2.startsWith "refused unpinned" && (vi2.splitOn s!"unpinned {reprStr pkg}").length > 1)
  let (ri3, vi3, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, mid, pkg]) (.install topBytes))
  r := note ri3 s!"LI3 install Top pinning Mid and Owned: {vi3}" (vi3 == "admitted")
  return r

/-- The call rows (LC): Relay chains through the real receivers. -/
def callRows (mode : Mode) (r0 : Run) (a : Sim.Member) : Run := Id.run do
  let prog := if mode = .unlawfulCodec then unlawfulCodec a.id else mode.program
  let mut r := r0
  -- LC calls: a chain of six Relay objects o0 … o5, o5 last (empty `next`); grant k lets o_k invoke o_{k+1}
  let some relayBytes := Wire.encodePackage relay | return note r "LC Relay has no bytes" false
  let (rc0, vc0, tc0) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install relayBytes))
  r := note rc0 s!"LC0 install Relay: {vc0}" (vc0 == "admitted")
  let some rid := tc0.bind fun t => (createdIds t).head? | return note r "LC no Relay id" false
  let some h0 := nat64 0 | return note r "LC no bytes for 0" false
  let aB := Sim.dc.bytes a.id
  let some meB := Wire.encodeData .digest (.digest aB) | return note r "LC no me bytes" false
  let some noneB := nextSlot none | return note r "LC no next bytes" false
  -- LD5 (LANG-41) a run's ids came from where ids enter: a call naming the signer is read by callsOf
  if mode = .unlawfulCodec || mode = .honest then
    let some cb := Wire.encodePackage caller | return note r "LD5 Caller has no bytes" false
    let (rd5, vd5, td5) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install cb))
    r := note rd5 s!"LD5a install Caller: {vd5}" (vd5 == "admitted")
    let some cid := td5.bind fun t => (createdIds t).head? | return note r "LD5 no Caller id" false
    let (rd5b, vd5b, td5b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, cid])
      (.create (some cid) [] []))
    r := note rd5b s!"LD5b A creates a Caller: {vd5b}" (vd5b == "admitted")
    let some co := td5b.bind fun t => (createdIds t).head? | return note r "LD5 no object id" false
    let some noArgs := Wire.encodeData CA (.record []) | return note r "LD5 no arguments" false
    let (rd5c, vd5c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, cid, co])
      (.invoke co 0 noArgs 10000 none))
    if mode = .unlawfulCodec then
      return note rd5c s!"PLANT unlawful-codec: LD5c a call naming the signer must now be refused by callsOf: {vd5c}"
        (vd5c.startsWith "refused program" && (vd5c.splitOn "calls: c0 obj: not a digest").length > 1)
    r := note rd5c s!"LD5c A invokes it, calling A as an object: {vd5c}" (vd5c.startsWith "refused wrongKind")
  -- LD (LANG-38) a digest is a type: what bytes could not refuse, by name
  if mode = .bytesIds || mode = .honest then
    let some b1 := Wire.encodePackage relayBytesId | return note r "LD1 no bytes" false
    let (_, vd1, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install b1))
    if mode = .bytesIds then
      return note r s!"PLANT bytes-ids: LD1 a call naming its callee by bytes must now install: {vd1}" (vd1 == "admitted")
    r := note r s!"LD1 install a Relay whose call names its callee by a bytes literal: {vd1}"
      (vd1.startsWith "refused program" && (vd1.splitOn "illTyped payload").length > 1)
  if mode = .skipLits || mode = .honest then
    let some b2 := Wire.encodePackage badListed | return note r "LD2 no bytes" false
    let (_, vd2, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install b2))
    if mode = .skipLits then
      return note r s!"PLANT skip-lits: LD2 an allowlist of a non-digest id must now install: {vd2}" (vd2 == "admitted")
    r := note r s!"LD2 install an allowlist naming a 3-byte id: {vd2}"
      (vd2.startsWith "refused program" && (vd2.splitOn "notDigest").length > 1)
  let some badNext := nextSlot (some "xyz".toUTF8) | return note r "LD3 no bytes" false
  let (rd3, vd3, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] [(stateBase, h0), (stateBase + 1, meB), (stateBase + 2, badNext)]))
  if mode = .totalDigest then
    r := note rd3 s!"PLANT total-digest: LD3 a seed whose next is not a digest must now be admitted: {vd3}" (vd3 == "admitted")
  else if mode != .skipJudge then
    r := note r s!"LD3 A creates a Relay whose next is not a digest: {vd3}"
      (vd3.startsWith "refused lawDenied" && (vd3.splitOn "state field next: not a digest").length > 1)
  let (rd4, vd4, td4) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] [(stateBase, h0), (stateBase + 1, meB), (stateBase + 2, noneB)]))
  r := note rd4 s!"LD4a A creates a last Relay: {vd4}" (vd4 == "admitted")
  let some lastO := td4.bind fun t => (createdIds t).head? | return note r "LD4 no object id" false
  let some badArgs := relayArgs .empty "xyz".toUTF8 | return note r "LD4 no arguments" false
  let (rd4b, vd4b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid, lastO])
    (.invoke lastO 0 badArgs 10000 none))
  if mode = .totalDigest then
    return note rd4b s!"PLANT total-digest: LD4b arguments whose via is not a digest must now be admitted: {vd4b}" (vd4b == "admitted")
  r := note rd4b s!"LD4b A invokes it with a via that is not a digest: {vd4b}"
    (vd4b.startsWith "refused program" && (vd4b.splitOn "arguments: not a digest").length > 1)
  let mut objs : List D := []
  for _ in [0:6] do
    let some nextB := nextSlot (objs.head?.map Sim.dc.bytes) | return note r "LC no next bytes" false
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
      (.create (some rid) [] [(stateBase, h0), (stateBase + 1, meB), (stateBase + 2, nextB)]))
    r := note rk s!"LC1 A creates Relay o{5 - objs.length}: {vk}" (vk == "admitted")
    let some o := tk.bind fun t => (createdIds t).head? | return note r "LC no object id" false
    objs := o :: objs
  let mut grants : List D := []
  for (x, y) in objs.zip objs.tail do
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, x, y]) (.grant y x [.invoke 0] none))
    r := note rk s!"LC2 A grants o_k invoke 0 on o_k+1: {vk}" (vk == "admitted")
    let some gk := tk.bind fun t => (createdIds t).head? | return note r "LC no grant id" false
    grants := grants ++ [gk]
  let gBytes := grants.map Sim.dc.bytes
  let pinsAll := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let o0 := objs.headD 0
  let o1 := objs.getD 1 0
  let o5 := objs.getD 5 0
  -- LC3 entered at o1: o2 … o5 at depths 1 … 4 = callDepthMax, admitted; every object ran once
  let some args1 := chainArgs aB gBytes.tail | return note r "LC3 no arguments" false
  let (rc3, vc3, _) := go prog r (Sim.signed r.st a a.key pinsAll (.invoke o1 0 args1 10000 none))
  r := { rc3 with log := r.log, bad := r.bad }
  let hit5 := hitsOf Sim.env r.st.host o5
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC3 the chain's end must now be untouched: {vc3}, o5 hits {hit5}" (vc3 == "admitted" && hit5 == some 0)
  else
    r := note r s!"LC3 A invokes o1, calls 4 deep: {vc3}; o5 hits {hit5}, o5 sees itself as self {meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5)}"
      (vc3 == "admitted" && hit5 == some 1 && hitsOf Sim.env r.st.host o1 == some 1 &&
        meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5))
  -- LC4 entered at o0: o5 would be at depth 5, past callDepthMax
  let some args0 := chainArgs aB gBytes | return note r "LC4 no arguments" false
  let pins4 := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let (rc4, vc4, _) := go prog r (Sim.signed r.st a a.key pins4 (.invoke o0 0 args0 10000 none))
  r := { rc4 with log := r.log, bad := r.bad }
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC4 five deep must now be admitted: {vc4}" (vc4 == "admitted")
  else
    r := note r s!"LC4 A invokes o0, calls 5 deep: {vc4}" (vc4.startsWith "refused callTooDeep")
  -- LC6 a method with more call slots than callsMax is not a method: install refuses it by name
  let some nineBytes := Wire.encodePackage nineCalls | return note r "LC6 NineCalls has no bytes" false
  let (rc6, vc6, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install nineBytes))
  r := note rc6 s!"LC6 install a method with {Kernel.Bounds.callsMax + 1} call slots: {vc6}"
    (vc6.startsWith "refused program" && (vc6.splitOn "badMethod go").length > 1)
  return r

/-! ### LR: a method and a law refuse by name (LANG-51)

`Gate` holds a natural. Its method `put {note, n}` refuses `note 0..4` unless the note is at most
four bytes (`len<=`), and its law `small` refuses `over 100` by `refuse` rather than a `refused`
verdict. Through the real receivers: a method's refusal is `program "put: refused note 0..4"`, a
law's is `lawDenied … "small: refused over 100"`, and the four-byte note at the bound lands. -/

def gateS : Ty := .record [("n", .nat)]
def gateArg : Ty := .record [("n", .nat), ("note", .bytes)]
def gateRes : String := tyS (resultTy gateS)

def gateText : String := s!"
(package (imports)
  (state {tyS gateS})
  (iface (rec (put (-> (rec) (-> {tyS gateS} (-> {tyS gateArg} (-> {rq} {gateRes})))))
              (small (-> {tyS gateS} (-> {tyS gateS} (-> {rq} {verdictText}))))))
  (methods put)
  (laws small)
  (rels)
  (body
    (record
      (put (fn (v (rec)) (s {tyS gateS}) (a {tyS gateArg}) (r {rq})
        (if (len<= (. a note) 4)
            (record (calls (record)) (edits (record)) (state (record (n (. a n)))))
            (refuse {gateRes} \"note 0..4\"))))
      (small (fn (old {tyS gateS}) (new {tyS gateS}) (r {rq})
        (if (<= (. new n) 100) (inj {verdictText} ok (record)) (refuse {verdictText} \"over 100\")))))))
"

def gateRows (mode : Mode) (r0 : Run) (a : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let p ← match Read.readPackage gateText with
    | .ok p => pure p
    | .error e => return note r s!"LR0 read Gate: {e.text}" false
  let some pb := Wire.encodePackage p | return note r "LR0 Gate has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LR0 A installs Gate (a refusing method and law): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LR0 no package id" false
  let some n0 := nat64 0 | return note r "LR no bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg])
    (.create (some pkg) [] [(stateBase, n0)]))
  r := note r2 s!"LR1 A creates a Gate at 0: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "LR1 no object id" false
  let put (n : Nat) (txt : String) : Option ByteArray :=
    Wire.encodeData gateArg (.record [("n", .nat n), ("note", .bytes txt.toUTF8)])
  let call (args : ByteArray) : Call D :=
    Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 args 10000 none)
  let some aLong := put 5 "fives" | return note r "LR no bytes" false
  let (_, v3, _) := go prog r (call aLong)
  r := note r s!"LR2 put with a five-byte note: {v3}"
    (v3.startsWith "refused program" && (v3.splitOn "put: refused note 0..4").length > 1)
  let some aBig := put 500 "ok" | return note r "LR no bytes" false
  let (_, v4, _) := go prog r (call aBig)
  r := note r s!"LR3 put 500: {v4}" (deniedWith v4 "small: refused over 100")
  let some aFour := put 7 "four" | return note r "LR no bytes" false
  let (r5, v5, _) := go prog r (call aFour)
  r := note r5 s!"LR4 put 7 with a four-byte note (at the bound): {v5}; slot {slotOf Sim.env r5.st.host obj 0 |>.map (·.toList)}"
    (v5 == "admitted" && slotOf Sim.env r5.st.host obj 0 == nat64 7)
  return r

def journey (mode : Mode) : Run := Id.run do
  let prog := mode.program
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := ctxWith prog
  let g ← match genesis X Sim.worldName (Sim.nonceOf 0) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
  let mut r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  if mode = .bytesIds || mode = .skipLits || mode = .totalDigest || mode = .unlawfulCodec then
    return callRows mode r a
  if mode = .dropRangeRow then
    return storyRows mode r a b
  -- L0 the resident's text reads to exactly the package
  let some ownedBytes := Wire.encodePackage owned | return note r "L0 Owned has no bytes" false
  let some illBytes := Wire.encodePackage illTyped | return note r "L0 illTyped has no bytes" false
  match Read.readPackage ownedText with
  | .error e => r := note r s!"L0 read Owned: {e.text}" false
  | .ok q =>
    let same := Wire.encodePackage q == some ownedBytes
    r := note r "L0 read Owned from text: same bytes as the AST" same
  -- L0c the printer (Lang.Print) gives Owned a text that reads back to the same bytes; a label
  -- that is not one atom has no text; non-UTF-8 bytes in a term print as #hex and read back
  match Print.package owned with
  | none => r := note r "L0c print Owned: no text" false
  | some t =>
    let same := match Read.readPackage t with
      | .ok q => Wire.encodePackage q == some ownedBytes
      | .error _ => false
    r := note r "L0c print Owned, read the text: same bytes" same
  r := note r "L0c a method label with a space has no text"
    (Print.package { owned with methods := ["s et"] }).isNone
  let ff : ByteArray := ⟨#[0xff, 0x22]⟩
  let hexBack := match Print.term (.prim .cat (.bytes ff) (.bytes "q".toUTF8)) with
    | some t => (match Read.readTerm t with
      | .ok (.prim .cat (.bytes x) (.bytes y)) => x == ff && y == "q".toUTF8
      | _ => false) && t == "(cat #ff22 \"q\")"
    | none => false
  r := note r "L0c bytes that are not quote-free UTF-8 print as #hex and read back" hexBack
  -- L0d the reader's fuel counts nesting, not length: an allowlist at `Std.idsMax` (a chain one
  -- level per id) prints and reads back; a list past `Read.listMax` is refused `tooLong`, a form
  -- nested past `Read.depthMax` `tooDeep`, and each bound itself is read
  let ids := (List.range Std.idsMax).map fun i => ByteArray.mk #[UInt8.ofNat (i / 256), UInt8.ofNat (i % 256)]
  let longOk := match Std.allowlist S ids with
    | .ok law => match Print.term law with
      | some t => (match Read.readTerm t with
        | .ok law' => Wire.encodePackage (Std.pkgOf S [("al", law')] []) == Wire.encodePackage (Std.pkgOf S [("al", law)] [])
        | .error _ => false)
      | none => false
    | .error _ => false
  r := note r s!"L0d an allowlist of {Std.idsMax} ids prints and reads back (the same package bytes)" longOk
  let recordOf (n : Nat) : String :=
    "(record" ++ String.join ((List.range n).map fun i => s!" (a{i} 1)") ++ ")"
  let wideOk := match Read.readTerm (recordOf (Read.listMax - 1)) with | .ok _ => true | .error _ => false
  r := note r s!"L0d a list of {Read.listMax} elements reads" wideOk
  let tooLong := match Read.readTerm (recordOf Read.listMax) with | .error (.tooLong _) => true | _ => false
  r := note r s!"L0d a list of {Read.listMax + 1} elements: tooLong" tooLong
  let nested (n : Nat) : String := String.join (List.replicate (n - 1) "(fix ") ++ "1" ++ String.join (List.replicate (n - 1) ")")
  let deepOk := match Read.readTerm (nested Read.depthMax) with | .ok _ => true | .error _ => false
  r := note r s!"L0d a form nested {Read.depthMax} deep reads" deepOk
  let tooDeep := match Read.readTerm (nested (Read.depthMax + 1)) with | .error (.tooDeep _) => true | _ => false
  r := note r s!"L0d a form nested {Read.depthMax + 1} deep: tooDeep" tooDeep
  -- L0e a binder named like a literal is refused by name (every use would read as the literal)
  for (txt, why) in [("(lam true bool true)", "true"), ("(lam 5 nat 5)", "a numeral"), ("(let #ab nat 1 #ab)", "#hex"),
                     ("(fn (false bool) false)", "false"),
                     ("(case (inj (sum (a nat)) a 1) (a 7 7))", "a numeral in a case arm"),
                     ("(lam if nat if)", "a head word"), ("(lam + nat +)", "a primitive")] do
    let refused := match Read.readTerm txt with
      | .error (.reservedBinder _ _) => true
      | _ => false
    r := note r s!"L0e refuse a binder named {why}: reservedBinder" refused
  let named := match Read.readTerm "(lam x5 nat x5)" with | .ok (.lam .nat (.var 0)) => true | _ => false
  r := note r "L0e a binder named x5 reads as a variable" named
  -- L0f (LANG-31) a package at the wire's depth bound, written as text: `n` record levels through field `f`
  -- make a body and an interface whose trees are `2n + 1` deep, so n = 511 puts the package's tree at
  -- Wire.depthMax and its text at Read.depthMax
  let nestTy (n : Nat) : String := String.join (List.replicate n "(rec (f ") ++ "(rec)" ++ String.join (List.replicate n "))")
  let nestT (n : Nat) : String := String.join (List.replicate n "(record (f ") ++ "(record)" ++ String.join (List.replicate n "))")
  let deepText (n : Nat) : String :=
    s!"(package\n  (imports)\n  (state (rec))\n  (iface {nestTy n})\n  (methods)\n  (laws)\n  (rels)\n  (body {nestT n}))\n"
  let deepOk := match Read.readPackage (deepText 511) with
    | .ok p => (p.checkWith []).toBool && (match Wire.encodePackage p, Print.package p with
      | some b, some t => (match Read.readPackage t with
        | .ok q => Wire.encodePackage q == some b
        | .error _ => false)
      | _, _ => false)
    | .error _ => false
  r := note r s!"L0f a package {Wire.depthMax} deep as a tree reads, checks, encodes, prints, reads back: same bytes" deepOk
  let deeper := match Read.readPackage (deepText 512) with | .error (.tooDeep _) => true | _ => false
  r := note r "L0f one level deeper: tooDeep" deeper
  r := note r "L0f a label with a space has no bytes"
    (Wire.encodePackage { owned with methods := ["s et"] }).isNone
  -- L0b a seed state read at the package's state type (Read.readData): fields in any order; a
  -- missing field, a wrong-typed value, an unknown sum arm refused `notOfType`
  let seedOk := match Read.readData S "(record (total 5) (owner #61))" with
    | .ok (.record [("owner", .digest o), ("total", .nat 5)]) => o == "a".toUTF8
    | _ => false
  r := note r "L0b read a seed at Owned's state type" seedOk
  -- the owner as a member's id: bytes that need not be UTF-8, written `#HEX`
  let ownerHex := (Print.data (.digest (Sim.dc.bytes a.id))).getD ""
  let hexOk := match Read.readData S s!"(record (owner {ownerHex}) (total 0))" with
    | .ok (.record [("owner", .digest o), ("total", .nat 0)]) => o == Sim.dc.bytes a.id
    | _ => false
  r := note r "L0b read a seed whose owner is a member id, as ob prints it (#HEX)" hexOk
  for (txt, why) in [("(record (total 5))", "missing field"), ("(record (owner 1) (total 5))", "wrong type"),
                     ("(record (owner #61) (total 18446744073709551616))", "past natLimit"),
                     ("(record (owner \"a\") (total 5))", "string at a digest"),
                     ("(record (owner #000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20) (total 5))",
                      "digest past digestBytesMax"),
                     ("(record (owner #6) (total 5))", "odd count of hex digits"),
                     ("(record (owner #6A) (total 5))", "uppercase hex digit"),
                     ("(record (owner #61) (total #05))", "hex at a nat")] do
    let refused := match Read.readData S txt with
      | .error (.notOfType _) => true
      | _ => false
    r := note r s!"L0b refuse a seed with a {why}: notOfType" refused
  -- L1 install
  let c1 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install ownedBytes)
  let (r1, v1, t1) := go prog r c1
  r := note r1 s!"L1 install Owned: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "L1 no package id" false
  -- L6 an ill-typed package
  let c6 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install illBytes)
  let (r6, v6, _) := go prog r c6
  r := note r6 s!"L6 install ill-typed: {v6}" (v6.startsWith "refused program")
  r := installRows mode r a pkg
  -- L2 create
  let some ownerBytes := Wire.encodeData .digest (.digest (Sim.dc.bytes a.id)) | return note r "L2 no owner bytes" false
  let some n0 := nat64 0 | return note r "L2 no bytes for 0" false
  let some n50 := nat64 50 | return note r "L3 no bytes for 50" false
  let some n101 := nat64 101 | return note r "L4 no bytes for 101" false
  let some n7 := nat64 7 | return note r "L5 no bytes for 7" false
  let seed : Slots := [(stateBase, ownerBytes), (stateBase + 1, n0)]
  let c2 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed)
  let (r2, v2, t2) := go prog r c2
  r := note r2 s!"L2 create object: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "L2 no object id" false
  -- L3 set 50
  let c3 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n50 10000 none)
  let (r3, v3, _) := go prog r c3
  r := note r3 s!"L3 A set 50: {v3}, total = {totalOf Sim.env r3.st.host obj}" (v3 == "admitted" && totalOf Sim.env r3.st.host obj == some 50)
  -- L4 set 101
  let c4 := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 n101 10000 none)
  let (r4, v4, _) := go prog r c4
  if mode = .skipJudge then
    r := note r4 s!"PLANT skip-judge: L4 A set 101 must now be admitted: {v4}" (v4 == "admitted")
  else
    r := note r4 s!"L4 A set 101: {v4}, total = {totalOf Sim.env r4.st.host obj}"
      (v4.startsWith "refused lawDenied" && (v4.splitOn "bounded: over 100").length > 1 && totalOf Sim.env r4.st.host obj == some 50)
  -- L5 B through a grant
  let cg := Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0] none)
  let (rg, vg, tg) := go prog r cg
  r := note rg s!"L5a A grants B invoke 0: {vg}" (vg == "admitted")
  let some gr := tg.bind fun t => (createdIds t).head? | return note r "L5 no grant id" false
  let c5 := Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (.invoke obj 0 n7 10000 (some gr))
  let (r5, v5, _) := go prog r c5
  unless mode = .skipJudge do
    r := note r5 s!"L5 B (granted) set 7: {v5}" (v5.startsWith "refused lawDenied" && (v5.splitOn "ownerOnly: not the owner").length > 1)
  r := { r5 with log := r.log, bad := r.bad }
  -- L8 a birth is judged as a birth: a seed carrying approvals is refused by `fresh`
  let some tallyBytes := Wire.encodePackage tally | return note r "L8 Tally has no bytes" false
  let (r8, v8, t8) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install tallyBytes))
  r := note r8 s!"L8a install Tally: {v8}" (v8 == "admitted")
  let some tid := t8.bind fun t => (createdIds t).head? | return note r "L8 no Tally id" false
  let some n7' := nat64 7 | return note r "L8 no bytes for 7" false
  let seeded : Slots := [(stateBase, n7'), (stateBase + 1, n0)]
  let (r8b, v8b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tid]) (.create (some tid) [] seeded))
  r := { r8b with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L8b the seeded birth must now be admitted: {v8b}" (v8b == "admitted")
  else if mode = .honest then
    r := note r s!"L8b A creates Tally seeded approvals = 7: {v8b}"
      (v8b.startsWith "refused lawDenied" && (v8b.splitOn "fresh: seeded").length > 1)
  let (r8c, v8c, t8c) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tid]) (.create (some tid) [] [(stateBase, n0), (stateBase + 1, n0)]))
  r := note r8c s!"L8c A creates Tally seeded approvals = 0: {v8c}" (v8c == "admitted")
  let some tobj := t8c.bind fun t => (createdIds t).head? | return note r "L8 no Tally object" false
  -- the invoke's method index reaches the law: `b` (method 1) is closed, `a` (method 0) open
  let (r8d, v8d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tobj, tid]) (.invoke tobj 0 n7 10000 none))
  r := note r8d s!"L8d A invokes Tally.a 7: {v8d}" (v8d == "admitted")
  let (r8e, v8e, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, tobj, tid]) (.invoke tobj 1 n7 10000 none))
  r := { r8e with log := r.log, bad := r.bad }
  if mode = .eraseOccasion || mode = .erasePayload then
    r := note r s!"PLANT {if mode = .eraseOccasion then "erase-occasion" else "erase-payload"}: L8e Tally.b must now be admitted: {v8e}" (v8e == "admitted")
  else if mode = .honest then
    r := note r s!"L8e A invokes Tally.b 7: {v8e}" (deniedWith v8e "fresh: method b is closed")
  -- L9 a law replacement is judged as one: `frozen` refuses its own removal
  let some frozenBytes := Wire.encodePackage frozen | return note r "L9 Frozen has no bytes" false
  let (r9, v9, t9) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install frozenBytes))
  r := note r9 s!"L9a install Frozen: {v9}" (v9 == "admitted")
  let some fid := t9.bind fun t => (createdIds t).head? | return note r "L9 no Frozen id" false
  let (r9b, v9b, t9b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, fid]) (.create none [fid] [(stateBase, n0)]))
  r := note r9b s!"L9b A creates a data object under Frozen: {v9b}" (v9b == "admitted")
  let some dobj := t9b.bind fun t => (createdIds t).head? | return note r "L9 no object id" false
  let (r9c, v9c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, dobj, fid]) (.write dobj [(0, some n7)] none))
  r := note r9c s!"L9c A writes under Frozen: {v9c}" (v9c == "admitted")
  let (r9d, v9d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, dobj, fid]) (.law dobj [] none))
  r := { r9d with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L9d removing Frozen must now be admitted: {v9d}" (v9d == "admitted")
  else if mode = .honest then
    r := note r s!"L9d A removes Frozen: {v9d}"
      (v9d.startsWith "refused lawDenied" && (v9d.splitOn "frozen: laws are frozen").length > 1)
  -- L10 the relaw carries the incoming laws: `onlyTo [Frozen]` admits exactly that replacement
  let some onlyBytes := Wire.encodePackage (onlyTo (Sim.dc.bytes fid)) | return note r "L10 OnlyTo has no bytes" false
  let (r10, v10, t10) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install onlyBytes))
  r := note r10 s!"L10a install OnlyTo [Frozen]: {v10}" (v10 == "admitted")
  let some oid := t10.bind fun t => (createdIds t).head? | return note r "L10 no OnlyTo id" false
  let (r10b, v10b, t10b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oid]) (.create none [oid] []))
  r := note r10b s!"L10b A creates a data object under OnlyTo: {v10b}" (v10b == "admitted")
  let some oobj := t10b.bind fun t => (createdIds t).head? | return note r "L10 no object id" false
  let (r10c, v10c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oobj, oid, tid]) (.law oobj [tid] none))
  r := { r10c with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    -- OnlyTo, told a write, now admits; the refusal is the incoming Tally judging the state it
    -- would govern (LANG-19), which lacks Tally's fields
    r := note r s!"PLANT erase-occasion: L10c OnlyTo must now pass the wrong replacement to the incoming laws: {v10c}"
      (deniedWith v10c "state field approvals missing")
  else if mode != .skipJudge then
    r := note r s!"L10c A replaces OnlyTo by [Tally]: {v10c}" (deniedWith v10c "onlyTo: not the agreed laws")
  if mode != .eraseOccasion then
    let (r10d, v10d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, oobj, oid, fid]) (.law oobj [fid] none))
    r := { r10d with log := r.log, bad := r.bad }
    if mode = .erasePayload then
      r := note r s!"PLANT erase-payload: L10d the agreed replacement must now be refused: {v10d}" (deniedWith v10d "onlyTo: not the agreed laws")
    else
      r := note r s!"L10d A replaces OnlyTo by [Frozen]: {v10d}" (v10d == "admitted")
  -- L11 adopt: `birthOnly` may be born under, never added later
  let some boBytes := Wire.encodePackage birthOnly | return note r "L11 BirthOnly has no bytes" false
  let (r11, v11, t11) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install boBytes))
  r := note r11 s!"L11a install BirthOnly: {v11}" (v11 == "admitted")
  let some bid := t11.bind fun t => (createdIds t).head? | return note r "L11 no BirthOnly id" false
  let (r11b, v11b, t11b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, bid]) (.create none [bid] []))
  r := note r11b s!"L11b A creates a data object under BirthOnly: {v11b}" (v11b == "admitted")
  let some bobj := t11b.bind fun t => (createdIds t).head? | return note r "L11 no BirthOnly object" false
  let (r11o, v11o, t11o) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
  r := note r11o s!"L11o A creates a lawless data object: {v11o}" (v11o == "admitted")
  let some lobj := t11o.bind fun t => (createdIds t).head? | return note r "L11 no object id" false
  let (r11c, v11c, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, lobj, bid]) (.law lobj [bid] none))
  r := { r11c with log := r.log, bad := r.bad }
  if mode = .eraseOccasion then
    r := note r s!"PLANT erase-occasion: L11c adding BirthOnly must now be admitted: {v11c}" (v11c == "admitted")
  else if mode != .skipJudge then
    r := note r s!"L11c A adds BirthOnly to an existing object: {v11c}" (deniedWith v11c "birthOnly: only at birth")
  -- L11d a law KEPT across a relaw is not adopted again: only the added Frozen judges adopt
  let (r11d, v11d, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, bobj, bid, fid]) (.law bobj [bid, fid] none))
  r := { r11d with log := r.log, bad := r.bad }
  if mode = .honest then
    r := note r s!"L11d A keeps BirthOnly and adds Frozen: {v11d}" (v11d == "admitted")
  if mode = .honest || mode = .skipJudge then
    r := tallyRows mode r a b
    r := storyRows mode r a b
  if mode = .honest then
    r := gateRows mode r a
  r := callRows mode r a
  -- L7 follower and auditor
  match World.fold Sim.env g r.st.log with
  | .ok w => r := note r s!"L7 follower reaches the Host's World ({r.st.log.length} turns)" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 follower refused at {i}: {Sim.nameOf e}" false
  match audit (ctxWith prog) g r.st.log with
  | .ok w => r := note r "L7 auditor reaches the Host's World" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 auditor refused at {i}: {reprStr e}" false
  return r

def runAll : IO UInt32 := do
  let runs := [Mode.honest, .skipJudge, .eraseOccasion, .erasePayload, .dropCalls, .rawInstall, .bytesIds,
    .skipLits, .totalDigest, .unlawfulCodec, .dropRangeRow].map journey
  for r in runs do for l in r.log do IO.println l
  let bad := (runs.map (·.bad)).foldl (· + ·) 0
  IO.println s!"lang-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
  return if bad = 0 then 0 else 1

end Nanodregg.Lang.Journey
