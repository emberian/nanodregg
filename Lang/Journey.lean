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
* LV (LANG-60) the package wire's version: `Owned`'s LANG-59 bytes (a fixture, no version byte) and
  its current bytes at the previous version are refused `lang/package-version/N` (N = `Bounds.packageWireVersion`) at install and at decode.
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
  view: the second is `stale` (its pinned row moved). LS12 (LANG-59) a layer's `steal`, an upsert of a
  proposal giving it another author, is refused by the guard `authored` (it sees the old row); LS12i a
  layer's `forge`, an insert under another author's name, is refused by it too; LS12' both on a
  CoAuthor whose guard admits any author are admitted. Plant skip-judge: LS6c is
  then ADMITTED.
* L7 the fold (`World.fold` from genesis) and the follower's re-derivation (`Receive.rederiveLog`) reach the Host's World.
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
import Lang.StdContextualHole
import Kernel.Sim
import Lang.Program
import Lang.Print
import Lang.Resident
import Lang.Std
import Lang.Journey.Activity
import Lang.Journey.HoleChecks
import Lang.Sim.Need
import Lang.Bell

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

/-- A LANG-59-era package (LANG-60's fixture): `Owned`'s bytes exactly as LANG-59's `lang/package/2`
wrote them (no version byte; 1,788 bytes, emitted at main 359e9e8). Under LANG-59 bytes of the
LANG-58 wire read as a DIFFERENT package; under the versioned wire these are refused by name. -/
def owned59Hex : String :=
  "00000700000004000206056f776e6572010700000605746f74616c010000000400030607626f756e6465640103000204"
    ++ "000206056f776e6572010700000605746f74616c0100000003000204000206056f776e6572010700000605746f74616c"
    ++ "0100000003000204000606056167656e740107000006096e6f744265666f72650100000006086f63636173696f6e0105"
    ++ "0005060561646f70740102000006056269727468010400000606696e766f6b6501000000060572656c61770102000006"
    ++ "0577726974650104000006097072696e636970616c01070000060473656c6601070000060a76616c6964556e74696c01"
    ++ "00000005000206026f6b010400000607726566757365640102000006096f776e65724f6e6c790103000204000206056f"
    ++ "776e6572010700000605746f74616c0100000003000204000206056f776e6572010700000605746f74616c0100000003"
    ++ "000204000606056167656e740107000006096e6f744265666f72650100000006086f63636173696f6e01050005060561"
    ++ "646f70740102000006056269727468010400000606696e766f6b6501000000060572656c617701020000060577726974"
    ++ "650104000006097072696e636970616c01070000060473656c6601070000060a76616c6964556e74696c010000000500"
    ++ "0206026f6b010400000607726566757365640102000006037365740103000204000003000204000206056f776e657201"
    ++ "0700000605746f74616c0100000003000200000003000204000606056167656e740107000006096e6f744265666f7265"
    ++ "0100000006086f63636173696f6e01050005060561646f70740102000006056269727468010400000606696e766f6b65"
    ++ "01000000060572656c617701020000060577726974650104000006097072696e636970616c01070000060473656c6601"
    ++ "070000060a76616c6964556e74696c01000000040003060563616c6c7301040000060565646974730104000006057374"
    ++ "6174650104000206056f776e6572010700000605746f74616c010000000800030f07626f756e64656401010002040002"
    ++ "06056f776e6572010700000605746f74616c0100000001000204000206056f776e6572010700000605746f74616c0100"
    ++ "000001000204000606056167656e740107000006096e6f744265666f72650100000006086f63636173696f6e01050005"
    ++ "060561646f70740102000006056269727468010400000606696e766f6b6501000000060572656c617701020000060577"
    ++ "726974650104000006097072696e636970616c01070000060473656c6601070000060a76616c6964556e74696c010000"
    ++ "000d0003070107020905746f74616c010004010000000004080000000000000064000b026f6b0205000206026f6b0104"
    ++ "0000060772656675736564010200000800000b07726566757365640205000206026f6b01040000060772656675736564"
    ++ "0102000006086f76657220313030000f096f776e65724f6e6c790101000204000206056f776e6572010700000605746f"
    ++ "74616c0100000001000204000206056f776e6572010700000605746f74616c0100000001000204000606056167656e74"
    ++ "0107000006096e6f744265666f72650100000006086f63636173696f6e01050005060561646f70740102000006056269"
    ++ "727468010400000606696e766f6b6501000000060572656c617701020000060577726974650104000006097072696e63"
    ++ "6970616c01070000060473656c6601070000060a76616c6964556e74696c010000000d000307010a0209056167656e74"
    ++ "010004000000000009056f776e657201000401000000000d000307010a0209056f776e6572010004020000000009056f"
    ++ "776e657201000401000000000b026f6b0205000206026f6b01040000060772656675736564010200000800000b077265"
    ++ "66757365640205000206026f6b0104000006077265667573656401020000060d6f776e6572206368616e676564000b07"
    ++ "726566757365640205000206026f6b0104000006077265667573656401020000060d6e6f7420746865206f776e657200"
    ++ "0f037365740101000204000001000204000206056f776e6572010700000605746f74616c010000000100020000000100"
    ++ "0204000606056167656e740107000006096e6f744265666f72650100000006086f63636173696f6e0105000506056164"
    ++ "6f70740102000006056269727468010400000606696e766f6b6501000000060572656c61770102000006057772697465"
    ++ "0104000006097072696e636970616c01070000060473656c6601070000060a76616c6964556e74696c01000000080003"
    ++ "0f0563616c6c73010800000f056564697473010800000f057374617465010800020f056f776e65720109056f776e6572"
    ++ "01000402000000000f05746f74616c01000401000000000100010103736574000100020107626f756e6465640001096f"
    ++ "776e65724f6e6c7900020000"

def owned59 : ByteArray := (Read.unhex .empty owned59Hex.toList).getD .empty

/-- `Owned`, as a resident writes it (Lang.Read): must read to exactly the package above. -/
def ownedText : String := s!"
(package (imports) (doc)
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

/-! ### Calls (LANG-23, KERNEL-28, LANG-77): a method's calls are derived as the object, at most
`callDepthMax` deep, and a method COMPOSES a nested call's argument

`Relay` keeps `{hits : nat, me : digest, n : nat, next : opt digest, via : opt digest}`. `arm {via}`
stores the grant this relay forwards through (a grant naming THIS object on `next`; it exists only
after both objects do, so it is not a seed). `go {n}` counts the hit, records `req.self` as `me` and
`n` as `n`, and, when `next` is `some o`, invokes `o`'s `go` through `via` with `{n := n + 1}`: an
argument it COMPUTED, which the runtime encodes at the slot's declared type (LANG-77). Before
LANG-77 the invoke arm's `args` were bytes, and a relay could only forward a byte string it held
(LANG-23 (iii)), so the journey nested each level's pre-encoded arguments inside the previous one. -/

def R : Ty := .record [("hits", .nat), ("me", .digest), ("n", .nat), ("next", optTy .digest), ("via", optTy .digest)]
/-- `go`'s argument. -/
def GA : Ty := .record [("n", .nat)]
/-- `arm`'s argument. -/
def VA : Ty := .record [("via", .digest)]

/-- The method indices (labels ascending). -/
def relayArmIx : Nat := 0
def relayGoIx : Nat := 1

/-- `go`'s one call slot: an invoke carrying a value of `GA`, nothing else. -/
def K : Ty := invokeOf GA

/-- `invoke obj go {n := n + 1} 1000 via`, inside `next`'s `some` arm (the next object var 0, req var 1,
args var 2, state var 3): the argument is composed from the one received, `via` is the state's. -/
def relayCallTo (obj : Term) : Term :=
  .inj K "invoke" (.record [("args", .record [("n", .prim .add (.get (.var 2) "n") (.nat 1))]), ("budget", .nat 1000),
    ("method", .nat relayGoIx), ("obj", obj), ("via", .get (.var 3) "via")])

def relayCall : Term := relayCallTo (.var 0)

def relayGoWith (call : Term) : Term :=
  .lam (.record []) (.lam R (.lam GA (.lam reqTy (resultT
    (.case (.get (.var 2) "next") [("none", callsT [noCallT K]), ("some", callsT [someCallT K call])])
    (.record [("hits", .prim .add (.get (.var 2) "hits") (.nat 1)), ("me", .get (.var 0) "self"),
      ("n", .get (.var 1) "n"), ("next", .get (.var 2) "next"), ("via", .get (.var 2) "via")])))))

def relayGo : Term := relayGoWith relayCall

/-- `arm {via}`: keep everything, hold `via`. -/
def relayArm : Term :=
  .lam (.record []) (.lam R (.lam VA (.lam reqTy (resultT (callsT [])
    (.record [("hits", .get (.var 2) "hits"), ("me", .get (.var 2) "me"), ("n", .get (.var 2) "n"),
      ("next", .get (.var 2) "next"), ("via", .inj (optTy .digest) "some" (.get (.var 1) "via"))])))))

def relayWith (go : Term) : Package :=
  { imports := [], state := R, iface := .record [("arm", methodTy R VA []), ("go", methodTy R GA [K])],
    body := .record [("arm", relayArm), ("go", go)], methods := ["arm", "go"], laws := [] }

def relay : Package := relayWith relayGo

/-- LC7 (LANG-77): a slot whose invoke arm carries a FUNCTION: no value of it has bytes, so the slot
is not a call slot and install refuses the method `badMethod`. -/
def fnSlot : Ty := invokeOf (.fn .nat .nat)

def fnCalls : Package :=
  { imports := [], state := R,
    iface := .record [("go", methodTy R GA [fnSlot])],
    body := .record [("go", .lam (.record []) (.lam R (.lam GA (.lam reqTy
      (resultT (callsT [noCallT fnSlot]) (.var 2))))))],
    methods := ["go"], laws := [] }

/-- LC8 (LANG-77): `Sink.go {n, note}` takes a wider argument than a relay sends: a relay whose `next`
is a Sink composes `{n}`, and the Sink's run refuses the bytes at ITS type, `arguments: …`, the one
place argument bytes are checked (the same refusal a root call with wrong bytes gets). The Sink has
the Relay's two method indices (`arm` 0, `go` 1), so the relay's `invoke next go` reaches its `go`. -/
def SA : Ty := .record [("n", .nat), ("note", .bytes)]

def sink : Package :=
  { imports := [], state := .record [],
    iface := .record [("arm", methodTy (.record []) (.record []) []), ("go", methodTy (.record []) SA [])],
    body := .record [
      ("arm", .lam (.record []) (.lam (.record []) (.lam (.record []) (.lam reqTy (resultT (callsT []) (.var 2)))))),
      ("go", .lam (.record []) (.lam (.record []) (.lam SA (.lam reqTy (resultT (callsT []) (.var 2))))))],
    methods := ["arm", "go"], laws := [] }

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

/-- `Caller.go`'s slot: an invoke with the empty argument. -/
def KC : Ty := invokeOf CA

def callerGo : Term :=
  .lam (.record []) (.lam CA (.lam CA (.lam reqTy (resultT
    (callsT [someCallT KC (.inj KC "invoke" (.record [("args", .record []), ("budget", .nat 1000),
      ("method", .nat 0), ("obj", .get (.var 0) "agent"), ("via", .inj (optTy .digest) "none" (.record []))]))])
    (.var 2)))))

def caller : Package :=
  { imports := [], state := CA, iface := .record [("go", methodTy CA CA [KC])],
    body := .record [("go", callerGo)], methods := ["go"], laws := [] }

/-- One call slot more than `callsMax`. -/
def nineLabels : List Label := slotLabels "c" (Kernel.Bounds.callsMax + 1)

def nineGo : Term :=
  .lam (.record []) (.lam R (.lam GA (.lam reqTy (resultT (callsT (nineLabels.map fun _ => noCallT K)) (.var 2)))))

def nineTy : Ty := methodTy R GA (nineLabels.map fun _ => K)

/-- A method whose calls row has one slot more than `callsMax`: its type is not a method's. -/
def nineCalls : Package :=
  { imports := [], state := R, iface := .record [("go", nineTy)],
    body := .record [("go", nineGo)], methods := ["go"], laws := [] }

/-- A u64 argument or slot (`none` past `2^64`). -/
def nat64 (n : Nat) : Option ByteArray := Wire.encodeData .nat (.nat n)

def ctxWith (prog : Program D) : Ctx D := Sim.ctxWith prog

def langProgram : Program D := Lang.program Sim.dc.bytes Sim.digestOf noReceipts

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
  let t := Lang.program Sim.dc.bytes totalDigestOf noReceipts
  { langProgram with run := t.run, judge := t.judge }

/-- A digest decoder that refuses exactly member `x`'s own id: a World whose codec does not read
that id back. Plant 9 gives it to the program only, so the `Ctx` stays lawful and `program_run_past_extraction`'s `hp` is what fails. -/
def refusing (x : D) (b : ByteArray) : Option D := if b = Sim.dc.bytes x then none else Sim.digestOf b

/-- Plant 9: the method run under a World whose codec refuses member `x`'s id. A request's ids are
the one source no boundary check reads (they are the World's own), so a call naming `x` is the
first place the refusal can land: `callsOf`. Install and judge are the deployed ones. -/
def unlawfulCodec (x : D) : Program D :=
  { langProgram with run := (Lang.program Sim.dc.bytes (refusing x) noReceipts).run }

/-- Plant 10: the run is handed each signed range without its last row (LS9). -/
def dropLastRow (rv : RowView D) : RowView D :=
  { points := rv.points
    ranges := fun parent rel => (rv.ranges parent rel).map fun qs => qs.map fun q => (q.1, q.2.1, q.2.2.dropLast) }

def dropRangeRow : Program D :=
  { langProgram with run := fun look rv p s m a r b => langProgram.run look (dropLastRow rv) p s m a r b }

/-- Plant 11: the run's row edits filed under the signer's id, not the object's (cv 01a14e16-78ac).
`run_rows_under` says `Lang.program` never does this; KERNEL's `rowParent` is the check that would
refuse it (LT4 under this plant). -/
def foreignRow : Program D :=
  { langProgram with run := fun look rv p s m a r b =>
      (langProgram.run look rv p s m a r b).map fun (s', cs, rows, t) =>
        (s', cs, rows.map (fun (sl, act) =>
          ((match sl with
            | .row k => .row { k with parent := r.agent }
            | x => x), act)), t) }

/-- A package with nothing in it but its imports (LI). -/
def importer (imports : List ByteArray) : Package :=
  { imports, state := .record [], iface := .record [], body := .record [], methods := [], laws := [] }

/-- Which program the journey runs under. -/
inductive Mode
  | honest | skipJudge | eraseOccasion | erasePayload | dropCalls | rawInstall | bytesIds | skipLits
  | totalDigest | unlawfulCodec | dropRangeRow | foreignRow
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
  | .foreignRow => Journey.foreignRow

/-- A method's refusal by name (LANG-51): `program "m: refused why"`. -/
def refusedBy (v m why : String) : Bool := v.startsWith "refused program" && (v.splitOn s!"{m}: refused {why}").length > 1

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

/-- A Relay object's state slot `i` (0 hits, 1 me, 2 n, 3 next, 4 via). -/
def slotOf (E : Kernel.Env D) (w : World D) (obj : D) (i : Nat) : Option ByteArray :=
  (w.live E obj).bind fun cell => cell.slots.get (stateBase + i)

def natSlotOf (E : Kernel.Env D) (w : World D) (obj : D) (i : Nat) : Option Nat :=
  match (slotOf E w obj i).map (Wire.decodeData .nat) with
  | some (.ok (.nat n)) => some n
  | _ => none

def hitsOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat := natSlotOf E w obj 0

/-- The `n` a relay's `go` received (LC3: the composed argument arrived). -/
def nOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Nat := natSlotOf E w obj 2

def meOf (E : Kernel.Env D) (w : World D) (obj : D) : Option ByteArray :=
  match (slotOf E w obj 1).map (Wire.decodeData .digest) with
  | some (.ok (.digest b)) => some b
  | _ => none

/-- `go`'s argument `{n}`. -/
def goArgs (n : Nat) : Option ByteArray := Wire.encodeData GA (.record [("n", .nat n)])

/-- `arm`'s argument `{via}` (an id: an argument typed `digest` must be one, LANG-38). -/
def armArgs (via : ByteArray) : Option ByteArray := Wire.encodeData VA (.record [("via", .digest via)])

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
def tallyGuardInText : String := tyS (guardInTy answersDecl)
def tallyOldText : String := tyS (optTy answersDecl.val)
def tallyOptEditText : String := tyS (optTy (editTy tallyRels))

/-- CappedTally as a resident writes it. -/
def cappedTallyText : String := s!"
(package (imports) (doc)
  (state {tallyStText})
  (iface (rec (decider (-> {tallyStText} (-> {tallyStText} (-> {rq} {verdictText}))))
              (mine (-> {tallyStText} (-> {rq} (-> {tallyGuardInText} {verdictText}))))
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
      (mine (fn (s {tallyStText}) (r {rq}) (g {tallyGuardInText})
        (let old {tallyOldText} (. g old)
          (let e {tallyRelEditText} (. g edit)
            (case e
              (insert x (if (deq (. (. x key) by) (. r agent))
                            (inj {verdictText} ok (record))
                            (inj {verdictText} refused \"not yours\")))
              (upsert x (inj {verdictText} refused \"answers are final\")))))))
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

/-- CappedTally in the authoring surface (LANG-50): the same package, written once, lowered to
EXACTLY the core above (LT0s). -/
def cappedTallySurface : String := "
(package
  (state (rec (closes nat) (decider digest)))
  (rel answers (key (by digest) (n nat)) (val (rec (amount nat))) (limit 64) (sum amount) (cap 1000) (guard mine))
  (method reply (arg (rec (amount nat) (by digest) (n nat))) (edits 1)
    (done state (insert answers (record (by arg.by) (n arg.n)) (record (amount arg.amount)))))
  (guard mine
    (case edit
      (insert x (if (deq x.key.by req.agent) ok (refuse \"not yours\")))
      (upsert x (refuse \"answers are final\"))))
  (law decider
    (on invoke (if (deq req.agent old.decider) (if (<= req.validUntil old.closes) ok (refuse \"closed\"))
                   (refuse \"not the decider\")))
    (else ok)))
"

/-- The tally's surface with one field misspelt in `reply`'s body: the checker's refusal names the
line it is on (LE). -/
def tallyTypo : String := cappedTallySurface.replace "(amount arg.amount)" "(amount arg.amout)"

/-- A layer over CappedTally (LANG-50 `layer`): one method added, `close`; the state, the
relation, `reply` and the law `decider` are the tally's own, run from its installed core. -/
def tallyLayerText (superHex : String) : String := s!"
(package
  (import tally \"{superHex}\")
  (layer tally)
  (method close (done (with state (closes 0)))))
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
      let (_, _, _, ticks, _) ← Lang.runMeasuredLive X.env.bytes X.digestOf noReceipts look rv p (stateOf cell) method args r budget
      let req ← Lang.Need.requiredOfLive X.env.bytes X.digestOf noReceipts look rv p (stateOf cell) method args r budget
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

/-- LL: a layer over the installed tally, through the receivers. -/
def layerRows (mode : Mode) (r0 : Run) (a : Sim.Member) (pkg : D) (tally : Package) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let tb := Sim.dc.bytes pkg
  let text := tallyLayerText (Print.hex tb)
  let l ← match Surface.readWith [(tb, tally)] text with
    | .ok l => pure l
    | .error e => return note r s!"LL0 read the layer: {e.text text}" false
  let p := l.pkg
  let some lb := Wire.encodePackage p | return note r "LL0 the layer has no bytes" false
  r := note r s!"LL0 a layer over CappedTally: {text.length} chars; {lb.size} package bytes; imports the tally; methods {p.methods} (the tally's reply keeps index 0); laws {p.laws}"
    (p.imports == [tb] && p.methods == ["reply", "close"] && p.laws == ["decider"] && p.rels == tally.rels)
  let bad := text.replace "(method close" "(law decider (else ok))\n  (method close"
  r := note r s!"LL0b a layer that overrides the tally's law: {match Surface.readWith [(tb, tally)] bad with | .ok _ => "read" | .error e => e.text bad}"
    (match Surface.readWith [(tb, tally)] bad with | .error (.overridesLaw _ "decider") => true | _ => false)
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.install lb))
  r := note r1 s!"LL1 A installs the layer: {v1}" (v1 == "admitted")
  let some lid := t1.bind fun t => (createdIds t).head? | return note r "LL1 no package id" false
  let some decA := Wire.encodeData .digest (.digest (Sim.dc.bytes a.id)) | return note r "LL no bytes" false
  let some cl := nat64 (r.st.host.height + 200) | return note r "LL no bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, lid, pkg])
    (.create (some lid) [] [(stateBase, cl), (stateBase + 1, decA)]))
  r := note r2 s!"LL2 A creates a tally under the layer, its own decider: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds t).head? | return note r "LL2 no object id" false
  let pins (r : Run) := Sim.S.pinsFor r.st.host [a.id, obj, lid, pkg]
  let some ans := Wire.encodeData tallyArg (.record [("amount", .nat 5), ("by", .digest (Sim.dc.bytes a.id)), ("n", .nat 1)])
    | return note r "LL no bytes" false
  let some ans2 := Wire.encodeData tallyArg (.record [("amount", .nat 7), ("by", .digest (Sim.dc.bytes a.id)), ("n", .nat 2)])
    | return note r "LL no bytes" false
  let some none_ := Wire.encodeData (.record []) (.record []) | return note r "LL no bytes" false
  let (r3, v3, _) := go prog r (Sim.signed r.st a a.key (pins r) (.invoke obj 0 ans 10000 none))
  r := note r3 s!"LL3 A replies 5 through the layer (the tally's own reply): {v3}, total {headSum r3.st.host obj 0}"
    (v3 == "admitted" && headSum r3.st.host obj 0 == some 5)
  let (r4, v4, _) := go prog r (Sim.signed r.st a a.key (pins r) (.invoke obj 1 none_ 10000 none))
  r := note r4 s!"LL4 A closes it (the layer's own method): {v4}" (v4 == "admitted")
  let (r5, v5, _) := go prog r (Sim.signed r.st a a.key (pins r) (.invoke obj 0 ans2 10000 none))
  r := note r5 s!"LL5 A replies after closing: {v5} (the tally's law, inherited, judges the layer's object)"
    (deniedWith v5 "decider: closed" && headSum r.st.host obj 0 == some 5)
  return r

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
  -- LT0s the surface text lowers to exactly this core; the core reader alone does not read it
  let sameCore := Surface.coreText cappedTallySurface == some printed
  let coreRefuses := (Read.readPackage cappedTallySurface).toOption.isNone
  let planted := Surface.coreText (cappedTallySurface.replace "(cap 1000)" "(cap 999)")
  let caught := planted.isSome && planted != some printed
  r := note r s!"LT0s CappedTally in the surface: {cappedTallySurface.length} chars (Mini 1269 without comments) lowers to the same core byte for byte: {sameCore}; Lang.Read alone refuses it: {coreRefuses}; plant (cap 1000) -> (cap 999) caught: {caught}"
    (sameCore && coreRefuses && caught && printed != "")
  -- LE a misspelt field: the refusal names the line it is on
  let typoLine := ((tallyTypo.splitOn "\n").zipIdx.find? (fun (l, _) => (l.splitOn "amout").length > 1)).map (·.2 + 1)
  let leLine := match Surface.readWith [] tallyTypo with
    | .ok l => match l.pkg.checkWith [] with
      | .error (.illTyped why) => (Surface.locateField l why.path).map (Surface.lineOf tallyTypo)
      | _ => none
    | .error _ => none
  r := note r s!"LE a misspelt field on line {typoLine}: the checker's refusal names line {leLine}" (leLine.isSome && leLine == typoLine)
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
  if mode = .foreignRow then
    return note r4 s!"PLANT foreign-row: LT4 B's reply with its row filed under B's own id: {v4}" (v4.startsWith "refused rowParent")
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
  if mode = .honest then
    r := layerRows mode r a pkg p
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

def coS : Ty := .record [("closes", .nat), ("round", .nat), ("window", .nat)]
def passageTy : Ty := .record [("author", .digest), ("text", .bytes), ("votes", .nat)]
def slotTy : Ty := .record [("slot", .nat)]
def coRel (key : List (Label × Ty)) (val : Ty) : RelDecl :=
  { key, val, limit := 4096, sum := none, cap := 0, retract := false, guard := none }
def authorsDecl : RelDecl := coRel [("round", .nat), ("author", .digest)] slotTy
def ballotsDecl : RelDecl := coRel [("round", .nat), ("voter", .digest)] slotTy
def chaptersDecl : RelDecl := coRel [("number", .nat)] passageTy
def proposalsDecl : RelDecl := { coRel [("round", .nat), ("slot", .nat)] passageTy with guard := some "authored" }
def coRels : List (Label × RelDecl) :=
  [("authors", authorsDecl), ("ballots", ballotsDecl), ("chapters", chaptersDecl), ("proposals", proposalsDecl)]
def proposeArg : Ty := .record [("slot", .nat), ("text", .bytes)]
def voteArg : Ty := .record [("slot", .nat)]

/-- CoAuthor as a resident writes it, in the authoring surface (LANG-50). A method refuses by name
(`refuse`, LANG-51), so the story has no `why` field and no law. The hand port's `react` law also
refused a direct `write`; KERNEL refuses that first, `hasMethods`, for every programmed object, before
any law runs (LS2b), so a law arm for it would be a no-op. A proposal's slot is the bounded argument
`(nat 0 7)` (refused `slot 0..7`), its text `(bytes 1 2000)`. The seal's walk over the range is
`fold`, the `let` chain LANG-47 wrote by hand. -/
def coAuthorText : String := "
(package
  (type Passage (rec (author digest) (text bytes) (votes nat)))
  (state (rec (closes nat) (round nat) (window nat)))
  (rel authors (key (round nat) (author digest)) (val (rec (slot nat))) (limit 4096))
  (rel ballots (key (round nat) (voter digest)) (val (rec (slot nat))) (limit 4096))
  (rel chapters (key (number nat)) (val Passage) (limit 4096))
  (rel proposals (key (round nat) (slot nat)) (val Passage) (limit 4096) (guard authored))
  (method propose (arg (rec (slot (nat 0 7)) (text (bytes 1 2000)))) (edits 2)
    (check ((<= req.validUntil state.closes) \"late\")
      (done state
        (insert authors (record (author req.agent) (round state.round)) (record (slot arg.slot)))
        (insert proposals (record (round state.round) (slot arg.slot))
                          (record (author req.agent) (text arg.text) (votes 0))))))
  (method edit (reads (proposals (points 1))) (arg (rec (slot nat) (text (bytes 1 2000)))) (edits 1)
    (check ((<= req.validUntil state.closes) \"late\")
      (case rows.proposals.p0 (none _ (refuse \"unknown\"))
        (some p (case p.val (none _ (refuse \"unknown\"))
          (some q (check ((and (== p.key.round state.round) (== p.key.slot arg.slot)) \"unknown\")
                         ((deq q.author req.agent) \"notAuthor\")
            (done state (upsert proposals p.key (extend q (text arg.text)))))))))))
  (method vote (reads (proposals (points 1))) (arg (rec (slot nat))) (edits 2)
    (check ((<= req.validUntil state.closes) \"late\")
      (case rows.proposals.p0 (none _ (refuse \"unknown\"))
        (some p (case p.val (none _ (refuse \"unknown\"))
          (some q (check ((and (== p.key.round state.round) (== p.key.slot arg.slot)) \"unknown\")
            (done state
              (insert ballots (record (round state.round) (voter req.agent)) (record (slot arg.slot)))
              (upsert proposals p.key (extend q (votes (+ q.votes 1))))))))))))
  (method seal (reads (proposals (range 1 8))) (edits 1)
    (check ((not (<= req.notBefore state.closes)) \"early\")
           ((== rows.proposals.range.pre.round state.round) \"round\")
      (case rows.proposals.range.rows.r0 (none _ (refuse \"empty\"))
        (some first
          (fold (best (row proposals) first) (q proposals)
            (if (< best.val.votes q.val.votes) q best)
            (done (extend state (closes (+ state.closes state.window)) (round (+ state.round 1)))
              (insert chapters (record (number state.round)) best.val)))))))
  (guard authored (case edit (insert x (if (deq x.val.author req.agent) ok (refuse \"author\")))
    (upsert x (case old (none _ (refuse \"unknown\"))
      (some o (if (deq x.val.author o.author) ok (refuse \"author\"))))))))
"

/-- A layer over CoAuthor whose `steal` gives a pinned proposal another author and whose `forge` files
a proposal under another author's name (LANG-59): only the guard `authored` can refuse them (it sees
the row an upsert replaces, and an insert's author). Methods: CoAuthor's first (edit 0, propose 1,
seal 2, vote 3), then `forge` 4, `steal` 5. -/
def storySteal (superHex : String) : String := s!"
(package
  (import story \"{superHex}\")
  (layer story)
  (method forge (arg (rec (slot nat) (to digest))) (edits 1)
    (done state (insert proposals (record (round state.round) (slot arg.slot))
      (record (author arg.to) (text \"forged\") (votes 0)))))
  (method steal (reads (proposals (points 1))) (arg (rec (slot nat) (to digest))) (edits 1)
    (case rows.proposals.p0 (none _ (refuse \"unknown\"))
      (some p (case p.val (none _ (refuse \"unknown\"))
        (some q (done state (upsert proposals p.key (extend q (author arg.to))))))))))
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
    | some (.row _ v _) => (Wire.decodeData d.val v).toOption
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
  let p ← match Surface.readPackage coAuthorText with
    | .ok p => pure p
    | .error e => return note r s!"LS0 read CoAuthor: {e.text coAuthorText}" false
  let some pb := Wire.encodePackage p | return note r "LS0 CoAuthor has no bytes" false
  let printed := (Print.package p).getD ""
  r := note r s!"LS0 CoAuthor read from its surface text: {coAuthorText.length} chars, {(coAuthorText.splitOn "\n").length - 2} lines; core {printed.length} chars; {pb.size} package bytes (historical, the hand ports' cores, their code since replaced: over relations 37287 chars / 30028 bytes; over lists 63865 / 52965)"
    (printed != "" && p.rels == coRels && p.laws.isEmpty)
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LS1 A installs CoAuthor: {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LS1 no package id" false
  let closes := r.st.host.height + 12
  let seedText := s!"(record (closes {closes}) (round 1) (window 20))"
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
  -- LS2b the owner writes `closes` directly: KERNEL refuses it (`hasMethods`) before any law
  let some far := nat64 (closes + 1000) | return note r "LS2b no bytes" false
  let (_, v2b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.write obj [(stateBase, some far)] none))
  r := note r s!"LS2b A writes the story's closing height directly: {v2b}" (v2b.startsWith "refused hasMethods")
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
    | some k => let s : RowSlot D := .row ⟨obj, 3, k⟩; [(s, rowPin Sim.env (headFloor Sim.env w.rows obj 3) (rowAt Sim.env w.rows s))]
    | none => []
  -- the round's proposals as one range read, pinned at the listing the signer sees on `w`
  let rangeP (w : World D) (round : Nat) : List (RangeRead D) :=
    match Wire.encodeData (keyWireTy proposalsDecl 1) (.record [("k0", .nat round)]), headOf Sim.env w.rows obj 3 with
    | some pre, some (_, _, _, _, width, _) =>
      match rangeRows Sim.env w.rows obj 3 width pre 8 with
      | some l => [{ parent := obj, rel := 3, pre, most := 8, seen := rangePin Sim.env obj 3 width pre (headFloor Sim.env w.rows obj 3) l }]
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
  let c4 := call r a 1 (proposeA 0 "a light on the rock") 0 closes [] []
  let (r4, v4, t4) := go prog r c4
  r := note r4 s!"LS4 A proposes \"a light on the rock\" at slot 0: {v4}; {cost c4 r.st.host t4}"
    (v4 == "admitted" && passageIs (passage r4.st.host 1 0) "a light on the rock" 0 && headCount r4.st.host obj 0 == some 1)
  -- LS4b/LS4c the bounded argument forms refuse by field and bound, by name
  let (_, v4b, _) := go prog r (call r a 1 (proposeA 9 "far out") 0 closes [] [])
  r := note r s!"LS4b A proposes at slot 9: {v4b}" (refusedBy v4b "propose" "slot 0..7")
  let (_, v4c, _) := go prog r (call r a 1 (proposeA 3 "") 0 closes [] [])
  r := note r s!"LS4c A proposes an empty passage: {v4c}" (refusedBy v4c "propose" "text 1..2000")
  let (r5, v5, _) := go prog r (call r b 1 (proposeA 1 "a ship in the fog") 0 closes [] [])
  r := note r5 s!"LS5 B proposes \"a ship in the fog\" at slot 1: {v5}" (v5 == "admitted")
  let (r5b, v5b, _) := go prog r (call r a 1 (proposeA 2 "another") 0 closes [] [])
  r := note { r5b with log := r.log, bad := r.bad } s!"LS5b A proposes again, at slot 2: {v5b} (Mini's alreadyProposed)" (v5b.startsWith "rejected keyTaken")
  -- LS6 votes: B for slot 1 (counted), B again (`keyTaken` on `ballots`), A for an empty slot (unknown)
  let c6 := call r b 3 (voteA 1) 0 closes (pinP r.st.host 1 1) []
  let (r6, v6, t6) := go prog r c6
  r := note r6 s!"LS6 B votes for slot 1: {v6}; {cost c6 r.st.host t6}"
    (v6 == "admitted" && passageIs (passage r6.st.host 1 1) "a ship in the fog" 1)
  let (r6b, v6b, _) := go prog r (call r b 3 (voteA 0) 0 closes (pinP r.st.host 1 0) [])
  r := note { r6b with log := r.log, bad := r.bad } s!"LS6b B votes again, for slot 0: {v6b} (Mini's alreadyVoted)" (v6b.startsWith "rejected keyTaken")
  let (r6c, v6c, _) := go prog r (call r a 3 (voteA 5) 0 closes (pinP r.st.host 1 5) [])
  r := note r6c s!"LS6c A votes for the empty slot 5: {v6c}" (refusedBy v6c "vote" "unknown")
  -- LS7 edits: A may not edit B's passage; B rewrites it
  let (r7, v7, _) := go prog r (call r a 0 (proposeA 1 "mine now") 0 closes (pinP r.st.host 1 1) [])
  r := note r7 s!"LS7 A edits B's passage: {v7}" (refusedBy v7 "edit" "notAuthor")
  let (r7b, v7b, _) := go prog r (call r b 0 (proposeA 1 "a ship in the mist") 0 closes (pinP r.st.host 1 1) [])
  r := note r7b s!"LS7b B rewrites its passage: {v7b}"
    (v7b == "admitted" && passageIs (passage r7b.st.host 1 1) "a ship in the mist" 1)
  -- LS8 a seal inside the window is early
  let (r8, v8, _) := go prog r (call r a 2 noA 0 (r.st.host.height + 50) [] (rangeP r.st.host 1))
  r := note r8 s!"LS8 A seals while the round is open: {v8}" (refusedBy v8 "seal" "early")
  -- the World moves past `closes` (lawless data objects, one turn each)
  for _ in [0:20] do
    if r.st.host.height ≤ closes then
      let (rp, _, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
      r := { rp with log := r.log, bad := r.bad }
  -- LS9 the seal over the round's one range: B's rewritten passage (1 vote, the LAST row) beats A's
  let hs := r.st.host.height
  let c9 := call r a 2 noA (closes + 1) (hs + 50) [] (rangeP r.st.host 1)
  let (r9, v9, t9) := go prog r c9
  let chapter := storyRow r9.st.host obj 2 chaptersDecl (.record [("number", .nat 1)])
  if mode = .dropRangeRow then
    return note r9 s!"PLANT drop-range-row: LS9 the seal is still admitted ({v9}) but chapter 1 is A's passage, the winner never seen"
      (v9 == "admitted" && passageIs chapter "a light on the rock" 0)
  r := note r9 s!"LS9 A seals after the window: {v9}; chapter 1 is B's rewritten passage with 1 vote: {passageIs chapter "a ship in the mist" 1}; {cost c9 r.st.host t9}"
    (v9 == "admitted" && passageIs chapter "a ship in the mist" 1 && headCount r9.st.host obj 2 == some 1)
  -- LS10 round two: two proposals signed over ONE view land, in both orders, to the same World
  let closes2 := closes + 20
  let c10a := call r a 1 (proposeA 0 "the keeper wakes") 0 closes2 [] []
  let c10b := call r b 1 (proposeA 1 "the lamp goes out") 0 closes2 [] []
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
  let c11a := call r a 3 (voteA 1) 0 closes2 pin11 []
  let c11b := call r b 0 (proposeA 1 "the lamp burns") 0 closes2 pin11 []
  let (r11a, v11a, _) := go prog r c11a
  r := note r11a s!"LS11a A votes for B's round-two passage: {v11a}" (v11a == "admitted")
  let (r11b, v11b, _) := go prog r c11b
  r := note { r11b with log := r.log, bad := r.bad } s!"LS11b B edits it, signed over the same view as the vote: {v11b}"
    (v11b.startsWith "rejected stale" && passageIs (passage r.st.host 2 1) "the lamp goes out" 1)
  -- LS12 the author is the guard's, not the method's (LANG-59): `steal` through a layer. `stolen q`
  -- installs `q` (CoAuthor or a planted copy), the layer over it and a story of the layer; A proposes
  -- at slot 0 and steals it for B; it gives the steal's verdict and the proposal's author after.
  let stolen (q : Package) (installed : Option D) (r : Run) : Except String (String × Option Data × String × Option Data) := do
    let some qb := Wire.encodePackage q | throw "no bytes"
    let (ra, qid) ← match installed with
      | some i => pure (r, i)
      | none =>
        let (ra, va, ta) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install qb))
        match ta.bind fun t => (createdIds t).head? with
        | some i => pure (ra, i)
        | none => throw s!"install: {va}"
    let tq := Sim.dc.bytes qid
    let text := storySteal (Print.hex tq)
    let l ← (Surface.readWith [(tq, q)] text).mapError fun e => s!"read the layer: {e.text text}"
    unless l.pkg.methods == ["edit", "propose", "seal", "vote", "forge", "steal"] do throw s!"the layer's methods {l.pkg.methods}"
    let some lb := Wire.encodePackage l.pkg | throw "the layer has no bytes"
    let (rb, vb, tb) := go prog ra (Sim.signed ra.st a a.key (Sim.S.pinsFor ra.st.host [a.id, qid]) (.install lb))
    let some lid := tb.bind fun t => (createdIds t).head? | throw s!"layer install: {vb}"
    let cl := rb.st.host.height + 12
    let some (.record ds) := (Read.readData p.state s!"(record (closes {cl}) (round 1) (window 20))").toOption | throw "seed"
    let some sd := stateSlots (recordRow p.state) ds 0 | throw "seed bytes"
    let (rc, vc, tc) := go prog rb (Sim.signed rb.st a a.key (Sim.S.pinsFor rb.st.host [a.id, lid, qid]) (.create (some lid) [] sd))
    let some lobj := tc.bind fun t => (createdIds t).head? | throw s!"create: {vc}"
    let ids := [a.id, lobj, lid, qid]
    let (rd, vd, _) := go prog rc (signedAt rc.st a (Sim.S.pinsFor rc.st.host ids) (.invoke lobj 1 (proposeA 0 "the first light") 100000 none) 0 cl)
    unless vd == "admitted" do throw s!"propose: {vd}"
    let some k := keyBytes proposalsDecl (.record [("round", .nat 1), ("slot", .nat 0)]) | throw "key"
    let ps : RowSlot D := .row ⟨lobj, 3, k⟩
    let stealA := args (.record [("slot", .nat), ("to", .digest)]) (.record [("slot", .nat 0), ("to", .digest (Sim.dc.bytes b.id))])
    let (re, ve, _) := go prog rd (signedAt rd.st a (Sim.S.pinsFor rd.st.host ids) (.invoke lobj 5 stealA 100000 none) 0 cl
      [(ps, rowPin Sim.env (headFloor Sim.env rd.st.host.rows lobj 3) (rowAt Sim.env rd.st.host.rows ps))])
    -- the forgery: A files slot 1 under B's name
    let forgeA := args (.record [("slot", .nat), ("to", .digest)]) (.record [("slot", .nat 1), ("to", .digest (Sim.dc.bytes b.id))])
    let (rf, vf, _) := go prog rd (signedAt rd.st a (Sim.S.pinsFor rd.st.host ids) (.invoke lobj 4 forgeA 100000 none) 0 cl)
    pure (ve, (storyRow re.st.host lobj 3 proposalsDecl (.record [("round", .nat 1), ("slot", .nat 0)])).bind (·.field "author"),
      vf, (storyRow rf.st.host lobj 3 proposalsDecl (.record [("round", .nat 1), ("slot", .nat 1)])).bind (·.field "author"))
  let authorIs (o : Option Data) (m : Sim.Member) : Bool :=
    match o with
    | some (.digest g) => g == Sim.dc.bytes m.id
    | _ => false
  match stolen p (some pkg) r with
  | .error e => r := note r s!"LS12 the stealing layer: {e}" false
  | .ok (v12, au, v12i, aui) =>
    r := note r s!"LS12 A, through a layer, gives its own proposal to B: {v12}; the author stays A: {authorIs au a}"
      (deniedWith v12 "authored: author" && authorIs au a)
    r := note r s!"LS12i A, through a layer, files a proposal under B's name: {v12i}; no row: {aui.isNone}"
      (deniedWith v12i "authored: author" && aui.isNone)
  let plantedSrc := (coAuthorText.replace "(if (deq x.val.author o.author) ok (refuse \"author\"))" "ok").replace
    "(insert x (if (deq x.val.author req.agent) ok (refuse \"author\")))" "(insert x ok)"
  match Surface.readPackage plantedSrc with
  | .error e => r := note r s!"LS12' read the planted CoAuthor: {e.text plantedSrc}" false
  | .ok pq =>
    match stolen pq none r with
    | .error e => r := note r s!"LS12' the planted stealing layer: {e}" false
    | .ok (v12', au', v12i', aui') =>
      r := note r s!"LS12' the same steal and forgery on a CoAuthor whose `authored` admits any author: {v12'}, {v12i'}; the authors are now B: {authorIs au' b}, {authorIs aui' b} (planted {plantedSrc != coAuthorText})"
        (plantedSrc != coAuthorText && v12' == "admitted" && authorIs au' b && v12i' == "admitted" && authorIs aui' b)
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

/-! ## LB: the Bell, a queue of rings a resident answers (LANG-52; a queue, LANG-58; answers in `rings`, LANG-59)

`world/resident/Bell.ob` is read from disk by `runAll` (one copy of the text: the file HOSTING's
resident installs). A ring inserts `pending` and `rings` at `(notBefore, ringer)`, its answer `none`;
the resident reads `pending` (the unanswered rings, in ring order) and answers one: it upserts
`rings[k]` with the answer, sending back the ring's text, and `pending` loses the row. The guard
`rung` sees the row the upsert or retract replaces: an answer is the resident's, once, over the
ring's own text; a retire takes an answered ring, or an unanswered one (with its pending row) from its
deadline on (LANG-76). Relations by index: pending 0, rings 1. -/

/-- Where the Bell's surface source and its emitted core live. -/
def bellSourcePath : System.FilePath := "world" / "resident" / "Bell.ob"
def bellCorePath : System.FilePath := "world" / "resident" / "Bell"

/-- The Bell's state field `ℓ` on `w`, read at the package's state type. -/
def bellField (p : Package) (w : World D) (obj : D) (ℓ : Label) : Option Data :=
  (w.live Sim.env obj).bind fun cell => (Nanodregg.Lang.readState Sim.digestOf (recordRow p.state) (stateOf cell)).toOption.bind (·.field ℓ)

/-- A field read as a boolean, bytes or digest (Data has no `BEq`). -/
def asBool : Option Data → Option Bool | some (.bool b) => some b | _ => none
def asBytes : Option Data → Option ByteArray | some (.bytes b) => some b | _ => none
def asDigest : Option Data → Option ByteArray | some (.digest b) => some b | _ => none

/-- An option of bytes: `some (some b)` for `some b`, `some none` for `none`, `none` otherwise. -/
def asOptBytes : Option Data → Option (Option ByteArray)
  | some (.inj "some" (.bytes b)) => some (some b)
  | some (.inj "none" (.record [])) => some none
  | _ => none

/-- An argument record's bytes at its type. -/
def argBytes (T : Ty) (d : Data) : ByteArray := (Wire.encodeData T d).getD .empty

/-- `ring`'s argument: an unaimed ring. -/
def bellArg (s : String) : ByteArray :=
  argBytes Bell.ringArg (.record [("text", .bytes s.toUTF8), ("to", Bell.toData none)])

/-- `ring`'s argument: a ring aimed at `target`'s method `method` through the Bell's grant `via`,
its candidate `cand`. -/
def aimedBellArg (s : String) (cand : ByteArray) (method : Nat) (target via : ByteArray) : ByteArray :=
  argBytes Bell.ringArg (.record [("text", .bytes s.toUTF8), ("to", Bell.toData (some (Bell.aimData cand method target via)))])

/-- A ring's key: its signed `notBefore` and its ringer. -/
def ringKey (nb : Nat) (ringer : Sim.Member) : Data :=
  .record [("agent", .digest (Sim.dc.bytes ringer.id)), ("notBefore", .nat nb)]

/-- `answer`'s argument: the ring's key, the ring's text and aim sent back, and the answer's text. -/
def answerArgTo (nb : Nat) (ringer : Sim.Member) (ringText s : String) (to : Option Data) : ByteArray :=
  argBytes Bell.answerArg (Bell.answerData nb ringText.toUTF8 (Sim.dc.bytes ringer.id) s.toUTF8 to)

/-- `answer`'s argument for an unaimed ring. -/
def answerArg (nb : Nat) (ringer : Sim.Member) (ringText s : String) : ByteArray :=
  answerArgTo nb ringer ringText s none

/-- `retire`'s argument: the ring's key. -/
def retireArg (nb : Nat) (ringer : Sim.Member) : ByteArray :=
  argBytes (.record [("notBefore", .nat), ("ringer", .digest)])
    (.record [("notBefore", .nat nb), ("ringer", .digest (Sim.dc.bytes ringer.id))])

/-- A layer over the Bell: `answer` without the resident check, `drop` (a ring retracted unanswered),
`rewrite` (an answered ring answered again, no `pending` edit), `say` (a ring inserted already
answered) and `seize` (the signer becomes the resident). The guards and the law, which no layer can
override, refuse what each would break. Methods: the Bell's first (answer 0, close 1, open 2,
retire 3, ring 4), then the layer's own (drop 5, rewrite 6, say 7, seize 8). -/
def bellTakeover (superHex : String) : String := s!"
(package
  (import bell \"{superHex}\")
  (layer bell)
  (type Aim (rec (cand digest) (method nat) (target digest) (via digest)))
  (type Support (rec (cell digest) (pin digest)))
  (type Proposal (rec (cand digest) (s0 (option Support)) (s1 (option Support)) (value bytes)))
  (method answer (arg (rec (notBefore nat) (ringText bytes) (ringer digest) (text bytes) (to (option Aim))))
    (calls ((invoke Proposal))) (edits 2)
    (done state
      (upsert rings (record (agent arg.ringer) (notBefore arg.notBefore))
        (record (answered (some (sum (ask bytes)) (inj (sum (ask bytes)) ask arg.text)))
          (captured (inj (sum (ask (rec (text bytes) (to (option Aim))))) ask (record (text arg.ringText) (to arg.to))))))
      (retract pending (record (agent arg.ringer) (notBefore arg.notBefore)))))
  (method drop (arg (rec (notBefore nat) (ringer digest))) (edits 2)
    (done state (retract rings (record (agent arg.ringer) (notBefore arg.notBefore)))
      (retract pending (record (agent arg.ringer) (notBefore arg.notBefore)))))
  (method rewrite (arg (rec (notBefore nat) (ringText bytes) (ringer digest) (text bytes) (to (option Aim)))) (edits 1)
    (done state (upsert rings (record (agent arg.ringer) (notBefore arg.notBefore))
      (record (answered (some (sum (ask bytes)) (inj (sum (ask bytes)) ask arg.text)))
          (captured (inj (sum (ask (rec (text bytes) (to (option Aim))))) ask (record (text arg.ringText) (to arg.to))))))))
  (method say (arg (rec (text bytes))) (edits 1)
    (done state (insert rings (record (agent req.agent) (notBefore req.notBefore))
      (record (answered (some (sum (ask bytes)) (inj (sum (ask bytes)) ask arg.text)))
          (captured (inj (sum (ask (rec (text bytes) (to (option Aim))))) ask (record (text arg.text) (to (none Aim)))))))))
  (method seize (done (with state (resident req.agent)))))
"

/-- Disable the actual generated guard fields in the checked Bell. The inherited
LB13 plant rows must then admit all four forbidden edits. -/
def bellPlant (src : String) : String := Id.run do
  let .ok p := Surface.readPackage src | return src
  let .record fs := p.body | return src
  let some queued := p.rels.lookup "pending" | return src
  let some rung := p.rels.lookup "rings" | return src
  unless (fs.lookup "queued").isSome && (fs.lookup "rung").isSome do return src
  let allow (d : RelDecl) := Term.lam p.state (.lam reqTy (.lam (guardInTy d) Std.okT))
  let fs := fs.map fun (n, t) => (n,
    if n == "queued" then allow queued else if n == "rung" then allow rung else t)
  return (Print.package { p with body := .record fs }).getD src

/-- The LB rows: the Bell through the real receivers. `a` is the operator (owner, and a ringer);
`b` is the resident (and a ringer). Under `skipJudge` the law row is the plant. -/
def bellRows (mode : Mode) (r0 : Run) (a b : Sim.Member) (src : String) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let p ← match Surface.readPackage src with
    | .ok p => pure p
    | .error e => return note r s!"LB1 read the Bell ({bellSourcePath}): {e.text src}" false
  let some pb := Wire.encodePackage p | return note r "LB1 the Bell has no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LB1 A installs the Bell from its surface source ({src.length} chars, {pb.size} package bytes; methods {p.methods}, laws {p.laws}, relations {p.rels.map (·.1)}): {v1}"
    (v1 == "admitted" && p.methods == ["answer", "close", "open", "retire", "ring"] && p.laws == ["bell"] &&
      p.rels.map (·.1) == ["pending", "rings"])
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LB1 no package id" false
  let some dP := p.rels.lookup "pending" | return note r "LB1 no pending" false
  let some dR := p.rels.lookup "rings" | return note r "LB1 no rings" false
  let seed ← match Read.readData p.state s!"(record (open true) (resident #{Print.hex (Sim.dc.bytes b.id)}))" with
    | .ok (.record ds) => match stateSlots (recordRow p.state) ds 0 with
      | some s => pure s
      | none => return note r "LB2 seed has no bytes" false
    | _ => return note r "LB2 no seed" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"LB2 no bell: {v2}" false
  r := note r2 s!"LB2 A creates the bell, B its resident: {v2}; its two relations are born empty"
    (v2 == "admitted" && [0, 1].all fun i => headCount r2.st.host obj i == some 0)
  let (r3, v3, t3) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0, .invoke 4] none))
  r := note r3 s!"LB3 A grants B answer and ring: {v3}" (v3 == "admitted")
  let some gr := t3.bind fun t => (createdIds t).head? | return note r "LB3 no grant id" false
  let pinsOf (r : Run) (m : Sim.Member) := Sim.S.pinsFor r.st.host ([m.id, obj, pkg] ++ if m.id == b.id then [gr] else [])
  let viaOf (m : Sim.Member) : Option D := if m.id == b.id then some gr else none
  -- the row of relation `rel` (declared `d`) of object `o` at `key`, pinned at what the signer sees on `w`
  let pinAtObj (o : D) (w : World D) (rel : Nat) (d : RelDecl) (key : Data) : List (RowSlot D × D) :=
    match keyBytes d key with
    | some k => let s : RowSlot D := .row ⟨o, rel, k⟩; [(s, rowPin Sim.env (headFloor Sim.env w.rows o rel) (rowAt Sim.env w.rows s))]
    | none => []
  let pinRow := pinAtObj obj
  -- a ring's two rows, pinned: what an answer edits
  let pinBoth (w : World D) (key : Data) := pinRow w 0 dP key ++ pinRow w 1 dR key
  let call (r : Run) (m : Sim.Member) (method : Nat) (x : ByteArray) (nb : Nat)
      (rowPins : List (RowSlot D × D) := []) : Call D :=
    signedAt r.st m (pinsOf r m) (.invoke obj method x 100000 (viaOf m)) nb (nb + 1024) rowPins
  let rowOf (o : D) (w : World D) (rel : Nat) (d : RelDecl) (key : Data) : Option Data := storyRow w o rel d key
  let capturedText (row : Option Data) : Option ByteArray := match row.bind (·.field "captured") with
    | some (.inj "ask" value) => asBytes (value.field "text")
    | _ => none
  let pendingText (w : World D) (key : Data) := capturedText (rowOf obj w 0 dP key)
  let ringText (w : World D) (key : Data) := capturedText (rowOf obj w 1 dR key)
  let ringAnswer (o : D) (w : World D) (key : Data) : Option (Option ByteArray) :=
    match (rowOf o w 1 dR key).bind (·.field "answered") with
    | some (.inj "none" (.record [])) => some none
    | some (.inj "some" (.inj "ask" (.bytes b))) => some (some b)
    | _ => none
  let present (w : World D) (rel : Nat) (d : RelDecl) (key : Data) : Bool :=
    match keyBytes d key with
    | some k => (rowAt Sim.env w.rows (.row ⟨obj, rel, k⟩)).isSome
    | none => false
  -- the pending rings' keys in the order `read BELL pending 64` lists them (THE range read)
  let queue (w : World D) : List (Nat × ByteArray) :=
    match headOf Sim.env w.rows obj 0 with
    | some (_, _, _, _, width, _) =>
      match rangeRows Sim.env w.rows obj 0 width .empty 64 with
      | some l => match rangeRowData Sim.digestOf "pending" dP l with
        | .ok ds => ds.filterMap fun d => match d.field "key" |>.bind (·.field "notBefore"), d.field "key" |>.bind (·.field "agent") with
          | some (.nat n), some (.digest g) => some (n, g)
          | _, _ => none
        | .error _ => []
      | none => []
    | none => []
  let cost (c : Call D) (w : World D) : String :=
    s!"required steps / ticks {match measure w c with | .ok (q, k) => s!"{q} / {k}" | .error e => e}"
  -- LB4 A rings: one turn, two inserts, no cell write
  let h0 := r.st.host.height
  let k0 := ringKey h0 a
  let c4 := call r a 4 (bellArg "is anyone home?") h0
  let (r4, v4, t4) := go prog r c4
  r := note r4 s!"LB4 A rings \"is anyone home?\" at notBefore {h0}: {v4}; {cost c4 r.st.host}"
    (v4 == "admitted" && pendingText r4.st.host k0 == some "is anyone home?".toUTF8 &&
      ringText r4.st.host k0 == some "is anyone home?".toUTF8 && ringAnswer obj r4.st.host k0 == some none &&
      (t4.map fun t => t.creates.isEmpty && t.rows.length == 2 && t.touches.all (·.act == .keep) &&
        t.touches.any (·.cell == obj)) == some true)
  -- LB5 two rings over ONE view, A's and B's: both land, in both orders, to the same World
  let h1 := r.st.host.height
  let c5a := call r a 4 (bellArg "anyone?") h1
  let c5b := call r b 4 (bellArg "me too") h1
  let (q5b, w5b, _) := go prog r c5b
  let (q5ba, w5ba, _) := go prog q5b c5a
  let (r5a, v5a, _) := go prog r c5a
  r := note r5a s!"LB5a A rings at notBefore {h1}: {v5a}" (v5a == "admitted")
  let (r5b, v5b, _) := go prog r c5b
  r := note r5b s!"LB5b B rings, signed over the same view as A: {v5b}" (v5b == "admitted" && headCount r5b.st.host obj 0 == some 3)
  r := note r s!"LB5c the other order (B then A): {w5b}, {w5ba}; the same rows root and cells root"
    (w5b == "admitted" && w5ba == "admitted" && headCount q5ba.st.host obj 0 == some 3 &&
      q5ba.st.host.rowsRoot Sim.env == r.st.host.rowsRoot Sim.env && q5ba.st.host.root Sim.env == r.st.host.root Sim.env)
  let (r5d, v5d, _) := go prog r (call r a 4 (bellArg "again") h1)
  r := note { r5d with log := r.log, bad := r.bad } s!"LB5d A rings again at notBefore {h1}: {v5d}" (v5d.startsWith "rejected keyTaken")
  -- LB6 the queue in ring order: A's first ring, then the two at h1 (by ringer digest)
  let q6 := queue r.st.host
  let ab := [Sim.dc.bytes a.id, Sim.dc.bytes b.id]
  let tie := if compare (Sim.dc.bytes a.id).toList (Sim.dc.bytes b.id).toList == .lt then ab else ab.reverse
  r := note r s!"LB6 the resident's read of pending lists {q6.length} rings, lowest first: notBefore {q6.map (·.1)}"
    (q6 == [(h0, Sim.dc.bytes a.id)] ++ tie.map (h1, ·))
  -- LB7 the resident answers the LOWEST pending ring (both its rows pinned), sending its text back
  let c7 := call r b 0 (answerArg h0 a "is anyone home?" "yes, I am here") r.st.host.height (pinBoth r.st.host k0)
  let (r7, v7, _) := go prog r c7
  r := note r7 s!"LB7 B answers the lowest ring \"yes, I am here\": {v7}; {cost c7 r.st.host}; the queue now starts at notBefore {(queue r7.st.host).head?.map (·.1)}"
    (v7 == "admitted" && ringAnswer obj r7.st.host k0 == some (some "yes, I am here".toUTF8) &&
      !present r7.st.host 0 dP k0 && ringText r7.st.host k0 == some "is anyone home?".toUTF8 &&
      (queue r7.st.host).map (·.1) == [h1, h1])
  -- LB7u the same answer unpinned: Lang asks for the row before any guard runs (what derivePins answers)
  let (_, v7u, _) := go prog r (call r b 0 (answerArg h1 a "anyone?" "hi") r.st.host.height)
  r := note r s!"LB7u B answers A's ring at {h1} without its rows pinned: {v7u}" (v7u.startsWith "refused rowUnpinned")
  -- LB7v every old row is found before any guard runs: the answered ring again with only its
  -- `rings` row pinned is refused `rowUnpinned` at `pending` (relation 0), not by `rung`
  let (_, v7v, _) := go prog r (call r b 0 (answerArg h0 a "is anyone home?" "again") r.st.host.height (pinRow r.st.host 1 dR k0))
  let pk0 := match keyBytes dP k0 with | some k => s!" 0 0x{Print.hex k}" | none => "?"
  r := note r s!"LB7v B answers the answered ring with only its rings row pinned: {v7v}"
    (v7v.startsWith "refused rowUnpinned" && (v7v.splitOn pk0).length > 1)
  -- LB8 exactly once, by the guard: the answered ring again (its rows pinned, pending's absent)
  let (r8, v8, _) := go prog r (call r b 0 (answerArg h0 a "is anyone home?" "again") r.st.host.height (pinBoth r.st.host k0))
  r := note { r8 with log := r.log, bad := r.bad } s!"LB8 B answers the answered ring again: {v8}"
    (deniedWith v8 "rung: answered" && ringAnswer obj r.st.host k0 == some (some "yes, I am here".toUTF8))
  -- LB8b two answers of one ring over one view: the second meets the answered row
  let k1 := ringKey h1 a
  let pins8 := pinBoth r.st.host k1
  let c8a := call r b 0 (answerArg h1 a "anyone?" "first") r.st.host.height pins8
  let c8b := call r b 0 (answerArg h1 a "anyone?" "second") r.st.host.height pins8
  let (r8a, v8a, _) := go prog r c8a
  r := note r8a s!"LB8a B answers A's ring at {h1}: {v8a}" (v8a == "admitted")
  let (r8b, v8b, _) := go prog r c8b
  -- KERNEL-66: the pins are compared before any receiver, so the view the first answer moved is
  -- declined `stale` before the guard reads the row; LB8 is the guard's own refusal, on a current view
  r := note { r8b with log := r.log, bad := r.bad } s!"LB8b B answers it again over the same view: {v8b}; the answer stays \"first\" (the view moved: the kernel declines it stale before the guard runs, KERNEL-66)"
    (v8b == "rejected stale" && ringAnswer obj r.st.host k1 == some (some "first".toUTF8))
  -- LB8t the answer is to the ring as rung: another text sent back is refused by the guard
  let kb := ringKey h1 b
  let (_, v8t, _) := go prog r (call r b 0 (answerArg h1 b "me three" "yes") r.st.host.height (pinBoth r.st.host kb))
  r := note r s!"LB8t B answers its own ring sending back another ring text: {v8t}" (deniedWith v8t "rung: text")
  -- LB9 only the resident answers; LB9b the text bound
  let (r9, v9, _) := go prog r (call r a 0 (answerArg h1 b "me too" "me, the owner") r.st.host.height (pinBoth r.st.host kb))
  r := note r9 s!"LB9 A (the owner, who may invoke every method) answers B's ring: {v9}" (refusedBy v9 "answer" "notResident")
  let (r9b, v9b, _) := go prog r (call r b 0 (answerArg h1 b "me too" "") r.st.host.height (pinBoth r.st.host kb))
  r := note r9b s!"LB9b B answers with an empty text: {v9b}" (refusedBy v9b "answer" "text 1..2000")
  -- LB10 retire: an answered ring leaves `rings`; an unanswered one is refused by the guard
  let (r10, v10, _) := go prog r (call r a 3 (retireArg h0 a) r.st.host.height (pinRow r.st.host 1 dR k0))
  r := note r10 s!"LB10 A retires the answered ring at {h0}: {v10}"
    (v10 == "admitted" && !present r10.st.host 1 dR k0 && headCount r10.st.host obj 1 == some 2)
  -- LB10b-LB10d (LANG-76) an unanswered ring has a deadline, its notBefore + 2048 (`(patience 2048)`):
  -- before it `rung` refuses retiring it; from it on, anyone the kernel lets invoke `retire` abandons
  -- it, its rings row and its pending row in one Turn (the heights are set, as LT's expiry row does)
  let (r10b, v10b, _) := go prog r (call r a 3 (retireArg h1 b) r.st.host.height (pinBoth r.st.host kb))
  r := note { r10b with log := r.log, bad := r.bad } s!"LB10b A retires B's ring, still pending, before its deadline {h1 + 2048}: {v10b}"
    (deniedWith v10b "rung: unanswered" && present r.st.host 1 dR kb && present r.st.host 0 dP kb)
  let atHeight (H : Nat) : Run := { r with st := { r.st with host := { r.st.host with height := H } } }
  let early := atHeight (h1 + 2047)
  let (_, v10c, _) := go prog early (call early a 3 (retireArg h1 b) (h1 + 2047) (pinBoth early.st.host kb))
  r := note r s!"LB10c A retires it one height before its deadline (signed notBefore {h1 + 2047}): {v10c}"
    (deniedWith v10c "rung: unanswered")
  let late := atHeight (h1 + 2048)
  let (r10d, v10d, _) := go prog late (call late a 3 (retireArg h1 b) (h1 + 2048) (pinBoth late.st.host kb))
  r := note r s!"LB10d A retires it at its deadline (signed notBefore {h1 + 2048}): {v10d}; its rings row and its pending row both leave"
    (v10d == "admitted" && !present r10d.st.host 1 dR kb && !present r10d.st.host 0 dP kb &&
      headCount r10d.st.host obj 0 == some 0 && headCount r10d.st.host obj 1 == some 1)
  -- LB11 the queue's bound: A fills pending to its limit, 64, one ring per height; the 65th is relationFull
  let mut fills := 0
  while headCount r.st.host obj 0 != some 64 && fills < 64 do
    fills := fills + 1
    let (rf, _, _) := go prog r (call r a 4 (bellArg "full?") r.st.host.height)
    r := { rf with log := r.log, bad := r.bad }
  let (r11, v11, _) := go prog r (call r a 4 (bellArg "one more") r.st.host.height)
  r := note { r11 with log := r.log, bad := r.bad } s!"LB11 pending holds {headCount r.st.host obj 0}; A rings once more: {v11}"
    (headCount r.st.host obj 0 == some 64 && v11.startsWith "rejected relationFull")
  -- LB12n-LB12q who may open, close and retire: the object's owner, or a member whose grant names
  -- the method (KERNEL-25 `invoke_authorized`). B, the resident, holds a grant for answer and ring
  -- only, so its close, open and retire are refused by the kernel before the Bell runs.
  let (r12n, v12n, _) := go prog r (call r b 1 (argBytes (.record []) (.record [])) r.st.host.height)
  r := note r s!"LB12n B (the resident, granted answer and ring) closes A's bell: {v12n}"
    (v12n.startsWith "refused grantRight" && asBool (bellField p r12n.st.host obj "open") == some true)
  let (_, v12o, _) := go prog r (call r b 2 (argBytes (.record []) (.record [])) r.st.host.height)
  r := note r s!"LB12o B opens A's bell: {v12o}" (v12o.startsWith "refused grantRight")
  let (r12q, v12q, _) := go prog r (call r b 3 (retireArg h1 a) r.st.host.height (pinRow r.st.host 1 dR k1))
  r := note r s!"LB12q B retires A's answered ring at {h1}: {v12q}"
    (v12q.startsWith "refused grantRight" && present r12q.st.host 1 dR k1)
  -- LB12 closed
  let (r12, v12, _) := go prog r (call r a 1 (argBytes (.record []) (.record [])) r.st.host.height)
  r := note r12 s!"LB12 A closes the bell: {v12}" (v12 == "admitted" && asBool (bellField p r12.st.host obj "open") == some false)
  let (r12b, v12b, _) := go prog r (call r a 4 (bellArg "after hours") r.st.host.height)
  r := note r12b s!"LB12b A rings a closed bell: {v12b}" (refusedBy v12b "ring" "closed")
  -- LB13 guards and the law outlive every layer. `layered q` installs package `q` (the Bell, or
  -- `bellPlant` of it), the takeover layer over it, and a bell of the layer whose resident is B,
  -- with B granted answer, rewrite and say; it gives the run, the closure's ids, the bell and the grant.
  let layered (q : Package) (installed : Option D) (r : Run) : Except String (Run × List D × D × D) := do
    let some qb := Wire.encodePackage q | throw "no bytes"
    let (ra, qid) ← match installed with
      | some i => pure (r, i)
      | none =>
        let (ra, va, ta) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install qb))
        match ta.bind fun t => (createdIds t).head? with
        | some i => pure (ra, i)
        | none => throw s!"install: {va}"
    let tq := Sim.dc.bytes qid
    let text := bellTakeover (Print.hex tq)
    let l ← (Surface.readWith [(tq, q)] text).mapError fun e => s!"read the layer: {e.text text}"
    let some lb := Wire.encodePackage l.pkg | throw "the layer has no bytes"
    unless l.pkg.laws == ["bell"] do throw s!"the layer's laws {l.pkg.laws}"
    -- the indices below are these: the Bell's methods first, then the layer's own
    unless l.pkg.methods == ["answer", "close", "open", "retire", "ring", "drop", "rewrite", "say", "seize"] do
      throw s!"the layer's methods {l.pkg.methods}"
    let (rb, vb, tb) := go prog ra (Sim.signed ra.st a a.key (Sim.S.pinsFor ra.st.host [a.id, qid]) (.install lb))
    let some lid := tb.bind fun t => (createdIds t).head? | throw s!"layer install: {vb}"
    let (rc, vc, tc) := go prog rb (Sim.signed rb.st a a.key (Sim.S.pinsFor rb.st.host [a.id, lid, qid]) (.create (some lid) [] seed))
    let some lobj := tc.bind fun t => (createdIds t).head? | throw s!"create: {vc}"
    let (rd, vd, td) := go prog rc (Sim.signed rc.st a a.key (Sim.S.pinsFor rc.st.host [a.id, b.id, lobj]) (.grant lobj b.id [.invoke 0, .invoke 6, .invoke 7] none))
    let some gid := td.bind fun t => (createdIds t).head? | throw s!"grant: {vd}"
    pure ({ rd with log := r.log, bad := r.bad }, [lobj, lid, qid], lobj, gid)
  -- one act on a layered bell: `m` signs method `meth` of `lobj` with the argument and the rows pinned
  let byL (r : Run) (ids : List D) (lobj : D) (gid : D) (m : Sim.Member) (meth : Nat) (x : ByteArray)
      (rowPins : List (RowSlot D × D)) : Run × String :=
    let via := if m.id == b.id then some gid else none
    let extra := if m.id == b.id then [gid] else []
    let h := r.st.host.height
    let (rr, v, _) := go prog r (signedAt r.st m (Sim.S.pinsFor r.st.host (m.id :: extra ++ ids)) (.invoke lobj meth x 100000 via) h (h + 1024) rowPins)
    (rr, v)
  -- the four takeovers, each from a fresh ring on the layered bell, each giving its verdict:
  -- T1 A answers through the layer's `answer` (no resident check); T2 B answers a ring, then
  -- `rewrite`s the answered ring (no pending edit); T3 A `drop`s its unanswered ring; T4 B `say`s
  -- a ring already answered
  let takeovers (r : Run) (ids : List D) (lobj gid : D) : List String :=
    let ring (r : Run) (m : Sim.Member) (s : String) : Run × Data × String :=
      let h := r.st.host.height
      let (rr, v) := byL r ids lobj gid m 4 (bellArg s) []
      (rr, ringKey h m, v)
    let both (w : World D) (k : Data) := pinAtObj lobj w 0 dP k ++ pinAtObj lobj w 1 dR k
    let nbOf (k : Data) : Nat := match k.field "notBefore" with | some (.nat n) => n | _ => 0
    let (r1, k1, w1) := ring r a "who answers?"
    let t1 := if w1 != "admitted" then s!"the ring: {w1}" else
      (byL r1 ids lobj gid a 0 (answerArg (nbOf k1) a "who answers?" "I do now") (both r1.st.host k1)).2
    let (r2, k2, w2) := ring r a "answer me once"
    let (r2a, w2a) := byL r2 ids lobj gid b 0 (answerArg (nbOf k2) a "answer me once" "once") (both r2.st.host k2)
    let t2 := if w2 != "admitted" || w2a != "admitted" then s!"the ring and its answer: {w2}, {w2a}" else
      (byL r2a ids lobj gid b 6 (answerArg (nbOf k2) a "answer me once" "twice") (pinAtObj lobj r2a.st.host 1 dR k2)).2
    let (r3, k3, w3) := ring r a "never mind"
    let t3 := if w3 != "admitted" then s!"the ring: {w3}" else
      (byL r3 ids lobj gid a 5 (retireArg (nbOf k3) a) (both r3.st.host k3)).2
    -- the layer's own `say` takes `(rec (text bytes))`: a text alone, no aim
    let sayArg := argBytes (.record [("text", .bytes)]) (.record [("text", .bytes "asked and answered".toUTF8)])
    let t4 := (byL r ids lobj gid b 7 sayArg []).2
    [t1, t2, t3, t4]
  let (rL, ids, lobj, gid) ← match layered p (some pkg) r with
    | .ok x => pure x
    | .error e => return note r s!"LB13 the layered bell: {e}" false
  r := note rL s!"LB13 A installs a layer over the Bell (answer without the resident check, drop, rewrite, say, seize) and a bell of it, B its resident"
    (asDigest (bellField p rL.st.host lobj "resident") == some (Sim.dc.bytes b.id))
  let ts := takeovers r ids lobj gid
  let want := [("LB13c A answers a ring through the layer, not being the resident", "rung: notResident"),
    ("LB13e B, the resident, answers a ring and then rewrites the answer through the layer (no pending row)", "rung: answered"),
    ("LB13f A drops its own unanswered ring through the layer", "rung: unanswered"),
    ("LB13g B says a ring already answered through the layer", "rung: answered")]
  for (w, v) in want.zip ts do
    r := note r s!"{w.1}: {v}" (deniedWith v w.2)
  -- the guard is what refuses each: the Bell with `rung` admitting every edit (and `queued` every
  -- retracter) admits all four
  let planted := bellPlant src
  match Surface.readPackage planted with
  | .error e => r := note r s!"LB13' read the planted Bell: {e.text planted}" false
  | .ok pq =>
    match layered pq none r with
    | .error e => r := note r s!"LB13' the planted layered bell: {e}" false
    | .ok (rq, qids, qobj, qgid) =>
      let vs := takeovers rq qids qobj qgid
      r := note r s!"LB13' the same four on a Bell whose `rung` admits every edit and `queued` any retracter: {vs} (planted {planted != src})"
        (planted != src && vs.length == 4 && vs.all (· == "admitted"))
  let (r13h, v13h, _) := go prog r (signedAt r.st a (Sim.S.pinsFor r.st.host (a.id :: ids)) (.invoke lobj 8 (argBytes (.record []) (.record [])) 100000 none)
    r.st.host.height (r.st.host.height + 1024))
  r := { r13h with log := r.log, bad := r.bad }
  if mode = .skipJudge then
    r := note r s!"PLANT skip-judge: LB13d the seizure must now be admitted: {v13h}" (v13h == "admitted")
  else
    r := note r s!"LB13d A seizes the layered bell, making itself the resident: {v13h}"
      (deniedWith v13h "bell: resident" && asDigest (bellField p r.st.host lobj "resident") == some (Sim.dc.bytes b.id))
  return r

/-! ## LQ / LW: the Std laws `quorum` and `windowed`, written as surface laws, through the receivers -/

/-- A setting two members change together: `quorum value 2 #a #b` over a proposal, approvals by
bit (member `i` sets bit `2^i`), and the change. The methods are permissive (`force` writes any value)
so that the law is what judges. -/
def quorumText (aHex bHex : String) : String := s!"
(package
  (type Proposal (sum (laws bytes) (set nat)))
  (state (rec (approvals nat) (proposal Proposal) (value nat)))
  (method apply
    (case state.proposal (laws _ (refuse \"notSet\"))
      (set v (done (with state (approvals 0) (value v))))))
  (method approve (arg (rec (bit nat))) (done (with state (approvals (+ state.approvals arg.bit)))))
  (method force (arg (rec (v nat))) (done (with state (approvals 0) (value arg.v))))
  (method propose (arg (rec (v nat))) (done (with state (approvals 0) (proposal (Proposal set arg.v)))))
  (law shared (quorum value 2 #{aHex} #{bHex})))
"

/-- A value changed at most twice per epoch of `W` heights: `windowed value W 2`. The method writes
the epoch of the call's own window and bumps the count on a change, as the law demands. -/
def rateW : Nat := 64
def rateText : String := s!"
(package
  (state (rec (count nat) (epoch nat) (value nat)))
  (method set (arg (rec (v nat)))
    (done (with state (value arg.v) (epoch (/ req.notBefore {rateW}))
      (count (+ (if (== (/ req.notBefore {rateW}) state.epoch) state.count 0) (if (== arg.v state.value) 0 1))))))
  (law rate (windowed value {rateW} 2)))
"

/-- A record argument `{ℓ = n}`. -/
def natArg (ℓ : Label) (n : Nat) : ByteArray := (Wire.encodeData (.record [(ℓ, .nat)]) (.record [(ℓ, .nat n)])).getD .empty
def unitArg : ByteArray := (Wire.encodeData (.record []) (.record [])).getD .empty

/-- A state field read as a number. -/
def asNat : Option Data → Option Nat | some (.nat n) => some n | _ => none

/-- The LQ rows: `quorum` through the receivers. `a` is member 0 (bit 1) and the owner; `b` member 1
(bit 2), acting through a grant. Under `skipJudge` the no-quorum row is the plant. -/
def quorumRows (mode : Mode) (r0 : Run) (a b : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let text := quorumText (Print.hex (Sim.dc.bytes a.id)) (Print.hex (Sim.dc.bytes b.id))
  let p ← match Surface.readPackage text with
    | .ok p => pure p
    | .error e => return note r s!"LQ1 read the quorum package: {e.text text}" false
  let some pb := Wire.encodePackage p | return note r "LQ1 no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LQ1 A installs a package whose law is the surface's (quorum value 2 #a #b) ({text.length} chars): {v1}"
    (v1 == "admitted" && p.methods == ["apply", "approve", "force", "propose"] && p.laws == ["shared"])
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LQ1 no package id" false
  let seedOf (approvals : Nat) : Option Slots :=
    match Read.readData p.state s!"(record (approvals {approvals}) (proposal (set 0)) (value 0))" with
    | .ok (.record ds) => stateSlots (recordRow p.state) ds 0 | _ => none
  let some seed := seedOf 0 | return note r "LQ2 no seed" false
  let some seeded := seedOf 1 | return note r "LQ2 no seed" false
  let (r2b, v2b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seeded))
  if mode != .skipJudge then
    r := note { r2b with log := r.log, bad := r.bad } s!"LQ2b A creates it with an approval already counted: {v2b}" (deniedWith v2b "shared: approvals at birth")
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"LQ2 no object: {v2}" false
  r := note r2 s!"LQ2 A creates the shared setting: {v2}" (v2 == "admitted")
  let (r3, v3, t3) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj]) (.grant obj b.id [.invoke 0, .invoke 1, .invoke 2, .invoke 3] none))
  r := note r3 s!"LQ3 A grants B every method: {v3}" (v3 == "admitted")
  let some gr := t3.bind fun t => (createdIds t).head? | return note r "LQ3 no grant id" false
  let byA (r : Run) (m : Nat) (x : ByteArray) : Call D :=
    Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj m x 100000 none)
  let byB (r : Run) (m : Nat) (x : ByteArray) : Call D :=
    Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, obj, pkg, gr]) (.invoke obj m x 100000 (some gr))
  let valueOf (r : Run) := asNat (bellField p r.st.host obj "value")
  let (r4, v4, _) := go prog r (byA r 3 (natArg "v" 5))
  r := note r4 s!"LQ4 A proposes value 5: {v4}" (v4 == "admitted")
  let (r5, v5, _) := go prog r (byA r 0 unitArg)
  r := { r5 with log := r.log, bad := r.bad }
  if mode = .skipJudge then
    r := note r s!"PLANT skip-judge: LQ5 applying with no approvals must now be admitted: {v5}" (v5 == "admitted")
  else
    r := note r s!"LQ5 A applies with no approvals: {v5}" (deniedWith v5 "shared: no quorum" && valueOf r == some 0)
  let (r6, v6, _) := go prog r (byA r 1 (natArg "bit" 2))
  if mode != .skipJudge then
    r := note { r6 with log := r.log, bad := r.bad } s!"LQ6 A sets B's approval bit: {v6}" (deniedWith v6 "shared: not an approval")
  let (r7, v7, _) := go prog r (byA r 1 (natArg "bit" 1))
  r := note r7 s!"LQ7 A approves (bit 1): {v7}" (v7 == "admitted")
  let (r7b, v7b, _) := go prog r (byA r 1 (natArg "bit" 1))
  if mode != .skipJudge then
    r := note { r7b with log := r.log, bad := r.bad } s!"LQ7b A approves twice: {v7b}" (deniedWith v7b "shared: not an approval")
  let (r8, v8, _) := go prog r (byA r 0 unitArg)
  if mode != .skipJudge then
    r := note { r8 with log := r.log, bad := r.bad } s!"LQ8 A applies with one approval of two: {v8}" (deniedWith v8 "shared: no quorum")
  let (r9, v9, _) := go prog r (byB r 1 (natArg "bit" 2))
  r := note r9 s!"LQ9 B approves (bit 2): {v9}" (v9 == "admitted")
  let (r9b, v9b, _) := go prog r (byB r 2 (natArg "v" 77))
  if mode != .skipJudge then
    r := note { r9b with log := r.log, bad := r.bad } s!"LQ9b B, with the quorum, writes 77 where 5 was proposed: {v9b}" (deniedWith v9b "shared: not the proposal")
  let (r10, v10, _) := go prog r (byB r 0 unitArg)
  r := note r10 s!"LQ10 B applies with both approvals: {v10}; value {valueOf r10}, approvals {asNat (bellField p r10.st.host obj "approvals")}"
    (v10 == "admitted" && valueOf r10 == some 5 && asNat (bellField p r10.st.host obj "approvals") == some 0)
  -- LQ11 the relaw arm: a DATA object governed by the same law; removing the law needs the quorum's laws proposal
  let (r11, v11, t11) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, pkg]) (.create none [pkg] seed))
  r := note r11 s!"LQ11 A creates a data object under the shared law: {v11}" (v11 == "admitted")
  let some dobj := t11.bind fun t => (createdIds t).head? | return note r "LQ11 no object" false
  let (r11b, v11b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, dobj, pkg]) (.law dobj [] none))
  r := { r11b with log := r.log, bad := r.bad }
  if mode = .skipJudge then
    r := note r s!"PLANT skip-judge: LQ11b removing the law with no quorum must now be admitted: {v11b}" (v11b == "admitted")
  else
    r := note r s!"LQ11b A removes the law with no quorum: {v11b}" (deniedWith v11b "shared: no quorum")
  return r

/-- The LW rows: `windowed` through the receivers, every call signed with a window inside one epoch of
`rateW` heights (the law reads the epoch from the window the signer committed to). -/
def windowedRows (mode : Mode) (r0 : Run) (a : Sim.Member) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  let p ← match Surface.readPackage rateText with
    | .ok p => pure p
    | .error e => return note r s!"LW1 read the rate package: {e.text rateText}" false
  let some pb := Wire.encodePackage p | return note r "LW1 no bytes" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install pb))
  r := note r1 s!"LW1 A installs a package whose law is the surface's (windowed value {rateW} 2) ({rateText.length} chars): {v1}"
    (v1 == "admitted" && p.laws == ["rate"])
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LW1 no package id" false
  -- the window of the epoch the next turn's height falls in
  let epochOf (r : Run) : Nat := (r.st.host.height + 1) / rateW
  let inEpoch (r : Run) (pins : List D) (body : Body D) : Call D :=
    let e := epochOf r
    signedAt r.st a (Sim.S.pinsFor r.st.host pins) body (e * rateW) (e * rateW + rateW - 1)
  let seedAt (e : Nat) : Option Slots :=
    match Read.readData p.state s!"(record (count 0) (epoch {e}) (value 0))" with
    | .ok (.record ds) => stateSlots (recordRow p.state) ds 0 | _ => none
  let some seed := seedAt (epochOf r) | return note r "LW2 no seed" false
  let some stale := seedAt (epochOf r + 1) | return note r "LW2 no seed" false
  let (r2b, v2b, _) := go prog r (inEpoch r [a.id, pkg] (.create (some pkg) [] stale))
  if mode != .skipJudge then
    r := note { r2b with log := r.log, bad := r.bad } s!"LW2b A creates it claiming the next epoch: {v2b}" (deniedWith v2b "rate: epoch is not the call's window")
  let (r2, v2, t2) := go prog r (inEpoch r [a.id, pkg] (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"LW2 no object: {v2}" false
  r := note r2 s!"LW2 A creates it in epoch {epochOf r}: {v2}" (v2 == "admitted")
  let set (r : Run) (v : Nat) : Call D := inEpoch r [a.id, obj, pkg] (.invoke obj 0 (natArg "v" v) 100000 none)
  let countOf (r : Run) := asNat (bellField p r.st.host obj "count")
  -- keep the rows inside one epoch: move the World to the start of the next one first
  for _ in [0:rateW] do
    if (r.st.host.height + 1) % rateW > rateW - 8 then
      let (rp, _, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
      r := { rp with log := r.log, bad := r.bad }
  let e0 := epochOf r
  let (r3, v3, _) := go prog r (set r 1)
  r := note r3 s!"LW3 A sets 1 in epoch {e0}: {v3}; count {countOf r3}" (v3 == "admitted" && countOf r3 == some 1)
  let (r4, v4, _) := go prog r (set r 2)
  r := note r4 s!"LW4 A sets 2: {v4}; count {countOf r4}" (v4 == "admitted" && countOf r4 == some 2)
  -- the plant's admitted third change is not kept: the rows after it run on the honest state
  let (_, v5, _) := go prog r (set r 3)
  if mode = .skipJudge then
    r := note r s!"PLANT skip-judge: LW5 a third change in one epoch must now be admitted: {v5}" (v5 == "admitted")
  else
    r := note r s!"LW5 A sets 3, a third change in epoch {e0}: {v5}" (deniedWith v5 "rate: rate limit 2" && countOf r == some 2)
  let (r6, v6, _) := go prog r (set r 2)
  r := note r6 s!"LW6 A sets 2 again (no change, no count): {v6}; count {countOf r6}" (v6 == "admitted" && countOf r6 == some 2)
  let e := epochOf r
  let span := signedAt r.st a (Sim.S.pinsFor r.st.host [a.id, obj, pkg]) (.invoke obj 0 (natArg "v" 4) 100000 none)
    (e * rateW) (e * rateW + rateW + 10)
  let (r7, v7, _) := go prog r span
  if mode != .skipJudge then
    r := note { r7 with log := r.log, bad := r.bad } s!"LW7 A signs a window spanning two epochs: {v7}" (deniedWith v7 "rate: window spans epochs")
  -- the next epoch: the count starts again
  for _ in [0:rateW + 1] do
    if epochOf r == e0 then
      let (rp, _, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.create none [] []))
      r := { rp with log := r.log, bad := r.bad }
  let (r8, v8, _) := go prog r (set r 3)
  r := note r8 s!"LW8 A sets 3 in epoch {epochOf r}: {v8}; count {countOf r8}" (v8 == "admitted" && countOf r8 == some 1 && epochOf r != e0)
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
  -- a Relay's seed: hits 0, me, n 0, next, via none
  let seed (nextB : ByteArray) : Slots :=
    [(stateBase, h0), (stateBase + 1, meB), (stateBase + 2, h0), (stateBase + 3, nextB), (stateBase + 4, noneB)]
  let some badNext := nextSlot (some "xyz".toUTF8) | return note r "LD3 no bytes" false
  let (rd3, vd3, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] (seed badNext)))
  if mode = .totalDigest then
    r := note rd3 s!"PLANT total-digest: LD3 a seed whose next is not a digest must now be admitted: {vd3}" (vd3 == "admitted")
  else if mode != .skipJudge then
    r := note r s!"LD3 A creates a Relay whose next is not a digest: {vd3}"
      (vd3.startsWith "refused lawDenied" && (vd3.splitOn "state field next: not a digest").length > 1)
  let (rd4, vd4, td4) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] (seed noneB)))
  r := note rd4 s!"LD4a A creates a last Relay: {vd4}" (vd4 == "admitted")
  let some lastO := td4.bind fun t => (createdIds t).head? | return note r "LD4 no object id" false
  let some badArgs := armArgs "xyz".toUTF8 | return note r "LD4 no arguments" false
  let (rd4b, vd4b, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid, lastO])
    (.invoke lastO relayArmIx badArgs 10000 none))
  if mode = .totalDigest then
    return note rd4b s!"PLANT total-digest: LD4b arguments whose via is not a digest must now be admitted: {vd4b}" (vd4b == "admitted")
  r := note rd4b s!"LD4b A arms it with a via that is not a digest: {vd4b}"
    (vd4b.startsWith "refused program" && (vd4b.splitOn "arguments: not a digest").length > 1)
  let mut objs : List D := []
  for _ in [0:6] do
    let some nextB := nextSlot (objs.head?.map Sim.dc.bytes) | return note r "LC no next bytes" false
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
      (.create (some rid) [] (seed nextB)))
    r := note rk s!"LC1 A creates Relay o{5 - objs.length}: {vk}" (vk == "admitted")
    let some o := tk.bind fun t => (createdIds t).head? | return note r "LC no object id" false
    objs := o :: objs
  let mut grants : List D := []
  for (x, y) in objs.zip objs.tail do
    let (rk, vk, tk) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, x, y])
      (.grant y x [.invoke relayGoIx] none))
    r := note rk s!"LC2 A grants o_k invoke go on o_k+1: {vk}" (vk == "admitted")
    let some gk := tk.bind fun t => (createdIds t).head? | return note r "LC no grant id" false
    grants := grants ++ [gk]
  -- LC2b each relay holds its grant: `arm {via}` (LANG-77's relay composes the next hop's argument;
  -- the grant it goes through is state, not an argument it forwards)
  for (x, g) in objs.zip grants do
    let some va := armArgs (Sim.dc.bytes g) | return note r "LC2b no arguments" false
    let (rk, vk, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid, x])
      (.invoke x relayArmIx va 10000 none))
    r := note rk s!"LC2b A arms o_k with its grant: {vk}" (vk == "admitted")
  let pinsAll := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let o0 := objs.headD 0
  let o1 := objs.getD 1 0
  let o5 := objs.getD 5 0
  let some args0 := goArgs 0 | return note r "LC3 no arguments" false
  -- LC3 entered at o1 with n = 0: o2 … o5 at depths 1 … 4 = callDepthMax, admitted; every object ran
  -- once, each composing `{n := n + 1}` for the next, so o5 received n = 4
  let (rc3, vc3, _) := go prog r (Sim.signed r.st a a.key pinsAll (.invoke o1 relayGoIx args0 10000 none))
  r := { rc3 with log := r.log, bad := r.bad }
  let hit5 := hitsOf Sim.env r.st.host o5
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC3 the chain's end must now be untouched: {vc3}, o5 hits {hit5}" (vc3 == "admitted" && hit5 == some 0)
  else
    r := note r s!"LC3 A invokes o1.go \{n 0}, calls 4 deep: {vc3}; o5 hits {hit5}, o5 received n {nOf Sim.env r.st.host o5} (composed by four relays), o5 sees itself as self {meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5)}"
      (vc3 == "admitted" && hit5 == some 1 && hitsOf Sim.env r.st.host o1 == some 1 &&
        nOf Sim.env r.st.host o5 == some 4 && nOf Sim.env r.st.host o1 == some 0 &&
        meOf Sim.env r.st.host o5 == some (Sim.dc.bytes o5))
  -- LC4 entered at o0: o5 would be at depth 5, past callDepthMax
  let pins4 := Sim.S.pinsFor r.st.host ([a.id, rid] ++ objs ++ grants)
  let (rc4, vc4, _) := go prog r (Sim.signed r.st a a.key pins4 (.invoke o0 relayGoIx args0 10000 none))
  r := { rc4 with log := r.log, bad := r.bad }
  if mode = .dropCalls then
    r := note r s!"PLANT drop-calls: LC4 five deep must now be admitted: {vc4}" (vc4 == "admitted")
  else
    r := note r s!"LC4 A invokes o0.go, calls 5 deep: {vc4}" (vc4.startsWith "refused callTooDeep")
  -- LC6 a method with more call slots than callsMax is not a method: install refuses it by name
  let some nineBytes := Wire.encodePackage nineCalls | return note r "LC6 NineCalls has no bytes" false
  let (rc6, vc6, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install nineBytes))
  r := note rc6 s!"LC6 install a method with {Kernel.Bounds.callsMax + 1} call slots: {vc6}"
    (vc6.startsWith "refused program" && (vc6.splitOn "badMethod go").length > 1)
  -- LC7 (LANG-77) a slot whose invoke carries a function: not a call slot, refused by name at install
  let some fnBytes := Wire.encodePackage fnCalls | return note r "LC7 FnCalls has no bytes" false
  let (rc7, vc7, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install fnBytes))
  r := note rc7 s!"LC7 install a method whose invoke slot carries an argument of type (fn nat nat): {vc7}"
    (vc7.startsWith "refused program" && (vc7.splitOn "badMethod go").length > 1)
  -- LC8 (LANG-77) a relay composes `{n}` for a Sink that takes `{n, note}`: the Sink's run refuses the
  -- bytes at ITS argument type, by name, and the whole tree with it
  let some sinkBytes := Wire.encodePackage sink | return note r "LC8 Sink has no bytes" false
  let (rc8a, vc8a, tc8a) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install sinkBytes))
  r := note rc8a s!"LC8a install Sink (go \{n nat, note bytes}): {vc8a}" (vc8a == "admitted")
  let some sid := tc8a.bind fun t => (createdIds t).head? | return note r "LC8 no Sink id" false
  let (rc8b, vc8b, tc8b) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, sid])
    (.create (some sid) [] []))
  r := note rc8b s!"LC8b A creates a Sink: {vc8b}" (vc8b == "admitted")
  let some so := tc8b.bind fun t => (createdIds t).head? | return note r "LC8 no Sink object" false
  let some toSink := nextSlot (some (Sim.dc.bytes so)) | return note r "LC8 no next bytes" false
  let (rc8c, vc8c, tc8c) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid])
    (.create (some rid) [] (seed toSink)))
  r := note rc8c s!"LC8c A creates a Relay whose next is the Sink: {vc8c}" (vc8c == "admitted")
  let some oS := tc8c.bind fun t => (createdIds t).head? | return note r "LC8 no relay object" false
  let (rc8d, vc8d, tc8d) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, so, oS])
    (.grant so oS [.invoke relayGoIx] none))
  let some gS := tc8d.bind fun t => (createdIds t).head? | return note rc8d s!"LC8d grant: {vc8d}" false
  let some vaS := armArgs (Sim.dc.bytes gS) | return note r "LC8 no arm arguments" false
  let (rc8e, vc8e, _) := go prog rc8d (Sim.signed rc8d.st a a.key (Sim.S.pinsFor rc8d.st.host [a.id, rid, oS])
    (.invoke oS relayArmIx vaS 10000 none))
  r := note rc8e s!"LC8d A grants the relay invoke go on the Sink ({vc8d}) and arms it ({vc8e})"
    (vc8d == "admitted" && vc8e == "admitted")
  let (rc8, vc8, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, rid, sid, oS, so, gS])
    (.invoke oS relayGoIx args0 10000 none))
  if mode = .dropCalls then
    r := note { rc8 with log := r.log, bad := r.bad }
      s!"PLANT drop-calls: LC8 the relay's call never reaches the Sink, so the tree must now be admitted: {vc8}" (vc8 == "admitted")
  else
    r := note { rc8 with log := r.log, bad := r.bad }
      s!"LC8 A invokes the relay, which composes \{n 1} for the Sink's \{n, note}: {vc8}; the relay's hits {hitsOf Sim.env r.st.host oS} (the tree failed whole)"
      (vc8.startsWith "refused program" && (vc8.splitOn "arguments:").length > 1 &&
        hitsOf Sim.env r.st.host oS == some 0)
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
(package (imports) (doc)
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


/-! ### LH: a hole with retained candidates and withdrawable facts (ACTIVITIES-DESIGN-20261022 section 9)

A hole whose SHAPE is fixed now (chooser, acceptor, cap, closes) and whose FILLING arrives later as a candidate,
retained with the reason it was set aside. A candidate records the FACTS it was verified under: rows other members
post on this object (assumption tokens, `(cell, pin)` as the poster saw it). A `select` point-reads the candidate
and its facts: a fact re-pinned or withdrawn by its poster refuses the select BY NAME (`support0 moved` /
`support0 withdrawn`), and the kernel's `stale` stands behind it for a view that no longer holds (the plant that
removes the method's pin check turns LH7 admitted; a select over a view that moved, LH7b, is `rejected stale` before the
method runs, KERNEL-66). The demonstration of the
`Lang/Contextual` closure theory; the text is the `.ob` a resident would write. -/

def hole_supportTy : Ty := .record [("cell", .digest), ("pin", .digest)]
def hole_optSupport : Ty := optTy hole_supportTy

def hole_supportData (cell pin : ByteArray) : Data :=
  .inj "some" (.record [("cell", .digest cell), ("pin", .digest pin)])
def hole_noSupport : Data := .inj "none" (.record [])

def hole_postArgTy : Ty := .record [("cell", .digest), ("pin", .digest)]
def hole_postArg (cell pin : ByteArray) : ByteArray :=
  argBytes hole_postArgTy (.record [("cell", .digest cell), ("pin", .digest pin)])
def hole_unpostArg (cell : ByteArray) : ByteArray := argBytes (.record [("cell", .digest)]) (.record [("cell", .digest cell)])

def hole_proposeArgTy : Ty := .record [("cand", .digest), ("s0", hole_optSupport), ("s1", hole_optSupport), ("value", .nat)]
def hole_proposeArg (cand : ByteArray) (s0 s1 : Data) (value : Nat) : ByteArray :=
  argBytes hole_proposeArgTy (.record [("cand", .digest cand), ("s0", s0), ("s1", s1), ("value", .nat value)])

def hole_selectArg (cand : ByteArray) : ByteArray := argBytes (.record [("cand", .digest)]) (.record [("cand", .digest cand)])
def hole_pruneArg (cand cell pin : ByteArray) (why : String) : ByteArray :=
  argBytes (.record [("blocker", Std.holeSupport), ("cand", .digest), ("why", .bytes)])
    (.record [("blocker", .record [("cell", .digest cell), ("pin", .digest pin)]),
      ("cand", .digest cand), ("why", .bytes why.toUTF8)])

/-- A row of relation `rel` of `obj` at `key`, pinned at what the signer sees on `w` (the LB rows' `pinAtObj`). -/
def hole_pinAt (obj : D) (w : World D) (rel : Nat) (d : RelDecl) (key : Data) : List (RowSlot D × D) :=
  match keyBytes d key with
  | some k => let s : RowSlot D := .row ⟨obj, rel, k⟩; [(s, rowPin Sim.env (headFloor Sim.env w.rows obj rel) (rowAt Sim.env w.rows s))]
  | none => []

/-- The status label of a candidate's row, read back. -/
def hole_statusOf (w : World D) (obj : D) (dC : RelDecl) (cand : ByteArray) : Option String :=
  match (storyRow w obj 0 dC (.record [("cand", .digest cand)])).bind (·.field "status") with
  | some (.inj l (.bytes b)) => some s!"{l} \"{String.fromUTF8! b}\""
  | some (.inj l _) => some l
  | _ => none

def hole_selectedOf (E : Kernel.Env D) (w : World D) (obj : D) : Option (Option ByteArray) :=
  match slotOf E w obj 5 |>.map (Wire.decodeData (optTy .digest)) with
  | some (.ok (.inj "some" (.digest b))) => some (some b)
  | some (.ok (.inj "none" _)) => some none
  | _ => none

def hole_acceptedOf (E : Kernel.Env D) (w : World D) (obj : D) : Option Bool :=
  match slotOf E w obj 0 |>.map (Wire.decodeData .bool) with
  | some (.ok (.bool b)) => some b
  | _ => none

/-- The one-use amount is contextual ROM code, selected from a pinned row on
every commitment. Both provider representations consume the supplied unit. -/
def p8ContextBundle : Except String Std.HoleBundle :=
  Std.contextualHole .nat
    { name := 0, ctx := [.nat], ty := .nat,
      code := [⟨.var 0, []⟩, ⟨.var 0, []⟩], selectionRel := 0, selectionKey := .empty,
      hypotheses := [none], guardPin := none, guard := .var 0 }
    [.var 1] (.lam Std.holeState (.lam .nat
      (.prim .le (.var 0) (.get (.var 1) "cap"))))

/-- The methods of a package that read relation `rel`, each with whether it reads it LIVE (E1): the
generator-level tooth of C1 (READ-E1-grok's residual). B1–B3 hold for packages whose fact reads are
live reads; a Std.hole whose generator emitted a facts read without `live` would treat a pin match
as current again, so the generated package is checked, not assumed. -/
def readsOfRel (p : Package) (rel : Label) : List (Label × Bool) :=
  p.methods.filterMap fun ℓ =>
    match Row.find? ℓ (recordRow p.iface) with
    | some t => match methodSig p.state p.rels t with
      | some sg => (sg.reads.lookup rel).map fun x => (ℓ, x.live)
      | none => none
    | none => none

def holeRows (mode : Mode) (r0 : Run) (a b : Sim.Member) (contextual : Bool := false) : Run := Id.run do
  let prog := mode.program
  let mut r := r0
  for (name, want, got) in Std.holeCheckRows do
    r := note r s!"LH-prefix {name}: {got}" (got == want)
  let bundle ← match (if contextual then p8ContextBundle else Std.generatedHoleBundle.mapError (·.name)) with
    | .ok b => pure b
    | .error e => return note r s!"LH0 generating the hole: {e}" false
  let mut libraryIds : List D := []
  for lib in bundle.libraries do
    let some bytes := Wire.encodePackage lib | return note r "LH0 library has no bytes" false
    let (rL, vL, tL) := go prog r (Sim.signed r.st a a.key
      (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rL s!"LH0 installing helper ROM ({bytes.size} bytes): {vL}"
      (vL == "admitted" && bytes.size ≤ Lang.Bounds.bytesMax)
    let some id := tL.bind fun t => (createdIds t).head? | return note r "LH0 no helper ROM id" false
    libraryIds := libraryIds ++ [id]
  let generated ← match (if contextual then bundle.linkContextual (libraryIds.map Sim.dc.bytes)
      else (bundle.link (libraryIds.map Sim.dc.bytes)).mapError (·.name)) with
    | .ok p => pure p
    | .error e => return note r s!"LH0 linking the hole: {e}" false
  let some src := Print.package generated | return note r "LH0 hole is not printable" false
  let p ← match Surface.readPackage src with
    | .ok p => pure p
    | .error e => return note r s!"LH0 read the generated hole: {e.text src}" false
  r := note r s!"LH0 generated hole reads ({src.length} chars): methods {p.methods}, laws {p.laws}, relations {p.rels.map (·.1)}"
    (p.methods == (["accept", "fill", "post", "propose", "prune", "rejudge", "repin", "resume_fill", "retire", "select", "unpost"] ++
      if contextual then ["choose_code", "execute"] else []).mergeSort &&
      p.laws == ["shape"] && p.rels.map (·.1) == (["candidates", "facts", "fills", "pending"] ++
      if contextual then ["computed", "selection"] else []).mergeSort &&
      p.holes.isEmpty == !contextual)
  let fr := readsOfRel p "facts"
  r := note r s!"LH0f every generated method reading facts reads it live: {fr}"
    (!fr.isEmpty && fr.all (·.2))
  let factsIndex := (p.rels.map (·.1)).idxOf "facts"
  let fillsIndex := (p.rels.map (·.1)).idxOf "fills"
  let pendingIndex := (p.rels.map (·.1)).idxOf "pending"
  let some pb := Wire.encodePackage p | return note r "LH0 no bytes" false
  let some dC := p.rels.lookup "candidates" | return note r "LH0 no candidates" false
  let some dF := p.rels.lookup "facts" | return note r "LH0 no facts" false
  -- LH1 install
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host (a.id :: libraryIds)) (.install pb))
  r := note r1 s!"LH1 A installs the hole ({pb.size} package bytes): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return note r "LH1 no package id" false
  -- LH2 create: cap 10, chooser A, acceptor B, closes far off, nothing selected
  let seedData : List (Label × Data) :=
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes b.id)), ("cap", .nat 10),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000), ("selected", .inj "none" (.record []))]
  let some seed := stateSlots (recordRow p.state) seedData 0 | return note r "LH2 seed has no bytes" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ libraryIds)) (.create (some pkg) [] seed))
  let some obj := t2.bind fun t => (createdIds t).head? | return note r2 s!"LH2 no hole: {v2}" false
  r := note r2 s!"LH2 A creates the hole (cap 10, chooser A, acceptor B): {v2}; all {p.rels.length} relations born empty"
    (v2 == "admitted" && (List.range p.rels.length).all fun i => headCount r2.st.host obj i == some 0)
  -- LH3 A grants B accept (0), post (1), repin (4), unpost (6)
  let (r3, v3, t3) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, b.id, obj])
    (.grant obj b.id [.invoke (p.methods.idxOf "accept"), .invoke (p.methods.idxOf "post"), .invoke (p.methods.idxOf "repin"), .invoke (p.methods.idxOf "unpost"), .invoke (p.methods.idxOf "resume_fill")] none))
  r := note r3 s!"LH3 A grants B accept, post, repin, unpost: {v3}" (v3 == "admitted")
  let some gr := t3.bind fun t => (createdIds t).head? | return note r "LH3 no grant id" false
  -- the facts' cells (f1 = a, f2 = b) are pinned: a fact read is a live read of its cell (E1)
  let pinsOf (r : Run) (m : Sim.Member) := Sim.S.pinsFor r.st.host ([m.id, a.id, b.id, obj, pkg] ++ libraryIds ++ if m.id == b.id then [gr] else [])
  let viaOf (m : Sim.Member) : Option D := if m.id == b.id then some gr else none
  let call (r : Run) (m : Sim.Member) (method : Label) (x : ByteArray) (rowPins : List (RowSlot D × D) := []) : Call D :=
    signedAt r.st m (pinsOf r m) (.invoke obj (p.methods.idxOf method) x 100000 (viaOf m)) r.st.host.height (r.st.host.height + 1024) rowPins
  let cost (c : Call D) (w : World D) : String :=
    s!"required steps / ticks {match measure w c with | .ok (q, k) => s!"{q} / {k}" | .error e => e}"
  -- the two facts: cells f1, f2 (any Sim digests), pins p1, p2
  let f1 := Sim.dc.bytes a.id
  let f2 := Sim.dc.bytes b.id
  let p1 := Sim.dc.bytes pkg
  let p2 := Sim.dc.bytes obj
  let p1' := Sim.dc.bytes gr
  let factKey (cell : ByteArray) : Data := .record [("cell", .digest cell)]
  let candKey (cand : ByteArray) : Data := .record [("cand", .digest cand)]
  let pinFact (w : World D) (cell : ByteArray) := hole_pinAt obj w factsIndex dF (factKey cell)
  let pinCand (w : World D) (cand : ByteArray) := hole_pinAt obj w 0 dC (candKey cand)
  let factPin (w : World D) (cell : ByteArray) : Option ByteArray :=
    match (storyRow w obj factsIndex dF (factKey cell)).bind (·.field "pin") with
    | some (.digest d) => some d
    | _ => none
  -- LH4 B posts f1@p1 and f2@p2
  let (r4a, v4a, _) := go prog r (call r b "post" (hole_postArg f1 p1))
  r := note r4a s!"LH4a B posts fact f1 at pin p1: {v4a}" (v4a == "admitted" && factPin r4a.st.host f1 == some p1)
  let (r4b, v4b, _) := go prog r (call r b "post" (hole_postArg f2 p2))
  r := note r4b s!"LH4b B posts fact f2 at pin p2: {v4b}" (v4b == "admitted" && headCount r4b.st.host obj factsIndex == some 2)
  let (_, v4c, _) := go prog r (call r a "post" (hole_postArg f1 p1))
  r := note r s!"LH4c A posts f1 again (B's token): {v4c}" (v4c.startsWith "rejected keyTaken")
  -- LH5 candidates: c1 over f1@p1, f2@p2; c2 over f2@p2; c3 past the cap
  let c1 := Sim.dc.bytes (founderId (ctxWith prog) r.st.host.origin 7)
  let c2 := Sim.dc.bytes (founderId (ctxWith prog) r.st.host.origin 8)
  let c3 := Sim.dc.bytes (founderId (ctxWith prog) r.st.host.origin 9)
  let (r5a, v5a, _) := go prog r (call r a "propose" (hole_proposeArg c1 (hole_supportData f1 p1) (hole_supportData f2 p2) 5) (pinFact r.st.host f1 ++ pinFact r.st.host f2))
  r := note r5a s!"LH5a A proposes c1 (value 5, facts f1@p1 f2@p2): {v5a}; status {hole_statusOf r5a.st.host obj dC c1}"
    (v5a == "admitted" && hole_statusOf r5a.st.host obj dC c1 == some "verified")
  let (r5b, v5b, _) := go prog r (call r a "propose" (hole_proposeArg c2 (hole_supportData f2 p2) hole_noSupport 7) (pinFact r.st.host f2))
  r := note r5b s!"LH5b A proposes c2 (value 7, fact f2@p2): {v5b}; status {hole_statusOf r5b.st.host obj dC c2}"
    (v5b == "admitted" && hole_statusOf r5b.st.host obj dC c2 == some "verified")
  let (r5c, v5c, _) := go prog r (call r a "propose" (hole_proposeArg c3 hole_noSupport hole_noSupport 50))
  r := note r5c s!"LH5c A proposes c3 (value 50, past the cap): {v5c}; retained with its reason: {hole_statusOf r5c.st.host obj dC c3}"
    (v5c == "admitted" && hole_statusOf r5c.st.host obj dC c3 == some "conflict \"clause\"")
  -- LH5d a candidate filed verified past the cap: the guard refuses it (the status is the clause's, not the author's)
  let (_, v5d, _) := go prog r (call r a "propose" (hole_proposeArg c3 hole_noSupport hole_noSupport 50))
  r := note r s!"LH5d A proposes c3 again (its key is taken): {v5d}" (v5d.startsWith "rejected keyTaken")
  let c4 := Sim.dc.bytes (founderId (ctxWith prog) r.st.host.origin 10)
  let (rf, vf, _) := go prog r (call r a "fill"
    (hole_proposeArg c4 (hole_supportData f1 p1) hole_noSupport 4) (pinFact r.st.host f1))
  r := note r s!"LH5f (scratch) fill a supported candidate atomically: {vf}"
    (vf == "admitted" && hole_selectedOf Sim.env rf.st.host obj == some (some c4) &&
      hole_statusOf rf.st.host obj dC c4 == some "verified")
  let (rx, vx, _) := go prog r (call r a "fill" (hole_proposeArg c4 hole_noSupport hole_noSupport 50))
  r := note r s!"LH5g fill a clause-conflicting candidate: {vx}"
    (refusedBy vx "fill" "conflict" && hole_statusOf rx.st.host obj dC c4 == none)
  let (_, vs, _) := go prog r (call r a "select" (hole_selectArg c3) (pinCand r.st.host c3))
  r := note r s!"LH5h select a clause-conflicting candidate: {vs}" (refusedBy vs "select" "conflict")
  let (rj, vj, _) := go prog r (call r a "rejudge" (hole_selectArg c3) (pinCand r.st.host c3))
  r := note r s!"LH5j rejudge records conflict: {vj}"
    (vj == "admitted" && hole_statusOf rj.st.host obj dC c3 == some "conflict \"clause\"")
  -- LH6 the view before the withdrawal, kept for LH7b; then B re-pins f1
  let viewBefore := r
  let (r6, v6, _) := go prog r (call r b "repin" (hole_postArg f1 p1') (pinFact r.st.host f1))
  r := note r6 s!"LH6 B re-pins fact f1 (p1 -> p1'): {v6}; the support c1 recorded has MOVED"
    (v6 == "admitted" && factPin r6.st.host f1 == some p1')
  -- LH7 A selects c1: its support f1 is not what it was verified under
  let c7 := call r a "select" (hole_selectArg c1) (pinCand r.st.host c1 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2)
  let (_, v7, _) := go prog r c7
  r := note r s!"LH7 A selects c1: {v7}; {cost c7 r.st.host}" (refusedBy v7 "select" "support0 moved")
  let (rf, vf, _) := go prog r (call r a "fill"
    (hole_proposeArg c4 (hole_supportData f1 p1) hole_noSupport 4) (pinFact r.st.host f1))
  r := note r s!"LH7f fill over a moved support: {vf}"
    (refusedBy vf "fill" "support0 moved" && hole_statusOf rf.st.host obj dC c4 == none)
  let (rj, vj, _) := go prog r (call r a "rejudge" (hole_selectArg c1)
    (pinCand r.st.host c1 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2))
  r := note r s!"LH7j rejudge records suspension: {vj}"
    (vj == "admitted" && hole_statusOf rj.st.host obj dC c1 == some "suspended \"support0 moved\"")
  -- LH7b the same select signed over the view before LH6 (the row pins of that view)
  let c7b := call viewBefore a "select" (hole_selectArg c1)
    (pinCand viewBefore.st.host c1 ++ pinFact viewBefore.st.host f1 ++ pinFact viewBefore.st.host f2)
  let (_, v7b, _) := go prog r c7b
  -- KERNEL-66: the view's row pins moved, so the kernel declines the call `stale` before the method
  -- runs; LH7 is the method's own `support0 moved`, on a current view
  r := note r s!"LH7b the same select signed over the view before the re-pin: {v7b} (the view moved: the kernel declines it stale before the method runs, KERNEL-66)"
    (v7b == "rejected stale")
  -- LH7c a select citing a candidate whose fact row is pinned absent (f1 unposted on a scratch World)
  let (rX, vX, _) := go prog r (call r b "unpost" (hole_unpostArg f1) (pinFact r.st.host f1))
  let cX := call rX a "select" (hole_selectArg c1) (pinCand rX.st.host c1 ++ pinFact rX.st.host f1 ++ pinFact rX.st.host f2)
  let (_, vX2, _) := go prog rX cX
  r := note r s!"LH7c (scratch) B withdraws f1 ({vX}); A selects c1: {vX2}" (vX == "admitted" && refusedBy vX2 "select" "support0 withdrawn")
  -- LH7u/LH7v (A11, LANG-79): the same candidate with its support's pin OMITTED is refused
  -- `unpinned support0` by name, not as the observed absence of LH7c (`support0 withdrawn`); on
  -- rejudge the omission would otherwise be recorded as a suspension of a fact that stands
  let (_, vU, _) := go prog r (call r a "select" (hole_selectArg c2) (pinCand r.st.host c2))
  r := note r s!"LH7u A selects c2 with its support f2's pin omitted: {vU}" (refusedBy vU "select" "unpinned support0")
  let (_, vUJ, _) := go prog r (call r a "rejudge" (hole_selectArg c2) (pinCand r.st.host c2))
  r := note r s!"LH7v A rejudges c2 with its support f2's pin omitted: {vUJ}" (refusedBy vUJ "rejudge" "unpinned support0")
  -- LH8 A selects c2: its one support f2@p2 still stands
  let c8 := call r a "select" (hole_selectArg c2) (pinCand r.st.host c2 ++ pinFact r.st.host f2)
  let (r8, v8, _) := go prog r c8
  r := note r8 s!"LH8 A selects c2 (fact f2@p2 unchanged): {v8}; selected {hole_selectedOf Sim.env r8.st.host obj |>.map (·.map Print.hex)}; {cost c8 r.st.host}"
    (v8 == "admitted" && hole_selectedOf Sim.env r8.st.host obj == some (some c2))
  -- LH8b B (not the chooser) selects
  let (_, v8b, _) := go prog r (call r b "select" (hole_selectArg c2) (pinCand r.st.host c2 ++ pinFact r.st.host f2))
  r := note r s!"LH8b B selects c2: {v8b}" (v8b.startsWith "refused grantRight" || refusedBy v8b "select" "notChooser")
  -- LH8p: a pruning reason is a live posted token; withdrawing it releases the branch.
  let (rP, vP, _) := go prog r (call r a "prune" (hole_pruneArg c2 f1 p1' "policy")
    (pinCand r.st.host c2 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2))
  r := note rP s!"LH8p A prunes c2 by posted f1: {vP}"
    (vP == "admitted" && hole_statusOf rP.st.host obj dC c2 == some "pruned \"policy\"")
  let (_, vPS, _) := go prog r (call r a "select" (hole_selectArg c2)
    (pinCand r.st.host c2 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2))
  r := note r s!"LH8q selecting the live-blocked candidate: {vPS}" (refusedBy vPS "select" "pruned")
  let (_, omittedBlocker, _) := go prog r (call r a "select" (hole_selectArg c2)
    (pinCand r.st.host c2 ++ pinFact r.st.host f2))
  r := note r s!"hole:omitted-blocker-pin-admits live blocker fact omitted from select pins: {omittedBlocker}"
    (refusedBy omittedBlocker "select" "unpinned blocker")
  let (_, omittedAccept, _) := go prog r (call r b "accept" (argBytes (.record []) (.record []))
    (pinCand r.st.host c2 ++ pinFact r.st.host f2))
  r := note r s!"hole:omitted-blocker-pin-admits live blocker fact omitted from accept pins: {omittedAccept}"
    (refusedBy omittedAccept "accept" "unpinned blocker")
  let (omittedRJ, omittedRejudge, _) := go prog r (call r a "rejudge" (hole_selectArg c2)
    (pinCand r.st.host c2 ++ pinFact r.st.host f2))
  r := note r s!"hole:omitted-blocker-pin-admits live blocker fact omitted from rejudge pins: {omittedRejudge}; status {hole_statusOf omittedRJ.st.host obj dC c2}"
    (refusedBy omittedRejudge "rejudge" "unpinned blocker")
  let (rW, vW, _) := go prog r (call r b "unpost" (hole_unpostArg f1) (pinFact r.st.host f1))
  r := note rW s!"LH8r B withdraws the pruning token: {vW}" (vW == "admitted")
  let (rJ, vJ, _) := go prog r (call r a "rejudge" (hole_selectArg c2)
    (pinCand r.st.host c2 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2))
  let reason := (storyRow rJ.st.host obj 0 dC (candKey c2)).bind (·.field "reason")
  r := note rJ s!"LH8s rejudge releases c2 and retains its reason: {vJ}; {hole_statusOf rJ.st.host obj dC c2}"
    (vJ == "admitted" && hole_statusOf rJ.st.host obj dC c2 == some "verified" &&
      asBytes reason == some "policy".toUTF8)
  -- LH14 (C1, LANG-75.1, cv 01a1649d) on a scratch branch: a fact is the poster's claim; every reader
  -- checks the cell it names. A cell the kernel never had: unpinned, the read refuses by name; pinned
  -- (at its absence), the candidate is recorded suspended and its selection refuses by name.
  let ghost : D := 0x5eed5eed5eed5eed
  let fG := Sim.dc.bytes ghost
  let c14 := Sim.dc.bytes (founderId (ctxWith prog) r.st.host.origin 14)
  let (rG, vG, _) := go prog r (call r a "post" (hole_postArg fG p1))
  let withGhost (r : Run) (method : Label) (x : ByteArray) (rowPins : List (RowSlot D × D)) : Call D :=
    signedAt r.st a (pinsOf r a ++ Sim.S.pinsFor r.st.host [ghost]) (.invoke obj (p.methods.idxOf method) x 100000 none)
      r.st.host.height (r.st.host.height + 1024) rowPins
  let proposeG := hole_proposeArg c14 (hole_supportData fG p1) hole_noSupport 3
  let (_, vU, _) := go prog rG (call rG a "propose" proposeG (pinFact rG.st.host fG))
  let (rP, vP, _) := go prog rG (withGhost rG "propose" proposeG (pinFact rG.st.host fG))
  let (_, vS, _) := go prog rP (withGhost rP "select" (hole_selectArg c14) (pinCand rP.st.host c14 ++ pinFact rP.st.host fG))
  r := note r s!"LH14a support of a digest the kernel never had, its cell unpinned: post {vG}; propose {vU}"
    (vG == "admitted" && (r.st.host.entry Sim.env ghost).isNone && vU.startsWith "refused unpinned")
  r := note r s!"LH14b support of a digest the kernel never had, its cell pinned absent: propose {vP}, recorded {hole_statusOf rP.st.host obj dC c14}; select {vS}"
    (vP == "admitted" && hole_statusOf rP.st.host obj dC c14 == some "suspended \"support0 dead\"" &&
      refusedBy vS "select" "support0 dead")
  -- LH9 B accepts; LH9b a select after acceptance
  let dispatchAt := r.st.host.height
  let (r9, v9, _) := go prog r (call r b "accept" (argBytes (.record []) (.record [])) (pinCand r.st.host c2 ++ pinFact r.st.host f1 ++ pinFact r.st.host f2))
  r := note r9 s!"LH9 B accepts the selected c2: {v9}; accepted {hole_acceptedOf Sim.env r9.st.host obj}"
    (v9 == "admitted" && hole_acceptedOf Sim.env r9.st.host obj == some true)
  let (_, v9b, _) := go prog r (call r a "select" (hole_selectArg c2) (pinCand r.st.host c2 ++ pinFact r.st.host f2))
  r := note r s!"LH9b A selects again after acceptance: {v9b}" (refusedBy v9b "select" "accepted")
  -- LH10 B withdraws f2 after acceptance: the executed prefix does not move
  let (r10, v10, _) := go prog r (call r b "unpost" (hole_unpostArg f2) (pinFact r.st.host f2))
  r := note r10 s!"LH10 B withdraws f2 after acceptance: {v10}; selected stays c2: {hole_selectedOf Sim.env r10.st.host obj == some (some c2)}; accepted: {hole_acceptedOf Sim.env r10.st.host obj}"
    (v10 == "admitted" && hole_selectedOf Sim.env r10.st.host obj == some (some c2) && hole_acceptedOf Sim.env r10.st.host obj == some true)
  -- LH11 accepted history also prevents pruning; the retained rows are unchanged
  let (r11, v11, _) := go prog r (call r a "prune" (hole_pruneArg c1 f1 p1' "support moved") (pinCand r.st.host c1))
  r := note r11 s!"LH11 A prunes c1: {v11}; candidates: c1 {hole_statusOf r11.st.host obj dC c1}, c2 {hole_statusOf r11.st.host obj dC c2}, c3 {hole_statusOf r11.st.host obj dC c3}"
    (refusedBy v11 "prune" "accepted" && hole_statusOf r11.st.host obj dC c1 == some "verified" &&
      hole_statusOf r11.st.host obj dC c2 == some "verified" && headCount r11.st.host obj 0 == some 3)
  -- LH11b B prunes (not the chooser): the guard refuses it
  let (_, v11b, _) := go prog r (call r b "prune" (hole_pruneArg c2 f1 p1' "mine") (pinCand r.st.host c2))
  r := note r s!"LH11b B prunes c2: {v11b}" (v11b.startsWith "refused grantRight" || refusedBy v11b "prune" "notChooser")
  let some dLog := p.rels.lookup "fills" | return note r "LH12 no activity log" false
  let some dPending := p.rels.lookup "pending" | return note r "LH12 no activity cursor" false
  let dispatchKey := Data.record [("agent", .digest (Sim.dc.bytes b.id)), ("notBefore", .nat dispatchAt)]
  let captured := match (storyRow r.st.host obj fillsIndex dLog dispatchKey).bind (·.field "captured") with
    | some (.inj "fill" (.nat 7)) => true | _ => false
  r := note r "LH12 acceptance dispatched captured value 7; withdrawal did not rewrite it"
    (captured && headCount r.st.host obj fillsIndex == some 1 && headCount r.st.host obj pendingIndex == some 1)
  let dispatchPins (w : World D) := hole_pinAt obj w fillsIndex dLog dispatchKey ++ hole_pinAt obj w pendingIndex dPending dispatchKey
  let resumeArg := argBytes (.record [("agent", .digest), ("notBefore", .nat), ("response", .record [])])
    (.record [("agent", .digest (Sim.dc.bytes b.id)), ("notBefore", .nat dispatchAt), ("response", .record [])])
  let (r12, v12, _) := go prog r (call r b "resume_fill" resumeArg (dispatchPins r.st.host))
  let answered := match (storyRow r12.st.host obj fillsIndex dLog dispatchKey).bind (·.field "answered") with
    | some (.inj "some" (.inj "fill" (.record []))) => true | _ => false
  r := note r12 s!"LH12b acceptor acknowledges the dispatched filling: {v12}"
    (v12 == "admitted" && answered && headCount r12.st.host obj pendingIndex == some 0)
  let (_, v12r, _) := go prog r (call r b "resume_fill" resumeArg (dispatchPins r.st.host))
  r := note r s!"LH12c the dispatch cannot be acknowledged twice: {v12r}"
    (deniedWith v12r "fills_waiting: answered")
  let retireArg := argBytes (keyTy dLog) dispatchKey
  let (r13, v13, _) := go prog r (call r a "retire" retireArg (hole_pinAt obj r.st.host fillsIndex dLog dispatchKey))
  r := note r13 s!"LH13 retire the answered dispatch: {v13}"
    (v13 == "admitted" && headCount r13.st.host obj fillsIndex == some 0 &&
      hole_acceptedOf Sim.env r13.st.host obj == some true)
  return r


/-! P8: one Store, one writer, one atomic turn across the hole and value cells.
The checked commitment re-executes the selected method; it never resumes a saved
effectful continuation. The grant is the kernel's counted Right.transfer 1.
Toy cryptographic parameters are those of the rest of this journey. -/

/-- Compose the generated checked select with one atomic transfer. The selected
row edit and accepted state remain in the same ordinary method result. -/
def p8CommitPackage (p : Package) : Except String Package := do
  let .record ts := p.iface | throw "P8 interface"
  let .record fs := p.body | throw "P8 root"
  let some select := Row.find? "select" fs | throw "P8 select"
  let some (.fn R (.fn _ (.fn _ (.fn _ SR)))) := Row.find? "select" ts | throw "P8 select type"
  let A := Ty.record [("asset", .digest), ("cand", .digest), ("grant", .digest)]
  let C := callOf ["transfer"]
  let RT := resultTy p.state [C] (editTy p.rels) 1
  let arg (l : Label) := Term.get (.var 2) l
  let transfer := Term.inj C "transfer" (.record [
    ("amount", .hole 0 [.nat 1]),
    ("dst", .inj acctRefTy "of" (.record [("asset", arg "asset"), ("owner", arg "cand")])),
    ("once", .inj (optTy .bytes) "none" (.record [])),
    ("src", .inj acctRefTy "well" (arg "asset")),
    ("via", .inj (optTy .digest) "some" (arg "grant"))])
  let finish := resultT (callsT [someCallT C transfer])
    (.extend (.get (.var 0) "state") [("accepted", .bool true)])
    (.get (.var 0) "edits")
  let selected := Std.activityApply select [.var 3, .var 2,
    .record [("cand", .get (.var 1) "cand")], .var 0]
  let body := Term.lam R (.lam p.state (.lam A (.lam reqTy
    (.ite (.prim .le (.get (.var 0) "validUntil") (.get (.var 2) "closes"))
      (.app (.lam SR finish) selected) (.refuse RT "closed".toUTF8)))))
  return { p with
    iface := .record (Row.sort (ts ++ [("commit", methodTy p.state A [C] R (editTy p.rels) 1)])),
    body := .record (Row.sort (fs ++ [("commit", body)])),
    methods := (Row.sort ((p.methods ++ ["commit"]).map (·, ()))).map (·.1) }

/-- Core source for the generated root plus atomic commitment. Placeholder
library identities are linked to actual installed helpers by p8Rows. -/
def p8Text : String :=
  match p8ContextBundle with
  | .error _ => ""
  | .ok b => match p8CommitPackage { b.layout with
        imports := b.libraries.map fun _ => ByteArray.mk (Array.replicate 32 (0 : UInt8)) } with
    | .error _ => ""
    | .ok p => (Print.package p).getD ""

/-- Each provider authority's state in the live kernel view, at the version its support recorded:
live, and pinned at that version. A tombstoned grant or a changed pin reads false. -/
def p8Live (w : World D) (supports : List (D × D)) : List Bool :=
  supports.map fun (g, pin) => (w.live Sim.env g).isSome && (pinOf Sim.env (w.entry Sim.env g) == pin)

def p8Arg (asset cand grant : D) : ByteArray :=
  argBytes (.record [("asset", .digest), ("cand", .digest), ("grant", .digest)])
    (.record [("asset", .digest (Sim.dc.bytes asset)), ("cand", .digest (Sim.dc.bytes cand)),
      ("grant", .digest (Sim.dc.bytes grant))])

/-- Read the REAL grant ledger, not an auxiliary spent flag. -/
def p8Left (w : World D) (g : D) : Option Nat :=
  (w.live Sim.env g).bind fun c => match ledgerLeft transferBase g c with
    | .ok (_, n) => some n
    | .error _ => none

def p8Rows (r0 : Run) (a b : Sim.Member) (src : String := p8Text) : Run := Id.run do
  let mut r := r0
  let prog := langProgram
  let X := ctxWith prog
  let p ← match Surface.readPackage src with
    | .ok p => pure p
    | .error e => return note r s!"P8 read: {e.text src}" false
  let bundle ← match p8ContextBundle with
    | .error e => return note r s!"P8 generate helpers: {e}" false
    | .ok b => pure b
  let mut libraryIds : List D := []
  for lib in bundle.libraries do
    let some bytes := Wire.encodePackage lib | return note r "P8 helper bytes" false
    let (rL, vL, tL) := go prog r (Sim.signed r.st a a.key
      (Sim.S.pinsFor r.st.host [a.id]) (.install bytes))
    r := note rL s!"P8 install checked helper ({bytes.size} bytes): {vL}"
      (vL == "admitted" && bytes.size ≤ Lang.Bounds.bytesMax)
    let some id := tL.bind fun t => (createdIds t).head? | return note r "P8 helper id" false
    libraryIds := libraryIds ++ [id]
  let p := { p with imports := libraryIds.map Sim.dc.bytes }
  let some pb := Wire.encodePackage p | return note r "P8 no package bytes" false
  let fr := readsOfRel p "facts"
  r := note r s!"P8 every method reading facts reads it live: {fr}" (!fr.isEmpty && fr.all (·.2))
  let some dc := p.rels.lookup "candidates" | return note r "P8 no candidates" false
  let some df := p.rels.lookup "facts" | return note r "P8 no facts" false
  let (r1, v1, t1) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host (a.id :: libraryIds)) (.install pb))
  r := note r1 s!"P8 install checked open artifact ({pb.size} bytes): {v1}" (v1 == "admitted")
  let some pkg := t1.bind fun t => (createdIds t).head? | return r
  let some seed := stateSlots (recordRow p.state)
    [("accepted", .bool false), ("acceptor", .digest (Sim.dc.bytes b.id)), ("cap", .nat 1),
     ("chooser", .digest (Sim.dc.bytes a.id)), ("closes", .nat 100000),
     ("selected", .inj "none" (.record []))] 0 | return note r "P8 seed" false
  let (r2, v2, t2) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host ([a.id, pkg] ++ libraryIds))
    (.create (some pkg) [] seed))
  r := note r2 s!"P8 requester cell: {v2}" (v2 == "admitted")
  let some obj := t2.bind fun t => (createdIds t).head? | return r
  let (r3, v3, t3) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id]) (.issue 10))
  r := note r3 s!"P8 B's value cell: {v3}" (v3 == "admitted")
  let some asset := t3.bind fun t => (createdIds t).head? | return r
  for owner in [a.id, b.id] do
    let (r', v, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.account asset owner))
    r := note r' s!"P8 provider account {owner}: {v}" (v == "admitted")
  let (r4, v4, t4) := go prog r (Sim.signed r.st b b.key (Sim.S.pinsFor r.st.host [b.id, asset, obj])
    (.grant asset obj [.transfer 1] none))
  r := note r4 s!"P8 B authorizes requester for ONE unit: {v4}" (v4 == "admitted")
  let some cap := t4.bind fun t => (createdIds t).head? | return r
  -- Two retained provider authorities; each can accept the open artifact.
  let mut providers : List D := []
  for owner in [a.id, b.id] do
    let (r', v, t) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, obj, owner])
      (.grant obj owner [.invoke (p.methods.idxOf "accept")] none))
    r := note r' s!"P8 provider authority {owner}: {v}" (v == "admitted")
    let some g := t.bind fun t => (createdIds t).head? | return r
    providers := providers ++ [g]
  let supports := providers.map fun g => (g, pinOf Sim.env (r.st.host.entry Sim.env g))
  let invoke (r : Run) (m : String) (arg : ByteArray) (rp : List (RowSlot D × D) := [])
      (extra : List (D × D) := []) : Call D :=
    signedAt r.st a (Sim.S.pinsFor r.st.host ([a.id, obj, pkg] ++ libraryIds) ++ extra)
      (.invoke obj (p.methods.idxOf m) arg 100000 none)
      r.st.host.height (r.st.host.height + 1024)
        (rp ++ hole_pinAt obj r.st.host 5 Std.codeSelection (.record [("hole", .nat 0)]))
  let pinF (w : World D) (g : D) := hole_pinAt obj w 2 df (.record [("cell", .digest (Sim.dc.bytes g))])
  let pinC (w : World D) (owner : D) := hole_pinAt obj w 0 dc (.record [("cand", .digest (Sim.dc.bytes owner))])
  for ((g, pin), owner) in supports.zip [a.id, b.id] do
    let (r', v, _) := go prog r (invoke r "post" (hole_postArg (Sim.dc.bytes g) (Sim.dc.bytes pin)))
    r := note r' s!"P8 post versioned provider support: {v}" (v == "admitted")
    let (r', v, _) := go prog r (invoke r "propose"
      (hole_proposeArg (Sim.dc.bytes owner) (hole_supportData (Sim.dc.bytes g) (Sim.dc.bytes pin)) hole_noSupport 1) (pinF r.st.host g)
      (Sim.S.pinsFor r.st.host [g]))
    r := note r' s!"P8 retain candidate {owner}: {v}" (v == "admitted")
  let commit (r : Run) (i : Nat) (owner : D) : Call D :=
    invoke r "commit" (p8Arg asset owner cap)
      (pinC r.st.host owner ++ pinF r.st.host (providers[i]?.getD 0))
      (Sim.S.pinsFor r.st.host [asset, accountId X owner asset, cap] ++ [supports[i]?.getD (0, 0)])
  let chooseCode (r : Run) (i : Nat) :=
    invoke r "choose_code" (argBytes (.record [("hole", .nat), ("index", .nat)])
      (.record [("hole", .nat 0), ("index", .nat i)]))
  let (r', vcode, _) := go prog r (chooseCode r 0)
  r := note r' s!"P8 live contextual amount selected: {vcode}" (vcode == "admitted")
  let ready := r
  let plan := commit r 1 b.id
  -- An unrelated birth changes height and cells, but none of the signed dependencies.
  let (r', vu, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.issue 2))
  r := note r' s!"P8.1 unrelated update: {vu}" (vu == "admitted")
  let (_, usable, _) := go prog r plan
  r := note r s!"P8.1 old signed plan after unrelated update: {usable}" (usable == "admitted")
  -- Withdraw one authority without discarding the conditional protocol or its alternatives.
  let oldPlan := commit r 0 a.id
  let preRevoke := r
  let (r', vr, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id, providers[0]!])
    (.revoke providers[0]!))
  r := note r' s!"P8.2 withdraw provider 0: {vr}" (vr == "admitted")
  let (_, stale, _) := go prog r oldPlan
  -- The plan signed before the revoke pins g0 at its live version, which the revoke moved: the kernel
  -- declines it `stale` before the commit method runs (KERNEL-66; as LH7b for a moved row).
  r := note r s!"P8.2 withdrawn instantiation: {stale}; live authority {p8Live r.st.host supports}"
    (stale.startsWith "rejected stale" &&
      p8Live r.st.host supports == [false, true] && headCount r.st.host obj 0 == some 2)
  -- C1 (LANG-75.1, cv 01a16171): a commit that RE-PINS the withdrawn provider's grant at its
  -- TOMBSTONE passes the kernel's pin check; the commit's live read of the facts sees the cited cell
  -- dead and refuses by name, in the same Turn as the spend. Before C1 it was admitted and spent
  -- the unit (fold/S2-tombstone-probe.txt; promo/E1-support-probe.txt).
  let g0 := providers[0]!
  let (_, vt, _) := go prog r (invoke r "commit" (p8Arg asset a.id cap)
      (pinC r.st.host a.id ++ pinF r.st.host g0)
      (Sim.S.pinsFor r.st.host [asset, accountId X a.id asset, cap, g0]))
  r := note r s!"P8.2 re-pinned tombstone: {vt}; counted left {p8Left r.st.host cap}"
    (refusedBy vt "commit" "support0 dead" && p8Left r.st.host cap == some 1 &&
      (match r.st.host.entry Sim.env g0 with | some .tomb => true | _ => false))
  -- C9 (LANG-75.2): the plan's two-Turn split, recorded. Turn 1 selects candidate 0 while its
  -- provider is live; the provider is revoked; Turn 2 commits. The second Turn reads the cell again
  -- through its own pins and refuses by the E1 path. The boundary: one Turn's pin check and its
  -- derived calls share one pinned view (`receive`); across Turns nothing is shared, so a second
  -- Turn that spent WITHOUT its own live read would admit — the kernel does not close that gap,
  -- the method's read does.
  let (s1, vs1, _) := go prog preRevoke (invoke preRevoke "select" (hole_selectArg (Sim.dc.bytes a.id))
      (pinC preRevoke.st.host a.id ++ pinF preRevoke.st.host g0) (Sim.S.pinsFor preRevoke.st.host [g0]))
  let (s2, vs2, _) := go prog s1 (Sim.signed s1.st a a.key (Sim.S.pinsFor s1.st.host [a.id, g0]) (.revoke g0))
  let (_, vs3, _) := go prog s2 (invoke s2 "commit" (p8Arg asset a.id cap)
      (pinC s2.st.host a.id ++ pinF s2.st.host g0)
      (Sim.S.pinsFor s2.st.host [asset, accountId X a.id asset, cap, g0]))
  r := note r s!"P8.2s two-Turn split: Turn 1 select while live {vs1}; revoke {vs2}; Turn 2 commit {vs3}; counted left {p8Left s2.st.host cap}"
    (vs1 == "admitted" && vs2 == "admitted" && refusedBy vs3 "commit" "support0 dead" &&
      p8Left s2.st.host cap == some 1)
  -- A commit that pins the live provider's authority at a version it never had is refused by
  -- the kernel's pin check.
  let (_, vw, _) := go prog r (invoke r "commit" (p8Arg asset b.id cap)
      (pinC r.st.host b.id ++ pinF r.st.host providers[1]!)
      (Sim.S.pinsFor r.st.host [asset, accountId X b.id asset, cap] ++ [(providers[1]!, 0)]))
  r := note r s!"P8.2 mismatched live authority pin: {vw}" (vw.startsWith "rejected stale")
  -- The live ROM selects the second provider's candidate; P8.4 commits it.
  let chosen := 1
  let (r', vcode, _) := go prog r (chooseCode r chosen)
  r := note r' s!"P8.3 second provider selects contextual ROM candidate: {vcode}"
    (vcode == "admitted")
  let selected := [a.id, b.id][chosen]?.getD 0
  let fresh := commit r chosen selected
  -- Cancellation exercises the kernel cancel operation on a scratch fork.
  match Receive.cancel X r.st.host fresh (Sim.toySign a.key (X.cancelMessage fresh)) with
  | .recorded _ rec wc =>
    let cancelled := { r with st := { r.st with host := wc, log := r.st.log ++ [.refusal rec] } }
    let (_, vc, _) := go prog cancelled fresh
    r := note r s!"P8 cancel recorded; submit cancelled plan: {vc}"
      (vc.startsWith "rejected refusedFinal" && p8Left wc cap == some 1)
  | _ => r := note r "P8 cancel did not record" false
  -- The same checked artifact outside its signed window refuses by name.
  let expired := { r with st := { r.st with host := { r.st.host with height := fresh.unsigned.validUntil + 1 } } }
  let (_, ve, _) := go prog expired fresh
  r := note r s!"P8 deadline: {ve}" (ve.startsWith "rejected outsideWindow" || ve.startsWith "refused outsideWindow")
  let late := { r with st := { r.st with host := { r.st.host with height := 99999 } } }
  let (_, vl, _) := go prog late (commit late chosen selected)
  r := note r s!"P8 contract deadline: {vl}" (refusedBy vl "commit" "closed")
  let g1 := providers[1]!
  let (moved, vm, _) := go prog r (invoke r "repin"
    (hole_postArg (Sim.dc.bytes g1) (Sim.dc.bytes cap)) (pinF r.st.host g1))
  let (_, vs, _) := go prog moved (commit moved chosen selected)
  r := note r s!"P8 support correspondence moved ({vm}): {vs}"
    (vm == "admitted" && refusedBy vs "commit" "support0 moved")
  let before := r
  let (r', vc, tc) := go prog r fresh
  r := note r' s!"P8.4 RE-EXECUTE atomic checked commitment: {vc}; counted left {p8Left r'.st.host cap}"
    (vc == "admitted" && p8Left r'.st.host cap == some 0 &&
      hole_acceptedOf Sim.env r'.st.host obj == some true &&
      hole_selectedOf Sim.env r'.st.host obj == some (some (Sim.dc.bytes selected)))
  let (_, replay, _) := go prog r fresh
  r := note r s!"P8.4 replay: {replay}" (replay.startsWith "rejected replayed")
  let (_, resumed, _) := go prog r (commit r chosen selected)
  r := note r s!"P8.4 freshly re-executed committed artifact: {resumed}" (refusedBy resumed "commit" "accepted")
  -- Isolate the kernel counted-right check using the object as the authorized actor.
  let spent := Receive.transfer X (pinned Sim.env r.st.host
    (Sim.S.pinsFor r.st.host [asset, accountId X a.id asset, cap]))
    ⟨obj, 0⟩ (.well asset) (.of a.id asset) 1 (some cap) none
  r := note r s!"P8.4 competing use of the same counted right: {match spent with | .error e => e.name | .ok _ => "admitted"}"
    (match spent with | .error (.transferSpent g) => g == cap | _ => false)
  match tc with
  | none => r := note r "P8 no receipt" false
  | some t =>
    r := note r "P8 receipt binds checked call and atomic transition"
      (t.event == X.callBytes fresh &&
       r.st.host.journalAt Sim.env (txIdOf X fresh) == some (before.st.host.height + 1, turnDigest Sim.env t))
    match World.fold Sim.env before.st.host [.turn t] with
    | .ok recovered =>
      let (_, rv, _) := go prog { r with st := { r.st with host := recovered } } fresh
      r := note r s!"P8 recovered suffix: left {p8Left recovered cap}; retry {rv}"
        (Sim.same recovered r.st.host && p8Left recovered cap == some 0 && rv.startsWith "rejected replayed")
    | .error _ => r := note r "P8 recovery failed" false
  r := note r "P8 initial authority was live for both candidates"
    (p8Live ready.st.host supports == [true, true])
  return r

/-- A fresh concrete integration session, also used by the mutation probes. -/
def p8Session (src : String := p8Text) : Run :=
  let X := ctxWith langProgram
  let fk := [("p8-a".toUTF8, "p8-a-next".toUTF8), ("p8-b".toUTF8, "p8-b-next".toUTF8)]
  match genesis X Sim.worldName (Sim.nonceOf 8) 100000000
      (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
  | .error e => note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } }
      s!"P8 genesis: {e.name}" false
  | .ok g =>
    let ms := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
    p8Rows { st := { rng := ⟨1⟩, host := g, members := ms } }
      (ms.headD ⟨0, .empty, .empty⟩) (ms.getD 1 ⟨0, .empty, .empty⟩) src

def journey (bell : String) (mode : Mode) : Run := Id.run do
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
  if mode = .foreignRow then
    return tallyRows mode r a b
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
    s!"(package\n  (imports)\n  (doc)\n  (state (rec))\n  (iface {nestTy n})\n  (methods)\n  (laws)\n  (rels)\n  (body {nestT n}))\n"
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
  -- LV (LANG-60) the package wire's version: Owned's LANG-59 bytes (no version byte) and Owned's
  -- current bytes at the previous version are each refused `lang/package-version/N` at install and at decode,
  -- where the old bytes used to be read; the current bytes begin with the current version
  let versionRefused (v : String) : Bool := v.startsWith "refused program" && (v.splitOn s!"lang/package-version/{Bounds.packageWireVersion}").length > 1
  let (rv1, vv1, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install owned59))
  r := note rv1 s!"LV1 install Owned's LANG-59 bytes ({owned59.size} bytes): {vv1}" (owned59.size == 1788 && versionRefused vv1)
  let prev := ownedBytes.set! 0 (Bounds.packageWireVersion - 1)
  let (rv2, vv2, _) := go prog r (Sim.signed r.st a a.key (Sim.S.pinsFor r.st.host [a.id]) (.install prev))
  r := note rv2 s!"LV2 install Owned's bytes at version {Bounds.packageWireVersion - 1}: {vv2}" (versionRefused vv2)
  let byName := fun (b : ByteArray) => match Wire.decodePackage b with
    | .error (.rejected 0 l) => l == s!"lang/package-version/{Bounds.packageWireVersion}"
    | _ => false
  r := note r s!"LV3 decode refuses both lang/package-version/{Bounds.packageWireVersion}; Owned's bytes begin with version {Bounds.packageWireVersion} and decode"
    (byName owned59 && byName prev && ownedBytes[0]! == Bounds.packageWireVersion &&
      (Wire.decodePackage ownedBytes).toBool)
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
    r := bellRows mode r a b bell
  if mode = .honest then
    r := holeRows mode r a b
    r := quorumRows mode r a b
    r := windowedRows mode r a
  if mode = .honest then
    r := gateRows mode r a

  r := callRows mode r a
  -- L7 the fold and the follower's re-derivation
  match World.fold Sim.env g r.st.log with
  | .ok w => r := note r s!"L7 follower reaches the Host's World ({r.st.log.length} turns)" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 follower refused at {i}: {Sim.nameOf e}" false
  match rederiveLog (ctxWith prog) g r.st.log with
  | .ok w => r := note r "L7 the re-derivation reaches the Host's World" (Sim.same w r.st.host)
  | .error (i, e) => r := note r s!"L7 the re-derivation refused at {i}: {reprStr e}" false
  return r

/-- Permanent real-Receive regression: declared support and blocker observations
must be complete. The same rows are also part of the ordinary journey. -/
def holeObservationJourney (contextual : Bool := false) : Run := Id.run do
  let mode : Mode := .honest
  let prog := mode.program
  let fk : List (ByteArray × ByteArray) :=
    [("f0".toUTF8, "f0-next".toUTF8), ("f1".toUTF8, "f1-next".toUTF8)]
  let X := ctxWith prog
  let g ← match genesis X Sim.worldName (Sim.nonceOf 0) 100000000 (fk.map fun (k, n) => (k, nextKeyDigest X n)) with
    | .ok g => pure g
    | .error e =>
        return note { st := { rng := ⟨1⟩, host := World.genesis X.env 0 0, members := [] } } s!"genesis refused {e.name}" false
  let members := fk.zipIdx.map fun ((k, n), i) => (⟨founderId X g.origin i, k, n⟩ : Sim.Member)
  let r : Run := { st := { rng := ⟨1⟩, host := g, members } }
  let a := members.headD ⟨0, .empty, .empty⟩
  let b := members.getD 1 ⟨0, .empty, .empty⟩
  return holeRows mode r a b contextual

/-- A session of the journey, registered by the module that defines it (`register`), so that no two
modules edit one line of `Main` to be run (that line cost five lanes a landing attempt each, real
2026-10-26): its name, the `IO` that reads what it needs from disk and runs it, and whether
`--contextual` selects it. EVERY registered session runs in the default journey, the one
`gates/runs.tsv` judges; `--contextual` and `--contextual-checks` are filters for a lane at work, not a
second verdict. Sessions run in registration order: this module's, then `Main`'s import order. -/
structure Session where
  name : String
  run : IO Run
  contextual : Bool := false

initialize sessionsRef : IO.Ref (Array Session) ← IO.mkRef #[]

/-- Register a session: one `initialize register { … }` line at the end of the module that defines it. -/
def register (s : Session) : IO Unit := sessionsRef.modify (·.push s)

/-- A text read from disk by name, `""` for a missing file (the shipped sources a session reads). -/
def readOr (p : System.FilePath) : IO String := try IO.FS.readFile p catch _ => pure ""

/-- A session of pure checks: each row a line `{tag} {name}`, a false row counted bad. -/
def checksRun (tag : String) (rows : List (String × Bool)) : Run :=
  rows.foldl (fun r (n, ok) => note r s!"{tag} {n}" ok)
    { st := { rng := ⟨1⟩, host := World.genesis (ctxWith Mode.honest.program).env 0 0, members := [] } }

/-- The registered sessions `args` select: `--contextual` the contextual ones, `--contextual-checks`
the checks session alone, otherwise every one. -/
def selectSessions (args : List String) (sessions : Array Session) : Array Session :=
  if args == ["--contextual"] then sessions.filter (·.contextual)
  else if args == ["--contextual-checks"] then sessions.filter (·.name == "contextual-checks")
  else sessions

/-- Every row of the journey: the LB/LA rows, the twelve modes, then every registered session; or,
under a filter (`selectSessions`), the selected sessions alone. -/
def runAll (args : List String) : IO UInt32 := do
  let sessions ← sessionsRef.get
  if args == ["--contextual"] || args == ["--contextual-checks"] then
    let runs ← (selectSessions args sessions).mapM (·.run)
    for r in runs do
      for line in r.log do IO.println line
    let bad := runs.foldl (fun n r => n + r.bad) 0
    IO.println s!"lang-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
    return if bad = 0 then 0 else 1
  if args == ["--hole-omitted-blocker-pin-admits"] then
    let r := holeObservationJourney
    for l in r.log do IO.println l
    IO.println s!"hole:omitted-blocker-pin-admits {if r.bad = 0 then "GREEN" else s!"RED ({r.bad})"}"
    IO.println s!"lang-journey: {if r.bad = 0 then "GREEN" else s!"RED ({r.bad})"}"
    return if r.bad = 0 then 0 else 1
  let some control := (match args with
      | [] => some false
      | ["--harness-control"] => some true
      | _ => none)
    | IO.eprintln s!"usage: lang-journey [--harness-control | --hole-omitted-blocker-pin-admits | --contextual | --contextual-checks] (got {args})"; return 2
  let bell ← try IO.FS.readFile bellSourcePath catch _ => pure ""
  let bellCore ← try IO.FS.readFile bellCorePath catch _ => pure ""
  -- LB0 the Bell's surface source lowers to exactly the core shipped beside it; one flipped edit is caught
  let (l0, ok0) := match Surface.readPackage bell with
    | .ok want => Surface.shippedRow "LB0" bell bellCore want ("(limits 64 1024)", "(limits 65 1024)")
    | .error e => (s!"LB0 read {bellSourcePath}: {e.text bell}", false)
  IO.println s!"{if ok0 then "ok  " else "FAIL"} {l0}"
  -- LB0d (LANG-60) the Bell states its clock and tie rule in its own doc: one line, printed by the one
  -- printer, read back by the one reader as the same bytes; a doc past `docMax` is refused `badDoc`
  let (ld, okd) := match Surface.readPackage bell with
    | .ok p =>
      let t := Print.bytesText p.doc
      let back := match Read.parse t with
        | .ok y => (match Read.doc 0 [y] with | .ok d => d == p.doc | .error _ => false)
        | .error _ => false
      let says := (t.splitOn "1024").length > 1 && (t.splitOn "ringer digest").length > 1
      let oneLine := !t.contains '\n'
      let long := bell.replace "(doc \"" ("(doc \"" ++ String.ofList (List.replicate Bounds.docMax 'x'))
      let refused := match Surface.readPackage long with
        | .error (.read (.badDoc _)) => true
        | _ => false
      (s!"LB0d the Bell's doc ({p.doc.size} bytes) prints as one line and reads back: {back && oneLine}; it states the window and the tie: {says}; one past docMax refused badDoc: {refused}",
        !p.doc.isEmpty && back && oneLine && says && refused && long != bell)
    | .error e => (s!"LB0d read {bellSourcePath}: {e.text bell}", false)
  IO.println s!"{if okd then "ok  " else "FAIL"} {ld}"
  -- LBw (HOSTING-44) the shipped core is the package the Bell witness names (`Lang.Bell.shapeOk`:
  -- no imports, no holes, its state and relations, `answer`'s type and body, `rung` the waiting
  -- guard), so `Lang.Proofs.Bell` speaks of what the sponsor installs; the core with `answer`
  -- planted to write the ring's text as the answer reads, and is not the witness's
  let (lw, okw) := match Read.readPackage bellCore with
    | .ok p =>
      let planted := bellCore.replace "ask (. x2 text))" "ask (. x2 ringText))"
      let caught := planted != bellCore && (match Read.readPackage planted with
        | .ok q => !Bell.shapeOk q
        | .error _ => false)
      (s!"LBw the shipped core ({bellCorePath}) is the Bell witness's package (Lang.Bell.shapeOk): {Bell.shapeOk p}; its answer planted to write the ring's text read and caught: {caught}",
        Bell.shapeOk p && caught)
    | .error e => (s!"LBw read {bellCorePath}: {e.text}", false)
  IO.println s!"{if okw then "ok  " else "FAIL"} {lw}"
  let activityVerdict := Std.activitySurfaceVerdict
  let activityOk := activityVerdict == "ok"
  IO.println s!"{if activityOk then "ok  " else "FAIL"} LA0 activity with its own facts relation reads and checks: {activityVerdict}"
  let runs := [Mode.honest, .skipJudge, .eraseOccasion, .erasePayload, .dropCalls, .rawInstall, .bytesIds,
    .skipLits, .totalDigest, .unlawfulCodec, .dropRangeRow, .foreignRow].map (journey bell)
  let runs := runs ++ (← sessions.mapM (·.run)).toList
  let runs := match control, runs with
    | true, r :: rest => note r "harness-control: GATES-15's known-red control, an expectation nothing meets (this run must read RED)" false :: rest
    | _, rs => rs
  for r in runs do for l in r.log do IO.println l
  let bad := (runs.map (·.bad)).foldl (· + ·) ((if ok0 then 0 else 1) + (if okd then 0 else 1) + (if okw then 0 else 1) + (if activityOk then 0 else 1))
  IO.println s!"lang-journey: {if bad = 0 then "GREEN" else s!"RED ({bad})"}"
  return if bad = 0 then 0 else 1

initialize register { name := "p8", run := pure (p8Session p8Text), contextual := true }
initialize register { name := "hole-observation", run := pure (holeObservationJourney true), contextual := true }

end Nanodregg.Lang.Journey
