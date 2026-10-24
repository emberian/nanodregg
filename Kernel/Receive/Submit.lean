/-
# Kernel.Receive.Submit — the Host's whole decision for one signed call

A retry is recognised before anything is derived: the transaction id is the digest of the signed
call, so a call already in the journal is `replayed` at its height whatever the World is now
(a retried rotation must not be re-judged against the key it already rotated). Otherwise: check its
signer, compare its pins, derive, then admit (`World.admit`). The Host commits exactly the returned
World.

Order of the checks `submit` makes (each refuses by name; the first that fails answers):
1. the journal: an exact retry is `replayed` at its height;
2. the recorded refusals: a recorded call is `refusedFinal` with its code (KERNEL-44);
3. its authority to be judged (`signedBy`): the World it names (`wrongWorld`, KERNEL-24), its signature
   (the one verify, PERF-1), the member's key (`authKey`: the current key, or for a rotation the
   precommitted next one). A party that holds no key of a member is answered here, before any cell is
   compared, so the pins are no oracle on the World's cells for it;
4. the pins (KERNEL-66, `checkPins`): every cell pin, row pin and range read against the Host's World.
   A moved pin is `stale`, before any receiver or law reads a cell: a stale call is judged by what it
   observed, never by what the World holds now (`Kernel.Proofs.Rederive.stale_declined_before_receive`);
5. the receivers (`deriveTurn`: authority, laws, programs) on the pinned view;
6. `World.admit` of the derived Turn, in the order its own header lists.
Steps 3 and 5 are `receive` with step 4 between them (`Kernel.Proofs.Receive.receive_signed`).
-/
import Kernel.Receive.Derive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

/-- Why a submission did not commit: the receive layer refused, or the kernel rejected. -/
inductive Verdict (D : Type)
  | refused (r : Refusal D)
  | rejected (r : Reject D)
  deriving DecidableEq, Repr

variable {D : Type} [Ord D] [DecidableEq D]

/-- A recorded refusal answers its transaction id with its code, without re-deriving (KERNEL-44). -/
def refusedAnswer (X : Ctx D) (w : World D) (c : Call D) : Option Nat :=
  match w.refusalAt X.env (.tx (txIdOf X c)) with
  | some (.refused _ code _) => some code
  | _ => none

/-- The signer's key, as the receive layer checks it: the member's current key, or for a rotation
the precommitted next key (`rotate`'s own check: KERNEL-47 amendment 7). -/
def authKey (X : Ctx D) (look : Pinned D) (c : Call D) : Except (Refusal D) Unit :=
  match c.unsigned.body with
  | .rotate key next => (rotate X look c key next).map fun _ => ()
  | _ => checkKey look c.unsigned

/-- The signature check, or nothing when it is already known to pass (`verified`): the verify is
made at most once per judgement. -/
def checkSignatureBy (X : Ctx D) (c : Call D) (verified : Bool) : Except (Refusal D) Unit :=
  if verified then .ok () else checkSignature X c

/-- Is the call signed, for THIS World, by a key the member holds (KERNEL-44's class (A))? The World it
names first (`wrongWorld`, KERNEL-24), then the signature (skipped when `verified` carries a passing
one: PERF-1), then the key (`authKey`). `submit` judges nothing else of a call until this passes
(KERNEL-66), and `judge` records only a refusal of a call it passes. -/
def signedBy (X : Ctx D) (w : World D) (c : Call D) (verified : Bool) : Except (Refusal D) Unit := do
  req (c.unsigned.world = w.origin) .wrongWorld
  checkSignatureBy X c verified
  authKey X (pinned X.env w c.unsigned.pins) c

/-- Judge a signed call: journal first (an exact retry is `replayed`), then the recorded refusals (a
refused call is `refusedFinal` with its recorded code, never re-derived: KERNEL-44), then its
authority to be judged (`signedBy`), then its pins (a moved one is `stale`, before anything is
derived: KERNEL-66), then derive (`deriveTurn` on the pinned view) and admit. -/
def submit (X : Ctx D) (w : World D) (c : Call D) : Except (Verdict D) (Turn D × World D) :=
  match w.journalAt X.env (txIdOf X c) with
  | some (h, _) => .error (.rejected (.replayed h))
  | none =>
      match refusedAnswer X w c with
      | some code => .error (.rejected (.refusedFinal code))
      | none =>
          match signedBy X w c false with
          | .error r => .error (.refused r)
          | .ok () =>
              match checkPins X.env w c.unsigned.pins c.unsigned.rowPins c.unsigned.ranges with
              | .error r => .error (.rejected r)
              | .ok () =>
                  match deriveTurn X (pinned X.env w c.unsigned.pins) (rowView X.env w c.unsigned) c with
                  | .error r => .error (.refused r)
                  | .ok t =>
                      match World.admit X.env w t with
                      | .error r => .error (.rejected r)
                      | .ok w' => .ok (t, w')

/-! ## Recording a refusal (KERNEL-44, KERNEL-47) -/

/-- The wire names of the receive refusals, in constructor order (checked against `Refusal.name` by
`codeName_code`). -/
def refusalNames : List String :=
  ["wrongWorld", "badSignature", "unknownKey", "notPrecommitted", "badPossession", "unpinned",
   "missingCell", "wrongKind", "malformedCell", "lawDenied", "program", "stateKey", "tooManyLaws",
   "hasMethods", "noMethods", "noGrant", "grantTarget", "grantRight", "grantWidens", "unrooted",
   "enrollSpent", "transferSpent", "creditSpent", "rightTarget", "notIssuer", "grantTooDeep", "overPrice", "eventMismatch",
   "duplicateEffect", "sameAccount", "zeroAmount", "assetMismatch", "overflow", "notWell",
   "notCallable", "callTooDeep", "revisited", "tooManyCalls", "overTicks", "rowUnpinned", "rangeUnpinned",
   "rangeTooLong", "rowParent", "duplicateRow",
   "cancelled", "cancelForged"]

/-- The wire names of the kernel's rejections, in constructor order (checked against `Reject.name`). -/
def rejectNames : List String :=
  ["overBound", "replayed", "duplicateTouch", "duplicateNullifier", "duplicateKey", "nonCanonicalCell",
   "outsideWindow", "stale", "spent", "chargeMismatch", "overAllowance", "idTaken", "notContentId",
   "bornTouched", "missingCell", "romWrite", "romRetire", "appendOnly", "valueMalformed", "belowFloor",
   "notConserved", "floorNotConserved", "refusedFinal", "refusalBudget", "keyTaken", "relationFull",
   "relationCapped", "rowParentUnpinned", "orphanRow", "rowsRemain", "keyWidth", "noRelation",
   "retractForbidden", "declareLate", "rangeTooLong", "duplicateRow", "rowShape", "missingRow",
   "refusalsFull"]

/-- A verdict's wire name. -/
def Verdict.name : Verdict D → String
  | .refused r => r.name
  | .rejected r => r.name

/-- The code a recorded refusal carries: its name's index, the receive refusals first. -/
def Verdict.code : Verdict D → Nat
  | .refused r => refusalNames.idxOf r.name
  | .rejected r => refusalNames.length + rejectNames.idxOf r.name

/-- Is the verdict a stale pin (KERNEL-54)? Such a refusal is never recorded (`judgeBy` declines it):
a pin observed on the fold and stale now is stale at every World the fold reaches
(`stale_behind_forever`), so the fold settles it without a record. -/
def Verdict.isStale : Verdict D → Bool
  | .rejected (.stale _) => true
  | _ => false

/-- The code a stale refusal would carry: one `judge` never records (`judge_recorded_not_stale`). -/
def staleCode : Nat := refusalNames.length + rejectNames.idxOf "stale"

/-- The name a recorded code answers with (`lookup`'s and a resubmit's `refused NAME`). -/
def codeName (k : Nat) : Option String :=
  if k < refusalNames.length then refusalNames[k]? else rejectNames[k - refusalNames.length]?

/-- The code table by name: every recorded code's name, in code order (`codeName`). A record holds
its code, never its name, so a Store is stamped with this table (`Host.Base.shapeStamp`): a binary
whose table differs (a refusal added, deleted or reordered moves every code after it) refuses the
Store `shapeMismatch` rather than reading its codes as other names. -/
def codeTable : String :=
  "kernel/refusal-codes/v1: " ++ ",".intercalate (refusalNames ++ rejectNames)

/-- What `World.refuse` records for call `c` with verdict `v` and cancel field `a` (KERNEL-60): the
call's own transaction id, member, window and bytes, whoever asks for the record. -/
def recordOf (X : Ctx D) (c : Call D) (v : Verdict D) (a : ByteArray) : Refused D :=
  { txId := txIdOf X c, member := c.unsigned.member, notBefore := c.unsigned.notBefore,
    validUntil := c.unsigned.validUntil, code := v.code, event := X.callBytes c, cancel := a }

/-- What `World.refuse` records for a call refused with `v`: its record with no cancel signature. -/
def refusedOf (X : Ctx D) (c : Call D) (v : Verdict D) : Refused D := recordOf X c v ByteArray.empty

/-- Did `submit` reach verdict `v` only past a signature that VERIFIED (PERF-1)? A refusal `receive`
made after its signature check (anything but `wrongWorld` and `badSignature`), a moved pin (`stale`,
KERNEL-66: compared only past `signedBy`), or any rejection `World.admit` made, is reached only through
`checkSignature`'s one verify passing (`submit_verified`). False for everything decided before that
verify or by it: the journal (`replayed`), the recorded refusals (`refusedFinal`), the World the call
names (`wrongWorld`), and `badSignature`, which a program may also name, so it does not say which
verify failed. -/
def Verdict.verified : Verdict D → Bool
  | .refused .wrongWorld => false
  | .refused .badSignature => false
  | .refused _ => true
  | .rejected (.replayed _) => false
  | .rejected (.refusedFinal _) => false
  | .rejected _ => true

/-- Was the call signed, for THIS World, by a key the member holds (KERNEL-44's class (A)), the
signature check skipped when `verified` already carries its passing (`judge`)? `signedBy` passed. -/
def authenticatedBy (X : Ctx D) (w : World D) (c : Call D) (verified : Bool) : Bool :=
  match signedBy X w c verified with
  | .ok () => true
  | .error _ => false

/-- Was the call signed, for THIS World, by a key the member holds (KERNEL-44's class (A))? Only
such a refusal is charged to the member and recorded; any other is answered and forgotten (U). -/
def authenticated (X : Ctx D) (w : World D) (c : Call D) : Bool := authenticatedBy X w c false

/-- What the Host does with a signed call (KERNEL-44): admitted; refused and RECORDED (final within
the window: `submit_refused_final`); or refused and NOT recorded (`declined`: stale (KERNEL-54), unauthenticated, early,
or over the member's `refusalBudget`, or the World's `refusalsFull` (KERNEL-55 R1), which is the
verdict then). None of these is final by a record. A call with a moved pin is `stale` before any
receiver or law judges it (KERNEL-66, `submit`'s order), so no receiver's refusal of the World as it
is now is recorded for it: a stale whose pin the fold has moved past (BEHIND) is final by the fold
instead (`stale_behind_forever`), and an AHEAD stale is not final. -/
inductive Outcome (D : Type) [Ord D]
  | admitted (t : Turn D) (w' : World D)
  | recorded (v : Verdict D) (r : Refused D) (w' : World D)
  | declined (v : Verdict D)

/-- `submit`, and for a refused call whether to record it, given how it is authenticated (`auth`
of the verdict): recorded when authenticated, not stale, and `World.refuse` takes it; declined
otherwise. A stale verdict is declined before authentication (KERNEL-54: never recorded, spends no
budget). -/
def judgeBy (X : Ctx D) (w : World D) (c : Call D) (auth : Verdict D → Bool) : Outcome D :=
  match submit X w c with
  | .ok (t, w') => .admitted t w'
  | .error v =>
      if v.isStale then .declined v else
      if auth v then
        match World.refuse X.env w (refusedOf X c v) with
        | .ok w' => .recorded v (refusedOf X c v) w'
        | .error .refusalBudget => .declined (.rejected .refusalBudget)
        | .error .refusalsFull => .declined (.rejected .refusalsFull)
        | .error _ => .declined v
      else .declined v

/-- The Host's decision. The signature is verified ONCE (PERF-1): a verdict `submit` reached past
its verify carries that verify's passing into the authentication (`Verdict.verified`), so a
recorded refusal costs what its admission would have, one verify per signature it carries.
`judge_eq`: the same Outcome as authenticating by `authenticated` (the two-verify judge). -/
def judge (X : Ctx D) (w : World D) (c : Call D) : Outcome D :=
  judgeBy X w c fun v => authenticatedBy X w c v.verified

/-! ## Cancelling a call (KERNEL-60, design C1)

A member ends one of its own outstanding calls before it lands by recording the refusal of that
very call, code `cancelled`: the record is the call's own (`recordOf`: its transaction id, member,
window and bytes), so every reader of refusals settles it as it settles a judged refusal: final, not
admitted. What authorises it is the member's signature over `domCancel ‖ txId` under the member's
CURRENT key on the World it is recorded on; the call's own signature is not needed (burning a txId
whose call was never validly signed harms nobody). `World.refuse` judges it unchanged: inside the
call's window only, never once the call is journaled (`replayed`) or already recorded
(`refusedFinal`), and charged like any record to the member's `refusalsPerWindow` and the World's
`refusalsPerWindowMax`: a cancel is SPAM-CLASS by decision, so a member that cancels sixteen calls
in a window has its later refusals declined `refusalBudget` until the window turns. -/

/-- The cancel signature's domain: distinct from `domCall`, so a cancel is never a call signature. -/
def domCancel : ByteArray := "nanodregg/kernel/cancel-signature".toUTF8

/-- What a cancel of `c` is a signature over: `domCancel`, then `c`'s transaction id's bytes. -/
def Ctx.cancelMessage (X : Ctx D) (c : Call D) : ByteArray := domCancel ++ X.env.bytes (txIdOf X c)

/-- The record a cancel of `c` with signature `sig` makes. -/
def cancelOf (X : Ctx D) (c : Call D) (sig : ByteArray) : Refused D :=
  recordOf X c (.refused .cancelled) sig

/-- A cancel's authority on `w`: the call names this World, the signature is non-empty and within
`cancelBytesMax`, and it verifies under the member's current key on `w`. -/
def cancelAuth (X : Ctx D) (w : World D) (c : Call D) (sig : ByteArray) : Except (Refusal D) Unit := do
  req (c.unsigned.world = w.origin) .wrongWorld
  req (decide (0 < sig.size ∧ sig.size ≤ Bounds.cancelBytesMax)) .badSignature
  match w.live X.env c.unsigned.member with
  | some m =>
      match m.slots.get slotKey with
      | some k =>
          if m.kind = kindMember then req (X.verify k (X.cancelMessage c) sig) .badSignature
          else .error (.unknownKey c.unsigned.member)
      | none => .error (.unknownKey c.unsigned.member)
  | none => .error (.unknownKey c.unsigned.member)

/-- The Host's decision on a cancel of `c` signed `sig`: recorded as `cancelOf X c sig`, or declined
(an unauthorised cancel by its receive name; one `World.refuse` refuses by its kernel name:
`outsideWindow`, `replayed`, `refusedFinal`, `refusalBudget`, `refusalsFull`). -/
def cancel (X : Ctx D) (w : World D) (c : Call D) (sig : ByteArray) : Outcome D :=
  match cancelAuth X w c sig with
  | .error e => .declined (.refused e)
  | .ok () =>
      match World.refuse X.env w (cancelOf X c sig) with
      | .ok w' => .recorded (.refused .cancelled) (cancelOf X c sig) w'
      | .error e => .declined (.rejected e)

end Nanodregg.Kernel.Receive
