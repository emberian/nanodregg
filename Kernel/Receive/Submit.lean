/-
# Kernel.Receive.Submit — the Host's whole decision for one signed call

A retry is recognised before anything is derived: the transaction id is the digest of the signed
call, so a call already in the journal is `replayed` at its height whatever the World is now
(a retried rotation must not be re-judged against the key it already rotated). Otherwise:
derive (`receive`), then admit (`World.admit`). The Host commits exactly the returned World.
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
  | some (.refused _ code) => some code
  | _ => none

/-- Judge a signed call: journal first (an exact retry is `replayed`), then the recorded refusals (a
refused call is `refusedFinal` with its recorded code, never re-derived: KERNEL-44), then derive and
admit. -/
def submit (X : Ctx D) (w : World D) (c : Call D) : Except (Verdict D) (Turn D × World D) :=
  match w.journalAt X.env (txIdOf X c) with
  | some (h, _) => .error (.rejected (.replayed h))
  | none =>
      match refusedAnswer X w c with
      | some code => .error (.rejected (.refusedFinal code))
      | none =>
          match receive X w c with
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
   "enrollSpent", "notIssuer", "grantTooDeep", "overPrice", "undecodableEvent", "eventMismatch",
   "duplicateEffect", "sameAccount", "zeroAmount", "assetMismatch", "overflow", "notWell",
   "notCallable", "callTooDeep", "revisited", "tooManyCalls", "overTicks"]

/-- The wire names of the kernel's rejections, in constructor order (checked against `Reject.name`). -/
def rejectNames : List String :=
  ["overBound", "replayed", "duplicateTouch", "duplicateNullifier", "duplicateKey", "nonCanonicalCell",
   "outsideWindow", "stale", "spent", "chargeMismatch", "overAllowance", "idTaken", "notContentId",
   "bornTouched", "missingCell", "romWrite", "romRetire", "appendOnly", "valueMalformed", "belowFloor",
   "notConserved", "floorNotConserved", "refusedFinal", "refusalBudget"]

/-- A verdict's wire name. -/
def Verdict.name : Verdict D → String
  | .refused r => r.name
  | .rejected r => r.name

/-- The code a recorded refusal carries: its name's index, the receive refusals first. -/
def Verdict.code : Verdict D → Nat
  | .refused r => refusalNames.idxOf r.name
  | .rejected r => refusalNames.length + rejectNames.idxOf r.name

/-- The name a recorded code answers with (`lookup`'s and a resubmit's `refused NAME`). -/
def codeName (k : Nat) : Option String :=
  if k < refusalNames.length then refusalNames[k]? else rejectNames[k - refusalNames.length]?

/-- What `World.refuse` records for a call refused with `v`. -/
def refusedOf (X : Ctx D) (c : Call D) (v : Verdict D) : Refused D :=
  { txId := txIdOf X c, member := c.unsigned.member, notBefore := c.unsigned.notBefore,
    validUntil := c.unsigned.validUntil, code := v.code, event := X.callBytes c }

/-- The signer's key, as the receive layer checks it: the member's current key, or for a rotation
the precommitted next key (`rotate`'s own check: KERNEL-47 amendment 7). -/
def authKey (X : Ctx D) (look : Pinned D) (c : Call D) : Except (Refusal D) Unit :=
  match c.unsigned.body with
  | .rotate key next => (rotate X look c key next).map fun _ => ()
  | _ => checkKey look c.unsigned

/-- Was the call signed, for THIS World, by a key the member holds (KERNEL-44's class (A))? Only
such a refusal is charged to the member and recorded; any other is answered and forgotten (U). -/
def authenticated (X : Ctx D) (w : World D) (c : Call D) : Bool :=
  match (do
      req (c.unsigned.world = w.origin) .wrongWorld
      checkSignature X c
      authKey X (pinned X.env w c.unsigned.pins) c : Except (Refusal D) Unit) with
  | .ok () => true
  | .error _ => false

/-- What the Host does with a signed call (KERNEL-44): admitted; refused and RECORDED (final within
the window: `submit_refused_final`); or refused and NOT recorded (`declined`: unauthenticated, early,
or over the member's `refusalBudget`, which is the verdict then; none of these is final). -/
inductive Outcome (D : Type) [Ord D]
  | admitted (t : Turn D) (w' : World D)
  | recorded (v : Verdict D) (r : Refused D) (w' : World D)
  | declined (v : Verdict D)

def judge (X : Ctx D) (w : World D) (c : Call D) : Outcome D :=
  match submit X w c with
  | .ok (t, w') => .admitted t w'
  | .error v =>
      if authenticated X w c then
        match World.refuse X.env w (refusedOf X c v) with
        | .ok w' => .recorded v (refusedOf X c v) w'
        | .error .refusalBudget => .declined (.rejected .refusalBudget)
        | .error _ => .declined v
      else .declined v

end Nanodregg.Kernel.Receive
