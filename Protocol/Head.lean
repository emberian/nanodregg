/-
# Protocol.Head — a World's position, and a member's attestation of its own (PROTOCOL-74; DESIGN-TRUST T1)

A HEAD is one World's position as every party states it: the World (its origin, KERNEL-24), its step
count (the chain's index, KERNEL-47), its height, its roots digest (what a receipt is checked
against, PROTOCOL-45) and its chain (what `fold_head_binds` binds: one `(steps, chain)` is one log).
Four spellings of it were in the tree (`logPage`'s pair, `receipt CALL`'s `head` line, `Std.head`'s
record, `host check`'s anchor); this is the one.

An ATTESTATION is a member's signed statement that its OWN follow's fold sits at a head: the head,
the member and its key, signed under `domHead` (the seventh signing domain, pairwise disjoint from
the six of `Protocol.Proofs.Domains`). It is not an authority: it says what one member holds, never
what the World is. Follow makes one at the tip of a catch-up (`nd sync --attest`: the message it
hands custody is its own World's head, `Command.attestTip`) and checks another member's
(`nd sync --check ATTEST`): the signature under the key it names, the World, and, on the World it
caught up to, that the key is the signer's CURRENT one (a rotated-away key is `staleKey`: an
attestation is checked under the signer's current key; rotate, then attest again).

The ANCHOR CHECK is the comparison (`anchorCheck`): as follow absorbs a page it advances the chain
over the page's steps, each with the roots digest after it (the record's shape, `Persist.steps`),
exactly as the kernel's `chainOf` does, and when the fold reaches the anchor's step count the chain
there must be the anchor's. Reaching it with another chain is `forked`: this member and the member
whose head that is hold two histories of one World (`Proofs.Head.forked_not_on_fold`); reaching it
with the same chain is `shared`: their logs agree up to that step, or two listed inputs collide
(`Proofs.Head.anchor_binds`, through `fold_head_binds`). The member that is BEHIND does the check: it
passes through the other's position on its way to the tip. One already past it answers `ahead` (its
World holds only the current chain; `host check STORE --anchor` on its own Store compares a past
position), and one whose writer's tip is below the anchor answers `unreached`.

A SELF-HEAD POST (PROTOCOL-75; DESIGN-TRUST T2) is the comparison made automatic, through the
writer: a member posts its own head into a `Std.head` object of THIS World (`nd sync --post OBJ`:
`headText` of follow's own World, planned as `invoke OBJ post` at the tip, `Command.body`), and
every follow that absorbs the page carrying that post reads the object (`selfPosts`: a head object
whose `world` is this World's origin, touched by a step of the page) and walks the page against the
posted `(steps, chain)` exactly as `sync --to` walks (`forkedSelfPost`). A post at a position the
page reaches with ANOTHER chain is `forkedPost`, the page kept (it is lawful on follow's fold) and
the command ended by name: the poster's signed call is the witness. A post at a position follow was
already past is not compared here: its chain is in follow's own Store (cv task T2b', the follow loop
through its index), as `host check --anchor` reads it.
-/
import Protocol.Envelope
import Protocol.Command.Text
import Protocol.Foreign

namespace Nanodregg.Protocol.Head

open Nanodregg.Codec Nanodregg.Kernel Nanodregg.Kernel.Receive

variable {D : Type} [Ord D] [DecidableEq D]

/-- One World's position. -/
structure Head (D : Type) where
  origin : D
  steps : Nat
  height : Nat
  roots : D
  chain : D
  deriving DecidableEq

/-- A World's own head. -/
def headOf (E : Env D) (w : World D) : Head D :=
  ⟨w.origin, w.steps, w.height, w.roots E, w.chain⟩

/-- The domain every attestation message begins with. -/
def domHead : ByteArray := "nanodregg/protocol/head/v1".toUTF8

/-- The signed part: the head's five fields, the member's id bytes and its key. -/
def unsignedLayout : Layout :=
  [.bytes "origin", .u64 "steps", .u64 "height", .bytes "roots", .bytes "chain", .bytes "member", .bytes "key"]

/-- An attestation on the wire: the signed bytes as carried, then the signature over them. -/
def attestationLayout : Layout := [.bytes "unsigned", .bytes "signature"]

def unsignedFrame : Stream (Layout.Ty Bounds.frameBytesMax unsignedLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) unsignedLayout

def attestationFrame : Stream (Layout.Ty Bounds.frameBytesMax attestationLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) attestationLayout

/-- The unsigned bytes of an attestation's fields, or `none` past the frame bound. -/
def unsignedBytes (E : Env D) (h : Head D) (member : D) (key : ByteArray) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (unsignedFrame.bytes (← f (E.bytes h.origin), h.steps.toUInt64, h.height.toUInt64,
    ← f (E.bytes h.roots), ← f (E.bytes h.chain), ← f (E.bytes member), ← f key, ()))

/-- What the member signs. -/
def message (unsigned : ByteArray) : ByteArray := domHead ++ unsigned

/-- An attestation's wire bytes, or `none` past the frame bound. -/
def bytes (unsigned signature : ByteArray) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (attestationFrame.bytes (← f unsigned, ← f signature, ()))

/-- A decoded attestation. -/
structure Attestation (D : Type) where
  head : Head D
  member : D
  key : ByteArray
  /-- the signed bytes exactly as carried (`unsignedFrame`) -/
  unsigned : ByteArray
  signature : ByteArray

/-- Why an attestation is not taken (law 7). -/
inductive Refusal
  /-- the bytes are not an attestation (either frame, or a digest field) -/
  | badAttestation
  /-- it names another World than the member's own -/
  | otherWorld
  /-- the signature does not verify over the bytes carried under the key they name -/
  | badHeadSignature
  /-- the member it names is not a live member of the World follow caught up to -/
  | notMember
  /-- the key it names is not that member's current key on the World follow caught up to -/
  | staleKey
  deriving DecidableEq, Repr

def Refusal.name : Refusal → String
  | .badAttestation => "badAttestation" | .otherWorld => "otherWorld"
  | .badHeadSignature => "badHeadSignature" | .notMember => "notMember" | .staleKey => "staleKey"

/-- The constructor's index, the thing a name must determine (`Proofs.Head.Refusal.name_injective`). -/
def Refusal.tag : Refusal → Nat
  | .badAttestation => 0 | .otherWorld => 1 | .badHeadSignature => 2 | .notMember => 3 | .staleKey => 4

def Refusal.all : List Refusal := [.badAttestation, .otherWorld, .badHeadSignature, .notMember, .staleKey]

/-- Decode the signed bytes, checking nothing they state. -/
def said (X : Ctx D) (u : ByteArray) : Option (Head D × D × ByteArray) :=
  match unsignedFrame.decode u with
  | .error _ => none
  | .ok (o, s, h, r, c, m, k, ()) => do
      pure (⟨← X.digestOf o.1, s.toNat, h.toNat, ← X.digestOf r.1, ← X.digestOf c.1⟩, ← X.digestOf m.1, k.1)

/-- Decode an attestation, checking nothing it states. -/
def ofBytes (X : Ctx D) (b : ByteArray) : Option (Attestation D) :=
  match attestationFrame.decode b with
  | .error _ => none
  | .ok (u, s, ()) => do
      let (h, m, k) ← said X u.1
      pure { head := h, member := m, key := k, unsigned := u.1, signature := s.1 }

/-- Decode and verify: the attestation is for `origin` and its signature verifies under the key it
names. Whether that key is the member's is `signer`'s question, asked on a caught-up World. -/
def verified (X : Ctx D) (origin : D) (b : ByteArray) : Except Refusal (Attestation D) :=
  match ofBytes X b with
  | none => .error .badAttestation
  | some a =>
    if a.head.origin ≠ origin then .error .otherWorld
    else if !X.verify a.key (message a.unsigned) a.signature then .error .badHeadSignature
    else .ok a

/-- On `w`, the attestation's member is live and the key it names is that member's current one. -/
def signer (X : Ctx D) (w : World D) (a : Attestation D) : Except Refusal Unit :=
  match currentKey X.env w a.member with
  | none => .error .notMember
  | some k => if k = a.key then .ok () else .error .staleKey

/-! ## The anchor check -/

/-- What walking a page's steps against an anchor finds. -/
inductive Anchored
  /-- the fold reached the anchor's step count with the anchor's chain -/
  | shared
  /-- the page ends before the anchor's step count (or began past it) -/
  | unreached
  /-- the fold reached the anchor's step count with ANOTHER chain -/
  | forked
  deriving DecidableEq, Repr

/-- From position `(s, c)`, advance the chain over the steps (each with the roots digest after it,
as `World.fold` stamps them: `stepLink`, `chainOf`) and compare at the anchor's step count. -/
def anchorCheck (E : Env D) (steps : Nat) (chain : ByteArray) : Nat → D → List (Kernel.Step D × D) → Anchored
  | _, _, [] => .unreached
  | s, c, (t, r) :: rest =>
      let c' := stepLink E c t r
      if s + 1 = steps then (if E.bytes c' = chain then .shared else .forked)
      else anchorCheck E steps chain (s + 1) c' rest

/-! ## Self-heads through the writer (PROTOCOL-75) -/

/-- `Std.headPackage`'s `post`: method 1 (methods by label, ascending: `fork`, `post`). -/
def postMethod : Nat := 1

/-- The text `sync --post` hands the head object's `post`: follow's own World's head at
`Std.headAtTy` (labels ascending: chain, height, roots, steps), as `nd invoke` would be given it. -/
def headText (X : Ctx D) (w : World D) : String :=
  s!"(record (chain #{Text.toHex (X.env.bytes w.chain)}) (height {w.height}) (roots #{Text.toHex (X.env.bytes (w.roots X.env))}) (steps {w.steps}))"

/-- The cells a step wrote or made: where a head object can have changed. -/
def stepCells : Kernel.Step D → List D
  | .turn t => t.touches.map (·.cell) ++ createdIds t
  | .refusal _ => []

/-- A self-head post: on `w'` (the World after the page), cell `c`, touched by step `s` of the page,
is a head object of THIS World (`Lang.headView` at `Foreign.headPackageId`, its `world` the World's
origin) holding an `at` head: its `(steps, chain)`, and the member whose call the step was. -/
def selfPost (X : Ctx D) (w' : World D) (s : Kernel.Step D) (c : D) : Option (Nat × ByteArray × Option D) := do
  let cell ← w'.live X.env c
  match Lang.headView X.digestOf (X.env.bytes (Foreign.headPackageId X.env)) cell with
  | some (.at world chain _ _ steps) =>
      if world = X.env.bytes w'.origin then
        some (steps, chain, match s with
          | .turn t => (X.decodeCall t.event).map (·.unsigned.member)
          | .refusal _ => none)
      else none
  | _ => none

/-- Every self-head post a page carries, in log order. -/
def selfPosts (X : Ctx D) (w' : World D) (ts : List (Kernel.Step D × D)) : List (Nat × ByteArray × Option D) :=
  ts.flatMap fun p => (stepCells p.1).filterMap (selfPost X w' p.1)

/-- The first self-head post whose position follow's fold reached ON THIS PAGE with another chain
(`anchorCheck` from follow's position before the page, as `sync --to` walks): its step count and
the poster. A post at a position follow was already past, or past the page, is `unreached` from here
and not compared. -/
@[irreducible] def forkedSelfPost (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (w' : World D) :
    Option (Nat × Option D) :=
  (selfPosts X w' ts).findSome? fun p =>
    if anchorCheck X.env p.1 p.2.1 w.steps w.chain ts = .forked then some (p.1, p.2.2) else none

/-- The self-head posts a page carries at a position follow was already AT or past before the page
(`steps ≤ w.steps`): exactly the ones `anchorCheck` cannot reach from follow's position (it compares
the step counts `w.steps + 1 …` the page walks), so `forkedSelfPost` leaves them `unreached`. Follow's
own Store answers them (`forkedBehindPost`, `Host.Follow.loop`: T2b'). -/
def behindPosts (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (w' : World D) :
    List (Nat × ByteArray × Option D) :=
  (selfPosts X w' ts).filter fun p => decide (p.1 ≤ w.steps)

/-- The first behind post whose chain is not the chain follow's own history holds at its step count
(`chainAt s`, read from follow's Store: `Host.Deployed.chainKept`), and its poster. A step the Store no
longer keeps (`chainAt s = none`: below its oldest kept file) is not compared: the Store cannot say. -/
def forkedBehindPost (posts : List (Nat × ByteArray × Option D)) (chainAt : Nat → Option ByteArray) :
    Option (Nat × Option D) :=
  posts.findSome? fun p => match chainAt p.1 with
    | some c => if c = p.2.1 then none else some (p.1, p.2.2)
    | none => none

/-! ## Certified heads (PROTOCOL-76; DESIGN-TRUST §1.2, §4.3: T3's unsigned half)

An attestation says what ONE MEMBER holds. A CERTIFICATE says what the WORLD is at: a head with
`threshold` signatures by the World's CERTIFIERS, the authority a World is given at its genesis
(KERNEL-69: `Kernel.Receive.Authority`, in the genesis input and the World's authority cell).
Every World today has `Authority.none` (no certifier, threshold 0: the writer's page is its bare
word and members audit, as before); one key at threshold 1 is the lock writer with a signature; `3f+1`
keys at threshold `2f+1` is the committee. The object, its domain (`domCertify`, the eighth a key
signs under) and its one verification path (`certified`: `threshold` DISTINCT listed certifiers,
each signature verifying over the certified bytes) land here, with refusals by name. No deployed
path PRODUCES a certificate yet (a Store holds no certify seed: cv 01a1769d, Ember's), and none
consumes one yet (the `Carried` start, the `log`/`read` reply field, `Thin.accept`, the head law's
`uncertified`: the next landing). What a verifier learns from `certified = .ok` is `Proofs.Head.certified_ok`; what two
certificates at one step count mean under a quorum is `certified_intersect` and
`certified_equivocation` there, the committee row of DESIGN-TRUST §1.3's table as a theorem over
the object alone. -/

/-! `Authority` here is KERNEL's (`Kernel.Receive.Authority`, KERNEL-69): who may certify and how
many must, fixed at genesis, committed in the origin (`GenesisInput`) and carried in the World as
one ROM cell (`authorityCell`, read back by `authorityOf`); `Authority.none` names nobody. This file
defines no copy of it. -/

/-- The domain every certificate message begins with (byte 19 differs from `domHead`). -/
def domCertify : ByteArray := "nanodregg/protocol/certify/v1".toUTF8

/-- The certified part: the head's five fields. No member, no key: a certificate is the World's
statement, and who made it is the authority's list, not the bytes. -/
def certifiedLayout : Layout :=
  [.bytes "origin", .u64 "steps", .u64 "height", .bytes "roots", .bytes "chain"]

/-- A certificate on the wire: the certified bytes as carried, then the signers (each an index into
the authority's list, as u64 bytes) and their signatures, two lists read in step. -/
def certificateLayout : Layout := [.bytes "certified", .list "signers", .list "signatures"]

def certifiedFrame : Stream (Layout.Ty Bounds.frameBytesMax certifiedLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) certifiedLayout

def certificateFrame : Stream (Layout.Ty Bounds.frameBytesMax certificateLayout) :=
  Layout.codec Bounds.frameBytesMax (by decide) certificateLayout

/-- The bytes a certifier signs over, or `none` past the frame bound. -/
def certifiedBytes (E : Env D) (h : Head D) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  pure (certifiedFrame.bytes (← f (E.bytes h.origin), h.steps.toUInt64, h.height.toUInt64,
    ← f (E.bytes h.roots), ← f (E.bytes h.chain), ()))

/-- What a certifier signs. -/
def certifyMessage (certified : ByteArray) : ByteArray := domCertify ++ certified

/-- A certificate's wire bytes, or `none` past the frame bounds. -/
def certificateBytes (certified : ByteArray) (sigs : List (Nat × ByteArray)) : Option ByteArray := do
  let f := Text.fit Bounds.frameBytesMax
  let l := Text.fitList Bounds.frameBytesMax
  pure (certificateFrame.bytes (← f certified, ← l (sigs.map fun p => Text.u64 p.1),
    ← l (sigs.map (·.2)), ()))

/-- A decoded certificate. -/
structure Certificate (D : Type) where
  head : Head D
  /-- the certified bytes exactly as carried (`certifiedFrame`) -/
  certified : ByteArray
  /-- the signers (indices into the authority's list) and their signatures, as carried -/
  sigs : List (Nat × ByteArray)
  deriving DecidableEq

/-- Why a certificate is not taken (law 7). -/
inductive CertRefusal
  /-- the bytes are not a certificate (either frame, a digest field, or lists of two lengths) -/
  | badCertificate
  /-- it names another World -/
  | otherWorld
  /-- signer `index` is not in the authority's list -/
  | unlisted (index : Nat)
  /-- certifier `index` signs twice -/
  | repeated (index : Nat)
  /-- certifier `index`'s signature does not verify over the certified bytes -/
  | badCertifySignature (index : Nat)
  /-- fewer distinct listed certifiers than the authority's threshold -/
  | belowThreshold (signers threshold : Nat)
  deriving DecidableEq, Repr

def CertRefusal.name : CertRefusal → String
  | .badCertificate => "badCertificate" | .otherWorld => "otherWorld" | .unlisted _ => "unlisted"
  | .repeated _ => "repeated" | .badCertifySignature _ => "badCertifySignature"
  | .belowThreshold .. => "belowThreshold"

/-- The constructor's index, the thing a name must determine (`Proofs.Head.CertRefusal.name_injective`). -/
def CertRefusal.tag : CertRefusal → Nat
  | .badCertificate => 0 | .otherWorld => 1 | .unlisted _ => 2 | .repeated _ => 3
  | .badCertifySignature _ => 4 | .belowThreshold .. => 5

/-- Decode the certified bytes, checking nothing they state. -/
def certifiedSaid (X : Ctx D) (u : ByteArray) : Option (Head D) :=
  match certifiedFrame.decode u with
  | .error _ => none
  | .ok (o, s, h, r, c, ()) => do
      pure ⟨← X.digestOf o.1, s.toNat, h.toNat, ← X.digestOf r.1, ← X.digestOf c.1⟩

/-- Decode a certificate, checking nothing it states. -/
def certificateOfBytes (X : Ctx D) (b : ByteArray) : Option (Certificate D) :=
  match certificateFrame.decode b with
  | .error _ => none
  | .ok (u, ss, sg, ()) =>
      match certifiedSaid X u.1, (Text.unlist ss).mapM Text.ofU64 with
      | some h, some signers =>
          if signers.length = (Text.unlist sg).length then
            some { head := h, certified := u.1, sigs := signers.zip (Text.unlist sg) }
          else none
      | _, _ => none

/-- Walk the signatures from the signers `seen`: each signer listed, not seen, verifying over `msg`.
Returns every signer accepted. -/
def certifySigners (X : Ctx D) (auth : Authority) (msg : ByteArray) :
    List (Nat × ByteArray) → List Nat → Except CertRefusal (List Nat)
  | [], seen => .ok seen
  | (i, s) :: rest, seen =>
      match auth.certifiers[i]? with
      | none => .error (.unlisted i)
      | some k =>
          if i ∈ seen then .error (.repeated i)
          else if !X.verify k msg s then .error (.badCertifySignature i)
          else certifySigners X auth msg rest (i :: seen)

/-- Decode and verify under `auth`: the certificate is for `origin`, and at least `auth.threshold`
distinct listed certifiers each signed its certified bytes under `domCertify`. The one path every
party that trusts a head without a World (a thin joiner, a foreign World, a phone) will run. -/
def certified (X : Ctx D) (auth : Authority) (origin : D) (b : ByteArray) :
    Except CertRefusal (Certificate D) :=
  match certificateOfBytes X b with
  | none => .error .badCertificate
  | some c =>
    if c.head.origin ≠ origin then .error .otherWorld
    else match certifySigners X auth (certifyMessage c.certified) c.sigs [] with
      | .error r => .error r
      | .ok signers =>
          if signers.length < auth.threshold then .error (.belowThreshold signers.length auth.threshold)
          else .ok c

end Nanodregg.Protocol.Head
