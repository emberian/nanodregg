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
every follow that
absorbs the page carrying that post reads it FROM THE STEP that made it (`selfPosts`, PROTOCOL-83:
the head a signed `post` call carries, or a head object of this World a turn bears, attributed to
the call's signer, at the step's own log position), never from the World after the page (a later
post on the same page would hide an earlier one, and an earlier toucher would be named for a later
head). A post naming a step its own position had not reached is `postBeyondPage`; one at a position
the page reaches with ANOTHER chain is `forkedPost`; either way the page is kept (it is lawful on
follow's fold) and the command ends by name, the step and the signer printed: the signed call is the
witness. A post at a position follow was already past is compared against follow's own Store
(`behindPosts`, `Host.Follow.behindOr`). No other post exists: a post's position is inside its page.
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

/-- A self-head post (PROTOCOL-83): what one admitted step says about its signer's head. The posted
head's step count and chain bytes, the member who signed the call, and the post's own log position
(`pos`: the World's step count when the step was admitted, so the step is the `pos + 1`-th). -/
structure Post (D : Type) where
  steps : Nat
  chain : ByteArray
  member : D
  pos : Nat

/-- The head of THIS World a cell holds, as `(steps, chain)`: the cell is a head object
(`Lang.headView` at `Foreign.headPackageId`) whose `world` is `origin`, holding an `at` head. -/
def selfHeadOf (X : Ctx D) (origin : D) (cell : Cell) : Option (Nat × ByteArray) :=
  match Lang.headView X.digestOf (X.env.bytes (Foreign.headPackageId X.env)) cell with
  | some (.at world chain _ _ steps) => if world = X.env.bytes origin then some (steps, chain) else none
  | _ => none

/-- `o` is a head object of THIS World: live on `w'` (after the page), else on `w` (before it), with
`world` the World's origin. A head object's package never changes (`Integrity.law`) and its `world`
is fixed by the head law, so either World answers. -/
def selfHeadObj (X : Ctx D) (w w' : World D) (o : D) : Bool :=
  match (w'.live X.env o).orElse fun _ => w.live X.env o with
  | some cell =>
    match Lang.headView X.digestOf (X.env.bytes (Foreign.headPackageId X.env)) cell with
    | some (.at world ..) | some (.forked world) => world = X.env.bytes w'.origin
    | none => false
  | none => false

/-- The head a `post` call's arguments carry: its step count and chain bytes. -/
def postedHead (args : ByteArray) : Option (Nat × ByteArray) :=
  match (Lang.Wire.decodeData Lang.Std.headAtTy args).toOption with
  | some (.record [("chain", .digest c), ("height", .nat _), ("roots", .digest _), ("steps", .nat s)]) =>
      some (s, c)
  | _ => none

/-- The self-head posts of one step at log position `pos`, read from the STEP, never from a later
World: each head object of this World the turn bears (a seed is a claim at its step, PROTOCOL-75),
then the head a signed `invoke OBJ post HEAD` carries when OBJ is a head object of this World. Each
is attributed to the member whose signed call the step is. A head object's state changed any other
way (a raw `write`, a nested call of a program) is no member's signed statement of its own head, and
is not a post. -/
def stepPosts (X : Ctx D) (w w' : World D) (pos : Nat) : Kernel.Step D → List (Post D)
  | .refusal _ => []
  | .turn t =>
    match X.decodeCall t.event with
    | none => []
    | some c =>
      let m := c.unsigned.member
      (t.creates.filterMap fun p => (selfHeadOf X w'.origin p.2).map fun h => ⟨h.1, h.2, m, pos⟩) ++
      match c.unsigned.body with
      | .invoke o meth args _ _ =>
          if meth = postMethod ∧ selfHeadObj X w w' o = true then
            match postedHead args with
            | some h => [⟨h.1, h.2, m, pos⟩]
            | none => []
          else []
      | _ => []

/-- Every self-head post a page carries, in log order, each at its own position (`w` the World
before the page, `w'` after it, `ts` the page's steps). -/
def selfPosts (X : Ctx D) (w w' : World D) (ts : List (Kernel.Step D × D)) : List (Post D) :=
  (ts.zipIdx w.steps).flatMap fun q => stepPosts X w w' q.2 q.1.1

/-- What is wrong with a post, if anything. -/
inductive PostFault
  /-- follow's fold reached the posted step count ON THIS PAGE with another chain -/
  | forked
  /-- the post names a step count its own position had not reached: no member of THIS history
  can have held that head when the post was admitted -/
  | beyond
  deriving DecidableEq, Repr

/-- A post's fault: `beyond` when it names a step past its own position (`pos < steps`), else
`forked` when the walk from follow's position before the page reaches its step count with another
chain. A post at or behind follow's position is the Store's to compare (`behindPosts`). -/
def postFault (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (p : Post D) : Option PostFault :=
  if p.pos < p.steps then some .beyond
  else if anchorCheck X.env p.steps p.chain w.steps w.chain ts = .forked then some .forked else none

/-- The first post of the page, in log order, with a fault. Since every post's position is inside
the page, a post at no fault is behind follow's position or reached by the walk with its own chain
(`Proofs.Head.pagePostFault_none`): no post escapes comparison. -/
@[irreducible] def pagePostFault (X : Ctx D) (w w' : World D) (ts : List (Kernel.Step D × D)) :
    Option (PostFault × Post D) :=
  (selfPosts X w w' ts).findSome? fun p => (postFault X w ts p).map (·, p)

/-- The self-head posts a page carries at a step count follow was already AT or past before the
page (`steps ≤ w.steps`): exactly the ones `anchorCheck` cannot reach from follow's position (it
compares the step counts `w.steps + 1 …` the page walks). Follow's own Store answers them
(`forkedBehindPost`, `Host.Follow.loop`: T2b'). -/
def behindPosts (X : Ctx D) (w w' : World D) (ts : List (Kernel.Step D × D)) : List (Post D) :=
  (selfPosts X w w' ts).filter fun p => decide (p.steps ≤ w.steps)

/-- The first behind post whose chain is not the chain follow's own history holds at its step count
(`chainAt s`, read from follow's Store: `Host.Deployed.chainKept`). A step the Store no longer keeps
(`chainAt s = none`) is not compared: the Store cannot say. -/
def forkedBehindPost (posts : List (Post D)) (chainAt : Nat → Option ByteArray) : Option (Post D) :=
  posts.find? fun p => match chainAt p.steps with
    | some c => c ≠ p.chain
    | none => false

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
`uncertified`: the next landing). [Out of date: `host serve --certify` produces one, every `log` page
carries one (`pageCertified`), and `adopt` consumes one (`certifiesWorld`).] What a verifier learns from `certified = .ok` is `Proofs.Head.certified_ok`; what two
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
  /-- the authority names nobody (threshold 0, `Authority.none`): it certifies nothing, so no
  certificate under it is taken, however many signatures it carries (PROTOCOL-77.1) -/
  | noAuthority
  /-- it verifies, but certifies another head than the World it is checked against (PROTOCOL-77.1:
  a stale certificate of an older base, or a forged World under a genuine one) -/
  | otherHead
  deriving DecidableEq, Repr

def CertRefusal.name : CertRefusal → String
  | .badCertificate => "badCertificate" | .otherWorld => "otherWorld" | .unlisted _ => "unlisted"
  | .repeated _ => "repeated" | .badCertifySignature _ => "badCertifySignature"
  | .belowThreshold .. => "belowThreshold" | .noAuthority => "noAuthority" | .otherHead => "otherHead"

/-- The constructor's index, the thing a name must determine (`Proofs.Head.CertRefusal.name_injective`). -/
def CertRefusal.tag : CertRefusal → Nat
  | .badCertificate => 0 | .otherWorld => 1 | .unlisted _ => 2 | .repeated _ => 3
  | .badCertifySignature _ => 4 | .belowThreshold .. => 5 | .noAuthority => 6 | .otherHead => 7

/-- One refusal of every name (arguments are placeholders; a name drops them). -/
def CertRefusal.all : List CertRefusal :=
  [.badCertificate, .otherWorld, .unlisted 0, .repeated 0, .badCertifySignature 0, .belowThreshold 0 0,
   .noAuthority, .otherHead]

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

/-- Decode and verify under `auth`: the authority names somebody (`noAuthority` otherwise: a
threshold of 0 would take a certificate with no signature), the certificate is for `origin`, and at
least `auth.threshold` distinct listed certifiers each signed its certified bytes under `domCertify`. The one path every
party that trusts a head without a World (a thin joiner, a foreign World, a phone) will run. -/
def certified (X : Ctx D) (auth : Authority) (origin : D) (b : ByteArray) :
    Except CertRefusal (Certificate D) :=
  if auth.threshold = 0 then .error .noAuthority else
  match certificateOfBytes X b with
  | none => .error .badCertificate
  | some c =>
    if c.head.origin ≠ origin then .error .otherWorld
    else match certifySigners X auth (certifyMessage c.certified) c.sigs [] with
      | .error r => .error r
      | .ok signers =>
          if signers.length < auth.threshold then .error (.belowThreshold signers.length auth.threshold)
          else .ok c

/-- **A World's head, certified under the World's own authority** (PROTOCOL-77.1): what a member
adopting a base asks of the writer's certificate `b`. Under an authority that names nobody nothing
is asked (`ok`: every World today, `Authority.none`); otherwise `b` verifies under that authority
(`certified`) and certifies exactly `headOf w` (`otherHead` else). A World that carries no single
authority cell is refused `noAuthority` (no honest fold reaches one: `authorityOf_honest_fold`). The
authority is read off `w`, so the caller must already trust `w`'s bytes (a pin binds them); what
this adds is the writer's own signature on the head, non-repudiable to anyone holding the genesis. -/
def certifiesWorld (X : Ctx D) (w : World D) (b : ByteArray) : Except CertRefusal Unit :=
  match authorityOf w with
  | none => .error .noAuthority
  | some auth =>
      if auth.threshold = 0 then .ok ()
      else match certified X auth w.origin b with
        | .error r => .error r
        | .ok c => if c.head = headOf X.env w then .ok () else .error .otherHead

/-! ## The writer's certified head on a log page (PROTOCOL-81; DESIGN-TRUST T3d)

A `log` page carries the writer's certificate of its newest base's head. Follow verifies it under
the authority of its OWN World, the fold from the start it already trusts (never the page's word:
KERNEL-69.2, `authorityOf_honest_fold`), and compares the certified chain with its own fold at that
step count, as it compares a member's self-head post. A mismatch is the writer's own signature on a
head of another history: attributable evidence of a fork, which no member's post can be. What it does
NOT show: that the certified head is lawful (a writer may sign one fabricated head per step count and
never equivocate); follow's re-execution is what makes its own fold lawful. -/

/-- The head a log page's certificate `b` certifies, as `(steps, chain bytes)`, when it verifies
under the authority of follow's World `w` for `w`'s origin (`certified`). `none` for no certificate,
an authority naming nobody, or a certificate that does not verify (not the writer's signature, so
evidence of nothing). -/
def pageCertified (X : Ctx D) (w : World D) (b : ByteArray) : Option (Nat × ByteArray) :=
  if b.isEmpty then none else
  match authorityOf w with
  | none => none
  | some auth =>
    match certified X auth w.origin b with
    | .ok c => some (c.head.steps, X.env.bytes c.head.chain)
    | .error _ => none

/-- The certified head's step count when follow's fold reached it ON THIS PAGE with another chain
(`anchorCheck` from follow's position `w` before the page, as `pagePostFault` walks). A head at a
position follow was already past is `behindCertified`'s (its own Store answers it); one past the
page is not compared here. -/
@[irreducible] def forkedCertified (X : Ctx D) (w : World D) (ts : List (Kernel.Step D × D)) (b : ByteArray) :
    Option Nat :=
  match pageCertified X w b with
  | some (s, c) => if anchorCheck X.env s c w.steps w.chain ts = .forked then some s else none
  | none => none

/-- Why a page's certificate is not the writer's, under an authority that certifies (PROTOCOL-84): it
is absent (`absent`: a relay stripped it, or the writer has no producer), or `certified` refuses it
by name. `none` when it verifies, or when the authority certifies nothing (`Authority.none`: an empty
certificate is the honest shape there). Read under follow's OWN World's authority, as `pageCertified`
reads it. -/
def pageUncertified (X : Ctx D) (w : World D) (b : ByteArray) : Option String :=
  match authorityOf w with
  | none => none
  | some auth =>
    if auth.threshold = 0 then none
    else if b.isEmpty then some "absent"
    else match certified X auth w.origin b with
      | .ok _ => none
      | .error r => some r.name

/-- The certified head when it sits AT or behind follow's position before the page (`steps ≤
w.steps`): `anchorCheck` cannot reach it, follow's own Store answers it (`Host.Follow.behindOr`). -/
def behindCertified (X : Ctx D) (w : World D) (b : ByteArray) : Option (Nat × ByteArray) :=
  (pageCertified X w b).filter fun p => decide (p.1 ≤ w.steps)

end Nanodregg.Protocol.Head
