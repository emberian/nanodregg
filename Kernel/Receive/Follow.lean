/-
# Kernel.Receive.Follow — who may follow the World, and the founders' genesis

The whole log is served only to a member holding a live World grant carrying `observe` whose
chain reaches a founder's root (PROTOCOL-3). Revoking any link revokes everything issued through
it. The founders' root grants (observe, enrol up to `enrollMax`) and member cells are the genesis
World; nothing else is trusted without a signature. `genesis` refuses, by name, an input past the
raw codec's bounds (`GenesisRefusal`), so the origin commits to everything genesis was made from.
-/
import Kernel.Receive.Derive
import Codec.Raw

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

def digestAt (X : Ctx D) (cell : Cell) (key : Nat) : Option D := cell.slots.get key >>= X.digestOf

/-- HOST's gate for `log` and whole-World `read`: `g` is a live World grant held by `member`
carrying `observe`, every link up to a founder's genesis grant live too. The same `walk` as every
other right, over the whole World (a follower's request pins nothing). -/
def mayFollow (X : Ctx D) (w : World D) (member g : D) : Bool :=
  match walk X (fun c => .ok (w.live X.env c)) (worldId X) .observe true grantDepthMax g member with
  | .ok _ => true
  | .error _ => false

def domFounder : String := "nanodregg/kernel/founder/v2"
def domFounderGrant : String := "nanodregg/kernel/founder-grant/v2"
def domOrigin : String := "nanodregg/kernel/origin/v3"

/-- Who may certify a position as the World's, and how many of them must (KERNEL-69; DESIGN-TRUST
§1.2): fixed at genesis, committed in the origin, carried in the World as one ROM cell
(`authorityCell`). A certificate names its signers as indices into `certifiers`
(`Protocol.Head.certified`). -/
structure Authority where
  certifiers : List ByteArray
  threshold : Nat
  deriving DecidableEq, Repr

/-- Nobody certifies: every World that names nobody. `certified` refuses a certificate under it
`noAuthority` before it reads a signer (PROTOCOL-77.1). -/
def Authority.none : Authority := ⟨[], 0⟩

/-- What a genesis is made from, as CODEC's raw combinators write it: the name, HOST's nonce, the
allowance, each founder's key and next-key digest bytes, in order, then the authority's certifier
keys, in order, and its threshold. -/
abbrev GenesisInput := ByteArray × ByteArray × Nat × List (ByteArray × ByteArray) × List ByteArray × Nat

open Nanodregg.Codec Nanodregg.Codec.Stream in
def genesisInput : Stream GenesisInput :=
  product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax) (product nat64
    (product (rawList Bounds.eventBytesMax (product (rawBytes Bounds.eventBytesMax) (rawBytes Bounds.eventBytesMax)))
      (product (rawList Bounds.eventBytesMax (rawBytes Bounds.eventBytesMax)) nat64))))

def inputOf (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : GenesisInput :=
  (name, nonce, allowance, founders.map (fun f => (f.1, X.env.bytes f.2)), auth.certifiers, auth.threshold)

/-- What a carry is made from (KERNEL-29, KERNEL-79), as CODEC's raw combinators write it: the name,
HOST's nonce, the exported World's origin bytes, the root bytes of the four carried tries as exported
(cells, rows, journal, window), the allowance, the height, then the STATED authority's certifier keys,
in order, and its threshold. Fixed-size but for the authority, like a genesis input: a carried
World's start (`CarryStart`) is this record, so a stranger holding it recomputes the origin and
checks a certificate under the authority it states (PROTOCOL-85). -/
abbrev CarryInput :=
  ByteArray × ByteArray × ByteArray × ByteArray × ByteArray × ByteArray × ByteArray × Nat × Nat ×
    List ByteArray × Nat

open Nanodregg.Codec Nanodregg.Codec.Stream in
def carryInput : Stream CarryInput :=
  product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
    (product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
      (product (rawBytes Bounds.eventBytesMax) (product (rawBytes Bounds.eventBytesMax)
        (product (rawBytes Bounds.eventBytesMax) (product nat64 (product nat64
          (product (rawList Bounds.eventBytesMax (rawBytes Bounds.eventBytesMax)) nat64)))))))))

open Nanodregg.Codec Nanodregg.Codec.Stream in
/-- A World's identity input: a genesis's or a carry's, under one domain, the case tagged by one
byte, so a carry's origin is never a genesis's without a collision of the origin hash
(`carry_origin_ne_genesis`). -/
def originInput : Stream (GenesisInput ⊕ CarryInput) := sum genesisInput carryInput

/-- The World's identity (KERNEL-24): the digest of everything its genesis is made from, the
authority included (KERNEL-69). -/
def originOf (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : D :=
  X.env.hash domOrigin (originInput.bytes (.inl (inputOf X name nonce allowance founders auth)))

/-- What `originOf` hashes. -/
def originPre (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : String × ByteArray :=
  (domOrigin, originInput.bytes (.inl (inputOf X name nonce allowance founders auth)))

/-- Founder ids are keyed by the World's ORIGIN, so two Worlds with one name share no member id. -/
def founderId (X : Ctx D) (origin : D) (i : Nat) : D :=
  X.env.hash domFounder (X.env.bytes origin ++ index32 i)

def founderGrantId (X : Ctx D) (origin : D) (i : Nat) : D :=
  X.env.hash domFounderGrant (X.env.bytes origin ++ index32 i)

def founderMember (X : Ctx D) (f : ByteArray × D) : Cell :=
  { kind := kindMember, discipline := .ram, slots := slotsOf [(slotKey, f.1), (slotNext, X.env.bytes f.2)] }

/-- A founder's root World grant: it may follow and enrol `enrollMax` members, and every World
right in the World is attenuated from one of these (`unrooted` refuses any other root). -/
def founderRoot (X : Ctx D) (member : D) : Cell :=
  { kind := kindGrant, discipline := .appendOnly,
    slots := slotsOf ([(grantTarget, X.env.bytes (worldId X)), (grantGrantee, X.env.bytes member),
      (grantIssuer, X.env.bytes member)] ++ rightSlots [.observe, .enroll enrollMax]) }

/-- Each founder's member cell, then its root World grant. -/
def founderEntries (X : Ctx D) (o : D) (founders : List (ByteArray × D)) : List (D × Entry) :=
  founders.zipIdx.flatMap fun p =>
    [(founderId X o p.2, .live (founderMember X p.1) 0),
     (founderGrantId X o p.2, .live (founderRoot X (founderId X o p.2)) 0)]

/-- The authority cell (KERNEL-69): ROM at its content id (`RomContent` holds of it as of every ROM
cell; `fold_rom` keeps it for the life of the World), kind `kindAuthority` (no receiver reads or
writes that kind): the threshold, the certifier count, then each certifier's key in order. -/
def authorityCell (a : Authority) : Cell :=
  { kind := kindAuthority, discipline := .rom,
    slots := slotsOf ([(slotThreshold, countBytes a.threshold), (slotCertifierCount, countBytes a.certifiers.length)] ++
      a.certifiers.zipIdx.map fun p => (certifierBase + p.2, p.1)) }

def authorityId (X : Ctx D) (a : Authority) : D := romIdOf X.env (authorityCell a)

/-- Everything a genesis World holds: each founder's member cell and root grant, then the authority. -/
def genesisEntries (X : Ctx D) (o : D) (founders : List (ByteArray × D)) (a : Authority) : List (D × Entry) :=
  founderEntries X o founders ++ [(authorityId X a, .live (authorityCell a) 0)]

/-- An authority cell read back: the threshold, then `count` keys from `certifierBase`. -/
def authorityOfCell (c : Cell) : Option Authority := do
  let t ← countOf (← c.slots.get slotThreshold)
  let n ← countOf (← c.slots.get slotCertifierCount)
  let ks ← (List.range n).mapM fun i => c.slots.get (certifierBase + i)
  pure ⟨ks, t⟩

/-- The authority a trie carries: its one live `kindAuthority` cell, read back. Two or none is
`none`: a verifier handed such a World refuses rather than choose (`authorityOf_genesis` is the
one every genesis World answers; `fold_rom` keeps that cell). -/
def authorityIn (t : Cells D) : Option Authority :=
  match t.toList.filterMap (fun p => match p.2 with
      | .entry (.live c _) => if c.kind = kindAuthority then some c else none
      | _ => none) with
  | [c] => authorityOfCell c
  | _ => none

/-- `authorityIn` of the World's trie (`authorityIn` reads a carried trie the same way, KERNEL-79). -/
def authorityOf (w : World D) : Option Authority := authorityIn w.trie

/-- The World a genesis builds, UNCHECKED: founders `(key, digest of next key)` as members, each
with a root World grant, and the authority cell; its origin commits to the name, HOST's `nonce`,
the allowance, the founders and the authority. Only `genesis` calls it on the request path; the
theorems about the genesis World are stated over it (`genesis_ok` says `genesis` returns exactly it). -/
def genesisWorld (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : World D :=
  let o := originOf X name nonce allowance founders auth
  let w := World.genesis X.env o allowance
  { w with trie := insertAll X.env w.trie (genesisEntries X o founders auth) }

/-- Why a genesis is refused (law 7): one constructor per clause of `GenesisFits`, in its order.
Past these bounds `genesisInput`'s raw codec truncates, so two different geneses would share one
origin with no hash collision (KERNEL-31). -/
inductive GenesisRefusal
  | nameTooLong
  | nonceTooLong
  | tooManyFounders
  /-- founder `index`'s key is longer than `Bounds.eventBytesMax` -/
  | founderKeyTooLong (index : Nat)
  /-- founder `index`'s next-key digest bytes are longer than `Bounds.eventBytesMax` -/
  | founderNextTooLong (index : Nat)
  /-- more certifiers than one cell's slots hold beside the two counts (KERNEL-69) -/
  | tooManyCertifiers
  /-- certifier `index`'s key is longer than `Bounds.eventBytesMax` -/
  | certifierTooLong (index : Nat)
  /-- certifier `index`'s key is an earlier certifier's: a quorum counts distinct keys -/
  | repeatedCertifier (index : Nat)
  /-- the threshold is zero with certifiers listed, or past their count: a quorum nobody, or nobody
  ever, meets -/
  | badThreshold
  /-- the allowance plus the genesis World's storage is not below 2^64: past it a retirement's credit
  could carry the allowance out of the World codec's `u64` (cv 01a14ba9-cbf4). Checked last, so the
  World is weighed only once every founder is within bounds. -/
  | allowanceTooLarge
  deriving DecidableEq, Repr

/-- The refusal's name on the wire: its constructor's, arguments dropped. -/
def GenesisRefusal.name : GenesisRefusal → String
  | .nameTooLong => "nameTooLong"
  | .nonceTooLong => "nonceTooLong"
  | .allowanceTooLarge => "allowanceTooLarge"
  | .tooManyFounders => "tooManyFounders"
  | .founderKeyTooLong _ => "founderKeyTooLong"
  | .founderNextTooLong _ => "founderNextTooLong"
  | .tooManyCertifiers => "tooManyCertifiers"
  | .certifierTooLong _ => "certifierTooLong"
  | .repeatedCertifier _ => "repeatedCertifier"
  | .badThreshold => "badThreshold"

/-- Each founder from index `i` on: its key, then its next-key digest bytes. -/
def checkFounders (X : Ctx D) : Nat → List (ByteArray × D) → Except GenesisRefusal Unit
  | _, [] => .ok ()
  | i, f :: rest => do
      req (f.1.size ≤ Bounds.eventBytesMax) (.founderKeyTooLong i)
      req ((X.env.bytes f.2).size ≤ Bounds.eventBytesMax) (.founderNextTooLong i)
      checkFounders X (i + 1) rest

/-- Each certifier from index `i` on: its key within bounds and not among the earlier ones (`seen`). -/
def checkCertifiers : Nat → List ByteArray → List ByteArray → Except GenesisRefusal Unit
  | _, _, [] => .ok ()
  | i, seen, k :: rest => do
      req (k.size ≤ Bounds.eventBytesMax) (.certifierTooLong i)
      req (seen.all fun s => decide (k ≠ s)) (.repeatedCertifier i)
      checkCertifiers (i + 1) (k :: seen) rest

/-- The authority is a quorum somebody can meet, within one cell (`Authority.Fits`,
`checkAuthority_ok`): the certifier count, the threshold, then each certifier. The ONE authority
check: a genesis (`checkGenesis`) and a carry (`checkCarry`, KERNEL-79) both run it. -/
def checkAuthority (auth : Authority) : Except GenesisRefusal Unit := do
  req (auth.certifiers.length + 2 ≤ Bounds.slotsPerCellMax) .tooManyCertifiers
  req (auth.threshold ≤ auth.certifiers.length ∧ (auth.threshold = 0 → auth.certifiers = [])) .badThreshold
  checkCertifiers 0 [] auth.certifiers

/-- The genesis input is within the raw codec's bounds and the authority is a quorum somebody can
meet (`GenesisFits`, `checkGenesis_ok`): the lengths first, then the authority (`checkAuthority`),
then each founder, and the World weighed last, once every one of them is within bounds. -/
def checkGenesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : Except GenesisRefusal Unit := do
  req (name.size ≤ Bounds.eventBytesMax) .nameTooLong
  req (nonce.size ≤ Bounds.eventBytesMax) .nonceTooLong
  req (founders.length ≤ Bounds.eventBytesMax) .tooManyFounders
  checkAuthority auth
  checkFounders X 0 founders
  req ((genesisWorld X name nonce allowance founders auth).weight + allowance < Bounds.counterLimit) .allowanceTooLarge

/-- THE genesis: refused by name outside `GenesisFits`, else `genesisWorld` (`genesis_ok`). -/
def genesis (X : Ctx D) (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D))
    (auth : Authority) : Except GenesisRefusal (World D) := do
  checkGenesis X name nonce allowance founders auth
  pure (genesisWorld X name nonce allowance founders auth)

/-! ## Carry (KERNEL-29, KERNEL-79): a new World from a carried state, under a stated authority -/

/-- What a carried World is made from, by roots (KERNEL-79): the name, HOST's nonce, the exported
World's origin, the roots of the four carried tries as exported (the cells with the OLD authority
cell in them: the carried World's provenance), the allowance and the height, and the authority the
operator STATES at the carry. The carried World's origin is the digest of exactly this
(`carryOriginOfStart`); a carried invitation signs it whole (PROTOCOL-85), so a joiner and a
stranger recompute the origin from it and read the authority off it. -/
structure CarryStart (D : Type) where
  name : ByteArray
  nonce : ByteArray
  fromOrigin : D
  trieRoot : D
  rowsRoot : D
  journalRoot : D
  windowRoot : D
  allowance : Nat
  height : Nat
  auth : Authority

/-- The carry start of a carried state `c`, from `fromOrigin`, under the stated authority `auth`. -/
def carryStartOf (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    CarryStart D :=
  { name, nonce, fromOrigin, trieRoot := c.trie.hashOf (trieSpec X.env), rowsRoot := c.rows.hashOf (rowSpec X.env),
    journalRoot := c.journal.hashOf (journalSpec X.env), windowRoot := c.refusals.hashOf (refusalSpec X.env),
    allowance := c.allowance, height := c.height, auth }

def carryInputOfStart (X : Ctx D) (s : CarryStart D) : CarryInput :=
  (s.name, s.nonce, X.env.bytes s.fromOrigin, X.env.bytes s.trieRoot, X.env.bytes s.rowsRoot,
    X.env.bytes s.journalRoot, X.env.bytes s.windowRoot, s.allowance, s.height, s.auth.certifiers, s.auth.threshold)

/-- A carried World's identity from its start: everything the carry is made from. -/
def carryOriginOfStart (X : Ctx D) (s : CarryStart D) : D :=
  X.env.hash domOrigin (originInput.bytes (.inr (carryInputOfStart X s)))

def carryInputOf (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    CarryInput :=
  carryInputOfStart X (carryStartOf X name nonce fromOrigin c auth)

/-- A carried World's identity: everything the carry is made from, the tries by their roots, the
stated authority whole. -/
def carryOriginOf (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) : D :=
  carryOriginOfStart X (carryStartOf X name nonce fromOrigin c auth)

/-- What `carryOriginOf` hashes. -/
def carryOriginPre (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    String × ByteArray :=
  (domOrigin, originInput.bytes (.inr (carryInputOf X name nonce fromOrigin c auth)))

/-- A live authority cell (KERNEL-69) at a cell slot: what a carry drops from the carried trie. -/
def liveAuthority : Slot D → Leaf → Bool
  | .cell _, .entry (.live c _) => c.kind == kindAuthority
  | _, _ => false

/-- The carried trie under the stated authority (KERNEL-79): every live authority cell dropped (the
old authority is the carried World's provenance, in its origin, never its authority), every other
entry kept as it is (cells, tombstones, spent nullifiers), and the stated authority's cell written
at its content id, as a genesis writes it. -/
def reauthor (X : Ctx D) (t : Cells D) (auth : Authority) : Cells D :=
  (Trie.retainAt (trieSpec X.env) (fun s l => !liveAuthority s l) [] t).insert (trieSpec X.env)
    (.cell (authorityId X auth)) (.entry (.live (authorityCell auth) 0))

/-- The stated authority's content id holds nothing in the carried trie but an authority cell: no
entry of another kind is overwritten by `reauthor` (such an entry is a collision of the ROM id). -/
def authorityFree (X : Ctx D) (t : Cells D) (auth : Authority) : Bool :=
  match t.get (trieSpec X.env) (.cell (authorityId X auth)) with
  | none => true
  | some l => liveAuthority (.cell (authorityId X auth)) l

/-- A meter key (KERNEL-68) of the window trie. -/
def isMeter : WindowSlot D → RefusalLeaf D → Bool
  | .meter _, _ => true
  | .refusal _, _ => false

/-- The carried window trie's meter (KERNEL-79): its meter leaves, nothing else. -/
def meterOnly (E : Env D) (r : Refusals D) : Refusals D :=
  Trie.retainAt (refusalSpec E) isMeter [] r

/-- The World a carry builds, UNCHECKED: the carried state under a new origin, its chain at
`genesisChain` of that origin, its authority the stated one (`reauthor`), its window trie the
carried meter (`meterOnly`). No founders: the members are the carried member cells, and their keys
sign the new World's calls (`Unsigned.world` = the new origin). -/
def carryWorld (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) : World D :=
  let o := carryOriginOf X name nonce fromOrigin c auth
  { trie := reauthor X c.trie auth, journal := c.journal, refusals := meterOnly X.env c.refusals, rows := c.rows,
    height := c.height, steps := c.height,
    chain := World.genesisChain X.env o, allowance := c.allowance, origin := o }

/-- Why a carry is refused (law 7): one constructor per clause of `CarryFits`, in its order. Past
these bounds `carryInput`'s raw codec truncates, so two different carries would share an origin. -/
inductive CarryRefusal
  | nameTooLong
  | nonceTooLong
  /-- the stated authority is not a quorum somebody can meet within one cell: genesis's own refusal
  (`checkAuthority`), by its name -/
  | authority (r : GenesisRefusal)
  /-- the stated authority's content id holds an entry of another kind in the carried trie -/
  | authorityTaken
  /-- a carried relation's parent is not a live cell of the re-authored trie (it was the old
  authority cell: no receiver writes one, so only a forged file reaches this) -/
  | rowsOrphaned
  /-- the carried allowance plus the carried World's cells' and rows' storage is not below 2^64
  (`fold_conserves` keeps that sum, so no later retirement can overflow the allowance; cv 01a14ba9-cbf4) -/
  | allowanceTooLarge
  | heightTooLarge
  /-- a digest's bytes (the exported origin, the four roots) are longer than `Bounds.eventBytesMax` -/
  | entryTooLarge
  deriving DecidableEq, Repr

def CarryRefusal.name : CarryRefusal → String
  | .nameTooLong => "nameTooLong"
  | .nonceTooLong => "nonceTooLong"
  | .authority r => r.name
  | .authorityTaken => "authorityTaken"
  | .rowsOrphaned => "rowsOrphaned"
  | .allowanceTooLarge => "allowanceTooLarge"
  | .heightTooLarge => "heightTooLarge"
  | .entryTooLarge => "entryTooLarge"

/-- The authority check under a carry's refusal. -/
def checkCarryAuthority (auth : Authority) : Except CarryRefusal Unit :=
  match checkAuthority auth with
  | .ok () => .ok ()
  | .error r => .error (.authority r)

/-- The carry input is within the raw codec's bounds, the stated authority passes genesis's own
check, and the World it makes is within the counters (`checkCarry_ok`). -/
def checkCarry (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    Except CarryRefusal Unit := do
  req (name.size ≤ Bounds.eventBytesMax) .nameTooLong
  req (nonce.size ≤ Bounds.eventBytesMax) .nonceTooLong
  checkCarryAuthority auth
  req (authorityFree X c.trie auth) .authorityTaken
  req (rowsParented X.env (reauthor X c.trie auth) c.rows) .rowsOrphaned
  req (cellsWeight (reauthor X c.trie auth) + rowsWeight c.rows + c.allowance < Bounds.counterLimit) .allowanceTooLarge
  req (c.height < Bounds.counterLimit) .heightTooLarge
  req ((X.env.bytes fromOrigin).size ≤ Bounds.eventBytesMax &&
      (X.env.bytes (c.trie.hashOf (trieSpec X.env))).size ≤ Bounds.eventBytesMax &&
      (X.env.bytes (c.rows.hashOf (rowSpec X.env))).size ≤ Bounds.eventBytesMax &&
      (X.env.bytes (c.journal.hashOf (journalSpec X.env))).size ≤ Bounds.eventBytesMax &&
      (X.env.bytes (c.refusals.hashOf (refusalSpec X.env))).size ≤ Bounds.eventBytesMax) .entryTooLarge

/-- THE carry: refused by name outside `CarryFits`, else `carryWorld` (`carry_ok`). `fromOrigin`
is the exported World's origin (its lineage, committed in the new origin); `auth` is the authority
the carried World bears, stated by the operator (KERNEL-79), never inherited. -/
def carry (X : Ctx D) (name nonce : ByteArray) (fromOrigin : D) (c : Carried D) (auth : Authority) :
    Except CarryRefusal (World D) := do
  checkCarry X name nonce fromOrigin c auth
  pure (carryWorld X name nonce fromOrigin c auth)

end Nanodregg.Kernel.Receive
