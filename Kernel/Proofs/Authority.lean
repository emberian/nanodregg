/-
# Kernel.Proofs.Authority — who may do what, as theorems about `receive`

* A grant chain: `principalOf … (some g) = .ok p` means a chain of live, pinned grant links from
  `g`, each aimed at the object, held by the next agent and carrying the right, ending at a root
  whose issuer is `p` (`Chain`).
* `write` and `law` are admitted only for the object's owner, directly or through such a chain
  rooted at the owner (the row plant "receiver skips the grant check on write" breaks this).
* Every call but `rotate` is signed by its member's CURRENT key; `rotate` only to the
  PRECOMMITTED key.
* Enrolment is a right (KERNEL-16): a derived `enroll` comes through a World grant chain carrying
  `enroll` and spends one of its own grant's count, appending the count left to its ledger; a grant
  on the World or carrying `enroll` always has a parent (so every such chain ends at a founder's
  genesis grant), and an enrolment count is carved out of what its parent has left.
-/
import Kernel.Proofs.Receive

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-- A grant chain from `g` for `agent` reaching principal `p`. -/
inductive Chain (X : Ctx D) (look : Pinned D) (obj : D) (right : Right) : Bool → D → D → D → Prop
  | root {pub : Bool} {g agent issuer : D} {cell : Cell} :
      readKind look g kindGrant = .ok cell →
      slotDigest X g cell grantTarget = .ok obj →
      granteeHolds X look g cell agent pub = .ok () →
      (cell.slots.get (rightKey right)).isSome = true →
      slotDigest X g cell grantIssuer = .ok issuer →
      cell.slots.get grantParent = none →
      Chain X look obj right pub g agent issuer
  | link {pub : Bool} {g agent issuer parent p : D} {cell : Cell} {pb : ByteArray} :
      readKind look g kindGrant = .ok cell →
      slotDigest X g cell grantTarget = .ok obj →
      granteeHolds X look g cell agent pub = .ok () →
      (cell.slots.get (rightKey right)).isSome = true →
      slotDigest X g cell grantIssuer = .ok issuer →
      cell.slots.get grantParent = some pb →
      X.digestOf pb = some parent →
      Chain X look obj right false parent issuer p →
      Chain X look obj right pub g agent p

omit [Ord D] in
theorem walk_chain {X : Ctx D} {look : Pinned D} {obj : D} {right : Right} :
    ∀ {pub : Bool} {fuel : Nat} {g agent p : D}, walk X look obj right pub fuel g agent = .ok p →
      Chain X look obj right pub g agent p
  | _, 0, _, _, _, h => by simp [walk] at h
  | _, fuel + 1, g, agent, p, h => by
      unfold walk at h
      simp only [except_bind_ok] at h
      obtain ⟨cell, hc, target, ht, ⟨⟩, hteq, ⟨⟩, hg, ⟨⟩, hr, issuer, hi, h⟩ := h
      rw [req_ok, decide_eq_true_eq] at hteq
      rw [req_ok] at hr
      subst hteq
      split at h
      · rename_i hp
        simp only [Except.ok.injEq] at h
        subst h
        exact .root hc ht hg hr hi hp
      · rename_i pb hp
        split at h
        · simp at h
        · rename_i parent hd
          exact .link hc ht hg hr hi hp hd (walk_chain h)

omit [Ord D] in
/-- **Write authority.** A derived `write` comes from the object's owner acting, or from an actor
holding a grant chain for `mutate` whose root issuer is the owner. -/
theorem write_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj : D}
    {edits : List (Nat × Option ByteArray)} {via : Option D} {d : Draft D}
    (h : write X look c a obj edits via = .ok d) :
    ∃ cell owner, readKind look obj kindObject = .ok cell ∧
      slotDigest X obj cell slotOwner = .ok owner ∧
      (via = none ∧ a.actor = owner ∨
        ∃ g, via = some g ∧ Chain X look obj .mutate true g a.actor owner) := by
  unfold write at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, _, _, ⟨⟩, _, principal, ha, _⟩ := h
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨cell, p, hc, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- What holding a link means (KERNEL-26): the link names the agent, or it names the World and the
agent's member cell is pinned and live. -/
theorem granteeHolds_ok {X : Ctx D} {look : Pinned D} {g : D} {cell : Cell} {agent : D} {pub : Bool}
    (h : granteeHolds X look g cell agent pub = .ok ()) :
    slotDigest X g cell grantGrantee = .ok agent ∨
      pub = true ∧ slotDigest X g cell grantGrantee = .ok (worldId X) ∧
        ∃ m, readKind look agent kindMember = .ok m := by
  unfold granteeHolds at h
  simp only [except_bind_ok] at h
  obtain ⟨grantee, hg, h⟩ := h
  split at h
  · rename_i he; subst he; exact .inl hg
  · split at h
    · rename_i _ hw
      obtain ⟨hp, hw⟩ := hw
      subst hw
      cases hr : readKind look agent kindMember with
      | error e => rw [hr] at h; simp [Except.map] at h
      | ok m => exact .inr ⟨hp, hg, m, rfl⟩
    · simp at h

omit [Ord D] in
/-- **Invoke authority** (KERNEL-25, the twin of `write_authorized`). A derived `invoke` comes from
the object's owner, or from an agent holding a grant chain for `invoke method` whose root issuer is
the owner; a stranger to the object without a grant is refused `noGrant`. The laws only refine. -/
theorem invoke_authorized {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D} {wk : Walk D}
    {actor obj : D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {r : Draft D × Walk D}
    (h : invoke X look rv c sub wk actor obj method args budget via = .ok r) :
    ∃ cell owner, readKind look obj kindObject = .ok cell ∧
      slotDigest X obj cell slotOwner = .ok owner ∧
      (via = none ∧ actor = owner ∨
        ∃ g, via = some g ∧ Chain X look obj (.invoke method) true g actor owner) := by
  unfold invoke at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, _, ⟨_, _, _⟩, hrun, _⟩ := h
  unfold invokeRun at hrun
  simp only [except_bind_ok] at hrun
  obtain ⟨cell, hc, _, _, _, _, principal, ha, _⟩ := hrun
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨cell, p, hc, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- **A stranger to the object is refused by name** (KERNEL-25). A member who is not a programmed
object's owner and invokes it with no grant is refused `noGrant obj`, whatever the laws say: the
refusal comes before any method runs or any law judges. -/
theorem invoke_stranger_noGrant {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {sub : Sub D}
    {wk : Walk D} {actor obj p owner : D} {method : Nat} {args : ByteArray} {budget : Nat}
    {cell : Cell} (hv : obj ∉ wk.visited)
    (hc : readKind look obj kindObject = .ok cell) (hp : packageOf X obj cell = .ok (some p))
    (ho : slotDigest X obj cell slotOwner = .ok owner) (hne : actor ≠ owner) :
    invoke X look rv c sub wk actor obj method args budget none = .error (.noGrant obj) := by
  simp [invoke, invokeRun, hv, hc, hp, requireMethods, ownerAuthority, ho, principalOf, req, hne, bind,
    Except.bind]

omit [Ord D] in
/-- **The laws only refine** (KERNEL-25). The authority gate does not read the program: under any
law program `P` the owner-authority verdict is the same, so no law can admit an invoke (or a write,
or a law replacement) the kernel refused; laws can only refuse more. -/
theorem ownerAuthority_program_free (X : Ctx D) (P : Program D) (look : Pinned D) (actor : D)
    (obj : D) (cell : Cell) (right : Right) (via : Option D) :
    ownerAuthority { X with program := P } look actor obj cell right via =
      ownerAuthority X look actor obj cell right via := rfl

omit [Ord D] in
/-- **Law authority.** Replacing a data object's laws needs the same owner authority. -/
theorem law_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj : D} {laws : List D}
    {via : Option D} {d : Draft D} (h : law X look c a obj laws via = .ok d) :
    ∃ cell owner, readKind look obj kindObject = .ok cell ∧
      slotDigest X obj cell slotOwner = .ok owner ∧
      (via = none ∧ a.actor = owner ∨
        ∃ g, via = some g ∧ Chain X look obj .mutate true g a.actor owner) := by
  unfold law at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, _, _, ⟨⟩, _, principal, ha, _⟩ := h
  unfold ownerAuthority at ha
  simp only [except_bind_ok] at ha
  obtain ⟨owner, ho, p, hp, ⟨⟩, hpo, _⟩ := ha
  rw [req_ok, decide_eq_true_eq] at hpo
  subst hpo
  refine ⟨cell, p, hc, ho, ?_⟩
  cases via with
  | none => left; simp [principalOf] at hp; exact ⟨rfl, hp⟩
  | some g => right; exact ⟨g, rfl, walk_chain hp⟩

omit [Ord D] in
/-- **Adoption judges the state** (KERNEL-6 as built by KERNEL-27/LANG-24, KERNEL-57). A derived
`law` turn was judged twice over the object's UNCHANGED state: by the laws in force, on
`relaw laws'` (the authority to change laws), and by every ADDED law (`laws'` less the laws in
force), on `adopt laws'` (each added law's base case: the state it is adopted over). A kept law is
not re-judged on `adopt` (LANG-4's amendment). The authority half is `law_authorized`; the
refusal half is `law_adopt_refused`; what `adopt` means for each Std law is LANG's
(`Lang.Proofs.Std.bounded_spec`, `quorum_adopt_fresh`, `windowed_fresh`, `machine_adopt`), reached
from a judge verdict by `Lang.Proofs.Receiver.judgeOne_admits`. -/
theorem law_judged {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj : D} {laws' : List D}
    {via : Option D} {d : Draft D} (h : law X look c a obj laws' via = .ok d) :
    ∃ cell principal laws, readKind look obj kindObject = .ok cell ∧
      packageOf X obj cell = .ok none ∧
      ownerAuthority X look a.actor obj cell .mutate via = .ok principal ∧
      checkLaws look laws' = .ok () ∧ lawsOf X obj cell = .ok laws ∧
      X.program.judge look none laws (stateOf cell) (stateOf cell)
        (reqOf c.unsigned obj principal (.relaw laws')) = .ok () ∧
      X.program.judge look none (laws'.filter fun l => decide (l ∉ laws)) (stateOf cell) (stateOf cell)
        (reqOf c.unsigned obj principal (.adopt laws')) = .ok () ∧
      d.effects = writeOf obj (diffOps (lawSlotsOf cell) (lawSlots X laws')) := by
  unfold law at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, pkg, hp, ⟨⟩, hn, principal, ha, ⟨⟩, hcl, laws, hl, ⟨⟩, hrel, ⟨⟩, had, h⟩ := h
  rw [req_ok] at hn
  cases pkg with
  | some _ => simp at hn
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨cell, principal, laws, hc, hp, ha, hcl, hl, hrel, had, rfl⟩

omit [Ord D] in
/-- **An added law that refuses the state is never installed, by its own name** (the tooth of
`law_judged`). Past the authority and the laws in force, a `law` turn whose ADDED laws refuse
`adopt laws'` over the unchanged state is refused with exactly that refusal (for LANG's program,
`lawDenied <law> <its reason>`: `Lang.Proofs.StdTeeth.bounded_adopt` is `bounded total ≤ 100`
refusing adoption over a total of 500). -/
theorem law_adopt_refused {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj principal : D}
    {laws laws' : List D} {via : Option D} {cell : Cell} {e : Refusal D}
    (hc : readKind look obj kindObject = .ok cell) (hp : packageOf X obj cell = .ok none)
    (ha : ownerAuthority X look a.actor obj cell .mutate via = .ok principal)
    (hcl : checkLaws look laws' = .ok ()) (hl : lawsOf X obj cell = .ok laws)
    (hrel : X.program.judge look none laws (stateOf cell) (stateOf cell)
      (reqOf c.unsigned obj principal (.relaw laws')) = .ok ())
    (had : X.program.judge look none (laws'.filter fun l => decide (l ∉ laws)) (stateOf cell)
      (stateOf cell) (reqOf c.unsigned obj principal (.adopt laws')) = .error e) :
    law X look c a obj laws' via = .error e := by
  simp only [law, hc, hp, ha, hcl, hl, hrel, had, req, bind, Except.bind, Option.isNone_none, if_true]

/-- **Current key.** Every derived call that is not a rotation is signed by a key its member cell
holds as current. -/
theorem key_current {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {t : Turn D}
    (h : receiveWith X look rv c = .ok t) (hnr : ∀ k n, c.unsigned.body ≠ .rotate k n) :
    ∃ m, readKind look c.unsigned.member kindMember = .ok m ∧
      m.slots.get slotKey = some c.unsigned.key := by
  have hk := receiveWith_key h
  unfold keyRule at hk
  split at hk
  · rename_i k n hb; exact absurd hb (hnr k n)
  · unfold checkKey at hk
    split at hk
    · simp at hk
    · simp at hk
    · rename_i m hm
      exact ⟨m, hm, by simpa [req_ok] using hk⟩

omit [Ord D] in
/-- **Pre-rotation.** A derived rotation moves the member to a key whose digest it had
precommitted, and is signed by that key. -/
theorem rotate_precommitted {X : Ctx D} {look : Pinned D} {c : Call D} {key : ByteArray} {next : D}
    {d : Draft D} (h : rotate X look c key next = .ok d) :
    c.unsigned.key = key ∧ ∃ m, readKind look c.unsigned.member kindMember = .ok m ∧
      slotDigest X c.unsigned.member m slotNext = .ok (nextKeyDigest X key) := by
  unfold rotate at h
  simp only [except_bind_ok] at h
  obtain ⟨m, hm, ⟨⟩, hkey, committed, hc, ⟨⟩, heq, _⟩ := h
  rw [req_ok, decide_eq_true_eq] at hkey heq
  exact ⟨hkey, m, hm, heq ▸ hc⟩

omit [Ord D] [DecidableEq D] in
/-- A spend of an enrolment count: within what the grant's ledger says is left, appending the
remainder at the ledger's next index (nothing for a spend of none). -/
theorem spendEnroll_ok {g : D} {cell : Cell} {units : Nat} {short : Refusal D}
    {ef : Option (D × Act)} (h : spendEnroll g cell units short = .ok ef) :
    ∃ i left, enrollLeft g cell = .ok (i, left) ∧ units ≤ left ∧
      ef = if units = 0 then none else some (g, .write [.set (enrollBase + i) (countBytes (left - units))]) := by
  unfold spendEnroll at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨i, left⟩, hl, ⟨⟩, hu, h⟩ := h
  rw [req_ok, decide_eq_true_eq] at hu
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨i, left, hl, hu, h.symm⟩

omit [Ord D] in
/-- **Enrolment authority** (KERNEL-16, the twin of `write_authorized`). A derived enrolment comes
from a sponsor holding a World grant chain that carries `enroll`, whose own grant had a count left,
and the Turn spends one of it: its effect appends `left - 1` to that grant's ledger.
A PUBLIC ENROLMENT POOL is possible (KERNEL-26): a World grant carrying `enroll n` whose grantee is
the World is held by every enrolled member, so any member may sponsor through it until its count
is spent; it is still carved from a founder's count (`grant_carves`) and rooted (`grant_rooted`). -/
theorem enroll_authorized {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {key : ByteArray}
    {next : D} {possession : ByteArray} {via : D} {d : Draft D}
    (h : enroll X look c a key next possession via = .ok d) :
    (∃ p, Chain X look (worldId X) (.enroll 0) true via a.actor p) ∧
      ∃ cell i left, readKind look via kindGrant = .ok cell ∧ enrollLeft via cell = .ok (i, left) ∧
        0 < left ∧ X.verify key (possessionMessage X a.actor next key) possession = true ∧
        d.effects = [(via, .write [.set (enrollBase + i) (countBytes (left - 1))])] ∧ d.nullifiers = [] := by
  unfold enroll at h
  simp only [except_bind_ok] at h
  obtain ⟨p, hw, cell, hc, ef, hs, ⟨⟩, hv, h⟩ := h
  obtain ⟨i, left, hl, hu, rfl⟩ := spendEnroll_ok hs
  rw [req_ok] at hv
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨⟨p, walk_chain hw⟩, cell, i, left, hc, hl, hu, hv, by simp, rfl⟩

omit [Ord D] in
/-- **World rights are rooted at genesis.** A derived grant on the World, or one carrying an
enrolment right, has a parent: no call roots one, so every such chain ends at a root that genesis
placed (a founder's). -/
theorem grant_rooted {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {target grantee : D}
    {rights : List Right} {parent : Option D} {d : Draft D}
    (h : grant X look c a target grantee rights parent = .ok d)
    (hw : target = worldId X ∨ rights.any isEnroll = true) : parent.isSome = true := by
  cases parent with
  | some _ => rfl
  | none =>
      unfold grant at h
      simp only [except_bind_ok] at h
      obtain ⟨_, _, ef, hp, _⟩ := h
      simp only [checkParent, except_bind_ok] at hp
      obtain ⟨⟨⟩, hr, _⟩ := hp
      rw [req_ok] at hr
      rcases hw with hw | hw <;> simp_all

omit [Ord D] in
/-- **Enrolment counts attenuate.** A derived grant carrying `enroll` carves its count out of its
parent's: the parent is a grant the signer holds on the same target, it had at least that much
left, and the Turn's effect is the parent's spend. -/
theorem grant_carves {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {target grantee p : D}
    {rights : List Right} {d : Draft D}
    (h : grant X look c a target grantee rights (some p) = .ok d) (he : rights.any isEnroll = true) :
    ∃ pc ef, readKind look p kindGrant = .ok pc ∧ slotDigest X p pc grantTarget = .ok target ∧
      slotDigest X p pc grantGrantee = .ok a.actor ∧
      spendEnroll p pc (enrollUnits rights) (.grantWidens p) = .ok ef ∧
      d.effects = ef.toList ∧ d.nullifiers = [] := by
  unfold grant at h
  simp only [except_bind_ok] at h
  obtain ⟨_, _, ef, hp, h⟩ := h
  simp only [checkParent, except_bind_ok, he, if_true] at hp
  obtain ⟨pc, hpc, pt, hpt, ⟨⟩, hteq, pg, hpg, ⟨⟩, hgeq, ⟨⟩, _, hs⟩ := hp
  rw [req_ok, decide_eq_true_eq] at hteq hgeq
  subst hteq; subst hgeq
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨pc, ef, hpc, hpt, hpg, hs, rfl, rfl⟩

end Nanodregg.Kernel.Receive
