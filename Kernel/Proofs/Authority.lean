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
    {actor obj : D} {caller : Option D} {method : Nat} {args : ByteArray} {budget : Nat} {via : Option D}
    {r : Draft D × Walk D}
    (h : invoke X look rv c sub wk actor caller obj method args budget via = .ok r) :
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
    {wk : Walk D} {actor obj p owner : D} {caller : Option D} {method : Nat} {args : ByteArray} {budget : Nat}
    {cell : Cell} (hv : obj ∉ wk.visited)
    (hc : readKind look obj kindObject = .ok cell) (hp : packageOf X obj cell = .ok (some p))
    (ho : slotDigest X obj cell slotOwner = .ok owner) (hne : actor ≠ owner) :
    invoke X look rv c sub wk actor caller obj method args budget none = .error (.noGrant obj) := by
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
        (reqOf c.unsigned obj principal (.relaw laws') a.caller) = .ok () ∧
      X.program.judge look none (laws'.filter fun l => decide (l ∉ laws)) (stateOf cell) (stateOf cell)
        (reqOf c.unsigned obj principal (.adopt laws') a.caller) = .ok () ∧
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
      (reqOf c.unsigned obj principal (.relaw laws') a.caller) = .ok ())
    (had : X.program.judge look none (laws'.filter fun l => decide (l ∉ laws)) (stateOf cell)
      (stateOf cell) (reqOf c.unsigned obj principal (.adopt laws') a.caller) = .error e) :
    law X look c a obj laws' via = .error e := by
  simp only [law, hc, hp, ha, hcl, hl, hrel, had, req, bind, Except.bind, Option.isNone_none, if_true]

omit [Ord D] in
/-- **A write is judged on the state it leaves** (KERNEL-28, the twin of `law_judged`). A derived
`write` read the object's cell (a data object: no package), passed the owner authority, and the laws
in force (`lawsOf`) admitted, on `write`, the move from the cell's state to exactly the state the
edits make of it (`applyEdits`); its one effect is the write `diffOps` derives between the two. The
authority half is `write_authorized`; the refusal half is `write_law_refused`; what the World holds
after it is `Kernel.Proofs.WriteNext.write_next_slots`. -/
theorem write_judged {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj : D}
    {edits : List (Nat × Option ByteArray)} {via : Option D} {d : Draft D}
    (h : write X look c a obj edits via = .ok d) :
    ∃ cell principal laws, readKind look obj kindObject = .ok cell ∧
      packageOf X obj cell = .ok none ∧
      ownerAuthority X look a.actor obj cell .mutate via = .ok principal ∧
      lawsOf X obj cell = .ok laws ∧
      X.program.judge look none laws (stateOf cell) (applyEdits (stateOf cell) edits)
        (reqOf c.unsigned obj principal .write a.caller) = .ok () ∧
      d = ⟨[], writeOf obj (diffOps (stateOf cell) (applyEdits (stateOf cell) edits)), [], []⟩ := by
  unfold write at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, pkg, hp, ⟨⟩, hn, principal, ha, ⟨⟩, -, laws, hl, ⟨⟩, hj, h⟩ := h
  rw [req_ok] at hn
  cases pkg with
  | some _ => simp at hn
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨cell, principal, laws, hc, hp, ha, hl, hj, h.symm⟩

omit [Ord D] in
/-- **A write the laws refuse is refused by their refusal** (the tooth of `write_judged`). Past the
authority and the key bounds, a `write` whose laws in force refuse the move to the edited state is
refused with exactly that refusal (for LANG's program, `lawDenied <law> <its reason>`), so no write
turn is derived that the laws did not judge. -/
theorem write_law_refused {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {obj principal : D}
    {edits : List (Nat × Option ByteArray)} {via : Option D} {cell : Cell} {laws : List D} {e : Refusal D}
    (hc : readKind look obj kindObject = .ok cell) (hp : packageOf X obj cell = .ok none)
    (ha : ownerAuthority X look a.actor obj cell .mutate via = .ok principal)
    (hk : ∀ e ∈ edits, stateBase + e.1 < Bounds.slotKeyLimit) (hl : lawsOf X obj cell = .ok laws)
    (hj : X.program.judge look none laws (stateOf cell) (applyEdits (stateOf cell) edits)
      (reqOf c.unsigned obj principal .write a.caller) = .error e) :
    write X look c a obj edits via = .error e := by
  unfold write
  rw [forEx_ok.mpr (fun x hx => req_ok.mpr (decide_eq_true (hk x hx)))]
  simp only [hc, hp, ha, hl, hj, req, bind, Except.bind, Option.isNone_none, if_true]

/-- **Current key.** Every derived call that is not a rotation (a member's or a certifier's) is signed by a key its member cell
holds as current. -/
theorem key_current {X : Ctx D} {look : Pinned D} {rv : RowView D} {c : Call D} {t : Turn D}
    (h : receiveWith X look rv c = .ok t) (hnr : ∀ k n, c.unsigned.body ≠ .rotate k n)
    (hnc : ∀ i k n, c.unsigned.body ≠ .rotateCertifier i k n) :
    ∃ m, readKind look c.unsigned.member kindMember = .ok m ∧
      m.slots.get slotKey = some c.unsigned.key := by
  have hk := receiveWith_key h
  unfold keyRule at hk
  split at hk
  · rename_i k n hb; exact absurd hb (hnr k n)
  · rename_i i k n hb; exact absurd hb (hnc i k n)
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
/-- **Pre-rotation of a certifier** (KERNEL-79). A derived certifier rotation read the call's member
as an authority cell, is signed by `key`, `key` is certifier `index`'s committed successor
(`Authority.preRotated`: its digest the one committed there, no listed certifier's key), and its
one effect writes that certifier's key and next commitment at the authority cell; it bears nothing. -/
theorem rotateCertifier_ok {X : Ctx D} {look : Pinned D} {c : Call D} {index : Nat} {key : ByteArray}
    {next : D} {d : Draft D} (h : rotateCertifier X look c index key next = .ok d) :
    ∃ cell a, readKind look c.unsigned.member kindAuthority = .ok cell ∧ authorityOfCell cell = some a ∧
      c.unsigned.key = key ∧ a.preRotated X index key = true ∧
      d = ⟨[], [(c.unsigned.member, .write (rotationOps X index key next))], [], []⟩ := by
  unfold rotateCertifier at h
  simp only [except_bind_ok] at h
  obtain ⟨cell, hc, h⟩ := h
  cases ha : authorityOfCell cell with
  | none => rw [ha] at h; simp [bind, Except.bind] at h
  | some a =>
    rw [ha] at h
    simp only [except_bind_ok] at h
    obtain ⟨a', ha', ⟨⟩, hreq, hd⟩ := h
    cases ha'
    rw [req_ok, Bool.and_eq_true, decide_eq_true_eq] at hreq
    simp only [pure, Except.pure, Except.ok.injEq] at hd
    exact ⟨cell, a, hc, ha, hreq.1, hreq.2, hd.symm⟩

omit [Ord D] [DecidableEq D] in
/-- **A spend of a counted right** (KERNEL-60: one mechanism for enrolment, transfer and credit):
within what the grant's ledger at `base` says is left; for a spend of something, at a ledger index
the ledger still reads (`ledgerSpendsMax`), appending the remainder there; for a spend of none,
nothing. -/
theorem spendAt_ok {base : Nat} {g : D} {cell : Cell} {units : Nat} {short : Refusal D}
    {ef : Option (D × Act)} (h : spendAt base g cell units short = .ok ef) :
    ∃ i left, ledgerLeft base g cell = .ok (i, left) ∧ units ≤ left ∧
      (units = 0 ∧ ef = none ∨
        units ≠ 0 ∧ i ≤ ledgerSpendsMax ∧ ef = some (g, .write [.set (base + i) (countBytes (left - units))])) := by
  unfold spendAt at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨i, left⟩, hl, ⟨⟩, hu, h⟩ := h
  rw [req_ok, decide_eq_true_eq] at hu
  split at h
  · rename_i h0
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨i, left, hl, hu, .inl ⟨h0, h.symm⟩⟩
  · rename_i h0
    simp only [except_bind_ok] at h
    obtain ⟨⟨⟩, hi, h⟩ := h
    rw [req_ok, decide_eq_true_eq] at hi
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨i, left, hl, hu, .inr ⟨h0, hi, h.symm⟩⟩

omit [Ord D] [DecidableEq D] in
/-- A spend of an enrolment count: within what the grant's ledger says is left, appending the
remainder at the ledger's next index (nothing for a spend of none). -/
theorem spendEnroll_ok {g : D} {cell : Cell} {units : Nat} {short : Refusal D}
    {ef : Option (D × Act)} (h : spendEnroll g cell units short = .ok ef) :
    ∃ i left, enrollLeft g cell = .ok (i, left) ∧ units ≤ left ∧
      ef = if units = 0 then none else some (g, .write [.set (enrollBase + i) (countBytes (left - units))]) := by
  obtain ⟨i, left, hl, hu, hc⟩ := spendAt_ok h
  refine ⟨i, left, hl, hu, ?_⟩
  rcases hc with ⟨h0, rfl⟩ | ⟨h0, _, rfl⟩ <;> simp [h0]

omit [Ord D] in
/-- **Enrolment authority** (KERNEL-16, the twin of `write_authorized`). A derived enrolment comes
from a sponsor holding a World grant chain that carries `enroll`, whose own grant had a count left,
and the Turn spends one of it: its effect appends `left - 1` to that grant's ledger.
A PUBLIC ENROLMENT POOL is possible (KERNEL-26): a World grant carrying `enroll n` whose grantee is
the World is held by every enrolled member, so any member may sponsor through it until its count
is spent; it is still carved from a founder's count (`grant_carves`) and rooted (`grant_rooted`). -/
theorem enroll_authorized {X : Ctx D} {look : Pinned D} {a : At D} {key : ByteArray}
    {next origin : D} {join : ByteArray} {via : D} {d : Draft D}
    (h : enroll X look a key next origin join via = .ok d) :
    (∃ p, Chain X look (worldId X) (.enroll 0) true via a.actor p) ∧
      ∃ cell i left, readKind look via kindGrant = .ok cell ∧ enrollLeft via cell = .ok (i, left) ∧
        0 < left ∧ X.verify key (joinMessage X origin a.actor next key) join = true ∧
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
/-- **A member is its consent** (PROTOCOL-79). A derived enrolment's join verifies under the
enrolled key over `joinMessage` of the World it names (that World is the receiving one:
`receive_join_world`), and the one cell it bears is at `memberId`, the digest of that consent: a
second enrolment of the same consent bears the same id, which `World.checkCreates` refuses
`idTaken`. -/
theorem enroll_join_bound {X : Ctx D} {look : Pinned D} {a : At D} {key : ByteArray}
    {next origin : D} {join : ByteArray} {via : D} {d : Draft D}
    (h : enroll X look a key next origin join via = .ok d) :
    X.verify key (joinMessage X origin a.actor next key) join = true ∧
      d.creates.map Prod.fst = [memberId X origin a.actor next key] := by
  obtain ⟨_, _, _, _, _, _, _, hv, -, -⟩ := enroll_authorized h
  refine ⟨hv, ?_⟩
  unfold enroll at h
  simp only [except_bind_ok] at h
  obtain ⟨_, _, _, _, _, _, ⟨⟩, _, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

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
      obtain ⟨_, _, ⟨⟩, _, ef, hp, _⟩ := h
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
  obtain ⟨_, _, ⟨⟩, _, ef, hp, h⟩ := h
  simp only [checkParent, except_bind_ok, he, if_true] at hp
  obtain ⟨pc, hpc, pt, hpt, ⟨⟩, hteq, pg, hpg, ⟨⟩, hgeq, ⟨⟩, _, hs⟩ := hp
  rw [req_ok, decide_eq_true_eq] at hteq hgeq
  subst hteq; subst hgeq
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨pc, ef, hpc, hpt, hpg, hs, rfl, rfl⟩

omit [Ord D] in
/-- **What `checkRights` admits** (KERNEL-60's target typing, the reason no carve skips a ledger): at
most one counted kind, `enroll` only on the World, `transfer` and `credit` never on it, and caps an
account can hold. -/
theorem checkRights_ok {X : Ctx D} {target : D} {rights : List Right}
    (h : checkRights X target rights = .ok ()) :
    ¬ (rights.any isTransfer = true ∧ rights.any isCredit = true) ∧
      ¬ (rights.any isEnroll = true ∧ (rights.any isTransfer = true ∨ rights.any isCredit = true)) ∧
      (rights.any isEnroll = true → target = worldId X) ∧
      (rights.any isTransfer = true ∨ rights.any isCredit = true → target ≠ worldId X) ∧
      transferUnits rights ≤ capMax ∧ creditUnits rights ≤ capMax := by
  unfold checkRights at h
  simp only [except_bind_ok] at h
  obtain ⟨⟨⟩, h1, h2⟩ := h
  rw [req_ok] at h1 h2
  simp only [decide_eq_true_eq] at h2
  refine ⟨?_, ?_, ?_, ?_, h2.1, h2.2⟩ <;>
    cases ht : rights.any isTransfer <;> cases hc : rights.any isCredit <;> cases he : rights.any isEnroll <;>
    simp_all

omit [Ord D] in
/-- **Transfer caps attenuate** (the twin of `grant_carves`, KERNEL-60). A derived grant carrying
`transfer` with a parent carves its cap out of the parent's transfer ledger: the parent is a grant
the signer holds on the same target, it had at least that much left, and the Turn's effect is the
parent's spend. -/
theorem grant_carves_transfer {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {target grantee p : D}
    {rights : List Right} {d : Draft D}
    (h : grant X look c a target grantee rights (some p) = .ok d) (ht : rights.any isTransfer = true) :
    ∃ pc ef, readKind look p kindGrant = .ok pc ∧ slotDigest X p pc grantTarget = .ok target ∧
      slotDigest X p pc grantGrantee = .ok a.actor ∧
      spendAt transferBase p pc (transferUnits rights) (.grantWidens p) = .ok ef ∧
      d.effects = ef.toList ∧ d.nullifiers = [] := by
  unfold grant at h
  simp only [except_bind_ok] at h
  obtain ⟨_, _, ⟨⟩, hr, ef, hp, h⟩ := h
  have he : rights.any isEnroll = false := by
    cases he : rights.any isEnroll
    · rfl
    · exact absurd ⟨he, .inl ht⟩ (checkRights_ok hr).2.1
  simp only [checkParent, except_bind_ok, he, ht, if_true, Bool.false_eq_true, if_false] at hp
  obtain ⟨pc, hpc, pt, hpt, ⟨⟩, hteq, pg, hpg, ⟨⟩, hgeq, ⟨⟩, _, hs⟩ := hp
  rw [req_ok, decide_eq_true_eq] at hteq hgeq
  subst hteq; subst hgeq
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨pc, ef, hpc, hpt, hpg, hs, rfl, rfl⟩

omit [Ord D] in
/-- **Credit caps attenuate** (KERNEL-60): as `grant_carves_transfer`, from the parent's credit
ledger. -/
theorem grant_carves_credit {X : Ctx D} {look : Pinned D} {c : Call D} {a : At D} {target grantee p : D}
    {rights : List Right} {d : Draft D}
    (h : grant X look c a target grantee rights (some p) = .ok d) (hk : rights.any isCredit = true) :
    ∃ pc ef, readKind look p kindGrant = .ok pc ∧ slotDigest X p pc grantTarget = .ok target ∧
      slotDigest X p pc grantGrantee = .ok a.actor ∧
      spendAt creditBase p pc (creditUnits rights) (.grantWidens p) = .ok ef ∧
      d.effects = ef.toList ∧ d.nullifiers = [] := by
  unfold grant at h
  simp only [except_bind_ok] at h
  obtain ⟨_, _, ⟨⟩, hr, ef, hp, h⟩ := h
  have hr' := checkRights_ok hr
  have he : rights.any isEnroll = false := by
    cases he : rights.any isEnroll
    · rfl
    · exact absurd ⟨he, .inr hk⟩ hr'.2.1
  have ht : rights.any isTransfer = false := by
    cases ht : rights.any isTransfer
    · rfl
    · exact absurd ⟨ht, hk⟩ hr'.1
  simp only [checkParent, except_bind_ok, he, ht, hk, if_true, Bool.false_eq_true, if_false] at hp
  obtain ⟨pc, hpc, pt, hpt, ⟨⟩, hteq, pg, hpg, ⟨⟩, hgeq, ⟨⟩, _, hs⟩ := hp
  rw [req_ok, decide_eq_true_eq] at hteq hgeq
  subst hteq; subst hgeq
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨pc, ef, hpc, hpt, hpg, hs, rfl, rfl⟩

end Nanodregg.Kernel.Receive
