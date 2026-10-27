/-
# Host.Proofs.Cli — `host import` writes no Store path before every check passed (HOST-28's gap)

`Host.Cli.importWith` is `host import`'s decision over its effects (`ImportFx`); the deployed verb
is it at `IO` (`importVerb`), where `genesis` is `Host.genesis`, the only effect that creates a
Store path. Here it runs at `Except (Option (Digest × World D))`, each effect answering a given result,
`genesis` throwing the key and World it was handed and `reopen` (`openWriter`, which truncates and
locks: it writes) throwing `none`: the same function, so the same order of effects. The run ends
`.error (some (k, w))` exactly when `genesis` was reached FIRST among the writing effects, with
`k` and `w`:

* `import_genesis_iff` — `genesis` is the first writing effect reached, with key `k` and World `w`,
  EXACTLY when the pin parsed, the nonce effect answered a nonce, the IN effect answered bytes,
  `Carry.importWorld` accepted them under the pin (the digest, or the origin of the World made;
  stamp, decode, anchor, KERNEL's carry) making
  `w`, and the key effect answered `k` (the bound on IN and the 32-byte key are the IO instance's
  `readBounded` and `Digest.ofBytes?`). Its `→` half is refuse-before-write; its `←` half is the tooth:
  a passing import reaches genesis before `reopen`, with the drawn key, so the claim is false of a
  function that never writes, writes first through `reopen`, or writes before a check.
-/
import Host.Cli
import Host.Proofs.Carry
import Kernel.Proofs.Weight
import Codec.Proofs.Digest
import Kernel.Proofs.Origin
import Kernel.Proofs.Cells
import Kernel.Proofs.Rows
import Kernel.Proofs.CarrySound
import Codec.Proofs.Carried
import Codec.Proofs.Deployed
import Protocol.Proofs.Invite

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

theorem import_genesis_iff (name : String) (pinHex : PinArg) (stated : Option Receive.Authority)
    (nonceR : Except Status ByteArray)
    (inR : Except (StoreFault (Record.Fault (Reject D))) ByteArray) (keyR : Option Digest)
    (k : Digest) (w : World D) :
    importWith (m := Except (Option (Digest × World D)))
        { nonce := pure nonceR, readIn := pure inR, key := pure keyR,
          genesis := fun k₀ w₀ => throw (some (k₀, w₀)),
          reopen := fun _ => throw none,
          refuse := fun _ _ => pure 1, report := fun _ => pure () } name pinHex stated = .error (some (k, w)) ↔
    ∃ pin nonce bytes r, pinHex.parse = some pin ∧ nonceR = .ok nonce ∧ inR = .ok bytes ∧
      Carry.importWorld X Codec.Deployed.digestCodec name.toUTF8 nonce pin stated bytes = .ok (w, r) ∧
      budgetFault w = none ∧ keyR = some k := by
  unfold importWith importWithPin
  cases hd : pinHex.parse <;> cases nonceR <;> cases inR <;>
    simp only [bind, Except.bind, pure, Except.pure] <;>
    (repeat' split) <;> simp_all [Prod.ext_iff, and_comm]
  all_goals (try (intro h₁; subst h₁; simp_all))
  all_goals (try (exact ⟨fun hh => ⟨hh.2, hh.1, hh.2 ▸ ‹budgetFault _ = none›⟩, fun hh => ⟨hh.2.1, hh.1⟩⟩))

/-- **`host join` writes no Store path before the invitation is accepted** (PROTOCOL-42, HOST-12's
condition). `genesis` is reached, with key `k` and World `w`, EXACTLY when INVITE and KEY parsed,
`Invite.acceptStart` accepted a genesis start under KEY, that start makes `w`, and the key effect answered `k`. Its
`→` half is refuse-before-write; its `←` half is the tooth: an accepted invitation reaches genesis
with the World `accept` made, so the claim is false of a `join` that writes first or writes another
World. -/
theorem join_genesis_iff (inviteHex keyHex : String) (keyR : Option Digest) (k : Digest) (w : World D) :
    joinWith (m := Except (Option (Digest × World D)))
        { nonce := pure (.ok ByteArray.empty), readIn := throw none, reopen := fun _ => throw none,
          key := pure keyR, genesis := fun k₀ w₀ => throw (some (k₀, w₀)),
          refuse := fun _ _ => pure 1, report := fun _ => pure () } inviteHex keyHex = .error (some (k, w)) ↔
    ∃ inv trusted i o name nonce allowance fs auth,
      Protocol.Text.ofHex inviteHex = some inv ∧ Protocol.Text.ofHex keyHex = some trusted ∧
      Protocol.Invite.acceptStart X trusted inv = .ok (i, o) ∧
      i.start = .genesis name nonce allowance fs auth ∧
      Protocol.Invite.startGenesis X i.start = .ok w ∧ budgetFault w = none ∧ keyR = some k := by
  unfold joinWith
  cases hi : Protocol.Text.ofHex inviteHex <;> cases hk : Protocol.Text.ofHex keyHex <;>
    simp only [bind, Except.bind, pure, Except.pure] <;>
    (repeat' split) <;> simp_all [Prod.ext_iff, and_comm]
  all_goals (try (intro h₁; subst h₁; simp_all))
  all_goals (try (exact ⟨fun hh => ⟨hh.2, hh.1, hh.2 ▸ ‹budgetFault _ = none›⟩, fun hh => ⟨hh.2.1, hh.1⟩⟩))

/-- A carried join writes exactly the imported World under the invitation's carry start: its name,
nonce and stated authority, pinned to the origin the start is the digest of (PROTOCOL-85), after
checking every signed head field. A missing or different export never reaches genesis. -/
theorem join_carried_iff (inviteHex keyHex path : String)
    (inR : Except (StoreFault (Record.Fault (Reject D))) ByteArray) (keyR : Option Digest)
    (k : Digest) (w : World D)
    {inv trusted : ByteArray} {i : Protocol.Invite.Invitation D} {accepted chain : D}
    {s : Receive.CarryStart D}
    (hi : Protocol.Text.ofHex inviteHex = some inv)
    (hk : Protocol.Text.ofHex keyHex = some trusted)
    (ha : Protocol.Invite.acceptStart X trusted inv = .ok (i, accepted))
    (hs : i.start = .carried s chain) :
    joinWith (m := Except (Option (Digest × World D)))
        { nonce := pure (.ok ByteArray.empty), readIn := pure inR, reopen := fun _ => throw none,
          key := pure keyR, genesis := fun k₀ w₀ => throw (some (k₀, w₀)),
          refuse := fun _ _ => pure 1, report := fun _ => pure () } inviteHex keyHex (some path) =
        .error (some (k, w)) ↔
    ∃ bytes r, inR = .ok bytes ∧
      Carry.importWorld X Codec.Deployed.digestCodec s.name s.nonce (.origin (Receive.carryOriginOfStart X s))
        (some s.auth) bytes = .ok (w, r) ∧
      r.head.fromOrigin = s.fromOrigin ∧ r.head.height = s.height ∧ r.head.chain = chain ∧
      budgetFault w = none ∧ keyR = some k := by
  simp only [joinWith, hi, hk, ha, hs, bind, Except.bind, pure, Except.pure]
  unfold importWithPin
  cases inR <;> simp only [bind, Except.bind, pure, Except.pure] <;>
    (repeat' split) <;> simp_all [Prod.ext_iff, and_comm]
  all_goals (try (intro h; subst w; simp_all))
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, ⟨rfl, rfl⟩, ‹_ ∧ _ ∧ _›.1, ‹_ ∧ _ ∧ _›.2.1, ‹_ ∧ _ ∧ _›.2.2, rfl, ‹budgetFault _ = none›⟩
  · rintro ⟨_, ⟨hw, _⟩, _, _, _, hk, _⟩
    exact ⟨hk, hw⟩

/-- **`host seal` writes only after the writer's open succeeded** (HOST-43): the seal effect, the
one that writes, is reached with the opened Store `r` EXACTLY when the key read and the writer's
open (the Store's lock) both succeeded with it. Its `→` half is refuse-before-write (a live writer's
`locked`, a missing key, a foreign or corrupt Store write nothing); its `←` half is the tooth: an
opened Store is sealed, so the claim is false of a verb that skips the seal or seals another Store. -/
theorem seal_writes_iff {R : Type} (keyR : Except (StoreFault (Record.Fault (Reject D))) Digest)
    (openR : Digest → Except (StoreFault (Record.Fault (Reject D))) R) (r : R) :
    sealWith (m := Except (Option R))
        { key := pure keyR, open_ := fun k => pure (openR k), write := fun r₀ => throw (some r₀),
          refuse := fun _ _ => pure 1, report := fun _ => pure () } = .error (some r) ↔
    ∃ k, keyR = .ok k ∧ openR k = .ok r := by
  unfold sealWith
  cases keyR <;> simp only [bind, Except.bind, pure, Except.pure] <;>
    (repeat' split) <;> simp_all

/-- **A World that passes the budget check stays within the World bound's weight** (HOST-56,
KERNEL-55): every World an admitted fold reaches from it weighs at most `potentialMax / 145`
(`allowance_bounds_world` with the check's second arm). This is the weight half of the writer-side
`reached_size_le`; the bytes half is CODEC's size equality (cv 01a150a3-2523). -/
theorem budget_reaches {w w' : World D} {l : List (Step D)} (hb : budgetFault w = none)
    (hc : w.Canon X.env) (hf : w.Slotted X.env) (hr : w.RowsCanon X.env) (h : World.fold X.env w l = .ok w') :
    potentialRatio.2 * w'.weight ≤ potentialMax := by
  have hw := allowance_bounds_world hc hf hr h
  unfold budgetFault at hb
  split at hb
  · cases hb
  · split at hb
    · cases hb
    · omega

/-- **`budget_reaches` at the World `host genesis` admits** (HOST-56): a genesis World the kernel
makes (`Receive.genesis`) and the budget check passes stays within `potentialMax / 145` of weight
over every admitted fold; Canon, Slotted and RowsCanon hold at a genesis World
(`receive_genesis_canon`, `receive_genesis_slotted`, `receive_genesis_rowsCanon`). Imported and joined
Worlds: cv 01a150ed-7bf7. -/
theorem genesis_budget_reaches {name nonce : ByteArray} {allowance : Nat} {fs : List (ByteArray × D)} {auth : Receive.Authority}
    {w w' : World D} {l : List (Step D)} (hg : Receive.genesis X name nonce allowance fs auth = .ok w)
    (hb : budgetFault w = none) (h : World.fold X.env w l = .ok w') :
    potentialRatio.2 * w'.weight ≤ potentialMax := by
  obtain ⟨-, rfl⟩ := Receive.genesis_ok.mp hg
  exact budget_reaches hb (receive_genesis_canon X _ _ _ _ _) (receive_genesis_slotted X _ _ _ _ _)
    (receive_genesis_rowsCanon X _ _ _ _ _) h

/-- **The allowance arm** (HOST-56, ROOT's Q3): a World carrying more than `allowanceMax` is refused
`allowancePastBound`, whatever its weight. -/
theorem budgetFault_allowance {w : World D} (h : allowanceMax < w.allowance) :
    budgetFault w = some .allowancePastBound := by
  unfold budgetFault; rw [if_pos h]

/-- **The potential arm, the one the allowance arm misses** (HOST-56): a World whose allowance passes
but whose potential is past `potentialMax` is refused `potentialPastBound`. -/
theorem budgetFault_potential {w : World D} (ha : w.allowance ≤ allowanceMax) (hp : potentialMax < potential w) :
    budgetFault w = some .potentialPastBound := by
  unfold budgetFault; rw [if_neg (by omega), if_pos hp]

/-- **An imported World meets `budget_reaches`' premises** (HOST-59, cv 01a150ed-7bf7): the World
`Carry.importWorld` makes is KERNEL's carry of a carried state the carried codec decoded
(`carried_decode_fits`), and the carry keeps that state's cells and rows tries
(`carryWorld`), so they are canonical and every cell leaf fits its slot. No premise. -/
theorem importWorld_premises {name nonce : ByteArray} {pin : Carry.Pin D} {stated : Option Receive.Authority}
    {f : ByteArray} {w : World D}
    {r : Carry.Read D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce pin stated f = .ok (w, r)) :
    w.Canon X.env ∧ w.Slotted X.env ∧ w.RowsCanon X.env := by
  obtain ⟨hr, ⟨auth, -, hw⟩, -⟩ := Carry.importWorld_ok h
  obtain ⟨_, hd⟩ := Carry.read_decoded hr
  have hf := Codec.Kernel.carried_decode_fits Codec.Deployed.digestCodec_lawful.on hd
  have hsl : ∀ s l, r.carried.trie.get (trieSpec X.env) s = some l → Leaf.fits s l = true :=
    fun s l hg => hf.cells.1.2 (s, l) ((Trie.mem_toList (trieSpec X.env) 0 _ hf.cells.2.1 s l).mpr hg)
  obtain ⟨-, -, -, -, hcanon, hslot, -⟩ := Receive.carry_sound hf.cells.2 hsl hw
  obtain ⟨-, rfl⟩ := Receive.carry_ok.mp hw
  exact ⟨hcanon, hslot, hf.rows.listing.2⟩

/-- **A joined World meets `budget_reaches`' premises** (HOST-59): the World an accepted invitation
makes is KERNEL's genesis World of its signed inputs (PROTOCOL's `accept_ok`, `genesis_ok`). No premise. -/
theorem accept_premises {trusted inv : ByteArray} {i : Protocol.Invite.Invitation D} {w : World D}
    (h : Protocol.Invite.accept X trusted inv = .ok (i, w)) :
    w.Canon X.env ∧ w.Slotted X.env ∧ w.RowsCanon X.env := by
  obtain ⟨_, _, _, _, _, _, hg⟩ := Protocol.Invite.accept_genesis h
  obtain ⟨-, rfl⟩ := Receive.genesis_ok.mp hg
  exact ⟨receive_genesis_canon X _ _ _ _ _, receive_genesis_slotted X _ _ _ _ _, receive_genesis_rowsCanon X _ _ _ _ _⟩

/-- **`budget_reaches` at every World `host import` admits** (HOST-59): no premise beyond the import
and the fold. -/
theorem import_budget_reaches {name nonce : ByteArray} {pin : Carry.Pin D} {stated : Option Receive.Authority}
    {f : ByteArray} {w w' : World D} {r : Carry.Read D} {l : List (Step D)}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce pin stated f = .ok (w, r))
    (hb : budgetFault w = none) (hf : World.fold X.env w l = .ok w') :
    potentialRatio.2 * w'.weight ≤ potentialMax :=
  let ⟨hc, hs, hr⟩ := importWorld_premises h
  budget_reaches hb hc hs hr hf

/-- **`budget_reaches` at every genesis World `host join` admits** (HOST-59). -/
theorem join_budget_reaches {trusted inv : ByteArray} {i : Protocol.Invite.Invitation D} {w w' : World D}
    {l : List (Step D)} (h : Protocol.Invite.accept X trusted inv = .ok (i, w))
    (hb : budgetFault w = none) (hf : World.fold X.env w l = .ok w') :
    potentialRatio.2 * w'.weight ≤ potentialMax :=
  let ⟨hc, hs, hr⟩ := accept_premises h
  budget_reaches hb hc hs hr hf

/-- **An imported World's log begins at its carried height** (HOST-61): KERNEL's carry sets the
step count to the height (`carryWorld`), so a Store `import` makes from a World at height N indexes
its first record at step N, and a page from before N is refused `beforeLog`
(`Host.Page.build_beforeLog`). Over any Ctx and digest codec. -/
theorem importWorld_steps {T : Type} [Ord T] [DecidableEq T] {X : Receive.Ctx T} {dc : Codec.Stream T}
    {name nonce : ByteArray} {pin : Carry.Pin T} {stated : Option Receive.Authority} {f : ByteArray} {w : World T}
    {r : Carry.Read T}
    (h : Carry.importWorld X dc name nonce pin stated f = .ok (w, r)) : w.steps = w.height := by
  obtain ⟨-, ⟨_, -, hw⟩, -⟩ := Carry.importWorld_ok h
  unfold Carry.world at hw
  obtain ⟨-, rfl⟩ := Receive.carry_ok.mp hw
  rfl

end Nanodregg.Host.Cli
