/-
# Host.Proofs.Trusted — `CheckpointTrusted`: the premise of every open from a base (HOST-64; KERNEL-44 Part 2)

The open folds the tail after a base; it never re-derives the World the base holds. Every theorem
about the World a Store holds after a reopen therefore rests on a fact about the BASE's World: that
it has a HISTORY here, i.e. it is reached by admitted steps from a World this binary STARTED a Store
with: a genesis (`Receive.genesis`, what `host genesis` and `host join` write) or an import
(`Carry.importWorld`, what `host import` writes), which passed the budget check (`budgetFault` = none,
HOST-56/59) and is `Kept`. Before HOST-64 that fact was used and never named: HOST-57's
`reached_size_le` states its bound over a fold from an admitted World, and a reopened writer is that
bound only if its base is such a World.

`CheckpointTrusted o w` names it, over the Store's RECORDED ORIGIN `o`: `w` is reached by admitted
steps from a World a start of this binary admits (a genesis or an import) whose origin is `o`. The
origin is the start's commitment (KERNEL's `originOf`: the hash of the genesis inputs;
`carryOriginOf`: the hash of the carried roots, allowance, height, journal, the exported origin, name
and nonce), every segment file's checkpoint header states it under the Store key (HOST-64), and it is
what an outside party checks: the founder compares it out of band (`host genesis` prints it), a
sponsor's invitation pins it (card 7a). The start it names is unique up to a collision among explicit
preimages (`start_genesis_unique`, `start_carry_commits`, `start_kinds_disjoint`), so trusting `o` is
trusting ONE start, never "some start of the right shape". (ROOT first ruled a separate start-digest
field; the origin's existing commitment refuted it: two commitments to one start are two shapes.)
It is DISCHARGED

* at the start of a Store: `genesis_trusted` (a genesis that passed the budget check) and
  `import_trusted` (an import that passed it), with `l = []`;
* along every admitted fold after (`trusted_fold`), so a reopen from a trusted base opens to a
  trusted World (`openWith_trusted`);
* for the writer's own base (`sealed_trusted`): a base file `Base.file` writes for a trusted World
  reads back as that World. That the bytes on disk ARE that file is the Store key's MAC: an
  integrity-at-rest key (HOST-16), not a proof; that the writer's World is trusted is the chain
  genesis/import → `trusted_fold` → seal, by induction over the writer's life (each open
  `openWith_trusted`, each seal `sealed_trusted`), which this module states link by link.

It is NOT discharged for a RECEIVED base: a thin member's adopt (the pin binds the bytes, not their
history: `Protocol.Thin`), a hosted follower's join from a served base, or a Store whose older segment
files were dropped (HOST-64), whose history before the oldest kept file nobody here can re-derive. For
those it is the premise, and the theorems below are what it buys:

* `trusted_kept`, `trusted_size_le`, `trusted_potential_le` — a trusted World is `Kept`, encodes within
  the derived World bound, and holds at most `potentialMax` of storage potential;
* `openWith_trusted` — an open whose base World is trusted opens to a trusted World;
* `opened_size_le` — the consumer: the World an open from a trusted base returns encodes within
  `worldBytesMax`, so the next seal of it does not refuse `worldTooLarge`.

It is REFUTABLE: `not_trusted_of_potential` — a World holding more potential than `potentialMax` is
not trusted. Such a World decodes, can be pinned, served and adopted; only the premise stands between
it and every bound above (`host import` refuses its carried file `potentialPastBound` or
`allowancePastBound`; a thin adopt does not look; PROTOCOL-22's `untrustedAdopt` row plants it).
-/
import Host.Proofs.Size
import Host.Proofs.Backup
import Host.Proofs.Genesis
import Kernel.Proofs.RootedFold
import Kernel.Proofs.RootedDeployed
import Kernel.Proofs.Carry
import Kernel.Proofs.Origin
import Host.Proofs.Carry

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Cli

/-- **The checkpoint premise** (HOST-64): `w` is reached by admitted steps from a World whose origin
is `o` (the Store's recorded origin), that a start of this binary admits (a genesis, or an import),
that passed the budget check and is `Kept`. -/
structure CheckpointTrusted (o : D) (w : World D) : Prop where
  reached : ∃ (w₀ : World D) (l : List (Step D)), w₀.origin = o ∧
    ((∃ (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)),
        Receive.genesis X name nonce allowance founders = .ok w₀) ∨
      (∃ (name nonce : ByteArray) (want : Digest) (f : ByteArray) (r : Carry.Read D),
        Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r))) ∧
    budgetFault w₀ = none ∧ Kept w₀ ∧ World.fold X.env w₀ l = .ok w

/-- **A genesis that passed the budget check is trusted** (`host genesis`, `host join`: the budget
check runs before the Store is written, HOST-56). -/
theorem genesis_trusted {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)}
    {w₀ : World D} (hg : Receive.genesis X name nonce allowance founders = .ok w₀)
    (hb : budgetFault w₀ = none) : CheckpointTrusted w₀.origin w₀ := by
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  exact ⟨⟨_, [], rfl, Or.inl ⟨name, nonce, allowance, founders, hg⟩, hb,
    kept_of_fits (genesisWorld_codecFits hf), by simp [World.fold]⟩⟩

/-- **An import that passed the budget check is trusted** (`host import`, HOST-59). -/
theorem import_trusted {name nonce : ByteArray} {want : Digest} {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r))
    (hb : budgetFault w₀ = none) : CheckpointTrusted w₀.origin w₀ :=
  ⟨⟨w₀, [], rfl, Or.inr ⟨name, nonce, want, f, r, h⟩, hb, kept_of_fits (importWorld_codecFits h),
    by simp [World.fold]⟩⟩

/-- An admitted fold from a trusted World reaches a trusted World. -/
theorem trusted_fold {o : D} {w w' : World D} {l : List (Step D)} (ht : CheckpointTrusted o w)
    (h : World.fold X.env w l = .ok w') : CheckpointTrusted o w' := by
  obtain ⟨w₀, l₀, ho, hs, hb, hk, hf⟩ := ht.reached
  exact ⟨⟨w₀, l₀ ++ l, ho, hs, hb, hk, fold_append.mpr ⟨w, hf, h⟩⟩⟩

/-- **A trusted World states the pinned origin**: admitted steps keep the origin
(`Receive.fold_origin`), so `o` is the World's own origin. Its Store's headers state the genesis CHAIN
of that origin (`openWith_header`; equal chains are equal origins up to a collision,
`Receive.genesis_chain_inj`). The premise means something only against a pin from an INDEPENDENT
record (the founder's out-of-band origin, a sponsor's invitation): instantiated at `w.origin` itself
it certifies any World some start admits, a forged import included. -/
theorem trusted_origin {o : D} {w : World D} (ht : CheckpointTrusted o w) : w.origin = o := by
  obtain ⟨_, _, ho, _, _, _, hf⟩ := ht.reached
  rw [Receive.fold_origin hf, ho]

/-- A trusted World is `Kept`. -/
theorem trusted_kept {o : D} {w : World D} (ht : CheckpointTrusted o w) : Kept w := by
  obtain ⟨_, _, _, _, _, hk, hf⟩ := ht.reached
  exact kept_fold hk hf

/-- **A trusted World encodes within the derived World bound** (HOST-57's `reached_size_le`, from
the premise). -/
theorem trusted_size_le {o : D} {w : World D} (ht : CheckpointTrusted o w) :
    ((Codec.Kernel.world X.env Codec.Deployed.digestCodec).bytes w).size ≤ Cadence.deployed.worldBytesMax := by
  obtain ⟨_, _, _, _, hb, hk, hf⟩ := ht.reached
  exact Size.reached_size_le hb hk hf

/-- **A trusted World holds at most `potentialMax` of storage potential**: the start's budget check
bounds it, and no admitted step raises it (`fold_potential`). -/
theorem trusted_potential_le {o : D} {w : World D} (ht : CheckpointTrusted o w) : potential w ≤ potentialMax := by
  obtain ⟨w₀, _, _, _, hb, hk, hf⟩ := ht.reached
  have hp := fold_potential hk.canon hk.slotted hk.rowsCanon hf
  unfold budgetFault at hb
  split at hb
  · cases hb
  · split at hb
    · cases hb
    · omega

/-- **The premise is refutable**: a World holding more potential than `potentialMax` is not trusted,
whatever bytes carry it and whoever pinned them. -/
theorem not_trusted_of_potential {o : D} {w : World D} (h : potentialMax < potential w) : ¬ CheckpointTrusted o w :=
  fun ht => absurd (trusted_potential_le ht) (Nat.not_le.mpr h)

/-- The deployed reopen's fold over records is an admitted fold (`Record.step_rooted`,
`RootedFold.fold`). -/
theorem Record.foldlM_reach : ∀ {w w' : World D} {rs : List ByteArray},
    rs.foldlM foldStep w = .ok w' → ∃ l : List (Step D), World.fold X.env w l = .ok w'
  | w, w', [], h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], by simp [World.fold, h]⟩
  | w, w', r :: rs, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i w₁ h₁
      obtain ⟨_, _, hr⟩ := Record.step_rooted h₁
      obtain ⟨l, hl⟩ := Record.foldlM_reach h
      exact ⟨_ ++ l, fold_append.mpr ⟨w₁, RootedFold.fold hr, hl⟩⟩

/-- **An open from a trusted base opens to a trusted World**: the base the deployed open decodes,
trusted, folded by the records after it. The premise is the BASE's: for the writer's own base it is
`sealed_trusted`; for a received one it is assumed, by name. -/
theorem openWith_trusted {r : D} {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hbase : ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file = .ok (b, n, d) → CheckpointTrusted r b.world) :
    CheckpointTrusted r o.opened.world := by
  obtain ⟨b, n, d, rs, hb, hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file H I S h
  obtain ⟨l, hl⟩ := Record.foldlM_reach hf
  exact trusted_fold (hbase b n d hb) hl

/-- **The consumer: an open from a trusted base holds a World within `worldBytesMax`** (HOST-57's
bound, which `Base.file` enforces as `worldTooLarge`), so the writer's next seal of it does not
refuse by size. The base World alone is bounded by its frame (`Cadence.baseRecordMax`); what the
premise bounds is the TAIL's growth, the fold of the records after the base, which no frame bounds. -/
theorem opened_size_le {r : D} {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hbase : ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file = .ok (b, n, d) → CheckpointTrusted r b.world) :
    world.size o.opened.world ≤ c.worldBytesMax := by
  have := trusted_size_le (openWith_trusted h hbase)
  rw [← (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on).size_eq] at this
  exact this

/-- **The writer's own base is trusted** (one link of the writer's life: genesis/import →
`trusted_fold` → seal → `openWith_trusted` → …): the base file `Base.file` writes for a World it
holds, trusted, reads back as that World. It does not say the bytes on disk are that file; that is
the Store key's MAC (HOST-16). -/
theorem sealed_trusted {o : D} {keys : Keys} {w : World D} {seg : Position} {ix : IndexAt} {keep : Keep}
    {file : ByteArray} (ht : CheckpointTrusted o w) (h : Base.file keys c world w seg ix keep = .ok file)
    (hcount : ix.count < 2 ^ 64)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hr : Base.read keys c world file = .ok (b, n, d)) :
    CheckpointTrusted o b.world := by
  obtain ⟨_, _, _, _, hb, hk, hf⟩ := ht.reached
  obtain ⟨_, hrd⟩ := Base.read_file (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    h (Size.reached_codecFits hb hk hf) hcount (by decide)
  have he := hr.symm.trans hrd
  injection he with he
  injection he with he
  rw [he]
  exact ht

/-! ## The recorded origin names ONE start (ROOT's (B′)) -/

/-- **Two geneses with one origin are one World**, or their two origin inputs collide (KERNEL's
`genesis_inj` over the explicit pair). -/
theorem start_genesis_unique {name nonce name' nonce' : ByteArray} {allowance allowance' : Nat}
    {founders founders' : List (ByteArray × D)} {w₀ w₀' : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀)
    (hg' : Receive.genesis X name' nonce' allowance' founders' = .ok w₀')
    (ho : w₀.origin = w₀'.origin) :
    w₀ = w₀' ∨ CollidesAmong X.env.hash
      [Receive.originPre X name nonce allowance founders, Receive.originPre X name' nonce' allowance' founders'] := by
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  obtain ⟨hf', rfl⟩ := Receive.genesis_ok.mp hg'
  rcases Receive.genesis_inj Receive.deployed_lawful hf hf' ho with ⟨rfl, rfl, rfl, rfl⟩ | hc
  · exact .inl rfl
  · exact .inr hc

/-- **Two imports with one origin carried one state**: the same name, nonce and exported origin, the
same trie and rows ROOTS, allowance and height, and the same journal (canonical, so its listing
is the trie), or their two carry inputs collide (KERNEL's `carry_inj_canon` over the explicit pair).
What is NOT proved here: that equal roots are equal tries (the trie's own binding, a KERNEL theorem
over its node preimages); the Worlds agree on everything the origin hashes. -/
theorem start_carry_commits {name nonce name' nonce' : ByteArray} {want want' : Digest}
    {f f' : ByteArray} {r r' : Carry.Read D} {w₀ w₀' : World D}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r))
    (h' : Carry.importWorld X Codec.Deployed.digestCodec name' nonce' want' f' = .ok (w₀', r'))
    (hj : Trie.Canon (journalSpec X.env) 0 r.carried.journal)
    (hj' : Trie.Canon (journalSpec X.env) 0 r'.carried.journal)
    (ho : w₀.origin = w₀'.origin) :
    (w₀.trie.hashOf (trieSpec X.env) = w₀'.trie.hashOf (trieSpec X.env) ∧
      w₀.rows.hashOf (rowSpec X.env) = w₀'.rows.hashOf (rowSpec X.env) ∧
      w₀.allowance = w₀'.allowance ∧ w₀.height = w₀'.height ∧ w₀.steps = w₀'.steps ∧
      w₀.journal = w₀'.journal ∧ w₀.refusals = w₀'.refusals ∧ w₀.chain = w₀'.chain) ∨
      CollidesAmong X.env.hash
        [Receive.carryOriginPre X name nonce r.head.fromOrigin r.carried,
         Receive.carryOriginPre X name' nonce' r'.head.fromOrigin r'.carried] := by
  obtain ⟨-, hw⟩ := Carry.importWorld_ok h
  obtain ⟨-, hw'⟩ := Carry.importWorld_ok h'
  obtain ⟨hf, rfl⟩ := Receive.carry_ok.mp hw
  obtain ⟨hf', rfl⟩ := Receive.carry_ok.mp hw'
  rcases Receive.carry_inj_canon Receive.deployed_lawful hj hj' hf hf' ho with
    ⟨_, _, _, ht, hr, ha, hh, hjl⟩ | hc
  · refine .inl ⟨ht, hr, ha, hh, hh, hjl, rfl, ?_⟩
    simp only [Receive.carryWorld] at ho ⊢
    rw [ho]
  · exact .inr hc

/-- **A genesis and an import never share an origin**, but by a collision between their two origin
inputs (KERNEL's `carry_origin_ne_genesis`: the two cases of one tagged codec). -/
theorem start_kinds_disjoint {name nonce name' nonce' : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {want : Digest} {f : ByteArray} {r : Carry.Read D} {w₀ w₀' : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀)
    (h' : Carry.importWorld X Codec.Deployed.digestCodec name' nonce' want f = .ok (w₀', r))
    (ho : w₀.origin = w₀'.origin) :
    CollidesAmong X.env.hash
      [Receive.carryOriginPre X name' nonce' r.head.fromOrigin r.carried,
       Receive.originPre X name nonce allowance founders] := by
  obtain ⟨_, rfl⟩ := Receive.genesis_ok.mp hg
  obtain ⟨-, hw'⟩ := Carry.importWorld_ok h'
  obtain ⟨_, rfl⟩ := Receive.carry_ok.mp hw'
  exact Receive.carry_origin_ne_genesis ho.symm

end Nanodregg.Host.Deployed
