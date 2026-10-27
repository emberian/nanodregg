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
`carryOriginOf`: the hash of the exported origin, the four carried roots, allowance, height, name,
nonce and the stated authority, KERNEL-79), every segment file's checkpoint header states it under the Store key (HOST-64), and it is
what an outside party checks: the founder compares it out of band (`host genesis` prints it), a
sponsor's invitation pins it (card 7a). The start it names is unique up to a collision among explicit
preimages (`start_genesis_unique`, `start_carry_commits`, `start_kinds_disjoint`), so trusting `o` is
trusting ONE start, never "some start of the right shape". (ROOT first ruled a separate start-digest
field; the origin's existing commitment refuted it: two commitments to one start are two shapes.)
It is DISCHARGED

* at the start of a Store: `genesis_trusted` (a genesis that passed the budget check) and
  `import_trusted` (an import that passed it), with `l = []`, each at its own origin; and
  `import_trusted_pinned`: `host import --origin O` (card 7a) is trusted at the `O` passed, because
  the import refuses any other origin (`carryMismatch wrongWorld`). The premise is named once:
  `CheckpointTrusted` is over the recorded origin, and the origin pin is the one place a Store's start
  is checked against an outside record (the invitation PROTOCOL-61 signs; that link is PROTOCOL's);
* along every admitted fold after (`trusted_fold`), so a reopen from a trusted base opens to a
  trusted World (`openWith_trusted`);
* for the writer's own base (`sealed_trusted`): a base file `Base.file` writes for a trusted World
  reads back as that World. That the bytes on disk ARE that file is the Store key's MAC: an
  integrity-at-rest key (HOST-16), not a proof; that the writer's World is trusted is the chain
  genesis/import → `trusted_fold` → seal, by induction over the writer's life (each open
  `openWith_trusted`, each round's last seal `sealed_trusted`, every other seal the end of a prefix
  life): `writer_life_trusted` over `WriterLife`, the abstract events (open, admitted fold, seal;
  HOST-69), from `genesis_life_trusted` / `import_life_trusted`. The fold of each batch is
  `host_run_kept`; that the loop holds nothing but those Worlds between the open and the seal is
  the fold premise of each link, read off (HOST-62's item), not re-derived.

It is NOT discharged for a RECEIVED base: a thin member's adopt (the pin binds the bytes, not their
history: `Protocol.Thin`), a hosted follower's join from a served base (a joiner of a CARRIED World
instead imports its file under `--origin`, which `import_trusted_pinned` discharges), or a Store whose older segment
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
    ((∃ (name nonce : ByteArray) (allowance : Nat) (founders : List (ByteArray × D)) (auth : Receive.Authority),
        Receive.genesis X name nonce allowance founders auth = .ok w₀) ∨
      (∃ (name nonce : ByteArray) (f : ByteArray) (r : Carry.Read D) (auth : Receive.Authority),
        Carry.read X.env Codec.Deployed.digestCodec f = .ok r ∧ Carry.world X name nonce auth r = .ok w₀)) ∧
    budgetFault w₀ = none ∧ Kept w₀ ∧ World.fold X.env w₀ l = .ok w

/-- **A genesis that passed the budget check is trusted** (`host genesis`, `host join`: the budget
check runs before the Store is written, HOST-56). -/
theorem genesis_trusted {name nonce : ByteArray} {allowance : Nat} {founders : List (ByteArray × D)} {auth : Receive.Authority}
    {w₀ : World D} (hg : Receive.genesis X name nonce allowance founders auth = .ok w₀)
    (hb : budgetFault w₀ = none) : CheckpointTrusted w₀.origin w₀ := by
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  exact ⟨⟨_, [], rfl, Or.inl ⟨name, nonce, allowance, founders, auth, hg⟩, hb,
    kept_of_fits (genesisWorld_codecFits hf), by simp [World.fold]⟩⟩

/-- **An import that passed the budget check is trusted** (`host import`, HOST-59). -/
theorem import_trusted {name nonce : ByteArray} {pin : Carry.Pin D} {stated : Option Receive.Authority}
    {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce pin stated f = .ok (w₀, r))
    (hb : budgetFault w₀ = none) : CheckpointTrusted w₀.origin w₀ :=
  have ⟨hr, ⟨auth, _, hw⟩, _⟩ := Carry.importWorld_ok h
  ⟨⟨w₀, [], rfl, Or.inr ⟨name, nonce, f, r, auth, hr, hw⟩, hb, kept_import h, by simp [World.fold]⟩⟩

/-- **An import pinned at `o` is trusted at `o`** (`host import --origin`, card 7a): whatever `o` the
operator passed, an import that succeeds made a World of that origin (the import refuses any other,
`carryMismatch wrongWorld`, `Carry.importWorld_wrongWorld`). It is `import_trusted` with the pin's
`Pin.Holds`; what it adds is the INSTANCE: the Store is trusted at the pinned `o`, which a joiner
takes from a sponsor-signed invitation (PROTOCOL-61, PROTOCOL's to state: no invitation appears
here), rather than at the origin its own import computed. Two imports pinned at one `o` carried one
state up to an explicit collision (`start_carry_commits`). -/
theorem import_trusted_pinned {name nonce : ByteArray} {o : D} {stated : Option Receive.Authority}
    {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce (.origin o) stated f = .ok (w₀, r))
    (hb : budgetFault w₀ = none) : CheckpointTrusted o w₀ := by
  have ho : w₀.origin = o := (Carry.importWorld_ok h).2.2
  exact ho ▸ import_trusted h hb

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

/-! ## The writer's life as ONE theorem (HOST-69; HOST-64's "NOT PROVED: the writer-life induction") -/

/-- **The writer's life, as the abstract events this module states link by link**: from a base
file, each link is one open of it (`openWith` to `o`), the loop's admitted steps after it (an
admitted fold `World.fold X.env o.opened.world l = .ok w'`), and the seal of the World it reached
(`Base.file`, the base file the next link opens). `refl` ends it. Stated over opens and seals only:
no append is an event.

The fold premise `hf`: the fold of ONE batch is `host_run_kept` (`Host.Proofs.Refine`, at
`(machine X)`, from `trusted_kept`'s `Kept`); the batches of a round concatenate by `fold_append`.
What stays READ OFF (HOST-62's item; host.md's "the resident World is only ever the open's World or
`admitBatch`'s") is that `Loop.serve` holds nothing but those Worlds between the open and the seal.
Nobody discharges `hf` over the IO loop; it enters as this premise.

A link's seal is the LAST seal of its round: the base the next open reads. A seal made mid-round
(`append`'s cadence, `makeRoom`'s `sealNow`) is not a link of the life that continues; it is the
END of a shorter life over the same open, since folds concatenate (`fold_append`). So every base
this writer writes ends some `WriterLife` from its start file, and `writer_life_trusted` covers
each; no single life lists every seal. -/
inductive WriterLife (keys : Keys) : ByteArray → ByteArray → Prop
  | refl (file : ByteArray) : WriterLife keys file file
  | link {file file' rest H I S : ByteArray} {o : Opening (World D)} {l : List (Step D)} {w' : World D}
      {seg : Position} {ix : IndexAt} {keep : Keep}
      (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
        (segReader I) (segReader S)) = .ok o)
      (hf : World.fold X.env o.opened.world l = .ok w')
      (hs : Base.file keys c world w' seg ix keep = .ok file')
      (hcount : ix.count < 2 ^ 64)
      (next : WriterLife keys file' rest) : WriterLife keys file rest

/-- **One link keeps the base trusted**: a base file whose World is trusted at `r`, opened, folded
by admitted steps and sealed, leaves a base file whose World is trusted at `r`
(`openWith_trusted`, `trusted_fold`, `sealed_trusted`). -/
theorem link_trusted {r : D} {keys : Keys} {file file' H I S : ByteArray} {o : Opening (World D)}
    {l : List (Step D)} {w' : World D} {seg : Position} {ix : IndexAt} {keep : Keep}
    (hbase : ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file = .ok (b, n, d) → CheckpointTrusted r b.world)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    (hf : World.fold X.env o.opened.world l = .ok w')
    (hs : Base.file keys c world w' seg ix keep = .ok file') (hcount : ix.count < 2 ^ 64) :
    ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file' = .ok (b, n, d) → CheckpointTrusted r b.world :=
  fun _ _ _ hr => sealed_trusted (trusted_fold (openWith_trusted h hbase) hf) hs hcount hr

/-- **The writer-life induction, as one theorem** (HOST-64's named gap): over a writer's life from a
base file whose World is trusted at `r`, the base file it ends at holds a World trusted at `r`
(every base file a writer reaches ends some life, so each is covered). The induction over
`WriterLife` composes `link_trusted`; the start is `genesis_life_trusted` / `import_life_trusted`. -/
theorem writer_life_trusted {r : D} {keys : Keys} {file₀ fileN : ByteArray}
    (life : WriterLife keys file₀ fileN)
    (hbase : ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file₀ = .ok (b, n, d) → CheckpointTrusted r b.world) :
    ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world fileN = .ok (b, n, d) → CheckpointTrusted r b.world := by
  induction life with
  | refl _ => exact hbase
  | link h hf hs hcount _ ih => exact ih (link_trusted hbase h hf hs hcount)

/-- The base `genesisImage` writes for a trusted World holds a trusted World: `Base.file` through
`sealed_trusted` at count 0. -/
theorem genesisImage_trusted {r : D} {keys : Keys} {w₀ : World D} (ht : CheckpointTrusted r w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world img.base = .ok (b, n, d) → CheckpointTrusted r b.world := by
  obtain ⟨file, hf, rfl⟩ := genesisImage_ok h
  exact fun _ _ _ hr => sealed_trusted ht hf (by decide) hr

/-- **A writer's life from `host genesis` holds trusted bases throughout** (at the genesis World's
origin): the genesis that passed the budget check (`genesis_trusted`), its image, then any life. -/
theorem genesis_life_trusted {keys : Keys} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Receive.Authority} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders auth = .ok w₀) (hb : budgetFault w₀ = none)
    {img : Image} (h : genesisImage keys c world recorder.mark w₀ = .ok img) {fileN : ByteArray}
    (life : WriterLife keys img.base fileN) :
    ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world fileN = .ok (b, n, d) → CheckpointTrusted w₀.origin b.world :=
  writer_life_trusted life (genesisImage_trusted (genesis_trusted hg hb) h)

/-- **A writer's life from `host import --origin O` holds bases trusted at `O` throughout**
(`import_trusted_pinned`: the pinned origin, the one an invitation names). -/
theorem import_life_trusted {keys : Keys} {name nonce : ByteArray} {o : D} {stated : Option Receive.Authority}
    {f : ByteArray} {r : Carry.Read D}
    {w₀ : World D} (hi : Carry.importWorld X Codec.Deployed.digestCodec name nonce (.origin o) stated f = .ok (w₀, r))
    (hb : budgetFault w₀ = none) {img : Image} (h : genesisImage keys c world recorder.mark w₀ = .ok img)
    {fileN : ByteArray} (life : WriterLife keys img.base fileN) :
    ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world fileN = .ok (b, n, d) → CheckpointTrusted o b.world :=
  writer_life_trusted life (genesisImage_trusted (import_trusted_pinned hi hb) h)

/-- **The consumer, over a life**: every World a reopen of any base of the life returns encodes
within `worldBytesMax` (`opened_size_le`), so no seal of the life refuses `worldTooLarge` by the
tail's growth. -/
theorem life_opened_size_le {keys : Keys} {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Receive.Authority} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders auth = .ok w₀) (hb : budgetFault w₀ = none)
    {img : Image} (h : genesisImage keys c world recorder.mark w₀ = .ok img) {fileN H I S : ByteArray}
    (life : WriterLife keys img.base fileN) {o : Opening (World D)}
    (ho : Id.run (openWith keys c world recorder.mark originChain foldStep fileN H S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    world.size o.opened.world ≤ c.worldBytesMax :=
  opened_size_le ho (genesis_life_trusted hg hb h life)

/-- **The tooth**: a life is refuted by any base it reaches holding more potential than
`potentialMax`: no `WriterLife` from a trusted start reaches it (`not_trusted_of_potential`). -/
theorem life_refutes_potential {r : D} {keys : Keys} {file₀ fileN : ByteArray}
    (hbase : ∀ (b : Base (World D)) (n : Nat) (d : ByteArray),
      Base.read keys c world file₀ = .ok (b, n, d) → CheckpointTrusted r b.world)
    {b : Base (World D)} {n : Nat} {d : ByteArray} (hr : Base.read keys c world fileN = .ok (b, n, d))
    (hp : potentialMax < potential b.world) : ¬ WriterLife keys file₀ fileN :=
  fun life => not_trusted_of_potential hp (writer_life_trusted life hbase b n d hr)

/-! ## The recorded origin names ONE start (ROOT's (B′)) -/

/-- **Two geneses with one origin are one World**, or their two origin inputs collide (KERNEL's
`genesis_inj` over the explicit pair). -/
theorem start_genesis_unique {name nonce name' nonce' : ByteArray} {allowance allowance' : Nat}
    {founders founders' : List (ByteArray × D)} {auth auth' : Receive.Authority} {w₀ w₀' : World D}
    (hg : Receive.genesis X name nonce allowance founders auth = .ok w₀)
    (hg' : Receive.genesis X name' nonce' allowance' founders' auth' = .ok w₀')
    (ho : w₀.origin = w₀'.origin) :
    w₀ = w₀' ∨ CollidesAmong X.env.hash
      [Receive.originPre X name nonce allowance founders auth, Receive.originPre X name' nonce' allowance' founders' auth'] := by
  obtain ⟨hf, rfl⟩ := Receive.genesis_ok.mp hg
  obtain ⟨hf', rfl⟩ := Receive.genesis_ok.mp hg'
  rcases Receive.genesis_inj Receive.deployed_lawful hf hf' ho with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hc
  · exact .inl rfl
  · exact .inr hc

/-- **Two imports with one origin carried one start**: the same name, nonce and exported origin, the
same four carried ROOTS, allowance and height, and the same stated authority (`carryStartOf`,
KERNEL-79), or their two carry inputs collide (KERNEL's `carry_inj` over the explicit pair). What is
NOT proved here: that equal roots are equal tries (the trie's own binding, KERNEL's
`TrieBinding`); the Worlds agree on everything the origin hashes. -/
theorem start_carry_commits {name nonce name' nonce' : ByteArray} {pin pin' : Carry.Pin D}
    {stated stated' : Option Receive.Authority}
    {f f' : ByteArray} {r r' : Carry.Read D} {w₀ w₀' : World D}
    (h : Carry.importWorld X Codec.Deployed.digestCodec name nonce pin stated f = .ok (w₀, r))
    (h' : Carry.importWorld X Codec.Deployed.digestCodec name' nonce' pin' stated' f' = .ok (w₀', r'))
    (ho : w₀.origin = w₀'.origin) :
    ∃ auth auth', Carry.statedAuthority r.carried stated = .ok auth ∧ Carry.statedAuthority r'.carried stated' = .ok auth' ∧
      (Receive.carryStartOf X name nonce r.head.fromOrigin r.carried auth =
        Receive.carryStartOf X name' nonce' r'.head.fromOrigin r'.carried auth' ∨
      CollidesAmong X.env.hash
        [Receive.carryOriginPre X name nonce r.head.fromOrigin r.carried auth,
         Receive.carryOriginPre X name' nonce' r'.head.fromOrigin r'.carried auth']) := by
  obtain ⟨-, ⟨auth, ha, hw⟩, -⟩ := Carry.importWorld_ok h
  obtain ⟨-, ⟨auth', ha', hw'⟩, -⟩ := Carry.importWorld_ok h'
  obtain ⟨hf, rfl⟩ := Receive.carry_ok.mp hw
  obtain ⟨hf', rfl⟩ := Receive.carry_ok.mp hw'
  exact ⟨auth, auth', ha, ha', Receive.carry_inj Receive.deployed_lawful hf hf' ho⟩

/-- **A genesis and an import never share an origin**, but by a collision between their two origin
inputs (KERNEL's `carry_origin_ne_genesis`: the two cases of one tagged codec). -/
theorem start_kinds_disjoint {name nonce name' nonce' : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {auth : Receive.Authority} {pin : Carry.Pin D} {stated : Option Receive.Authority}
    {f : ByteArray} {r : Carry.Read D} {w₀ w₀' : World D}
    (hg : Receive.genesis X name nonce allowance founders auth = .ok w₀)
    (h' : Carry.importWorld X Codec.Deployed.digestCodec name' nonce' pin stated f = .ok (w₀', r))
    (ho : w₀.origin = w₀'.origin) :
    ∃ auth', CollidesAmong X.env.hash
      [Receive.carryOriginPre X name' nonce' r.head.fromOrigin r.carried auth',
       Receive.originPre X name nonce allowance founders auth] := by
  obtain ⟨_, rfl⟩ := Receive.genesis_ok.mp hg
  obtain ⟨-, ⟨auth', -, hw'⟩, -⟩ := Carry.importWorld_ok h'
  obtain ⟨_, rfl⟩ := Receive.carry_ok.mp hw'
  exact ⟨auth', Receive.carry_origin_ne_genesis ho.symm⟩

end Nanodregg.Host.Deployed
