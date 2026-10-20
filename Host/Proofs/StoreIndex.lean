/-
# Host.Proofs.StoreIndex — the Store's index is coherent, at every open (cv 01a15180-9499)

`StoreIndexes` is `Host.Proofs.Coherence`'s `Page.Indexes` for a Store, and the theorems that every
Store written at an open has it, and so its deployed pages short of the tip are non-empty. The
module header of `Host.Proofs.Coherence` lists them and what is not proved.
-/
import Host.Proofs.Coherence
import Host.Proofs.Seal

namespace Nanodregg.Host

open Nanodregg.Host.Log ByteArray
open Nanodregg.Host.Page (Indexes frameOf)

/-! ## The Store: every entry the base counts, and every entry since -/

/-- **The Store's index points at its records** (cv 01a15180-9499): the base file decodes to a
base `b`; the first `b.indexCount` entries of the index file (all inside it) read back at their
positions under the Store's index key as `L`; and `L` is a coherent run over the segment to the
base (its offset and its World's step count), the segment reaching the base. What the deployed
open adds to it is the tail's entries (`openWith_indexes`). Every Store this Host writes keeping its whole index has it:
`StoreIndexes.of_open_empty` (genesis, import, adopt: no entry), `StoreIndexes.append` (records
and orphans appended), `StoreIndexes.cut_open` (the writer's truncation at open), `sealed_indexes`
(a seal). It is stated over the LOGICAL index from entry 0, so it covers a Store that keeps its
whole index (the default); a Store that dropped entries (`indexFrom` > 0, HOST-64) is outside it: its
pages read the kept entries through `Page.kept`, which no theorem here states. -/
def StoreIndexes {W D : Type} (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) (file I S : ByteArray) :
    Prop :=
  ∃ (b : Base W) (n : Nat) (d : ByteArray) (L : List Entry), Base.read keys c world file = .ok (b, n, d) ∧
    L.length = b.indexCount ∧ L.length * entryBytes keys ≤ I.size ∧ b.offset ≤ S.size ∧
    (∀ (i : Nat) (hi : i < L.length), Entry.read (keys.forStore (origin b.world)) i
      (I.extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys)) = some L[i]) ∧
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1)

variable {W F D : Type}

/-- **The open's entries point at their records**: over a Store whose base's entries are a
coherent run to the base, the one open's entries since the base continue it to the open's
position and World (`Host.indexed` makes each from the frame the open verified), when each fold
step decodes its record to steps that move the step count by their number (`hstep`). -/
theorem openWith_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W) (mark : W → Nat × ByteArray)
    (origin : W → ByteArray) (step : W → ByteArray → Except F W) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d)) {L : List Entry}
    (hL : Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray)) L
      (b.offset, (mark b.world).1)) :
    Indexes dc keys.segment c.recordBytesMax (fun o l => (pure (S.extract o (o + l)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) := by
  obtain ⟨b', _, _, _, op, _, hb', hlen, hoff, htag, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  obtain ⟨rs, he, hf, _, _, hrs⟩ := open_sound_bounded keys.segment (indexed mark step) _ _ _ hop
  have hesz : (encodeAll keys.segment b.tag.bytes rs).size = op.validLen := by
    rw [← he]; simp only [size_extract]; omega
  have he' : S.extract b.offset (b.offset + (encodeAll keys.segment b.tag.bytes rs).size) =
      encodeAll keys.segment b.tag.bytes rs := by
    rw [hesz, ← he, extract_extract]; congr 1 <;> omega
  have hp : S.extract (b.offset - tagBytes) (b.offset - tagBytes + tagBytes) = b.tag.bytes := by
    rw [show b.offset - tagBytes + tagBytes = b.offset by omega]; exact htag
  obtain ⟨M, hM, hI, hhd⟩ := indexed_indexes (dc := dc) (S := S) mark step hstep rs b.world #[] b.offset
    b.tag.bytes hrs hp he' hf
  have hend := openLog_indexed_off keys.segment c.recordBytesMax mark step b.world #[] b.offset _ _ hop
  simp only [List.nil_append] at hM
  dsimp only
  rw [hM, ← hend]
  exact Indexes.append L M _ hL hI hhd

/-- A Store whose base counts no entry has a coherent index: the empty one. -/
theorem StoreIndexes.of_count_zero (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (dc : Codec.Stream D) {file I S : ByteArray}
    {b : Base W} {n : Nat} {d : ByteArray} (hb : Base.read keys c world file = .ok (b, n, d))
    (h0 : b.indexCount = 0) (hS : b.offset ≤ S.size) :
    StoreIndexes keys c world mark origin dc file I S :=
  ⟨b, n, d, [], hb, h0.symm, by simp, hS, fun _ hi => absurd hi (by simp), trivial⟩

/-- **A Store whose the index file is empty has a coherent index** (genesis, import and a follower's
adopted base all write an empty one): whenever the one open succeeds over it. -/
theorem StoreIndexes.of_open_empty (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    (dc : Codec.Stream D) (file H S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size ByteArray.empty.size
      (segReader ByteArray.empty) (segReader S)) = .ok o) :
    StoreIndexes keys c world mark origin dc file ByteArray.empty S := by
  obtain ⟨b, _, _, _, _, _, hb, hlen, _, _, _, _, _, hi, _, _, _, _, _⟩ :=
    openWith_seg_ok keys c world mark origin step file H ByteArray.empty S h
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have heb : 0 < entryBytes keys := by unfold entryBytes; omega
  simp only [ByteArray.size_empty, Nat.le_zero, Nat.mul_eq_zero] at hi
  exact StoreIndexes.of_count_zero keys c world mark origin dc hb (hi.resolve_right (by omega)) (by omega)

theorem Entry.read_extract_append {keys : Keys} {I x : ByteArray} {L : List Entry} {i : Nat}
    (hi : i < L.length) (hI : L.length * entryBytes keys ≤ I.size) :
    (I ++ x).extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys) =
      I.extract (i * entryBytes keys) (i * entryBytes keys + entryBytes keys) := by
  have : (i + 1) * entryBytes keys ≤ L.length * entryBytes keys := Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at this
  exact extract_append_le (by omega)

/-- **Appending keeps the index coherent**: records appended to the segment and entries (or
orphans) appended to the index file leave every entry the base counts, and the run to the base, as
they were. -/
theorem StoreIndexes.append {keys : Keys} {c : Cadence} {world : Codec.Stream W}
    {mark : W → Nat × ByteArray} {origin : W → ByteArray} {dc : Codec.Stream D} {file I S : ByteArray}
    (x y : ByteArray) (h : StoreIndexes keys c world mark origin dc file I S) :
    StoreIndexes keys c world mark origin dc file (I ++ x) (S ++ y) := by
  obtain ⟨b, n, d, L, hb, hc, hI, hS, hr, hL⟩ := h
  refine ⟨b, n, d, L, hb, hc, by rw [size_append]; omega, by rw [size_append]; omega,
    fun i hi => by rw [Entry.read_extract_append hi hI]; exact hr i hi, ?_⟩
  exact Indexes.congr (fun i j hj => (extract_append_le (by simp only at hj; omega)).symm) L hL

/-- **The writer's cut keeps the index coherent**: `openWriter` truncates the segment to the open's
valid end and the index file to the entries the base counts (`Host.openWriter`); the cut Store has
the same coherent index. -/
theorem StoreIndexes.cut_open (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {dc : Codec.Stream D} (file H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hS : StoreIndexes keys c world mark origin dc file I S) :
    StoreIndexes keys c world mark origin dc file (I.extract 0 (o.sealed.index.count * entryBytes keys))
      (S.extract 0 o.pos.offset) := by
  obtain ⟨b, n, d, L, hb, hc, hI, hSz, hr, hL⟩ := hS
  obtain ⟨b', _, _, _, op, _, hb', hlen, _, _, _, _, _, _, _, _, hop, _, rfl⟩ :=
    openWith_seg_ok keys c world mark origin step file H I S h
  rw [hb] at hb'; cases hb'
  obtain ⟨hs, _⟩ := tailRead_ok hlen
  have hvl := openLog_validLen_le hop
  simp only [size_extract] at hvl
  dsimp only
  rw [← hc]
  refine ⟨b, n, d, L, hb, hc, by simp only [size_extract]; omega, by simp only [size_extract]; omega,
    fun i hi => ?_, ?_⟩
  · have : (i + 1) * entryBytes keys ≤ L.length * entryBytes keys := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    rw [extract_prefix I (by omega)]; exact hr i hi
  · exact Indexes.congr (fun i j hj => (extract_prefix S (by simp only at hj; omega)).symm) L hL

theorem entryBytes_forStore (keys : Keys) (sid : ByteArray) :
    entryBytes (keys.forStore sid) = entryBytes keys := rfl

/-- **A seal keeps the index coherent** (the completeness side, discharged at seal): the seal of
an opened World at the open's position, with the entries since the base (what both checkpoints
write, `Base.seal`), over a Store whose index is coherent, leaves a Store (the new base, the index file
with the seal's entries appended, the segment cut at the open's position) whose index is coherent:
the old base's entries, then the open's (`openWith_indexes`), each read back at its position
(`run_read`). Premises are `sealed_opens`' and `hstep`. -/
theorem sealed_indexes (keys : Keys) (c : Cadence) (world : Codec.Stream W)
    (mark : W → Nat × ByteArray) (origin : W → ByteArray) (step : W → ByteArray → Except F W)
    {P : W → Prop} (hw : Codec.Stream.LawfulOn P world)
    (horigin : ∀ w r w', step w r = .ok w' → origin w' = origin w)
    (hmono : ∀ w r w', step w r = .ok w' → (mark w).1 < (mark w').1)
    (hcap : c.baseRecordMax < 2 ^ 32) {dc : Codec.Stream D}
    (hstep : ∀ w r w', step w r = .ok w' → ∃ ts : List (Kernel.Step D × D),
      (Record.codec dc).decode r = .ok ts ∧ (mark w').1 = (mark w).1 + ts.length)
    (file₀ H I S : ByteArray) {o : Opening W}
    (h : Id.run (openWith keys c world mark origin step file₀ H S.size I.size (segReader I) (segReader S)) = .ok o)
    (hP : P o.opened.world) {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (origin o.opened.world)) c world o.opened.world o.pos o.sealed.index
      (sealEntries o.index) I.size keep = .ok (page, ix', file))
    (hS : StoreIndexes keys c world mark origin dc file₀ I S) :
    StoreIndexes keys c world mark origin dc file (I ++ page) (S.extract 0 o.pos.offset) := by
  obtain ⟨-, hrd, -, hle, -, -, -, -, hI, hcnt, -, hsz, -, -⟩ :=
    seal_facts keys c world mark origin step hw horigin hmono hcap file₀ H I S h hP hseal
  obtain ⟨b, n, d, L, hb, hc, hIL, -, hr, hL⟩ := hS
  have hL' := openWith_indexes keys c world mark origin step hstep file₀ H I S h hb hL
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world mark origin step file₀ H I S h
  rw [hb] at hb'; cases hb'
  have hcount : o.sealed.index.count = L.length := by rw [ho]; exact hc.symm
  obtain ⟨b'', _, _, rs, hb'', hf, -⟩ := openWith_world keys c world mark origin step file₀ H I S h
  rw [hb] at hb''; cases hb''
  have hor : origin o.opened.world = origin b.world := foldlM_origin horigin rs _ _ hf
  obtain ⟨-, hent, -⟩ := seal_at_end _ _ _ _ _ _ _ _ _ hseal
  obtain ⟨hfit, -, -, hp, -, -⟩ := entries_ok hent
  have hes : (sealEntries o.index).toList = o.index.toList := by simp [sealEntries]
  rw [hes] at hp hfit
  have hL'' : Indexes dc keys.segment c.recordBytesMax
      (fun x y => (pure ((S.extract 0 o.pos.offset).extract x (x + y)) : Id ByteArray))
      (L ++ o.index.toList) (o.pos.offset, (mark o.opened.world).1) :=
    Indexes.congr (fun i j (hj : j ≤ o.pos.offset) => (extract_prefix S hj).symm) _ hL'
  refine ⟨_, _, _, L ++ o.index.toList, hrd, ?_, ?_, ?_, ?_, hL''⟩
  · simp only [List.length_append, Array.length_toList]; omega
  · rw [hsz, hcnt, hcount]; simp only [List.length_append, Array.length_toList]; exact Nat.le_refl _
  · dsimp only; simp only [size_extract]; omega
  · intro i hi
    dsimp only
    by_cases hiL : i < L.length
    · rw [Entry.read_extract_append hiL hIL, List.getElem_append_left hiL, hor]; exact hr i hiL
    · obtain ⟨j, rfl⟩ : ∃ j, i = L.length + j := ⟨i - L.length, by omega⟩
      have hj : j < o.index.toList.length := by simp only [List.length_append] at hi; omega
      have hpos : (L.length + j) * entryBytes keys = I.size + j * entryBytes keys := by
        rw [hI, hcount, Nat.add_mul]
      rw [hpos, show I.size + j * entryBytes keys + entryBytes keys =
          I.size + (j * entryBytes keys + entryBytes keys) by omega, extract_append_size_add' rfl, hp,
        List.getElem_append_right (by omega)]
      have hr' := run_read (keys.forStore (origin o.opened.world)) o.sealed.index.count o.index.toList j hj hfit
      rw [entryBytes_forStore, show o.sealed.index.count + j = L.length + j by rw [hcount]] at hr'
      simp only [Nat.add_sub_cancel_left]
      exact hr'

end Nanodregg.Host

namespace Nanodregg.Host.Deployed

open Nanodregg.Kernel Nanodregg.Codec ByteArray

/-- The deployed reopen's step decodes its record to the steps it takes: the step count moves by
their number (`openWith_indexes`' `hstep`). -/
theorem foldStep_decode {w w' : World D} {r : ByteArray} (h : foldStep w r = .ok w') :
    ∃ ts : List (Step D × D), (Record.codec Codec.Deployed.digestCodec).decode r = .ok ts ∧
      (recorder.mark w').1 = (recorder.mark w).1 + ts.length := by
  obtain ⟨ps, hd, hr⟩ := Record.step_rooted (dc := Codec.Deployed.digestCodec) (admit := World.step X.env)
    (root := World.roots X.env) h
  exact ⟨ps, hd, by rw [recorder_mark, recorder_mark]; exact rooted_steps hr⟩

/-- The deployed index is coherent: what `page_nonempty` assumes, and every deployed Store
write keeps (`genesis_indexes`, `import_indexes`, `StoreIndexes.append`, `StoreIndexes.cut_open`,
`sealed_indexes_deployed`). -/
abbrev Coherent (keys : Keys) (file I S : ByteArray) : Prop :=
  StoreIndexes keys c world recorder.mark originChain Codec.Deployed.digestCodec file I S

theorem coherent_reader {keys : Keys} {file H I S : ByteArray} {o : Opening (World D)}
    (hS : Coherent keys file I S)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o) :
    ∃ L : List Entry, L.length = o.sealed.index.count + o.index.size ∧
      Page.Indexes Codec.Deployed.digestCodec keys.segment c.recordBytesMax
        (fun x y => (pure (S.extract x (x + y)) : Id ByteArray)) L (o.pos.offset, (recorder.mark o.opened.world).1) ∧
      ∀ k e, Page.entryAt (m := Id) (keys.forStore (originChain o.opened.world))
        (fun x y => pure (I.extract x (x + y))) o.sealed.index.count o.index k = .ok e → L[k]? = some e := by
  obtain ⟨b, n, d, L, hb, hc, -, -, hr, hL⟩ := hS
  have hL' := openWith_indexes keys c world recorder.mark originChain foldStep
    (fun _ _ _ hs => foldStep_decode hs) file H I S h hb hL
  obtain ⟨b', _, _, _, _, _, hb', _, _, _, _, _, _, _, _, _, _, _, ho⟩ :=
    openWith_seg_ok keys c world recorder.mark originChain foldStep file H I S h
  rw [hb] at hb'; cases hb'
  have hcount : o.sealed.index.count = L.length := by rw [ho]; exact hc.symm
  obtain ⟨b'', _, _, rs, hb'', hf, -⟩ := openWith_world keys c world recorder.mark originChain foldStep file H I S h
  rw [hb] at hb''; cases hb''
  have hor : originChain o.opened.world = originChain b.world :=
    foldlM_origin (fun _ _ _ hs => foldStep_originChain hs) rs _ _ hf
  refine ⟨L ++ o.index.toList, by simp only [List.length_append, Array.length_toList]; omega, hL', ?_⟩
  intro k e hk
  rcases Page.entryAt_ok (rd := fun x y => I.extract x (x + y)) hk with ⟨hlt, hre⟩ | ⟨hge, hm⟩
  · rw [hcount] at hlt
    rw [hor, entryBytes_forStore, hr k hlt] at hre
    rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
    exact hre
  · rw [List.getElem?_append_right (by omega), ← hcount, Array.getElem?_toList]
    exact hm

/-- **A page short of the tip is non-empty, at the deployed instance** (HOST-60's lift, cv
01a15180-9499). Over a Store whose index is coherent (`Coherent`: every deployed write keeps it),
the deployed open's state (the resident a writer or a follower starts from), and the deployed
pager (`Host.Deployed.pager`'s `log` arm over bytes: `Page.build` with `Page.entryAt` over the
base's entries on disk and the open's since, the durable end, the World's mark), every page served
from a `start` below the World's step count holds at least one event. -/
theorem page_nonempty (keys : Keys) (file H I S : ByteArray) {o : Opening (World D)}
    (hS : Coherent keys file I S)
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {start : Nat} (hs : start < o.opened.world.steps) {a : Page.Acc}
    (ha : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain o.opened.world)) (fun x y => pure (I.extract x (x + y)))
        o.sealed.index.count o.index)
      (o.sealed.index.count + o.index.size) o.pos.offset (recorder.mark o.opened.world) start) = .ok a) :
    0 < a.events.size := by
  obtain ⟨L, hlen, hL, hget⟩ := coherent_reader hS h
  rw [← hlen] at ha
  exact Page.build_nonempty Codec.Deployed.digestCodec_lawful.on Page.budget_fits_event hget hL hs ha

/-- **A deployed page is refused `beforeLog` only from below the entry its search reads first**
(HOST-61's entry-0 case): the deployed pager over any the index file and any loop entries, when it
holds an entry and reads entry 0 as `e₀`, refuses `beforeLog` only from a `start` below `e₀`'s step
count. Not proved: that entry 0 is the Store's first record, at step 0 for a Store genesis made and
at the import's step for an imported one (`StoreIndexes` ties each entry to a record, not entry 0
to the first one after the origin frame). -/
theorem page_beforeLog_first (keys : Keys) (I S : ByteArray) (r : Resident (World D)) {start x y : Nat}
    (hc : r.sealed.index.count + r.index.size ≠ 0)
    (ha : Id.run (Page.build X.env Codec.Deployed.digestCodec X.digestOf keys.segment c.recordBytesMax
      Page.budget (fun x y => pure (S.extract x (x + y)))
      (Page.entryAt (keys.forStore (originChain r.world)) (fun x y => pure (I.extract x (x + y)))
        r.sealed.index.count r.index)
      (r.sealed.index.count + r.index.size) r.pos.offset (recorder.mark r.world) start) =
        .error (.beforeLog x y))
    {e₀ : Entry} (h0 : Page.entryAt (m := Id) (keys.forStore (originChain r.world))
      (fun x y => pure (I.extract x (x + y))) r.sealed.index.count r.index 0 = .ok e₀) :
    start < e₀.steps :=
  Page.build_beforeLog_first hc h0 (fun k x' y' hk => by
    have := Page.entryAt_error (rd := fun x y => I.extract x (x + y)) hk
    cases this) ha

/-- `sealed_indexes` at the deployed instance: every premise discharged as in
`sealed_opens_deployed`. -/
theorem sealed_indexes_deployed (keys : Keys) (file₀ H I S : ByteArray) {o : Opening (World D)}
    (h : Id.run (openWith keys c world recorder.mark originChain foldStep file₀ H S.size I.size
      (segReader I) (segReader S)) = .ok o)
    {keep : Keep} {page file : ByteArray} {ix' : IndexAt}
    (hseal : Base.seal (keys.forStore (originChain o.opened.world)) c world o.opened.world o.pos
      o.sealed.index (sealEntries o.index) I.size keep = .ok (page, ix', file))
    (hS : Coherent keys file₀ I S) :
    Coherent keys file (I ++ page) (S.extract 0 o.pos.offset) :=
  sealed_indexes keys c world recorder.mark originChain foldStep
    (Codec.Kernel.world_lawfulOn X.env Codec.Deployed.digestCodec_lawful.on)
    (fun _ _ _ hs => foldStep_originChain hs) (fun _ _ _ hs => foldStep_steps hs) (by decide)
    (fun _ _ _ hs => foldStep_decode hs) file₀ H I S h (openWith_codecFits h) hseal hS

/-- **`host genesis`'s Store has a coherent index**: it holds none. -/
theorem genesis_indexes (keys : Keys) (hkeys : keys.chainBytes = Digest.width) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × D)} {w₀ : World D}
    (hg : Receive.genesis X name nonce allowance founders = .ok w₀) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment := by
  obtain ⟨o, ho, -⟩ := genesis_reopens keys hkeys hg h
  obtain ⟨_, -, rfl⟩ := genesisImage_ok h
  exact StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep _ _ _ _ ho

/-- **`host import`'s Store has a coherent index**: it holds none (a page before its World's step
is refused `beforeLog`, `Page.build_beforeLog_none`). -/
theorem import_indexes (keys : Keys) (hkeys : keys.chainBytes = Digest.width) {name nonce : ByteArray} {want : Codec.Digest} {f : ByteArray}
    {r : Carry.Read D} {w₀ : World D}
    (hi : Carry.importWorld X Codec.Deployed.digestCodec name nonce want f = .ok (w₀, r)) {img : Image}
    (h : genesisImage keys c world recorder.mark w₀ = .ok img) :
    Coherent keys img.base img.index img.segment := by
  obtain ⟨o, ho, -⟩ := import_reopens keys hkeys hi h
  obtain ⟨_, -, rfl⟩ := genesisImage_ok h
  exact StoreIndexes.of_open_empty keys c world recorder.mark originChain foldStep _ _ _ _ ho

end Nanodregg.Host.Deployed
