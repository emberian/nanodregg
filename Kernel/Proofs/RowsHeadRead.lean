/-
# Kernel.Proofs.RowsHeadRead — the phone reads the rows against a head (cv 01a14f7e)

The fourth instance of the head-read family (`Kernel.Proofs.Logic.HeadRead`), beside the cells, the
journal and the refusals. The chain commits the rows' root in `rootsDigest`, so a phone that trusts
one head can be shown a relation's head or a row (its leaf: counters, value, version), or that a rows
key is absent.

* `row_headSound`: the rows trie is a `HeadSound` instance on the leaf codec's domain
  (`Codec.Kernel.RowLeaf.Fits`), at any digest size. Its leaf bodies are injective with NO bound on
  the keys (`rowBody_inj`, from `rowKeyBytes_append_inj`: the relation and the key length are LEB128,
  prefix-free over all of `Nat`); before cv 01a14f7e they were one byte each, wrapping at 256, and
  the rows were no instance.
* `rows_inclusion_sound` / `rows_exclusion_sound`: a proof that verifies against a World's rows root
  tells the truth about the key, or two of the inputs the read compares collide (`inclPres`,
  `readPres`); `row_prove_verifies` / `row_prove_absent`: the World proves every leaf it holds and
  every key it does not.
* `head_rows_read` / `head_rows_absent`: the same against a head record that hashes to the chain any
  step reached, its `rd` opened to the four roots (`head_roots`).
Premises: `hE : E.Lawful n`; the rows trie canonical (`RowsCanon`); for inclusion, the World's rows
invariant (`RowsOk`: every leaf fits, `rowFits_leaf`) and the claimed leaf in the leaf codec's domain
(every counter below 2^64, a value of at most `Bounds.valueBytesMax` bytes). The claimed leaf's bound
is load-bearing: `rowDigest_wraps` / `rows_inclusion_unbounded`. The KEY carries no premise: an
exclusion or inclusion at a key outside `rowFits` (relation 256, a 300-byte key) is as sound as any.
At the deployed codec (`Receive.deployed_*`) every premise but the claimed leaf's bound is discharged
for every World a checked genesis and a fold reach.
-/
import Kernel.Proofs.RowsSep
import Kernel.Proofs.RowsHead
import Kernel.Proofs.RootedDeployed
import Codec.Proofs.Rows

namespace Nanodregg.Kernel

variable {D : Type} [Ord D] [DecidableEq D]

/-! ## The leaf body is injective, for every key -/

omit [Ord D] [DecidableEq D] in
theorem rowKeyBytes_size_pos (E : Env D) (s : RowSlot D) : 0 < (rowKeyBytes E s).size := by
  cases s <;> simp only [rowKeyBytes, rowsPrefix, ByteArray.size_append, byte8_size] <;> omega

omit [DecidableEq D] in
/-- **A rows leaf's body determines its entries**, at any digest size and for every key: each entry
is a key (prefix-free, `rowKeyBytes_append_inj`) then a digest of `n` bytes, and a key is never
empty, so an empty leaf is told from a full one. -/
theorem rowBody_inj {E : Env D} {n : Nat} (hE : E.Lawful n) : ∀ x y : List (RowSlot D × D),
    Trie.leafBody (rowSpec E) x = Trie.leafBody (rowSpec E) y → x = y
  | [], [], _ => rfl
  | [], q :: ys, h => by
      have := congrArg ByteArray.size h
      change 0 = (rowKeyBytes E q.1 ++ E.bytes q.2 ++ Trie.leafBody (rowSpec E) ys).size at this
      have := rowKeyBytes_size_pos E q.1
      simp only [ByteArray.size_append] at *
      omega
  | p :: xs, [], h => by
      have := congrArg ByteArray.size h
      change (rowKeyBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (rowSpec E) xs).size = 0 at this
      have := rowKeyBytes_size_pos E p.1
      simp only [ByteArray.size_append] at *
      omega
  | p :: xs, q :: ys, h => by
      change rowKeyBytes E p.1 ++ E.bytes p.2 ++ Trie.leafBody (rowSpec E) xs =
        rowKeyBytes E q.1 ++ E.bytes q.2 ++ Trie.leafBody (rowSpec E) ys at h
      simp only [ByteArray.append_assoc] at h
      obtain ⟨hk, h⟩ := rowKeyBytes_append_inj hE h
      obtain ⟨hd, ht⟩ := bytes_append_inj h (by rw [hE.size, hE.size])
      rw [Prod.ext hk (hE.bytes_inj hd), rowBody_inj hE xs ys ht]

omit [Ord D] [DecidableEq D] in
/-- Every leaf `rowFits` admits is in the leaf codec's domain. -/
theorem rowFits_leaf {s : RowSlot D} {l : RowLeaf} (h : rowFits s l = true) : Codec.Kernel.RowLeaf.Fits l := by
  cases s <;> cases l <;> simp_all [Codec.Kernel.RowLeaf.Fits, rowFits, Bounds.counterLimit,
    Bounds.rowsPerRelationMax, Bounds.keyBytesMax] <;> omega

/-- **Every leaf of a `RowsOk` World is in the leaf codec's domain.** -/
theorem rowsOk_fits {E : Env D} {w : World D} (hc : w.RowsCanon E) (hw : w.RowsOk E) :
    ∀ k v, rowAt E w.rows k = some v → Codec.Kernel.RowLeaf.Fits v := fun k v hg =>
  rowFits_leaf (hw.1 (k, v) ((Trie.mem_toList (rowSpec E) 0 w.rows hc.1 k v).mpr hg))

/-! ## The World proves what it holds, and what it does not -/

/-- **A World proves every rows leaf it holds.** -/
theorem row_prove_verifies {E : Env D} {w : World D} (hc : w.RowsCanon E) {k : RowSlot D}
    {v : RowLeaf} (hg : rowAt E w.rows k = some v) :
    Trie.verifyInclusion (rowSpec E) (w.rowsRoot E) k (rowDigest E v) (w.rows.prove (rowSpec E) k) = true :=
  Trie.prove_includes (rowSpec E) hc.2.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

/-- **A World proves every rows key it does not hold.** -/
theorem row_prove_absent {E : Env D} {w : World D} (hc : w.RowsCanon E) {k : RowSlot D}
    (hg : rowAt E w.rows k = none) :
    Trie.verifyExclusion (rowSpec E) (w.rowsRoot E) k (w.rows.prove (rowSpec E) k) = true :=
  Trie.prove_excludes (rowSpec E) hc.2.1 hc.1 (Trie.shallow_of_shape _ 0 _ hc.2.2) hg

theorem step_rowsCanon {E : Env D} {w w' : World D} {s : Step D} (hc : w.RowsCanon E)
    (h : World.step E w s = .ok w') : w'.RowsCanon E :=
  fold_rowsCanon hc (l := [s]) (fold_cons_ok.mpr ⟨w', h, rfl⟩)

theorem step_rowsOk {E : Env D} {n : Nat} (hE : E.Lawful n) {w w' : World D} {s : Step D}
    (hc : w.RowsCanon E) (hw : w.RowsOk E) (h : World.step E w s = .ok w') : w'.RowsOk E :=
  fold_rowsOk hE hc hw (l := [s]) (fold_cons_ok.mpr ⟨w', h, rfl⟩)

/-! ## Soundness at the World and at a head -/

section Sound
variable {E : Env D} {n : Nat} (hE : E.Lawful n)

include hE in
omit [DecidableEq D] in
/-- **The rows trie is a `HeadSound` instance** (cv 01a14f7e) on `RowLeaf.Fits`, at any digest size
and with no bound on its keys (`rowBody_inj`). -/
theorem row_headSound : HeadSound E (rowSpec E) Codec.Kernel.RowLeaf.Fits rowLeafPre :=
  ⟨rowBody_inj hE, dbytes_pair_inj hE, fun _ => rfl, fun _ => rfl,
    fun hv hv' h => Codec.Kernel.rowLeafBytes_inj hv hv' (congrArg Prod.snd h)⟩

include hE in
/-- **Rows inclusion is sound at the World**: a claimed leaf proved against the rows root is the
World's leaf at the key, or two of the inputs the read compares collide. -/
theorem rows_inclusion_sound {w : World D} (hc : w.RowsCanon E) (hw : w.RowsOk E) {k : RowSlot D}
    {v : RowLeaf} (hv : Codec.Kernel.RowLeaf.Fits v) {p : Trie.Proof (RowSlot D) D}
    (hp : Trie.verifyInclusion (rowSpec E) (w.rowsRoot E) k (rowDigest E v) p = true) :
    rowAt E w.rows k = some v ∨ CollidesAmong E.hash (inclPres (rowSpec E) rowLeafPre k v p w.rows) :=
  (row_headSound hE).inclusion hc (rowsOk_fits hc hw) hv hp

include hE in
/-- **Rows exclusion is sound at the World**, for every key: a key proved absent against the rows
root is not in the World's rows, or two of the inputs the read compares collide. -/
theorem rows_exclusion_sound {w : World D} (hc : w.RowsCanon E) {k : RowSlot D}
    {p : Trie.Proof (RowSlot D) D} (hp : Trie.verifyExclusion (rowSpec E) (w.rowsRoot E) k p = true) :
    rowAt E w.rows k = none ∨ CollidesAmong E.hash (readPres (rowSpec E) k p w.rows) :=
  (row_headSound hE).exclusion hc hp

include hE in
/-- **The phone's rows read**: a head record that hashes to the chain a step reached, and an
inclusion proof against the record's rows root, show the leaf at the key in that World's rows, or two
of the inputs the opening and the read compare collide. -/
theorem head_rows_read {w w' : World D} {s : Step D} (hc : w.RowsCanon E) (hw : w.RowsOk E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RowSlot D} {v : RowLeaf} (hv : Codec.Kernel.RowLeaf.Fits v) {p : Trie.Proof (RowSlot D) D}
    (hp : Trie.verifyInclusion (rowSpec E) wroot' k (rowDigest E v) p = true) :
    rowAt E w'.rows k = some v ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        inclPres (rowSpec E) rowLeafPre k v p w'.rows) :=
  (row_headSound hE).head_read (fun _ _ _ r => r) (step_rowsCanon hc h) rfl
    (rowsOk_fits (step_rowsCanon hc h) (step_rowsOk hE hc hw h)) (head_roots hE h hhead hrd) hv hp

include hE in
/-- **The phone's rows absence** against a head, for every key: the key is not in that World's rows,
or two of the inputs the opening and the read compare collide. -/
theorem head_rows_absent {w w' : World D} {s : Step D} (hc : w.RowsCanon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RowSlot D} {p : Trie.Proof (RowSlot D) D}
    (hp : Trie.verifyExclusion (rowSpec E) wroot' k p = true) :
    rowAt E w'.rows k = none ∨
      CollidesAmong E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
        readPres (rowSpec E) k p w'.rows) :=
  (row_headSound hE).head_absent (fun _ _ _ r => r) (step_rowsCanon hc h) rfl
    (head_roots hE h hhead hrd) hp

/-! ### Teeth: under `Separates` of the inputs each theorem names, its binding fact alone -/

include hE in
theorem rows_inclusion_sound_sep {w : World D} (hc : w.RowsCanon E) (hw : w.RowsOk E) {k : RowSlot D}
    {v : RowLeaf} (hv : Codec.Kernel.RowLeaf.Fits v) {p : Trie.Proof (RowSlot D) D}
    (hsep : Separates E.hash (inclPres (rowSpec E) rowLeafPre k v p w.rows))
    (hp : Trie.verifyInclusion (rowSpec E) (w.rowsRoot E) k (rowDigest E v) p = true) :
    rowAt E w.rows k = some v :=
  hsep.elim (rows_inclusion_sound hE hc hw hv hp)

include hE in
theorem rows_exclusion_sound_sep {w : World D} (hc : w.RowsCanon E) {k : RowSlot D}
    {p : Trie.Proof (RowSlot D) D} (hsep : Separates E.hash (readPres (rowSpec E) k p w.rows))
    (hp : Trie.verifyExclusion (rowSpec E) (w.rowsRoot E) k p = true) : rowAt E w.rows k = none :=
  hsep.elim (rows_exclusion_sound hE hc hp)

include hE in
theorem head_rows_read_sep {w w' : World D} {s : Step D} (hc : w.RowsCanon E) (hw : w.RowsOk E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RowSlot D} {v : RowLeaf} (hv : Codec.Kernel.RowLeaf.Fits v) {p : Trie.Proof (RowSlot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      inclPres (rowSpec E) rowLeafPre k v p w'.rows))
    (hp : Trie.verifyInclusion (rowSpec E) wroot' k (rowDigest E v) p = true) :
    rowAt E w'.rows k = some v :=
  hsep.elim (head_rows_read hE hc hw h hhead hrd hv hp)

include hE in
theorem head_rows_absent_sep {w w' : World D} {s : Step D} (hc : w.RowsCanon E)
    (h : World.step E w s = .ok w') {prev td rd root' jroot' rroot' wroot' : D} {g : UInt8}
    (hhead : headLink E prev g td rd = w'.chain) (hrd : rootsDigest E root' jroot' rroot' wroot' = rd)
    {k : RowSlot D} {p : Trie.Proof (RowSlot D) D}
    (hsep : Separates E.hash (headPres E w [s] w' prev g td rd root' jroot' rroot' wroot' ++
      readPres (rowSpec E) k p w'.rows))
    (hp : Trie.verifyExclusion (rowSpec E) wroot' k p = true) : rowAt E w'.rows k = none :=
  hsep.elim (head_rows_absent hE hc h hhead hrd hp)

end Sound


/-! ### The defect closed, on a concrete trie (cv 01a14f7e)

A toy `Env` over one-byte digests (`bytes d = [d]`, a fold for the hash) and the rows trie holding one
head: relation 0 under parent 7. Under the one-byte relation, relation 256's key bytes were
`7 ‖ 0 ‖ 0`, relation 0's: the held head's own proof verified an inclusion at relation 256 and no
exclusion of relation 256 verified. -/

private def wrapEnv : Env UInt8 where
  hash _ b := b.foldl (fun a x => a * 31 + x) 7
  bytes d := ⟨#[d]⟩
  turnBytes _ := ByteArray.empty
  cellBytes _ := ByteArray.empty

private def wrapLeaf : RowLeaf := .head 0 0 4 0 2 false 0

private def wrapRows : Rows UInt8 := Trie.T.empty.insert (rowSpec wrapEnv) (.head 7 0) wrapLeaf

/-- TOOTH (`row_headSound` with no key bound): on the one-head trie, the held head's own proof does
NOT verify relation 256's inclusion at the held leaf, relation 256's own exclusion proof verifies,
and relation 0's does not. -/
theorem rows_rel_wrap_read :
    Trie.verifyInclusion (rowSpec wrapEnv) (wrapRows.hashOf (rowSpec wrapEnv)) (.head 7 256)
        (rowDigest wrapEnv wrapLeaf) (wrapRows.prove (rowSpec wrapEnv) (.head 7 0)) = false ∧
      Trie.verifyExclusion (rowSpec wrapEnv) (wrapRows.hashOf (rowSpec wrapEnv)) (.head 7 256)
        (wrapRows.prove (rowSpec wrapEnv) (.head 7 256)) = true ∧
      Trie.verifyExclusion (rowSpec wrapEnv) (wrapRows.hashOf (rowSpec wrapEnv)) (.head 7 0)
        (wrapRows.prove (rowSpec wrapEnv) (.head 7 0)) = false := by
  decide +kernel

private def wrapRowKey : RowSlot UInt8 := .row ⟨7, 0, ByteArray.empty⟩

private def wrapRowRows : Rows UInt8 :=
  Trie.T.empty.insert (rowSpec wrapEnv) wrapRowKey (.row 0 ByteArray.empty 0)

/-- TOOTH (`rows_inclusion_unbounded`, a concrete instance): on a one-row trie holding `.row 0 [] 0`,
the trie's own proof verifies the out-of-domain leaf `.row (2^64) [] 0`, which the trie does not hold.
-/
theorem rows_inclusion_unbounded_toy :
    Trie.verifyInclusion (rowSpec wrapEnv) (wrapRowRows.hashOf (rowSpec wrapEnv)) wrapRowKey
        (rowDigest wrapEnv (.row (2 ^ 64) ByteArray.empty 0)) (wrapRowRows.prove (rowSpec wrapEnv) wrapRowKey) = true ∧
      wrapRowRows.get (rowSpec wrapEnv) wrapRowKey ≠ some (.row (2 ^ 64) ByteArray.empty 0) := by
  decide +kernel

omit [Ord D] [DecidableEq D] in
/-- PLANT (the claimed leaf's bound): past 2^64 a rows leaf digest wraps, with no collision.
`.row (2^64) v u` and `.row 0 v u` have one digest under any `Env`. -/
theorem rowDigest_wraps (E : Env D) (v : ByteArray) (u : Nat) :
    rowDigest E (.row (2 ^ 64) v u) = rowDigest E (.row 0 v u) := by
  have : Nanodregg.Codec.Stream.nat64.bytes (2 ^ 64) = Nanodregg.Codec.Stream.nat64.bytes 0 := by
    rw [Nanodregg.Codec.Stream.nat64_bytes, Nanodregg.Codec.Stream.nat64_bytes]
    congr 1
  simp only [rowDigest, rowLeafBytes]
  rw [this]

/-- TOOTH (`rows_inclusion_sound`'s `hv`): **the claimed leaf's bound is load-bearing.** On any
canonical World holding `.row 0 v u` at `k`, the World's own proof verifies the out-of-domain leaf
`.row (2^64) v u` at `k`, which the World does not hold: dropping `hv`, the first disjunct is false
with no collision in sight. -/
theorem rows_inclusion_unbounded {E : Env D} {w : World D} (hc : w.RowsCanon E) {k : RowSlot D}
    {v : ByteArray} {u : Nat} (hg : rowAt E w.rows k = some (.row 0 v u)) :
    Trie.verifyInclusion (rowSpec E) (w.rowsRoot E) k (rowDigest E (.row (2 ^ 64) v u))
        (w.rows.prove (rowSpec E) k) = true ∧
      rowAt E w.rows k ≠ some (.row (2 ^ 64) v u) := by
  refine ⟨by rw [rowDigest_wraps]; exact row_prove_verifies hc hg, ?_⟩
  rw [hg]; intro h; cases h

end Nanodregg.Kernel

/-! ## At the deployed codec -/

namespace Nanodregg.Kernel.Receive

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Codec.Deployed

/-- **Deployed: every World a checked genesis and a fold reach has canonical rows that keep the rows
invariant**, no premise. -/
theorem deployed_reach_rows (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w : World Digest} {l : List (Step Digest)}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w) :
    w.RowsCanon env ∧ w.RowsOk env := by
  obtain ⟨-, rfl⟩ := genesis_ok.mp hg
  exact ⟨fold_rowsCanon (receive_genesis_rowsCanon (ctx program) name nonce allowance founders) hl,
    fold_rowsOk deployed_lawful (receive_genesis_rowsCanon (ctx program) name nonce allowance founders)
      (receive_genesis_rowsOk (ctx program) name nonce allowance founders) hl⟩

/-- **Deployed: the phone's rows read.** On a World a checked genesis and a fold reach, a head record
that hashes to the chain the next step reached, and an inclusion proof against the record's rows
root, show the leaf in that World's rows, or two of the inputs it compares collide. The one premise
left is the claimed leaf's: its counters below 2^64 and its value within `Bounds.valueBytesMax`. -/
theorem deployed_head_rows_read (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : RowSlot Digest} {v : RowLeaf}
    (hv : Codec.Kernel.RowLeaf.Fits v) {p : Trie.Proof (RowSlot Digest) Digest}
    (hp : Trie.verifyInclusion (rowSpec env) wroot' k (rowDigest env v) p = true) :
    rowAt env w'.rows k = some v ∨
      CollidesAmong env.hash (headPres env w [s] w' prev tag td rd root' jroot' rroot' wroot' ++
        inclPres (rowSpec env) rowLeafPre k v p w'.rows) :=
  head_rows_read deployed_lawful (deployed_reach_rows program hg hl).1 (deployed_reach_rows program hg hl).2
    h hhead hrd hv hp

/-- **Deployed: the phone's rows absence**, no premise, for every key. -/
theorem deployed_head_rows_absent (program : Program Digest) {name nonce : ByteArray} {allowance : Nat}
    {founders : List (ByteArray × Digest)} {g w w' : World Digest} {l : List (Step Digest)} {s : Step Digest}
    (hg : genesis (ctx program) name nonce allowance founders = .ok g) (hl : World.fold env g l = .ok w)
    (h : World.step env w s = .ok w') {prev td rd root' jroot' rroot' wroot' : Digest} {tag : UInt8}
    (hhead : headLink env prev tag td rd = w'.chain)
    (hrd : rootsDigest env root' jroot' rroot' wroot' = rd) {k : RowSlot Digest}
    {p : Trie.Proof (RowSlot Digest) Digest}
    (hp : Trie.verifyExclusion (rowSpec env) wroot' k p = true) :
    rowAt env w'.rows k = none ∨
      CollidesAmong env.hash (headPres env w [s] w' prev tag td rd root' jroot' rroot' wroot' ++
        readPres (rowSpec env) k p w'.rows) :=
  head_rows_absent deployed_lawful (deployed_reach_rows program hg hl).1 h hhead hrd hp

end Nanodregg.Kernel.Receive
