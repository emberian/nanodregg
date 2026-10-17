import Codec.Stream

/-!
# Tree — the one recursive codec

A recursive type (LANG's terms and types) is encoded as a `Tree`: a node is a tag byte, a payload
written with the ordinary codecs, and its children. The recursion lives here, once, depth-bounded:
a reader nests at most `depth` levels, and anything deeper is refused (`tooDeep`) before it is
read. A type becomes a `Stream` with `Stream.viaTree`, a refinement of `tree`. Its author proves
only that `toTree` and `ofTree` are inverse (`refine_lawful`); the byte-level canonicity is
`tree_lawful`, proved here.

Wire: `u8 tag ‖ u32le |payload| ‖ payload ‖ u32le |children| ‖ child*`.
-/

namespace Nanodregg.Codec

/-- A node: a tag, the payload bytes, the children. -/
inductive Tree where
  | node (tag : UInt8) (payload : ByteArray) (children : List Tree)
  deriving Inhabited

namespace Tree

/-- `t` nests at most `depth` levels, and every payload and child list is at most `max` long. -/
def fits (max : Nat) : Nat → Tree → Bool
  | 0, _ => false
  | d + 1, node _ p cs => decide (p.size ≤ max) && decide (cs.length ≤ max) && cs.all (fits max d)

/-- The trees `fits` accepts. -/
abbrev Fitting (max d : Nat) := { t : Tree // t.fits max d = true }

/-- The bytes `putD d t` appends, without writing them. -/
def sizeD : Nat → Tree → Nat
  | 0, _ => 0
  | d + 1, node _ p cs => cs.foldl (fun n c => n + sizeD d c) (1 + 4 + p.size + 4)

/-- Write `t` with fuel `d` (enough when `fits max d t`). -/
def putD : Nat → Tree → ByteArray → ByteArray
  | 0, _, buf => buf
  | d + 1, node tag p cs, buf =>
    cs.foldl (fun out c => putD d c out)
      (Stream.u32.put (UInt32.ofNat cs.length) (Stream.u32.put (UInt32.ofNat p.size) (buf.push tag) ++ p))

/-- The bytes of a node's children, one after the other. -/
def kidsBytes (d : Nat) (cs : List Tree) : ByteArray :=
  cs.foldl (fun out c => putD d c out) ByteArray.empty

mutual
/-- Read one tree nested at most `d` levels at offset `i`. The result carries its `fits` proof. -/
def getD (max limit : Nat) (b : ByteArray) : (d : Nat) → Nat → Except Refusal (Fitting max d × Nat)
  | 0, i => .error (.tooDeep i limit)
  | d + 1, i =>
    match Stream.u8.get b i with
    | .error e => .error e
    | .ok (tag, j) =>
      match Stream.u32.get b j with
      | .error e => .error e
      | .ok (n, k) =>
        if hn : n.toNat ≤ max then
          if h : k + n.toNat ≤ b.size then
            match Stream.u32.get b (k + n.toNat) with
            | .error e => .error e
            | .ok (m, l) =>
              if m.toNat ≤ max then
                match getKids max limit b d m.toNat l #[] with
                | .ok (cs, r) =>
                  if hl : cs.size ≤ max then
                    .ok (⟨node tag (b.extract k (k + n.toNat)) (cs.toList.map Subtype.val), by
                      simp only [fits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
                      refine ⟨⟨by simp [ByteArray.size_extract]; omega, by simpa using hl⟩, ?_⟩
                      intro c hc
                      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hc
                      exact x.2⟩, r)
                  else .error (.pastBound l max cs.size)
                | .error e => .error e
              else .error (.pastBound (k + n.toNat) max m.toNat)
          else .error (.truncated k n.toNat)
        else .error (.pastBound j max n.toNat)
termination_by d _ => (d, 0)

/-- Read `n` sibling trees, each nested at most `d` levels. -/
def getKids (max limit : Nat) (b : ByteArray) (d : Nat) :
    Nat → Nat → Array (Fitting max d) → Except Refusal (Array (Fitting max d) × Nat)
  | 0, i, acc => .ok (acc, i)
  | n + 1, i, acc =>
    match getD max limit b d i with
    | .ok (c, j) => getKids max limit b d n j (acc.push c)
    | .error e => .error e
termination_by n _ _ => (d, n + 1)
end

end Tree

namespace Stream

/-- Trees nested at most `depth` levels, with payloads and child lists of at most `max`. -/
def tree (max depth : Nat) (_fits : max < 2 ^ 32 := by decide) : Stream (Tree.Fitting max depth) where
  shape := .tree max depth
  size t := Tree.sizeD depth t.val
  put t buf := Tree.putD depth t.val buf
  get b i := Tree.getD max depth b depth i

end Stream
end Nanodregg.Codec
