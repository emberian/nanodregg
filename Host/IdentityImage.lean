/- Durable file images for the HOST-71 correspondence proof; no deployed consumer. -/
import Host.Physical

namespace Nanodregg.Host

/-- The durable segment image used to state the physical correspondence. The file layer
realizes this as physicalHeader ++ body; metadata is authenticated by physicalRead. -/
structure SegmentImage where
  generation : Nat
  header : Header
  body : ByteArray

/-- File-system image at a durability boundary. generation is the identity in the atomic
base, not a second independently published file. index is the logical retained index. -/
structure IdentityImage where
  generation : Nat
  base : ByteArray
  index : ByteArray
  files : Nat → Option SegmentImage

def IdentityImage.empty : IdentityImage :=
  ⟨0, .empty, .empty, fun _ => none⟩

/-- The exact naming rule used by genesis, rotation and prepareAdoption. -/
def IdentityImage.put (s : IdentityImage) (f : SegmentImage) : IdentityImage :=
  { s with files := fun id =>
      if id = segmentIdentity f.generation f.header.start then some f else s.files id }

/-- An append or torn-tail truncation changes only the body of an existing identity. -/
def IdentityImage.body (s : IdentityImage) (id : Nat) (edit : ByteArray → ByteArray) : IdentityImage :=
  { s with files := fun j =>
      if j = id then (s.files j).map (fun f => { f with body := edit f.body }) else s.files j }

/-- Atomic base publication (ordinary seal keeps generation; adoption selects its fresh one).
Index bytes are durable before this operation. -/
def IdentityImage.publish (s : IdentityImage) (generation : Nat) (base index : ByteArray) : IdentityImage :=
  { s with generation, base, index }

def IdentityImage.drop (s : IdentityImage) (remove : Nat → Bool) : IdentityImage :=
  { s with files := fun id => if remove id then none else s.files id }

/-- Logical offsets select ONLY the generation committed by the base. The u64 gate is
the header/base codecs' bound; it prevents offset arithmetic from crossing generations. -/
def IdentityImage.at (s : IdentityImage) (offset : Nat) : Option SegmentImage :=
  if offset < 2 ^ 64 then s.files (segmentIdentity s.generation offset) else none

end Nanodregg.Host
