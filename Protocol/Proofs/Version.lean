/-
# Protocol.Proofs.Version — the version is read first, and nothing else is read when it is not ours
-/
import Protocol.Version

namespace Nanodregg.Protocol

/-- The version is `versionBytes` bytes. -/
theorem wireBytes_size : wireBytes.size = versionBytes := by
  simp only [wireBytes, ByteArray.size_extract, wireStamp.size_eq, versionBytes]
  decide

/-- A client's request reads back as its payload: `unwire` inverts `versioned`. -/
theorem unwire_versioned (p : ByteArray) : unwire (versioned p) = .ok p := by
  have hs : versionBytes ≤ (wireBytes ++ p).size := by
    simp only [ByteArray.size_append, wireBytes_size]; omega
  have hv : (wireBytes ++ p).extract 0 versionBytes = wireBytes := by
    rw [← wireBytes_size, ByteArray.extract_append_eq_left (by rfl)]
  have hr : (wireBytes ++ p).extract versionBytes (wireBytes ++ p).size = p := by
    have h := @ByteArray.extract_append_size_add wireBytes p 0 p.size
    rw [Nat.add_zero, ByteArray.extract_zero_size, wireBytes_size] at h
    rw [ByteArray.size_append, wireBytes_size]
    exact h
  simp only [unwire, versioned, versionOf?, hs, if_true, hv, hr]

/-- **A request at another version is refused by name, and the name is the only thing read**: when
the bytes after the op do not begin with this wire's version, `unwire` answers the refusal text of
the version field alone, whatever follows it. -/
theorem unwire_other (b : ByteArray) (h : versionOf? b ≠ some wireBytes) :
    unwire b = .error (wireRefusal (versionOf? b)) := by
  unfold unwire
  split
  · rename_i v hv
    rw [hv] at h
    have : v ≠ wireBytes := fun e => h (by rw [e])
    simp only [this, if_false, hv]
  · rename_i hv
    rw [hv]

/-- **The answer to another version depends on the version field alone**: two requests whose four
bytes after the op are the same, and not ours, are answered alike, however their payloads differ. So
no field after the version is decoded before the version is checked. -/
theorem unwire_reads_only_version (b b' : ByteArray) (h : versionOf? b = versionOf? b')
    (hne : versionOf? b ≠ some wireBytes) : unwire b = unwire b' := by
  rw [unwire_other b hne, unwire_other b' (h ▸ hne), h]

/-- Our own version passes, and what follows it is handed on unread. -/
theorem unwire_ours (b : ByteArray) (h : versionOf? b = some wireBytes) :
    unwire b = .ok (b.extract versionBytes b.size) := by
  simp only [unwire, h, if_true]

end Nanodregg.Protocol
