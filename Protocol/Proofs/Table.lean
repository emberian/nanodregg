/-
# Protocol.Proofs.Table — what the table guarantees

* decoding is the inverse of encoding and accepts nothing else (`ofCode?_code`, `code_of_ofCode?`),
  for operations, statuses and steps;
* no two operations share a byte, on either socket, so a frame sent to the wrong socket is refused
  rather than reinterpreted (`Op.code_injective`);
* no two operations name the same receiver: no function has two wires (`Op.receiver_injective`) —
  minidregg's twin class (one receiver behind a family opcode and behind op 2, 34 beside 164);
* exactly one operation may append (`Op.effect_write_iff`): one admission path (law 1);
* the client's bounds fit inside one frame.
-/
import Protocol.Table

namespace Nanodregg.Protocol

namespace Op

theorem mem_all (op : Op) : op ∈ all := by cases op <;> decide

theorem code_injective {a b : Op} (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [code] at h)

theorem ofCode?_code (op : Op) : ofCode? op.code = some op := by cases op <;> decide

theorem code_of_ofCode? {b : UInt8} {op : Op} (h : ofCode? b = some op) : op.code = b := by
  have := List.find?_some h
  simpa using this

theorem receiver_injective {a b : Op} (h : a.receiver = b.receiver) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [receiver] at h)

theorem effect_write_iff (op : Op) : op.effect = .write ↔ op = .submit := by
  cases op <;> decide

theorem write_on_host (op : Op) (h : op.effect = .write) : op.socket = .host := by
  rw [(effect_write_iff op).mp h]; rfl

end Op

namespace Status

theorem ofCode?_code (s : Status) : ofCode? s.code = some s := by cases s <;> decide

theorem code_of_ofCode? {b : UInt8} {s : Status} (h : ofCode? b = some s) : s.code = b := by
  have := List.find?_some h
  simpa using this

end Status

namespace Step

theorem ofCode?_code (s : Step) : ofCode? s.code = some s := by cases s <;> decide

theorem code_of_ofCode? {b : UInt8} {s : Step} (h : ofCode? b = some s) : s.code = b := by
  have := List.find?_some h
  simpa using this

end Step

theorem argv_fits_frame : Bounds.argvBytesMax + 1 ≤ Bounds.frameBytesMax := by decide

end Nanodregg.Protocol
