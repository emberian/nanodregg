/-
# Hosting.Proofs.Reply — Lean reads the reply text out of the provider's answer (HOSTING-29)

- `Proofs.Broker.reply_printed` (beside the printer's specification it needs): a body holding one
  text block, printed by Lean's own JSON printer (`Broker.Json.str`), is read back to exactly its
  text, for every UTF-8 text up to `replyMax`, whatever bytes it holds.
- `reply_over`: a reply text past `replyMax` is refused.
- `reply_status`: any status other than 200 is passed on as that status, its body unread.
- `reply_encodes`: every verdict `reply` returns has a frame, so `hosting-broker`'s `unencodable`
  end stays unreachable.
- `decodeRequest_reply`, `answerCodec_lawful`, `decodeAnswer_reply`: the frames read back.
- Teeth (closed instances, `decide +kernel`): an Anthropic-shaped body with every escape kind and a
  surrogate pair; two text blocks around a non-text block; a decoy `content` inside a string;
  a repeated `content`, a repeated `text`, a lone surrogate, a raw control byte, trailing bytes,
  a text that is not UTF-8, and nesting past `depthMax` are each `replyMalformed`, while nesting
  at the bound is read.
-/
import Hosting.Reply
import Hosting.Proofs.Broker

namespace Nanodregg.Hosting.Proofs.Reply

open Nanodregg.Codec Nanodregg.Hosting.Broker

/-! ## The status, and the frames -/

theorem reply_status {s : UInt32} (h : s ≠ 200) (body : ByteArray) : Broker.reply s body = .status s := by
  simp [Broker.reply, h]

theorem answerCodec_lawful : Stream.Lawful Wire.answerCodec :=
  Tagged.codec_lawful _ _ _ Proofs.Broker.answerCodes_nodup

theorem decodeRequest_reply (s : UInt32) (b : Bytes Bounds.frameMax) :
    Wire.decodeRequest (Wire.requestCodec.bytes ⟨⟨2, by decide⟩, (s, b, ())⟩) = .ok (.reply s b.val) := by
  simp [Wire.decodeRequest, Stream.decode_bytes Proofs.Broker.requestCodec_lawful, Except.map]

theorem decodeAnswer_reply (t : Bytes Bounds.frameMax) :
    Wire.decodeAnswer (Wire.answerCodec.bytes ⟨⟨0, by decide⟩, (t, ())⟩) = .ok (.reply t.val) := by
  simp [Wire.decodeAnswer, Stream.decode_bytes answerCodec_lawful, Except.map, Wire.answerOf]

/-- Every verdict `reply` returns has a frame: a status is five bytes, a refusal two, and a reply
text of at most `replyMax` bytes fits with its tag and length. -/
theorem reply_encodes (s : UInt32) (body : ByteArray) :
    (Wire.encodeVerdict (Broker.reply s body)).isSome = true := by
  unfold Broker.reply
  split
  · simp only [Wire.encodeVerdict, Wire.verdictWire?, pure, bind, Option.bind]
    rw [← Proofs.Broker.verdictCodec_lawful.size_eq]
    rfl
  · split
    · rename_i t _
      split
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hm : t.size ≤ Bounds.frameMax := by
          have := hc.2; unfold Bounds.replyMax at this; omega
        simp only [Wire.encodeVerdict, Wire.verdictWire?, Wire.bytes?, dif_pos hm, bind, Option.bind, pure]
        rw [← Proofs.Broker.verdictCodec_lawful.size_eq]
        show (if 1 + ((4 + t.size) + 0) ≤ Bounds.frameMax then _ else none).isSome = true
        rw [if_pos (by have := hc.2; unfold Bounds.replyMax at this; unfold Bounds.frameMax at *; omega)]
        rfl
      · exact Proofs.Broker.refuse_encodes _
    · exact Proofs.Broker.refuse_encodes _

/-! ## Teeth -/

private def rd (body : String) : Verdict := Broker.reply 200 body.toUTF8

/-- An Anthropic-shaped body: other fields before and after `content` (a nested `usage` object, a
`null`, numbers), and a text using `\n`, `\"`, `\/`, `\u00e9` and the pair `\ud83d\ude00`. -/
theorem anthropic_tooth : rd "{\"id\":\"msg_01\",\"type\":\"message\",\"role\":\"assistant\",\"model\":\"claude-x\",\"content\":[{\"type\":\"text\",\"text\":\"Hi,\\n\\\"you\\\" \\u00e9\\ud83d\\ude00\\/\"}],\"stop_reason\":\"end_turn\",\"stop_sequence\":null,\"usage\":{\"input_tokens\":10,\"output_tokens\":-5.2e3}}"
    = .reply "Hi,\n\"you\" é😀/".toUTF8 := by decide +kernel

/-- Text blocks are concatenated in order; a block of another type adds nothing. -/
theorem blocks_tooth : rd "{\"content\":[{\"type\":\"text\",\"text\":\"a\"},{\"type\":\"thinking\",\"thinking\":\"zz\"},{\"text\":\"b\",\"type\":\"text\"}]}"
    = .reply "ab".toUTF8 := by decide +kernel

/-- A `content` written inside another field's string is that string's bytes, not a field. -/
theorem decoy_tooth : rd "{\"id\":\"\\\"content\\\":[{\\\"type\\\":\\\"text\\\",\\\"text\\\":\\\"forged\\\"}]\",\"content\":[{\"type\":\"text\",\"text\":\"real\"}]}"
    = .reply "real".toUTF8 := by decide +kernel

theorem malformed_teeth :
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"a\"}],\"content\":[{\"type\":\"text\",\"text\":\"b\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"a\",\"text\":\"b\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"\\ud83d\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"\\ude00\\ud83d\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"a\nb\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"a\"}]} x" = .refuse .replyMalformed ∧
    rd "{\"content\":{\"type\":\"text\",\"text\":\"a\"}}" = .refuse .replyMalformed ∧
    rd "[{\"type\":\"text\",\"text\":\"a\"}]" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"type\":\"text\"}]}" = .refuse .replyMalformed := by decide +kernel

/-- A text that is not UTF-8 (a raw 0xFF byte inside the string) is refused. -/
theorem utf8_tooth :
    Broker.reply 200 ("{\"content\":[{\"type\":\"text\",\"text\":\"".toUTF8 ++ ⟨#[0xFF]⟩ ++ "\"}]}".toUTF8) =
      .refuse .replyMalformed := by decide +kernel

private def nest (k : Nat) : String := "{\"x\":" ++ String.ofList (List.replicate k '[') ++
  String.ofList (List.replicate k ']') ++ ",\"content\":[{\"type\":\"text\",\"text\":\"ok\"}]}"

/-- Nesting at the bound is read; one level past it is refused (the reader's recursion is bounded). -/
theorem depth_tooth : rd (nest 63) = .reply "ok".toUTF8 ∧ rd (nest 64) = .refuse .replyMalformed := by
  decide +kernel

private def nestObj : Nat → String
  | 0 => "{}"
  | k + 1 => "{\"x\":" ++ nestObj k ++ "}"

/-- Objects use up depth as arrays do: a chain of 63 objects is read, 64 are refused. -/
theorem object_depth_tooth :
    rd ("{\"x\":" ++ nestObj 62 ++ ",\"content\":[{\"type\":\"text\",\"text\":\"ok\"}]}") = .reply "ok".toUTF8 ∧
    rd ("{\"x\":" ++ nestObj 63 ++ ",\"content\":[{\"type\":\"text\",\"text\":\"ok\"}]}") = .refuse .replyMalformed := by
  decide +kernel

/-- The other escapes: `\b \f \r \t`, uppercase hex, and a three-byte scalar value (`€`). -/
theorem escapes_tooth :
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"\\b\\f\\r\\t\\u00E9\\u20ac\"}]}" =
      .reply ((ByteArray.mk #[8, 12, 13, 9]) ++ "é€".toUTF8) := by decide +kernel

/-- A pretty-printed body (spaces, line feeds, tabs, carriage returns between tokens) is read. -/
theorem whitespace_tooth :
    rd " {\n\t\"content\" : [ {\r\n \"type\" :\"text\" , \"text\": \"w\" } ] ,\n \"n\" : 1 } \n" = .reply "w".toUTF8 := by
  decide +kernel

/-- A body longer than a small fuel would carry: a 300-element array before `content`. -/
theorem fuel_tooth :
    rd ("{\"x\":[" ++ String.intercalate "," (List.replicate 300 "1") ++ "],\"content\":[{\"type\":\"text\",\"text\":\"f\"}]}") =
      .reply "f".toUTF8 := by decide +kernel

/-- A key repeated in any object of the body (here `id`, and one inside `usage`) is refused; a bad
literal or number, a block without a `type`, and a block that is not an object are refused; no
text block is the empty reply. -/
theorem shape_teeth :
    rd "{\"id\":\"a\",\"id\":\"b\",\"content\":[{\"type\":\"text\",\"text\":\"x\"}]}" = .refuse .replyMalformed ∧
    rd "{\"usage\":{\"n\":1,\"n\":2},\"content\":[{\"type\":\"text\",\"text\":\"x\"}]}" = .refuse .replyMalformed ∧
    rd "{\"a\":Z,\"content\":[{\"type\":\"text\",\"text\":\"x\"}]}" = .refuse .replyMalformed ∧
    rd "{\"a\":tru,\"content\":[{\"type\":\"text\",\"text\":\"x\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[{\"text\":\"x\"}]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[\"x\"]}" = .refuse .replyMalformed ∧
    rd "{\"content\":[]}" = .reply ByteArray.empty ∧
    rd "{\"content\":[{\"type\":\"tool_use\",\"id\":\"t\"}]}" = .reply ByteArray.empty := by decide +kernel

/-- A reply text longer than `replyMax` is refused, whatever else holds. -/
theorem reply_over {body t : ByteArray} (h : Json.replyText body = some t)
    (hl : Bounds.replyMax < t.size) : Broker.reply 200 body = .refuse .replyMalformed := by
  simp only [Broker.reply, h]
  simp
  intro _
  exact hl

theorem status_tooth : Broker.reply 429 "{\"content\":[{\"type\":\"text\",\"text\":\"a\"}]}".toUTF8 = .status 429 := by
  decide +kernel

end Nanodregg.Hosting.Proofs.Reply
