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
- `value_fuel`, `replyText_fuel`: the fuel `replyText` gives its reader (three steps per byte) never
  decides a reading: any more fuel reads the same, for every body.
- `value_depth`: the depth bound is exact, for every body: a reading at depth `d` is the reading at
  any larger depth, kept exactly when its value is nested at most `d` levels (`Within`, where an
  object is a level as an array is).
- Teeth (closed instances, `decide +kernel`): an Anthropic-shaped body with every escape kind and a
  surrogate pair; two text blocks around a non-text block; a decoy `content` inside a string;
  a repeated `content`, a repeated `text`, a lone surrogate, a raw control byte, trailing bytes,
  a text that is not UTF-8, and nesting past `depthMax` are each `replyMalformed`, while nesting
  at the bound is read. Each tooth is a short body: the kernel reads a `ByteArray` index by walking
  a list, so its cost grows with the square of the body (HOSTING-51: a 650-byte body took 12.3 GB);
  a fact about long or deep bodies is a theorem above, not a tooth.
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

/-! ## The fuel never decides, and the depth bound is exact -/

theorem byteAt_lt {b : ByteArray} {i : Nat} {x : UInt8} (h : Json.byteAt b i = some x) : i < b.size := by
  unfold Json.byteAt at h; split at h
  · assumption
  · cases h

theorem ws_ge (b : ByteArray) : ∀ n i, i ≤ Json.ws b n i
  | 0, i => by simp [Json.ws]
  | n + 1, i => by
    have := ws_ge b n (i + 1)
    unfold Json.ws; split
    · split <;> omega
    · omega

theorem dropNum_ge (b : ByteArray) : ∀ n i, i ≤ Json.dropNum b n i
  | 0, i => by simp [Json.dropNum]
  | n + 1, i => by
    have := dropNum_ge b n (i + 1)
    unfold Json.dropNum; split
    · split <;> omega
    · omega

theorem unstrAcc_ge (b : ByteArray) : ∀ n i acc r j, Json.unstrAcc b n i acc = some (r, j) → i ≤ j
  | 0, _, _, _, _, h => by simp [Json.unstrAcc] at h
  | n + 1, i, acc, r, j, h => by
    have ih := unstrAcc_ge b n
    unfold Json.unstrAcc at h
    repeat' (first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
      | (have := ih _ _ _ _ h; omega)
      | (simp at h; done)
      | split at h)

theorem atom_ge (b : ByteArray) (i j : Nat) (h : Json.atom b i = some j) : i ≤ j := by
  have := dropNum_ge b b.size (i + 1)
  unfold Json.atom at h
  repeat' (first
    | (simp only [Option.some.injEq] at h; omega)
    | (simp at h; done)
    | split at h)

/-- Every reading ends at or after where it starts. -/
theorem value_ge (b : ByteArray) : ∀ n,
    (∀ d i v j, Json.value b n d i = some (v, j) → i ≤ j) ∧
    (∀ d i acc vs j, Json.elems b n d i acc = some (vs, j) → i ≤ j) ∧
    (∀ d i acc kvs j, Json.members b n d i acc = some (kvs, j) → i ≤ j)
  | 0 => ⟨fun d i v j h => by simp [Json.value] at h, fun d i acc vs j h => by simp [Json.elems] at h,
      fun d i acc kvs j h => by simp [Json.members] at h⟩
  | n + 1 => by
    obtain ⟨hv, he, hm⟩ := value_ge b n
    refine ⟨fun d i v j h => ?_, fun d i acc vs j h => ?_, fun d i acc kvs j h => ?_⟩
    · cases d with
      | zero => simp [Json.value] at h
      | succ d =>
        have w0 := ws_ge b b.size i
        have w1 := ws_ge b b.size (Json.ws b b.size i + 1)
        simp only [Json.value] at h
        split at h
        · obtain ⟨⟨r, k⟩, hu, hk⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hk
          have := unstrAcc_ge b _ _ _ _ _ hu; omega
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
          · obtain ⟨⟨r, k⟩, hu, hk⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hk
            have := he _ _ _ _ _ hu; omega
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
          · obtain ⟨⟨r, k⟩, hu, hk⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hk
            have := hm _ _ _ _ _ hu; omega
        · obtain ⟨k, hu, hk⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hk
          have := atom_ge b _ _ hu; omega
    · simp only [Json.elems] at h
      split at h
      · simp at h
      · rename_i v k hvk
        have := hv _ _ _ _ hvk
        have := ws_ge b b.size k
        repeat' (first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
          | (have := he _ _ _ _ _ h; omega)
          | (simp at h; done)
          | split at h)
    · simp only [Json.members] at h
      have w0 := ws_ge b b.size i
      split at h
      · split at h
        · simp at h
        · rename_i k j1 hk
          have := unstrAcc_ge b _ _ _ _ _ hk
          have := ws_ge b b.size j1
          split at h
          · split at h
            · simp at h
            · rename_i v j2 hvj
              have := hv _ _ _ _ hvj
              have := ws_ge b b.size j2
              repeat' (first
                | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
                | (have := hm _ _ _ _ _ h; omega)
                | (simp at h; done)
                | split at h)
          · simp at h
      · simp at h

/-- Fuel past the bound never changes a reading: a value at `i` read with at least three steps per
byte left plus one (an array's elements or an object's members: plus two) reads the same with any
more. So the fuel is never what refuses a body. -/
theorem value_fuel (b : ByteArray) : ∀ n,
    (∀ m d i, 3 * (b.size - i) + 1 ≤ n → n ≤ m → Json.value b m d i = Json.value b n d i) ∧
    (∀ m d i acc, 3 * (b.size - i) + 2 ≤ n → n ≤ m → Json.elems b m d i acc = Json.elems b n d i acc) ∧
    (∀ m d i acc, 3 * (b.size - i) + 2 ≤ n → n ≤ m → Json.members b m d i acc = Json.members b n d i acc)
  | 0 => ⟨fun _ _ _ h _ => by omega, fun _ _ _ _ h _ => by omega, fun _ _ _ _ h _ => by omega⟩
  | n + 1 => by
    obtain ⟨hv, he, hm⟩ := value_fuel b n
    refine ⟨fun m d i hb hm' => ?_, fun m d i acc hb hm' => ?_, fun m d i acc hb hm' => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      cases d with
      | zero => simp [Json.value]
      | succ d =>
        have w0 := ws_ge b b.size i
        have w1 := ws_ge b b.size (Json.ws b b.size i + 1)
        simp only [Json.value]
        split
        · rfl
        · rename_i hx
          have := byteAt_lt hx
          split
          · rfl
          · rw [he m d _ [] (by omega) (by omega)]
        · rename_i hx
          have := byteAt_lt hx
          split
          · rfl
          · rw [hm m d _ [] (by omega) (by omega)]
        · rfl
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Json.elems]
      rw [hv m d i (by omega) (by omega)]
      split
      · rfl
      · rename_i v k hvk
        have := (value_ge b n).1 _ _ _ _ hvk
        have := ws_ge b b.size k
        split
        · rename_i hx
          have := byteAt_lt hx
          exact he m d _ _ (by omega) (by omega)
        · rfl
        · rfl
    · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Json.members]
      have w0 := ws_ge b b.size i
      split
      · rename_i hx0
        have := byteAt_lt hx0
        split
        · rfl
        · rename_i k j1 hk
          have := unstrAcc_ge b _ _ _ _ _ hk
          have := ws_ge b b.size j1
          split
          · rename_i hx1
            have := byteAt_lt hx1
            rw [hv m d _ (by omega) (by omega)]
            split
            · rfl
            · rename_i v j2 hvj
              have := (value_ge b n).1 _ _ _ _ hvj
              have := ws_ge b b.size j2
              split
              · rfl
              · split
                · rename_i hx2
                  have := byteAt_lt hx2
                  exact hm m d _ _ (by omega) (by omega)
                · rfl
                · rfl
          · rfl
      · rfl

/-- The fuel `replyText` gives its reader never decides the reading: any more reads the same. -/
theorem replyText_fuel (body : ByteArray) (k : Nat) :
    Json.value body (3 * body.size + 3 + k) Bounds.depthMax 0 =
      Json.value body (3 * body.size + 3) Bounds.depthMax 0 :=
  (value_fuel body _).1 _ _ _ (by omega) (by omega)

/-- `v` is nested at most `d` levels: every value is one level, and an array's elements and an
object's member values sit one level under it. -/
inductive Within : Nat → Json.Value → Prop
  | str {d : Nat} (s : ByteArray) : Within (d + 1) (.str s)
  | atom {d : Nat} : Within (d + 1) .atom
  | arr {d : Nat} {vs : List Json.Value} : (∀ v ∈ vs, Within d v) → Within (d + 1) (.arr vs)
  | obj {d : Nat} {kvs : List (ByteArray × Json.Value)} : (∀ p ∈ kvs, Within d p.2) → Within (d + 1) (.obj kvs)

theorem elems_acc (b : ByteArray) : ∀ n d i acc vs j, Json.elems b n d i acc = some (vs, j) → ∀ v ∈ acc, v ∈ vs
  | 0, _, _, _, _, _, h => by simp [Json.elems] at h
  | n + 1, d, i, acc, vs, j, h => by
    intro v hv
    simp only [Json.elems] at h
    split at h
    · simp at h
    · repeat' (first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [hv])
        | (exact elems_acc b n _ _ _ _ _ h v (List.mem_cons_of_mem _ hv))
        | (simp at h; done)
        | split at h)

theorem members_acc (b : ByteArray) : ∀ n d i acc kvs j, Json.members b n d i acc = some (kvs, j) → ∀ p ∈ acc, p ∈ kvs
  | 0, _, _, _, _, _, h => by simp [Json.members] at h
  | n + 1, d, i, acc, kvs, j, h => by
    intro p hp
    simp only [Json.members] at h
    repeat' (first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [hp])
      | (exact members_acc b n _ _ _ _ _ h p (List.mem_cons_of_mem _ hp))
      | (simp at h; done)
      | split at h)

/-- More depth never changes a reading that succeeded. -/
theorem value_depth_mono (b : ByteArray) : ∀ n,
    (∀ d d' i r, d ≤ d' → Json.value b n d i = some r → Json.value b n d' i = some r) ∧
    (∀ d d' i acc r, d ≤ d' → Json.elems b n d i acc = some r → Json.elems b n d' i acc = some r) ∧
    (∀ d d' i acc r, d ≤ d' → Json.members b n d i acc = some r → Json.members b n d' i acc = some r)
  | 0 => ⟨fun _ _ _ _ _ h => by simp [Json.value] at h, fun _ _ _ _ _ _ h => by simp [Json.elems] at h,
      fun _ _ _ _ _ _ h => by simp [Json.members] at h⟩
  | n + 1 => by
    obtain ⟨hv, he, hm⟩ := value_depth_mono b n
    refine ⟨fun d d' i r hd h => ?_, fun d d' i acc r hd h => ?_, fun d d' i acc r hd h => ?_⟩
    · cases d with
      | zero => simp [Json.value] at h
      | succ d =>
        obtain ⟨d', rfl⟩ : ∃ e, d' = e + 1 := ⟨d' - 1, by omega⟩
        simp only [Json.value] at h ⊢
        split at h
        · rename_i hx; (try simp only [hx]); exact h
        · rename_i hx; (try simp only [hx])
          split at h
          · rename_i hy; (try simp only [hy]); exact h
          · rename_i hy
            obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
            rw [he _ _ _ _ _ (by omega) hp]; rfl
        · rename_i hx; (try simp only [hx])
          split at h
          · rename_i hy; (try simp only [hy]); exact h
          · rename_i hy
            obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
            rw [hm _ _ _ _ _ (by omega) hp]; rfl
        · rename_i x h34 h91 h123
          exact h
    · simp only [Json.elems] at h ⊢
      split at h
      · simp at h
      · rename_i v k hvk
        rw [hv _ _ _ _ hd hvk]
        try simp only
        split at h
        · rename_i hx; (try simp only [hx]); exact he _ _ _ _ _ hd h
        · rename_i hx; (try simp only [hx]); exact h
        · simp at h
    · simp only [Json.members] at h ⊢
      split at h
      · rename_i hx0; (try simp only [hx0])
        split at h
        · simp at h
        · rename_i k j1 hk; (try simp only [hk])
          split at h
          · rename_i hx1; (try simp only [hx1])
            split at h
            · simp at h
            · rename_i v j2 hvj
              rw [hv _ _ _ _ hd hvj]
              try simp only
              split at h
              · simp at h
              · rename_i hacc; (try simp only [hacc])
                split at h
                · rename_i hx2; (try simp only [hx2]); exact hm _ _ _ _ _ hd h
                · rename_i hx2; (try simp only [hx2]); exact h
                · simp at h
          · simp at h
      · simp at h

/-- What a reading at depth `d` returns is nested at most `d` levels. -/
theorem value_within (b : ByteArray) : ∀ n,
    (∀ d i v j, Json.value b n d i = some (v, j) → Within d v) ∧
    (∀ d i acc vs j, Json.elems b n d i acc = some (vs, j) → ∀ v ∈ vs, v ∈ acc ∨ Within d v) ∧
    (∀ d i acc kvs j, Json.members b n d i acc = some (kvs, j) → ∀ p ∈ kvs, p ∈ acc ∨ Within d p.2)
  | 0 => ⟨fun _ _ _ _ h => by simp [Json.value] at h, fun _ _ _ _ _ h => by simp [Json.elems] at h,
      fun _ _ _ _ _ h => by simp [Json.members] at h⟩
  | n + 1 => by
    obtain ⟨hv, he, hm⟩ := value_within b n
    refine ⟨fun d i v j h => ?_, fun d i acc vs j h => ?_, fun d i acc kvs j h => ?_⟩
    · cases d with
      | zero => simp [Json.value] at h
      | succ d =>
        simp only [Json.value] at h
        split at h
        · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hp; rw [← hp.1]; exact .str _
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .arr (by simp)
          · obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hq; rw [← hq.1]
            exact .arr fun w hw => (he _ _ _ _ _ hp w hw).resolve_left (by simp)
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .obj (by simp)
          · obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hq; rw [← hq.1]
            exact .obj fun w hw => (hm _ _ _ _ _ hp w hw).resolve_left (by simp)
        · obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hp; rw [← hp.1]; exact .atom
    · intro w hw
      simp only [Json.elems] at h
      split at h
      · simp at h
      · rename_i v k hvk
        have hW := hv _ _ _ _ hvk
        split at h
        · rcases he _ _ _ _ _ h w hw with h' | h'
          · rcases List.mem_cons.1 h' with rfl | h''
            · exact .inr hW
            · exact .inl h''
          · exact .inr h'
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hw
          rcases List.mem_cons.1 (List.mem_reverse.1 hw) with rfl | h''
          · exact .inr hW
          · exact .inl h''
        · simp at h
    · intro w hw
      simp only [Json.members] at h
      repeat' (first
        | (simp at h; done)
        | (rename_i v j2 hvj _ _ _
           have hW := hv _ _ _ _ hvj
           first
           | (rcases hm _ _ _ _ _ h w hw with h' | h'
              · rcases List.mem_cons.1 h' with rfl | h''
                · exact .inr hW
                · exact .inl h''
              · exact .inr h')
           | (simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hw
              rcases List.mem_cons.1 (List.mem_reverse.1 hw) with rfl | h''
              · exact .inr hW
              · exact .inl h''))
        | split at h)

/-- A reading at another depth whose value is nested at most `d` levels is the reading at `d`. -/
theorem value_depth_conv (b : ByteArray) : ∀ n,
    (∀ d d' i v j, Json.value b n d' i = some (v, j) → Within d v → Json.value b n d i = some (v, j)) ∧
    (∀ d d' i acc vs j, Json.elems b n d' i acc = some (vs, j) → (∀ v ∈ vs, Within d v) →
      Json.elems b n d i acc = some (vs, j)) ∧
    (∀ d d' i acc kvs j, Json.members b n d' i acc = some (kvs, j) → (∀ p ∈ kvs, Within d p.2) →
      Json.members b n d i acc = some (kvs, j))
  | 0 => ⟨fun _ _ _ _ _ h => by simp [Json.value] at h, fun _ _ _ _ _ _ h => by simp [Json.elems] at h,
      fun _ _ _ _ _ _ h => by simp [Json.members] at h⟩
  | n + 1 => by
    obtain ⟨hv, he, hm⟩ := value_depth_conv b n
    refine ⟨fun d d' i v j h hw => ?_, fun d d' i acc vs j h hw => ?_, fun d d' i acc kvs j h hw => ?_⟩
    · cases d' with
      | zero => simp [Json.value] at h
      | succ d' =>
        simp only [Json.value] at h
        split at h
        · rename_i hx
          obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq
          cases hw
          simp only [Json.value]; (try simp only [hx]); rw [hp]; rfl
        · rename_i hx
          split at h
          · rename_i hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            cases hw
            simp only [Json.value]; (try simp only [hx]); (try simp only [hy])
          · rename_i hy
            obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq
            cases hw with
            | arr hs =>
              simp only [Json.value]; (try simp only [hx])
              rw [he _ _ _ _ _ _ hp hs]; rfl
        · rename_i hx
          split at h
          · rename_i hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            cases hw
            simp only [Json.value]; (try simp only [hx]); (try simp only [hy])
          · rename_i hy
            obtain ⟨p, hp, hq⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq
            cases hw with
            | obj hs =>
              simp only [Json.value]; (try simp only [hx])
              rw [hm _ _ _ _ _ _ hp hs]; rfl
        · rename_i x h34 h91 h123
          obtain ⟨k, hk, hq⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq
          cases hw
          simp only [Json.value]
          first
            | (rw [hk]; rfl)
            | (split <;> first
                | (rename_i hz; exact absurd hz h34)
                | (rename_i hz; exact absurd hz h91)
                | (rename_i hz; exact absurd hz h123)
                | (rw [hk]; rfl))
    · simp only [Json.elems] at h ⊢
      split at h
      · simp at h
      · rename_i v k hvk
        split at h
        · rename_i hx
          have hW := hw v (elems_acc b n _ _ _ _ _ h v (List.mem_cons_self ..))
          rw [hv _ _ _ _ _ hvk hW]
          (try simp only); (try simp only [hx])
          exact he _ _ _ _ _ _ h hw
        · rename_i hx
          have h' := h
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          have hW := hw v (by rw [← h'.1]; simp)
          rw [hv _ _ _ _ _ hvk hW]
          (try simp only); (try simp only [hx])
          exact h
        · simp at h
    · simp only [Json.members] at h ⊢
      split at h
      · rename_i hx0; (try simp only [hx0])
        split at h
        · simp at h
        · rename_i k j1 hk; (try simp only [hk])
          split at h
          · rename_i hx1; (try simp only [hx1])
            split at h
            · simp at h
            · rename_i v j2 hvj
              split at h
              · simp at h
              · rename_i hacc
                split at h
                · rename_i hx2
                  have hW := hw (k, v) (members_acc b n _ _ _ _ _ h _ (List.mem_cons_self ..))
                  rw [hv _ _ _ _ _ hvj hW]
                  (try simp only); (try simp only [hacc]); (try simp only [hx2])
                  exact hm _ _ _ _ _ _ h hw
                · rename_i hx2
                  have h' := h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h'
                  have hW := hw (k, v) (by rw [← h'.1]; simp)
                  rw [hv _ _ _ _ _ hvj hW]
                  (try simp only); (try simp only [hacc]); (try simp only [hx2])
                  exact h
                · simp at h
          · simp at h
      · simp at h

/-- The depth bound is exact: a reading at depth `d` is the reading at any larger depth, kept
exactly when its value is nested at most `d` levels. -/
theorem value_depth (b : ByteArray) (n d d' i : Nat) (r : Json.Value × Nat) (hd : d ≤ d') :
    Json.value b n d i = some r ↔ Json.value b n d' i = some r ∧ Within d r.1 :=
  ⟨fun h => ⟨(value_depth_mono b n).1 _ _ _ _ hd h, (value_within b n).1 _ _ _ _ h⟩,
   fun ⟨h, hw⟩ => (value_depth_conv b n).1 _ _ _ _ _ h hw⟩

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

/-- The other escapes: `\b \f \r \t`, uppercase hex, and a three-byte scalar value (`€`). -/
theorem escapes_tooth :
    rd "{\"content\":[{\"type\":\"text\",\"text\":\"\\b\\f\\r\\t\\u00E9\\u20ac\"}]}" =
      .reply ((ByteArray.mk #[8, 12, 13, 9]) ++ "é€".toUTF8) := by decide +kernel

/-- A pretty-printed body (spaces, line feeds, tabs, carriage returns between tokens) is read. -/
theorem whitespace_tooth :
    rd " {\n\t\"content\" : [ {\r\n \"type\" :\"text\" , \"text\": \"w\" } ] ,\n \"n\" : 1 } \n" = .reply "w".toUTF8 := by
  decide +kernel

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
