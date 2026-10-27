/-
# Protocol.Command.Frames — what follow's frames carry, read off their bytes (HOSTING-47)

A frame of follow's machine is `Command.step` on a continuation and a RESULT (the Host's reply,
custody's, the attempt store's). Which events the step can absorb is a function of the result's
bytes alone (`Protocol.Proofs.FollowHead.step_world`), so a list of results bounds every call follow
re-derived on that run. These are the readings the theorems state; no deployed path calls them.

- `pageEvents b`: the events of a log page in `b`, when `b` is the Host's `ok` reply holding one.
- `frameEvents res`: the page in the result as the Host sent it, or in custody's `ok` payload
  (`stepResult`'s two readings; follow absorbs only at a `log` reply's phase).
- `frameCalls res`, `pathCalls S`: the call bytes (`eventCall`) of those events, for one result and
  for the results `S` of a run of frames, in order.
-/
import Protocol.Command.Machine

namespace Nanodregg.Protocol.Command

/-- The events a log page in `b` carries: `b` is the Host's `ok` reply holding a `logPage`; none
otherwise. -/
def pageEvents (b : ByteArray) : List ByteArray :=
  match hostReply b with
  | some (.ok, p) => match logPage p with
    | some pg => pg.events
    | none => []
  | _ => []

/-- The writer's certificate a log page in `b` carries (PROTOCOL-81); empty otherwise. -/
def pageCertificate (b : ByteArray) : ByteArray :=
  match hostReply b with
  | some (.ok, p) => match logPage p with
    | some pg => pg.certificate
    | none => ByteArray.empty
  | _ => ByteArray.empty

/-- The writer's certificate one frame's result carries on a log page, read where `frameEvents`
reads the page's events (the Host's reply, or custody's `ok` payload). -/
def frameCertificate (res : ByteArray) : ByteArray :=
  let c := pageCertificate res
  if c.isEmpty then
    match hostReply res with
    | some (.ok, p) => pageCertificate p
    | _ => ByteArray.empty
  else c

/-- **Every event one frame's result could hand follow's fold**: a log page in the result as the
Host sent it, or in custody's `ok` payload (`stepResult`'s two readings; follow absorbs only at a
`log` reply's phase). A function of the frame's bytes alone, so a list of frames' results bounds
what follow absorbed from them. -/
def frameEvents (res : ByteArray) : List ByteArray :=
  pageEvents res ++ match hostReply res with
    | some (.ok, p) => pageEvents p
    | _ => []

/-- The call bytes every event of a frame's result carries (`frameEvents`, `eventCall`). -/
def frameCalls (res : ByteArray) : List ByteArray := (frameEvents res).map eventCall

/-- Every call byte string the frames' results `S` carry, in order (`frameCalls`). -/
def pathCalls (S : List ByteArray) : List ByteArray := S.flatMap frameCalls

end Nanodregg.Protocol.Command
