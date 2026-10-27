/-
# Hosting.Contextual.NanoBridge — nano's free program over effects as an open protocol (lane PROTOCOL)

`Hosting.Resident.Prog` (`cmd | keep | forget | ask | say`, a continuation per result) is the
instance of `Lang.Contextual.Protocol.Prot` with a trivial index (`Unit`) and no holes (`Empty`):
`ofProg` embeds a program, `toEv` reads a performed interaction as nano's trace event, `oracleH` is
nano's oracle as a deterministic environment. Definitions only; the theorems (`nano_runs_iff`,
`nano_interp_agrees`, `nano_interp_runs`) are in `Hosting.Proofs.ContextualNano`.

The resident's two peers and their reliability (PROT-5, Barwell et al.'s reliable roles): `Peer`,
one Boolean per peer (`Peer.reliable`), the ring an effect asks a peer about (`Peer.req`) and
whether its reply was lost (`lostReply`). The theorem reading the Boolean is
`Hosting.Proofs.ContextualFailures` (`Failures.lost_reply_policy`).
-/
import Lang.Contextual.Protocol
import Hosting.Resident.Trace

namespace Nanodregg.Lang.Contextual.Protocol.Nano

open Nanodregg.Hosting Nanodregg.Hosting.Resident

/-- Nano's five effects as operation shapes. -/
inductive NOp
  | cmd (c : Cmd)
  | keep (r : Ring) (t : ByteArray)
  | forget
  | ask (r : Ring) (q : Broker.Ask)
  | say (s : String)

/-- Each effect's result type, as `Prog`'s continuations take it. -/
def NOp.Resp : NOp → Type
  | .cmd _ => Except String Reply
  | .keep _ _ => Bool
  | .forget => Bool
  | .ask _ _ => AskEnd
  | .say _ => Unit

/-- The trivially indexed signature of nano's effects. -/
def sig : Sig Unit where
  Op := fun _ => NOp
  Resp := fun op => NOp.Resp op
  next := fun _ _ => ()

/-- A nano program as an open protocol without holes. -/
def ofProg {α : Type} : Prog α → Prot sig (fun _ => Empty) (fun _ => α) ()
  | .done a => .ret a
  | .cmd c k => .call (S := sig) (NOp.cmd c) fun x => ofProg (k x)
  | .keep r t k => .call (S := sig) (NOp.keep r t) fun b => ofProg (k b)
  | .forget k => .call (S := sig) NOp.forget fun b => ofProg (k b)
  | .ask r q k => .call (S := sig) (NOp.ask r q) fun x => ofProg (k x)
  | .say s k => .call (S := sig) (NOp.say s) fun _ => ofProg k

/-- A performed interaction as nano's trace event. -/
def toEv : Entry sig → Ev
  | ⟨_, op, r⟩ => match op, r with
    | .cmd c, x => .cmd c x
    | .keep r t, b => .keep r t b
    | .forget, b => .forget b
    | .ask r q, x => .ask r q x
    | .say s, _ => .say s

/-- The oracle as a deterministic environment whose state is the call counter. -/
def oracleH (o : Oracle) : Handler sig (fun _ => Nat) where
  handle := fun op n => match op with
    | .cmd _ => ⟨o.cmd n, n + 1⟩
    | .keep _ _ => ⟨o.keep n, n + 1⟩
    | .forget => ⟨o.forget n, n + 1⟩
    | .ask _ _ => ⟨o.ask n, n + 1⟩
    | .say _ => ⟨(), n + 1⟩

/-- The resident's two peers: the member's kernel (every `cmd` goes to it through the member socket)
and keybroker (every `ask`). The volume and stderr are the resident's own, not peers. -/
inductive Peer
  | kernel
  | broker
deriving DecidableEq, Repr

/-- One Boolean per peer: may a request whose reply was lost be sent again? The kernel is RELIABLE:
an exact retry of a signed call is `replayed` from the journal at the height it committed
(`Failures.submit_at_most_once`), and the resident's re-delivery is a fresh call the bell's
`answered` guard refuses after the first landed. Keybroker is UNRELIABLE: it charges the meter per
ask and deduplicates nothing, so a spent ask is never sent again. -/
def Peer.reliable : Peer → Bool
  | .kernel => true
  | .broker => false

/-- The ring an effect asks peer `p` about: an invoke of an answer (the kernel), an ask (keybroker). -/
def Peer.req : Peer → Ev → Option Ring
  | .kernel, .cmd (.invoke _ r _) _ => some r
  | .broker, .ask r _ _ => some r
  | _, _ => none

/-- The effect's reply was lost: a command whose reply never came back, an ask that ended `lost`
(it left in full, so it is spent). -/
def lostReply : Ev → Bool
  | .cmd _ (.error _) => true
  | .ask _ _ (.lost _) => true
  | _ => false

end Nanodregg.Lang.Contextual.Protocol.Nano
