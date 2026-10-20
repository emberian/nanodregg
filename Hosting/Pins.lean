/-
# Hosting.Pins — the provider leaf keys keybroker accepts, as the repository ships them (HOSTING-28)

keybroker reads its pins from the operator's PINS file (`HOST SHA256-HEX` lines: the SHA-256 of the
provider's leaf certificate's DER SubjectPublicKeyInfo), checked after rustls has verified the
chain for the host Lean names, and refuses any other leaf `pinMismatch` before a request byte is
written. Only the leaf can be pinned soundly: rustls exposes the chain the server SENT, not the path
it verified, and a forger may send any public intermediate beside a mis-issued leaf.

`deploy/tls/pins` is `text`, emitted by `emit-pins` and checked byte for byte on every commit
(`gates/generated.tsv`), as `deploy/tls/anchors.pem` is. The installed copy is the operator's: a
provider's key rotation is an operator act by the RUNBOOK's recipe, with no rebuild.

`pins` holds ONE pin, `api.anthropic.com`, taken 2026-10-21 by the RUNBOOK §2a recipe (Ember approved
THE PIN; decisions/ops.md OPS-19): leaf CN=api.anthropic.com, issuer Google Trust Services WE1, valid
2026-09-21 18:15:27Z to 2026-12-20 19:15:03Z. The leaf rotates: after 2026-12-20 (sooner if renewed
early) every real call is refused `pinMismatch` until the operator pins the new leaf; the installed
file is the operator's, and a rotation needs no rebuild.
-/

namespace Nanodregg.Hosting.Pins

/-- (host, lowercase hex SHA-256 of a leaf SubjectPublicKeyInfo), in file order. -/
def pins : List (String × String) :=
  [("api.anthropic.com", "9fe3851dbd7a61523c284bb1e372e4e238c5b0aefac4ba256af95c0024045eae")]

/-- The PINS file: one `HOST HEX` line per pin, each ended by LF; empty when no pin is shipped. -/
def text : String := String.join (pins.map fun (h, p) => h ++ " " ++ p ++ "\n")

end Nanodregg.Hosting.Pins
