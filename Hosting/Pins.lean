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

`pins` is EMPTY: no leaf key has been read from any provider, so keybroker refuses every real call
`pinMismatch` until the operator computes the pin at the first real call (Ember's act; nothing in
this tree contacts a provider).
-/

namespace Nanodregg.Hosting.Pins

/-- (host, lowercase hex SHA-256 of a leaf SubjectPublicKeyInfo), in file order. -/
def pins : List (String × String) := []

/-- The PINS file: one `HOST HEX` line per pin, each ended by LF; empty when no pin is shipped. -/
def text : String := String.join (pins.map fun (h, p) => h ++ " " ++ p ++ "\n")

end Nanodregg.Hosting.Pins
