/-
# Host.Proofs.Cli — `host import` writes no Store path before every check passed (HOST-28's gap)

`Host.Cli.importWith` is `host import`'s decision over its effects (`ImportFx`); the deployed verb
is it at `IO` (`importVerb`), where `genesis` is `Host.genesis`, the only effect that creates a
Store path. Here it runs at `Except (Option (Digest × World D))`, each effect answering a given result,
`genesis` throwing the key and World it was handed and `reopen` (`openWriter`, which truncates and
locks: it writes) throwing `none`: the same function, so the same order of effects. The run ends
`.error (some (k, w))` exactly when `genesis` was reached FIRST among the writing effects, with
`k` and `w`:

* `import_genesis_iff` — `genesis` is the first writing effect reached, with key `k` and World `w`,
  EXACTLY when the digest parsed, the nonce effect answered a nonce, the IN effect answered bytes,
  `Carry.importWorld` accepted them under the digest (stamp, decode, anchor, KERNEL's carry) making
  `w`, and the key effect answered `k` (the bound on IN and the 32-byte key are the IO instance's
  `readBounded` and `Digest.ofBytes?`). Its `→` half is refuse-before-write; its `←` half is the tooth:
  a passing import reaches genesis before `reopen`, with the drawn key, so the claim is false of a
  function that never writes, writes first through `reopen`, or writes before a check.
-/
import Host.Cli
import Host.Proofs.Carry

namespace Nanodregg.Host.Cli

open Nanodregg.Kernel Nanodregg.Codec Nanodregg.Host.Deployed

theorem import_genesis_iff (name digestHex : String) (nonceR : Except Status ByteArray)
    (inR : Except (StoreFault (Record.Fault (Reject D))) ByteArray) (keyR : Option Digest)
    (k : Digest) (w : World D) :
    importWith (m := Except (Option (Digest × World D)))
        { nonce := pure nonceR, readIn := pure inR, key := pure keyR,
          genesis := fun k₀ w₀ => throw (some (k₀, w₀)),
          reopen := fun _ => throw none,
          refuse := fun _ _ => pure 1, report := fun _ => pure () } name digestHex = .error (some (k, w)) ↔
    ∃ want nonce bytes r, hexDigest digestHex = some want ∧ nonceR = .ok nonce ∧ inR = .ok bytes ∧
      Carry.importWorld X Codec.Deployed.digestCodec name.toUTF8 nonce want bytes = .ok (w, r) ∧
      keyR = some k := by
  unfold importWith
  cases hd : hexDigest digestHex <;> cases nonceR <;> cases inR <;>
    simp only [bind, Except.bind, pure, Except.pure] <;>
    (repeat' split) <;> simp_all [Prod.ext_iff, and_comm]

end Nanodregg.Host.Cli
