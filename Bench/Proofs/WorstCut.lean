/-
# Bench.Proofs.WorstCut — the bench signer signs the bytes the Sim signs (PERF-12)

`Signer` (Bench.WorstCut) derives a member's Ed25519 key once; its public key and signatures are
`P.pub`'s and `P.sign`'s.
-/
import Bench.WorstCut

namespace Nanodregg.Bench.WorstCut

theorem Signer.pk_eq (secret : ByteArray) : (Signer.of secret).pk = P.pub secret := by
  simp only [Signer.of, P, Kernel.Sim.Deployed.params, Codec.Ed25519.publicKey]

theorem Signer.sign_eq (secret msg : ByteArray) : (Signer.of secret).sign msg = P.sign secret msg := by
  simp only [Signer.of, P, Kernel.Sim.Deployed.params, Codec.Ed25519.sign]
  generalize Codec.Ed25519.expand (Kernel.Sim.Deployed.seed secret) = e
  cases e; rfl

end Nanodregg.Bench.WorstCut
