# What a member trusts

One writer orders a World's history. Members check its proposed history: [Receive.rederive](../Kernel/Receive/Rederive.lean) reconstructs each event against the member's World and checks the transition. Step count includes admitted turns and recorded refusals; height advances with admitted turns.

Trusted computation includes the member's executable, codecs, digests/signatures and custody. The operator sees the World: there is no content secrecy from the writer. Filesystem and process guarantees depend on platform contracts named in [Spec](../Spec/README.md).

A receipt proves a journal/refusal answer against particular roots; it does not authenticate the head itself. Local settlement uses follow's own World. A [foreign receipt](../Protocol/Foreign.lean) uses a head object the receiving World holds. Its soundness premise says the head belongs to a fold of the foreign World, not that it is the latest head.

A head records origin, steps, height, roots and chain. Members compare positions, sign attestations and post heads into ordinary objects. Sync --to detects differing chains at a reached position; --check also checks the attestation and member key. A head object's fork state retains conflicting evidence. These mechanisms expose incompatible histories when evidence is compared; they do not make multiple writers agree.

Genesis inputs can name certifiers and a threshold, committed in the World. [Head.certified](../Protocol/Head.lean) checks distinct listed signers, signatures, threshold and origin. A zero-threshold authority certifies nothing.

A thin joiner accepts an invitation under a sponsor key it trusts and downloads the pinned base. When that World names certifiers, adoption also requires a certificate of exactly its head. Without certifying authority, adoption uses the sponsor pin alone. The consumer reads base.cert; the deployed Store has no certificate producer. A nonzero authority without a valid certificate cannot complete thin adoption.

The certificate is checked beside the sponsor pin. Founders must check the genesis inputs they intend to authorize. Browser visitors obtaining executable and sponsor key from the page server rely on that server for bootstrap.

The member-history theorem retains keyFaithful: an adopt continuation must name the trusted sponsor key. Re-deriving resumed plans does not remove this premise. Law-chain claims also have their stated reference restrictions and canonical-trie premises. Read [Spec's claims and floors](../Spec/README.md) before treating a component theorem as composed assurance.
