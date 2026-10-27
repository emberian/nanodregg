# decisions/ — one file per layer, the only place new decisions go (ROOT ruling 2026-10-16 after two stale-index collisions on DECISIONS.md)

Files: kernel.md codec.md host.md protocol.md client.md gates.md lang.md root.md. Format per entry: `## <LAYER>-<n> <title> (<date>)` then decision · alternatives · why · CRITIQUE · META-CRITIQUE · status (open | ruled by ROOT <date> | superseded by <id>). The top-level DECISIONS.md is FROZEN as it stands: existing entries stay there; it gains only an index line per new decision if the owner wants one. Cross-layer answers go in the ANSWERING layer file with a pointer.

The current system guide starts at [docs/OVERVIEW.md](../docs/OVERVIEW.md). Historical design entries retain their original alternatives; corrected status lines identify implemented successors. The archive-recovery obligations are in ROOT-DOCS in [root.md](root.md).
