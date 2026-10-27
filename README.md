# gh-pages: the nanodregg testground, built

This branch is a build output, not source: only the files the browser loads for the testground
page, assembled by `testground/build/publish.sh` (recipe: `testground/PUBLISH.md` on `main`).
Every republish replaces it whole. Served at https://emberian.github.io/nanodregg/

## The kernel

    kernel.wasm  sha256 6a7c46d611881fb737816a389c98169c8f03856de2b148c96fb213b352e3ce6c  (4905379 bytes)
    built from   nanodregg 6087dd4ab86dc67d69d3d93bda2bc4f84ef932bd (clean tree), Lean v4.30.0, emcc 6.0.9

The page hashes the kernel.wasm it fetched and instantiates those same bytes, and shows the hash in
the World window beside `kernel.json`'s commit, so a visitor can tie the tab's kernel to the commit:
`testground/build/build.sh all WORK` at 6087dd4ab86dc67d69d3d93bda2bc4f84ef932bd makes a kernel.wasm with this sha256 (objects named
by their C's content, the link order sorted).

## In the tab (the default) and the live World

Opening the page runs a whole World in the tab: one writer and one follow per member, all in the
kernel; nothing is sent anywhere. Break anything there. The desktop's **Join the live World** opens `wss://nano.demo.dregg.online/ws` (World origin `1569c3aadac11753e493822fc61f93850695ca07cd3a761cb33b89c15a741101` when this was published); `?live` in the address is the same door.
A visitor of a hosted World is a member: its keys and follow stay in the tab, the follow re-derives
every reply, and the World window lists the members its own fold holds. The keys and membership
are kept in the browser's storage for this page, so a returning visitor is the same member;
**Forget me** deletes them. `?hosted=wss://HOST/ws&join` joins any other hosted World.

What a visitor trusts: whoever serves this page and world.json chooses the kernel and the sponsor
key (deploy/testground/README.md on main); the hash above is how to check the first.
