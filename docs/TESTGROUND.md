# The kernel in a browser

The [testground](../testground/index.html) runs shared Lean kernel and command machinery compiled to WebAssembly. JavaScript handles browser interaction and transport. Local scenarios use a writer in the tab; hosted mode sends writer frames over WebSocket while the follower remains in the tab.

The [build script](../testground/build/build.sh) accepts c WORK, wasm WORK or all WORK after its path testground/build/build.sh. Use a private WORK directory. The C stage uses the pinned Lean toolchain and builds Web.Sim.Testground's closure. The WebAssembly stage requires Emscripten, builds the single-threaded runtime and writes testground/kernel.mjs and kernel.wasm, copying example packages beside the page. The stages can use separate build machines and the generated pack.

The WebAssembly stage also writes testground/kernel.json: the commit the C came from, whether the tree was clean, and kernel.wasm's sha256. The page fetches kernel.wasm once, hashes it, instantiates exactly those bytes, and shows the hash beside kernel.json's commit in the World window, so a visitor can tie the tab's kernel to a commit by building it (objects are named by content and the link order is sorted, so one tree gives one sha256).

Publish with [publish.sh](../testground/build/publish.sh) by the recipe in [PUBLISH.md](../testground/PUBLISH.md): it assembles what the browser loads and stamps deployment.json with the deployment's live World, refusing a kernel that no pushed commit names. Serve over HTTP(S), not a local file URL. [publish-check.mjs](../testground/publish-check.mjs) checks a served page in Chromium.

The page opens on a World in the tab, the sandbox. When deployment.json names a live World, a desktop icon and the Start here window offer "Join the live World" (the address ?live is the same door). A visitor who joins is a member: the World window lists the members its own follow's fold holds (tg_members, not a list a server keeps), the Wire window shows its frames, and its keys and membership are kept in the browser's localStorage per relay, so returning to the page makes it the same member again, caught up by re-deriving every Turn since the invitation. "Forget me" deletes them. The kept seeds are toy member keys, readable by any script on the page's origin.

For a hosted World, [run.sh](../deploy/testground/run.sh) accepts genesis STATE, start STATE, serve STATE or stop STATE; PORT selects the loopback relay port. The foreground serve mode keeps the three processes under the Type=simple systemd unit and fails the unit when one process exits. Deployment needs Host and nd-supervise, Node, Python and the built browser kernel. Genesis creates guest-book custody and is an operator action.

The service has a supervised writer socket, guest-book member enrolling visitors, and byte relay exposing WebSocket and invitation/enrollment endpoints. Expose the loopback relay through the operator's TLS proxy. Open the page with ?hosted=wss://HOST/ws&join; each tab is a separate member.

The fork STATE FORK form creates a second writer from the same genesis for the fork demonstration. With the second endpoint supplied through the fork query parameter, the page can compare its guest-book attestation; the follower reports forkedWorld when the reached position has a different chain. These are demonstration Worlds, not a multi-writer operating mode.

Visitors re-execute replies but obtain executable and sponsor key from the page service, making it part of bootstrap trust. A certificate consumer alone does not independently authenticate either download; see [TRUST](TRUST.md).

[Deployment details](../deploy/testground/README.md), [scenarios](../testground/scenario.mjs) and the [hosted runner](../testground/hosted-run.mjs) show the paths through the programs.
