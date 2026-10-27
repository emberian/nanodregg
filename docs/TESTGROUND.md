# The kernel in a browser

The [testground](../testground/index.html) runs shared Lean kernel and command machinery compiled to WebAssembly. JavaScript handles browser interaction and transport. Local scenarios use a writer in the tab; hosted mode sends writer frames over WebSocket while the follower remains in the tab.

The [build script](../testground/build/build.sh) accepts c WORK, wasm WORK or all WORK after its path testground/build/build.sh. Use a private WORK directory. The C stage uses the pinned Lean toolchain and builds Web.Sim.Testground's closure. The WebAssembly stage requires Emscripten, builds the single-threaded runtime and writes testground/kernel.mjs and kernel.wasm, copying example packages beside the page. The stages can use separate build machines and the generated pack.

Publish the resulting testground/ directory through a static web server, preserving module, WebAssembly and package paths. Use the deployment's normal publishing mechanism; the repository has no separate publish command. Serve over HTTP(S), not a local file URL.

For a hosted World, [run.sh](../deploy/testground/run.sh) accepts genesis STATE, start STATE, serve STATE or stop STATE; PORT selects the loopback relay port. The foreground serve mode keeps the three processes under the Type=simple systemd unit and fails the unit when one process exits. Deployment needs Host and nd-supervise, Node, Python and the built browser kernel. Genesis creates guest-book custody and is an operator action.

The service has a supervised writer socket, guest-book member enrolling visitors, and byte relay exposing WebSocket and invitation/enrollment endpoints. Expose the loopback relay through the operator's TLS proxy. Open the page with ?hosted=wss://HOST/ws&join; each tab is a separate member.

The fork STATE FORK form creates a second writer from the same genesis for the fork demonstration. With the second endpoint supplied through the fork query parameter, the page can compare its guest-book attestation; the follower reports forkedWorld when the reached position has a different chain. These are demonstration Worlds, not a multi-writer operating mode.

Visitors re-execute replies but obtain executable and sponsor key from the page service, making it part of bootstrap trust. A certificate consumer alone does not independently authenticate either download; see [TRUST](TRUST.md).

[Deployment details](../deploy/testground/README.md), [scenarios](../testground/scenario.mjs) and the [hosted runner](../testground/hosted-run.mjs) show the paths through the programs.
