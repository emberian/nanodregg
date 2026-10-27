# Republishing the testground to GitHub Pages

The page is served from the `gh-pages` branch of emberian/nanodregg at
https://emberian.github.io/nanodregg/ (Pages source: `gh-pages`, `/`). The branch is a build
output: an orphan commit holding only what the browser loads, assembled by `build/publish.sh`.
Every republish replaces it whole. A change to the kernel's closure (wire, rows, `Host.Follow`,
`Web.Sim.Testground`) makes the published kernel stale; republish after it, and rebuild the demo
box's tenant at the same commit when the wire moved (the page's follow and the box's writer must
speak one wire; `dregg-infra-demo-vm/edge/demo/tenants/nd-testground/README.md`, "flag day").

**This deployment's live World:** `wss://nano.demo.dregg.online/ws` (the demo box's tenant
`nd-testground`). It is the `LIVE` argument of step 3 for GitHub Pages (the sandbox mirror, with a door
to the box). The box serves the page itself at https://nano.demo.dregg.online/ (beside /ws, /world.json,
/enroll, /attest): its tarball is assembled with `LIVE` = `self`, and the page then joins
`wss://<its own host>/ws`. It is set here and stamped into
`deployment.json` at publish time, never edited into the page.

## 1. Build the kernel at a pushed commit (hbox: the toolchain and emsdk at ~/tools/emsdk)

    git -C /tank/dregg-build/nanodregg/main fetch -q origin
    git -C /tank/dregg-build/nanodregg/main worktree add --detach ~/nd-land/publish origin/main   # or checkout --detach in it
    cd ~/nd-land/publish     # a warm .lake/build copied from a sibling (cp -a, never cp -al) saves the closure build
    source ~/tools/emsdk/emsdk_env.sh
    SWARM_MEM_MAX=6G LEAN_NUM_THREADS=2 JOBS=3 ionice -c3 nice -n 15 swarm-build testground/build/build.sh all ~/.cache/nd-testground/v4.30.0

`build.sh` writes `testground/kernel.json`: the commit, whether the tree was clean, the sha256 of
`kernel.wasm`, the toolchain. Build from a clean checkout of the commit you publish: `publish.sh`
refuses a dirty tree's kernel, and a commit that is not on `origin/main`.

## 2. Check it (the tree's gate, and the page locally)

    testground/build/gate.sh "$(mktemp -d)"          # every lie, the axes, a hosted World: basic, document, door
    (cd testground && python3 -m http.server 18741 --bind 127.0.0.1 & echo $! > /tmp/tg-http.pid)
    node testground/publish-check.mjs http://127.0.0.1:18741/ /tmp/tg-local   # on a machine with ~/tools/playwright
    kill "$(cat /tmp/tg-http.pid)"

## 3. Assemble and push

    testground/build/publish.sh /tmp/pages-out wss://nano.demo.dregg.online/ws
    git clone -q git@github.com:emberian/nanodregg.git /tmp/pages && cd /tmp/pages
    git checkout -q --orphan gh-pages-new && git rm -rq --cached . && git clean -fdxq
    cp -R /tmp/pages-out/. . && git add -A
    git commit -q -m "testground: the page built from nanodregg main $(python3 -c 'import json; print(json.load(open("kernel.json"))["commit"][:8])')"
    git push -f origin gh-pages-new:gh-pages

`publish.sh OUT LIVE [REPO]` copies the files the browser loads, `kernel.json`, writes
`deployment.json` (`live`, `repo`) and the branch README (both hashes, the door), and refuses unless
`kernel.json`'s sha256 is `kernel.wasm`'s, the tree was clean, the commit is on `origin/main`, the
live World's `world.json` answers, and its `wire.json` (the running writer's own answer to a request with
no version, PROTOCOL-87) names the wire `kernel.json` says the kernel speaks: a box at another commit is
never published behind a page that cannot join it (rebuild the tenant at the commit first). The page
makes the same check before it joins and says so in a sentence. `LIVE` = `none` publishes no door.

## 4. Check the live page (Chromium, Playwright from ~/tools/playwright)

    until [ "$(gh api repos/emberian/nanodregg/pages/builds/latest --jq .status)" = built ]; do sleep 10; done
    node testground/publish-check.mjs https://emberian.github.io/nanodregg/ ~/dev/redregg/work/promo/testground-published --live

It requires: the desktop, "Start here" step 1 `exit ok`, the Writer menu, the World window's
kernel sha256 equal to the tab's own hash of the bytes it runs and to `kernel.json`'s; with `--live`,
the door: joined and enrolled, first sync `ok`, the roster (the tab's own fold) holding the visitor
and the guest-book, the Wire showing its frames, a reload returning the SAME member, and "Forget me"
leaving nothing kept. Each `--live` run enrols one member of the live World (256 per World; the
guest-book keeps the last 16 for the operator), so run it once per publish.
