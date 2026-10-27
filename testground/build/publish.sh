#!/usr/bin/env bash
# testground/build/publish.sh OUT LIVE [REPO] — the page as a deployment publishes it: OUT gets exactly
# the files the browser loads (from testground/, after build.sh), kernel.json as build.sh wrote it,
# deployment.json naming this deployment's live World (LIVE, a wss://…/ws relay, or `none`) and the
# repository its commit links to, a README with both hashes, LICENSE and .nojekyll. The live origin is
# this argument, never an edit to the page: testground/PUBLISH.md names the value for each deployment.
#
# It refuses (and writes nothing) unless the kernel can be tied to a commit a visitor can fetch:
# kernel.json's sha256 is kernel.wasm's, its tree was clean, and its commit is on REPO's main as this
# clone last fetched it (origin/main). And unless LIVE answers: its world.json names an origin.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd); tg=$root/testground
out=${1:?usage: publish.sh OUT LIVE [REPO]}; live=${2:?usage: publish.sh OUT LIVE [REPO]}
repo=${3:-https://github.com/emberian/nanodregg}
die() { echo "publish: $*" >&2; exit 1; }
sha() { if command -v sha256sum >/dev/null; then sha256sum < "$1" | cut -c1-64; else shasum -a 256 < "$1" | cut -c1-64; fi; }

[ -f "$tg/kernel.wasm" ] && [ -f "$tg/kernel.json" ] || die "no kernel.wasm/kernel.json in testground/: run build.sh first"
kj() { python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$tg/kernel.json" "$1"; }
commit=$(kj commit); tree=$(kj tree); stamped=$(kj sha256); actual=$(sha "$tg/kernel.wasm")
[ "$stamped" = "$actual" ] || die "kernel.json says sha256 $stamped, kernel.wasm is $actual"
[ "$tree" = clean ] || die "the kernel was built from a $tree tree: no commit names it"
git -C "$root" merge-base --is-ancestor "$commit" origin/main 2>/dev/null || die "commit $commit is not on origin/main (git fetch, or push it first)"
if [ "$live" != none ]; then
  http=$(printf '%s' "$live" | sed -e 's|^ws|http|' -e 's|/ws$||')
  origin=$(curl -sf -m 15 "$http/world.json" | python3 -c 'import json,sys; print(json.load(sys.stdin)["origin"])') \
    || die "the live World does not answer: $http/world.json"
fi

mkdir -p "$out"
for f in index.html testground.css testground.js nd.js transport.js hosted.mjs demos.js kernel.mjs kernel.wasm kernel.json; do
  cp "$tg/$f" "$out/$f"
done
rm -rf "$out/world" && cp -R "$tg/world" "$out/world"
cp "$root/LICENSE" "$out/LICENSE"; touch "$out/.nojekyll"
python3 - "$out/deployment.json" "$live" "$repo" <<'EOF'
import json, sys
out, live, repo = sys.argv[1:]
json.dump({"live": "" if live == "none" else live, "repo": repo}, open(out, "w")); open(out, "a").write("\n")
EOF
door=$([ "$live" = none ] && echo "No live World is linked from this deployment." || echo "The desktop's **Join the live World** opens \`$live\` (World origin \`${origin:-?}\` when this was published); \`?live\` in the address is the same door.")
cat > "$out/README.md" <<EOF
# gh-pages: the nanodregg testground, built

This branch is a build output, not source: only the files the browser loads for the testground
page, assembled by \`testground/build/publish.sh\` (recipe: \`testground/PUBLISH.md\` on \`main\`).
Every republish replaces it whole. Served at https://emberian.github.io/nanodregg/

## The kernel

    kernel.wasm  sha256 $actual  ($(wc -c < "$tg/kernel.wasm" | tr -d ' ') bytes)
    built from   nanodregg $commit (clean tree), Lean $(kj lean), emcc $(kj emcc)

The page hashes the kernel.wasm it fetched and instantiates those same bytes, and shows the hash in
the World window beside \`kernel.json\`'s commit, so a visitor can tie the tab's kernel to the commit:
\`testground/build/build.sh all WORK\` at $commit makes a kernel.wasm with this sha256 (objects named
by their C's content, the link order sorted).

## In the tab (the default) and the live World

Opening the page runs a whole World in the tab: one writer and one follow per member, all in the
kernel; nothing is sent anywhere. Break anything there. $door
A visitor of a hosted World is a member: its keys and follow stay in the tab, the follow re-derives
every reply, and the World window lists the members its own fold holds. The keys and membership
are kept in the browser's storage for this page, so a returning visitor is the same member;
**Forget me** deletes them. \`?hosted=wss://HOST/ws&join\` joins any other hosted World.

What a visitor trusts: whoever serves this page and world.json chooses the kernel and the sponsor
key (deploy/testground/README.md on main); the hash above is how to check the first.
EOF
echo "published into $out: kernel $actual from $commit; live ${live}"
