#!/usr/bin/env bash
# scripts/standing.sh [REV] — the standing verdict of one commit (default HEAD), on a laptop.
#
#   tip -> gates -> full build -> census + generated files -> sim -> rows -> one line:
#   STANDING <sha> gates=… build=… census=… sim=… rows=… unmeasured=N waste=N => GREEN|RED|INCOMPLETE
#
# GREEN needs every stage to have RUN and passed. A stage that does not exist yet (no `sim`
# lean_exe, no rows/run) is ABSENT, and any ABSENT stage or unmeasured ceiling makes the verdict
# INCOMPLETE, never GREEN: a gate that cannot run is not a pass. The line is also appended to
# <git-common-dir>/nanodregg-standing/verdicts.log.
#   sim:  `lake exe sim --seeds 64` in the judged tree (KERNEL's Kernel/Sim + a lean_exe "sim")
#   rows: `rows/run` in the judged tree, exit 0 = every required row passed
set -uo pipefail
. "$(dirname "$0")/gate-lib.sh"
rev=${1:-HEAD}
sha=$(git -C "$repo" rev-parse "$rev") || exit 2
base=$(git -C "$repo" rev-parse -q --verify "$sha^^{tree}" || echo "$empty_tree")
G=$common/nanodregg-standing
lock nanodregg-standing || exit 2
materialize "$sha^{tree}" "$G/tree" || exit 2
materialize "$base" "$G/base" || exit 2
T=$G/tree
log=$G/${sha:0:12}.log
: > "$log"
run() { "$@" >> "$log" 2>&1 && echo ok || echo RED; }

git -C "$repo" log -1 --format=%B "$sha" > "$G/msg"
git -C "$repo" diff --name-only "$base" "$sha^{tree}" > "$G/changed"
gates=$(run python3 "$T/gates/check.py" "$T" --changed "$G/changed" --base-tree "$G/base" --base-size "$G/base/SIZE.md" --base-waste "$G/base/gates/waste.tsv" --message "$G/msg")
unmeasured=$(grep -c '^WARN ' "$log" || true)
# shellcheck disable=SC2046
build=$(run env -C "$T" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake build $(lean_targets "$T"))
census=ABSENT; sim=ABSENT; rows=ABSENT
if [ "$build" = ok ]; then
  census=$(run python3 "$T/gates/census.py" "$T")
  while read -r exe out; do
    [ -n "$exe" ] && [ "$(run env -C "$T" lake exe "$exe" --check "$out")" = RED ] && census=RED
  done < <(generated_checks "$T")
  if python3 -c 'import sys,tomllib; sys.exit(0 if any(e["name"]=="sim" for e in tomllib.load(open(sys.argv[1],"rb")).get("lean_exe",[])) else 1)' "$T/lakefile.toml"; then
    sim=$(run env -C "$T" lake exe sim --seeds "${SIM_SEEDS:-64}")
  fi
  if [ -x "$T/rows/run" ]; then rows=$(run env -C "$T" ./rows/run); fi
fi
waste=$(grep -c -v -e '^#' -e '^[[:space:]]*$' "$T/gates/waste.tsv" 2>/dev/null || echo 0)
all="$gates $build $census $sim $rows"
case $all in
  *RED*) verdict=RED ;;
  *ABSENT*) verdict=INCOMPLETE ;;
  *) [ "$unmeasured" -gt 0 ] && verdict=INCOMPLETE || verdict=GREEN ;;
esac
line="STANDING ${sha:0:12} gates=$gates build=$build census=$census sim=$sim rows=$rows unmeasured=$unmeasured waste-pinned=$waste => $verdict"
echo "$line" | tee -a "$G/verdicts.log"
echo "log: $log"
[ "$verdict" = RED ] && exit 1
exit 0
