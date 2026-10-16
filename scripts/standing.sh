#!/usr/bin/env bash
# scripts/standing.sh [REV] — the standing verdict of one commit (default HEAD), on a laptop.
#
#   tip -> gates -> full build -> census + generated files -> sim -> rows -> one line:
#   STANDING <sha> gates=… build=… census=… sim=… rows=… waste=… unmeasured=N => GREEN|RED|INCOMPLETE
#
# GREEN needs every stage to have RUN and passed. A stage that does not exist yet (no `sim`
# lean_exe, no rows/run) is ABSENT, and any ABSENT stage or unmeasured ceiling makes the verdict
# INCOMPLETE, never GREEN: a gate that cannot run is not a pass. The line is also appended to
# <git-common-dir>/nanodregg-standing/verdicts.log.
#   sim:  every lean_exe named `*-sim` (host-sim, kernel-sim, …), run as `lake exe X SEED` for
#         SEED in ${SIM_SEEDS:-1 2 3}: each must exit 0 with a last line `ALL PASS`, else RED
#         naming the first `FAIL <check>`. No `*-sim` exe => sim=ABSENT => INCOMPLETE.
#   rows: `rows/run` in the judged tree, exit 0 = every required row passed
#   waste: the `WASTE <op> <metric> <ratio>` lines the sims print, against gates/waste.tsv
#          (gates/waste.py --measured): a pinned row above its ceiling or unmeasured is RED;
#          no measurement and no row at all is ABSENT (INCOMPLETE)
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
: > "$G/waste.measured"
  sims=$(for e in $(lean_exes "$T"); do case $e in *-sim) echo "$e" ;; esac; done)
  if [ -n "$sims" ]; then
    sim=ok
    for exe in $sims; do
      for seed in ${SIM_SEEDS:-1 2 3}; do
        out=$(env -C "$T" lake exe "$exe" "$seed" 2>&1); rc=$?
        printf '%s\n' "$out" >> "$log"
        printf '%s\n' "$out" | grep '^WASTE ' >> "$G/waste.measured"
        if [ $rc -ne 0 ] || [ "$(printf '%s\n' "$out" | tail -1)" != "ALL PASS" ]; then
          sim="RED($exe $seed: $(printf '%s\n' "$out" | grep -m1 '^FAIL ' || echo "exit $rc"))"
          break 2
        fi
      done
    done
  fi
  if [ -x "$T/rows/run" ]; then rows=$(run env -C "$T" ./rows/run); fi
fi
waste=$(grep -c -v -e '^#' -e '^[[:space:]]*$' "$T/gates/waste.tsv" 2>/dev/null || echo 0)
wastev=ABSENT
if [ -s "$G/waste.measured" ] || [ "$waste" -gt 0 ]; then
  wastev=$(run python3 "$T/gates/waste.py" "$T" --measured "$G/waste.measured")
fi
unpinned=$(grep -c '^unpinned' "$log" || true)
all="$gates $build $census $sim $rows $wastev"
case $all in
  *RED*) verdict=RED ;;
  *ABSENT*) verdict=INCOMPLETE ;;
  *) [ "$unmeasured" -gt 0 ] && verdict=INCOMPLETE || verdict=GREEN ;;
esac
line="STANDING ${sha:0:12} gates=$gates build=$build census=$census sim=$sim rows=$rows waste=$wastev(pinned $waste, unpinned $unpinned) unmeasured=$unmeasured => $verdict"
echo "$line" | tee -a "$G/verdicts.log"
echo "log: $log"
[ "$verdict" = RED ] && exit 1
exit 0
