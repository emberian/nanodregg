#!/usr/bin/env bash
# scripts/standing.sh [--here] [REV] — the standing verdict of one commit (default HEAD), on a
# laptop. Refused unless this checkout is at main (--here: judge with this checkout's scripts).
#
#   tip -> gates -> full build -> census + generated files -> runs -> waste -> one line:
#   STANDING <sha> gates=… build=… census=… runs=… waste=… unmeasured=N => GREEN|RED|INCOMPLETE
#
# GREEN only when every stage's value is exactly `ok` and no ceiling is unmeasured; any RED stage
# makes the line RED; anything else (ABSENT, INCOMPLETE, KILLED(load)) is INCOMPLETE: a gate that
# cannot run is not a pass. The line is also appended to <git-common-dir>/nanodregg-standing/verdicts.log.
#   runs:  gates/runs.py over every lean_exe gates/runs.tsv classifies as a verdict (sims, journeys,
#          rows, plants), with the arguments the table gives (kernel-sim --seeds 64: its
#          planted-refusal coverage gate judges only >= 16 seeds). ok / INCOMPLETE(first pending
#          run: a row with no driver) / UNJUDGED(first killed or twice-timed-out run) / RED(first red run).
#   waste: the `WASTE <op> <metric> <ratio>` lines the runs print, against gates/waste.tsv
#          (gates/waste.py --measured): a pinned row above its ceiling or unmeasured is RED;
#          no measurement and no row at all is ABSENT (INCOMPLETE)
set -uo pipefail
. "$(dirname "$0")/gate-lib.sh"
here=0
[ "${1:-}" = --here ] && { here=1; shift; }
rev=${1:-HEAD}
# These scripts and gates are the checkout's own: a checkout behind main judges with old gates.
# Run from a checkout at main, or say --here to judge with this checkout's scripts on purpose.
if [ $here = 0 ] && [ "$(git -C "$repo" rev-parse HEAD)" != "$(git -C "$repo" rev-parse refs/heads/main)" ]; then
  echo "standing: REFUSED — this checkout is at $(git -C "$repo" rev-parse --short HEAD), main is $(git -C "$repo" rev-parse --short refs/heads/main): git checkout --detach main, or pass --here" >&2
  exit 2
fi
sha=$(git -C "$repo" rev-parse "$rev") || exit 2
# A parentless commit has nothing to be judged against (the ratchets compare with the parent).
if ! base=$(git -C "$repo" rev-parse -q --verify "$sha^^{tree}"); then
  echo "STANDING ${sha:0:12} => REFUSED(noParent)"; exit 1
fi
G=$common/nanodregg-standing
lock nanodregg-standing || exit 2
export CARGO_TARGET_DIR=$G/cargo-target
materialize "$sha^{tree}" "$G/tree" || exit 2
materialize "$base" "$G/base" || exit 2
T=$G/tree
log=$G/${sha:0:12}.log
: > "$log"
run() { "$@" >> "$log" 2>&1 && echo ok || echo RED; }

git -C "$repo" log -1 --format=%B "$sha" > "$G/msg"
git -C "$repo" diff --name-only "$base" "$sha^{tree}" > "$G/changed"
gates=$(run python3 "$T/gates/check.py" "$T" --changed "$G/changed" --base-tree "$G/base" --base-waste "$G/base/gates/waste.tsv" --message "$G/msg")
unmeasured=$(grep -c '^WARN ' "$log" || true)
# shellcheck disable=SC2046
build=$(run wrapped env -C "$T" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake build $(lean_targets "$T"))
census=ABSENT; runs=ABSENT; : > "$G/waste.measured"
if [ "$build" = ok ]; then
  census=$(run wrapped python3 "$T/gates/census.py" "$T")
  while read -r exe out; do
    [ -n "$exe" ] && [ "$(run generated_check "$T" "$exe" "$out")" = RED ] && census=RED
  done < <(generated_checks "$T")
  # runs: every verdict exe as gates/runs.tsv says (sims, journeys, rows, plants), gates/runs.py.
  # --standing: the `standing:` rows (minutes-long benches) run here and nowhere else (GATES-17)
  wrapped python3 "$T/gates/runs.py" "$T" --standing --waste-out "$G/waste.measured" > "$G/runs.out" 2>> "$log"; rc=$?
  cat "$G/runs.out" >> "$log"
  first() { grep -m1 -E "^  run .*: $1" "$G/runs.out" | sed 's/^  run //'; }
  case $rc in
    0) runs=ok ;;
    3) runs="INCOMPLETE($(first INCOMPLETE))" ;;
    76) runs="UNJUDGED($(first '(KILLED|UNREAD\(timeout)'))" ;;   # killed or timed out twice (GATES-16)
    *) runs="RED($(first 'RED' || echo "runs.py exit $rc"))" ;;
  esac
fi
waste=$(grep -c -v -e '^#' -e '^[[:space:]]*$' "$T/gates/waste.tsv" 2>/dev/null || echo 0)
wastev=ABSENT
if [ -s "$G/waste.measured" ] || [ "$waste" -gt 0 ]; then
  wastev=$(run python3 "$T/gates/waste.py" "$T" --measured "$G/waste.measured")
fi
unpinned=$(grep -c '^unpinned' "$log" || true)
# GREEN only when every stage is the verdict `ok` and no ceiling is unmeasured; any stage that is
# RED makes the line RED; anything else (ABSENT, INCOMPLETE, or a value that is not a verdict) is
# INCOMPLETE.
verdict=GREEN
for v in "$gates" "$build" "$census" "$runs" "$wastev"; do
  case $v in
    ok) ;;
    RED*) verdict=RED; break ;;
    *) verdict=INCOMPLETE ;;
  esac
done
[ $verdict = GREEN ] && [ "$unmeasured" -gt 0 ] && verdict=INCOMPLETE
line="STANDING ${sha:0:12} gates=$gates build=$build census=$census runs=$runs waste=$wastev(pinned $waste, unpinned $unpinned) unmeasured=$unmeasured => $verdict"
echo "$line" | tee -a "$G/verdicts.log"
echo "log: $log"
[ "$verdict" = RED ] && exit 1
exit 0
