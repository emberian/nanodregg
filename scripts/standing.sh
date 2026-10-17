#!/usr/bin/env bash
# scripts/standing.sh [--here] [REV] — the standing verdict of one commit (default HEAD), on a
# laptop. Refused unless this checkout is at main (--here: judge with this checkout's scripts).
#
#   tip -> gates -> full build -> census + generated files -> sim -> rows -> one line:
#   STANDING <sha> gates=… build=… census=… sim=… rows=… waste=… unmeasured=N => GREEN|RED|INCOMPLETE
#
# GREEN needs every stage to have RUN and passed. A stage that does not exist yet (no `sim`
# lean_exe, no rows/run) is ABSENT, and any ABSENT stage or unmeasured ceiling makes the verdict
# INCOMPLETE, never GREEN: a gate that cannot run is not a pass. The line is also appended to
# <git-common-dir>/nanodregg-standing/verdicts.log.
#   sim:  every lean_exe named `*-sim` (host-sim, kernel-sim, …), run as `lake exe X SEED` for
#         SEED in ${SIM_SEEDS:-1 2 3} (kernel-sim: once, `--seeds 64`, so its planted-refusal
#         coverage gate runs): each must exit 0 with a last line `ALL PASS`, else RED
#         naming the first `FAIL <check>`. No `*-sim` exe => sim=ABSENT => INCOMPLETE.
#   rows: `rows/run` in the judged tree (PROTOCOL's runner, Protocol.Rows.Run): one line per row
#         `ROW <name> PASS|FAIL <why>|PENDING <why>`; exit 0 (`ALL PASS`) = ok, exit 3 (no FAIL,
#         some PENDING: a row with no driver yet) = INCOMPLETE(n pending), anything else = RED
#         naming the first failing row
#   waste: the `WASTE <op> <metric> <ratio>` lines the sims and the rows print, against gates/waste.tsv
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
census=ABSENT; sim=ABSENT; rows=ABSENT
if [ "$build" = ok ]; then
  census=$(run wrapped python3 "$T/gates/census.py" "$T")
  while read -r exe out; do
    [ -n "$exe" ] && [ "$(run wrapped env -C "$T" lake exe "$exe" --check "$out")" = RED ] && census=RED
  done < <(generated_checks "$T")
: > "$G/waste.measured"
  sims=$(for e in $(lean_exes "$T"); do case $e in *-sim) echo "$e" ;; esac; done)
  if [ -n "$sims" ]; then
    sim=ok
    for exe in $sims; do
      # kernel-sim runs once over 64 seeds: its planted-refusal coverage gate (every planted
      # name met at least once) only judges a run of >= 16 seeds (KERNEL-20, ROOT 10-16).
      case $exe in kernel-sim) runs=("--seeds 64") ;; *) runs=(${SIM_SEEDS:-1 2 3}) ;; esac
      for seed in "${runs[@]}"; do
        out=$(wrapped env -C "$T" lake exe "$exe" $seed 2>&1); rc=$?
        printf '%s\n' "$out" >> "$log"
        printf '%s\n' "$out" | grep '^WASTE ' >> "$G/waste.measured"
        if [ $rc -ne 0 ] || [ "$(printf '%s\n' "$out" | tail -1)" != "ALL PASS" ]; then
          sim="RED($exe $seed: $(printf '%s\n' "$out" | grep -m1 '^FAIL ' || echo "exit $rc"))"
          break 2
        fi
      done
    done
  fi
  if [ -x "$T/rows/run" ]; then
    wrapped env -C "$T" ./rows/run > "$G/rows.out" 2>&1; rc=$?
    cat "$G/rows.out" >> "$log"
    grep '^WASTE ' "$G/rows.out" >> "$G/waste.measured"
    case $rc in
      0) rows=ok ;;
      3) rows="INCOMPLETE($(grep -c '^ROW [^ ]* PENDING' "$G/rows.out") pending)" ;;
      *) rows="RED($(grep -m1 '^ROW [^ ]* FAIL' "$G/rows.out" | cut -c5- || echo "exit $rc"))" ;;
    esac
  fi
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
for v in "$gates" "$build" "$census" "$sim" "$rows" "$wastev"; do
  case $v in
    ok) ;;
    RED*) verdict=RED; break ;;
    *) verdict=INCOMPLETE ;;
  esac
done
[ $verdict = GREEN ] && [ "$unmeasured" -gt 0 ] && verdict=INCOMPLETE
line="STANDING ${sha:0:12} gates=$gates build=$build census=$census sim=$sim rows=$rows waste=$wastev(pinned $waste, unpinned $unpinned) unmeasured=$unmeasured => $verdict"
echo "$line" | tee -a "$G/verdicts.log"
echo "log: $log"
[ "$verdict" = RED ] && exit 1
exit 0
