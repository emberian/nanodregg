#!/usr/bin/env bash
# scripts/standing.sh [--here] [REV] — the standing verdict of one commit (default HEAD), on a
# laptop. Refused unless this checkout is at main (--here: judge with this checkout's scripts).
#
#   tip -> gates -> full build -> census -> generated files -> the Rust workspace -> runs -> waste -> one line:
#   STANDING <sha> gates=… build=… census=… generated=… cargo=… runs=… waste=… unmeasured=N … carried=N daily=N => GREEN|RED|INCOMPLETE
#   and a time line, `stages: gates=Ns build=Ns census=Ns generated=Ns cargo=Ns runs=Ns waste=Ns total=Ns`, by this
#   script's clock (also <sha12>.times); runs.py prints each row's own `  time ROW: N s` (GATES-20g). Times are
#   REPORTED, never gated.
# THE CARRY (GATES-20l; Ember 10-21 via ROOT: a docs-only delta converges in minutes): what the delta since the last
# run cannot reach is not run again, and nothing is carried for more than a day (ND_DAILY seconds, default 86400):
#   build   carried when the build inputs (every .lean, .c and .h, lakefile.lean, lean-toolchain, lake-manifest.json,
#           as git blob ids) are byte-identical to those of the last build that read ok in this directory (its .lake
#           is that build's product): `build=ok(carried SHA: inputs byte-identical)`;
#   census  the same over the build inputs and every path under gates/ (the census reads the allow tables there);
#   rows    gates/runs.py --reuse/--record/--daily: a row whose traced key is byte-identical to its last ok run's.
# Everything else (the gates, the generated files, the Rust workspace, the waste ceilings) runs every time.
# It is THE CONVERGENCE (GATES-22): scripts/converge runs it on main every 3 h while landings happen, and every
# check a FAST landing does not run is here: the census, the generated files, the whole Rust workspace (cargo
# check, clippy -D warnings, rustfmt; per landing since GATES-22 only check + fmt of the reached packages), every
# row (the benches included) and the waste ceilings.
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
daily=${ND_DAILY:-86400}
t_start=$(date +%s); t_last=$t_start; times=""
lap() { local now; now=$(date +%s); times="$times $1=$(( now - t_last ))s"; t_last=$now; }
# input_key KIND: sha256 over the blob ids of the paths a stage reads (build: the build inputs; census: those and
# gates/), from the judged tree object: equal keys are byte-identical inputs.
input_key() {
  git -C "$repo" ls-tree -r "$sha^{tree}" | awk -v k="$1" -F '\t' '{ split($1, m, " "); p = $2
    if (p ~ /\.(lean|c|h)$/ || p == "lakefile.lean" || p == "lean-toolchain" || p == "lake-manifest.json" ||
        (k == "census" && p ~ /^gates\//)) print m[3] "\t" p }' | sha256sum | cut -c1-64
}
# carried KIND KEY: `ok(carried SHA: …)` when KIND's last ok run in this directory had KEY less than $daily s ago
carried() {
  local f=$G/$1.carry k s at
  [ -f "$f" ] && read -r k s at < "$f" || return 1
  [ "$k" = "$2" ] && [ $(( $(date +%s) - at )) -le "$daily" ] && echo "ok(carried ${s:0:12}: inputs byte-identical)"
}

git -C "$repo" log -1 --format=%B "$sha" > "$G/msg"
git -C "$repo" diff --name-only "$base" "$sha^{tree}" > "$G/changed"
gates=$(run python3 "$T/gates/check.py" "$T" --changed "$G/changed" --base-tree "$G/base" --base-waste "$G/base/gates/waste.tsv" --message "$G/msg")
unmeasured=$(grep -c '^WARN ' "$log" || true)
lap gates
bkey=$(input_key build); ckey=$(input_key census)
if ! build=$(carried build "$bkey"); then
  rm -f "$G/build.carry" "$G/census.carry"   # this directory's .lake is about to change
  # shellcheck disable=SC2046
  build=$(run wrapped env -C "$T" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" lake build $(lean_targets "$T"))
  [ "$build" = ok ] && echo "$bkey $sha $(date +%s)" > "$G/build.carry"
fi
lap build
census=ABSENT; generated=ABSENT; runs=ABSENT; : > "$G/waste.measured"
# The Rust workspace whole (it needs no Lean build): what pre-push judged on every Rust landing until GATES-22.
cargo=ok
if [ -f "$T/Cargo.toml" ]; then
  for c in "check --quiet --locked --workspace --all-targets" "clippy --quiet --locked --workspace --all-targets" "fmt --all --check"; do
    # shellcheck disable=SC2086
    if [ "${c%% *}" = clippy ]; then r=$(run wrapped cargo $c --manifest-path "$T/Cargo.toml" -- -D warnings)
    else r=$(run wrapped cargo $c --manifest-path "$T/Cargo.toml"); fi
    [ "$r" = ok ] || { cargo="RED(cargo ${c%% *})"; break; }
  done
fi
lap cargo
case $build in ok|ok\(carried*) built=1 ;; *) built=0 ;; esac
if [ $built = 1 ]; then
  if ! census=$(carried census "$ckey"); then
    rm -f "$G/census.carry"
    census=$(run wrapped python3 "$T/gates/census.py" "$T")
    [ "$census" = ok ] && echo "$ckey $sha $(date +%s)" > "$G/census.carry"
  fi
  lap census
  generated=ok gred=""
  while read -r exe out; do
    [ -n "$exe" ] && [ "$(run generated_check "$T" "$exe" "$out")" = RED ] && gred="$gred${gred:+,}$out"
  done < <(generated_checks "$T")
  [ -n "$gred" ] && generated="RED($gred)"
  lap generated
  # runs: every verdict exe as gates/runs.tsv says (sims, journeys, rows, plants), gates/runs.py.
  # --standing: the `standing:` rows (minutes-long benches) run here and nowhere else (GATES-17)
  # GATES-20: every run traced; the re-trace check reds a fresh read-set the stored one (same key) omits;
  # reads outside the tree are REPORTED (`outside=N` below; RED is GATES-20c, trigger: the census sorted);
  # a row whose trace could not be read (`untraced=N`, GATES-20d) leaves its re-trace unjudged: INCOMPLETE.
  # GATES-20g: rows run concurrently, at most N (the judge slot count) at once: standing's own lock runs one row and
  # each further row borrows a FREE judge slot for its run (never while a lander waits for one), so a convergence
  # holds at most N-1 judge slots at any moment and gives each back at its row's end.
  # GATES-20l: a row whose traced key is byte-identical to its last ok run's (carry.record) is carried, unless that
  # run is older than $daily s; the record is replaced by this run's (ok rows only: a red is never carried).
  : > "$G/carry.new"
  wrapped python3 "$T/gates/runs.py" "$T" --standing --waste-out "$G/waste.measured" \
    --traces "$common/nanodregg-traces" --tree-oid "$(git -C "$repo" rev-parse "$sha^{tree}")" \
    --slots-dir "$common" --slots "$(slot_count)" --reuse "$G/carry.record" --record "$G/carry.new" --daily "$daily" \
    > "$G/runs.out" 2>> "$log"; rc=$?
  mv -f "$G/carry.new" "$G/carry.record"
  cat "$G/runs.out" >> "$log"
  lap runs
  cp "$G/runs.out" "$G/${sha:0:12}.runs.out"   # scripts/converge attributes its red rows from it
  first() { grep -m1 -E "^  run .*: $1" "$G/runs.out" | sed 's/^  run //'; }
  case $rc in
    0) runs=ok ;;
    3) runs="INCOMPLETE($(first INCOMPLETE))" ;;
    76) runs="UNJUDGED($(first '(KILLED|UNREAD\((timeout|tracer))'))" ;;   # killed, timed out or tracer failed twice
    *) runs="RED($(first 'RED' || echo "runs.py exit $rc"))" ;;
  esac
fi
waste=$(grep -c -v -e '^#' -e '^[[:space:]]*$' "$T/gates/waste.tsv" 2>/dev/null || echo 0)
wastev=ABSENT
if [ -s "$G/waste.measured" ] || [ "$waste" -gt 0 ]; then
  wastev=$(run python3 "$T/gates/waste.py" "$T" --measured "$G/waste.measured")
fi
lap waste
carriedn=$(grep -c '^  carry .*: carried ' "$G/runs.out" 2>/dev/null || true)
dailyn=$(grep -c '^  daily ' "$G/runs.out" 2>/dev/null || true)
unpinned=$(grep -c '^unpinned' "$log" || true)
outside=$(grep -c '^  outside ' "$G/runs.out" 2>/dev/null || true)
traced=$(grep -q '^  trace: strace unavailable' "$G/runs.out" 2>/dev/null && echo untraced || echo traced)
untraced=$(grep -c '^  untraced ' "$G/runs.out" 2>/dev/null || true)
flakes=$(grep -c '^  flake ' "$G/runs.out" 2>/dev/null || true)
# GREEN only when every stage is the verdict `ok` and no ceiling is unmeasured; any stage that is
# RED makes the line RED; anything else (ABSENT, INCOMPLETE, or a value that is not a verdict) is
# INCOMPLETE.
verdict=GREEN
for v in "$gates" "$build" "$census" "$generated" "$cargo" "$runs" "$wastev"; do
  case $v in
    ok|ok\(carried*) ;;
    RED*) verdict=RED; break ;;
    *) verdict=INCOMPLETE ;;
  esac
done
[ $verdict = GREEN ] && [ "$unmeasured" -gt 0 ] && verdict=INCOMPLETE
[ $verdict = GREEN ] && [ "${untraced:-0}" -gt 0 ] && verdict=INCOMPLETE
line="STANDING ${sha:0:12} gates=$gates build=$build census=$census generated=$generated cargo=$cargo runs=$runs waste=$wastev(pinned $waste, unpinned $unpinned) unmeasured=$unmeasured outside=${outside:-0}($traced) untraced=${untraced:-0} flakes=${flakes:-0} carried=${carriedn:-0} daily=${dailyn:-0} => $verdict"
echo "$line" | tee -a "$G/verdicts.log"
echo "stages:$times total=$(( $(date +%s) - t_start ))s" | tee "$G/${sha:0:12}.times"
echo "log: $log"
[ "$verdict" = RED ] && exit 1
exit 0
