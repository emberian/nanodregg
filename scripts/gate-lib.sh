# Shared by scripts/standing.sh and scripts/converge (the convergence report). Source it; do not run it.
# The report materializes the exact tree it builds into a directory of its own (read-tree -u keeps that
# directory's .lake incremental).

repo=$(git rev-parse --show-toplevel)
common=$(cd "$repo" && cd "$(git rev-parse --git-common-dir)" && pwd)
empty_tree=$(git hash-object -t tree /dev/null)
export PATH=$HOME/.elan/bin:$PATH

# materialize TREE-ISH DIR: make DIR hold exactly that tree (untracked .lake/ survives).
materialize() {
  mkdir -p "$2"
  GIT_INDEX_FILE="$2.index" git -C "$repo" --work-tree="$2" read-tree --reset -u "$1"
}

# The build wrapper is the clone's setting (hbox: `swarm-build`, the cgroup with the enforced memory
# cap; ~/.claude/CLAUDE.md on hbox builds). Every lake/cargo/census invocation runs under it, so a
# lane cannot forget it. Empty elsewhere.
read -r -a wrap <<< "$(git -C "$repo" config nanodregg.buildwrap || true)"
# Every build and run here is at idle I/O and low CPU priority (WORK-RULES 10-27 rule 7: the box is shared).
wrapped() {
  local p=(nice -n 15)
  command -v ionice > /dev/null && p=(ionice -c3 "${p[@]}")
  "${p[@]}" "${wrap[@]}" "$@"
}

# flock_or_refuse: the locks are flock(1) file locks (util-linux): held by an fd of the judging
# process, released when it exits however it exits, so there is no stale-lock logic. A box
# without flock cannot judge (the Mac is a reader since 10-17).
flock_or_refuse() {
  command -v flock > /dev/null || { echo "gate: flock(1) not found; this box cannot judge (main lives on hbox)" >&2; return 1; }
}

# lock NAME: one judge at a time per NAME on fd 8 (deadline 30 min).
lock() {
  flock_or_refuse || return 1
  exec 8> "$common/$1.flock"
  flock -w 1800 8 || { echo "gate: lock $1 held for 30 min; refusing" >&2; return 1; }
}

# slot_count: N, how many rows the convergence runs at once (nanodregg.gateslots; default 4 on hbox, 1 elsewhere):
# runs.py --slots N takes a row token from <common>/nanodregg-gate-K.flock, K = 1..N, per row (GATES-20g).
slot_count() {
  local n
  n=$(git -C "$repo" config nanodregg.gateslots || true)
  if [ -z "$n" ]; then
    if [ "$(git -C "$repo" config --bool nanodregg.landing || true)" = true ]; then n=4; else n=1; fi
  fi
  echo "$n"
}

# lean_targets DIR: every lean_lib and lean_exe name in DIR's lakefile.lean.
lean_targets() { python3 "$1/gates/tree.py" targets "$1"; }

# lean_exes DIR: every lean_exe name (each links the extern_libs, so building them builds the C).
lean_exes() { python3 "$1/gates/tree.py" exes "$1"; }

# generated_checks DIR: one "exe path" line per gates/generated.tsv row.
generated_checks() {
  [ -f "$1/gates/generated.tsv" ] && grep -v -e '^#' -e '^[[:space:]]*$' "$1/gates/generated.tsv" | tr '\t' ' '
}

# generated_check DIR EXE PATH: the generator's own `--check PATH` (exit 0 = the file is exactly
# what it emits). EXE is a lean_exe (`lake exe EXE`), or `cargo:BIN`, a bin of the root Cargo
# workspace (`cargo run --locked --bin BIN`: OPS-2's emit-anchors, whose output widens TLS trust if
# hand-edited, so it is checked like the Lean generators). The convergence's, under the build wrapper (a shell function cannot be handed to swarm-build).
generated_check() {
  local dir=$1 exe=$2 out=$3
  case $exe in
    cargo:*) wrapped env -C "$dir" cargo run --quiet --locked --manifest-path "$dir/Cargo.toml" --bin "${exe#cargo:}" -- --check "$out" ;;
    *) wrapped env -C "$dir" lake exe "$exe" --check "$out" ;;
  esac
}
