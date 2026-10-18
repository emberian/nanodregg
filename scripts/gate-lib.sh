# Shared by scripts/commit, scripts/pre-push and scripts/standing.sh. Source it; do not run it.
#
# A gate never builds the shared working tree: six agents edit it at once and it is always
# greener or redder than any commit. It materializes the exact tree being judged into a private
# directory under the git common dir (read-tree -u keeps that directory's .lake incremental).

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
wrapped() { "${wrap[@]}" "$@"; }

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

# gate_slot: take one of N judge slots, N = nanodregg.gateslots (default 4 on the landing clone, 1
# elsewhere); each slot is a directory with its own tree, base, .lake and cargo target. Sets G to
# the slot directory; fd 9 holds the slot until this process exits (call it in the judging shell
# itself, never in `$(…)`: a subshell's lock dies with the subshell). The first free slot is taken
# at once; when all are busy, this process waits on one (pid mod N) for at most 30 min.
gate_slot() {
  flock_or_refuse || return 1
  local n k
  n=$(git -C "$repo" config nanodregg.gateslots || true)
  if [ -z "$n" ]; then
    if [ "$(git -C "$repo" config --bool nanodregg.landing || true)" = true ]; then n=4; else n=1; fi
  fi
  for k in $(seq 1 "$n"); do
    exec 9> "$common/nanodregg-gate-$k.flock"
    if flock -n 9; then G=$common/nanodregg-gate-$k; return 0; fi
  done
  k=$(( $$ % n + 1 ))
  exec 9> "$common/nanodregg-gate-$k.flock"
  flock -w 1800 9 || { echo "gate: every judge slot busy for 30 min; refusing" >&2; return 1; }
  G=$common/nanodregg-gate-$k
}

# lean_targets DIR: every lean_lib and lean_exe name in DIR's lakefile.lean.
lean_targets() { python3 "$1/gates/tree.py" targets "$1"; }

# lean_exes DIR: every lean_exe name (each links the extern_libs, so building them builds the C).
lean_exes() { python3 "$1/gates/tree.py" exes "$1"; }

# rust_changed BASE CAND: prints `workspace` when the Rust workspace must be judged: the root
# Cargo.toml or Cargo.lock changed, or a path under one of its members did (ROOT 10-17: one
# workspace, one lock, one target dir). Members are read from CAND's root Cargo.toml.
rust_changed() {
  git -C "$repo" diff --name-only "$1" "$2" | python3 -c '
import sys, subprocess, tomllib
cand = sys.argv[1]
# No root Cargo.toml: no workspace. One that does not parse or names no members is judged whole
# (cargo reds it), never skipped (GATES-15: an unreadable input is not "nothing changed").
r = subprocess.run(["git", "-C", sys.argv[2], "cat-file", "-e", cand + ":Cargo.toml"], capture_output=True)
members = []
if r.returncode == 0:
    try:
        text = subprocess.run(["git", "-C", sys.argv[2], "show", cand + ":Cargo.toml"], capture_output=True, check=True).stdout
        members = tomllib.loads(text.decode())["workspace"]["members"]
        assert isinstance(members, list) and all(isinstance(m, str) for m in members)
    except Exception:
        print("workspace"); sys.exit(0)
paths = sys.stdin.read().split()
if any(p in ("Cargo.toml", "Cargo.lock") or any(p.startswith(m.rstrip("/") + "/") for m in members) for p in paths):
    print("workspace")' "$2" "$repo"
}

# generated_checks DIR: one "exe path" line per gates/generated.tsv row.
generated_checks() {
  [ -f "$1/gates/generated.tsv" ] && grep -v -e '^#' -e '^[[:space:]]*$' "$1/gates/generated.tsv" | tr '\t' ' '
}

# generated_check DIR EXE PATH: the generator's own `--check PATH` (exit 0 = the file is exactly
# what it emits). EXE is a lean_exe (`lake exe EXE`), or `cargo:BIN`, a bin of the root Cargo
# workspace (`cargo run --locked --bin BIN`: OPS-2's emit-anchors, whose output widens TLS trust if
# hand-edited, so it is checked on every commit like the Lean generators). One function for
# pre-push and standing, under the build wrapper (a shell function cannot be handed to swarm-build).
generated_check() {
  local dir=$1 exe=$2 out=$3
  case $exe in
    cargo:*) wrapped env -C "$dir" cargo run --quiet --locked --manifest-path "$dir/Cargo.toml" --bin "${exe#cargo:}" -- --check "$out" ;;
    *) wrapped env -C "$dir" lake exe "$exe" --check "$out" ;;
  esac
}
