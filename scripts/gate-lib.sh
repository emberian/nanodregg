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

# rust_changed BASE CAND: the Cargo manifests whose crate changed.
rust_changed() {
  git -C "$repo" diff --name-only "$1" "$2" | awk -F/ 'NF>1 {print $1}' | sort -u | while read -r d; do
    [ -f "$repo/$d/Cargo.toml" ] && echo "$d"
  done
}

# generated_checks DIR: one "exe path" line per gates/generated.tsv row.
generated_checks() {
  [ -f "$1/gates/generated.tsv" ] && grep -v -e '^#' -e '^[[:space:]]*$' "$1/gates/generated.tsv" | tr '\t' ' '
}
