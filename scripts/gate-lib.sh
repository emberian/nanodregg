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
# at once; when all are busy, this process tries every slot again each 5 s, for at most 30 min, and
# takes whichever frees first. (It waited on one fixed slot, pid mod N, until GATES-8: a judge sat
# ~10 min behind a busy slot while two others stood free, 10-18.) Returns 3 when no slot freed in 30
# min: the caller says NOT JUDGED (exit 76), never RED (GATES-22; the landing of GATES-20b-prime read
# "REFUSED by scripts/pre-push" on a slot wait).
gate_slot() {
  flock_or_refuse || return 1
  local n k
  n=$(git -C "$repo" config nanodregg.gateslots || true)
  if [ -z "$n" ]; then
    if [ "$(git -C "$repo" config --bool nanodregg.landing || true)" = true ]; then n=4; else n=1; fi
  fi
  # GATES-22 (ROOT, lanes' measurements): a waiting judge KEEPS its place: every 30 min it names the holders and
  # waits on; only after ND_SLOT_WAIT seconds (default 4 h) is it NOT JUDGED (return 3), never refused.
  local start; start=$(date +%s)
  local end=$(( start + ${ND_SLOT_WAIT:-14400} )) next=$(( start + 1800 )) said=
  while :; do
    for k in $(seq 1 "$n"); do
      exec 9> "$common/nanodregg-gate-$k.flock"
      if flock -n 9; then
        G=$common/nanodregg-gate-$k
        [ -z "$said" ] || echo "gate: slot $k freed; judging in it" >&2
        return 0
      fi
    done
    exec 9>&-
    if [ "$(date +%s)" -ge "$next" ] || [ "$(date +%s)" -ge "$end" ]; then
      echo "gate: every judge slot busy for $(( ($(date +%s) - start) / 60 )) min; holders:" >&2
      for k in $(seq 1 "$n"); do
        local h; h=$(fuser "$common/nanodregg-gate-$k.flock" 2>/dev/null | tr -s ' ' '\n' | grep -E '^[0-9]+$' | head -1)
        echo "  slot $k: ${h:-?} $( [ -n "$h" ] && tr '\0' ' ' < /proc/$h/cmdline 2>/dev/null | cut -c1-200) ($(ls -t "$common/nanodregg-gate-$k"/*.log 2>/dev/null | head -1 | xargs -r basename))" >&2
      done
      [ "$(date +%s)" -ge "$end" ] && { echo "gate: no slot in $(( ${ND_SLOT_WAIT:-14400} / 60 )) min; not judged" >&2; return 3; }
      next=$(( next + 1800 ))
    fi
    [ -n "$said" ] || { echo "gate: all $n judge slots busy; waiting, in place, for the first to free" >&2; said=1; }
    sleep 5
  done
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

# new_ticket [QUEUE]: take a landing-queue ticket (gates/land.py; GATES-19): QUEUE/<seq>.<pid>, seq
# from a counter kept under QUEUE/seq.flock, the ticket flock'd on fd 6 by this process until it
# exits, so a dead lander's ticket is released by the kernel. Sets ticket. Call it in the process
# that must hold it, never in `$(…)`.
new_ticket() {
  flock_or_refuse || return 1
  local q=${1:-$common/nanodregg-queue} s
  mkdir -p "$q" || return 1
  exec 7>> "$q/seq.flock"
  flock -w 60 7 || { echo "gate: the queue counter lock was held for 60 s" >&2; exec 7>&-; return 1; }
  s=$(( $(cat "$q/seq" 2>/dev/null || echo 0) + 1 ))
  echo "$s" > "$q/seq"
  ticket=$q/$(printf '%08d' "$s").$$
  exec 6>> "$ticket"
  flock -n 6 || { echo "gate: could not lock the new ticket $ticket" >&2; exec 7>&-; return 1; }
  exec 7>&-
}
