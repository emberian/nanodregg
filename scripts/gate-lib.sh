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

# lock NAME: one judge at a time per NAME. The lock is a directory holding the owner's PID; a
# lock whose PID is dead is taken over, a live one is waited for (deadline 30 min).
lock() {
  local d="$common/$1.lock" waited=0
  while ! mkdir "$d" 2>/dev/null; do
    local pid; pid=$(cat "$d/pid" 2>/dev/null || true)
    if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then
      echo "gate: taking over stale lock $d (pid $pid is gone)" >&2
      rm -rf "$d"; continue
    fi
    if [ "$waited" -ge 1800 ]; then echo "gate: lock $d held by pid $pid for 30 min; refusing" >&2; return 1; fi
    sleep 5; waited=$((waited + 5))
  done
  echo $$ > "$d/pid"
  trap 'rm -rf "'"$d"'"' EXIT
}

# lean_targets DIR: every lean_lib and lean_exe name in DIR's lakefile.lean.
lean_targets() { python3 "$1/gates/tree.py" targets "$1"; }

# lean_exes DIR: every lean_exe name (each links the extern_libs, so building them builds the C).
lean_exes() { python3 "$1/gates/tree.py" exes "$1"; }

# affected DIR BASE CAND: modules changed between two trees plus everything that imports them;
# prints ALL when the build itself changed (lakefile, toolchain) or DIR has never built. Every
# exe is appended whenever anything is built or a C source changed: exes link the C shim.
affected() {
  local dir=$1 base=$2 cand=$3 changed
  changed=$(git -C "$repo" diff --name-only "$base" "$cand")
  if [ ! -d "$dir/.lake/build" ] || printf '%s\n' "$changed" | grep -qxE 'lakefile.lean|lakefile.toml|lean-toolchain'; then
    echo ALL; return
  fi
  printf '%s\n' "$changed" | python3 -c '
import sys; sys.path.insert(0, sys.argv[1] + "/gates"); import tree
t = tree.read(sys.argv[1]); deps = t.dependents()
want = set()
for p in sys.stdin.read().split():
    if p.endswith(".lean"):
        m = p[:-5].replace("/", ".")
        if m in t.modules: want |= {m} | deps[m]
print(" ".join(sorted(want)))' "$dir" | { read -r mods; if [ -n "$mods" ] || printf '%s\n' "$changed" | grep -qE '\.(c|h)$'; then echo "$mods $(lean_exes "$dir")"; fi; }
}

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
