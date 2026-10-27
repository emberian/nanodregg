#!/usr/bin/env bash
# testground/build/gate.sh FRESH [--harness-control] — the testground's lies as a verdict (gates/runs.tsv
# `script:testground/build/gate.sh`): the kernel the page loads, built from THIS tree (build.sh all), runs
# every Writer-menu scene (lies-run.mjs) and its control with the lies off (--honest), then each axis's
# demo (axes-run.mjs: the generator, the creator, the meter to ticksBudget, the time-lock, the document), the tutorial's
# steps in order (teach-run.mjs: each command ends as its step says), then a real
# hosted World on a fresh genesis (hosted-run.mjs basic, document and door: the live World's door, CLIENT-49). The expectation
# of each scene is its row's, read off Protocol.rows by the kernel, so a row that changes its lines is
# RED here until its scene follows, never silently left behind.
#
# The work directory (the toolchain's Init/Std C, the runtime, objects named by their C's content) is
# shared by every tree on the box, one build at a time (flock): ND_TESTGROUND_WORK, default
# ~/.cache/nd-testground/TOOLCHAIN. emcc is the one tool the judge needs beyond the tree's: on PATH, or
# ~/tools/emsdk (restore: `git clone https://github.com/emscripten-core/emsdk ~/tools/emsdk && cd
# ~/tools/emsdk && ./emsdk install 6.0.9 && ./emsdk activate 6.0.9`). Without it this row is RED.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
fresh=${1:?usage: gate.sh FRESH [--harness-control]}; shift
tc=$(cat "$root/lean-toolchain"); tag=${tc##*:}
if ! command -v emcc >/dev/null && [ -f "$HOME/tools/emsdk/emsdk_env.sh" ]; then
  source "$HOME/tools/emsdk/emsdk_env.sh" >/dev/null 2>&1
fi
command -v emcc >/dev/null || { echo "FAIL no emcc on PATH or in ~/tools/emsdk (the restore command: testground/build/gate.sh's header)"; exit 1; }
command -v node >/dev/null || { echo "FAIL no node"; exit 1; }
work=${ND_TESTGROUND_WORK:-$HOME/.cache/nd-testground/$tag}; mkdir -p "$work"
t0=$(date +%s)
if ! ( flock 9; "$here/build.sh" all "$work" ) 9>"$work/.lock" > "$fresh/build.log" 2>&1; then
  tail -20 "$fresh/build.log"; echo "FAIL the kernel did not build (build.sh all; log above)"; exit 1
fi
echo "kernel: $(wc -c < "$root/testground/kernel.wasm") bytes, built in $(( $(date +%s) - t0 )) s"
cd "$root/testground"
# the hosted World (CLIENT-43): `host serve` under nd-supervise, the guest-book and the relay on a fresh
# genesis (deploy/testground/run.sh, every process by its PID file), two members in two kernels joined
# over the guest-book's invitation; hosted-run.mjs's `basic` and `document` must answer as scripted.
# STATE lives under TMPDIR (runs.py's own per run): host.sock must fit sun_path.
node_ws=(node); node -e 'process.exit(typeof WebSocket === "undefined" ? 1 : 0)' || node_ws=(node --experimental-websocket)
hosted() {   # hosted SCENE... [--harness-control]
  local st port rc=0
  ( cd "$root" && cargo build -q --release -p nanodregg-client --bin nd-supervise ) || { echo "FAIL nd-supervise did not build"; return 1; }
  st=$(mktemp -d "${TMPDIR:-/tmp}/ndtg.XXXXXX")
  port=$(python3 -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
  export ND_TESTGROUND_ENROLL_FLOOR=250   # hosted-run.mjs door: a join past the scenes' six meets the floor
  export ND_HOST=${ND_LEAN_BIN:-$root/.lake/build/bin}/host ND_SUPERVISE=${CARGO_TARGET_DIR:-$root/target}/release/nd-supervise
  if "$root/deploy/testground/run.sh" genesis "$st/w" > "$st/genesis.log" 2>&1 && PORT=$port "$root/deploy/testground/run.sh" start "$st/w" > "$st/start.log" 2>&1; then
    for _ in $(seq 100); do curl -sf "http://127.0.0.1:$port/world.json" > /dev/null && break; sleep 0.2; done
    for sc in "$@"; do
      case $sc in --*) continue ;; esac
      "${node_ws[@]}" hosted-run.mjs "ws://127.0.0.1:$port/ws" "$sc" $([ "${!#}" = --harness-control ] && echo --harness-control) 2>&1 | grep -v -e ExperimentalWarning -e 'UNDICI-WS' -e trace-warnings | tail -3
      [ "${PIPESTATUS[0]}" -eq 0 ] || rc=1
    done
  else
    tail -5 "$st/genesis.log" "$st/start.log"; echo "FAIL the hosted World did not start (run.sh)"; rc=1
  fi
  "$root/deploy/testground/run.sh" stop "$st/w" > /dev/null 2>&1 || true
  rm -rf "$st"
  return $rc
}
if [ "${1-}" = --harness-control ]; then
  # each reader's own known-red control must read red; the row's control reads red only if both did
  if node lies-run.mjs --harness-control; then echo "FAIL harness: lies-run.mjs --harness-control passed"; exit 0; fi
  if node axes-run.mjs --harness-control; then echo "FAIL harness: axes-run.mjs --harness-control passed"; exit 0; fi
  if node teach-run.mjs --harness-control; then echo "FAIL harness: teach-run.mjs --harness-control passed"; exit 0; fi
  if hosted basic --harness-control; then echo "FAIL harness: hosted-run.mjs --harness-control passed"; exit 0; fi
  echo "FAIL harness-control: every reader read its known-red step red"; exit 1
fi
node lies-run.mjs || { echo "FAIL a lie's scene did not end as its row expects (lies-run.mjs)"; exit 1; }
node lies-run.mjs --honest || { echo "FAIL the control: with the lies off a scene still ended as its row expects (lies-run.mjs --honest)"; exit 1; }
node axes-run.mjs || { echo "FAIL an axis demo did not answer as scripted (axes-run.mjs)"; exit 1; }
node teach-run.mjs || { echo "FAIL a tutorial step did not end as it says (teach-run.mjs)"; exit 1; }
hosted basic document door || { echo "FAIL the hosted World did not answer as scripted (hosted-run.mjs)"; exit 1; }
echo "TESTGROUND GATE GREEN"
