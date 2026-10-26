#!/usr/bin/env bash
# testground/build/build.sh — the kernel in the browser: Lean's C for Web.Sim.Testground's import
# closure, compiled with emscripten into testground/kernel.{mjs,wasm} (measured 10-26: 3.5 MB, 0.66 MB
# gzipped). Two halves, because the Lean half wants the build box and the wasm half wants emcc:
#
#   build.sh c    WORK   (a machine with the pinned toolchain and the tree; hbox) → WORK/pack.tgz
#   build.sh wasm WORK   (a machine with emscripten ≥ 6) WORK/pack.tgz → testground/kernel.*
#   build.sh all  WORK   both on one machine
#
# Then serve testground/ (any static server; GitHub Pages) — `build.sh wasm` also copies the shipped
# package texts the demos install (world/doc, world/resident, world/escrow) beside the page.
#
# The Lean half: `lake build Web.Sim.Testground:c` (the tree's own C), then the toolchain's Init/Std C
# for the closure, re-emitted from the toolchain's sources with the flag the core build uses
# (-Dbackward.do.legacy=false). One module differs from the toolchain's own build:
# Init.Data.String.PosRaw, whose official IR names an auxiliary `instDecidableLtRaw._aux_1` that
# importers inline and a standalone `lean -c` does not emit; stage0's PosRaw.c at the same tag is ours
# plus exactly that definition, so it is used (measured: every other symbol we define is the
# toolchain's, `nm` over libInit.a/libStd.a; a recorded trace of 368 kernel calls replayed byte for
# byte on a native build of the same C, redregg/work/codex/TESTGROUND.report.md). The wasm half: the v4.30.0 runtime (single-threaded: GitHub Pages cannot send the
# COOP/COEP headers a threaded module needs; no GMP; no mimalloc; four bit-rotted no-libuv stubs
# patched, patch-rt.sh), every closure C file, Web/c/glue.c (the byte ABI), one ES module.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
mode=${1:?usage: build.sh c|wasm|all WORK}; work=$(mkdir -p "${2:?WORK}" && cd "$2" && pwd)
tc=$(cat "$root/lean-toolchain"); tag=${tc##*:}; T=$HOME/.elan/toolchains/${tc//\//--}; T=${T//:/---}
lean4=$work/lean4

lean4_src() {   # the toolchain's runtime, include and stage0 PosRaw, at the pinned tag
  [ -d "$lean4/src/runtime" ] && return
  git clone -q --depth 1 --branch "$tag" --filter=blob:none --sparse https://github.com/leanprover/lean4 "$lean4"
  git -C "$lean4" sparse-checkout set --no-cone '/src/runtime/*' '/src/include/*' '/src/util/*' '/stage0/stdlib/Init/Data/String/PosRaw.c'
}

half_c() {
  ( cd "$root" && lake build Web.Sim.Testground:c )
  python3 "$here/closure.py" "$root" "$T/src/lean" Web.Sim.Testground > "$work/closure.txt"
  rm -rf "$work/pack" && mkdir -p "$work/pack/tree" "$work/pack/std" "$work/stdc"
  for m in $(grep '^T ' "$work/closure.txt" | cut -c3-); do
    cp -p "$root/.lake/build/ir/${m//.//}.c" "$work/pack/tree/${m//./_}.c"
  done
  printf '#!/bin/sh\no=%s/stdc/$(echo $1 | tr . _).c; [ -s $o ] && exit 0\n%s/bin/lean -Dbackward.do.legacy=false -R %s/src/lean -c $o %s/src/lean/$(echo $1 | tr . /).lean >/dev/null || echo "FAIL $1" >&2\n' \
    "$work" "$T" "$T" "$T" > "$work/stdc1.sh"; chmod +x "$work/stdc1.sh"
  grep '^L ' "$work/closure.txt" | cut -c3- | xargs -P "${JOBS:-3}" -n 1 "$work/stdc1.sh"
  for m in $(grep '^L ' "$work/closure.txt" | cut -c3-); do cp -p "$work/stdc/${m//./_}.c" "$work/pack/std/"; done
  lean4_src
  cp "$lean4/stage0/stdlib/Init/Data/String/PosRaw.c" "$work/pack/std/Init_Data_String_PosRaw.c"
  cp "$root"/Host/c/*.c "$work/pack/"
  tar czf "$work/pack.tgz" -C "$work" pack
  echo "pack: $(grep -c '^T ' "$work/closure.txt") tree modules, $(grep -c '^L ' "$work/closure.txt") toolchain modules → $work/pack.tgz"
}

half_wasm() {
  lean4_src
  rm -rf "$work/pack" && tar xzf "$work/pack.tgz" -C "$work"   # the pack is the truth: never a stale one
  "$here/patch-rt.sh" "$lean4/src/runtime"
  mkdir -p "$work/gen/lean" "$work/rt/uv" "$work/obj"
  printf '#pragma once\n#include <lean/version.h>\n#define LEAN_SMALL_ALLOCATOR\n#define LEAN_IS_STAGE0 0\n' > "$work/gen/lean/config.h"
  sed 's/^#define LEAN_PLATFORM_TARGET .*/#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"/' "$T/include/lean/version.h" > "$work/gen/lean/version.h"
  echo "#define LEAN_GITHASH \"$(git -C "$lean4" rev-parse HEAD)\"" > "$work/gen/githash.h"
  local inc="-I$work/gen -I$lean4/src/include -I$lean4/src"
  for o in debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal; do
    [ -f "$work/rt/$o.o" ] || em++ -std=c++20 -O2 -fwasm-exceptions -DLEAN_EMSCRIPTEN -DLEAN_EXPORTING -DNDEBUG $inc -c "$lean4/src/runtime/$o.cpp" -o "$work/rt/$o.o"
  done
  rm -f "$work/rt/libleanrt.a"; emar rcs "$work/rt/libleanrt.a" "$work"/rt/*.o "$work"/rt/uv/*.o
  # an object is rebuilt when its C is newer (a flag day re-emits the tree's C; a kept .o would ship the old kernel)
  printf '#!/bin/sh\no=%s/obj/$(basename $1 .c).o; [ $o -nt $1 ] || emcc -Os -fwasm-exceptions -DLEAN_EMSCRIPTEN -DNDEBUG %s -w -c $1 -o $o\n' \
    "$work" "$inc" > "$work/cc1.sh"; chmod +x "$work/cc1.sh"
  ls "$work"/pack/tree/*.c "$work"/pack/std/*.c "$work"/pack/file.c "$root/Web/c/glue.c" | xargs -P "${JOBS:-6}" -n 1 "$work/cc1.sh"
  em++ -Os -fwasm-exceptions "$work"/obj/*.o "$work/rt/libleanrt.a" -o "$root/testground/kernel.mjs" \
    --no-entry -sMODULARIZE=1 -sEXPORT_ES6=1 -sENVIRONMENT=web,node \
    -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=67108864 -sSTACK_SIZE=8388608 \
    -sERROR_ON_UNDEFINED_SYMBOLS=1 \
    -sEXPORTED_FUNCTIONS=_w_init,_w_out,_w_genesis,_w_host,_w_follow,_w_pub,_w_sign,_w_attempt,_w_table,_w_lie,_w_lied,_w_lies,_w_cold,_w_forge,_w_text,_malloc,_free \
    -sEXPORTED_RUNTIME_METHODS=HEAPU8
  for d in doc resident escrow head; do mkdir -p "$root/testground/world/$d" && cp "$root/world/$d"/* "$root/testground/world/$d/"; done
  ls -la "$root/testground/kernel.wasm"; echo "gzip: $(gzip -9 -c "$root/testground/kernel.wasm" | wc -c) bytes"
}

case $mode in
  c) half_c ;;
  wasm) half_wasm ;;
  all) half_c; half_wasm ;;
  *) echo "usage: build.sh c|wasm|all WORK" >&2; exit 2 ;;
esac
