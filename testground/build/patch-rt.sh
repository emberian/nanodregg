#!/usr/bin/env bash
# patch-rt.sh RUNTIME_DIR — the LEAN_EMSCRIPTEN, single-threaded branch of the v4.30.0 runtime has
# bit-rotted (upstream builds it only with -pthread): the single-thread unique_lock stub lacks the
# adopt_lock constructor and release(), and three no-libuv stubs disagree with their headers.
# And one 32-bit defect: `string_to_list_core` ends `String.toList`'s list with `lean_box_uint32(0)`,
# which on a 32-bit target (wasm32) is a heap object, not the scalar `[]`; Lean code reads its tag 0
# as `[]`, but `lean_string_mk` walks to the first scalar and runs off the end (std::bad_alloc: the
# kernel threw on any atom that ends a text, `nd install x`). The nil is `lean_box(0)` on every target.
# Idempotent: it restores the five files from git first.
set -euo pipefail
cd "${1:?RUNTIME_DIR}"
git checkout -q -- thread.h uv/event_loop.cpp uv/dns.h uv/system.h object.cpp
perl -0pi -e 's|    unique_lock\(T const &\) \{\}|    unique_lock(T const &) {}\n    unique_lock(T const &, std::adopt_lock_t) {}\n    void release() {}|' thread.h
perl -0pi -e 's/extern "C" LEAN_EXPORT lean_obj_res lean_uv_event_loop_alive\(\) \{\n    return io_result_mk_error\("lean_uv_event_loop_alive is not supported"\);/extern "C" LEAN_EXPORT uint8_t lean_uv_event_loop_alive() {\n    return 0;/' uv/event_loop.cpp
perl -pi -e 's|lean_uv_dns_get_info\(b_obj_arg name, b_obj_arg service, uint8_t family\);|lean_uv_dns_get_info(b_obj_arg name, b_obj_arg service, uint8_t family, int8_t protocol);|' uv/dns.h
perl -pi -e 's|lean_uv_os_get_group\(uint64_t gid\);|lean_uv_os_get_group();|' uv/system.h
perl -pi -e 's|obj_res  r = lean_box_uint32\(0\);|obj_res  r = lean_box(0);|' object.cpp
[ "$(git diff --stat | tail -1 | grep -o '[0-9]* files')" = "5 files" ] || { echo "patch-rt: expected 5 files changed" >&2; exit 1; }
