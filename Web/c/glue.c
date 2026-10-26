/* Web/c/glue.c — the testground kernel's byte ABI: the page hands a buffer, the Lean export
   decides, the result is copied into one out buffer the page reads (w_out; its length is the return
   value, -1 for an IO error). Built natively by lake like Host/c (an archive member nothing native
   references, so no executable links it) and to wasm by testground/build/build.sh. */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#else
#define EMSCRIPTEN_KEEPALIVE
#endif
extern lean_object* tg_genesis(lean_object*);
extern lean_object* tg_host(uint8_t, lean_object*);
extern lean_object* tg_follow(uint32_t, uint8_t, lean_object*);
extern lean_object* tg_pub(lean_object*);
extern lean_object* tg_sign(lean_object*, lean_object*);
extern lean_object* tg_table(lean_object*);
extern uint8_t tg_attempt(uint8_t, uint8_t, uint8_t);
lean_object* initialize_nanodregg_Web_Sim_Testground(uint8_t builtin);
void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);

static uint8_t *out_buf = 0;
static size_t out_len = 0;

static lean_object* ba(const uint8_t* p, size_t n) {
  lean_object* a = lean_alloc_sarray(1, n, n);
  if (n) memcpy(lean_sarray_cptr(a), p, n);
  return a;
}
static int32_t take(lean_object* a) {
  free(out_buf);
  out_len = lean_sarray_size(a);
  out_buf = malloc(out_len ? out_len : 1);
  if (out_len) memcpy(out_buf, lean_sarray_cptr(a), out_len);
  lean_dec(a);
  return (int32_t)out_len;
}
static int32_t io_take(lean_object* r) {
  if (lean_io_result_is_error(r)) { lean_dec(r); return -1; }
  lean_object* v = lean_io_result_get_value(r);
  lean_inc(v); lean_dec(r);
  return take(v);
}
EMSCRIPTEN_KEEPALIVE uint8_t* w_out(void) { return out_buf; }
EMSCRIPTEN_KEEPALIVE int32_t w_init(void) {
  lean_initialize_runtime_module();
  lean_object* r = initialize_nanodregg_Web_Sim_Testground(1);
  if (lean_io_result_is_error(r)) return 1;
  lean_dec_ref(r);
  lean_io_mark_end_initialization();
  return 0;
}
EMSCRIPTEN_KEEPALIVE int32_t w_genesis(const uint8_t* p, size_t n) { return io_take(tg_genesis(ba(p, n))); }
EMSCRIPTEN_KEEPALIVE int32_t w_host(uint32_t op, const uint8_t* p, size_t n) { return io_take(tg_host((uint8_t)op, ba(p, n))); }
EMSCRIPTEN_KEEPALIVE int32_t w_follow(uint32_t i, uint32_t op, const uint8_t* p, size_t n) { return io_take(tg_follow(i, (uint8_t)op, ba(p, n))); }
EMSCRIPTEN_KEEPALIVE int32_t w_pub(const uint8_t* p, size_t n) { return take(tg_pub(ba(p, n))); }
EMSCRIPTEN_KEEPALIVE int32_t w_sign(const uint8_t* s, size_t sn, const uint8_t* m, size_t mn) { return take(tg_sign(ba(s, sn), ba(m, mn))); }
EMSCRIPTEN_KEEPALIVE int32_t w_attempt(uint32_t left, uint32_t req, uint32_t seen) { return tg_attempt((uint8_t)left, (uint8_t)req, (uint8_t)seen); }
EMSCRIPTEN_KEEPALIVE int32_t w_table(void) {
  lean_object* s = tg_table(lean_box(0));
  free(out_buf);
  out_len = lean_string_size(s) - 1;
  out_buf = malloc(out_len + 1);
  memcpy(out_buf, lean_string_cstr(s), out_len);
  lean_dec(s);
  return (int32_t)out_len;
}
