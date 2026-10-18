/*
 * Host/c/sock.c — THE client end of a Unix stream socket (HOST-52): Lean 4.30 has no AF_UNIX.
 * Moves bytes, decides nothing (law 2). Every failure is an IO error naming it: `timeout`, `pathNul`,
 * `pathEmpty`, `pathTooLong` (checked against sun_path before any copy), `timeoutZero`,
 * `readMaxZero`, `readMaxPastBound`, else the call and errno. Every call is bounded by the
 * connection's timeout (a monotonic deadline); EINTR is retried on what is left of it, never
 * reported. MSG_NOSIGNAL (SO_NOSIGPIPE on Darwin) on every send, though Lean's runtime already
 * ignores SIGPIPE (measured, HOST-52): the flag keeps this file off a runtime internal. A read is
 * 1..max bytes, or empty exactly at end of stream. The socket is non-blocking, so connect is bounded
 * too: Linux never answers EINPROGRESS for AF_UNIX, and a full backlog is EAGAIN at once.
 * clock_gettime's result is unchecked: CLOCK_MONOTONIC fails only with EINVAL for an unsupported
 * clock id, and POSIX requires it on both platforms.
 */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

lean_obj_res nd_io_errno(const char *call, int err); /* Host/c/file.c */

#ifdef MSG_NOSIGNAL
#define ND_SEND_FLAGS MSG_NOSIGNAL
#else
#define ND_SEND_FLAGS 0
#endif
#define ND_READ_MAX (16u << 20)

typedef struct { int fd; uint32_t ms; } nd_conn;

static void nd_conn_finalize(void *p) { close(((nd_conn *)p)->fd); free(p); }
static void nd_conn_foreach(void *p, b_lean_obj_arg fn) { (void)p; (void)fn; }
static lean_external_class *nd_conn_class = NULL;
static nd_conn *conn_of(b_lean_obj_arg c) { return (nd_conn *)lean_get_external_data(c); }

static lean_obj_res named(const char *name) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(name)));
}

static int64_t now_ms(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}

/* 1: ready for `ev` (or hung up; the next call reports it), 0: past `end`, -1: poll failed. */
static int ready(int fd, short ev, int64_t end) {
  for (;;) {
    int64_t left = end - now_ms();
    if (left <= 0) return 0;
    struct pollfd p = { fd, ev, 0 };
    int r = poll(&p, 1, left > INT_MAX ? INT_MAX : (int)left);
    if (r > 0) return 1;
    if (r < 0 && errno != EINTR) return -1;
  }
}

static lean_obj_res fail_close(int fd, const char *call, int err) {
  close(fd);
  return err == 0 ? named(call) : nd_io_errno(call, err);
}

LEAN_EXPORT lean_obj_res nd_unix_connect(b_lean_obj_arg path, uint32_t ms, lean_obj_arg w) {
  (void)w;
  struct sockaddr_un a;
  const char *s = lean_string_cstr(path);
  size_t n = lean_string_size(path) - 1;
  if (strlen(s) != n) return named("pathNul");
  if (n == 0) return named("pathEmpty");
  if (n >= sizeof a.sun_path) return named("pathTooLong");
  if (ms == 0) return named("timeoutZero");
  memset(&a, 0, sizeof a); a.sun_family = AF_UNIX; memcpy(a.sun_path, s, n);
#ifdef SOCK_CLOEXEC
  int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0);
  if (fd < 0) return nd_io_errno("socket", errno);
#else
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return nd_io_errno("socket", errno);
  if (fcntl(fd, F_SETFD, FD_CLOEXEC) != 0 || fcntl(fd, F_SETFL, O_NONBLOCK) != 0)
    return fail_close(fd, "fcntl", errno);
#endif
#ifdef SO_NOSIGPIPE
  int one = 1;
  if (setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one) != 0)
    return fail_close(fd, "setsockopt(SO_NOSIGPIPE)", errno);
#endif
  if (connect(fd, (struct sockaddr *)&a, sizeof a) != 0) {
    if (errno != EINPROGRESS && errno != EINTR) return fail_close(fd, "connect", errno);
    int r = ready(fd, POLLOUT, now_ms() + ms);
    if (r == 0) return fail_close(fd, "timeout", 0);
    int e = 0; socklen_t l = sizeof e;
    if (r < 0) e = errno;
    else if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &e, &l) != 0) e = errno;
    if (e != 0) return fail_close(fd, "connect", e);
  }
  nd_conn *c = (nd_conn *)malloc(sizeof(nd_conn));
  if (c == NULL) return fail_close(fd, "malloc", ENOMEM);
  c->fd = fd; c->ms = ms;
  if (nd_conn_class == NULL)
    nd_conn_class = lean_register_external_class(nd_conn_finalize, nd_conn_foreach);
  return lean_io_result_mk_ok(lean_alloc_external(nd_conn_class, c));
}

/* Every byte before the deadline, or an IO error; a short send is continued, never success. */
LEAN_EXPORT lean_obj_res nd_conn_write_all(b_lean_obj_arg c, b_lean_obj_arg bytes, lean_obj_arg w) {
  (void)w;
  nd_conn *k = conn_of(c);
  const uint8_t *p = lean_sarray_cptr(bytes);
  size_t left = lean_sarray_size(bytes);
  int64_t end = now_ms() + k->ms;
  while (left > 0) {
    int r = ready(k->fd, POLLOUT, end);
    if (r == 0) return named("timeout");
    if (r < 0) return nd_io_errno("poll", errno);
    ssize_t n = send(k->fd, p, left, ND_SEND_FLAGS);
    if (n < 0) {
      if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) continue;
      return nd_io_errno("send", errno);
    }
    p += n; left -= (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* 1..max bytes before the deadline, or none at end of stream. */
LEAN_EXPORT lean_obj_res nd_conn_read(b_lean_obj_arg c, size_t max, lean_obj_arg w) {
  (void)w;
  if (max == 0) return named("readMaxZero");
  if (max > ND_READ_MAX) return named("readMaxPastBound");
  nd_conn *k = conn_of(c);
  int64_t end = now_ms() + k->ms;
  lean_object *arr = lean_alloc_sarray(1, 0, max);
  for (;;) {
    int r = ready(k->fd, POLLIN, end);
    if (r <= 0) {
      int e = errno;
      lean_dec(arr);
      return r == 0 ? named("timeout") : nd_io_errno("poll", e);
    }
    ssize_t n = recv(k->fd, lean_sarray_cptr(arr), max, 0);
    if (n < 0) {
      if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) continue;
      int e = errno;
      lean_dec(arr);
      return nd_io_errno("recv", e);
    }
    lean_sarray_set_size(arr, (size_t)n);
    return lean_io_result_mk_ok(arr);
  }
}
