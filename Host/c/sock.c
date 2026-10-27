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
 *
 * A confined Linux child cannot make a socket (sandbox/src/linux.rs, CLIENT-48): when ND_CONNECTOR
 * names a descriptor, the connect is asked of the launcher over it instead. The wire is the sandbox
 * crate's (`linux::ask`): the path as one seqpacket message; the reply a u32le errno (0: connected)
 * with the connected, non-blocking socket as SCM_RIGHTS. One ask at a time (a mutex), so two threads
 * never read each other's reply. Errors read as before: `connect: … (errno 13)` for a path the
 * launcher's policy does not grant, the connect's own errno otherwise.
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
#ifdef __linux__
#include <pthread.h>
#include <stdint.h>
#endif

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

/* The connected socket `fd` as a Conn bounded by `ms`. */
static lean_obj_res conn_ok(int fd, uint32_t ms) {
  nd_conn *c = (nd_conn *)malloc(sizeof(nd_conn));
  if (c == NULL) return fail_close(fd, "malloc", ENOMEM);
  c->fd = fd; c->ms = ms;
  if (nd_conn_class == NULL)
    nd_conn_class = lean_register_external_class(nd_conn_finalize, nd_conn_foreach);
  return lean_io_result_mk_ok(lean_alloc_external(nd_conn_class, c));
}

#ifdef __linux__
static pthread_mutex_t nd_connector_lock = PTHREAD_MUTEX_INITIALIZER;

/* The connected socket at `path` from the launcher's connector `k`, or -1 with errno set. */
static int nd_connector_ask(int k, const char *path, size_t n) {
  pthread_mutex_lock(&nd_connector_lock);
  ssize_t sent;
  do sent = send(k, path, n, MSG_NOSIGNAL); while (sent < 0 && errno == EINTR);
  if (sent != (ssize_t)n) { int e = sent < 0 ? errno : EPROTO; pthread_mutex_unlock(&nd_connector_lock); errno = e; return -1; }
  uint8_t code[4];
  union { struct cmsghdr h; char b[CMSG_SPACE(sizeof(int))]; } ctl;
  struct iovec io = { code, sizeof code };
  struct msghdr m;
  memset(&m, 0, sizeof m);
  m.msg_iov = &io; m.msg_iovlen = 1; m.msg_control = ctl.b; m.msg_controllen = sizeof ctl.b;
  ssize_t got;
  do got = recvmsg(k, &m, MSG_CMSG_CLOEXEC); while (got < 0 && errno == EINTR);
  int e = got < 0 ? errno : 0;
  pthread_mutex_unlock(&nd_connector_lock);
  if (got < 0) { errno = e; return -1; }
  int fd = -1;
  for (struct cmsghdr *c = CMSG_FIRSTHDR(&m); c != NULL; c = CMSG_NXTHDR(&m, c))
    if (c->cmsg_level == SOL_SOCKET && c->cmsg_type == SCM_RIGHTS && c->cmsg_len == CMSG_LEN(sizeof(int)))
      memcpy(&fd, CMSG_DATA(c), sizeof fd);
  if (got != 4) { if (fd >= 0) close(fd); errno = EPROTO; return -1; }
  uint32_t err = (uint32_t)code[0] | (uint32_t)code[1] << 8 | (uint32_t)code[2] << 16 | (uint32_t)code[3] << 24;
  if (err != 0) { if (fd >= 0) close(fd); errno = (int)err; return -1; }
  if (fd < 0) { errno = EPROTO; return -1; }
  return fd;
}

/* The connector this process was handed (ND_CONNECTOR), or -1 when it has none. */
static int nd_connector(void) {
  const char *v = getenv("ND_CONNECTOR");
  if (v == NULL || *v == 0) return -1;
  char *end = NULL;
  long n = strtol(v, &end, 10);
  return (*end == 0 && n > 2 && n < INT_MAX) ? (int)n : -1;
}
#endif

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
#ifdef __linux__
  int k = nd_connector();
  if (k >= 0) {
    int fd = nd_connector_ask(k, s, n);
    if (fd < 0) return nd_io_errno("connect", errno);
    return conn_ok(fd, ms);
  }
#endif
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
  return conn_ok(fd, ms);
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
