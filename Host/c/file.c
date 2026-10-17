/*
 * Host/c/file.c — the Store's physical IO: one file descriptor per segment.
 *
 * Lean's IO.FS.Handle is a FILE* with no fsync, no positioned read and no truncate-to-length;
 * this file is the POSIX calls the Store needs and the one signal disposition its writes need,
 * and nothing else. It moves bytes and
 * decides nothing (law 2): every error is returned to Lean as an IO error naming the call and
 * errno; nothing is retried here (a failed fsync is never retried: HOST-4).
 *
 * Durability: on Darwin, fsync does not flush the drive's cache; F_FULLFSYNC does. If the
 * file system refuses F_FULLFSYNC the sync FAILS rather than falling back to a weaker fsync
 * (a refused check never becomes an accepting one). Elsewhere, fdatasync.
 */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct { int fd; } nd_file;

static void nd_file_finalize(void *p) {
  nd_file *f = (nd_file *)p;
  if (f->fd >= 0) close(f->fd);
  free(f);
}

static void nd_file_foreach(void *p, b_lean_obj_arg fn) { (void)p; (void)fn; }

static lean_external_class *nd_file_class = NULL;

static lean_external_class *file_class(void) {
  if (nd_file_class == NULL)
    nd_file_class = lean_register_external_class(nd_file_finalize, nd_file_foreach);
  return nd_file_class;
}

static lean_obj_res io_errno(const char *call, int err) {
  char buf[160];
  snprintf(buf, sizeof buf, "%s: %s (errno %d)", call, strerror(err), err);
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static int fd_of(b_lean_obj_arg f) { return ((nd_file *)lean_get_external_data(f))->fd; }

/* mode 0: read only. mode 1: append, create 0600. mode 2: write, create exclusively 0600. */
LEAN_EXPORT lean_obj_res nd_file_open(b_lean_obj_arg path, uint8_t mode, lean_obj_arg w) {
  (void)w;
  int flags;
  switch (mode) {
    case 0: flags = O_RDONLY; break;
    case 1: flags = O_WRONLY | O_APPEND | O_CREAT; break;
    case 2: flags = O_WRONLY | O_CREAT | O_EXCL; break;
    default: return io_errno("nd_file_open: mode", EINVAL);
  }
  int fd;
  do { fd = open(lean_string_cstr(path), flags | O_CLOEXEC, 0600); } while (fd < 0 && errno == EINTR);
  if (fd < 0) return io_errno("open", errno);
  nd_file *f = (nd_file *)malloc(sizeof(nd_file));
  if (f == NULL) { close(fd); return io_errno("malloc", ENOMEM); }
  f->fd = fd;
  return lean_io_result_mk_ok(lean_alloc_external(file_class(), f));
}

/* Write every byte or fail; a short write is continued, never reported as success. */
LEAN_EXPORT lean_obj_res nd_file_write_all(b_lean_obj_arg f, b_lean_obj_arg bytes, lean_obj_arg w) {
  (void)w;
  const uint8_t *p = lean_sarray_cptr(bytes);
  size_t left = lean_sarray_size(bytes);
  while (left > 0) {
    ssize_t n = write(fd_of(f), p, left);
    if (n < 0) { if (errno == EINTR) continue; return io_errno("write", errno); }
    if (n == 0) return io_errno("write", EIO);
    p += n; left -= (size_t)n;
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res nd_file_sync(b_lean_obj_arg f, lean_obj_arg w) {
  (void)w;
#ifdef __APPLE__
  if (fcntl(fd_of(f), F_FULLFSYNC) != 0) return io_errno("fcntl(F_FULLFSYNC)", errno);
#else
  if (fdatasync(fd_of(f)) != 0) return io_errno("fdatasync", errno);
#endif
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res nd_file_size(b_lean_obj_arg f, lean_obj_arg w) {
  (void)w;
  struct stat st;
  if (fstat(fd_of(f), &st) != 0) return io_errno("fstat", errno);
  return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}

/* Exactly `len` bytes at `off`, or fewer only at end of file. */
LEAN_EXPORT lean_obj_res nd_file_read_at(b_lean_obj_arg f, uint64_t off, size_t len, lean_obj_arg w) {
  (void)w;
  lean_object *arr = lean_alloc_sarray(1, 0, len);
  uint8_t *p = lean_sarray_cptr(arr);
  size_t got = 0;
  while (got < len) {
    ssize_t n = pread(fd_of(f), p + got, len - got, (off_t)(off + got));
    if (n < 0) { if (errno == EINTR) continue; lean_dec(arr); return io_errno("pread", errno); }
    if (n == 0) break;
    got += (size_t)n;
  }
  lean_sarray_set_size(arr, got);
  return lean_io_result_mk_ok(arr);
}

/* Truncate to `len` and make the new length durable. */
LEAN_EXPORT lean_obj_res nd_file_truncate(b_lean_obj_arg f, uint64_t len, lean_obj_arg w) {
  if (ftruncate(fd_of(f), (off_t)len) != 0) return io_errno("ftruncate", errno);
  return nd_file_sync(f, w);
}

/* An exclusive lock for the writer's lifetime; false if another process holds it. */
LEAN_EXPORT lean_obj_res nd_file_try_lock(b_lean_obj_arg f, lean_obj_arg w) {
  (void)w;
  int r;
  do { r = flock(fd_of(f), LOCK_EX | LOCK_NB); } while (r != 0 && errno == EINTR);
  if (r == 0) return lean_io_result_mk_ok(lean_box(1));
  if (errno == EWOULDBLOCK) return lean_io_result_mk_ok(lean_box(0));
  return io_errno("flock", errno);
}

/* HOST-27: ignored, a write past RLIMIT_FSIZE fails EFBIG (short writes continue in write_all
   until it does): an IO error the loop answers `uncertain`, never a death by signal. */
LEAN_EXPORT lean_obj_res nd_ignore_sigxfsz(lean_obj_arg w) {
  (void)w;
  if (signal(SIGXFSZ, SIG_IGN) == SIG_ERR) return io_errno("signal(SIGXFSZ)", errno);
  return lean_io_result_mk_ok(lean_box(0));
}

/* Make a directory entry (a create or a rename inside `path`) durable. */
LEAN_EXPORT lean_obj_res nd_dir_sync(b_lean_obj_arg path, lean_obj_arg w) {
  (void)w;
  int fd;
  do { fd = open(lean_string_cstr(path), O_RDONLY | O_DIRECTORY | O_CLOEXEC); } while (fd < 0 && errno == EINTR);
  if (fd < 0) return io_errno("open(dir)", errno);
#ifdef __APPLE__
  int r = fcntl(fd, F_FULLFSYNC);
#else
  int r = fsync(fd);
#endif
  int err = errno;
  close(fd);
  if (r != 0) return io_errno("sync(dir)", err);
  return lean_io_result_mk_ok(lean_box(0));
}
