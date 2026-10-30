// test/index.sh: an LD_PRELOAD shim that fails one chosen libc call (or two),
// to test the index writer's order at the open and at the close.
//   FI_OP: open, fstat, lstat, renameat2, rename, link, ftruncate, unlink, close
//   FI_PATH: the call fails only when its path (for open, lstat, unlink:
//     the path; renameat2, rename: the source path; fstat, ftruncate, close:
//     the file the descriptor names, from /proc/self/fd) ends with FI_PATH
//   FI_NTH: the n-th matching call fails (default 1), with FI_ERRNO
//     (default EACCES; a number). Every other call goes through.
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

// A second failure, FI_OP2 / FI_PATH2 (its first matching call; FI_ERRNO2,
// default EACCES). FI_ALL=1: every matching call of FI_OP fails, not only
// the FI_NTH-th (a file system that never supports it).
static int hits, hits2;
static int ends(const char* p, const char* s) {
  size_t a = strlen(p), b = strlen(s);
  return a >= b && strcmp(p + a - b, s) == 0;
}
static int fire(const char* op, const char* path) {
  const char* o2 = getenv("FI_OP2"); const char* s2 = getenv("FI_PATH2");
  if (o2 != NULL && s2 != NULL && strcmp(o2, op) == 0 && path != NULL && ends(path, s2) && ++hits2 == 1) { const char* e2 = getenv("FI_ERRNO2"); errno = e2 ? atoi(e2) : EACCES; return 1; }
  const char* o = getenv("FI_OP"); const char* s = getenv("FI_PATH");
  if (o == NULL || s == NULL || strcmp(o, op) != 0 || path == NULL || !ends(path, s)) return 0;
  hits += 1;
  const char* n = getenv("FI_NTH");
  if (!getenv("FI_ALL") && hits != (n ? atoi(n) : 1)) return 0;
  const char* e = getenv("FI_ERRNO");
  errno = e ? atoi(e) : EACCES;
  return 1;
}
static int fire_fd(const char* op, int fd) {
  const char* o = getenv("FI_OP"); const char* o2 = getenv("FI_OP2");
  if ((o == NULL || strcmp(o, op) != 0) && (o2 == NULL || strcmp(o2, op) != 0)) return 0;
  char l[64], p[4096];
  snprintf(l, sizeof l, "/proc/self/fd/%d", fd);
  ssize_t k = readlink(l, p, sizeof p - 1);
  if (k <= 0) return 0;
  p[k] = 0;
  return fire(op, p);
}
#define NEXT(f) static __typeof__(f)* next_##f; if (!next_##f) next_##f = (__typeof__(f)*)dlsym(RTLD_NEXT, #f)

int open(const char* p, int fl, ...) {
  NEXT(open);
  mode_t m = 0;
  if (fl & (O_CREAT | O_TMPFILE)) { va_list a; va_start(a, fl); m = va_arg(a, mode_t); va_end(a); }
  if (fire("open", p)) return -1;
  return next_open(p, fl, m);
}
int fstat(int fd, struct stat* st) { NEXT(fstat); if (fire_fd("fstat", fd)) return -1; return next_fstat(fd, st); }
int lstat(const char* p, struct stat* st) { NEXT(lstat); if (fire("lstat", p)) return -1; return next_lstat(p, st); }
int renameat2(int a, const char* f, int b, const char* t, unsigned int fl) { NEXT(renameat2); if (fire("renameat2", f)) return -1; return next_renameat2(a, f, b, t, fl); }
int rename(const char* f, const char* t) { NEXT(rename); if (fire("rename", f)) return -1; return next_rename(f, t); }
int ftruncate(int fd, off_t n) { NEXT(ftruncate); if (fire_fd("ftruncate", fd)) return -1; return next_ftruncate(fd, n); }
int link(const char* f, const char* t) { NEXT(link); if (fire("link", f)) return -1; return next_link(f, t); }
int unlink(const char* p) { NEXT(unlink); if (fire("unlink", p)) return -1; return next_unlink(p); }
int close(int fd) {
  NEXT(close);
  if (fire_fd("close", fd)) { next_close(fd); return -1; }
  return next_close(fd);
}
