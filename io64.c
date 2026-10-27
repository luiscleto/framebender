// framebender driver effects (trusted code, used only by main.bend).
//
// Io.pread_full: read n bytes at a 64-bit offset (hi * 2^32 + lo), retrying
// until n bytes are read or the file ends (Base's File.read_at takes a 32-bit
// offset and makes one pread, capped at INT32_MAX bytes).
// Io.write_fd: write all the bytes to an inherited descriptor (1: stdout,
// 2: stderr) without reopening it (Base has no byte-exact write to them).

#ifdef CID(Io.pread_full)
static void io_pread_full_call(IoWork* w) {
  int fd = (int)w->hand;
  if (w->data == NULL) {
    w->code = ENOMEM;
    w->size = 0;
    return;
  }
  uint64_t want = w->word;
  uint64_t got = 0;
  off_t off = (off_t)w->made;
  while (got < want) {
    ssize_t n = pread(fd, w->data + got, want - got > INT32_MAX ? INT32_MAX : want - got, off + (off_t)got);
    if (n < 0) {
      if (errno == EINTR) continue;
      io_sys_end(w, n);
      w->size = got;
      return;
    }
    if (n == 0) break;
    got += (uint64_t)n;
  }
  w->size = got;
}
static Term io_pread_full_pack(Env e, IoWork* w) {
  Term r = io_res(e, w, io_list(e, w->data, w->data == NULL ? 0 : w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}
Term io_pread_full_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  w->made = (intptr_t)(((uint64_t)(u32)f[1] << 32) | (uint64_t)(u32)f[2]);
  w->word = (u32)f[3];
  w->data = malloc((size_t)w->word + 1);
  return io_work(w, io_pread_full_call, io_pread_full_pack);
}
static void __attribute__((constructor)) io_pread_full_use(void) {
  io_eff(CID(Io.pread_full), io_pread_full_run);
}
#endif

#ifdef CID(Io.write_fd)
static void io_write_fd_call(IoWork* w) {
  int fd = (int)w->hand;
  ssize_t n = 0;
  for (uint64_t at = 0; at < w->size; at += (uint64_t)n) {
    n = write(fd, w->data + at, w->size - at);
    if (n < 0 && errno == EINTR) { n = 0; continue; }
    if (n <= 0) {
      if (n == 0) w->code = EIO; else io_sys_end(w, n);
      return;
    }
  }
}
static Term io_write_fd_pack(Env e, IoWork* w) {
  Term r = io_res(e, w, term_pak(CID(Unit), 0));
  free(w->data);
  return r;
}
// A value past 255 fails with EINVAL before any byte is written.
Term io_write_fd_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)(u32)f[0];
  w->data = io_cbuf(e, f[1], &w->size, CID(Con));
  w->code = w->data == NULL ? EINVAL : 0;
  return w->code ? io_write_fd_pack(e, w)
    : io_work(w, io_write_fd_call, io_write_fd_pack);
}
static void __attribute__((constructor)) io_write_fd_use(void) {
  io_eff(CID(Io.write_fd), io_write_fd_run);
}
#endif

// Io.read_str: read up to max bytes from the file's position, as a String
// with one Char per byte (Base's File.read decodes UTF-8; File.read_bytes
// gives a List that the driver had to convert).
// Io.write_str: write a String whose Chars are bytes (0-255) to an inherited
// descriptor, one byte per Char (Base's File.write encodes UTF-8).

#if defined(CID(Io.read_str)) || defined(CID(Io.write_str))
// A String of one Char per byte (io_str without the UTF-8 decoding).
static Term io64_bytes_str(Env e, const char* p, u64 n) {
  Term  s;
  Term* hole = &s;
  for (u64 i = 0; i < n; i += 1) {
    u64  l = heap_alloc(e, 1);
    Term t = term_ctr(CID(SCon), l);
    e.mem[l] = (uint8_t)p[i];
    *hole = hole == &s ? t : io_seal(e, t, CID(SCon));
    hole = &e.mem[l + 1];
  }
  *hole = term_pak(CID(SNil), 0);
  return s;
}

// The bytes of a String of Chars 0-255 (io_cbuf without the UTF-8
// encoding); NULL if a Char is past 255.
static char* io64_str_bytes(Env e, Term s, u64* len) {
  u64   cap = 64, n = 0, bad = 0;
  char* buf = io_mem(malloc(cap));
  while (term_aux(s) == CID(SCon)) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n + 2 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    bad |= fb[0] > 255;
    buf[n++] = (char)fb[0];
    s = fb[1];
  }
  buf[n] = 0;
  *len = n;
  if (bad) {
    free(buf);
    return NULL;
  }
  return buf;
}
#endif

#ifdef CID(Io.read_str)
static void io_read_str_call(IoWork* w) {
  int fd = (int)w->hand;
  ssize_t n;
  do {
    n = read(fd, w->data, w->word);
  } while (n < 0 && errno == EINTR);
  w->size = io_sys_end(w, n);
}
static Term io_read_str_pack(Env e, IoWork* w) {
  Term r = io_res(e, w, io64_bytes_str(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}
Term io_read_str_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  u64 max = (u32)f[1];
  w->word = max < INT32_MAX ? max : INT32_MAX;
  w->data = io_mem(malloc(w->word + 1));
  return io_work(w, io_read_str_call, io_read_str_pack);
}
static void __attribute__((constructor)) io_read_str_use(void) {
  io_eff(CID(Io.read_str), io_read_str_run);
}
#endif

#ifdef CID(Io.write_str)
Term io_write_str_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)(u32)f[0];
  w->data = io64_str_bytes(e, f[1], &w->size);
  w->code = w->data == NULL ? EINVAL : 0;
  return w->code ? io_write_fd_pack(e, w)
    : io_work(w, io_write_fd_call, io_write_fd_pack);
}
static void __attribute__((constructor)) io_write_str_use(void) {
  io_eff(CID(Io.write_str), io_write_str_run);
}
#endif
