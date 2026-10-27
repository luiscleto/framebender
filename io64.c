// framebender driver effects (trusted code, used only by main.bend).
//
// Io.write_fd: write all the bytes of a list to an inherited descriptor
// (1: stdout, 2: stderr) without reopening it (Base has no byte-exact write
// to them). Used for messages.
// Io.read_block: read the next piece of a file straight into a packed block.
// Io.fa_read: read a FASTA range at a 64-bit offset and pack its letters.
// Io.write_block: write the first n bytes of a packed block to a descriptor.
//
// A packed block is an Array<U32> of 2^d words, byte i in byte i & 3 of word
// i >> 2 (little-endian). The blocks these effects make are exactly
// bytes_enc.bend's enc: the smallest d with 4 * 2^d >= n (d = 0 for n = 0),
// every byte past n zero.

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

// The depth of the smallest block that holds n bytes: 4 * 2^d >= n.
static u32 io64_depth(uint64_t n) {
  u32 d = 0;
  while (((uint64_t)4 << d) < n) d += 1;
  return d;
}

// A block of depth d (2^d u32 words); its heap location in *loc. Its bytes
// are not set: the caller writes the first n and zeroes the rest
// (io64_pad). Returns 0 when the heap is full.
static int io64_block(Env e, u32 d, u64* loc) {
  *loc = heap_alloc(e, blk_wcls(0, d));
  if (err_seen(e.mem)) return 0;
  return 1;
}

// Every byte of the block from n on set to 0.
static void io64_pad(Env e, u32 d, u64 loc, uint64_t n) {
  memset((char*)(e.mem + loc) + n, 0, ((size_t)4 << d) - n);
}

#ifdef CID(Io.read_block)
// Io.read_block(file, max): read from the file's position until max bytes
// (max <= 2^31) are read or the file ends; answers (n, block) with the n
// bytes read packed as enc (n = 0 at the end of the file). A read error
// fails with errno.
Term io_read_block_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  uint64_t max = (u32)f[1];
  if (max > ((uint64_t)1 << 31)) max = (uint64_t)1 << 31;
  u32 d = io64_depth(max);
  u64 loc;
  if (!io64_block(e, d, &loc)) {
    return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
  }
  char* p = (char*)(e.mem + loc);
  uint64_t got = 0;
  while (got < max) {
    ssize_t n = read(fd, p + got, max - got > INT32_MAX ? INT32_MAX : max - got);
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) {
      u32 code = (u32)errno;
      heap_free(e, blk_wcls(0, d), loc);
      return io_tup(e, io_hand(fd), io_fail(e, code, NULL));
    }
    if (n == 0) break;
    got += (uint64_t)n;
  }
  u32 d2 = io64_depth(got);
  if (d2 < d) {
    // A short last piece: move it to the smallest block (enc's).
    u64 loc2;
    if (!io64_block(e, d2, &loc2)) {
      return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
    }
    memcpy((char*)(e.mem + loc2), p, (size_t)got);
    heap_free(e, blk_wcls(0, d), loc);
    loc = loc2;
    d = d2;
  }
  io64_pad(e, d, loc, got);
  return io_tup(e, io_hand(fd), io_done(e, io_tup(e, (Term)(u32)got, term_blk(0, d, loc))));
}
static void __attribute__((constructor)) io_read_block_use(void) {
  io_eff(CID(Io.read_block), io_read_block_run);
}
#endif

#ifdef CID(Io.fa_read)
// Io.fa_read(file, hi, lo, shi, slo, col, lb, lw, want): read the span of
// shi * 2^32 + slo bytes of the FASTA file at offset hi * 2^32 + lo, in
// parts of at most 16 MiB, where the first byte is at column col of the
// contig's line layout (lb letters, then LF, or CR LF when lw = lb + 2;
// col < lw). Every byte must be where the layout puts it: an LF at column
// lw - 1; a CR at column lb, only when lw = lb + 2; any other byte at a
// column below lb, and not a space or tab. The letters (the bytes that are
// not LF or CR; want <= 2^31) are packed as enc. Answers (code, (n, block)):
// code 0 when every byte fits and exactly want letters were read; 1 when a
// byte does not fit the layout; 2 when fewer (or more) than want letters
// were read (the file ends early). A read error fails with errno.
#define IO64_PART ((uint64_t)1 << 24)
Term io_fa_read_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  uint64_t off = ((uint64_t)(u32)f[1] << 32) | (uint64_t)(u32)f[2];
  uint64_t span = ((uint64_t)(u32)f[3] << 32) | (uint64_t)(u32)f[4];
  uint64_t col = (u32)f[5], lb = (u32)f[6], lw = (u32)f[7];
  uint64_t want = (u32)f[8];
  if (want > ((uint64_t)1 << 31)) want = (uint64_t)1 << 31;
  char* buf = malloc(IO64_PART);
  if (buf == NULL) return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
  u32 d = io64_depth(want);
  u64 loc;
  if (!io64_block(e, d, &loc)) {
    free(buf);
    return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
  }
  char* p = (char*)(e.mem + loc);
  uint64_t n = 0;
  u32 code = 0;
  uint64_t done = 0;
  while (done < span && code == 0) {
    // One part: up to 16 MiB of the span, read in full unless the file ends.
    uint64_t part = span - done < IO64_PART ? span - done : IO64_PART;
    uint64_t got = 0;
    while (got < part) {
      ssize_t k = pread(fd, buf + got, part - got, (off_t)(off + done + got));
      if (k < 0 && errno == EINTR) continue;
      if (k < 0) {
        u32 err = (u32)errno;
        free(buf);
        heap_free(e, blk_wcls(0, d), loc);
        return io_tup(e, io_hand(fd), io_fail(e, err, NULL));
      }
      if (k == 0) break;
      got += (uint64_t)k;
    }
    uint64_t i = 0;
    while (i < got && code == 0) {
      if (col < lb) {
        // A run of letters up to the line's end: tested in one pass, then
        // copied. If it holds a byte that is not a letter, or more letters
        // than want, the bytes are taken one at a time (below) to stop
        // where the per-byte rule stops.
        uint64_t k = lb - col < got - i ? lb - col : got - i;
        unsigned bad = 0;
        for (uint64_t j = 0; j < k; j += 1) {
          unsigned char c = (unsigned char)buf[i + j];
          bad |= (c == 10) | (c == 13) | (c == 32) | (c == 9);
        }
        if (!bad && n + k <= want) {
          memcpy(p + n, buf + i, (size_t)k);
          n += k;
          i += k;
          col += k;
          continue;
        }
      }
      // One byte, by the rule above.
      unsigned char c = (unsigned char)buf[i];
      int fits;
      if (c == 10) fits = col + 1 == lw;
      else if (c == 13) fits = col == lb && lw == lb + 2;
      else fits = c != 32 && c != 9 && col < lb;
      if (!fits) { code = 1; break; }
      if (c != 10 && c != 13) {
        if (n == want) { code = 2; break; }
        p[n++] = (char)c;
      }
      col = col + 1 == lw ? 0 : col + 1;
      i += 1;
    }
    done += got;
    if (got < part) break;  // the file ended
  }
  free(buf);
  if (code == 0 && n != want) code = 2;
  if (code != 0) n = 0;  // the block is not used: the program stops
  io64_pad(e, d, loc, n);
  return io_tup(e, io_hand(fd), io_done(e, io_tup(e, (Term)code, io_tup(e, (Term)(u32)n, term_blk(0, d, loc)))));
}
static void __attribute__((constructor)) io_fa_read_use(void) {
  io_eff(CID(Io.fa_read), io_fa_read_run);
}
#endif

#ifdef CID(Io.write_block)
// Io.write_block(fd, n, block): write the block's first n bytes (n at most
// its size) to the inherited descriptor fd, all of them; frees the block.
// Answers 0, or the errno of a failed write (EIO for a write of 0 bytes).
Term io_write_block_run(Env e, Term* f, IoWork* w) {
  int fd = (int)(u32)f[0];
  uint64_t n = (u32)f[1];
  Term a = f[2];
  uint64_t cap = (uint64_t)4 << blk_cls(a);
  if (n > cap) n = cap;
  const char* p = (const char*)(e.mem + blk_loc(e.mem, a));
  u32 code = 0;
  ssize_t k = 0;
  for (uint64_t at = 0; at < n; at += (uint64_t)k) {
    k = write(fd, p + at, n - at > INT32_MAX ? INT32_MAX : n - at);
    if (k < 0 && errno == EINTR) { k = 0; continue; }
    if (k <= 0) { code = k == 0 ? EIO : (u32)errno; break; }
  }
  blk_free(e, a);
  return (Term)code;
}
static void __attribute__((constructor)) io_write_block_use(void) {
  io_eff(CID(Io.write_block), io_write_block_run);
}
#endif
