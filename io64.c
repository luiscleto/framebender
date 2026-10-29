// framebender driver effects (trusted code, used only by main.bend).
//
// Io.write_fd: write all the bytes of a list to an inherited descriptor
// (1: stdout, 2: stderr) without reopening it (Base has no byte-exact write
// to them). Used for messages.
// Io.read_block: read the next piece of a file's text straight into a packed
// block (a BGZF VCF is decompressed; the next piece is read ahead).
// Io.fa_start, Io.fa_wait: read a FASTA range at a 64-bit offset and pack
// its letters, on a helper thread (a batch's reads at once).
// Io.write_block: write the first n bytes of a packed block to a descriptor.
//
// A packed block is an Array<U32> of 2^d words, byte i in byte i & 3 of word
// i >> 2 (little-endian). The blocks these effects make are exactly
// bytes_enc.bend's enc: the smallest d with 4 * 2^d >= n (d = 0 for n = 0),
// every byte past n zero.
//
// A read buffer or libdeflate's decompressor that cannot be allocated fails
// with ENOMEM; the driver reports it as "out of memory". A full heap is not
// seen here on a CPU build: Bend's runtime stops the run first, with
// "bend: out of memory: ..." and exit code 1.

#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "io64.c packs blocks little-endian: byte i in byte i & 3 of word i >> 2"
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

// The depth of the smallest block that holds n bytes: 4 * 2^d >= n.
static u32 io64_depth(uint64_t n) {
  u32 d = 0;
  while (((uint64_t)4 << d) < n) d += 1;
  return d;
}

// A block of depth d (2^d u32 words); its heap location in *loc. Its bytes
// are not set: the caller writes the first n and zeroes the rest
// (io64_pad). Returns 0 when the heap is full (device builds only; on a CPU
// build the runtime stops the run instead).
static int io64_block(Env e, u32 d, u64* loc) {
  *loc = heap_alloc(e, blk_wcls(0, d));
  if (err_seen(e.mem)) return 0;
  return 1;
}

// Every byte of the block from n on set to 0, to the end of its heap cells
// (a block of depth 0 takes a whole 8-byte cell).
static void io64_pad(Env e, u32 d, u64 loc, uint64_t n) {
  size_t cells = d == 0 ? 8 : (size_t)4 << d;
  memset((char*)(e.mem + loc) + n, 0, cells - n);
}

#ifdef CID(Io.read_block)
// Io.read_block(file, max, gz): read the next max bytes of the file's text
// (max <= 2^31; fewer only at its end); answers (n, block) with the n bytes
// packed as enc (n = 0 at the end). The text is the file's bytes, or, when
// gz is 1 and the file starts with a BGZF block header, the bytes its BGZF
// blocks decompress to. A read error fails with errno; a file whose first two
// bytes are 1f 8b (gzip's) and that does not start with a BGZF block header
// with IO64_NOT_BGZF; a BGZF block that is damaged or cut short (its header,
// deflate data, CRC32 or ISIZE), or a BGZF file that does not end with an
// empty block (bgzip's end-of-file marker), with IO64_BAD_BGZF; a BGZF file
// in a build without libdeflate with IO64_NO_DEFLATE.
//
// The driver reads one such stream at a time (the .fai to its end, then the
// VCF). After a full piece, the next pieces of the same stream (up to
// IO64_AHEAD of them) are read ahead, in order, by one helper thread into
// blocks allocated here, through its own duplicate of the descriptor (which
// shares the file position), and handed out one per call, in order. The
// helper stops after a piece that is short (the end) or failed; that piece's
// answer (its error, if any) is handed out when its turn comes. Heap blocks
// are allocated and freed only on the calling thread; a block being filled
// is referenced by no term until it is handed out.

#define IO64_NOT_BGZF 1001
#define IO64_BAD_BGZF 1002
#define IO64_NO_DEFLATE 1003

#include <sys/stat.h>
#ifdef FB_LIBDEFLATE
#include <libdeflate.h>
#endif

// The stream: the file (descriptor, device, inode), its format (0 not known
// yet, 1 plain, 2 BGZF), the first bytes read to learn it and not handed out
// yet (head), and for BGZF whether the last block read was empty (last0), the
// bytes of the last block not handed out yet (carry) and one compressed block
// (blk).
typedef struct {
  int fd; dev_t dev; ino_t ino; int kind; int last0;
  unsigned char head[18]; size_t hn, hat;
  unsigned char carry[65536]; size_t cn, cat;
  unsigned char blk[65536];
#ifdef FB_LIBDEFLATE
  struct libdeflate_decompressor* dec;
#endif
} Io64In;

// The pieces read ahead: a ring of io64_ahead_n slots, each free, holding a
// block to fill (want), or a filled one (full: got bytes read, code its
// error, 0 if none). The helper fills slot fi, the calling thread hands out
// slot ti and gives blocks to the free slots from ai on (ti <= fi <= ai <=
// ti + io64_ahead_n, as counts). on: a helper was started and not joined;
// done: it stopped (after a short or failed piece, or when asked: stop); the
// helper's descriptor (a duplicate); the size of every piece (max), the
// depth of their blocks (d). io64_ahead_n is 16, or --threads N (Io.threads,
// before the first read), at most IO64_AHEAD_MAX; a plain static, as the
// runtime runs the driver's effects in order and the helper starts after it
// is set (pthread_create).
#define IO64_AHEAD_MAX 128
static u32 io64_ahead_n = 16;
enum { IO64_FREE, IO64_WANT, IO64_FULL };
typedef struct { int state; u64 loc; char* p; uint64_t got; u32 code; } Io64Slot;
typedef struct {
  int on, done, stop; pthread_t th; int fd; uint64_t max; u32 d;
  uint64_t ti, fi, ai;
  Io64Slot q[IO64_AHEAD_MAX];
  pthread_mutex_t mu; pthread_cond_t cv;
} Io64Ahead;

static Io64In io64_in = {.fd = -1};
static Io64Ahead io64_ahead = {.mu = PTHREAD_MUTEX_INITIALIZER, .cv = PTHREAD_COND_INITIALIZER};

#ifdef CID(Io.threads)
// Io.threads(n): the depth of the read-ahead, n (the thread count) or 16 for
// 0, at most IO64_AHEAD_MAX. The driver calls it once, before its first
// read (no helper runs yet). Answers 0.
Term io_threads_run(Env e, Term* f, IoWork* w) {
  u32 n = (u32)f[0];
  io64_ahead_n = n == 0 ? 16 : n < IO64_AHEAD_MAX ? n : IO64_AHEAD_MAX;
  return (Term)0;
}
static void __attribute__((constructor)) io_threads_use(void) {
  io_eff(CID(Io.threads), io_threads_run);
}
#endif

// Exactly n bytes from fd, fewer only at the end of the file; the count, or
// -errno.
static int64_t io64_full(int fd, unsigned char* p, uint64_t n) {
  uint64_t got = 0;
  while (got < n) {
    ssize_t k = read(fd, p + got, n - got > INT32_MAX ? INT32_MAX : n - got);
    if (k < 0 && errno == EINTR) continue;
    if (k < 0) return -(int64_t)errno;
    if (k == 0) break;
    got += (uint64_t)k;
  }
  return (int64_t)got;
}

// The BGZF block header bgzip and htslib write: gzip, deflate, only FEXTRA,
// an extra field of 6 bytes holding the subfield BC of length 2 (BSIZE).
static int io64_bgzf_head(const unsigned char* h) {
  return h[0] == 31 && h[1] == 139 && h[2] == 8 && h[3] == 4
    && h[10] == 6 && h[11] == 0 && h[12] == 'B' && h[13] == 'C' && h[14] == 2 && h[15] == 0;
}

// Learn the stream's format from its first bytes (kept in head); with gz 0
// it is plain, and nothing is read. Answers 0, -errno, or an IO64_ code.
static int64_t io64_kind(Io64In* s, int fd, int gz) {
  if (!gz) { s->kind = 1; return 0; }
  int64_t k = io64_full(fd, s->head, 18);
  if (k < 0) return k;
  s->hn = (size_t)k; s->hat = 0;
  if (k >= 2 && s->head[0] == 31 && s->head[1] == 139) {
    if (k < 18 || !io64_bgzf_head(s->head)) return IO64_NOT_BGZF;
#ifdef FB_LIBDEFLATE
    if (s->dec == NULL) s->dec = libdeflate_alloc_decompressor();
    if (s->dec == NULL) return ENOMEM;
    s->kind = 2;
    s->last0 = 0;
    return 0;
#else
    return IO64_NO_DEFLATE;
#endif
  }
  s->kind = 1;
  return 0;
}

static uint32_t io64_le32(const unsigned char* b) {
  return (uint32_t)b[0] | (uint32_t)b[1] << 8 | (uint32_t)b[2] << 16 | (uint32_t)b[3] << 24;
}

// The next BGZF block of the stream into dst (room for 65536 bytes): its
// size in *n, which may be 0 (the empty block bgzip ends a file with, also
// found between the members of concatenated files); *end set at the end of
// the file instead, which must come right after an empty block: a file cut
// at a block boundary has none. Answers 0, -errno or IO64_BAD_BGZF.
static int64_t io64_block_in(Io64In* s, int fd, unsigned char* dst, size_t* n, int* end) {
#ifdef FB_LIBDEFLATE
  unsigned char* b = s->blk;
  size_t at = 0;
  if (s->hat < s->hn) {  // the first block's header was read to learn the format
    at = s->hn - s->hat;
    memcpy(b, s->head + s->hat, at);
    s->hat = s->hn;
  }
  int64_t k = io64_full(fd, b + at, 18 - at);
  if (k < 0) return k;
  *n = 0;
  *end = at + (size_t)k == 0;
  if (*end) return s->last0 ? 0 : IO64_BAD_BGZF;
  if (at + (size_t)k < 18 || !io64_bgzf_head(b)) return IO64_BAD_BGZF;
  size_t size = (size_t)(b[16] | b[17] << 8) + 1;  // BSIZE + 1: the whole block
  if (size < 26) return IO64_BAD_BGZF;
  k = io64_full(fd, b + 18, size - 18);
  if (k < 0) return k;
  if ((size_t)k != size - 18) return IO64_BAD_BGZF;
  uint32_t crc = io64_le32(b + size - 8), isize = io64_le32(b + size - 4);
  size_t in = 0, out = 0;
  if (isize > 65536
      || libdeflate_deflate_decompress_ex(s->dec, b + 18, size - 26, dst, isize, &in, &out) != LIBDEFLATE_SUCCESS
      || in != size - 26 || out != isize || libdeflate_crc32(0, dst, out) != crc) {
    return IO64_BAD_BGZF;
  }
  *n = out;
  s->last0 = out == 0;
  return 0;
#else
  (void)s; (void)fd; (void)dst; (void)n; (void)end;
  return IO64_NO_DEFLATE;
#endif
}

// Up to max bytes of the stream's text into p, all of them unless it ends;
// the count, -errno, or an IO64_ code.
static int64_t io64_text(Io64In* s, int fd, char* p, uint64_t max) {
  uint64_t got = 0;
  if (s->kind == 1) {
    while (got < max && s->hat < s->hn) p[got++] = (char)s->head[s->hat++];
    int64_t k = io64_full(fd, (unsigned char*)p + got, max - got);
    return k < 0 ? k : (int64_t)(got + (uint64_t)k);
  }
  while (got < max) {
    if (s->cat < s->cn) {
      size_t k = s->cn - s->cat < max - got ? s->cn - s->cat : (size_t)(max - got);
      memcpy(p + got, s->carry + s->cat, k);
      s->cat += k;
      got += k;
      continue;
    }
    // A block that fits goes straight into the piece; else into carry.
    int direct = max - got >= 65536;
    size_t n;
    int end;
    int64_t r = io64_block_in(s, fd, direct ? (unsigned char*)p + got : s->carry, &n, &end);
    if (r != 0) return r < 0 ? r : -r;
    if (end) break;
    if (direct) got += n;
    else { s->cn = n; s->cat = 0; }
  }
  return (int64_t)got;
}

static void* io64_ahead_run(void* x) {
  Io64Ahead* a = x;
  pthread_mutex_lock(&a->mu);
  for (;;) {
    Io64Slot* sl = &a->q[a->fi % io64_ahead_n];
    while (sl->state != IO64_WANT && !a->stop) pthread_cond_wait(&a->cv, &a->mu);
    if (a->stop) break;
    pthread_mutex_unlock(&a->mu);
    int64_t r = io64_text(&io64_in, a->fd, sl->p, a->max);
    pthread_mutex_lock(&a->mu);
    sl->code = r < 0 ? (u32)-r : 0;
    sl->got = r < 0 ? 0 : (uint64_t)r;
    sl->state = IO64_FULL;
    a->fi += 1;
    pthread_cond_broadcast(&a->cv);
    if (sl->code != 0 || sl->got < a->max) break;
  }
  a->done = 1;
  pthread_cond_broadcast(&a->cv);
  pthread_mutex_unlock(&a->mu);
  return NULL;
}

// Blocks for the free slots, while the helper goes on. A block the heap
// cannot give is simply not added (the queue is then shorter).
static void io64_ahead_give(Env e) {
  Io64Ahead* a = &io64_ahead;
  for (;;) {
    pthread_mutex_lock(&a->mu);
    int more = !a->done && a->ai < a->ti + io64_ahead_n;
    pthread_mutex_unlock(&a->mu);
    if (!more) return;
    u64 loc;
    if (!io64_block(e, a->d, &loc)) return;
    pthread_mutex_lock(&a->mu);
    Io64Slot* sl = &a->q[a->ai % io64_ahead_n];
    *sl = (Io64Slot){IO64_WANT, loc, (char*)(e.mem + loc), 0, 0};
    a->ai += 1;
    pthread_cond_broadcast(&a->cv);
    pthread_mutex_unlock(&a->mu);
  }
}

// Stop the helper (if one runs), join it, close its descriptor, and free the
// blocks of the slots not handed out; answers whether one of them holds
// bytes (a piece read ahead and not handed out).
static int io64_ahead_end(Env e) {
  Io64Ahead* a = &io64_ahead;
  if (!a->on) return 0;
  pthread_mutex_lock(&a->mu);
  a->stop = 1;
  pthread_cond_broadcast(&a->cv);
  pthread_mutex_unlock(&a->mu);
  pthread_join(a->th, NULL);
  close(a->fd);
  int left = 0;
  for (; a->ti < a->ai; a->ti += 1) {
    Io64Slot* sl = &a->q[a->ti % io64_ahead_n];
    if (sl->state == IO64_FULL && sl->got != 0) left = 1;
    heap_free(e, blk_wcls(0, a->d), sl->loc);
    sl->state = IO64_FREE;
  }
  a->on = 0;
  return left;
}

// Start reading the stream's next pieces of max bytes ahead into blocks of
// depth d. Nothing is started if a descriptor or a thread is not available:
// the next call then reads the piece itself.
static void io64_ahead_start(Env e, int fd, u32 d, uint64_t max) {
  Io64Ahead* a = &io64_ahead;
  int dup_fd = dup(fd);
  if (dup_fd < 0) return;
  a->done = a->stop = 0; a->fd = dup_fd; a->max = max; a->d = d;
  a->ti = a->fi = a->ai = 0;
  for (int i = 0; i < IO64_AHEAD_MAX; i += 1) a->q[i].state = IO64_FREE;
  if (pthread_create(&a->th, NULL, io64_ahead_run, a) != 0) {
    close(dup_fd);
    return;
  }
  a->on = 1;
  io64_ahead_give(e);
}

// The next piece read ahead (the helper runs): waits for its slot to be
// filled, takes it out of the queue, gives the free slots new blocks (or,
// after the stream's last piece, ends the helper).
static Io64Slot io64_ahead_take(Env e) {
  Io64Ahead* a = &io64_ahead;
  pthread_mutex_lock(&a->mu);
  Io64Slot* sl = &a->q[a->ti % io64_ahead_n];
  while (sl->state != IO64_FULL && a->ai > a->ti && !(a->done && a->fi == a->ti)) pthread_cond_wait(&a->cv, &a->mu);
  Io64Slot got = *sl;
  if (sl->state == IO64_FULL) {
    sl->state = IO64_FREE;
    a->ti += 1;
  }
  pthread_mutex_unlock(&a->mu);
  if (got.state != IO64_FULL) {
    // No piece for this call: the queue is empty (the heap gave no block)
    // or the helper stopped. Nothing past the pieces handed out was read:
    // end the helper; the caller reads the piece itself.
    io64_ahead_end(e);
    return got;
  }
  if (got.code != 0 || got.got < a->max) io64_ahead_end(e);
  else io64_ahead_give(e);
  return got;
}

// The answer for a piece of got bytes read into the block of depth d at loc
// (code: its error, 0 if none). A short last piece moves to enc's smaller
// block; the padding is zeroed.
static Term io64_piece(Env e, int fd, u32 d, u64 loc, uint64_t got, u32 code) {
  if (code != 0) {
    heap_free(e, blk_wcls(0, d), loc);
    return io_tup(e, io_hand(fd), io_fail(e, code, NULL));
  }
  u32 d2 = io64_depth(got);
  if (d2 < d) {
    u64 loc2;
    if (!io64_block(e, d2, &loc2)) {
      heap_free(e, blk_wcls(0, d), loc);
      return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
    }
    memcpy((char*)(e.mem + loc2), (char*)(e.mem + loc), (size_t)got);
    heap_free(e, blk_wcls(0, d), loc);
    loc = loc2;
    d = d2;
  }
  io64_pad(e, d, loc, got);
  return io_tup(e, io_hand(fd), io_done(e, io_tup(e, (Term)(u32)got, term_blk(0, d, loc))));
}

Term io_read_block_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  uint64_t max = (u32)f[1];
  int gz = (u32)f[2] == 1;
  if (max > ((uint64_t)1 << 31)) max = (uint64_t)1 << 31;
  u32 d = io64_depth(max);
  struct stat st;
  if (fstat(fd, &st) != 0) return io_tup(e, io_hand(fd), io_fail(e, (u32)errno, NULL));
  Io64In* s = &io64_in;
  if (s->fd != fd || s->dev != st.st_dev || s->ino != st.st_ino) {
    // Another file: the last stream must have nothing left to hand out (a
    // piece read ahead, if any, is its empty end).
    if (io64_ahead_end(e) || s->hat < s->hn || s->cat < s->cn) {
      return io_tup(e, io_hand(fd), io_fail(e, EBUSY, NULL));
    }
    s->fd = fd; s->dev = st.st_dev; s->ino = st.st_ino; s->kind = 0;
    s->hn = s->hat = s->cn = s->cat = 0;
  }
  if (io64_ahead.on) {
    // The next piece read ahead, for this stream. The driver asks every
    // piece with the same max; a call with another max fails (EINVAL).
    if (io64_ahead.max != max) {
      io64_ahead_end(e);
      return io_tup(e, io_hand(fd), io_fail(e, EINVAL, NULL));
    }
    Io64Slot a = io64_ahead_take(e);
    if (a.state == IO64_FULL) return io64_piece(e, fd, io64_ahead.d, a.loc, a.got, a.code);
  }
  if (s->kind == 0) {
    int64_t r = io64_kind(s, fd, gz);
    if (r < 0) return io_tup(e, io_hand(fd), io_fail(e, (u32)-r, NULL));
    if (r > 0) return io_tup(e, io_hand(fd), io_fail(e, (u32)r, NULL));
  }
  u64 loc;
  if (!io64_block(e, d, &loc)) {
    return io_tup(e, io_hand(fd), io_fail(e, ENOMEM, NULL));
  }
  int64_t r = io64_text(s, fd, (char*)(e.mem + loc), max);
  uint64_t got = r < 0 ? 0 : (uint64_t)r;
  if (r >= 0 && got == max) io64_ahead_start(e, fd, d, max);
  return io64_piece(e, fd, d, loc, got, r < 0 ? (u32)-r : 0);
}
static void __attribute__((constructor)) io_read_block_use(void) {
  io_eff(CID(Io.read_block), io_read_block_run);
}
#endif

#ifdef CID(Io.fa_start)
// A FASTA read (Io.fa_start's arguments: file, hi, lo, shi, slo, chi, clo,
// bhi, blo, whi, wlo, want):
// read the span of shi * 2^32 + slo bytes of the FASTA file at offset
// hi * 2^32 + lo, in parts of at most 1 MiB, where the first byte is at
// column col = chi * 2^32 + clo of the contig's line layout (lb = bhi * 2^32
// + blo letters, then LF, or CR LF when lw = whi * 2^32 + wlo = lb + 2;
// col < lw). The driver keeps offsets and spans below 2^47. Every byte must
// be where the layout puts it: an LF at column lw - 1; a CR at column lb,
// only when lw = lb + 2; any other byte at a column below lb, and not a
// space or tab. The letters (the bytes that are
// not LF or CR; want <= 2^31) are packed as enc. Answers (code, (n, block)):
// code 0 when every byte fits and exactly want letters were read; 1 when a
// byte does not fit the layout; 2 when fewer (or more) than want letters
// were read (the file ends early). A read error fails with errno.
#define IO64_PART ((uint64_t)1 << 20)

#ifdef __SSE2__
#include <emmintrin.h>
// The 16 bytes at p hold an LF, CR, space or tab: their mask.
static inline unsigned io64_bad16(const char* p) {
  __m128i v = _mm_loadu_si128((const __m128i*)p);
  __m128i m = _mm_or_si128(_mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8(10)), _mm_cmpeq_epi8(v, _mm_set1_epi8(13))),
                           _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8(32)), _mm_cmpeq_epi8(v, _mm_set1_epi8(9))));
  return (unsigned)_mm_movemask_epi8(m);
}
#endif

// A whole line at src, lb letters (16 <= lb <= 64) and then its LF: if no
// letter is an LF, CR, space or tab and byte lb is an LF, copies the letters
// to dst and answers 1; else copies nothing and answers 0. The letters are
// read in blocks of 16 bytes, the last block ending at lb (it may overlap the
// one before). Without SSE2 it answers 0 (the bytes then go by the rules
// below).
static inline int io64_line(char* dst, const char* src, uint64_t lb) {
#ifdef __SSE2__
  uint64_t nb = (lb + 15) / 16;
  unsigned bad = 0;
  for (uint64_t j = 0; j < nb; j += 1) {
    bad |= io64_bad16(src + (j * 16 + 16 <= lb ? j * 16 : lb - 16));
  }
  if (bad != 0 || src[lb] != 10) return 0;
  memcpy(dst, src, (size_t)lb);
  return 1;
#else
  (void)dst; (void)src; (void)lb;
  return 0;
#endif
}
static uint64_t io64_wide(Term hi, Term lo) {
  return ((uint64_t)(u32)hi << 32) | (uint64_t)(u32)lo;
}

// One read: its arguments, its block (depth d at loc, p its bytes), and what
// it found: the read's errno (err, 0 if none), the code and the letters n.
typedef struct {
  int fd; uint64_t off, span, col, lb, lw, want;
  u32 d; u64 loc; char* p;
  u32 err, code; uint64_t n;
} Io64Fa;

// The read itself, into r->p (no heap access: it may run on a helper
// thread). Sets err (and then nothing else is used), or code and n.
static void io64_fa_do(Io64Fa* r) {
  char* buf = malloc(IO64_PART);
  if (buf == NULL) { r->err = ENOMEM; return; }
  int fd = r->fd;
  uint64_t off = r->off, span = r->span, col = r->col, lb = r->lb, lw = r->lw, want = r->want;
  char* p = r->p;
  uint64_t n = 0;
  u32 code = 0;
  uint64_t done = 0;
  while (done < span && code == 0) {
    // One part: up to 1 MiB of the span, read in full unless the file ends.
    uint64_t part = span - done < IO64_PART ? span - done : IO64_PART;
    uint64_t got = 0;
    while (got < part) {
      ssize_t k = pread(fd, buf + got, part - got, (off_t)(off + done + got));
      if (k < 0 && errno == EINTR) continue;
      if (k < 0) {
        r->err = (u32)errno;
        free(buf);
        return;
      }
      if (k == 0) break;
      got += (uint64_t)k;
    }
    uint64_t i = 0;
    while (i < got && code == 0) {
      if (col == 0 && lw == lb + 1 && lb >= 16 && lb <= 64 && got - i >= lw && n + lb <= want
          && io64_line(p + n, buf + i, lb)) {
        // A whole line and its LF, as the rules below take them.
        n += lb;
        i += lw;
        continue;
      }
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
  r->code = code;
  r->n = n;
}

// A read's arguments from the effect's (f[0] .. f[11]); its block not yet
// allocated.
static Io64Fa io64_fa_args(Term* f) {
  Io64Fa r = {0};
  r.fd = io_hand_v(f[0]);
  r.off = io64_wide(f[1], f[2]);
  r.span = io64_wide(f[3], f[4]);
  r.col = io64_wide(f[5], f[6]);
  r.lb = io64_wide(f[7], f[8]);
  r.lw = io64_wide(f[9], f[10]);
  r.want = (u32)f[11];
  if (r.want > ((uint64_t)1 << 31)) r.want = (uint64_t)1 << 31;
  r.d = io64_depth(r.want);
  return r;
}

// The block for a read (err = ENOMEM if the heap is full).
static void io64_fa_alloc(Env e, Io64Fa* r) {
  if (!io64_block(e, r->d, &r->loc)) { r->err = ENOMEM; return; }
  r->p = (char*)(e.mem + r->loc);
}

// The effect's answer for a read done (its block freed on an error).
static Term io64_fa_answer(Env e, Io64Fa* r) {
  if (r->err != 0) {
    if (r->p != NULL) heap_free(e, blk_wcls(0, r->d), r->loc);
    return io_tup(e, io_hand(r->fd), io_fail(e, r->err, NULL));
  }
  io64_pad(e, r->d, r->loc, r->n);
  return io_tup(e, io_hand(r->fd), io_done(e, io_tup(e, (Term)r->code, io_tup(e, (Term)(u32)r->n, term_blk(0, r->d, r->loc)))));
}

// Io.fa_start(file, hi, lo, ...): the read above, started on a helper
// thread; answers (file, t), t its ticket. Io.fa_wait(file, t): waits for the
// read with ticket t and answers (code, (n, block)) or its errno, as above.
// The driver starts at most IO64_FA_MAX reads before waiting for each of them,
// in order (32, or --threads N: main.bend's answers). The read's block is
// allocated (and later padded and handed out, or freed) on the calling thread;
// the helper only fills it. A read whose block or thread cannot be had is done
// (or fails, ENOMEM) at once; its answer is kept for Io.fa_wait. A ticket that is not pending fails (EINVAL).
#define IO64_FA_MAX 128
typedef struct { int used, running; pthread_t th; Io64Fa r; } Io64FaSlot;
static Io64FaSlot io64_fa[IO64_FA_MAX];

static void* io64_fa_run(void* x) {
  io64_fa_do(&((Io64FaSlot*)x)->r);
  return NULL;
}

Term io_fa_start_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  u32 t = 0;
  while (t < IO64_FA_MAX && io64_fa[t].used) t += 1;
  if (t == IO64_FA_MAX) return io_tup(e, io_hand(fd), (Term)(u32)IO64_FA_MAX);
  Io64FaSlot* s = &io64_fa[t];
  *s = (Io64FaSlot){1, 0, 0, io64_fa_args(f)};
  io64_fa_alloc(e, &s->r);
  if (s->r.err == 0) {
    if (pthread_create(&s->th, NULL, io64_fa_run, s) == 0) s->running = 1;
    else io64_fa_do(&s->r);
  }
  return io_tup(e, io_hand(fd), (Term)t);
}

Term io_fa_wait_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  u32 t = (u32)f[1];
  if (t >= IO64_FA_MAX || !io64_fa[t].used) return io_tup(e, io_hand(fd), io_fail(e, EINVAL, NULL));
  Io64FaSlot* s = &io64_fa[t];
  if (s->running) pthread_join(s->th, NULL);
  s->running = 0;
  s->used = 0;
  return io64_fa_answer(e, &s->r);
}

static void __attribute__((constructor)) io_fa_start_use(void) {
  io_eff(CID(Io.fa_start), io_fa_start_run);
  io_eff(CID(Io.fa_wait), io_fa_wait_run);
}
#endif

#ifdef CID(Io.write_block)
// Io.write_block(fd, n, block): write the block's first n bytes (n at most
// its size) to the inherited descriptor fd, all of them; frees the block.
// Answers 0, or the errno of a failed write (EIO for a write of 0 bytes);
// EINVAL, writing nothing, if the block is not a packed buffer of at most
// 2^31 bytes (depth 29).
Term io_write_block_run(Env e, Term* f, IoWork* w) {
  int fd = (int)(u32)f[0];
  uint64_t n = (u32)f[1];
  Term a = f[2];
  if (term_tag(a) != TAG_BUF || blk_cls(a) > 29) return (Term)EINVAL;
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

#ifndef FB_NO_RTS_THREADS
// Bend's worker threads follow --threads: before main, the program's words
// are read as Bend's runtime splits them (the words between +RTS and -RTS are
// the runtime's; every word after --RTS is the program's), and, if they are a
// command line B.Args.parse accepts with a --threads N (the last one), the
// words "--threads N" are put before BENDRTS, which the runtime reads first.
// So the runtime runs at most N workers unless the user's own BENDRTS or
// +RTS --threads says otherwise (the runtime takes the last one). Anything
// unexpected (no command line to read, a command line of 1 MiB or more, a
// line Args.parse refuses) leaves BENDRTS as it is. On Linux the words come from /proc/self/cmdline, on macOS
// from _NSGetArgv(); elsewhere nothing is done.
#if defined(__linux__) || defined(__APPLE__)
#ifdef __APPLE__
#include <crt_externs.h>
#endif

// One or more decimal digits of a value below 2^48 (B.Pos.read stops the run
// on a larger one: "a Nat past the largest immediate"); the value, capped at
// 1000.
static int io64_num(const char* x, unsigned* v) {
  if (*x == 0) return 0;
  uint64_t n = 0;
  for (; *x; x += 1) {
    if (*x < '0' || *x > '9') return 0;
    n = n * 10 + (uint64_t)(*x - '0');
    if (n >> 48) return 0;
  }
  *v = n > 1000 ? 1000 : (unsigned)n;
  return 1;
}

// B.Args.threads of the program's words w[0 .. n): N, or 0 for none (no
// --threads, or a line Args.parse refuses).
static unsigned io64_threads_of(char** w, int n) {
  if (n < 1 || strcmp(w[0], "norm") != 0) return 0;
  int pend = 0, ok = 1, ref = 0, vcf = 0;
  unsigned thr = 0, v = 0;
  for (int i = 1; i < n; i += 1) {
    const char* x = w[i];
    if (pend == 'f') { ok = ok && !ref; ref = 1; pend = 0; }
    else if (pend == 'c') { ok = ok && (!strcmp(x, "e") || !strcmp(x, "w")); pend = 0; }
    else if (pend == 'w') { ok = ok && io64_num(x, &v) && v >= 1; pend = 0; }
    else if (pend == 't') {
      if (io64_num(x, &v)) { thr = v; ok = ok && v >= 1 && v <= 128; } else ok = 0;
      pend = 0;
    }
    else if (!strcmp(x, "-f")) pend = 'f';
    else if (!strcmp(x, "-c")) pend = 'c';
    else if (!strcmp(x, "-w")) pend = 'w';
    else if (!strcmp(x, "--threads")) pend = 't';
    else { ok = ok && !(x[0] == '-' && x[1] != 0) && !vcf; vcf = 1; }
  }
  return ok && pend == 0 && ref && vcf ? thr : 0;
}

static void __attribute__((constructor)) io64_rts_threads(void) {
  int argc = 0;
  char** argv = NULL;
  char* buf = NULL;
#ifdef __APPLE__
  argc = *_NSGetArgc();
  argv = *_NSGetArgv();
#else
  int fd = open("/proc/self/cmdline", O_RDONLY);
  if (fd < 0) return;
  size_t cap = 1 << 20, len = 0;
  buf = malloc(cap + 1);
  if (buf == NULL) { close(fd); return; }
  for (;;) {
    ssize_t k = read(fd, buf + len, cap - len);
    if (k < 0 && errno == EINTR) continue;
    if (k < 0) { close(fd); free(buf); return; }
    if (k == 0) break;
    len += (size_t)k;
    if (len == cap) { close(fd); free(buf); return; }
  }
  close(fd);
  buf[len] = 0;
  for (size_t i = 0; i < len; i += 1) if (buf[i] == 0) argc += 1;
  argv = malloc(((size_t)argc + 1) * sizeof(char*));
  if (argv == NULL) { free(buf); return; }
  for (size_t i = 0, at = 0, j = 0; i < len; i += 1) {
    if (buf[i] == 0) { argv[j++] = buf + at; at = i + 1; }
  }
#endif
  char** w = malloc(((size_t)argc + 1) * sizeof(char*));
  int n = 0, in = 0, all = 0;
  if (w != NULL) {
    for (int i = 1; i < argc; i += 1) {
      const char* a = argv[i];
      if (all) w[n++] = argv[i];
      else if (!strcmp(a, "--RTS")) all = 1;
      else if (!strcmp(a, "+RTS") || !strcmp(a, "-RTS")) in = a[0] == '+';
      else if (!in) w[n++] = argv[i];
    }
    unsigned t = io64_threads_of(w, n);
    if (t != 0) {
      const char* old = getenv("BENDRTS");
      char* rts = malloc(32 + (old != NULL ? strlen(old) : 0));
      if (rts != NULL) {
        sprintf(rts, "--threads %u%s%s", t, old != NULL ? " " : "", old != NULL ? old : "");
        setenv("BENDRTS", rts, 1);
        free(rts);
      }
    }
    free(w);
  }
#ifndef __APPLE__
  free(argv);
  free(buf);
#endif
}
#endif
#endif
