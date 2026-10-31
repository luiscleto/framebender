// framebender driver effects (trusted code, used only by main.bend).
//
// Io.write_fd: write all the bytes of a list to an inherited descriptor
// (1: stdout, 2: stderr) without reopening it (Base has no byte-exact write
// to them). Used for messages.
// Io.read_block: read the next piece of a file's text straight into a packed
// block (a BGZF VCF is decompressed; the next piece is read ahead).
// Io.fa_start, Io.fa_wait: read a FASTA range at a 64-bit offset and pack
// its letters, on a helper thread (a batch's reads at once).
// Io.out_set, Io.out_write, Io.out_close: the output (stdout or the -o file,
// plain or BGZF), as B.Args.output says.
// Io.ix_found: whether htslib would read a name as an index (stat), for the
// warning about old indexes beside a BGZF -o file written without -W.
//
// A packed block is an Array<U32> of 2^d words, byte i in byte i & 3 of word
// i >> 2 (little-endian). The blocks these effects make are exactly
// bytes_enc.bend's enc: the smallest d with 4 * 2^d >= n (d = 0 for n = 0),
// every byte past n zero.
//
// libdeflate's decompressor that cannot be allocated fails with ENOMEM (as
// does a read that the system answers with ENOMEM); the driver reports it as
// "out of memory". A full heap is not
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
#include <signal.h>
#ifdef FB_LIBDEFLATE
#include <libdeflate.h>
#if defined(FB_HTSLIB) && defined(FB_LIBDEFLATE)
#define IO64_IX 1
#endif
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

// The files read so far through Io.read_block (the .fai, the VCF), by device
// and inode, from fstat of their open descriptors: the -o file must not be
// one of them (Io.out_write).
#define IO64_SEEN_MAX 8
static struct { dev_t dev; ino_t ino; } io64_seen[IO64_SEEN_MAX];
static int io64_seen_n = 0;
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

#ifdef CID(Io.ix_found)
// Io.ix_found(path): 1 when stat finds something at path that is not a
// directory, else 0 (also for a path with a NUL byte). htslib 1.24 reads the
// first index name stat finds (hts_idx_check_local); a directory it finds
// too, but reading it fails ("could not load index"), so it never answers a
// query. Only stat: nothing is opened or changed. Used, without -W, to warn
// about old indexes beside a BGZF -o file (main.bend's stale).
Term io_ix_found_run(Env e, Term* f, IoWork* w) {
  uint64_t len;
  char* p = io_cbuf(e, f[0], &len, CID(Con));
  struct stat st;
  u32 r = p != NULL && memchr(p, 0, len) == NULL && stat(p, &st) == 0 && !S_ISDIR(st.st_mode);
  free(p);
  return (Term)r;
}
static void __attribute__((constructor)) io_ix_found_use(void) {
  io_eff(CID(Io.ix_found), io_ix_found_run);
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
    if (io64_seen_n < IO64_SEEN_MAX) {
      io64_seen[io64_seen_n].dev = st.st_dev;
      io64_seen[io64_seen_n].ino = st.st_ino;
      io64_seen_n += 1;
    }
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
// hi * 2^32 + lo, in parts of at most 128 KiB, where the first byte is at
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
// The parts go through the read's slot's buffer, io64_fa_buf below (not
// malloc: a per-thread glibc arena kept it, up to 32 MiB at once,
// notes/memory.md; not the stack: 128 KiB overflows a small ulimit -s).
#define IO64_PART ((uint64_t)1 << 17)

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

// The read itself, into r->p, its parts through buf (IO64_PART bytes; no
// heap access: it may run on a helper thread). Sets err (and then nothing
// else is used), or code and n.
static void io64_fa_do(Io64Fa* r, char* buf) {
  int fd = r->fd;
  uint64_t off = r->off, span = r->span, col = r->col, lb = r->lb, lw = r->lw, want = r->want;
  char* p = r->p;
  uint64_t n = 0;
  u32 code = 0;
  uint64_t done = 0;
  while (done < span && code == 0) {
    // One part: up to 128 KiB of the span, read in full unless the file ends.
    uint64_t part = span - done < IO64_PART ? span - done : IO64_PART;
    uint64_t got = 0;
    while (got < part) {
      ssize_t k = pread(fd, buf + got, part - got, (off_t)(off + done + got));
      if (k < 0 && errno == EINTR) continue;
      if (k < 0) {
        r->err = (u32)errno;
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
// Each slot has its own part buffer, used by its read wherever it runs: a
// slot belongs to one read until Io.fa_wait joins it. A buffer's pages are
// committed only once a read touches them.
#define IO64_FA_MAX 128
typedef struct { int used, running; pthread_t th; Io64Fa r; } Io64FaSlot;
static Io64FaSlot io64_fa[IO64_FA_MAX];
static char io64_fa_buf[IO64_FA_MAX][IO64_PART];

static void* io64_fa_run(void* x) {
  Io64FaSlot* s = x;
  io64_fa_do(&s->r, io64_fa_buf[s - io64_fa]);
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
    else io64_fa_do(&s->r, io64_fa_buf[t]);
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

#ifdef CID(Io.out_set)
// The output: where and how the machine's bytes are written (B.Args.output's
// Sink; law output). Io.out_set records it before the loop; the -o file is
// opened at the first Io.out_write (or at Io.out_close for an empty output),
// after the first VCF piece was read, so a run that fails on its inputs
// leaves an existing file as it was. Opening: O_WRONLY | O_CREAT, mode 0666
// less the umask; the file, of any type, is compared (device and inode) with
// the files read so far (the .fai and the VCF: io64_seen) and the open FASTA,
// and, when stderr is a regular file, with stderr; it is refused if
// it is one of them (IO64_OUT_INPUT, before anything is changed). A regular
// file is then emptied (ftruncate); another (a FIFO, /dev/stdout) is not.
//
// Plain: each buffer is written at once, all of its bytes (short writes and
// EINTR retried). BGZF: the text is cut into blocks as bgzip 1.24 cuts text
// (htslib's bgzip.c, text mode): windows of IO64_BS bytes, each the bytes
// carried from the last cut and the next ones; while in the header (lines
// that start with '#' or '@' at the start of the text) a window is cut after
// the header's last line, else after its last LF, or kept whole if it has
// none; at the end, the last short window is cut the same way and the bytes
// after its cut are one more block. Each block is deflated (libdeflate, the
// level mapped as htslib maps it; level 0: a stored block as htslib writes
// it) into a gzip member with the BC extra field, by io64_out.nth compressor
// threads, and one writer thread writes the blocks in order. The compressed
// bytes depend only on the text and the level: they are those of bgzip -l L
// on the same text.
//
// Memory: a window inside a buffer is compressed where it lies; the windows
// that span two buffers are copied, and the bytes carried past a buffer's end
// are copied out (into win) before the buffer is freed. Io.out_write returns
// once every block of its buffer is written, and frees the buffer: the
// compressors work in parallel on one buffer at a time. (Keeping the buffer
// and compressing it while the machine computes its next step was 3% faster,
// but made Bend's heap grow by up to 250 MB on files of large records:
// notes/compress.md.) At most io64_out.limit blocks are taken by a
// compressor and not yet written (2 x the compressor threads, at least 4).
//
// Errors: the first one is kept (err): an errno of a write, open, truncate or
// close (cannot write), ENOMEM, or IO64_OUT_INPUT. After it nothing more is
// written to the output; Io.out_write and Io.out_close answer it. The
// end-of-file block is written by Io.out_close only for exit code 0 and no
// error: a BGZF file is complete exactly when the run succeeded (if closing a
// regular -o file then fails, the block is cut off again, through a duplicate
// of its descriptor kept from the open, unless that take-back fails itself:
// its truncate, or the duplicate's own close; a pipe cannot take it back). A run that stops otherwise (a driver error, exit 2; Bend's
// runtime) exits with the threads running: the blocks written so far stay,
// without the end-of-file block (the bytes carried for the next window are
// not written: the file is a prefix of the text).
#define IO64_OUT_INPUT 2001
#define IO64_OUT_NOLIB 2002
#define IO64_BS 65280
#define IO64_BMAX 65536
#define IO64_JOBS 65536

#ifdef IO64_IX
// The index writer (-W, phase J; law machine's comment in MACHINE.bend): the
// index built while the BGZF output is written, with htslib 1.24's own code.
// Each compressor thread parses the whole lines of its block with tbx_parse1
// (the parser tabix uses); the writer thread, in block order, knows each
// block's compressed address and pushes the records with hts_idx_push at the
// virtual offsets bgzf_tell would give a reader (tbx_index's loop). Lines
// across blocks (only those longer than a block) are joined and parsed by
// the writer. Io.out_index starts it. Built only with htslib and libdeflate
// (build.sh); without them Io.out_index answers 2003.
// Parts of htslib's tbx.c (MIT/Expat, Genome Research Ltd.) are restated
// here, as they are static there: the ##contig length scan
// (adjust_max_ref_len_vcf), the metadata (tbx_set_meta), the level formula
// without a length, the empty index, and the name-to-id order (get_tid).
//
// Memory: the writer indexes a block (idx_block) before it frees the block's
// copy (j->own) and before it counts the block written; a buffer of the
// machine is freed by Io.out_write only after io64_out_drain, that is after
// every block inside it was indexed; the bytes of a line that runs past a
// block are copied (io64_ix.carry) inside idx_block. The last short blocks
// (io64_out_tail at Io.out_close) are copies (own), indexed the same way.
//
// Data race: tbx_parse1 reads and writes a function-static (reported, tbx.c
// 1.24 line 218) when INFO/END is not past POS; it only gates a log line
// (and the log is off), but two compressor threads must not touch it at
// once. The static is reached only for a line whose INFO has END=; a line
// holding "END=" anywhere (a superset of htslib's test) is parsed under
// io64_ix_mu, every other line without a lock.
//
// Two end cases kept as tbx_index has them: a last line with no LF is pushed
// at the end-of-file block's address, offset 0 (bgzf_getline moves to the
// next block even without the LF), and hts_idx_finish gets that same
// address: where the 28-byte end-of-file block is written, not the offset
// after it.
#include <stddef.h>
#include <htslib/hts.h>
#include <htslib/tbx.h>
#include <htslib/hts_log.h>
#include <htslib/khash.h>
#include <htslib/kstring.h>

#if HTS_VERSION != 102400
#error "the index writer is written for htslib 1.24 (tbx_parse1, tbx_intv_t)"
#endif

// tbx_intv_t as tbx.c 1.24 defines it (not in a header).
typedef struct { int64_t beg, end; char *ss, *se; int tid; } tbx_intv_t;
_Static_assert(offsetof(tbx_intv_t, beg) == 0 && offsetof(tbx_intv_t, end) == 8 && offsetof(tbx_intv_t, ss) == 16
  && offsetof(tbx_intv_t, se) == 24 && offsetof(tbx_intv_t, tid) == 32 && sizeof(tbx_intv_t) == 40, "tbx_intv_t of htslib 1.24");
int tbx_parse1(const tbx_conf_t* conf, size_t len, char* line, tbx_intv_t* intv);
void hts_adjust_csi_settings(int64_t max_len_in, int* min_shift_, int* n_lvls_);
KHASH_MAP_INIT_STR(s2i, int)

// One whole line of a block: its end (after the LF), kind 0 a record (beg,
// end, CHROM at ss, sl bytes), 1 a meta line (clen: a ##contig length, or 0),
// 2 a line tbx_parse1 refuses.
typedef struct { uint32_t eo, ss, sl; int kind; int64_t beg, end, clen; } IdxRec;

static pthread_mutex_t io64_ix_mu = PTHREAD_MUTEX_INITIALIZER;

static struct {
  int on, fmt, min_shift, n_lvls;
  // bad: the index cannot be built (a line tabix refuses, a push refused, no
  // memory). Its own flag, never io64_out.err: it is acted on
  // only at Io.out_close with code 0. Set and read by the writer thread, read
  // by Io.out_close after the writer stopped.
  int bad;
  // path: the index (B.Args.index's path); other: the other format's name;
  // tmp: the temporary file, made at the open, NULL when there is none; htmp:
  // its name as htslib is given it ("./" before a relative path, so that no
  // scheme such as file: or http: is read).
  char *path, *other, *tmp, *htmp;
  hts_idx_t* idx; khash_t(s2i)* dict; uint64_t last_off; int64_t max_ref_len;
  kstring_t carry; int carrying; char* lname; size_t llen; int ltid;
  uint64_t addr;
  // The first bytes of the text (CSI: bcftools index reads the format from
  // the first 16, and refuses a file not starting with ##fileformat=VCF).
  unsigned char head[16]; size_t nhead;
} io64_ix;

// The name htslib is given for path: "./" before a relative path.
static char* idx_hname(const char* p) {
  size_t n = strlen(p);
  char* h = malloc(n + 3);
  if (h == NULL) return NULL;
  if (p[0] == '/') memcpy(h, p, n + 1);
  else { h[0] = '.'; h[1] = '/'; memcpy(h + 2, p, n + 1); }
  return h;
}

static void idx_rm_tmp(void) {
  if (io64_ix.tmp != NULL) unlink(io64_ix.tmp);
  free(io64_ix.tmp);
  io64_ix.tmp = NULL;
}

// A run that exits otherwise (a driver error) removes the temporary file
// too. A kill leaves it, and so does Bend's runtime, which stops with _exit
// (out of memory, a Nat past 2^48): atexit does not run.
static void idx_atexit(void) {
  if (io64_ix.tmp != NULL) unlink(io64_ix.tmp);
}

// The index errors (main.bend's out_fail turns them into messages): 2004
// cannot index, 2005 not a regular file, then for the index name n (.csi or
// .tbi): 2006/2007 cannot write n, 2008/2009 n is an input, 2010/2011 n is
// the -o file; 2012 an older <stem>.csi, which htslib reads before
// <path>.tbi.
#define IO64_IX_NOLIB 2003
#define IO64_IX_BAD 2004
#define IO64_IX_NOTREG 2005
#define IO64_IX_WRITE 2006
#define IO64_IX_INPUT 2008
#define IO64_IX_SELF 2010
#define IO64_IX_HIDDEN 2012

static u32 idx_code(u32 base, const char* n) {
  size_t l = strlen(n);
  return base + (l >= 4 && strcmp(n + l - 4, ".tbi") == 0);
}

static int64_t idx_clen(const char* s) {
  if (strncmp(s, "##contig", 8) != 0) return 0;
  const char* p = strstr(s + 8, "length");
  if (!p) return 0;
  for (p += 6; *p == ' ' || *p == '='; p++) {}
  return strtoll(p, NULL, 10);
}

// Parse the line s (NUL-terminated copy, CR stripped, l bytes) into r.
static void idx_parse(char* s, size_t l, IdxRec* r) {
  r->ss = r->sl = 0; r->beg = r->end = 0; r->clen = 0;
  if (s[0] == '#') { r->kind = 1; r->clen = idx_clen(s); return; }
  tbx_intv_t iv;
  int lock = memmem(s, l, "END=", 4) != NULL, k;
  if (lock) pthread_mutex_lock(&io64_ix_mu);
  k = tbx_parse1(&tbx_conf_vcf, l, s, &iv);
  if (lock) pthread_mutex_unlock(&io64_ix_mu);
  if (k != 0 || iv.beg < 0 || iv.end < 0) { r->kind = 2; return; }
  r->kind = 0; r->beg = iv.beg; r->end = iv.end; r->ss = (uint32_t)(iv.ss - s); r->sl = (uint32_t)(iv.se - iv.ss);
}

// In a compressor thread: the whole lines of block b (n bytes; cont: it
// starts inside a line) into *out (*nrec entries; NULL when there is none).
// Sets the first line start (*fs; n + 1 when no LF ends the line it starts
// inside) and the start of the last partial line (*ls). 0, or -1 for no
// memory (then the index is bad).
static int idx_scan(const unsigned char* b, size_t n, int cont, IdxRec** out, size_t* nrec, size_t* fs, size_t* ls, kstring_t* k) {
  size_t at = 0;
  *out = NULL; *nrec = 0;
  if (cont) {
    const unsigned char* e = memchr(b, '\n', n);
    if (e == NULL) { *fs = *ls = n + 1; return 0; }
    at = (size_t)(e - b) + 1;
  }
  *fs = at;
  size_t cap = 0; IdxRec* rs = NULL;
  for (;;) {
    const unsigned char* e = at < n ? memchr(b + at, '\n', n - at) : NULL;
    if (e == NULL) break;
    size_t le = (size_t)(e - b), l = le - at;
    k->l = 0;
    if (kputsn((const char*)b + at, l, k) < 0) { free(rs); return -1; }
    if (k->l > 0 && k->s[k->l - 1] == '\r') k->s[--k->l] = 0;
    if (*nrec == cap) {
      cap = cap == 0 ? 64 : 2 * cap;
      IdxRec* q = realloc(rs, cap * sizeof(IdxRec));
      if (q == NULL) { free(rs); return -1; }
      rs = q;
    }
    IdxRec* r = &rs[(*nrec)++];
    idx_parse(k->s, k->l, r);
    if (r->kind == 0) r->ss += (uint32_t)at;
    r->eo = (uint32_t)(le + 1);
    at = le + 1;
  }
  *ls = at;
  *out = rs;
  return 0;
}

// The first record: the levels (CSI: from the ##contig lengths, else from
// min_shift), then the index.
static void idx_first(void) {
  if (io64_ix.idx != NULL) return;
  if (io64_ix.fmt == HTS_FMT_CSI) {
    if (io64_ix.max_ref_len) hts_adjust_csi_settings(io64_ix.max_ref_len, &io64_ix.min_shift, &io64_ix.n_lvls);
    else io64_ix.n_lvls = io64_ix.min_shift < 10 ? 9 : io64_ix.min_shift < 25 ? 9 - (io64_ix.min_shift - 10) / 3 : 4;
  }
  io64_ix.idx = hts_idx_init(0, io64_ix.fmt, io64_ix.last_off, io64_ix.min_shift, io64_ix.n_lvls);
  if (io64_ix.idx == NULL) io64_ix.bad = 1;
}

// In the writer: one line (its CHROM name at nm, r->sl bytes), ending at
// voff v.
static void idx_take(const IdxRec* r, const char* nm, uint64_t v) {
  if (io64_ix.bad) return;
  if (r->kind == 1) {
    if (io64_ix.idx == NULL && io64_ix.fmt == HTS_FMT_CSI && io64_ix.max_ref_len < r->clen) io64_ix.max_ref_len = r->clen;
    io64_ix.last_off = v;
    return;
  }
  if (r->kind == 2) { io64_ix.bad = 1; return; }
  idx_first();
  if (io64_ix.bad) return;
  int tid;
  if (io64_ix.lname != NULL && io64_ix.llen == r->sl && memcmp(io64_ix.lname, nm, r->sl) == 0) {
    tid = io64_ix.ltid;
  } else {
    char* key = malloc(r->sl + 1);
    if (key == NULL) { io64_ix.bad = 1; return; }
    memcpy(key, nm, r->sl); key[r->sl] = 0;
    int absent; khint_t k = kh_put(s2i, io64_ix.dict, key, &absent);
    if (absent < 0) { free(key); io64_ix.bad = 1; return; }
    if (absent) kh_val(io64_ix.dict, k) = kh_size(io64_ix.dict) - 1; else free(key);
    tid = kh_val(io64_ix.dict, k);
    io64_ix.lname = (char*)kh_key(io64_ix.dict, k); io64_ix.llen = r->sl; io64_ix.ltid = tid;
  }
  if (hts_idx_push(io64_ix.idx, tid, r->beg, r->end, v, 1) < 0) io64_ix.bad = 1;
}

// The carried line, complete: parsed here.
static void idx_carry_done(uint64_t v) {
  kstring_t* c = &io64_ix.carry;
  io64_ix.carrying = 0;
  if (io64_ix.bad) return;
  if (c->s == NULL && kputs("", c) < 0) { io64_ix.bad = 1; return; }
  if (c->l > 0 && c->s[c->l - 1] == '\r') c->s[--c->l] = 0;
  IdxRec r; idx_parse(c->s, c->l, &r);
  idx_take(&r, c->s + r.ss, v);
  c->l = 0;
}

// In the writer, block b (n bytes) at compressed address a, size sz; its
// lines rs (nrec; scan: idx_scan's answer).
static void idx_block(const unsigned char* b, size_t n, uint64_t a, size_t sz, int scan, IdxRec* rs, size_t nrec, size_t fs, size_t ls) {
  if (scan != 0) io64_ix.bad = 1;
  if (io64_ix.nhead < 16) {
    size_t k = 16 - io64_ix.nhead < n ? 16 - io64_ix.nhead : n;
    memcpy(io64_ix.head + io64_ix.nhead, b, k);
    io64_ix.nhead += k;
    if (io64_ix.nhead == 16 && io64_ix.fmt == HTS_FMT_CSI && memcmp(io64_ix.head, "##fileformat=VCF", 16) != 0) io64_ix.bad = 1;
  }
  if (io64_ix.bad) return;
#define VO(o) ((o) == n ? (a + sz) << 16 : a << 16 | (o))
  if (io64_ix.carrying) {
    if (fs == n + 1) { if (kputsn((const char*)b, n, &io64_ix.carry) < 0) io64_ix.bad = 1; return; }
    if (kputsn((const char*)b, fs - 1, &io64_ix.carry) < 0) { io64_ix.bad = 1; return; }
    idx_carry_done(VO(fs));
  }
  for (size_t i = 0; i < nrec; i += 1) idx_take(&rs[i], (const char*)b + rs[i].ss, VO(rs[i].eo));
  if (ls < n) {
    io64_ix.carry.l = 0;
    if (kputsn((const char*)b + ls, n - ls, &io64_ix.carry) < 0) { io64_ix.bad = 1; return; }
    io64_ix.carrying = 1;
  }
#undef VO
}

// Io.out_index: the index of format fmt (1 CSI, 2 TBI) at path p (ending in
// .csi or .tbi), before the output opens. 0, or ENOMEM.
static u32 idx_begin(u32 fmt, char* p) {
  size_t n = strlen(p);
  if (n < 4) return EINVAL;
  io64_ix.path = p;
  io64_ix.other = strdup(p);
  if (io64_ix.other == NULL) return ENOMEM;
  int tbi = fmt == 2;
  memcpy(io64_ix.other + n - 4, tbi ? ".csi" : ".tbi", 4);
  hts_set_log_level(HTS_LOG_OFF);
  if (!tbi) io64_ix.fmt = HTS_FMT_CSI, io64_ix.min_shift = 14, io64_ix.n_lvls = (TBX_MAX_SHIFT - 14 + 2) / 3;
  else io64_ix.fmt = HTS_FMT_TBI, io64_ix.min_shift = 14, io64_ix.n_lvls = 5;
  io64_ix.dict = kh_init(s2i);
  if (io64_ix.dict == NULL) return ENOMEM;
  atexit(idx_atexit);
  io64_ix.on = 1;
  return 0;
}

// At Io.out_close with code 0, the last blocks written (the writer stopped),
// eof the end-of-file block's address: the carried line, then the index
// finished (an empty one as tbx_index makes it: the first settings, no
// level adjustment) with its metadata (tbx_set_meta's bytes). 0, or -1
// (cannot index; CSI: also a text shorter than 16 bytes).
static int idx_finish(uint64_t eof) {
  if (io64_ix.carrying) idx_carry_done(eof << 16);
  if (io64_ix.fmt == HTS_FMT_CSI && io64_ix.nhead < 16) io64_ix.bad = 1;
  if (io64_ix.bad) return -1;
  if (io64_ix.idx == NULL) io64_ix.idx = hts_idx_init(0, io64_ix.fmt, io64_ix.last_off, io64_ix.min_shift, io64_ix.n_lvls);
  if (io64_ix.idx == NULL) return -1;
  if (hts_idx_finish(io64_ix.idx, eof << 16) != 0) return -1;
  khash_t(s2i)* d = io64_ix.dict;
  int nn = kh_size(d), l = 0;
  char** name = calloc(nn + 1, sizeof(char*));
  if (name == NULL) return -1;
  for (khint_t k = kh_begin(d); k != kh_end(d); ++k) if (kh_exist(d, k)) { name[kh_val(d, k)] = (char*)kh_key(d, k); l += strlen(kh_key(d, k)) + 1; }
  uint8_t* meta = malloc(28 + (size_t)l);
  if (meta == NULL) { free(name); return -1; }
  uint32_t x[7];
  memcpy(x, &tbx_conf_vcf, 24); x[6] = (uint32_t)l;
  if (ed_is_big()) for (int i = 0; i < 7; ++i) x[i] = ed_swap_4(x[i]);
  memcpy(meta, x, 28);
  for (int i = 0, o = 28; i < nn; i++) { int w = strlen(name[i]) + 1; memcpy(meta + o, name[i], w); o += w; }
  free(name);
  if (hts_idx_set_meta(io64_ix.idx, 28 + l, meta, 0) != 0) { free(meta); return -1; }
  return 0;
}

// After the end-of-file block is written and the -o file closed: the index
// saved to the temporary file and renamed to path. 0, or -1 (cannot write
// <path>; the temporary file removed).
static int idx_save(void) {
  if (hts_idx_save_as(io64_ix.idx, io64_ix.htmp, io64_ix.htmp, io64_ix.fmt) != 0 || rename(io64_ix.tmp, io64_ix.path) != 0) {
    idx_rm_tmp();
    return -1;
  }
  free(io64_ix.tmp);
  io64_ix.tmp = NULL;
  return 0;
}
#endif

// A block to compress: the text (src, inside the buffer being written, or
// own, a copy), its length, and once compressed the BGZF block (out, outn).
typedef struct {
  const unsigned char* src; unsigned char* own; size_t n;
  unsigned char* out; size_t outn; int done;
#ifdef IO64_IX
  int cont, scan; IdxRec* rec; size_t nrec, fs, ls;
#endif
} Io64Job;

static struct {
  int file, z, level, opened, started; unsigned nth; char* path; int fd;
  dev_t fa_dev; ino_t fa_ino; int fa_ok;
  u32 err;
  // The text not cut yet: stream bytes [ws, ps) in win, the stream offset
  // of the next window (cs), bgzip's header flags.
  // wend: the end of the last full window (no byte after it: the carried
  // bytes are written at the end as one block, as bgzip's last bgzf_write).
  unsigned char* win; uint64_t ws, cs, ps, wend; int in_header, long_line, reg;
  // A duplicate of a regular -o file's descriptor, kept from its open until
  // the close (for the take-back: -1 when there is none).
  int dupfd;
  // The jobs: appended up to tail, taken by a compressor up to take,
  // written up to wr (wr <= take <= tail, in a ring of IO64_JOBS).
  Io64Job* job; uint64_t tail, take, wr, limit;
  pthread_t th[128], wth; unsigned nrun; int wrun, stop;
  pthread_mutex_t mu; pthread_cond_t cv;
} io64_out = {.fd = -1, .dupfd = -1, .mu = PTHREAD_MUTEX_INITIALIZER, .cv = PTHREAD_COND_INITIALIZER};

// All n bytes to fd; 0, or the errno (EIO for a write of 0 bytes).
static u32 io64_wall(int fd, const unsigned char* p, size_t n) {
  for (size_t at = 0; at < n;) {
    ssize_t k = write(fd, p + at, n - at > INT32_MAX ? INT32_MAX : n - at);
    if (k < 0 && errno == EINTR) continue;
    if (k <= 0) return k == 0 ? EIO : (u32)errno;
    at += (size_t)k;
  }
  return 0;
}

#ifdef FB_LIBDEFLATE
static void io64_put16(unsigned char* p, unsigned v) { p[0] = v & 255; p[1] = (v >> 8) & 255; }
static void io64_put32(unsigned char* p, uint32_t v) { for (int i = 0; i < 4; i += 1) p[i] = (v >> (8 * i)) & 255; }

// One BGZF block of the n <= IO64_BS bytes at s into d (IO64_BMAX bytes);
// its length. c is NULL for level 0 (a stored block, as htslib writes it).
static size_t io64_bgzf_block(struct libdeflate_compressor* c, const unsigned char* s, size_t n, unsigned char* d) {
  static const unsigned char h[16] = {31, 139, 8, 4, 0, 0, 0, 0, 0, 255, 6, 0, 66, 67, 2, 0};
  size_t k = 0;
  if (c != NULL) k = libdeflate_deflate_compress(c, s, n, d + 18, IO64_BMAX - 26);
  if (k == 0) {
    // Level 0, or (never for IO64_BS bytes) a deflate that does not fit.
    d[18] = 1;
    io64_put16(d + 19, (unsigned)n);
    io64_put16(d + 21, (unsigned)~n & 0xffff);
    memcpy(d + 23, s, n);
    k = n + 5;
  }
  memcpy(d, h, 16);
  io64_put16(d + 16, (unsigned)(k + 25));
  io64_put32(d + 18 + k, libdeflate_crc32(0, s, n));
  io64_put32(d + 22 + k, (uint32_t)n);
  return k + 26;
}

static void* io64_zrun(void* x) {
  struct libdeflate_compressor* c = x;
#ifdef IO64_IX
  kstring_t ks = {0, 0, NULL};
#endif
  pthread_mutex_lock(&io64_out.mu);
  for (;;) {
    while (!io64_out.stop && !(io64_out.take < io64_out.tail && io64_out.take - io64_out.wr < io64_out.limit)) {
      pthread_cond_wait(&io64_out.cv, &io64_out.mu);
    }
    if (io64_out.stop) break;
    Io64Job* j = &io64_out.job[io64_out.take % IO64_JOBS];
    io64_out.take += 1;
    pthread_mutex_unlock(&io64_out.mu);
    unsigned char* out = malloc(IO64_BMAX);
    size_t on = out != NULL ? io64_bgzf_block(c, j->src != NULL ? j->src : j->own, j->n, out) : 0;
#ifdef IO64_IX
    if (io64_ix.on) j->scan = idx_scan(j->src != NULL ? j->src : j->own, j->n, j->cont, &j->rec, &j->nrec, &j->fs, &j->ls, &ks);
#endif
    pthread_mutex_lock(&io64_out.mu);
    j->out = out;
    j->outn = on;
    j->done = 1;
    pthread_cond_broadcast(&io64_out.cv);
  }
  pthread_mutex_unlock(&io64_out.mu);
#ifdef IO64_IX
  free(ks.s);
#endif
  if (c != NULL) libdeflate_free_compressor(c);
  return NULL;
}

// The writer: the blocks in order; after the first error it writes nothing
// more (and still takes the blocks, so that no one waits).
static void* io64_wrun(void* x) {
  pthread_mutex_lock(&io64_out.mu);
  for (;;) {
    Io64Job* j = &io64_out.job[io64_out.wr % IO64_JOBS];
    while (!io64_out.stop && !(io64_out.wr < io64_out.take && j->done)) pthread_cond_wait(&io64_out.cv, &io64_out.mu);
    if (!(io64_out.wr < io64_out.take && j->done)) break;
    int skip = io64_out.err != 0;
    pthread_mutex_unlock(&io64_out.mu);
    u32 e = 0;
    if (j->out == NULL) e = ENOMEM;
    else if (!skip) e = io64_wall(io64_out.fd, j->out, j->outn);
#ifdef IO64_IX
    // Indexed before the frees below.
    if (io64_ix.on && !skip && e == 0) {
      idx_block(j->src != NULL ? j->src : j->own, j->n, io64_ix.addr, j->outn, j->scan, j->rec, j->nrec, j->fs, j->ls);
      io64_ix.addr += j->outn;
    }
    free(j->rec);
#endif
    free(j->out);
    free(j->own);
    pthread_mutex_lock(&io64_out.mu);
    if (e != 0 && io64_out.err == 0) io64_out.err = e;
    *j = (Io64Job){0};
    io64_out.wr += 1;
    pthread_cond_broadcast(&io64_out.cv);
  }
  pthread_mutex_unlock(&io64_out.mu);
  return NULL;
}

// Start the compressors and the writer; 0 or ENOMEM.
static u32 io64_out_start(void) {
  static const int lvl[10] = {0, 1, 2, 3, 5, 6, 7, 8, 10, 12};
  io64_out.win = malloc(IO64_BS);
  io64_out.job = calloc(IO64_JOBS, sizeof(Io64Job));
  if (io64_out.win == NULL || io64_out.job == NULL) return ENOMEM;
  io64_out.in_header = 1;
  io64_out.limit = 2 * (uint64_t)io64_out.nth < 4 ? 4 : 2 * (uint64_t)io64_out.nth;
  for (unsigned i = 0; i < io64_out.nth; i += 1) {
    struct libdeflate_compressor* c = NULL;
    if (io64_out.level != 0) {
      c = libdeflate_alloc_compressor(lvl[io64_out.level]);
      if (c == NULL) return ENOMEM;
    }
    if (pthread_create(&io64_out.th[i], NULL, io64_zrun, c) != 0) {
      if (c != NULL) libdeflate_free_compressor(c);
      break;
    }
    io64_out.nrun += 1;
  }
  if (io64_out.nrun == 0) return ENOMEM;
  if (pthread_create(&io64_out.wth, NULL, io64_wrun, NULL) != 0) return ENOMEM;
  io64_out.wrun = 1;
  io64_out.started = 1;
  return 0;
}

// Queue a block: the n bytes at src (kept by the caller until written) or,
// with src NULL, a copy of the n bytes at cp.
static u32 io64_out_job(const unsigned char* src, const unsigned char* cp, size_t n) {
  unsigned char* own = NULL;
  if (src == NULL) {
    own = malloc(n);
    if (own == NULL) return ENOMEM;
    memcpy(own, cp, n);
  }
  pthread_mutex_lock(&io64_out.mu);
  while (io64_out.tail - io64_out.wr >= IO64_JOBS) pthread_cond_wait(&io64_out.cv, &io64_out.mu);
  io64_out.job[io64_out.tail % IO64_JOBS] = (Io64Job){src, own, n, NULL, 0, 0};
#ifdef IO64_IX
  static int nl = 1;
  io64_out.job[io64_out.tail % IO64_JOBS].cont = !nl;
  if (n > 0) nl = (src != NULL ? src : own)[n - 1] == '\n';
#endif
  io64_out.tail += 1;
  pthread_cond_broadcast(&io64_out.cv);
  pthread_mutex_unlock(&io64_out.mu);
  return 0;
}

// Wait until every queued block is written.
static void io64_out_drain(void) {
  pthread_mutex_lock(&io64_out.mu);
  while (io64_out.wr < io64_out.tail) pthread_cond_wait(&io64_out.cv, &io64_out.mu);
  pthread_mutex_unlock(&io64_out.mu);
}

// Where bgzip 1.24 cuts the window w of c2 bytes (text mode): the length of
// its block.
static size_t io64_cut(const unsigned char* w, size_t c2) {
  if (io64_out.in_header && (io64_out.long_line || w[0] == '@' || w[0] == '#')) {
    size_t last = 0, n = 0;
    while (n < c2) {
      if (w[n++] != '\n') continue;
      last = n;
      if (n < c2 && !(w[n] == '@' || w[n] == '#')) {
        io64_out.in_header = 0;
        break;
      }
    }
    if (last == 0) {
      io64_out.long_line = 1;
      return c2;
    }
    io64_out.long_line = 0;
    return last;
  }
  for (size_t n = c2; n > 0; n -= 1) {
    if (w[n - 1] == '\n') return n;
  }
  return c2;
}

// The full windows of the text so far: the bytes [ws, ps) in win, then the
// n bytes at p (stream offsets ps on); queues their blocks and carries the
// rest into win. The blocks inside p point into it.
static u32 io64_out_text(const unsigned char* p, uint64_t n) {
  u32 r = 0;
  while (r == 0 && io64_out.ps + n - io64_out.cs >= IO64_BS) {
    uint64_t cs = io64_out.cs;
    size_t c;
    if (cs < io64_out.ps) {
      // A window across the carried bytes and p: copied.
      unsigned char* w = malloc(IO64_BS);
      if (w == NULL) return ENOMEM;
      size_t l = (size_t)(io64_out.ps - cs);
      memcpy(w, io64_out.win + (cs - io64_out.ws), l);
      memcpy(w + l, p, IO64_BS - l);
      c = io64_cut(w, IO64_BS);
      r = io64_out_job(NULL, w, c);
      free(w);
    } else {
      const unsigned char* w = p + (cs - io64_out.ps);
      c = io64_cut(w, IO64_BS);
      r = io64_out_job(w, NULL, c);
    }
    io64_out.cs = cs + c;
    io64_out.wend = cs + IO64_BS;
  }
  if (r != 0) return r;
  // Carry [cs, ps + n) into win (fewer than IO64_BS bytes).
  uint64_t cs = io64_out.cs;
  if (cs < io64_out.ps) {
    size_t l = (size_t)(io64_out.ps - cs);
    memmove(io64_out.win, io64_out.win + (cs - io64_out.ws), l);
    memcpy(io64_out.win + l, p, (size_t)n);
  } else {
    memcpy(io64_out.win, p + (cs - io64_out.ps), (size_t)(io64_out.ps + n - cs));
  }
  io64_out.ws = cs;
  io64_out.ps += n;
  return 0;
}

// The end of the text, as bgzip ends it: the last short window, cut, and the
// bytes after its cut as one more block; or, when no byte came after the last
// full window (bgzip's next read gives nothing), the bytes carried from it as
// one block, uncut.
static u32 io64_out_tail(void) {
  size_t l = (size_t)(io64_out.ps - io64_out.cs);
  if (l == 0) return 0;
  const unsigned char* w = io64_out.win + (io64_out.cs - io64_out.ws);
  size_t c = io64_out.ps == io64_out.wend ? l : io64_cut(w, l);
  u32 r = io64_out_job(NULL, w, c);
  if (r == 0 && c < l) r = io64_out_job(NULL, w + c, l - c);
  io64_out.cs = io64_out.ps;
  return r;
}

// Stop the compressors and the writer (every block written first).
static void io64_out_stop(void) {
  if (!io64_out.started) return;
  io64_out_drain();
  pthread_mutex_lock(&io64_out.mu);
  io64_out.stop = 1;
  pthread_cond_broadcast(&io64_out.cv);
  pthread_mutex_unlock(&io64_out.mu);
  for (unsigned i = 0; i < io64_out.nrun; i += 1) pthread_join(io64_out.th[i], NULL);
  if (io64_out.wrun) pthread_join(io64_out.wth, NULL);
  io64_out.started = 0;
}
#endif

static u32 io64_out_get_err(void) {
  pthread_mutex_lock(&io64_out.mu);
  u32 e = io64_out.err;
  pthread_mutex_unlock(&io64_out.mu);
  return e;
}

static void io64_out_err(u32 e) {
  pthread_mutex_lock(&io64_out.mu);
  if (io64_out.err == 0) io64_out.err = e;
  pthread_mutex_unlock(&io64_out.mu);
}

static int io64_same(const struct stat* a, dev_t dev, ino_t ino) {
  return a->st_dev == dev && a->st_ino == ino;
}

#ifdef IO64_IX
// A file st is the output o, the FASTA, a file read so far, or stderr's
// regular file (step 3 of the open).
static int idx_alias(const struct stat* st, const struct stat* o) {
  struct stat er;
  int same = io64_same(st, o->st_dev, o->st_ino) || (io64_out.fa_ok && io64_same(st, io64_out.fa_dev, io64_out.fa_ino));
  for (int i = 0; i < io64_seen_n; i += 1) same = same || io64_same(st, io64_seen[i].dev, io64_seen[i].ino);
  if (fstat(2, &er) == 0 && S_ISREG(er.st_mode)) same = same || io64_same(st, er.st_dev, er.st_ino);
  return same;
}

// Step 3, for one index name p: refused (nothing changed) if it is a
// directory (itself, or through a symlink), cannot be looked at, or is
// (itself, or the file a symlink there names) the output, an input or
// stderr's file. 0 or the error.
static u32 idx_check_name(const char* p, const struct stat* o) {
  struct stat l, s;
  if (lstat(p, &l) != 0) return errno == ENOENT ? 0 : idx_code(IO64_IX_WRITE, p);
  if (S_ISDIR(l.st_mode) || (stat(p, &s) == 0 && S_ISDIR(s.st_mode))) return idx_code(IO64_IX_WRITE, p);
  if (idx_alias(&l, o) || (stat(p, &s) == 0 && idx_alias(&s, o))) {
    if (io64_same(&l, o->st_dev, o->st_ino) || (stat(p, &s) == 0 && io64_same(&s, o->st_dev, o->st_ino))) return idx_code(IO64_IX_SELF, p);
    return idx_code(IO64_IX_INPUT, p);
  }
  return 0;
}

// Step 3, the names htslib 1.24 reads before ours (hts_idx_check_local, for
// the -o path f: f.csi, then f up to its last '.' after the first byte with
// .csi, then the same two with .tbi; the first that stat finds is read).
// <path>.csi is first, so nothing comes before a CSI; before a TBI, f.csi
// (step 5 moves it aside) and that <stem>.csi, which is not ours to remove
// (it may index another file, f without its extension): refused while stat
// finds it. 0 or the error.
static u32 idx_check_hidden(void) {
  if (io64_ix.fmt != HTS_FMT_TBI) return 0;
  size_t n = strlen(io64_ix.path) - 4, i;
  if (n < 2) return 0;
  for (i = n - 1; i > 0 && io64_ix.path[i] != '.'; i -= 1) {}
  if (i == 0) return 0;
  char* c = malloc(i + 5);
  if (c == NULL) return ENOMEM;
  memcpy(c, io64_ix.path, i); memcpy(c + i, ".csi", 5);
  struct stat s;
  int hid = stat(c, &s) == 0;
  free(c);
  return hid ? IO64_IX_HIDDEN : 0;
}

// Steps 3 and 4 (after the open and the checks of the -o file st, before it
// is emptied): the index names checked, the temporary file made (O_EXCL,
// mode 0666 less the umask; <path>.tmp, then .tmp1 ... on EEXIST). 0 or the
// error, nothing changed.
static u32 idx_open(const struct stat* st) {
  u32 r = idx_check_name(io64_ix.path, st);
  if (r == 0) r = idx_check_name(io64_ix.other, st);
  if (r == 0) r = idx_check_hidden();
  if (r != 0) return r;
  size_t n = strlen(io64_ix.path);
  char* t = malloc(n + 16);
  if (t == NULL) return ENOMEM;
  for (int k = 0;; k += 1) {
    if (k == 0) sprintf(t, "%s.tmp", io64_ix.path); else sprintf(t, "%s.tmp%d", io64_ix.path, k);
    int fd = open(t, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0666);
    if (fd >= 0) { close(fd); break; }
    if (errno != EEXIST || k == 999) { free(t); return idx_code(IO64_IX_WRITE, io64_ix.path); }
  }
  io64_ix.tmp = t;
  io64_ix.htmp = idx_hname(t);
  if (io64_ix.htmp == NULL) { idx_rm_tmp(); return ENOMEM; }
  return 0;
}

// Step 5 (before the -o file is emptied): each old index that
// exists is renamed aside, to <name>.old (.old1, .old2, ... when that name
// exists: renameat2 with RENAME_NOREPLACE, so nothing is ever replaced). If
// one cannot be moved, the one moved already is moved back, the temporary
// file removed, and the run refused ("cannot write <name>"): nothing changed,
// unless that move back fails too, when that index stays as <name>.old
// beside the unchanged -o file. Where renameat2 cannot do
// RENAME_NOREPLACE (EINVAL, ENOSYS, EOPNOTSUPP: NFS, some FUSE file systems,
// old kernels), a move is link(from, to), which never replaces a file
// either, then unlink(from); if that unlink fails, the link is removed and
// the move fails with nothing changed. Where link is not
// supported either, the move fails: no check-then-rename, which could
// replace a file. Linux only (renameat2; macOS would use renamex_np).
#ifndef RENAME_NOREPLACE
#define RENAME_NOREPLACE 1
#endif
extern int renameat2(int, const char*, int, const char*, unsigned int);
static char* io64_ix_aside[2];

static int idx_move(const char* from, const char* to) {
  if (renameat2(AT_FDCWD, from, AT_FDCWD, to, RENAME_NOREPLACE) == 0) return 0;
  if (errno != EINVAL && errno != ENOSYS && errno != EOPNOTSUPP) return -1;
  if (link(from, to) != 0) return -1;
  if (unlink(from) != 0) {
    int e = errno;
    unlink(to);
    errno = e;
    return -1;
  }
  return 0;
}

// Moves name aside; 0 (also when there is no such name), or -1.
static int idx_aside1(const char* name, char** got) {
  *got = NULL;
  size_t n = strlen(name);
  char* t = malloc(n + 16);
  if (t == NULL) return -1;
  for (int k = 0; k < 1000; k += 1) {
    if (k == 0) sprintf(t, "%s.old", name); else sprintf(t, "%s.old%d", name, k);
    if (idx_move(name, t) == 0) { *got = t; return 0; }
    if (errno == ENOENT) { free(t); return 0; }
    if (errno != EEXIST) break;
  }
  free(t);
  return -1;
}

// Step 6's undo (and step 5's, for the first index): the old indexes moved
// back. If a move back fails, that index stays as <name>.old, the -o file
// unchanged; the message is the step's own.
static void idx_unstage(void) {
  if (io64_ix_aside[0] != NULL) idx_move(io64_ix_aside[0], io64_ix.path);
  if (io64_ix_aside[1] != NULL) idx_move(io64_ix_aside[1], io64_ix.other);
}

// 0, or the error (the temporary file removed).
static u32 idx_stage(void) {
  if (idx_aside1(io64_ix.path, &io64_ix_aside[0]) != 0) { idx_rm_tmp(); return idx_code(IO64_IX_WRITE, io64_ix.path); }
  if (idx_aside1(io64_ix.other, &io64_ix_aside[1]) != 0) {
    idx_unstage();
    idx_rm_tmp();
    return idx_code(IO64_IX_WRITE, io64_ix.other);
  }
  return 0;
}

// Step 7 (after the -o file was emptied): the moved files
// removed. A failure leaves <name>.old, a file htslib never reads; the run
// goes on.
static void idx_drop_old(void) {
  for (int i = 0; i < 2; i += 1) {
    if (io64_ix_aside[i] != NULL && unlink(io64_ix_aside[i]) != 0) {}
    free(io64_ix_aside[i]);
    io64_ix_aside[i] = NULL;
  }
}

#endif

// Open the output (once): stdout, or the -o file; 0 or the error. SIGXFSZ is
// ignored from here on, so that a write past a file size limit fails (EFBIG:
// cannot write) instead of killing the run.
static u32 io64_out_open(void) {
  if (io64_out.opened) return 0;
  io64_out.opened = 1;
  signal(SIGXFSZ, SIG_IGN);
  if (!io64_out.file) {
    io64_out.fd = 1;
  } else {
    // With -W: (1) opened without emptying it, O_NONBLOCK so that a FIFO
    // with no reader fails (ENXIO) instead of blocking; (2) a regular file,
    // not an input; (3) the index names checked; (4) the temporary file made;
    // (5) the old indexes renamed aside; (6) the file emptied (the old
    // indexes moved back if that fails); (7) the moved old indexes removed. A
    // failure in (1) to (6) leaves the old file and both old indexes (a new
    // -o file stays, empty), except an index whose move back fails, which
    // stays as <name>.old.
    int ix = 0;
#ifdef IO64_IX
    ix = io64_ix.on;
#endif
    int fd = open(io64_out.path, O_WRONLY | O_CREAT | O_CLOEXEC | (ix ? O_NONBLOCK : 0), 0666);
#ifdef IO64_IX
    if (fd < 0 && ix && errno == ENXIO) return IO64_IX_NOTREG;
#endif
    if (fd < 0) return (u32)errno;
    struct stat st, er;
    if (fstat(fd, &st) != 0) {
      u32 e = (u32)errno;
      close(fd);
      return e;
    }
    // An input of any type (a FIFO or a pipe too: writing into it would feed
    // the VCF its own output, and keep its reader from ever seeing the end);
    // stderr when it is a regular file (emptying it would wipe the messages;
    // output and messages on one pipe or terminal is what the user asked for,
    // as with -o /dev/stdout 2>&1).
    int same = io64_out.fa_ok && io64_same(&st, io64_out.fa_dev, io64_out.fa_ino);
    for (int i = 0; i < io64_seen_n; i += 1) same = same || io64_same(&st, io64_seen[i].dev, io64_seen[i].ino);
    if (fstat(2, &er) == 0 && S_ISREG(er.st_mode)) same = same || io64_same(&st, er.st_dev, er.st_ino);
    if (same) {
      close(fd);
      return IO64_OUT_INPUT;
    }
    io64_out.reg = S_ISREG(st.st_mode);
#ifdef IO64_IX
    if (ix) {
      if (!io64_out.reg) {
        close(fd);
        return IO64_IX_NOTREG;
      }
      int fl = fcntl(fd, F_GETFL);
      u32 e = fl < 0 || fcntl(fd, F_SETFL, fl & ~O_NONBLOCK) != 0 ? (u32)errno : 0;
      if (e == 0) e = idx_open(&st);
      if (e == 0) e = idx_stage();
      if (e != 0) {
        close(fd);
        return e;
      }
    }
#endif
    if (io64_out.reg) {
      // The duplicate for the take-back (Io.out_close), then the file
      // emptied.
      io64_out.dupfd = fcntl(fd, F_DUPFD_CLOEXEC, 3);
      if (io64_out.dupfd < 0 || ftruncate(fd, 0) != 0) {
        u32 e = (u32)errno;
        if (io64_out.dupfd >= 0) close(io64_out.dupfd);
        io64_out.dupfd = -1;
        close(fd);
#ifdef IO64_IX
        if (ix) idx_unstage();
        idx_rm_tmp();
#endif
        return e;
      }
    }
#ifdef IO64_IX
    if (ix) idx_drop_old();
#endif
    io64_out.fd = fd;
  }
#ifdef FB_LIBDEFLATE
  if (io64_out.z) return io64_out_start();
#endif
  return 0;
}

// Io.out_set(fa, path, file, z, level, n): the output (the -o path's bytes
// when file is 1, else stdout), BGZF when z is 1, at level (0 to 9, htslib's
// scale), with n compressor threads (0: 16; at most 128); fa is the open
// FASTA. Answers (fa, 0), or (fa, IO64_OUT_NOLIB) for BGZF in a build
// without libdeflate.
Term io_out_set_run(Env e, Term* f, IoWork* w) {
  int fd = io_hand_v(f[0]);
  uint64_t len;
  io64_out.path = io_cbuf(e, f[1], &len, CID(Con));
  io64_out.file = (u32)f[2] == 1;
  io64_out.z = (u32)f[3] == 1;
  u32 lv = (u32)f[4], n = (u32)f[5];
  io64_out.level = lv > 9 ? 9 : (int)lv;
  io64_out.nth = n == 0 ? 16 : n > 128 ? 128 : n;
  struct stat st;
  if (fstat(fd, &st) == 0) {
    io64_out.fa_ok = 1;
    io64_out.fa_dev = st.st_dev;
    io64_out.fa_ino = st.st_ino;
  }
  u32 r = 0;
#ifndef FB_LIBDEFLATE
  if (io64_out.z) r = IO64_OUT_NOLIB;
#endif
  if (io64_out.path == NULL || memchr(io64_out.path, 0, len) != NULL) r = EINVAL;
  return io_tup(e, io_hand(fd), (Term)r);
}

// Io.out_write(n, block): the block's first n bytes to the output (n at most
// its size; the block is freed, now or at the next call). Answers 0 or the
// first error; EINVAL, writing nothing, if the block is not a packed buffer
// of at most 2^31 bytes (depth 29).
Term io_out_write_run(Env e, Term* f, IoWork* w) {
  uint64_t n = (u32)f[0];
  Term a = f[1];
  if (term_tag(a) != TAG_BUF || blk_cls(a) > 29) return (Term)EINVAL;
  uint64_t cap = (uint64_t)4 << blk_cls(a);
  if (n > cap) n = cap;
  const unsigned char* p = (const unsigned char*)(e.mem + blk_loc(e.mem, a));
  u32 r = io64_out_get_err();
  if (r == 0) r = io64_out_open();
#ifdef FB_LIBDEFLATE
  if (r == 0 && io64_out.z) {
    // This buffer's windows, compressed and written before it is freed.
    r = io64_out_text(p, n);
    if (r != 0) io64_out_err(r);
    io64_out_drain();
    r = io64_out_get_err();
  } else
#endif
  if (r == 0) r = io64_wall(io64_out.fd, p, (size_t)n);
  if (r != 0) io64_out_err(r);
  blk_free(e, a);
  return (Term)r;
}

// Io.out_close(c): the end of the output, for a run ending with exit code c:
// opens it if nothing was written (an empty output), writes the last blocks,
// and for BGZF the end-of-file block only when c is 0 and nothing failed;
// closes the -o file. Answers 0 or the first error.
Term io_out_close_run(Env e, Term* f, IoWork* w) {
  u32 c = (u32)f[0];
  off_t at = -1;
  u32 r = io64_out_get_err();
  if (r == 0) r = io64_out_open();
#ifdef FB_LIBDEFLATE
  if (io64_out.started) {
    if (r == 0) r = io64_out_tail();
    if (r != 0) io64_out_err(r);
    io64_out_stop();
    r = io64_out_get_err();
    static const unsigned char eof[28] = {31, 139, 8, 4, 0, 0, 0, 0, 0, 255, 6, 0, 66, 67, 2, 0, 27, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0};
#ifdef IO64_IX
    // An index failure counts only for code 0, after all of the machine's
    // messages: no end-of-file block, "cannot index" (2004).
    if (io64_ix.on && r == 0 && c == 0 && idx_finish(io64_ix.addr) != 0) r = IO64_IX_BAD;
#endif
    if (r == 0 && c == 0) {
      at = io64_out.file && io64_out.reg ? lseek(io64_out.fd, 0, SEEK_CUR) : -1;
      r = io64_wall(io64_out.fd, eof, 28);
    }
  }
#endif
  if (io64_out.file && io64_out.fd >= 0) {
    if (close(io64_out.fd) != 0 && r == 0) {
      r = (u32)errno;
      // The end-of-file block written, then close failed: take the block
      // back through the duplicate (the same open file, whatever its path
      // names now), so that the file does not look complete. A regular file
      // always has the duplicate; one written to a pipe or FIFO cannot be
      // taken back. If this truncate fails, the error stays reported and
      // the file keeps the block.
      if (at >= 0 && io64_out.dupfd >= 0 && ftruncate(io64_out.dupfd, at) != 0) {}
    }
    // The duplicate's own close, checked too: its failure is reported
    // (cannot write); with no descriptor left, the end-of-file block (if
    // written) then stays.
#ifdef IO64_IX
    // The index, after the end-of-file block and the close: saved to the
    // temporary file, renamed. If that fails, the block is taken back
    // (cannot write <path>.csi or .tbi).
    if (io64_ix.on && r == 0 && c == 0 && idx_save() != 0) {
      if (at >= 0 && io64_out.dupfd >= 0 && ftruncate(io64_out.dupfd, at) != 0) {}
      r = idx_code(IO64_IX_WRITE, io64_ix.path);
    }
    // The duplicate's close failing after the rename: the index removed, the
    // error phase H's (cannot write <path>).
    if (io64_ix.on && io64_out.dupfd >= 0) {
      int ok = r == 0;
      if (close(io64_out.dupfd) != 0 && ok) {
        r = (u32)errno;
        if (c == 0) unlink(io64_ix.path);
      }
      io64_out.dupfd = -1;
    }
#endif
    if (io64_out.dupfd >= 0 && close(io64_out.dupfd) != 0 && r == 0) r = (u32)errno;
    io64_out.dupfd = -1;
    io64_out.fd = -1;
  }
#ifdef IO64_IX
  // No index for any other end (the temporary file removed).
  if (io64_ix.on && io64_ix.tmp != NULL) idx_rm_tmp();
#endif
  if (r != 0) io64_out_err(r);
  return (Term)r;
}

// Io.out_index(fmt, path): -W, before the first step (B.Args.index's Idx:
// fmt 1 CSI, 2 TBI; path the index's bytes). Answers 0, ENOMEM, EINVAL (a
// path with a NUL byte), or IO64_IX_NOLIB (2003) in a build without htslib
// and libdeflate.
Term io_out_index_run(Env e, Term* f, IoWork* w) {
#ifdef IO64_IX
  u32 fmt = (u32)f[0];
  uint64_t len;
  char* p = io_cbuf(e, f[1], &len, CID(Con));
  if (p == NULL || memchr(p, 0, len) != NULL) return (Term)EINVAL;
  return (Term)idx_begin(fmt, p);
#else
  return (Term)2003;
#endif
}

static void __attribute__((constructor)) io_out_use(void) {
  io_eff(CID(Io.out_index), io_out_index_run);
  io_eff(CID(Io.out_set), io_out_set_run);
  io_eff(CID(Io.out_write), io_out_write_run);
  io_eff(CID(Io.out_close), io_out_close_run);
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

// x ends with e (lower case), ignoring ASCII case (B.Args.ends_ci).
static int io64_ends_ci(const char* x, const char* e) {
  size_t a = strlen(x), b = strlen(e);
  if (a < b) return 0;
  for (size_t i = 0; i < b; i += 1) {
    char c = x[a - b + i];
    if (c >= 'A' && c <= 'Z') c = (char)(c + 32);
    if (c != e[i]) return 0;
  }
  return 1;
}

// A value of -O: v, z, or z and one digit (B.Args.otype).
static int io64_otype(const char* x) {
  return !strcmp(x, "v") || !strcmp(x, "z") || (x[0] == 'z' && x[1] >= '0' && x[1] <= '9' && x[2] == 0);
}

// B.Args.threads of the program's words w[0 .. n): N, or 0 for none (no
// --threads, or a line Args.parse refuses).
// The eight index options (B.Args.wfmt), one word each.
static int io64_wfmt(const char* x) {
  static const char* const f[8] = {"-W", "--write-index", "-Wcsi", "-W=csi", "--write-index=csi", "-Wtbi", "-W=tbi", "--write-index=tbi"};
  for (int i = 0; i < 8; i += 1) if (!strcmp(x, f[i])) return 1;
  return 0;
}

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
    else if (pend == 'o') { ok = ok && !io64_ends_ci(x, ".bcf"); pend = 0; }
    else if (pend == 'O') { ok = ok && io64_otype(x); pend = 0; }
    else if (!strcmp(x, "-f")) pend = 'f';
    else if (!strcmp(x, "-c")) pend = 'c';
    else if (!strcmp(x, "-w")) pend = 'w';
    else if (!strcmp(x, "--threads")) pend = 't';
    else if (!strcmp(x, "-o")) pend = 'o';
    else if (!strcmp(x, "-O")) pend = 'O';
    else if (!strncmp(x, "-O", 2)) ok = ok && io64_otype(x + 2);
    else if (io64_wfmt(x)) {}
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
