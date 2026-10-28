import Base
import ./types.bend as B
import ./run.bend as R
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/fast.bend as F

# framebender: the run's bookkeeping on packed bytes (code, not spec).
#
# The machine's counterpart of run.bend's RunSt, with the waiting items'
# texts kept as bytes. The refinement (notes/bytes.md, "The run on bytes"):
# a Run stands for the RunSt whose
#   out   is the text of ob's first ow bytes (what was written this step;
#         earlier steps' bytes were handed to the driver),
#   buf   is front ++ reverse(back), each Ck standing for the Item whose text
#         is the next len bytes of ob after ow (in buffer order),
#   last  is the last item written, without its text (run.bend only reads
#         its key and where it came from),
#   notes is the reverse of notes,
# and every other field is the same. Every item of buf and last has CHROM cur.

# An item waiting in the buffer (or the last one written): its key, its input
# POS, its line number, its POS as written (None: Nat.show(key), as for an
# unchanged record) and the length of its text.
type Ck is Data:
  Ck{key: Nat, inpos: Nat, line: Nat, pos: Maybe<&2, String>, len: U32}

# The run.
#   n, inbody, head, cur, ended, cnt, halt: as RunSt's.
#   cb: cur's bytes (empty when cur is None), for the fast path.
#   last: RunSt's last, without its text.
#   front, back: the buffer is front ++ reverse(back); bn items; tail: the
#     largest key in it (its last item's).
#   ob, ow: the bytes written this step (the first ow), then the texts of
#     the buffered items in buffer order.
#   notes: the messages of this step, newest first.
type Run is Type:
  Run{n: Nat, inbody: Bool, head: String, cur: Maybe<&2, String>, cb: D.Bytes, ended: List<&2, String>, last: Maybe<&2, Ck>, front: List<&2, Ck>, back: List<&2, Ck>, bn: Nat, tail: Nat, cnt: R.Cnt, ob: D.Bytes, ow: U32, notes: List<&2, B.Note>, halt: Bool}

# The text of an item: the bytes s .. s+n-1 of the input (Raw), or a text of
# its own (Own).
type Txt is Data:
  Raw{}
  Own{s: String}

# Where x goes in a sorted list (after every key at most x's): the items
# before it and their text length, and the rest.
type Ins is Data:
  Ins{pre: List<&2, Ck>, plen: U32, rest: List<&2, Ck>}

type Fl is Type:
  Fl{r: Run, go: Bool}

def Ck.key(c: Ck) -> Nat:
  match c:
    case Ck{k, ip, l, p, n}:
      k

def Ck.len(c: Ck) -> U32:
  match c:
    case Ck{k, ip, l, p, n}:
      n

def pos_text(m: Maybe<&2, String>, +k: Nat) -> String:
  match m:
    case None{}:
      Nat.show(k)
    case Some{s}:
      s

# Where an item came from (its CHROM is the run's).
def Ck.at(c: Ck, +chrom: String) -> B.At:
  match c:
    case Ck{+k, ip, l, p, n}:
      B.At{l, chrom, pos_text(p, k)}

def at_of(m: Maybe<&2, Ck>, +chrom: String) -> Maybe<&2, B.At>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{Ck.at(c, chrom)}

def start() -> Run:
  Run{0n, False{}, "", None{}, BY.empty(0n), Nil{}, None{}, Nil{}, Nil{}, 0n, 0n, R.Cnt{0n, 0n, 0n, 0n}, BY.empty(16n), 0, Nil{}, False{}}

# ---------------------------------------------------------------------------
# Bytes
# ---------------------------------------------------------------------------

def depth.go(fuel: Nat, +d: Nat, +need: U32) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      Bool.pick(Nat, U32.is_le(need, U32.shln(4, d)), d, depth.go(f, Nat.add(d, 1n), need))

# The smallest depth whose block holds need bytes (at most 29).
def depth(+need: U32) -> Nat:
  depth.go(29n, 0n, need)

def room.if(ok: Bool, +n: U32, b: D.Bytes) -> D.Bytes:
  match ok:
    case True{}:
      b
    case False{}:
      BY.grow(b, depth((n * 2 : U32)))

def room.k(+n: U32, r: D.Bytes & U32) -> D.Bytes:
  (b, +cap) = r
  room.if(U32.is_le(n, cap), n, b)

def room.len(+k: U32, r: D.Bytes & U32) -> D.Bytes:
  (b, +len) = r
  room.k((len + k + 8 : U32), BY.capacity(b))

# b with room for k more bytes (and 8 to spare: the fast append writes up
# to 3 bytes past the end).
def room(b: D.Bytes, +k: U32) -> D.Bytes:
  room.len(k, BY.len(b))

def put_str.go(s: String, b: D.Bytes) -> D.Bytes:
  match s:
    case SNil{}:
      b
    case SCon{Chr{x}, t}:
      put_str.go(t, BY.push(b, x))

# The bytes of a text (one byte per Char) added at the end of b.
def put_str(b: D.Bytes, +s: String) -> D.Bytes:
  put_str.go(s, room(b, U32.from_nat(String.length(s))))

# A text as a new buffer.
def of_str(+s: String) -> D.Bytes:
  put_str(BY.empty(0n), s)

def put_bytes.k(r: D.Bytes & D.Bytes) -> D.Bytes & D.Bytes:
  (dst, src) = r
  (dst, src)

# Bytes s .. s+n-1 of src added at the end of dst; src handed back.
def put_bytes(dst: D.Bytes, src: D.Bytes, +s: U32, +n: U32) -> D.Bytes & D.Bytes:
  F.append(room(dst, n), src, s, n)

# ---------------------------------------------------------------------------
# Messages and counts
# ---------------------------------------------------------------------------

def rev_onto(xs: List<&2, B.Note>, acc: List<&2, B.Note>) -> List<&2, B.Note>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_onto(t, x <> acc)

# The run stops with a message (R.stop with nothing more written).
def stop(r: Run, nt: B.Note) -> Run:
  match r:
    case Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, nt <> ns, True{}}

def tick(r: Run) -> Run:
  match r:
    case Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      Run{1n+n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}

def Run.n(r: Run) -> Run & Nat:
  match r:
    case Run{+n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      (Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, n)

def Run.flags(r: Run) -> Run & (Bool & Bool):
  match r:
    case Run{n, +i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, +x}:
      (Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, (i, x))

def Run.cnt(r: Run) -> Run & R.Cnt:
  match r:
    case Run{n, i, h, c, cb, e, l, f, b, bn, tl, +k, ob, ow, ns, x}:
      (Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, k)

# ---------------------------------------------------------------------------
# Writing ready items: run.bend's flush of take_ready, then drop_ready
# ---------------------------------------------------------------------------

def flush.stop(r: Run, +bad: Ck) -> Run:
  match r:
    case Run{n, i, h, +c, cb, e, +l, f, b, bn, tl, k, ob, ow, ns, x}:
      +chrom = Maybe.default(&2, String, c, "")
      Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, B.Stop{B.Unsorted{}, Some{Ck.at(bad, chrom)}, at_of(l, chrom)} <> ns, True{}}

def last_le(m: Maybe<&2, Ck>, +k: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ck{lk, ip, l, p, n}}:
      Nat.is_le(lk, k)

def rev_ck(xs: List<&2, Ck>, acc: List<&2, Ck>) -> List<&2, Ck>:
  match xs:
    case Nil{}:
      acc
    case x <> t:
      rev_ck(t, x <> acc)

def Run.bn(r: Run) -> Run & Nat:
  match r:
    case Run{n, i, h, c, cb, e, l, f, b, +bn, tl, k, ob, ow, ns, x}:
      (Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}, bn)

def txt_len(t: Txt, +n: U32) -> U32:
  match t:
    case Raw{}:
      n
    case Own{s}:
      U32.from_nat(String.length(s))

def put_txt(t: Txt, ob: D.Bytes, src: D.Bytes, +s: U32, +n: U32) -> D.Bytes & D.Bytes:
  match t:
    case Raw{}:
      put_bytes(ob, src, s, n)
    case Own{+x}:
      (put_str(ob, x), src)

def at_end.fin(+x: Ck, +kx: Nat, p: D.Bytes & D.Bytes, +nn: Nat, +i: Bool, h: String, c: Maybe<&2, String>, cb: D.Bytes, e: List<&2, String>, l: Maybe<&2, Ck>, f: List<&2, Ck>, b: List<&2, Ck>, +bn: Nat, k: R.Cnt, +ow: U32, ns: List<&2, B.Note>, hl: Bool) -> Run & D.Bytes:
  (ob, src) = p
  (Run{nn, i, h, c, cb, e, l, f, x <> b, 1n+bn, kx, k, ob, ow, ns, hl}, src)

def at_end(+x: Ck, +kx: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32, r: Run) -> Run & D.Bytes:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      at_end.fin(x, kx, put_txt(t, ob, src, s, n), nn, i, h, c, cb, e, l, f, b, bn, k, ow, ns, hl)

# Bytes from + k onwards of b moved to a new buffer, b cut to from.
def cut_tail.k(+from: U32, r: D.Bytes & D.Bytes) -> D.Bytes & D.Bytes:
  (tmp, b) = r
  (BY.truncate(b, from), tmp)

def cut_tail.len(+from: U32, r: D.Bytes & U32) -> D.Bytes & D.Bytes:
  (b, +len) = r
  cut_tail.k(from, put_bytes(BY.empty(0n), b, from, (len - from : U32)))

def cut_tail(b: D.Bytes, +from: U32) -> D.Bytes & D.Bytes:
  cut_tail.len(from, BY.len(b))

def ins.cons(+y: Ck, i: Ins) -> Ins:
  match i:
    case Ins{p, n, r}:
      Ins{y <> p, (n + Ck.len(y) : U32), r}

def append_ck(xs: List<&2, Ck>, ys: List<&2, Ck>) -> List<&2, Ck>:
  match xs:
    case Nil{}:
      ys
    case x <> t:
      x <> append_ck(t, ys)

def put_all(ob: D.Bytes, tmp: D.Bytes) -> D.Bytes & D.Bytes:
  D.Bytes{+tn, tb} = tmp
  put_bytes(ob, D.Bytes{tn, tb}, 0, tn)

def mid.join(p: D.Bytes & D.Bytes) -> D.Bytes:
  (ob, tmp) = p
  ob

def mid.fin(+x: Ck, pre: List<&2, Ck>, rest: List<&2, Ck>, p: D.Bytes & D.Bytes, tmp: D.Bytes, r: Run) -> Run & D.Bytes:
  (ob, src) = p
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, hl}:
      (Run{nn, i, h, c, cb, e, l, append_ck(pre, x <> rest), Nil{}, 1n+bn, tl, k, mid.join(put_all(ob, tmp)), ow, ns, hl}, src)

def mid.k(+x: Ck, t: Txt, src: D.Bytes, +s: U32, +n: U32, pre: List<&2, Ck>, rest: List<&2, Ck>, q: D.Bytes & D.Bytes, r: Run) -> Run & D.Bytes:
  (ob, tmp) = q
  mid.fin(x, pre, rest, put_txt(t, ob, src, s, n), tmp, r)

def mid.go(+x: Ck, t: Txt, src: D.Bytes, +s: U32, +n: U32, ins: Ins, r: Run) -> Run & D.Bytes:
  match ins r:
    case Ins{pre, +pl, rest} Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, hl}:
      mid.k(x, t, src, s, n, pre, rest, cut_tail(ob, (ow + pl : U32)), Run{nn, i, h, c, cb, e, l, Nil{}, Nil{}, bn, tl, k, BY.empty(0n), ow, ns, hl})

# ins.start's walk: y is the next item, le says its key is at most k.
def ins.go(t: List<&2, Ck>, le: Bool, +y: Ck, +k: Nat) -> Ins:
  match t le:
    case _ False{}:
      Ins{Nil{}, 0, y <> t}
    case Nil{} True{}:
      Ins{[y], Ck.len(y), Nil{}}
    case +z <> t2 True{}:
      ins.cons(y, ins.go(t2, Nat.is_le(Ck.key(z), k), z, k))

def ins.start(xs: List<&2, Ck>, +k: Nat) -> Ins:
  match xs:
    case Nil{}:
      Ins{Nil{}, 0, Nil{}}
    case +y <> t:
      ins.go(t, Nat.is_le(Ck.key(y), k), y, k)

# An item whose key is below the buffer's largest (rare): the buffer is made
# one sorted list and the item's text inserted in ob at its place.
def mid(+x: Ck, +kx: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32, r: Run) -> Run & D.Bytes:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      mid.go(x, t, src, s, n, ins.start(append_ck(f, rev_ck(b, Nil{})), kx), Run{nn, i, h, c, cb, e, l, Nil{}, Nil{}, bn, tl, k, ob, ow, ns, hl})

def add.if(end: Bool, +x: Ck, +kx: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32, r: Run) -> Run & D.Bytes:
  match end:
    case True{}:
      at_end(x, kx, t, src, s, n, r)
    case False{}:
      mid(x, kx, t, src, s, n, r)

# run.bend's insert: x goes after every item whose key is at most its own.
def add(r: Run, +x: Ck, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, +bn, +tl, k, ob, ow, ns, hl}:
      add.if(Nat.is_eq(bn, 0n) || Nat.is_le(tl, Ck.key(x)), x, Ck.key(x), t, src, s, n, Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl})

def flush.one(ok: Bool, r: Run, +x: Ck, t: List<&2, Ck>) -> Fl:
  match ok r:
    case False{} _:
      Fl{flush.stop(r, x), False{}}
    case True{} Run{n, i, h, c, cb, e, l, f, b, 1n+bn, tl, k, ob, ow, ns, hl}:
      Fl{Run{n, i, h, c, cb, e, Some{x}, t, b, bn, tl, k, ob, (ow + Ck.len(x) : U32), ns, hl}, True{}}
    case True{} Run{n, i, h, c, cb, e, l, f, b, 0n, tl, k, ob, ow, ns, hl}:
      Fl{Run{n, i, h, c, cb, e, Some{x}, t, b, 0n, tl, k, ob, (ow + Ck.len(x) : U32), ns, hl}, True{}}

# The first item x is ready: written, unless its key is below last's.
def flush.ok(r: Run, +x: Ck, t: List<&2, Ck>) -> Fl:
  match r:
    case Run{n, i, h, c, cb, e, +l, f, b, bn, tl, k, ob, ow, ns, hl}:
      flush.one(last_le(l, Ck.key(x)), Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}, x, t)

def flush.head(ready: Bool, r: Run, +x: Ck, t: List<&2, Ck>) -> Fl:
  match ready r:
    case False{} Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      Fl{Run{n, i, h, c, cb, e, l, x <> t, b, bn, tl, k, ob, ow, ns, hl}, False{}}
    case True{} _:
      flush.ok(r, x, t)

def flush.front(fr: List<&2, Ck>, r: Run, +w: Nat, +inpos: Nat, +all: Bool) -> Fl:
  match fr:
    case Nil{}:
      Fl{r, False{}}
    case +x <> t:
      flush.head(all || Nat.is_le(Nat.add(Ck.key(x), w), inpos), r, x, t)

# One step: the first buffered item written if it is ready (front refilled
# from back when it is empty); go says to try the next one.
def flush.step(r: Run, +w: Nat, +inpos: Nat, +all: Bool) -> Fl:
  match r:
    case Run{n, i, h, c, cb, e, l, Nil{}, b, bn, tl, k, ob, ow, ns, False{}}:
      flush.front(rev_ck(b, Nil{}), Run{n, i, h, c, cb, e, l, Nil{}, Nil{}, bn, tl, k, ob, ow, ns, False{}}, w, inpos, all)
    case Run{n, i, h, c, cb, e, l, f <> ft, b, bn, tl, k, ob, ow, ns, False{}}:
      flush.front(f <> ft, Run{n, i, h, c, cb, e, l, Nil{}, b, bn, tl, k, ob, ow, ns, False{}}, w, inpos, all)
    case Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, True{}}:
      Fl{Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, True{}}, False{}}

def flush.go(fuel: Nat, p: Fl, +w: Nat, +inpos: Nat, +all: Bool) -> Run:
  match fuel p:
    case 0n Fl{r, g}:
      r
    case 1n+f Fl{r, False{}}:
      r
    case 1n+f Fl{r, True{}}:
      flush.go(f, flush.step(r, w, inpos, all), w, inpos, all)

def flush.k(+w: Nat, +inpos: Nat, +all: Bool, p: Run & Nat) -> Run:
  (r, +bn) = p
  flush.go(Nat.add(bn, 2n), Fl{r, True{}}, w, inpos, all)

# The ready items (key + w <= inpos; all of them when all) written in order;
# the run stops (UNSORTED) at the first one whose key is below the last
# key written. (The buffer is sorted, so only its first item can be.)
def flush(r: Run, +w: Nat, +inpos: Nat, +all: Bool) -> Run:
  flush.k(w, inpos, all, Run.bn(r))

# ---------------------------------------------------------------------------
# keyed, same_run, new_run (run.bend's, on bytes)
# ---------------------------------------------------------------------------

def same_run.k(+w: Nat, +inpos: Nat, p: Run & D.Bytes) -> Run & D.Bytes:
  (r, src) = p
  (flush(r, w, inpos, False{}), src)

# Same CHROM run: the item is inserted, then the ready items written.
def same_run(r: Run, +w: Nat, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  same_run.k(w, inpos, add(r, x, t, src, s, n))

def push_cur(c: Maybe<&2, String>, e: List<&2, String>) -> List<&2, String>:
  match c:
    case None{}:
      e
    case Some{s}:
      s <> e

def new_run.go(halt: Bool, again: Bool, r: Run, +w: Nat, +chrom: String, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match halt again r:
    case True{} _ _:
      (r, src)
    case False{} True{} _:
      (stop(r, B.Stop{B.Unsorted{}, Some{Ck.at(x, chrom)}, None{}}), src)
    case False{} False{} Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      same_run(Run{nn, i, h, Some{chrom}, of_str(chrom), push_cur(c, e), None{}, Nil{}, Nil{}, 0n, 0n, k, ob, ow, ns, hl}, w, x, inpos, t, src, s, n)

def new_run.k(r: Run, +w: Nat, +chrom: String, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match r:
    case Run{nn, i, h, c, cb, +e, l, f, b, bn, tl, k, ob, ow, ns, +hl}:
      new_run.go(hl, R.has(chrom, e), Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}, w, chrom, x, inpos, t, src, s, n)

# A new CHROM: the whole buffer is written; a CHROM whose run ended stops the
# run (UNSORTED); else its run starts.
def new_run(r: Run, +w: Nat, +chrom: String, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  new_run.k(flush(r, w, 0n, True{}), w, chrom, x, inpos, t, src, s, n)

def keyed.go(same: Bool, r: Run, +w: Nat, +chrom: String, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match same:
    case True{}:
      same_run(r, w, x, inpos, t, src, s, n)
    case False{}:
      new_run(r, w, chrom, x, inpos, t, src, s, n)

# A line that goes on: its messages and counts, then the CHROM-run rule and
# the buffer rule. Its text is t (Raw: bytes s .. s+n-1 of src).
# (The counts are bumped as run.bend's callers do: changed, skipped, warned.)
def keyed(r: Run, +w: Nat, +chrom: String, +x: Ck, +inpos: Nat, t: Txt, src: D.Bytes, +s: U32, +n: U32, nts: List<&2, B.Note>, ch: Bool, sk: Bool, wa: Bool) -> Run & D.Bytes:
  match r:
    case Run{nn, i, h, +c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      keyed.go(R.is_cur(c, chrom), Run{nn, i, h, c, cb, e, l, f, b, bn, tl, R.bump(k, ch, sk, wa), ob, ow, rev_onto(nts, ns), hl}, w, chrom, x, inpos, t, src, s, n)

# ---------------------------------------------------------------------------
# One body line by its result (run.bend's body_line); its text is the bytes
# s .. s+n-1 of src (the line as it came, with its terminator)
# ---------------------------------------------------------------------------

def item(+k: Nat, +inpos: Nat, +at: B.At, +n: U32) -> Ck:
  match at:
    case B.At{line, c, p}:
      Ck{k, inpos, line, Some{p}, n}

def At.chrom(at: B.At) -> String:
  match at:
    case B.At{l, c, p}:
      c

def problem_line(strict: Bool, r: Run, +w: Nat, +c: B.Code, +at: B.At, +inpos: Nat, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match strict:
    case True{}:
      (stop(r, B.Stop{c, Some{at}, None{}}), src)
    case False{}:
      keyed(r, w, At.chrom(at), item(inpos, inpos, at, n), inpos, Raw{}, src, s, n, [B.Warning{c, at}], False{}, False{}, True{})

def own.if(same: Bool, +t: String, +term: String) -> Txt:
  match same:
    case True{}:
      Raw{}
    case False{}:
      Own{t ++ term}

# The text of a normalized line: the line's bytes when it is unchanged
# (t ++ term is then the line's text), else t ++ term.
def normalized(r: Run, +w: Nat, +k: Nat, +t: String, +stale: Bool, +l: B.Line, +at: B.At, +inpos: Nat, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  +same = String.eq(t, B.Line.body(l))
  +tx = own.if(same, t, B.Line.term(l))
  keyed(r, w, At.chrom(at), item(k, inpos, at, txt_len(tx, n)), inpos, tx, src, s, n, R.stale_note(stale, at), Bool.not(same), False{}, False{})

def body_line(res: B.Res, r: Run, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  match res:
    case B.Res{B.Broken{}, k, t, st}:
      (stop(r, B.Stop{B.Malformed{}, Some{at}, None{}}), src)
    case B.Res{B.NoContig{}, k, t, st}:
      (stop(r, B.Stop{B.UnknownChrom{}, Some{at}, None{}}), src)
    case B.Res{B.Problem{+c}, k, t, st}:
      problem_line(R.Opts.strict(o), r, R.Opts.w(o), c, at, inpos, src, s, n)
    case B.Res{B.Skipped{}, k, t, st}:
      keyed(r, R.Opts.w(o), At.chrom(at), item(inpos, inpos, at, n), inpos, Raw{}, src, s, n, Nil{}, False{}, True{}, False{})
    case B.Res{B.Normalized{}, +k, +t, +st}:
      normalized(r, R.Opts.w(o), k, t, st, l, at, inpos, src, s, n)

# A record already in normal form (J.fast gives Same): written as it came.
def same_done(r: Run, +o: B.Opts, +at: B.At, +inpos: Nat, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  keyed(r, R.Opts.w(o), At.chrom(at), item(inpos, inpos, at, n), inpos, Raw{}, src, s, n, Nil{}, False{}, False{}, False{})

def bump(r: Run, changed: Bool, skipped: Bool, warned: Bool) -> Run:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, hl}:
      Run{nn, i, h, c, cb, e, l, f, b, bn, tl, R.bump(k, changed, skipped, warned), ob, ow, ns, hl}

# The fast path's record (norm_fast.bend): in the current run, in normal
# form, written as it came; its POS is written as Nat.show(pos).
def fast_done(r: Run, +w: Nat, +line: Nat, +pos: Nat, src: D.Bytes, +s: U32, +n: U32) -> Run & D.Bytes:
  same_run(bump(r, False{}, False{}, False{}), w, Ck{pos, pos, line, None{}, n}, pos, Raw{}, src, s, n)

# The header is written at once (the buffer is empty before the first body
# line): ow covers all of ob.
def head_line.out(ob: D.Bytes, r: Run) -> Run:
  D.Bytes{+n, buf} = ob
  match r:
    case Run{nn, i, h, c, cb, e, la, f, b, bn, tl, k, o0, ow, ns, hl}:
      Run{nn, i, h, c, cb, e, la, f, b, bn, tl, k, D.Bytes{n, buf}, n, ns, hl}

# ---------------------------------------------------------------------------
# Header lines (run.bend's head_line)
# ---------------------------------------------------------------------------

def head_line(isc: Bool, r: Run, +o: B.Opts, +l: B.Line) -> Run:
  match isc r l:
    case True{} Run{nn, i, h, c, cb, e, la, f, b, bn, tl, k, ob, ow, ns, hl} B.Line{+bd, +term}:
      head_line.out(put_str(ob, h ++ R.added(o, term) ++ bd ++ term), Run{nn, True{}, "", c, cb, e, la, f, b, bn, tl, k, BY.empty(0n), ow, ns, hl})
    case False{} Run{nn, i, h, c, cb, e, la, f, b, bn, tl, k, ob, ow, ns, hl} _:
      Run{nn, i, h ++ B.Line.text(l), c, cb, e, la, f, b, bn, tl, k, ob, ow, ns, hl}

def summary(k: R.Cnt) -> B.Note:
  match k:
    case R.Cnt{n, ch, sk, wa}:
      B.Summary{n, ch, sk, wa}

# ---------------------------------------------------------------------------
# The end of the file (run.bend's finish): the code
# ---------------------------------------------------------------------------

def finish.k(r: Run) -> Run & Nat:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, +k, ob, ow, ns, True{}}:
      (Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, True{}}, 1n)
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, +k, ob, ow, ns, False{}}:
      (Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, summary(k) <> ns, False{}}, 0n)

# A run that stopped ends with code 1; a file without a #CHROM line is
# NO_HEADER (nothing was written); else the buffer is written and the run
# ends with the summary (or UNSORTED).
def finish(r: Run, +w: Nat) -> Run & Nat:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, True{}}:
      (Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, True{}}, 1n)
    case Run{nn, False{}, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, False{}}:
      (Run{nn, False{}, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, [B.Stop{B.NoHeader{}, None{}, None{}}], True{}}, 1n)
    case Run{nn, True{}, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, False{}}:
      finish.k(flush(Run{nn, True{}, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, False{}}, w, 0n, True{}))

# ---------------------------------------------------------------------------
# The end of a step: the bytes written are handed out, the buffered texts
# kept in a new buffer
# ---------------------------------------------------------------------------

def take.k(+ow: U32, r: D.Bytes & D.Bytes) -> D.Bytes & D.Bytes:
  (keep, ob) = r
  (BY.truncate(ob, ow), keep)

# The new buffer holds the buffered texts and room for left more bytes (the
# input not handled yet).
def take.len(+ow: U32, +left: U32, r: D.Bytes & U32) -> D.Bytes & D.Bytes:
  (ob, +len) = r
  take.k(ow, put_bytes(BY.empty(depth(((len - ow : U32) + left + 65536 : U32))), ob, ow, (len - ow : U32)))

def take.if(none: Bool, +ow: U32, +left: U32, ob: D.Bytes) -> D.Bytes & D.Bytes:
  match none:
    case True{}:
      (BY.empty(0n), ob)
    case False{}:
      take.len(ow, left, BY.len(ob))

def take.fin(p: D.Bytes & D.Bytes, r: Run) -> (D.Bytes & List<&2, B.Note>) & Run:
  (out, ob) = p
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, hl}:
      ((out, List.reverse(&2, B.Note, ns)), Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, 0, Nil{}, hl})

# What this step wrote (bytes, messages in order), and the run with both
# emptied; left: the input bytes not handled yet.
def take(r: Run, +left: U32) -> (D.Bytes & List<&2, B.Note>) & Run:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, hl}:
      take.fin(take.if(U32.is_zero(ow), ow, left, ob), Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, hl})

def reserve.if(ok: Bool, +n: U32, b: D.Bytes) -> D.Bytes:
  match ok:
    case True{}:
      b
    case False{}:
      BY.grow(b, depth(n))

def reserve.k(+n: U32, r: D.Bytes & U32) -> D.Bytes:
  (b, +cap) = r
  reserve.if(U32.is_le(n, cap), n, b)

def reserve.len(+k: U32, r: D.Bytes & U32) -> D.Bytes:
  (b, +len) = r
  reserve.k((len + k + 8 : U32), BY.capacity(b))

# ob with room for k more bytes, grown once to the smallest block that holds
# them (a piece's records are about its size).
def reserve(r: Run, +k: U32) -> Run:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, kk, ob, ow, ns, hl}:
      Run{nn, i, h, c, cb, e, l, f, b, bn, tl, kk, reserve.len(k, BY.len(ob)), ow, ns, hl}

# ---------------------------------------------------------------------------
# The run as run.bend's state (for the String mode, norm.bend)
# ---------------------------------------------------------------------------

def chars(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, t}:
      SCon{Chr{x}, chars(t)}

def spec.item(c: Ck, +chrom: String, +t: String) -> R.Item:
  match c:
    case Ck{+k, ip, l, p, n}:
      R.Item{k, ip, B.At{l, chrom, pos_text(p, k)}, t}

# The items with their texts, taken in order from t.
def spec.items(cs: List<&2, Ck>, +chrom: String, +t: String) -> List<&2, R.Item>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +n = U32.to_nat(Ck.len(c))
      spec.item(c, chrom, String.take(t, n)) <> spec.items(rest, chrom, String.drop(t, n))

def spec.last(m: Maybe<&2, Ck>, +chrom: String) -> Maybe<&2, R.Item>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{spec.item(c, chrom, "")}

def spec.k(+n: Nat, +i: Bool, h: String, +c: Maybe<&2, String>, e: List<&2, String>, l: Maybe<&2, Ck>, f: List<&2, Ck>, b: List<&2, Ck>, k: R.Cnt, +ow: U32, ns: List<&2, B.Note>, x: Bool, r: D.Bytes & List<&2, U32>) -> R.RunSt:
  (ob, xs) = r
  +t = chars(xs)
  +chrom = Maybe.default(&2, String, c, "")
  R.RunSt{n, i, h, c, e, spec.last(l, chrom), spec.items(append_ck(f, rev_ck(b, Nil{})), chrom, String.drop(t, U32.to_nat(ow))), k, String.take(t, U32.to_nat(ow)), List.reverse(&2, B.Note, ns), x}

# The run as run.bend's RunSt: out is what was written this step, notes this
# step's messages in order, the buffer's items with their texts from ob, and
# the last item written with an empty text (run.bend reads only its key and
# where it came from).
def to_spec(r: Run) -> R.RunSt:
  match r:
    case Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      D.Bytes{+len, buf} = ob
      spec.k(nn, i, h, c, e, l, f, b, k, ow, ns, x, BY.to_list(D.Bytes{len, buf}, 0, len))
