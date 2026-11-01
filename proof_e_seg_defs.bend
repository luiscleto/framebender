import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_e_defs.bend as SD
import ./proof_run_sort.bend as S

# Phase E, area "seg": the definitions of the segment lemma's proof
# (notes/parallel_proofs_seg.md). X is the true run, Y the task's run T on
# the same lines; once S's buffer E is written, X is lift(Y).

# What X's last item is for Y's: the phantom stands for q (X's last before
# T wrote anything), a real item for itself, its line moved on by d.
def img.k(ph: Bool, +q: Maybe<&2, R.Item>, +x: R.Item, +d: Nat) -> Maybe<&2, R.Item>:
  match ph:
    case True{}:
      q
    case False{}:
      Some{SD.item_shift(d, x)}

def img(+q: Maybe<&2, R.Item>, m: Maybe<&2, R.Item>, +d: Nat) -> Maybe<&2, R.Item>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      img.k(SD.is_phantom(x), q, x, d)

# X as Y's state: lines d more, S's head, ended z under Y's, written p
# before Y's, counts sk added, S's notes then Y's (moved on by d), the
# buffer's lines moved on by d.
def lift(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{Nat.add(n, d), i, sh, c, List.append(&2, String, e, z), img(q, l, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), SD.notes_app(sns, SD.notes_shift(d, ns)), x}

# No item is the phantom (line 0).
def allreal(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.not(SD.is_phantom(x)) && allreal(t)

# q is at most the phantom's key (when Y's last is the phantom).
def qok.k(ph: Bool, +q: Maybe<&2, R.Item>, +x: R.Item) -> Bool:
  match ph:
    case True{}:
      Nat.is_le(S.lkey(q), R.Item.key(x))
    case False{}:
      True{}

def qok(+q: Maybe<&2, R.Item>, m: Maybe<&2, R.Item>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      qok.k(SD.is_phantom(x), q, x)

# Y's state as the simulation keeps it.
def inv2(+q: Maybe<&2, R.Item>, st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      i && Bool.not(x) && allreal(b) && qok(q, l)

# What only grows along a run: being stopped, and the CHROMs started.
def M(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      Bool.not(x) && SD.chroms_ok(List.append(&2, String, SD.cur_list(c), e), c0, se, sc)

def halt(st: R.RunSt) -> Bool:
  R.RunSt.halt(st)

# T's end as segok sees it: not stopped, its CHROMs fresh.
def Good(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +st: R.RunSt) -> Bool:
  Bool.not(halt(st)) && M(c0, se, sc, st)

def G1(+l: Nat, +mb: Nat, st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, i, h, c, e, tl, +b, k, o, ns, x}:
      Nat.is_lt(0n, n) && (Bool.not(List.is_empty(&2, String, e)) || (SD.keys_ge(b, l) && Nat.is_le(mb, SD.max_inpos(b, SD.real_inpos(tl)))))

# Phase 1 (S's buffer not all written yet): also some line, and T left c0
# or kept only keys at least l and some item at least mb in input POS.
def Good1(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l: Nat, +mb: Nat, +st: R.RunSt) -> Bool:
  Good(c0, se, sc, st) && G1(l, mb, st)

# A T state that segok refuses: stopped, or still in its first run with a
# key below l buffered.
def Bad(+l: Nat, st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, i, h, c, e, tl, b, k, o, ns, x}:
      x || (List.is_empty(&2, String, e) && Bool.not(SD.keys_ge(b, l)))

# Every input POS is below m.
def all_lt(xs: List<&2, R.Item>, +m: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Nat.is_lt(R.Item.inpos(x), m) && all_lt(t, m)

def is_flushed(f: R.Flush) -> Bool:
  match f:
    case R.Flushed{o, l}:
      True{}
    case R.Broke{o, b, p}:
      False{}

def fmap(+q: Maybe<&2, R.Item>, +d: Nat, f: R.Flush) -> R.Flush:
  match f:
    case R.Flushed{o, l}:
      R.Flushed{o, img(q, l, d)}
    case R.Broke{o, b, p}:
      R.Broke{o, b, p}

# The phantom of rs0.
def ph(+c0: String, +l: Nat) -> R.Item:
  R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}
