import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G
import ./proof_b_frame_fr.bend as F

# Phase E, area "seg": a task's messages. The true run X writes T's messages
# with their line numbers moved on (G.lift: S's, then T's); nothing else
# reads them, so messages T already has can be moved into X's (F.pre in
# front of T's state, SD.notes_app at the end of S's): the step lemmas are
# shown for a T state with no messages, and the rest follows.

# notes_app is List.append.
def na_eq(+a: List<&2, B.Note>, +b: List<&2, B.Note>) -> {SD.notes_app(a, b) == List.append(&2, B.Note, a, b) : List<&2, B.Note>}:
  match b:
    case Nil{}:
      Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, a, Nil{}), a, P.append_nil(B.Note, a))
    case +x <> +t:
      {==}

# Moving messages on keeps appends.
def ns_app(+d: Nat, +xs: List<&2, B.Note>, +ys: List<&2, B.Note>) ->
  {SD.notes_shift(d, List.append(&2, B.Note, xs, ys)) == List.append(&2, B.Note, SD.notes_shift(d, xs), SD.notes_shift(d, ys)) : List<&2, B.Note>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(List<&2, B.Note>, SD.notes_shift(d, List.append(&2, B.Note, t, ys)), List.append(&2, B.Note, SD.notes_shift(d, t), SD.notes_shift(d, ys)), ns_app(d, t, ys)) :
        {SD.note_shift(d, x) <> _ == SD.note_shift(d, x) <> List.append(&2, B.Note, SD.notes_shift(d, t), SD.notes_shift(d, ys)) : List<&2, B.Note>}
      {==}

# X's messages: S's, then a's and b's (moved on by d).
def na3(+sns: List<&2, B.Note>, +d: Nat, +a: List<&2, B.Note>, +b: List<&2, B.Note>) ->
  {SD.notes_app(sns, SD.notes_shift(d, List.append(&2, B.Note, a, b))) == SD.notes_app(SD.notes_app(sns, SD.notes_shift(d, a)), SD.notes_shift(d, b)) : List<&2, B.Note>}:
  +A = SD.notes_shift(d, a)
  +Bx = SD.notes_shift(d, b)
  +e1 = na_eq(sns, SD.notes_shift(d, List.append(&2, B.Note, a, b)))
  +e2 = Equal.cong(List<&2, B.Note>, List<&2, B.Note>, z => List.append(&2, B.Note, sns, z), SD.notes_shift(d, List.append(&2, B.Note, a, b)), List.append(&2, B.Note, A, Bx), ns_app(d, a, b))
  +e3 = Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, sns, A), Bx), List.append(&2, B.Note, sns, List.append(&2, B.Note, A, Bx)), P.append_assoc(B.Note, sns, A, Bx))
  +e4 = na_eq(SD.notes_app(sns, A), Bx)
  +e5 = Equal.cong(List<&2, B.Note>, List<&2, B.Note>, z => List.append(&2, B.Note, z, Bx), SD.notes_app(sns, A), List.append(&2, B.Note, sns, A), na_eq(sns, A))
  Equal.trans(List<&2, B.Note>, SD.notes_app(sns, SD.notes_shift(d, List.append(&2, B.Note, a, b))), List.append(&2, B.Note, List.append(&2, B.Note, sns, A), Bx), SD.notes_app(SD.notes_app(sns, A), Bx),
    Equal.trans(List<&2, B.Note>, SD.notes_app(sns, SD.notes_shift(d, List.append(&2, B.Note, a, b))), List.append(&2, B.Note, sns, List.append(&2, B.Note, A, Bx)), List.append(&2, B.Note, List.append(&2, B.Note, sns, A), Bx),
      Equal.trans(List<&2, B.Note>, SD.notes_app(sns, SD.notes_shift(d, List.append(&2, B.Note, a, b))), List.append(&2, B.Note, sns, SD.notes_shift(d, List.append(&2, B.Note, a, b))), List.append(&2, B.Note, sns, List.append(&2, B.Note, A, Bx)), e1, e2),
      e3),
    Equal.sym(List<&2, B.Note>, SD.notes_app(SD.notes_app(sns, A), Bx), List.append(&2, B.Note, List.append(&2, B.Note, sns, A), Bx),
      Equal.trans(List<&2, B.Note>, SD.notes_app(SD.notes_app(sns, A), Bx), List.append(&2, B.Note, SD.notes_app(sns, A), Bx), List.append(&2, B.Note, List.append(&2, B.Note, sns, A), Bx), e4, e5)))

# T's messages N in front: X's messages are S's then N's (moved on).
def lift_pre(+d: Nat, +sh: String, +z: List<&2, String>, +p: String, +sk: R.Cnt, +sns: List<&2, B.Note>, +q: Maybe<&2, R.Item>, +N: List<&2, B.Note>, +st: R.RunSt) ->
  {G.lift(d, sh, z, p, sk, sns, q, F.pre("", N, st)) == G.lift(d, sh, z, p, sk, SD.notes_app(sns, SD.notes_shift(d, N)), q, st) : R.RunSt}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %na3(sns, d, N, ns) :
        {R.RunSt{Nat.add(n, d), i, sh, c, List.append(&2, String, e, z), G.img(q, l, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), SD.notes_app(sns, SD.notes_shift(d, List.append(&2, B.Note, N, ns))), x}
          == R.RunSt{Nat.add(n, d), i, sh, c, List.append(&2, String, e, z), G.img(q, l, d), SD.items_shift(d, b), SD.cnt_add(sk, k), String.append(p, o), _, x} : R.RunSt}
      {==}

# A state with messages N is the same state without them, N in front.
def strip(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +N: List<&2, B.Note>, +x: Bool) ->
  {R.RunSt{n, i, h, c, e, l, b, k, o, N, x} == F.pre("", N, R.RunSt{n, i, h, c, e, l, b, k, o, Nil{}, x}) : R.RunSt}:
  %P.append_nil(B.Note, N) : {R.RunSt{n, i, h, c, e, l, b, k, o, _, x} == R.RunSt{n, i, h, c, e, l, b, k, o, List.append(&2, B.Note, N, Nil{}), x} : R.RunSt}
  {==}

# Good, Good1 and inv2 do not read messages or what was written.
def good_pre(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +O: String, +N: List<&2, B.Note>, +st: R.RunSt) ->
  {G.Good(c0, se, sc, F.pre(O, N, st)) == G.Good(c0, se, sc, st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

def good1_pre(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +l0: Nat, +mb: Nat, +O: String, +N: List<&2, B.Note>, +st: R.RunSt) ->
  {G.Good1(c0, se, sc, l0, mb, F.pre(O, N, st)) == G.Good1(c0, se, sc, l0, mb, st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

def inv2_pre(+q: Maybe<&2, R.Item>, +O: String, +N: List<&2, B.Note>, +st: R.RunSt) ->
  {G.inv2(q, F.pre(O, N, st)) == G.inv2(q, st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

# Messages in front of S's, then T's.
def na_pre(+N: List<&2, B.Note>, +a: List<&2, B.Note>, +b: List<&2, B.Note>) ->
  {List.append(&2, B.Note, N, SD.notes_app(a, b)) == SD.notes_app(List.append(&2, B.Note, N, a), b) : List<&2, B.Note>}:
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, a), x <> t), List.append(&2, B.Note, N, List.append(&2, B.Note, a, x <> t)), P.append_assoc(B.Note, N, a, x <> t))
