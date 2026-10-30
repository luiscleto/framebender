import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import ./proof_run_base.bend as RBS
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The flush loop (norm_run.bend's flush.go) on a pictured run, against
# run.bend's flush of the ready items (all of them when all).

def chromof(+c: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, c, "")

def TXT(+obl: U32, +obt: AT.Tree<U32>) -> String:
  NR.chars(D.view(C.BT(obl, obt)))

# The buffered items, as run.bend's, with their texts.
def ISS(+xs: List<&2, NR.Ck>, +c: Maybe<&2, String>, +obl: U32, +obt: AT.Tree<U32>, +ow: U32) -> List<&2, R.Item>:
  NR.spec.items(xs, chromof(c), String.drop(TXT(obl, obt), U32.to_nat(ow)))

# What the flush writes and leaves (all: everything).
def TRd(all: Bool, +w: Nat, +inpos: Nat, +its: List<&2, R.Item>) -> List<&2, R.Item>:
  match all:
    case True{}:
      its
    case False{}:
      R.take_ready(w, inpos, its)

def DRd(all: Bool, +w: Nat, +inpos: Nat, +its: List<&2, R.Item>) -> List<&2, R.Item>:
  match all:
    case True{}:
      Nil{}
    case False{}:
      R.drop_ready(w, inpos, its)

# What a flush's outcome shows: stopped, the text written, the note (for a
# stop), the last item written (its text blanked).
type FS is Data:
  FS{halt: Bool, out: String, note: Maybe<&2, B.Note>, last: Maybe<&2, R.Item>}

def fs(f: R.Flush) -> FS:
  match f:
    case R.Flushed{o, l}:
      FS{False{}, o, None{}, P.blank(l)}
    case R.Broke{o, bad, prev}:
      FS{True{}, o, Some{B.Stop{B.Unsorted{}, Some{bad}, prev}}, None{}}

def fspre(+s: String, x: FS) -> FS:
  match x:
    case FS{h, o, n, l}:
      FS{h, String.append(s, o), n, l}

def consm(m: Maybe<&2, B.Note>, ns: List<&2, B.Note>) -> List<&2, B.Note>:
  match m:
    case None{}:
      ns
    case Some{v}:
      v <> ns

# The machine's result (l2, f2, b2, ow2, ns2, x2) for a flush outcome S, from
# a run with ow and ns, ob's text text: written text appended, the note
# added; when it goes on, the last item and the items left.
def FLR(x: FS, +chrom: String, +text: String, +ow: U32, +ns: List<&2, B.Note>, +dr: List<&2, R.Item>,
  +l2: Maybe<&2, NR.Ck>, +f2: List<&2, NR.Ck>, +b2: List<&2, NR.Ck>, +ow2: U32, +ns2: List<&2, B.Note>, +x2: Bool) -> Type:
  match x:
    case FS{False{}, o, n, la}:
      {x2 == False{} : Bool}
      & ({String.take(text, U32.to_nat(ow2)) == String.append(String.take(text, U32.to_nat(ow)), o) : String}
      & ({ns2 == ns : List<&2, B.Note>}
      & ({NR.spec.last(l2, chrom) == la : Maybe<&2, R.Item>}
      & {NR.spec.items(RD.items(f2, b2), chrom, String.drop(text, U32.to_nat(ow2))) == dr : List<&2, R.Item>})))
    case FS{True{}, o, n, la}:
      {x2 == True{} : Bool}
      & ({String.take(text, U32.to_nat(ow2)) == String.append(String.take(text, U32.to_nat(ow)), o) : String}
      & {ns2 == consm(n, ns) : List<&2, B.Note>})

# Small facts
# ===========

law fs_pre:
  for +s: String
  for +f: R.Flush
  {fs(R.Flush.pre(s, f)) == fspre(s, fs(f)) : FS}

def fs_pre(s, f):
  match f:
    case R.Flushed{+o, +l}:
      {==}
    case R.Broke{+o, +b, +p}:
      {==}

def fsl.c(+c: Bool, +x: R.Item, +k: Nat, +p: Nat, +a: B.At, +t1: String, +t2: String, +rest: R.Flush) ->
  {fs(R.flush.put(c, x, Some{R.Item{k, p, a, t1}}, rest)) == fs(R.flush.put(c, x, Some{R.Item{k, p, a, t2}}, rest)) : FS}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# A flush reads only the last item's key and where it came from.
law fs_last:
  for +xs: List<&2, R.Item>
  for +k: Nat
  for +p: Nat
  for +a: B.At
  for +t1: String
  for +t2: String
  {fs(R.flush(xs, Some{R.Item{k, p, a, t1}})) == fs(R.flush(xs, Some{R.Item{k, p, a, t2}})) : FS}

def fs_last(xs, k, p, a, t1, t2):
  match xs:
    case Nil{}:
      {==}
    case Con{R.Item{+k2, +p2, +a2, +t3}, +rest}:
      fsl.c(Nat.is_le(k, k2), R.Item{k2, p2, a2, t3}, k, p, a, t1, t2, R.flush(rest, Some{R.Item{k2, p2, a2, t3}}))

law blank_last:
  for +l: Maybe<&2, NR.Ck>
  for +chrom: String
  {P.blank(NR.spec.last(l, chrom)) == NR.spec.last(l, chrom) : Maybe<&2, R.Item>}

def blank_last(l, chrom):
  match l:
    case None{}:
      {==}
    case Some{NR.Ck{+k, +ip, +ln, +ps, +n}}:
      {==}

law ok_eq:
  for +l: Maybe<&2, NR.Ck>
  for +chrom: String
  for +k: Nat
  {R.flush.ok(NR.spec.last(l, chrom), k) == NR.last_le(l, k) : Bool}

def ok_eq(l, chrom, k):
  match l:
    case None{}:
      {==}
    case Some{NR.Ck{+k2, +ip, +ln, +ps, +n}}:
      {==}

law at_eq:
  for +l: Maybe<&2, NR.Ck>
  for +chrom: String
  {R.at_of(NR.spec.last(l, chrom)) == NR.at_of(l, chrom) : Maybe<&2, B.At>}

def at_eq(l, chrom):
  match l:
    case None{}:
      {==}
    case Some{NR.Ck{+k2, +ip, +ln, +ps, +n}}:
      {==}

law append_ck_nil:
  for +xs: List<&2, NR.Ck>
  {NR.append_ck(xs, Nil{}) == xs : List<&2, NR.Ck>}

def append_ck_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %append_ck_nil(t) : {x <> NR.append_ck(t, Nil{}) == x <> _ : List<&2, NR.Ck>}
      {==}

law len_rev:
  for +xs: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  {List.length(&2, NR.Ck, NR.rev_ck(xs, acc)) == Nat.add(List.length(&2, NR.Ck, xs), List.length(&2, NR.Ck, acc)) : Nat}

def len_rev(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +LTt = List.length(&2, NR.Ck, t)
      +LA = List.length(&2, NR.Ck, acc)
      %Equal.sym(Nat, List.length(&2, NR.Ck, NR.rev_ck(t, x <> acc)), Nat.add(LTt, 1n+LA), len_rev(t, x <> acc)) : {_ == 1n+Nat.add(LTt, LA) : Nat}
      N.add_succ(LTt, LA)

law keys_rev:
  for +xs: List<&2, NR.Ck>
  for +acc: List<&2, NR.Ck>
  for +tl: Nat
  for +h1: {RD.keys_le(xs, tl) == True{} : Bool}
  for +h2: {RD.keys_le(acc, tl) == True{} : Bool}
  {RD.keys_le(NR.rev_ck(xs, acc), tl) == True{} : Bool}

def keys_rev(xs, acc, tl, h1, h2):
  match xs:
    case Nil{}:
      h2
    case Con{+x, +t}:
      keys_rev(t, x <> acc, tl, LM.andr(Nat.is_le(NR.Ck.key(x), tl), RD.keys_le(t, tl), h1),
        LM.and_mk(Nat.is_le(NR.Ck.key(x), tl), RD.keys_le(acc, tl), LM.andl(Nat.is_le(NR.Ck.key(x), tl), RD.keys_le(t, tl), h1), h2))

law app_assoc_n:
  for +xs: List<&2, B.Note>
  for +ys: List<&2, B.Note>
  for +zs: List<&2, B.Note>
  {List.append(&2, B.Note, List.append(&2, B.Note, xs, ys), zs) == List.append(&2, B.Note, xs, List.append(&2, B.Note, ys, zs)) : List<&2, B.Note>}

def app_assoc_n(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %app_assoc_n(t, ys, zs) : {x <> List.append(&2, B.Note, List.append(&2, B.Note, t, ys), zs) == x <> _ : List<&2, B.Note>}
      {==}

law rev_go:
  for +xs: List<&2, B.Note>
  for +acc: List<&2, B.Note>
  {List.reverse.go(&2, B.Note, xs, acc) == List.append(&2, B.Note, List.reverse.go(&2, B.Note, xs, Nil{}), acc) : List<&2, B.Note>}

def rev_go(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +RT = List.reverse.go(&2, B.Note, t, Nil{})
      %Equal.sym(List<&2, B.Note>, List.reverse.go(&2, B.Note, t, y <> acc), List.append(&2, B.Note, RT, y <> acc), rev_go(t, y <> acc)) : {_ == List.append(&2, B.Note, List.reverse.go(&2, B.Note, t, [y]), acc) : List<&2, B.Note>}
      %Equal.sym(List<&2, B.Note>, List.reverse.go(&2, B.Note, t, [y]), List.append(&2, B.Note, RT, [y]), rev_go(t, [y])) : {List.append(&2, B.Note, RT, y <> acc) == List.append(&2, B.Note, _, acc) : List<&2, B.Note>}
      Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, RT, [y]), acc), List.append(&2, B.Note, RT, y <> acc), app_assoc_n(RT, [y], acc))

law rev_cons:
  for +x: B.Note
  for +xs: List<&2, B.Note>
  {List.reverse(&2, B.Note, x <> xs) == List.append(&2, B.Note, List.reverse(&2, B.Note, xs), [x]) : List<&2, B.Note>}

def rev_cons(x, xs):
  rev_go(xs, [x])

# The first item ready (or all): written, the rest decides.
def tr_t(+all: Bool, +w: Nat, +inpos: Nat, +it: R.Item, +rest: List<&2, R.Item>,
  +hrd: {Bool.or(all, R.ready(w, inpos, it)) == True{} : Bool}) ->
  {TRd(all, w, inpos, it <> rest) == it <> TRd(all, w, inpos, rest) : List<&2, R.Item>}
  & {DRd(all, w, inpos, it <> rest) == DRd(all, w, inpos, rest) : List<&2, R.Item>}:
  match all:
    case True{}:
      ({==}, {==})
    case False{}:
      (AB.subst(Bool, z => {R.take_ready.go(it <> rest, z, w, inpos) == it <> R.take_ready(w, inpos, rest) : List<&2, R.Item>}, True{}, R.ready(w, inpos, it), Equal.sym(Bool, R.ready(w, inpos, it), True{}, hrd), {==}),
       AB.subst(Bool, z => {R.drop_ready.go(it <> rest, z, w, inpos) == R.drop_ready(w, inpos, rest) : List<&2, R.Item>}, True{}, R.ready(w, inpos, it), Equal.sym(Bool, R.ready(w, inpos, it), True{}, hrd), {==}))

# The first item not ready: nothing written.
def tr_f(+all: Bool, +w: Nat, +inpos: Nat, +it: R.Item, +rest: List<&2, R.Item>,
  +hrd: {Bool.or(all, R.ready(w, inpos, it)) == False{} : Bool}) ->
  {TRd(all, w, inpos, it <> rest) == Nil{} : List<&2, R.Item>}
  & {DRd(all, w, inpos, it <> rest) == it <> rest : List<&2, R.Item>}:
  match all:
    case True{}:
      Empty.absurd({TRd(True{}, w, inpos, it <> rest) == Nil{} : List<&2, R.Item>} & {DRd(True{}, w, inpos, it <> rest) == it <> rest : List<&2, R.Item>},
        AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hrd)))
    case False{}:
      (AB.subst(Bool, z => {R.take_ready.go(it <> rest, z, w, inpos) == Nil{} : List<&2, R.Item>}, False{}, R.ready(w, inpos, it), Equal.sym(Bool, R.ready(w, inpos, it), False{}, hrd), {==}),
       AB.subst(Bool, z => {R.drop_ready.go(it <> rest, z, w, inpos) == it <> rest : List<&2, R.Item>}, False{}, R.ready(w, inpos, it), Equal.sym(Bool, R.ready(w, inpos, it), False{}, hrd), {==}))

# One item written first: its text s comes before the rest's.
def lift(x: FS, +s: String, +chrom: String, +text: String, +ow: U32, +owr: U32, +ns: List<&2, B.Note>, +dr: List<&2, R.Item>,
  +l2: Maybe<&2, NR.Ck>, +f2: List<&2, NR.Ck>, +b2: List<&2, NR.Ck>, +ow2: U32, +ns2: List<&2, B.Note>, +x2: Bool,
  +er: {String.take(text, U32.to_nat(owr)) == String.append(String.take(text, U32.to_nat(ow)), s) : String},
  h: FLR(x, chrom, text, owr, ns, dr, l2, f2, b2, ow2, ns2, x2)) ->
  FLR(fspre(s, x), chrom, text, ow, ns, dr, l2, f2, b2, ow2, ns2, x2):
  match x:
    case FS{False{}, +o, +n, +la}:
      (a1, q1) = h
      (a2, q2) = q1
      (a3, q3) = q2
      (a4, a5) = q3
      +A = String.take(text, U32.to_nat(ow))
      (a1, (Equal.trans(String, String.take(text, U32.to_nat(ow2)), String.append(String.take(text, U32.to_nat(owr)), o), String.append(A, String.append(s, o)), a2,
        Equal.trans(String, String.append(String.take(text, U32.to_nat(owr)), o), String.append(String.append(A, s), o), String.append(A, String.append(s, o)),
          Equal.cong(String, String, z => String.append(z, o), String.take(text, U32.to_nat(owr)), String.append(A, s), er), RBS.s_append_assoc(A, s, o))), (a3, (a4, a5))))
    case FS{True{}, +o, +n, +la}:
      (a1, q1) = h
      (a2, a3) = q1
      +A = String.take(text, U32.to_nat(ow))
      (a1, (Equal.trans(String, String.take(text, U32.to_nat(ow2)), String.append(String.take(text, U32.to_nat(owr)), o), String.append(A, String.append(s, o)), a2,
        Equal.trans(String, String.append(String.take(text, U32.to_nat(owr)), o), String.append(String.append(A, s), o), String.append(A, String.append(s, o)),
          Equal.cong(String, String, z => String.append(z, o), String.take(text, U32.to_nat(owr)), String.append(A, s), er), RBS.s_append_assoc(A, s, o))), a3))

# The loop's result from the state (L front, b0 back), fuel steps.
def LoopR(+fuel: Nat, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>,
  +w: Nat, +inpos: Nat, +all: Bool, +xs: List<&2, NR.Ck>) -> Type:
  &l2: Maybe<&2, NR.Ck> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &ow2: U32 -> &ns2: List<&2, B.Note> -> &x2: Bool ->
  ({NR.flush.go(fuel, NR.Fl{P.mkRun(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b0, bn, tl, k, obl, obt, ow, ns, False{}}), True{}}, w, inpos, all) == P.mkRun(P.RunP{n, i, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, x2}) : NR.Run}
  & ({RD.inv.k(i, h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, x2) == True{} : Bool}
  & FLR(fs(R.flush(TRd(all, w, inpos, ISS(xs, c, obl, obt, ow)), NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, ISS(xs, c, obl, obt, ow)), l2, f2, b2, ow2, ns2, x2)))

# The same from one step in: fr the front list, the run's front emptied.
def LoopC(+g: Nat, +fr: List<&2, NR.Ck>, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>,
  +w: Nat, +inpos: Nat, +all: Bool, +xs: List<&2, NR.Ck>) -> Type:
  &l2: Maybe<&2, NR.Ck> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &ow2: U32 -> &ns2: List<&2, B.Note> -> &x2: Bool ->
  ({NR.flush.go(g, NR.flush.front(fr, NR.Run{n, i, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}, w, inpos, all), w, inpos, all) == P.mkRun(P.RunP{n, i, h, c, cbl, cbt, e, l2, f2, b2, bn2, tl, k, obl, obt, ow2, ns2, x2}) : NR.Run}
  & ({RD.inv.k(i, h, c, cbl, cbt, f2, b2, bn2, tl, obl, obt, ow2, ns2, x2) == True{} : Bool}
  & FLR(fs(R.flush(TRd(all, w, inpos, ISS(xs, c, obl, obt, ow)), NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, ISS(xs, c, obl, obt, ow)), l2, f2, b2, ow2, ns2, x2)))

def pf(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def ps(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# The first item not ready (all is False): nothing written, the run as it was.
def cc.nr(+g2: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == False{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) -> LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  +ST = {P.RunP{n, True{}, h, c, cbl, cbt, e, l, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, k, obl, obt, ow, ns, False{}} : P.RunP}
  +eq = AB.subst(Bool, z => {NR.flush.go(1n+g2, NR.flush.head(z, NR.Run{n, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}, NR.Ck{ky, ipy, lny, psy, ny}, ys), w, inpos, all) == P.mkRun(ST) : NR.Run}, False{}, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), Equal.sym(Bool, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), False{}, hrd), {==})
  +e1 = pf({TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == Nil{} : List<&2, R.Item>}, {DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) : List<&2, R.Item>}, tr_f(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), hrd))
  +e2 = ps({TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == Nil{} : List<&2, R.Item>}, {DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) : List<&2, R.Item>}, tr_f(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), hrd))
  flr1 = AB.subst(List<&2, R.Item>, z => FLR(fs(R.flush(z, NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), l, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, ow, ns, False{}), Nil{}, TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Equal.sym(List<&2, R.Item>, TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Nil{}, e1),
    ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), ({==}, (Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l, chromof(c))), NR.spec.last(l, chromof(c)), blank_last(l, chromof(c))), {==})))))
  flr2 = AB.subst(List<&2, R.Item>, z => FLR(fs(R.flush(TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, z, l, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, ow, ns, False{}), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Equal.sym(List<&2, R.Item>, DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), e2), flr1)
  (l, (Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, (b0, (bn, (ow, (ns, (False{}, (eq, (hi, flr2)))))))))


# The first item ready but below the last written: UNSORTED.
def cc.stop(+g2: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == True{} : Bool},
  +hokb: {NR.last_le(l, ky) == False{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) -> LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  +RHS = {P.RunP{n, True{}, h, c, cbl, cbt, e, l, Nil{}, b0, bn, tl, k, obl, obt, ow, B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, NR.at_of(l, chromof(c))} <> ns, True{}} : P.RunP}
  +eq1 = AB.subst(Bool, z => {NR.flush.go(1n+g2, NR.flush.one(z, NR.Run{n, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}, NR.Ck{ky, ipy, lny, psy, ny}, ys), w, inpos, all) == P.mkRun(RHS) : NR.Run}, False{}, NR.last_le(l, ky), Equal.sym(Bool, NR.last_le(l, ky), False{}, hokb), {==})
  +eq = AB.subst(Bool, z => {NR.flush.go(1n+g2, NR.flush.head(z, NR.Run{n, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}, NR.Ck{ky, ipy, lny, psy, ny}, ys), w, inpos, all) == P.mkRun(RHS) : NR.Run}, True{}, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), Equal.sym(Bool, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), True{}, hrd), eq1)
  +hinv = PI.inv_mk(True{}, h, c, cbl, cbt, Nil{}, b0, bn, tl, obl, obt, ow, B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, NR.at_of(l, chromof(c))} <> ns, True{},
    (PI.pr1(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr2(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr3(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr4(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), ({==}, ({==}, ({==}, (PI.pr8(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr9(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi), ({==}, PI.pr11(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi))))))))))))
  +e1 = pf({TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, {DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, tr_t(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), hrd))
  +eok = Equal.trans(Bool, R.flush.ok(NR.spec.last(l, chromof(c)), ky), NR.last_le(l, ky), False{}, ok_eq(l, chromof(c), ky), hokb)
  +nseq = Equal.cong(Maybe<&2, B.At>, List<&2, B.Note>, z => B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, z} <> ns, NR.at_of(l, chromof(c)), R.at_of(NR.spec.last(l, chromof(c))), Equal.sym(Maybe<&2, B.At>, R.at_of(NR.spec.last(l, chromof(c))), NR.at_of(l, chromof(c)), at_eq(l, chromof(c))))
  flr1 = AB.subst(Bool, z => FLR(fs(R.flush.put(z, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.last(l, chromof(c)), R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l, Nil{}, b0, ow, B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, NR.at_of(l, chromof(c))} <> ns, True{}), False{}, R.flush.ok(NR.spec.last(l, chromof(c)), ky), Equal.sym(Bool, R.flush.ok(NR.spec.last(l, chromof(c)), ky), False{}, eok),
    ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), nseq)))
  flr2 = AB.subst(List<&2, R.Item>, z => FLR(fs(R.flush(z, NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l, Nil{}, b0, ow, B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, NR.at_of(l, chromof(c))} <> ns, True{}), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Equal.sym(List<&2, R.Item>, TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), e1), flr1)
  (l, (Nil{}, (b0, (bn, (ow, (B.Stop{B.Unsorted{}, Some{NR.Ck.at(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c))}, NR.at_of(l, chromof(c))} <> ns, (True{}, (eq, (hinv, flr2)))))))))


def cc.go.k(+g2: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn2: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == True{} : Bool},
  +hokb: {NR.last_le(l, ky) == True{} : Bool},
  +eadd: {U32.to_nat((ow + ny : U32)) == Nat.add(U32.to_nat(ow), U32.to_nat(ny)) : Nat},
  rr: LoopR(1n+g2, n, True{}, h, c, cbl, cbt, e, Some{NR.Ck{ky, ipy, lny, psy, ny}}, ys, b0, bn2, tl, k, obl, obt, (ow + ny : U32), ns, w, inpos, all, RD.items(ys, b0))) -> LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, 1n+bn2, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  (+l2, q1) = rr
  (+f2, q2) = q1
  (+b2, q3) = q2
  (+bn3, q4) = q3
  (+ow2, q5) = q4
  (+ns2, q6) = q5
  (+x2, q7) = q6
  (eqr, q8) = q7
  (invr, flrr) = q8
  +RHS = {P.RunP{n, True{}, h, c, cbl, cbt, e, l2, f2, b2, bn3, tl, k, obl, obt, ow2, ns2, x2} : P.RunP}
  +eq1 = AB.subst(Bool, z => {NR.flush.go(1n+g2, NR.flush.one(z, NR.Run{n, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, 1n+bn2, tl, k, C.BT(obl, obt), ow, ns, False{}}, NR.Ck{ky, ipy, lny, psy, ny}, ys), w, inpos, all) == P.mkRun(RHS) : NR.Run}, True{}, NR.last_le(l, ky), Equal.sym(Bool, NR.last_le(l, ky), True{}, hokb), eqr)
  +eq = AB.subst(Bool, z => {NR.flush.go(1n+g2, NR.flush.head(z, NR.Run{n, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, b0, 1n+bn2, tl, k, C.BT(obl, obt), ow, ns, False{}}, NR.Ck{ky, ipy, lny, psy, ny}, ys), w, inpos, all) == P.mkRun(RHS) : NR.Run}, True{}, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), Equal.sym(Bool, Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), True{}, hrd), eq1)
  +eDrop = Equal.trans(String, String.drop(TXT(obl, obt), U32.to_nat((ow + ny : U32))), String.drop(TXT(obl, obt), Nat.add(U32.to_nat(ow), U32.to_nat(ny))), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)),
    Equal.cong(Nat, String, z => String.drop(TXT(obl, obt), z), U32.to_nat((ow + ny : U32)), Nat.add(U32.to_nat(ow), U32.to_nat(ny)), eadd), BF.str_drop_add(TXT(obl, obt), U32.to_nat(ow), U32.to_nat(ny)))
  +eTake = Equal.trans(String, String.take(TXT(obl, obt), U32.to_nat((ow + ny : U32))), String.take(TXT(obl, obt), Nat.add(U32.to_nat(ow), U32.to_nat(ny))), String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))),
    Equal.cong(Nat, String, z => String.take(TXT(obl, obt), z), U32.to_nat((ow + ny : U32)), Nat.add(U32.to_nat(ow), U32.to_nat(ny)), eadd), BF.str_take_add(TXT(obl, obt), U32.to_nat(ow), U32.to_nat(ny)))
  flr1 = AB.subst(String, z => FLR(fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), z)), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), "")})), chromof(c), TXT(obl, obt), (ow + ny : U32), ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), z)), l2, f2, b2, ow2, ns2, x2),
    String.drop(TXT(obl, obt), U32.to_nat((ow + ny : U32))), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), eDrop, flrr)
  flr2 = lift(fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), "")})), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), chromof(c), TXT(obl, obt), ow, (ow + ny : U32), ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l2, f2, b2, ow2, ns2, x2, eTake, flr1)
  +efl = fs_last(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), ky, ipy, B.At{lny, chromof(c), NR.pos_text(psy, ky)}, String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), "")
  flr3 = AB.subst(FS, z => FLR(fspre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), z), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l2, f2, b2, ow2, ns2, x2), fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), "")})), fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))})), Equal.sym(FS, fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))})), fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), "")})), efl), flr2)
  flr4 = AB.subst(FS, z => FLR(z, chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l2, f2, b2, ow2, ns2, x2), fspre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), fs(R.Flush.pre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))),
    Equal.sym(FS, fs(R.Flush.pre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), fspre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), fs(R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), fs_pre(String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)), R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), flr3)
  +eok = Equal.trans(Bool, R.flush.ok(NR.spec.last(l, chromof(c)), ky), NR.last_le(l, ky), True{}, ok_eq(l, chromof(c), ky), hokb)
  flr5 = AB.subst(Bool, z => FLR(fs(R.flush.put(z, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.last(l, chromof(c)), R.flush(TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Some{NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))}))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l2, f2, b2, ow2, ns2, x2), True{}, R.flush.ok(NR.spec.last(l, chromof(c)), ky), Equal.sym(Bool, R.flush.ok(NR.spec.last(l, chromof(c)), ky), True{}, eok), flr4)
  +e1 = pf({TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, {DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, tr_t(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), hrd))
  +e2 = ps({TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, {DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) == DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))) : List<&2, R.Item>}, tr_t(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))), hrd))
  flr6 = AB.subst(List<&2, R.Item>, z => FLR(fs(R.flush(z, NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), l2, f2, b2, ow2, ns2, x2), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Equal.sym(List<&2, R.Item>, TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> TRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), e1), flr5)
  flr7 = AB.subst(List<&2, R.Item>, z => FLR(fs(R.flush(TRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), NR.spec.last(l, chromof(c)))), chromof(c), TXT(obl, obt), ow, ns, z, l2, f2, b2, ow2, ns2, x2), DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), Equal.sym(List<&2, R.Item>, DRd(all, w, inpos, NR.spec.item(NR.Ck{ky, ipy, lny, psy, ny}, chromof(c), String.take(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny))) <> NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), DRd(all, w, inpos, NR.spec.items(RD.items(ys, b0), chromof(c), String.drop(String.drop(TXT(obl, obt), U32.to_nat(ow)), U32.to_nat(ny)))), e2), flr6)
  (l2, (f2, (b2, (bn3, (ow2, (ns2, (x2, (eq, (invr, flr7)))))))))

def F31() -> U32:
  1073741824

# The first item ready and in order: written, then the loop goes on.
def cc.go(+g2: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn2: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == True{} : Bool},
  +hokb: {NR.last_le(l, ky) == True{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  ih: @bn2:Nat -> @ow2:U32 -> {RD.inv.k(True{}, h, c, cbl, cbt, ys, b0, bn2, tl, obl, obt, ow2, ns, False{}) == True{} : Bool} -> LoopR(1n+g2, n, True{}, h, c, cbl, cbt, e, Some{NR.Ck{ky, ipy, lny, psy, ny}}, ys, b0, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, RD.items(ys, b0))) -> LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, 1n+bn2, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  +LS1 = RD.lens(RD.items(ys, b0))
  +A = U32.to_nat(ow)
  +Bn = U32.to_nat(ny)
  +M = Nat.mul(4n, Nat.pow(2n, 29n))
  +esum = N.eq_sound(Nat.add(A, Nat.add(Bn, LS1)), U32.to_nat(obl), PI.pr5(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi))
  +hob = Equal.trans(Bool, Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U32.is_le(obl, F31()), True{},
    Equal.sym(Bool, U32.is_le(obl, F31()), Nat.is_le(U32.to_nat(obl), U32.to_nat(F31())), U.is_le_to_nat(obl, F31())), PI.pr2(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi))
  +h30 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(obl), y) == True{} : Bool}, U32.to_nat(F31()), Nat.pow(2n, 30n), PL.lit_pow(30n, F31(), {==}, {==}), hob)
  +hoM = N.le_trans(U32.to_nat(obl), Nat.add(U32.to_nat(obl), 8n), M, N.le_add_r(U32.to_nat(obl), 8n), N.lt_to_le(Nat.add(U32.to_nat(obl), 8n), M, SZ.lt31(U32.to_nat(obl), h30)))
  +hab0 = N.le_add_mono_l(A, Bn, Nat.add(Bn, LS1), N.le_add_r(Bn, LS1))
  +hab1 = AB.subst(Nat, y => {Nat.is_le(Nat.add(A, Bn), y) == True{} : Bool}, Nat.add(A, Nat.add(Bn, LS1)), U32.to_nat(obl), esum, hab0)
  +eadd = C.add_fits(ow, ny, 29n, {==}, N.le_trans(Nat.add(A, Bn), U32.to_nat(obl), M, hab1, hoM))
  +esum1 = Equal.trans(Nat, Nat.add(U32.to_nat((ow + ny : U32)), LS1), Nat.add(Nat.add(A, Bn), LS1), U32.to_nat(obl),
    Equal.cong(Nat, Nat, z => Nat.add(z, LS1), U32.to_nat((ow + ny : U32)), Nat.add(A, Bn), eadd),
    Equal.trans(Nat, Nat.add(Nat.add(A, Bn), LS1), Nat.add(A, Nat.add(Bn, LS1)), U32.to_nat(obl), N.add_assoc(A, Bn, LS1), esum))
  +h5r = AB.subst(Nat, y => {Nat.is_eq(Nat.add(U32.to_nat((ow + ny : U32)), LS1), y) == True{} : Bool}, Nat.add(U32.to_nat((ow + ny : U32)), LS1), U32.to_nat(obl), esum1, N.eq_refl(Nat.add(U32.to_nat((ow + ny : U32)), LS1)))
  +h7r = LM.andr(Nat.is_le(ky, tl), RD.keys_le(ys, tl), PI.pr7(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi))
  +h11r = AB.subst(Nat, y => {Nat.is_le(U32.to_nat((ow + ny : U32)), y) == True{} : Bool}, Nat.add(U32.to_nat((ow + ny : U32)), LS1), U32.to_nat(obl), esum1, N.le_add_r(U32.to_nat((ow + ny : U32)), LS1))
  +hir = PI.inv_mk(True{}, h, c, cbl, cbt, ys, b0, bn2, tl, obl, obt, (ow + ny : U32), ns, False{},
    (PI.pr1(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (PI.pr2(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (PI.pr3(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (PI.pr4(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (h5r, (PI.pr6(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (h7r, (PI.pr8(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), (PI.pr9(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 1n+bn2, tl, obl, obt, ow, ns, False{}, hi), ({==}, h11r)))))))))))
  cc.go.k(g2, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, bn2, tl, k, obl, obt, ow, ns, w, inpos, all, hrd, hokb, eadd, ih(bn2, (ow + ny : U32), hir))

def cc.ok(+okb: Bool, +bn: Nat, +g2: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hokb: {NR.last_le(l, ky) == okb : Bool},
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == True{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  ih: @bn2:Nat -> @ow2:U32 -> {RD.inv.k(True{}, h, c, cbl, cbt, ys, b0, bn2, tl, obl, obt, ow2, ns, False{}) == True{} : Bool} -> LoopR(1n+g2, n, True{}, h, c, cbl, cbt, e, Some{NR.Ck{ky, ipy, lny, psy, ny}}, ys, b0, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, RD.items(ys, b0))) -> LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  match okb bn:
    case False{} _:
      cc.stop(g2, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, hrd, hokb, hi)
    case True{} 0n:
      Empty.absurd(LoopC(1n+g2, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, 0n, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)), AB.false_ne_true(PI.pr6(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, 0n, tl, obl, obt, ow, ns, False{}, hi)))
    case True{} 1n+bn2:
      cc.go(g2, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, bn2, tl, k, obl, obt, ow, ns, w, inpos, all, hrd, hokb, hi, ih)

def cc.rd(+rd: Bool, +g: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +ky: Nat, +ipy: Nat, +lny: Nat, +psy: Maybe<&2, String>, +ny: U32, +ys: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hrd: {Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)) == rd : Bool},
  +hfuel: {Nat.is_lt(Nat.add(List.length(&2, NR.Ck, ys), List.length(&2, NR.Ck, b0)), g) == True{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  ih: @bn2:Nat -> @ow2:U32 -> {RD.inv.k(True{}, h, c, cbl, cbt, ys, b0, bn2, tl, obl, obt, ow2, ns, False{}) == True{} : Bool} -> LoopR(g, n, True{}, h, c, cbl, cbt, e, Some{NR.Ck{ky, ipy, lny, psy, ny}}, ys, b0, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, RD.items(ys, b0))) -> LoopC(g, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)):
  match rd g:
    case _ 0n:
      Empty.absurd(LoopC(0n, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, n, True{}, h, c, cbl, cbt, e, l, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, b0)), AB.lt_zero_absurd(Nat.add(List.length(&2, NR.Ck, ys), List.length(&2, NR.Ck, b0)), hfuel))
    case False{} 1n+g2:
      cc.nr(g2, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, hrd, hi)
    case True{} 1n+g2:
      cc.ok(NR.last_le(l, ky), bn, g2, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, tl, k, obl, obt, ow, ns, w, inpos, all, {==}, hrd, hi, ih)

law lt_add2:
  for +x: Nat
  {Nat.is_lt(x, Nat.add(x, 2n)) == True{} : Bool}

def lt_add2(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      lt_add2(p)

# The back list reversed into the front (z :: zs back, reversed y :: ys).
def lp.rev2(+g: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>,
  +z: NR.Ck, +zs: List<&2, NR.Ck>, +y: NR.Ck, +ys: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +ev: {NR.rev_ck(zs, [z]) == Con{y, ys} : List<&2, NR.Ck>},
  +hfuel: {Nat.is_lt(List.length(&2, NR.Ck, zs), g) == True{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  ihg: @yy:NR.Ck -> @yss:List<&2, NR.Ck> -> {Nat.is_lt(Nat.add(List.length(&2, NR.Ck, yss), 0n), g) == True{} : Bool} -> @bn2:Nat -> @ow2:U32 -> {RD.inv.k(True{}, h, c, cbl, cbt, yss, Nil{}, bn2, tl, obl, obt, ow2, ns, False{}) == True{} : Bool} -> LoopR(g, n, True{}, h, c, cbl, cbt, e, Some{yy}, yss, Nil{}, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, RD.items(yss, Nil{}))) -> LoopC(g, NR.rev_ck(zs, [z]), n, True{}, h, c, cbl, cbt, e, l, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Nil{}, Con{z, zs})):
  match y:
    case NR.Ck{+ky, +ipy, +lny, +psy, +ny}:
      +ly = Equal.trans(Nat, 1n+List.length(&2, NR.Ck, zs), Nat.add(List.length(&2, NR.Ck, zs), 1n), 1n+List.length(&2, NR.Ck, ys),
        Equal.sym(Nat, Nat.add(List.length(&2, NR.Ck, zs), 1n), 1n+List.length(&2, NR.Ck, zs), N.add_one(List.length(&2, NR.Ck, zs))),
        Equal.trans(Nat, Nat.add(List.length(&2, NR.Ck, zs), 1n), List.length(&2, NR.Ck, NR.rev_ck(zs, [z])), 1n+List.length(&2, NR.Ck, ys),
          Equal.sym(Nat, List.length(&2, NR.Ck, NR.rev_ck(zs, [z])), Nat.add(List.length(&2, NR.Ck, zs), 1n), len_rev(zs, [z])),
          Equal.cong(List<&2, NR.Ck>, Nat, q => List.length(&2, NR.Ck, q), NR.rev_ck(zs, [z]), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, ev)))
      +lzy = N.succ_inj(List.length(&2, NR.Ck, zs), List.length(&2, NR.Ck, ys), ly)
      +hf2 = AB.subst(Nat, q => {Nat.is_lt(q, g) == True{} : Bool}, List.length(&2, NR.Ck, zs), Nat.add(List.length(&2, NR.Ck, ys), 0n),
        Equal.trans(Nat, List.length(&2, NR.Ck, zs), List.length(&2, NR.Ck, ys), Nat.add(List.length(&2, NR.Ck, ys), 0n), lzy, Equal.sym(Nat, Nat.add(List.length(&2, NR.Ck, ys), 0n), List.length(&2, NR.Ck, ys), N.add_zero(List.length(&2, NR.Ck, ys)))), hfuel)
      +eXS = Equal.trans(List<&2, NR.Ck>, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{}), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, RD.items(Nil{}, Con{z, zs}), append_ck_nil(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}), Equal.sym(List<&2, NR.Ck>, NR.rev_ck(zs, [z]), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, ev))
      +h5 = AB.subst(List<&2, NR.Ck>, q => {Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(q)), U32.to_nat(obl)) == True{} : Bool}, RD.items(Nil{}, Con{z, zs}), RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{}),
        Equal.sym(List<&2, NR.Ck>, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{}), RD.items(Nil{}, Con{z, zs}), eXS), PI.pr5(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi))
      +h6 = AB.subst(Nat, q => {Nat.is_eq(bn, 1n+q) == True{} : Bool}, List.length(&2, NR.Ck, zs), Nat.add(List.length(&2, NR.Ck, ys), 0n),
        Equal.trans(Nat, List.length(&2, NR.Ck, zs), List.length(&2, NR.Ck, ys), Nat.add(List.length(&2, NR.Ck, ys), 0n), lzy, Equal.sym(Nat, Nat.add(List.length(&2, NR.Ck, ys), 0n), List.length(&2, NR.Ck, ys), N.add_zero(List.length(&2, NR.Ck, ys)))),
        PI.pr6(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi))
      +hkz = PI.pr8(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi)
      +hk7 = AB.subst(List<&2, NR.Ck>, q => {RD.keys_le(q, tl) == True{} : Bool}, NR.rev_ck(zs, [z]), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, ev,
        keys_rev(zs, [z], tl, LM.andr(Nat.is_le(NR.Ck.key(z), tl), RD.keys_le(zs, tl), hkz), LM.and_mk(Nat.is_le(NR.Ck.key(z), tl), True{}, LM.andl(Nat.is_le(NR.Ck.key(z), tl), RD.keys_le(zs, tl), hkz), {==})))
      +hi2 = PI.inv_mk(True{}, h, c, cbl, cbt, Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{}, bn, tl, obl, obt, ow, ns, False{},
        (PI.pr1(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr2(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr3(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr4(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi), (h5, (h6, (hk7, ({==}, (PI.pr9(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi), ({==}, PI.pr11(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}, hi))))))))))))
      AB.subst(List<&2, NR.Ck>, q => LoopC(g, NR.rev_ck(zs, [z]), n, True{}, h, c, cbl, cbt, e, l, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, q), RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{}), RD.items(Nil{}, Con{z, zs}), eXS,
        AB.subst(List<&2, NR.Ck>, q => LoopC(g, q, n, True{}, h, c, cbl, cbt, e, l, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, Nil{})), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, NR.rev_ck(zs, [z]), Equal.sym(List<&2, NR.Ck>, NR.rev_ck(zs, [z]), Con{NR.Ck{ky, ipy, lny, psy, ny}, ys}, ev),
          cc.rd(Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), g, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, {==}, hf2, hi2, ihg(NR.Ck{ky, ipy, lny, psy, ny}, ys, hf2))))

def lp.rev(+g: Nat, +n: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>,
  +z: NR.Ck, +zs: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hfuel: {Nat.is_lt(List.length(&2, NR.Ck, zs), g) == True{} : Bool},
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, Nil{}, Con{z, zs}, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  ihg: @yy:NR.Ck -> @yss:List<&2, NR.Ck> -> {Nat.is_lt(Nat.add(List.length(&2, NR.Ck, yss), 0n), g) == True{} : Bool} -> @bn2:Nat -> @ow2:U32 -> {RD.inv.k(True{}, h, c, cbl, cbt, yss, Nil{}, bn2, tl, obl, obt, ow2, ns, False{}) == True{} : Bool} -> LoopR(g, n, True{}, h, c, cbl, cbt, e, Some{yy}, yss, Nil{}, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, RD.items(yss, Nil{})),
  rr: &y: NR.Ck -> &ys: List<&2, NR.Ck> -> {NR.rev_ck(zs, [z]) == Con{y, ys} : List<&2, NR.Ck>}) -> LoopC(g, NR.rev_ck(zs, [z]), n, True{}, h, c, cbl, cbt, e, l, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Nil{}, Con{z, zs})):
  (+y, q) = rr
  (+ys, ev) = q
  lp.rev2(g, n, h, c, cbl, cbt, e, l, z, zs, y, ys, bn, tl, k, obl, obt, ow, ns, w, inpos, all, ev, hfuel, hi, ihg)

# The buffer empty: nothing to write.
def lp.done(+g: Nat, +all: Bool, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat,
  +hi: {RD.inv.k(i, h, c, cbl, cbt, Nil{}, Nil{}, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) ->
  LoopR(1n+g, n, i, h, c, cbl, cbt, e, l, Nil{}, Nil{}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Nil{}, Nil{})):
  match g all:
    case 0n True{}:
      (l, (Nil{}, (Nil{}, (bn, (ow, (ns, (False{}, ({==}, (hi, ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), ({==}, (Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l, chromof(c))), NR.spec.last(l, chromof(c)), blank_last(l, chromof(c))), {==})))))))))))))
    case 0n False{}:
      (l, (Nil{}, (Nil{}, (bn, (ow, (ns, (False{}, ({==}, (hi, ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), ({==}, (Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l, chromof(c))), NR.spec.last(l, chromof(c)), blank_last(l, chromof(c))), {==})))))))))))))
    case 1n+g2 True{}:
      (l, (Nil{}, (Nil{}, (bn, (ow, (ns, (False{}, ({==}, (hi, ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), ({==}, (Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l, chromof(c))), NR.spec.last(l, chromof(c)), blank_last(l, chromof(c))), {==})))))))))))))
    case 1n+g2 False{}:
      (l, (Nil{}, (Nil{}, (bn, (ow, (ns, (False{}, ({==}, (hi, ({==}, (Equal.sym(String, String.append(String.take(TXT(obl, obt), U32.to_nat(ow)), ""), String.take(TXT(obl, obt), U32.to_nat(ow)), RBS.s_append_nil(String.take(TXT(obl, obt), U32.to_nat(ow)))), ({==}, (Equal.sym(Maybe<&2, R.Item>, P.blank(NR.spec.last(l, chromof(c))), NR.spec.last(l, chromof(c)), blank_last(l, chromof(c))), {==})))))))))))))

# The loop: fuel more than the buffered items.
def loop(+fuel: Nat, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hfuel: {Nat.is_lt(Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b0)), fuel) == True{} : Bool},
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) -> LoopR(fuel, n, i, h, c, cbl, cbt, e, l, f, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(f, b0)):
  match fuel i f b0:
    case 0n _ _ _:
      Empty.absurd(LoopR(0n, n, i, h, c, cbl, cbt, e, l, f, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(f, b0)), AB.lt_zero_absurd(Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b0)), hfuel))
    case 1n+g _ Nil{} Nil{}:
      lp.done(g, all, n, i, h, c, cbl, cbt, e, l, bn, tl, k, obl, obt, ow, ns, w, inpos, hi)
    case 1n+g False{} Con{+y, +ys} _:
      Empty.absurd(LoopR(1n+g, n, False{}, h, c, cbl, cbt, e, l, Con{y, ys}, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Con{y, ys}, b0)), AB.false_ne_true(LM.andr(U32.is_zero(obl), False{} && (RD.is_nil(b0) && (False{} || RD.no_notes(ns))), PI.pr10(False{}, h, c, cbl, cbt, Con{y, ys}, b0, bn, tl, obl, obt, ow, ns, False{}, hi))))
    case 1n+g False{} Nil{} Con{+y, +ys}:
      Empty.absurd(LoopR(1n+g, n, False{}, h, c, cbl, cbt, e, l, Nil{}, Con{y, ys}, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(Nil{}, Con{y, ys})), AB.false_ne_true(LM.andl(False{}, False{} || RD.no_notes(ns), LM.andr(True{}, False{} && (False{} || RD.no_notes(ns)), LM.andr(U32.is_zero(obl), True{} && (False{} && (False{} || RD.no_notes(ns))), PI.pr10(False{}, h, c, cbl, cbt, Nil{}, Con{y, ys}, bn, tl, obl, obt, ow, ns, False{}, hi))))))
    case 1n+g True{} Con{NR.Ck{+ky, +ipy, +lny, +psy, +ny}, +ys} _:
      cc.rd(Bool.or(all, Nat.is_le(Nat.add(ky, w), inpos)), g, n, h, c, cbl, cbt, e, l, ky, ipy, lny, psy, ny, ys, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, {==}, hfuel, hi,
        bn2 => ow2 => hh => loop(g, n, True{}, h, c, cbl, cbt, e, Some{NR.Ck{ky, ipy, lny, psy, ny}}, ys, b0, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, hfuel, hh))
    case 1n+g True{} Nil{} Con{+z, +zs}:
      lp.rev(g, n, h, c, cbl, cbt, e, l, z, zs, bn, tl, k, obl, obt, ow, ns, w, inpos, all, hfuel, hi,
        yy => yss => hf => bn2 => ow2 => hh => loop(g, n, True{}, h, c, cbl, cbt, e, Some{yy}, yss, Nil{}, bn2, tl, k, obl, obt, ow2, ns, w, inpos, all, hf, hh),
        BF.rev_nz(zs, z, Nil{}))

# NR.flush on a pictured run that goes on.
def flush_t(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b0: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +w: Nat, +inpos: Nat, +all: Bool,
  +hi: {RD.inv.k(i, h, c, cbl, cbt, f, b0, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool}) -> LoopR(Nat.add(bn, 2n), n, i, h, c, cbl, cbt, e, l, f, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all, RD.items(f, b0)):
  +X = Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b0))
  +eb = N.eq_sound(bn, X, PI.pr6(i, h, c, cbl, cbt, f, b0, bn, tl, obl, obt, ow, ns, False{}, hi))
  loop(Nat.add(bn, 2n), n, i, h, c, cbl, cbt, e, l, f, b0, bn, tl, k, obl, obt, ow, ns, w, inpos, all,
    AB.subst(Nat, q => {Nat.is_lt(X, Nat.add(q, 2n)) == True{} : Bool}, X, bn, Equal.sym(Nat, bn, X, eb), lt_add2(X)), hi)
