import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as ST
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G

# Phase E, area "seg": what only grows along a run (G.M: the messages and
# the CHROMs started), so a good end state says the states before it were
# good; and the backward fact: an item below l in T's first CHROM run's
# buffer stops T or stays to the end (G.Bad).

law app_ne:
  for +ns: List<&2, B.Note>
  for +x: B.Note
  for +xs: List<&2, B.Note>
  {List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, x <> xs)) == False{} : Bool}

def app_ne(ns, x, xs):
  match ns:
    case Nil{}:
      {==}
    case +y <> +t:
      {==}

law app_empty_l:
  for +ns: List<&2, B.Note>
  for +xs: List<&2, B.Note>
  for h: {List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, xs)) == True{} : Bool}
  {List.is_empty(&2, B.Note, ns) == True{} : Bool}

def app_empty_l(ns, xs, h):
  match ns:
    case Nil{}:
      {==}
    case +y <> +t:
      h

law push_cl:
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  {R.push_cur(c, e) == List.append(&2, String, SD.cur_list(c), e) : List<&2, String>}

def push_cl(c, e):
  match c:
    case None{}:
      {==}
    case Some{+s}:
      {==}

# A state that stopped with a message is not M.
law stop_m:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +nt: B.Note
  for hm: {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, List.append(&2, B.Note, ns, [nt]), x}) == True{} : Bool}
  Empty

def stop_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, nt, hm):
  +e1 = P.and_true_l(List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, [nt])), SD.chroms_ok(List.append(&2, String, SD.cur_list(c), e), c0, se, sc), hm)
  P.false_ne_true(Equal.trans(Bool, False{}, List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, [nt])), True{},
    Equal.sym(Bool, List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, [nt])), False{}, app_ne(ns, nt, Nil{})), e1))

# M of the state before same_run.
law sr_m:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  for hm: {G.M(c0, se, sc, R.same_run(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, it)) == True{} : Bool}
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool}

def sr_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, it, hm):
  ST.SR(s => {G.M(c0, se, sc, s) == True{} : Bool} -> {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
    n, i, h, c, e, l, b, k, o, ns, x, w, it,
    o3 => bad => prev => ef => hm2 => Empty.absurd({G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
      stop_m(c0, se, sc, n, i, h, c, e, l, Nil{}, k, o ++ o3, ns, True{}, B.Stop{B.Unsorted{}, Some{bad}, prev}, hm2)),
    o2 => l2 => ef => hm2 => hm2)(hm)

# The CHROM a new run starts is fresh, and M held before.
law nr_cond:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +chrom: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  for hm: {G.M(c0, se, sc, R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o, ns, x}, w, it)) == True{} : Bool}
  {(String.eq(chrom, c0) || (Bool.not(R.has(chrom, se)) && Bool.not(R.is_cur(sc, chrom)))) == True{} : Bool}

def nr_cond(c0, se, sc, n, i, h, chrom, c, e, k, o, ns, x, w, it, hm):
  +m = sr_m(c0, se, sc, n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o, ns, x, w, it, hm)
  +cond = String.eq(chrom, c0) || (Bool.not(R.has(chrom, se)) && Bool.not(R.is_cur(sc, chrom)))
  +ch = P.and_true_r(List.is_empty(&2, B.Note, ns), Bool.and(cond, SD.chroms_ok(R.push_cur(c, e), c0, se, sc)), m)
  P.and_true_l(cond, SD.chroms_ok(R.push_cur(c, e), c0, se, sc), ch)

law nr_m0:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +chrom: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  for hm: {G.M(c0, se, sc, R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o, ns, x}, w, it)) == True{} : Bool}
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool}

def nr_m0(c0, se, sc, n, i, h, chrom, c, e, l, b, k, o, ns, x, w, it, hm):
  +m = sr_m(c0, se, sc, n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o, ns, x, w, it, hm)
  +cond = String.eq(chrom, c0) || (Bool.not(R.has(chrom, se)) && Bool.not(R.is_cur(sc, chrom)))
  +ch = P.and_true_r(List.is_empty(&2, B.Note, ns), Bool.and(cond, SD.chroms_ok(R.push_cur(c, e), c0, se, sc)), m)
  +ch2 = P.and_true_r(cond, SD.chroms_ok(R.push_cur(c, e), c0, se, sc), ch)
  %push_cl(c, e) :
    {Bool.and(List.is_empty(&2, B.Note, ns), SD.chroms_ok(_, c0, se, sc)) == True{} : Bool}
  S.and_intro(List.is_empty(&2, B.Note, ns), SD.chroms_ok(R.push_cur(c, e), c0, se, sc),
    P.and_true_l(List.is_empty(&2, B.Note, ns), Bool.and(cond, SD.chroms_ok(R.push_cur(c, e), c0, se, sc)), m), ch2)

law nr_m:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +chrom: String
  for +it: R.Item
  for hm: {G.M(c0, se, sc, R.new_run(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)) == True{} : Bool}
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool}

def nr_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, chrom, it, hm):
  ST.NR(s => {G.M(c0, se, sc, s) == True{} : Bool} -> {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
    n, i, h, c, e, l, b, k, o, ns, x, w, chrom, it,
    o3 => bad => prev => ef => hm2 => Empty.absurd({G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
      stop_m(c0, se, sc, n, i, h, c, e, l, b, k, o ++ o3, ns, True{}, B.Stop{B.Unsorted{}, Some{bad}, prev}, hm2)),
    o2 => l2 => ef => eg => hm2 => Empty.absurd({G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool},
      stop_m(c0, se, sc, n, i, h, c, e, l, b, k, o ++ o2, ns, True{}, B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}, hm2)),
    o2 => l2 => ef => eg => hm2 => nr_m0(c0, se, sc, n, i, h, chrom, c, e, l, b, k, o ++ o2, ns, x, w, it, hm2))(hm)

def keyed_m.go(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +g: Bool, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat, +chrom: String, +it: R.Item,
  hm: {G.M(c0, se, sc, R.keyed.go(g, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)) == True{} : Bool}) ->
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool}:
  match g:
    case True{}:
      sr_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, it, hm)
    case False{}:
      nr_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, chrom, it, hm)

# M of the state keyed starts from (its messages and counts).
law keyed_m:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  for hm: {G.M(c0, se, sc, R.keyed(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, it, nts, k2)) == True{} : Bool}
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x}) == True{} : Bool}

def keyed_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, it, nts, k2, hm):
  keyed_m.go(c0, se, sc, R.is_cur(c, R.Item.chrom(it)), n, i, h, c, e, l, b, k2, o, List.append(&2, B.Note, ns, nts), x, w, R.Item.chrom(it), it, hm)

law keyed_m2:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +w: Nat
  for +it: R.Item
  for +nts: List<&2, B.Note>
  for +k2: R.Cnt
  for hm: {G.M(c0, se, sc, R.keyed(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, it, nts, k2)) == True{} : Bool}
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}) == True{} : Bool}

def keyed_m2(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, it, nts, k2, hm):
  +m = keyed_m(c0, se, sc, n, i, h, c, e, l, b, k, o, ns, x, w, it, nts, k2, hm)
  +ch = SD.chroms_ok(List.append(&2, String, SD.cur_list(c), e), c0, se, sc)
  S.and_intro(List.is_empty(&2, B.Note, ns), ch,
    app_empty_l(ns, nts, P.and_true_l(List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, nts)), ch, m)),
    P.and_true_r(List.is_empty(&2, B.Note, List.append(&2, B.Note, ns, nts)), ch, m))

def hl_m(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +isc: Bool, +o: B.Opts, +li: B.Line, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  hm: {G.M(c0, se, sc, R.head_line(isc, R.RunSt{1n+n, False{}, h, c, e, l, b, k, out, ns, False{}}, o, li)) == True{} : Bool}) ->
  {G.M(c0, se, sc, R.RunSt{n, False{}, h, c, e, l, b, k, out, ns, False{}}) == True{} : Bool}:
  match isc li:
    case True{} B.Line{+bd, +term}:
      hm
    case False{} _:
      hm

def good_in(+c0: String, +se: List<&2, String>, +sc: Maybe<&2, String>, +fa: List<&2, B.Contig>, +o: B.Opts, +li: B.Line, +i: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  hm: {G.M(c0, se, sc, L.line_in(i, fa, o, R.RunSt{1n+n, i, h, c, e, l, b, k, out, ns, False{}}, li)) == True{} : Bool}) ->
  {G.M(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, out, ns, False{}}) == True{} : Bool}:
  match i:
    case False{}:
      hl_m(c0, se, sc, R.is_chrom_line(B.Line.body(li)), o, li, n, h, c, e, l, b, k, out, ns, hm)
    case True{}:
      +fs = B.Rec.fields(B.Line.body(li))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +st = {R.RunSt{1n+n, True{}, h, c, e, l, b, k, out, ns, False{}} : R.RunSt}
      -goal = {{G.M(c0, se, sc, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}) == True{} : Bool} : Type}
      ST.BL(s => {G.M(c0, se, sc, s) == True{} : Bool} -> goal, L.judge(fa, B.Line.body(li)), st, o, li, at, B.Rec.pos(fs),
        ST.judge_ok(fa, B.Line.body(li)),
        cd => eu => hm2 => Empty.absurd(goal, stop_m(c0, se, sc, 1n+n, True{}, h, c, e, l, b, k, out ++ "", ns, True{}, B.Stop{cd, Some{at}, None{}}, hm2)),
        nts => k2 => eu => hm2 => keyed_m2(c0, se, sc, 1n+n, True{}, h, c, e, l, b, k, out, ns, False{}, R.Opts.w(o), L.item_of(L.judge(fa, B.Line.body(li)), li, at, B.Rec.pos(fs)), nts, k2, hm2))(hm)

law good_step:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +li: B.Line
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for hg: {G.Good(c0, se, sc, L.line_step(fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}, li)) == True{} : Bool}
  {G.Good(c0, se, sc, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}) == True{} : Bool}

def good_step(c0, se, sc, fa, o, li, n, i, h, c, e, l, b, k, out, ns, x, hg):
  match x:
    case True{}:
      hg
    case False{}:
      +st1 = L.line_step(fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, False{}}, li)
      +hm = P.and_true_r(Bool.not(G.halt(st1)), G.M(c0, se, sc, st1), hg)
      good_in(c0, se, sc, fa, o, li, i, n, h, c, e, l, b, k, out, ns, hm)

# A good end state: every state before it was good.
law good_back:
  for +c0: String
  for +se: List<&2, String>
  for +sc: Maybe<&2, String>
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for hg: {G.Good(c0, se, sc, L.run.go(ls, fa, o, st)) == True{} : Bool}
  {G.Good(c0, se, sc, st) == True{} : Bool}

def good_back(c0, se, sc, ls, fa, o, st, hg):
  match ls:
    case Nil{}:
      hg
    case +li <> +t:
      match st:
        case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +out, +ns, +x}:
          good_step(c0, se, sc, fa, o, li, n, i, h, c, e, l, b, k, out, ns, x,
            good_back(c0, se, sc, t, fa, o, L.line_step(fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}, li), hg))

# doom: an item below l in T's first CHROM run
# =============================================

def lt_chain.go(+a: Nat, +b: Nat, +l: Nat, +v: Bool, ev: {Nat.is_le(l, b) == v : Bool},
  e1: {Nat.is_le(a, b) == False{} : Bool}, e2: {Nat.is_le(l, a) == False{} : Bool}) -> {v == False{} : Bool}:
  match v:
    case True{}:
      +la = Q.le_trans(l, b, a, ev, Q.le_of_s(b, a, Q.le_flip_s(a, b, e1)))
      Empty.absurd({True{} == False{} : Bool}, P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_le(l, a), False{}, Equal.sym(Bool, Nat.is_le(l, a), True{}, la), e2)))
    case False{}:
      {==}

law lt_chain:
  for +a: Nat
  for +b: Nat
  for +l: Nat
  for e1: {Nat.is_le(a, b) == False{} : Bool}
  for e2: {Nat.is_le(l, a) == False{} : Bool}
  {Nat.is_le(l, b) == False{} : Bool}

def lt_chain(a, b, l, e1, e2):
  lt_chain.go(a, b, l, Nat.is_le(l, b), {==}, e1, e2)

law bad_halt:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +l0: Nat
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {G.Bad(l0, L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})) == True{} : Bool}

def bad_halt(ls, fa, o, l0, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.RunSt, L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}), R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}},
    ST.halted_go(ls, fa, o, n, i, h, c, e, l, b, k, out, ns)) : {G.Bad(l0, _) == True{} : Bool}
  {==}

# The IH of doom, for any state of its shape.
def DoomIH(+rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat) -> Type:
  @n: Nat -> @h: String -> @k: R.Cnt -> @out: String -> @ns: List<&2, B.Note> -> @y0: R.Item -> @t: List<&2, R.Item> ->
    {Nat.is_le(l, R.Item.key(y0)) == False{} : Bool} ->
    {G.Bad(l, L.run.go(rest, fa, o, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, y0 <> t, k, out, ns, False{}})) == True{} : Bool}

def doom.rd(+rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +w: Nat, +inpos: Nat, +at: B.At, +y0: R.Item, +t: List<&2, R.Item>, +rd: Bool,
  hy0: {Nat.is_le(l, R.Item.key(y0)) == False{} : Bool}, ih: DoomIH(rest, fa, o, c0, l)) ->
  {G.Bad(l, L.run.go(rest, fa, o, R.emit.ready(R.flush(R.take_ready.go(y0 <> t, rd, w, inpos), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}),
    R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k, out, ns, False{}}, R.drop_ready.go(y0 <> t, rd, w, inpos), at))) == True{} : Bool}:
  match rd:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(l, R.Item.key(y0)), False{}, hy0) :
        {G.Bad(l, L.run.go(rest, fa, o, R.emit.ready(R.flush.put(_, y0, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, R.flush(R.take_ready.go(t, R.head_ready(w, inpos, t), w, inpos), Some{y0})),
          R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k, out, ns, False{}}, R.drop_ready.go(t, R.head_ready(w, inpos, t), w, inpos), at))) == True{} : Bool}
      bad_halt(rest, fa, o, l, 1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(y0)}, R.at_of(Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}})}]))
    case False{}:
      ih(1n+n, h, k, out ++ "", ns, y0, t, hy0)

def doom.ins(+rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +w: Nat, +key: Nat, +inpos: Nat, +at: B.At, +text: String, +x0: R.Item, +t: List<&2, R.Item>, +g2: Bool,
  eg2: {Nat.is_le(R.Item.key(x0), key) == g2 : Bool},
  hx0: {Nat.is_le(l, R.Item.key(x0)) == False{} : Bool}, ih: DoomIH(rest, fa, o, c0, l)) ->
  {G.Bad(l, L.run.go(rest, fa, o, R.emit.ready(R.flush(R.take_ready(w, inpos, R.insert.put(g2, x0, R.Item{key, inpos, at, text}, t, R.insert(R.Item{key, inpos, at, text}, t))), Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}),
    R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, Nil{}, k, out, ns, False{}}, R.drop_ready(w, inpos, R.insert.put(g2, x0, R.Item{key, inpos, at, text}, t, R.insert(R.Item{key, inpos, at, text}, t))), at))) == True{} : Bool}:
  match g2:
    case True{}:
      +t2 = R.insert(R.Item{key, inpos, at, text}, t)
      doom.rd(rest, fa, o, c0, l, n, h, k, out, ns, w, inpos, at, x0, t2, R.ready(w, inpos, x0), hx0, ih)
    case False{}:
      +y0 = {R.Item{key, inpos, at, text} : R.Item}
      doom.rd(rest, fa, o, c0, l, n, h, k, out, ns, w, inpos, at, y0, x0 <> t, R.ready(w, inpos, y0), lt_chain(R.Item.key(x0), key, l, eg2, hx0), ih)

def doom.kd(+rest: List<&2, B.Line>, +fa: List<&2, B.Contig>, +o: B.Opts, +c0: String, +l: Nat, +n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +w: Nat, +x0: R.Item, +t: List<&2, R.Item>, +g: Bool, +chrom: String, +it: R.Item,
  hx0: {Nat.is_le(l, R.Item.key(x0)) == False{} : Bool}, ih: DoomIH(rest, fa, o, c0, l)) ->
  {G.Bad(l, L.run.go(rest, fa, o, R.keyed.go(g, R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out, ns, False{}}, w, chrom, it))) == True{} : Bool}:
  match g it:
    case True{} R.Item{+key, +inpos, +at, +text}:
      doom.ins(rest, fa, o, c0, l, n, h, k, out, ns, w, key, inpos, at, text, x0, t, Nat.is_le(R.Item.key(x0), key), {==}, hx0, ih)
    case False{} _:
      %Equal.sym(Bool, Nat.is_le(l, R.Item.key(x0)), False{}, hx0) :
        {G.Bad(l, L.run.go(rest, fa, o, R.new_run.go(R.flush.put(_, x0, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, R.flush(t, Some{x0})), R.has(chrom, Nil{}),
          R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out, ns, False{}}, w, chrom, it))) == True{} : Bool}
      bad_halt(rest, fa, o, l, 1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(x0)}, R.at_of(Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}})}]))

# An item below l at the head of T's first-run buffer (the last written is
# the phantom): T stops, or ends in its first run with that key buffered.
law doom:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +x0: R.Item
  for +t: List<&2, R.Item>
  for +hx0: {Nat.is_le(l, R.Item.key(x0)) == False{} : Bool}
  {G.Bad(l, L.run.go(ls, fa, o, R.RunSt{n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out, ns, False{}})) == True{} : Bool}

def doom(ls, fa, o, c0, l, n, h, k, out, ns, x0, t, hx0):
  match ls:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_le(l, R.Item.key(x0)), False{}, hx0) : {Bool.not(Bool.and(_, SD.keys_ge(t, l))) == True{} : Bool}
      {==}
    case +li <> +rest:
      ih = {(n2 => h2 => k2 => out2 => ns2 => y0 => t2 => hy0 => doom(rest, fa, o, c0, l, n2, h2, k2, out2, ns2, y0, t2, hy0)) : DoomIH(rest, fa, o, c0, l)}
      +fs = B.Rec.fields(B.Line.body(li))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +st = {R.RunSt{1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out, ns, False{}} : R.RunSt}
      ST.BL(s => {G.Bad(l, L.run.go(rest, fa, o, s)) == True{} : Bool}, L.judge(fa, B.Line.body(li)), st, o, li, at, B.Rec.pos(fs),
        ST.judge_ok(fa, B.Line.body(li)),
        cd => eu => bad_halt(rest, fa, o, l, 1n+n, True{}, h, Some{c0}, Nil{}, Some{R.Item{l, l, B.At{0n, c0, Nat.show(l)}, ""}}, x0 <> t, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        nts => k2 => eu => doom.kd(rest, fa, o, c0, l, n, h, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o), x0, t,
          R.is_cur(Some{c0}, R.Item.chrom(L.item_of(L.judge(fa, B.Line.body(li)), li, at, B.Rec.pos(fs)))),
          R.Item.chrom(L.item_of(L.judge(fa, B.Line.body(li)), li, at, B.Rec.pos(fs))),
          L.item_of(L.judge(fa, B.Line.body(li)), li, at, B.Rec.pos(fs)), hx0, ih))
