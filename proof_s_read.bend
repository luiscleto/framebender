import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_scan.bend as SC
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_same.bend as S
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The byte splitter's small reads on a well-formed line: is1, txt, letters.
# Each hands the line back (its pair form) and answers what the spec asks of
# the range's text (TX). Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def X(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# String.eq on the text of bytes (proof_c_pre_let.bend's, for NR.chars)
# ---------------------------------------------------------------------------

def order_lt(+a: String, +b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def order_gt(+a: String, +b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      {==}
    case SCon{h, t} SNil{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

def ord_c(+s: String, +u: String, +c: Cmp) ->
  {Cmp.is_eq(String.order.go(s, u, c)) == Bool.and(Cmp.is_eq(c), Cmp.is_eq(String.order.go(s, u, EQ{}))) : Bool}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      %Equal.sym(Cmp, String.order.go(s, u, LT{}), LT{}, order_lt(s, u)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, String.order.go(s, u, GT{}), GT{}, order_gt(s, u)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

def sc(+x: U32, +y: U32, +s: String, +u: String) ->
  {String.eq(SCon{Chr{x}, s}, SCon{Chr{y}, u}) == Bool.and(U32.is_eq(x, y), String.eq(s, u)) : Bool}:
  ord_c(s, u, U32.cmp(x, y))

law seq:
  for +xs: L32()
  for +ys: L32()
  {String.eq(NR.chars(xs), NR.chars(ys)) == D.list_eq(xs, ys) : Bool}

def seq(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> +yt:
      {==}
    case +x <> +xt Nil{}:
      {==}
    case +x <> +xt +y <> +yt:
      %Equal.sym(Bool, String.eq(SCon{Chr{x}, NR.chars(xt)}, SCon{Chr{y}, NR.chars(yt)}), Bool.and(U32.is_eq(x, y), String.eq(NR.chars(xt), NR.chars(yt))), sc(x, y, NR.chars(xt), NR.chars(yt))) : {_ == Bool.and(U32.is_eq(x, y), D.list_eq(xt, yt)) : Bool}
      %Equal.sym(Bool, String.eq(NR.chars(xt), NR.chars(yt)), D.list_eq(xt, yt), seq(xt, yt)) : {Bool.and(U32.is_eq(x, y), _) == Bool.and(U32.is_eq(x, y), D.list_eq(xt, yt)) : Bool}
      {==}

# ---------------------------------------------------------------------------
# Slices
# ---------------------------------------------------------------------------

def hsize(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n(a), n((z - a : U32))), n(len)) == True{} : Bool}:
  W.pv_put(len, a, z, hp)

# Byte j and the rest, for j < z <= len.
def sl_cons(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool}) ->
  {D.slice(X(len, t), n(j), Nat.sub(n(z), n(j))) == C.AT(len, t, j) <> D.slice(X(len, t), n((j + 1 : U32)), Nat.sub(n(z), n((j + 1 : U32)))) : L32()}:
  +hjl = N.lt_le_trans(n(j), n(z), n(len), hjz, hzl)
  +hg = Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, j)}, List.get(&2, U32, X(len, t), n(j)),
    C.at_view_t(len, t, d, j, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hjl))
  %Equal.sym(Nat, n((j + 1 : U32)), Nat.add(n(j), 1n), AL.inc_len(len, t, d, j, h, hjl)) :
    {D.slice(X(len, t), n(j), Nat.sub(n(z), n(j))) == C.AT(len, t, j) <> D.slice(X(len, t), _, Nat.sub(n(z), _)) : L32()}
  LS.slice_lt(X(len, t), n(j), n(z), C.AT(len, t, j), hjz, hg)

def tx_eq(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32, +haz: {Nat.is_le(n(a), n(z)) == True{} : Bool}) ->
  {WT.TX(len, t, NS.Rg{a, z}) == NR.chars(D.slice(X(len, t), n(a), Nat.sub(n(z), n(a)))) : String}:
  %Equal.sym(Nat, n((z - a : U32)), Nat.sub(n(z), n(a)), W.nsub(a, z, haz)) : {NR.chars(D.slice(X(len, t), n(a), _)) == NR.chars(D.slice(X(len, t), n(a), Nat.sub(n(z), n(a)))) : String}
  {==}

# ---------------------------------------------------------------------------
# txt: the range's text
# ---------------------------------------------------------------------------

def txt_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NS.Rg,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, x) == True{} : Bool}) ->
  {NS.txt(C.BT(len, t), x) == (C.BT(len, t), WT.TX(len, t, x)) : D.Bytes & String}:
  match x:
    case NS.Rg{+a, +z}:
      +k = (z - a : U32)
      %Equal.sym(D.Bytes & L32(), BY.to_list(C.BT(len, t), a, k), (C.BT(len, t), Pair.snd(D.Bytes, L32(), BY.to_list(C.BT(len, t), a, k))), S.to_list_pair_t(len, t, a, k)) :
        {NS.txt.k(_) == (C.BT(len, t), WT.TX(len, t, NS.Rg{a, z})) : D.Bytes & String}
      %Equal.sym(L32(), Pair.snd(D.Bytes, L32(), BY.to_list(C.BT(len, t), a, k)), D.slice(X(len, t), n(a), n(k)), S.to_list_view_t(len, t, d, a, k, h, hsize(len, t, d, a, z, h, hp))) :
        {(C.BT(len, t), NR.chars(_)) == (C.BT(len, t), WT.TX(len, t, NS.Rg{a, z})) : D.Bytes & String}
      {==}

# ---------------------------------------------------------------------------
# is1: the range is the one byte c
# ---------------------------------------------------------------------------

def IS1(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, +c: U32) -> Bool:
  match x:
    case NS.Rg{+a, +z}:
      Bool.and(U32.is_eq((z - a : U32), 1), U32.is_eq(C.AT(len, t, a), c))

def is1.k_t(+e: Bool, +len: U32, +t: AT.Tree<U32>, +a: U32, +c: U32) ->
  {NS.is1.if(e, C.BT(len, t), a, c) == (C.BT(len, t), Bool.and(e, U32.is_eq(C.AT(len, t, a), c))) : D.Bytes & Bool}:
  match e:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), a), (C.BT(len, t), C.AT(len, t, a)), C.at_pair_t(len, t, a)) :
        {NS.is1.k(c, _) == (C.BT(len, t), Bool.and(True{}, U32.is_eq(C.AT(len, t, a), c))) : D.Bytes & Bool}
      {==}
    case False{}:
      {==}

def is1_t(+len: U32, +t: AT.Tree<U32>, +x: NS.Rg, +c: U32) -> {NS.is1(C.BT(len, t), x, c) == (C.BT(len, t), IS1(len, t, x, c)) : D.Bytes & Bool}:
  match x:
    case NS.Rg{+a, +z}:
      is1.k_t(U32.is_eq((z - a : U32), 1), len, t, a, c)

def is1_v.k(+e: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +he: {U32.is_eq((z - a : U32), 1) == e : Bool}) ->
  {Bool.and(e, U32.is_eq(C.AT(len, t, a), c)) == String.eq(WT.TX(len, t, NS.Rg{a, z}), SCon{Chr{c}, SNil{}}) : Bool}:
  match e:
    case True{}:
      +sl = W.SL(len, t, a, z)
      +e1 = Equal.cong(U32, Nat, w => U32.to_nat(w), (z - a : U32), 1, U.is_eq_true((z - a : U32), 1, he))
      +haz = W.pv_a(len, a, z, hp)
      +ez = {%W.nsub(a, z, haz) : {_ == 1n : Nat}; e1 : {Nat.sub(n(z), n(a)) == 1n : Nat}}
      +ez2 = {%N.le_sub_add(n(a), n(z), haz) : {_ == Nat.add(n(a), 1n) : Nat};
        %Equal.sym(Nat, Nat.sub(n(z), n(a)), 1n, ez) : {Nat.add(n(a), _) == Nat.add(n(a), 1n) : Nat}; {==} : {n(z) == Nat.add(n(a), 1n) : Nat}}
      +hal = {%ez2 : {Nat.is_le(_, n(len)) == True{} : Bool}; W.pv_z(len, a, z, hp) : {Nat.is_le(Nat.add(n(a), 1n), n(len)) == True{} : Bool}}
      +hlt = {%N.le_succ_lt(n(a), n(len)) : {_ == True{} : Bool}; %N.add_one(n(a)) : {Nat.is_le(_, n(len)) == True{} : Bool}; hal : {Nat.is_lt(n(a), n(len)) == True{} : Bool}}
      +hg = Equal.sym(Maybe<&2, U32>, Some{C.AT(len, t, a)}, List.get(&2, U32, X(len, t), n(a)),
        C.at_view_t(len, t, d, a, C.ok_full(len, t, d, h), C.ok_d(len, t, d, h), C.ok_len(len, t, d, h), hlt))
      +hl1 = {%N.le_succ_lt(n(a), Nat.add(n(a), 1n)) : {_ == True{} : Bool}; %Equal.sym(Nat, Nat.add(n(a), 1n), 1n+n(a), N.add_one(n(a))) : {Nat.is_le(1n+n(a), _) == True{} : Bool}; N.le_refl(1n+n(a)) : {Nat.is_lt(n(a), Nat.add(n(a), 1n)) == True{} : Bool}}
      +es = {%Equal.sym(Nat, n((z - a : U32)), 1n, e1) : {D.slice(X(len, t), n(a), _) == [C.AT(len, t, a)] : L32()};
        %N.sub_add_l(n(a), 1n) : {D.slice(X(len, t), n(a), _) == [C.AT(len, t, a)] : L32()};
        %Equal.sym(L32(), D.slice(X(len, t), n(a), Nat.sub(Nat.add(n(a), 1n), n(a))), C.AT(len, t, a) <> D.slice(X(len, t), Nat.add(n(a), 1n), Nat.sub(Nat.add(n(a), 1n), Nat.add(n(a), 1n))),
          LS.slice_lt(X(len, t), n(a), Nat.add(n(a), 1n), C.AT(len, t, a), hl1, hg)) : {_ == [C.AT(len, t, a)] : L32()};
        %Equal.sym(Nat, Nat.sub(Nat.add(n(a), 1n), Nat.add(n(a), 1n)), 0n, LS.sub_self(Nat.add(n(a), 1n))) : {C.AT(len, t, a) <> D.slice(X(len, t), Nat.add(n(a), 1n), _) == [C.AT(len, t, a)] : L32()};
        %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, X(len, t), Nat.add(n(a), 1n)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, X(len, t), Nat.add(n(a), 1n)))) : {C.AT(len, t, a) <> _ == [C.AT(len, t, a)] : L32()};
        {==} : {sl == [C.AT(len, t, a)] : L32()}}
      %Equal.sym(Bool, String.eq(NR.chars(sl), NR.chars([c])), D.list_eq(sl, [c]), seq(sl, [c])) : {Bool.and(True{}, U32.is_eq(C.AT(len, t, a), c)) == _ : Bool}
      %Equal.sym(L32(), sl, [C.AT(len, t, a)], es) : {Bool.and(True{}, U32.is_eq(C.AT(len, t, a), c)) == D.list_eq(_, [c]) : Bool}
      Equal.sym(Bool, Bool.and(U32.is_eq(C.AT(len, t, a), c), True{}), U32.is_eq(C.AT(len, t, a), c), LS.and_true(U32.is_eq(C.AT(len, t, a), c)))
    case False{}:
      +sl = W.SL(len, t, a, z)
      +hne = {%U.is_eq_to_nat((z - a : U32), 1) : {_ == False{} : Bool}; he : {Nat.is_eq(n((z - a : U32)), 1n) == False{} : Bool}}
      +hl = AL.slice_len(X(len, t), n(a), n((z - a : U32)), %AL.len_x(len, t, d, h) : {Nat.is_le(Nat.add(n(a), n((z - a : U32))), _) == True{} : Bool}; W.pv_put(len, a, z, hp))
      %Equal.sym(Bool, String.eq(NR.chars(sl), NR.chars([c])), D.list_eq(sl, [c]), seq(sl, [c])) : {False{} == _ : Bool}
      Equal.sym(Bool, D.list_eq(sl, [c]), False{}, AL.list_eq_len(sl, [c], %Equal.sym(Nat, List.length(&2, U32, sl), n((z - a : U32)), hl) : {Nat.is_eq(_, 1n) == False{} : Bool}; hne))

def is1_v(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NS.Rg, +c: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, x) == True{} : Bool}) ->
  {IS1(len, t, x, c) == String.eq(WT.TX(len, t, x), SCon{Chr{c}, SNil{}}) : Bool}:
  match x:
    case NS.Rg{+a, +z}:
      is1_v.k(U32.is_eq((z - a : U32), 1), len, t, d, a, z, c, h, hp, {==})

# ---------------------------------------------------------------------------
# letters: one or more letters (B.Text.is_letters)
# ---------------------------------------------------------------------------

def BS(+len: U32, +t: AT.Tree<U32>, +j: U32, +z: U32) -> L32():
  D.slice(X(len, t), n(j), Nat.sub(n(z), n(j)))

def ev_done(+q: Nat, +len: U32, +t: AT.Tree<U32>, +j: U32, +z: U32, +ok: Bool) ->
  {NS.letters.loop(q, NS.Ev{C.BT(len, t), j, z, ok, True{}}) == NS.Ev{C.BT(len, t), j, z, ok, True{}} : NS.Ev}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

def nofuel(-A: Type, +a: Nat, +z: Nat, +haz: {Nat.is_le(a, z) == True{} : Bool}, +hm: {Nat.is_lt(z, Nat.add(a, 0n)) == True{} : Bool}) -> A:
  +h1 = {%N.add_zero(a) : {Nat.is_lt(z, _) == True{} : Bool}; hm : {Nat.is_lt(z, a) == True{} : Bool}}
  Empty.absurd(A, P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, N.lt_irrefl(a)), N.le_lt_trans(a, z, a, haz, h1))))

def LTR(+len: U32, +t: AT.Tree<U32>, +j: U32, +z: U32, -r: D.Bytes & Bool) -> Type:
  {r == (C.BT(len, t), B.Text.all_letters(NR.chars(BS(len, t, j, z)))) : D.Bytes & Bool}

def lt.pre(+len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool},
  +hb: {NS.letter(C.AT(len, t, j)) == True{} : Bool}) ->
  {B.Text.all_letters(NR.chars(BS(len, t, j, z))) == B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))) : Bool}:
  +x = C.AT(len, t, j)
  %Equal.sym(L32(), BS(len, t, j, z), x <> BS(len, t, (j + 1 : U32), z), sl_cons(len, t, d, j, z, h, hzl, hjz)) :
    {B.Text.all_letters(NR.chars(_)) == B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))) : Bool}
  %Equal.sym(Bool, NS.letter(x), True{}, hb) :
    {Bool.and(_, B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z)))) == B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))) : Bool}
  {==}

def lt.e(+e2: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool},
  +hb: {NS.letter(C.AT(len, t, j)) == True{} : Bool},
  +he: {U32.is_eq((j + 1 : U32), z) == e2 : Bool},
  ih: {Nat.is_lt(n((j + 1 : U32)), n(z)) == True{} : Bool} -> LTR(len, t, (j + 1 : U32), z, NS.letters.fin(NS.letters.loop(q, NS.Ev{C.BT(len, t), (j + 1 : U32), z, True{}, False{}})))) ->
  LTR(len, t, j, z, NS.letters.fin(NS.letters.loop(q, NS.Ev{C.BT(len, t), (j + 1 : U32), z, True{}, e2}))):
  match e2:
    case True{}:
      +j1 = (j + 1 : U32)
      +ez = Equal.cong(U32, Nat, w => U32.to_nat(w), j1, z, U.is_eq_true(j1, z, he))
      %Equal.sym(Bool, B.Text.all_letters(NR.chars(BS(len, t, j, z))), B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))), lt.pre(len, t, d, j, z, h, hzl, hjz, hb)) :
        {NS.letters.fin(NS.letters.loop(q, NS.Ev{C.BT(len, t), j1, z, True{}, True{}})) == (C.BT(len, t), _) : D.Bytes & Bool}
      %Equal.sym(NS.Ev, NS.letters.loop(q, NS.Ev{C.BT(len, t), j1, z, True{}, True{}}), NS.Ev{C.BT(len, t), j1, z, True{}, True{}}, ev_done(q, len, t, j1, z, True{})) :
        {NS.letters.fin(_) == (C.BT(len, t), B.Text.all_letters(NR.chars(BS(len, t, j1, z)))) : D.Bytes & Bool}
      %Equal.sym(Nat, n(j1), n(z), ez) : {(C.BT(len, t), True{}) == (C.BT(len, t), B.Text.all_letters(NR.chars(D.slice(X(len, t), _, Nat.sub(n(z), _))))) : D.Bytes & Bool}
      %Equal.sym(Nat, Nat.sub(n(z), n(z)), 0n, LS.sub_self(n(z))) : {(C.BT(len, t), True{}) == (C.BT(len, t), B.Text.all_letters(NR.chars(D.slice(X(len, t), n(z), _)))) : D.Bytes & Bool}
      %Equal.sym(L32(), List.take(&2, U32, List.drop(&2, U32, X(len, t), n(z)), 0n), Nil{}, Q.take_zero(List.drop(&2, U32, X(len, t), n(z)))) :
        {(C.BT(len, t), True{}) == (C.BT(len, t), B.Text.all_letters(NR.chars(_))) : D.Bytes & Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, B.Text.all_letters(NR.chars(BS(len, t, j, z))), B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))), lt.pre(len, t, d, j, z, h, hzl, hjz, hb)) :
        {NS.letters.fin(NS.letters.loop(q, NS.Ev{C.BT(len, t), (j + 1 : U32), z, True{}, False{}})) == (C.BT(len, t), _) : D.Bytes & Bool}
      ih(SC.lt_of((j + 1 : U32), z, SC.j1_le(len, t, d, j, z, h, hzl, hjz), he))

def lt.b(+b: Bool, +q: Nat, +len: U32, +t: AT.Tree<U32>, +d: Nat, +j: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool},
  +hb: {NS.letter(C.AT(len, t, j)) == b : Bool},
  ih: {Nat.is_lt(n((j + 1 : U32)), n(z)) == True{} : Bool} -> LTR(len, t, (j + 1 : U32), z, NS.letters.fin(NS.letters.loop(q, NS.Ev{C.BT(len, t), (j + 1 : U32), z, True{}, False{}})))) ->
  LTR(len, t, j, z, NS.letters.fin(NS.letters.loop(q, NS.letters.if(b, C.BT(len, t), j, z)))):
  match b:
    case True{}:
      lt.e(U32.is_eq((j + 1 : U32), z), q, len, t, d, j, z, h, hzl, hjz, hb, {==}, ih)
    case False{}:
      +x = C.AT(len, t, j)
      %Equal.sym(NS.Ev, NS.letters.loop(q, NS.Ev{C.BT(len, t), j, z, False{}, True{}}), NS.Ev{C.BT(len, t), j, z, False{}, True{}}, ev_done(q, len, t, j, z, False{})) :
        {NS.letters.fin(_) == (C.BT(len, t), B.Text.all_letters(NR.chars(BS(len, t, j, z)))) : D.Bytes & Bool}
      %Equal.sym(L32(), BS(len, t, j, z), x <> BS(len, t, (j + 1 : U32), z), sl_cons(len, t, d, j, z, h, hzl, hjz)) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), B.Text.all_letters(NR.chars(_))) : D.Bytes & Bool}
      %Equal.sym(Bool, NS.letter(x), False{}, hb) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), Bool.and(_, B.Text.all_letters(NR.chars(BS(len, t, (j + 1 : U32), z))))) : D.Bytes & Bool}
      {==}

law lt_go:
  for +m: Nat
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +j: U32
  for +z: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}
  for +hjz: {Nat.is_lt(n(j), n(z)) == True{} : Bool}
  for +hm: {Nat.is_lt(n(z), Nat.add(n(j), m)) == True{} : Bool}
  LTR(len, t, j, z, NS.letters.fin(NS.letters.loop(m, NS.Ev{C.BT(len, t), j, z, True{}, False{}})))

def lt_go(m, len, t, d, j, z, h, hzl, hjz, hm):
  match m:
    case 0n:
      nofuel(LTR(len, t, j, z, NS.letters.fin(NS.letters.loop(0n, NS.Ev{C.BT(len, t), j, z, True{}, False{}}))), n(j), n(z), N.lt_to_le(n(j), n(z), hjz), hm)
    case 1n+(+q):
      +j1 = (j + 1 : U32)
      +ej = AL.inc_len(len, t, d, j, h, N.lt_le_trans(n(j), n(z), n(len), hjz, hzl))
      +hm2 = {%Equal.sym(Nat, n(j1), Nat.add(n(j), 1n), ej) : {Nat.is_lt(n(z), Nat.add(_, q)) == True{} : Bool}; SC.fuel_step(n(j), n(j), n(z), q, N.le_refl(n(j)), hm) : {Nat.is_lt(n(z), Nat.add(n(j1), q)) == True{} : Bool}}
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        LTR(len, t, j, z, NS.letters.fin(NS.letters.loop(q, NS.letters.next(_, j, z))))
      lt.b(NS.letter(C.AT(len, t, j)), q, len, t, d, j, z, h, hzl, hjz, {==}, h1 => lt_go(q, len, t, d, j1, z, h, hzl, h1, hm2))

law lt_nle:
  for +a: Nat
  for +z: Nat
  for +h: {Nat.is_lt(a, z) == True{} : Bool}
  {Nat.is_le(z, a) == False{} : Bool}

def lt_nle(a, z, h):
  match a z:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, P.false_ne_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+p) == False{} : Bool}, P.false_ne_true(h))
    case 1n+p 1n+q:
      lt_nle(p, q, h)

# One or more bytes: is_letters is all_letters.
def il_al(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(a), n(z)) == True{} : Bool}) ->
  {B.Text.is_letters(NR.chars(BS(len, t, a, z))) == B.Text.all_letters(NR.chars(BS(len, t, a, z))) : Bool}:
  +cs = {C.AT(len, t, a) <> BS(len, t, (a + 1 : U32), z) : L32()}
  %Equal.sym(L32(), BS(len, t, a, z), cs, sl_cons(len, t, d, a, z, h, hzl, hlt)) :
    {B.Text.is_letters(NR.chars(_)) == B.Text.all_letters(NR.chars(BS(len, t, a, z))) : Bool}
  %Equal.sym(L32(), BS(len, t, a, z), cs, sl_cons(len, t, d, a, z, h, hzl, hlt)) :
    {B.Text.all_letters(NR.chars(cs)) == B.Text.all_letters(NR.chars(_)) : Bool}
  {==}

def lt.top(+c: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +z: U32,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, NS.Rg{a, z}) == True{} : Bool},
  +hc: {U32.is_lt(a, z) == c : Bool}) ->
  {NS.letters.fin(NS.letters.loop(1n+n((z - a : U32)), NS.Ev{C.BT(len, t), a, z, c, U32.is_le(z, a)})) == (C.BT(len, t), B.Text.is_letters(WT.TX(len, t, NS.Rg{a, z}))) : D.Bytes & Bool}:
  match c:
    case True{}:
      +haz = W.pv_a(len, a, z, hp)
      +hzl = W.pv_z(len, a, z, hp)
      +N1 = {1n+n((z - a : U32)) : Nat}
      +hlt = Equal.trans(Bool, Nat.is_lt(n(a), n(z)), U32.is_lt(a, z), True{}, Equal.sym(Bool, U32.is_lt(a, z), Nat.is_lt(n(a), n(z)), U.is_lt_to_nat(a, z)), hc)
      +hle = Equal.trans(Bool, U32.is_le(z, a), Nat.is_le(n(z), n(a)), False{}, U.is_le_to_nat(z, a), lt_nle(n(a), n(z), hlt))
      %Equal.sym(Bool, U32.is_le(z, a), False{}, hle) :
        {NS.letters.fin(NS.letters.loop(N1, NS.Ev{C.BT(len, t), a, z, True{}, _})) == (C.BT(len, t), B.Text.is_letters(WT.TX(len, t, NS.Rg{a, z}))) : D.Bytes & Bool}
      %Equal.sym(String, WT.TX(len, t, NS.Rg{a, z}), NR.chars(BS(len, t, a, z)), tx_eq(len, t, a, z, haz)) :
        {NS.letters.fin(NS.letters.loop(N1, NS.Ev{C.BT(len, t), a, z, True{}, False{}})) == (C.BT(len, t), B.Text.is_letters(_)) : D.Bytes & Bool}
      %Equal.sym(Bool, B.Text.is_letters(NR.chars(BS(len, t, a, z))), B.Text.all_letters(NR.chars(BS(len, t, a, z))), il_al(len, t, d, a, z, h, hzl, hlt)) :
        {NS.letters.fin(NS.letters.loop(N1, NS.Ev{C.BT(len, t), a, z, True{}, False{}})) == (C.BT(len, t), _) : D.Bytes & Bool}
      lt_go(N1, len, t, d, a, z, h, hzl, hlt, SC.fuel0(a, z, haz))
    case False{}:
      +haz = W.pv_a(len, a, z, hp)
      +N1 = {1n+n((z - a : U32)) : Nat}
      +hnl = Equal.trans(Bool, Nat.is_lt(n(a), n(z)), U32.is_lt(a, z), False{}, Equal.sym(Bool, U32.is_lt(a, z), Nat.is_lt(n(a), n(z)), U.is_lt_to_nat(a, z)), hc)
      +hzan = N.not_lt_le(n(a), n(z), hnl)
      +hza = Equal.trans(Bool, U32.is_le(z, a), Nat.is_le(n(z), n(a)), True{}, U.is_le_to_nat(z, a), hzan)
      %Equal.sym(Bool, U32.is_le(z, a), True{}, hza) :
        {NS.letters.fin(NS.letters.loop(N1, NS.Ev{C.BT(len, t), a, z, False{}, _})) == (C.BT(len, t), B.Text.is_letters(WT.TX(len, t, NS.Rg{a, z}))) : D.Bytes & Bool}
      %Equal.sym(NS.Ev, NS.letters.loop(N1, NS.Ev{C.BT(len, t), a, z, False{}, True{}}), NS.Ev{C.BT(len, t), a, z, False{}, True{}}, ev_done(N1, len, t, a, z, False{})) :
        {NS.letters.fin(_) == (C.BT(len, t), B.Text.is_letters(WT.TX(len, t, NS.Rg{a, z}))) : D.Bytes & Bool}
      %Equal.sym(String, WT.TX(len, t, NS.Rg{a, z}), "", WT.tx_nil(len, t, a, z, haz, hzan)) :
        {(C.BT(len, t), False{}) == (C.BT(len, t), B.Text.is_letters(_)) : D.Bytes & Bool}
      {==}

def letters_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +x: NS.Rg,
  +h: {D.ok(C.BT(len, t), d) == True{} : Bool}, +hp: {W.PV(len, x) == True{} : Bool}) ->
  {NS.letters(C.BT(len, t), x) == (C.BT(len, t), B.Text.is_letters(WT.TX(len, t, x))) : D.Bytes & Bool}:
  match x:
    case NS.Rg{+a, +z}:
      lt.top(U32.is_lt(a, z), len, t, d, a, z, h, hp, {==})
