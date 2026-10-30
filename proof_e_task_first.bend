import Base
import ./types.bend as B
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cut_str.bend as CS
import ./proof_b_cut_ne.bend as CN
import ./proof_b_lines_str.bend as LSS
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area D (task): the plan's first line. Its CHROM (the bytes before
# the first tab) is field 0 of the line B.Text.lines reads, also when the
# line ends with a CR.

# ---------------------------------------------------------------------------
# A first hit before a shorter end
# ---------------------------------------------------------------------------

def rlt.k(+q: Bool, +RM: Nat, +RK: Nat, +r: Nat, +k: Nat,
  +h1: {Bool.pick(Nat, q, 0n, Nat.add(1n, RM)) == r : Nat},
  +h2: {Nat.is_lt(r, 1n+k) == True{} : Bool},
  ih: @r2: Nat -> {RM == r2 : Nat} -> {Nat.is_lt(r2, k) == True{} : Bool} -> {RK == r2 : Nat}) ->
  {Bool.pick(Nat, q, 0n, Nat.add(1n, RK)) == r : Nat}:
  match q:
    case True{}:
      h1
    case False{}:
      +h2b = AB.subst(Nat, z => {Nat.is_lt(z, 1n+k) == True{} : Bool}, r, 1n+RM, Equal.sym(Nat, 1n+RM, r, h1), h2)
      Equal.trans(Nat, 1n+RK, 1n+RM, r, Equal.cong(Nat, Nat, z => 1n+z, RK, RM, ih(RM, {==}, h2b)), h1)

# The leading run of non-9 values, cut at m, is r < k <= m: cut at k, it is r.
def rlt(+ys: List<&2, U32>, +k: Nat, +m: Nat, +r: Nat,
  +h1: {D.run_len(List.take(&2, U32, ys, m), 9) == r : Nat},
  +h2: {Nat.is_lt(r, k) == True{} : Bool},
  +h3: {Nat.is_le(k, m) == True{} : Bool}) ->
  {D.run_len(List.take(&2, U32, ys, k), 9) == r : Nat}:
  match ys k m:
    case Nil{} _ _:
      h1
    case Con{+y, +t} 0n _:
      Empty.absurd({D.run_len(List.take(&2, U32, Con{y, t}, 0n), 9) == r : Nat},
        N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(r, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r, 0n), False{}, N.lt_zero(r)), h2)))
    case Con{+y, +t} 1n+k2 0n:
      Empty.absurd({D.run_len(List.take(&2, U32, Con{y, t}, 1n+k2), 9) == r : Nat}, N.false_ne_true(h3))
    case Con{+y, +t} 1n+k2 1n+m2:
      rlt.k(U32.is_eq(y, 9), D.run_len(List.take(&2, U32, t, m2), 9), D.run_len(List.take(&2, U32, t, k2), 9), r, k2, h1, h2,
        r2 => e1 => e2 => rlt(t, k2, m2, r2, e1, e2, h3))

# The first 9 in a .. b-1 is at e < c <= b: it is the first in a .. c-1.
def first_shrink(+xs: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +e: Nat,
  +hf: {D.first(xs, a, b, 9) == e : Nat},
  +hae: {Nat.is_le(a, e) == True{} : Bool},
  +hec: {Nat.is_lt(e, c) == True{} : Bool},
  +hcb: {Nat.is_le(c, b) == True{} : Bool}) ->
  {D.first(xs, a, c, 9) == e : Nat}:
  +Z = List.drop(&2, U32, xs, a)
  +R = D.run_len(List.take(&2, U32, Z, Nat.sub(b, a)), 9)
  +r = Nat.sub(e, a)
  +hR = Equal.trans(Nat, R, Nat.sub(Nat.add(a, R), a), r, Equal.sym(Nat, Nat.sub(Nat.add(a, R), a), R, N.sub_add_l(a, R)),
    Equal.cong(Nat, Nat, z => Nat.sub(z, a), Nat.add(a, R), e, hf))
  +hlt = CS.lt_sub(a, e, c, hae, hec)
  +hle = CS.sub_mono(c, b, a, hcb)
  +hK = rlt(Z, Nat.sub(c, a), Nat.sub(b, a), r, hR, hlt, hle)
  %Equal.sym(Nat, D.run_len(List.take(&2, U32, Z, Nat.sub(c, a)), 9), r, hK) : {Nat.add(a, _) == e : Nat}
  N.le_sub_add(a, e, hae)

# ---------------------------------------------------------------------------
# Field 0 of a line (proof_fast.bend's cut lemmas, copied: that file brings
# in open TODOs of other phases)
# ---------------------------------------------------------------------------

def cl(c: J.Cut) -> List<&2, String>:
  match c:
    case J.Cut{f, r, True{}}:
      f <> String.split(r, '\t')
    case J.Cut{f, r, False{}}:
      [f]

def cl_k(+h: Char, +c: J.Cut) -> {cl(J.cut.k(h, c)) == String.split.push(h, cl(c)) : List<&2, String>}:
  match c:
    case J.Cut{f, r, True{}}:
      {==}
    case J.Cut{f, r, False{}}:
      {==}

def cut_go(+t: String, +b: Bool, +h: Char) -> {cl(J.cut.go(t, b, h)) == String.split.fin(h, String.split(t, '\t'), b) : List<&2, String>}:
  match t b:
    case SNil{} True{}:
      {==}
    case SCon{+c, +t2} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, +t2} False{}:
      +X = J.cut.go(t2, Char.is_eq(c, '\t'), c)
      %Equal.sym(List<&2, String>, cl(J.cut.k(h, X)), String.split.push(h, cl(X)), cl_k(h, X)) :
        {_ == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      %Equal.sym(List<&2, String>, cl(X), String.split(SCon{c, t2}, '\t'), cut_go(t2, Char.is_eq(c, '\t'), c)) :
        {String.split.push(h, _) == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      {==}

def cut_split(+s: String) -> {cl(J.cut(s)) == String.split(s, '\t') : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      cut_go(t, Char.is_eq(h, '\t'), h)

# The text a .. b-1 whose first tab is at e: its field 0 is a .. e-1.
def field0_cut(+xs: List<&2, U32>, +a: Nat, +e: Nat, +b: Nat,
  +hae: {Nat.is_le(a, e) == True{} : Bool},
  +heb: {Nat.is_lt(e, b) == True{} : Bool},
  +hf: {D.first(xs, a, b, 9) == e : Nat},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}) ->
  {B.Rec.field(B.Rec.fields(CS.fld(xs, a, b)), 0n) == CS.fld(xs, a, e) : String}:
  %cut_split(CS.fld(xs, a, b)) :
    {Maybe.default(&2, String, List.get(&2, String, _, 0n), "") == CS.fld(xs, a, e) : String}
  %Equal.sym(J.Cut, J.cut(CS.fld(xs, a, b)), J.Cut{CS.fld(xs, a, e), CS.fld(xs, Nat.add(e, 1n), b), True{}}, CS.cut_fld(xs, a, e, b, hae, heb, hf, htab)) :
    {Maybe.default(&2, String, List.get(&2, String, cl(_), 0n), "") == CS.fld(xs, a, e) : String}
  {==}

# With a CR at c (the line's last byte), the first tab e is before c.
def tab_lt.k(+q: Bool, +xs: List<&2, U32>, +e: Nat, +c: Nat, +x: U32,
  +hq: {Nat.is_eq(e, c) == q : Bool},
  +hle: {Nat.is_le(e, c) == True{} : Bool},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>},
  +hx: {List.get(&2, U32, xs, c) == Some{x} : Maybe<&2, U32>},
  +hcr: {U32.is_eq(x, 13) == True{} : Bool}) ->
  {Nat.is_lt(e, c) == True{} : Bool}:
  match q:
    case True{}:
      +eq = N.eq_sound(e, c, hq)
      +h9 = AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{9} : Maybe<&2, U32>}, e, c, eq, htab)
      +hx9 = Equal.trans(Maybe<&2, U32>, Some{x}, List.get(&2, U32, xs, c), Some{9}, Equal.sym(Maybe<&2, U32>, List.get(&2, U32, xs, c), Some{x}, hx), h9)
      +h = AB.subst(U32, z => {U32.is_eq(z, 13) == True{} : Bool}, x, 9, CS.some_eq(x, 9, hx9), hcr)
      Empty.absurd({Nat.is_lt(e, c) == True{} : Bool}, N.false_ne_true(h))
    case False{}:
      Equal.trans(Bool, Nat.is_lt(e, c), Nat.is_le(1n+e, c), True{}, Equal.sym(Bool, Nat.is_le(1n+e, c), Nat.is_lt(e, c), N.le_succ_lt(e, c)), N.le_ne(e, c, hle, hq))

def fld0.k(+cr: Bool, +xs: List<&2, U32>, +a: Nat, +e: Nat, +c: Nat, +x: U32,
  +hcr: {U32.is_eq(x, 13) == cr : Bool},
  +hae: {Nat.is_le(a, e) == True{} : Bool},
  +hle: {Nat.is_le(e, c) == True{} : Bool},
  +hf: {D.first(xs, a, 1n+c, 9) == e : Nat},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>},
  +hx: {List.get(&2, U32, xs, c) == Some{x} : Maybe<&2, U32>}) ->
  {B.Rec.field(B.Rec.fields(CS.BDY(xs, a, 1n+c, c, cr)), 0n) == CS.fld(xs, a, e) : String}:
  match cr:
    case False{}:
      field0_cut(xs, a, e, 1n+c, hae, Equal.trans(Bool, Nat.is_lt(e, 1n+c), Nat.is_le(e, c), True{}, N.lt_succ_iff(e, c), hle), hf, htab)
    case True{}:
      +hlt = tab_lt.k(Nat.is_eq(e, c), xs, e, c, x, {==}, hle, htab, hx, hcr)
      +hc1 = AB.subst(Nat, z => {Nat.is_le(c, z) == True{} : Bool}, Nat.add(c, 1n), 1n+c, N.add_one(c), N.le_add_r(c, 1n))
      field0_cut(xs, a, e, c, hae, hlt, first_shrink(xs, a, 1n+c, c, e, hf, hae, hlt, hc1), htab)

# The line a .. b-1 (its LF at b) whose first tab is at e: field 0 of its
# body is a .. e-1.
def fld0(+xs: List<&2, U32>, +a: Nat, +e: Nat, +b: Nat,
  +hae: {Nat.is_le(a, e) == True{} : Bool},
  +heb: {Nat.is_lt(e, b) == True{} : Bool},
  +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  +hf: {D.first(xs, a, b, 9) == e : Nat},
  +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}) ->
  {B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(CS.fld(xs, a, b)))), 0n) == CS.fld(xs, a, e) : String}:
  match b:
    case 0n:
      Empty.absurd({B.Rec.field(B.Rec.fields(B.Line.body(B.Text.line(CS.fld(xs, a, 0n)))), 0n) == CS.fld(xs, a, e) : String},
        N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(e, 0n), True{}, Equal.sym(Bool, Nat.is_lt(e, 0n), False{}, N.lt_zero(e)), heb)))
    case 1n+c:
      +L = List.length(&2, U32, xs)
      +hcl = Equal.trans(Bool, Nat.is_lt(c, L), Nat.is_le(1n+c, L), True{}, Equal.sym(Bool, Nat.is_le(1n+c, L), Nat.is_lt(c, L), N.le_succ_lt(c, L)), hb)
      +x = CN.XV(xs, c)
      +hx = CN.get_xv(xs, c, hcl)
      +hle = Equal.trans(Bool, Nat.is_le(e, c), Nat.is_lt(e, 1n+c), True{}, Equal.sym(Bool, Nat.is_lt(e, 1n+c), Nat.is_le(e, c), N.lt_succ_iff(e, c)), heb)
      +hac = N.le_trans(a, e, c, hae, hle)
      %LSS.line_eq(CS.fld(xs, a, 1n+c)) :
        {B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n) == CS.fld(xs, a, e) : String}
      %Equal.sym(String, B.Line.body(Q.line(CS.fld(xs, a, 1n+c))), CS.BDY(xs, a, 1n+c, c, U32.is_eq(x, 13)), CS.body_eq(xs, a, 1n+c, c, x, N.add_one(c), hac, hb, hx)) :
        {B.Rec.field(B.Rec.fields(_), 0n) == CS.fld(xs, a, e) : String}
      fld0.k(U32.is_eq(x, 13), xs, a, e, c, x, {==}, hae, hle, hf, htab, hx)
