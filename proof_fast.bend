import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./tan.bend as V
import ./norm_line.bend as J
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_rec.bend as RR
import ./proof_var_lists.bend as VL

# Proofs for the machine's fast paths: J.pfs (the first 8 fields, cut without
# splitting the rest of the line) agrees with B.Rec.fields on everything
# judging reads; J.same implies judge_in gives the record unchanged; and
def Strs() -> Data:
  List<&2, String>

# Cutting at the first tab
# ========================

def cl(c: J.Cut) -> List<&2, String>:
  match c:
    case J.Cut{f, r, True{}}:
      f <> String.split(r, '\t')
    case J.Cut{f, r, False{}}:
      [f]

law cl_k:
  for +h: Char
  for +c: J.Cut
  {cl(J.cut.k(h, c)) == String.split.push(h, cl(c)) : List<&2, String>}

def cl_k(h, c):
  match c:
    case J.Cut{f, r, True{}}:
      {==}
    case J.Cut{f, r, False{}}:
      {==}

law cut_go:
  for +t: String
  for +b: Bool
  for +h: Char
  {cl(J.cut.go(t, b, h)) == String.split.fin(h, String.split(t, '\t'), b) : List<&2, String>}

def cut_go(t, b, h):
  match t b:
    case SNil{} True{}:
      {==}
    case SCon{+c, +t2} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, +t2} False{}:
      +X = J.cut.go(t2, Char.is_eq(c, '\t'), c)
      %Equal.sym(Strs(), cl(J.cut.k(h, X)), String.split.push(h, cl(X)), cl_k(h, X)) :
        {_ == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      %Equal.sym(Strs(), cl(X), String.split(SCon{c, t2}, '\t'), cut_go(t2, Char.is_eq(c, '\t'), c)) :
        {String.split.push(h, _) == String.split.push(h, String.split(SCon{c, t2}, '\t')) : List<&2, String>}
      {==}

law cut_split:
  for +s: String
  {cl(J.cut(s)) == String.split(s, '\t') : List<&2, String>}

def cut_split(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      cut_go(t, Char.is_eq(h, '\t'), h)

law lt8:
  for +n: Nat
  {Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+n, 8n) == False{} : Bool}

def lt8(n):
  P.lt_zero(n)

def ctail(c: J.Cut) -> List<&2, String>:
  match c:
    case J.Cut{f, r, True{}}:
      String.split(r, '\t')
    case J.Cut{f, r, False{}}:
      Nil{}

def split_ft.k(+c: J.Cut) -> {cl(c) == J.Cut.f(c) <> ctail(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      {==}
    case J.Cut{+f, +r, False{}}:
      {==}

law split_ft:
  for +s: String
  {String.split(s, '\t') == J.Cut.f(J.cut(s)) <> ctail(J.cut(s)) : List<&2, String>}

def split_ft(s):
  %cut_split(s) : {_ == J.Cut.f(J.cut(s)) <> ctail(J.cut(s)) : List<&2, String>}
  split_ft.k(J.cut(s))

# The 7 cut fields and the rest are the line's fields
# ===================================================

def gsplit(g: J.C7, +F: List<&2, String>) -> List<&2, String>:
  match g:
    case J.Got{f0, f1, f2, f3, f4, f5, f6, r}:
      f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t')
    case J.Short{}:
      F

def c7g(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +c: J.Cut) ->
  {gsplit(J.c7.g(f0, f1, f2, f3, f4, f5, c), f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> cl(c)) == f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      {==}
    case J.Cut{+f, +r, False{}}:
      {==}

def c7f(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +c: J.Cut) ->
  {gsplit(J.c7.f(f0, f1, f2, f3, f4, c), f0 <> f1 <> f2 <> f3 <> f4 <> cl(c)) == f0 <> f1 <> f2 <> f3 <> f4 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.g(f0, f1, f2, f3, f4, f, J.cut(r)), f0 <> f1 <> f2 <> f3 <> f4 <> f <> _) == f0 <> f1 <> f2 <> f3 <> f4 <> f <> _ : List<&2, String>}
      c7g(f0, f1, f2, f3, f4, f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

def c7e(+f0: String, +f1: String, +f2: String, +f3: String, +c: J.Cut) ->
  {gsplit(J.c7.e(f0, f1, f2, f3, c), f0 <> f1 <> f2 <> f3 <> cl(c)) == f0 <> f1 <> f2 <> f3 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.f(f0, f1, f2, f3, f, J.cut(r)), f0 <> f1 <> f2 <> f3 <> f <> _) == f0 <> f1 <> f2 <> f3 <> f <> _ : List<&2, String>}
      c7f(f0, f1, f2, f3, f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

def c7d(+f0: String, +f1: String, +f2: String, +c: J.Cut) ->
  {gsplit(J.c7.d(f0, f1, f2, c), f0 <> f1 <> f2 <> cl(c)) == f0 <> f1 <> f2 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.e(f0, f1, f2, f, J.cut(r)), f0 <> f1 <> f2 <> f <> _) == f0 <> f1 <> f2 <> f <> _ : List<&2, String>}
      c7e(f0, f1, f2, f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

def c7c(+f0: String, +f1: String, +c: J.Cut) ->
  {gsplit(J.c7.c(f0, f1, c), f0 <> f1 <> cl(c)) == f0 <> f1 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.d(f0, f1, f, J.cut(r)), f0 <> f1 <> f <> _) == f0 <> f1 <> f <> _ : List<&2, String>}
      c7d(f0, f1, f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

def c7b(+f0: String, +c: J.Cut) ->
  {gsplit(J.c7.b(f0, c), f0 <> cl(c)) == f0 <> cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.c(f0, f, J.cut(r)), f0 <> f <> _) == f0 <> f <> _ : List<&2, String>}
      c7c(f0, f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

def c7a(+c: J.Cut) -> {gsplit(J.c7.a(c), cl(c)) == cl(c) : List<&2, String>}:
  match c:
    case J.Cut{+f, +r, True{}}:
      %cut_split(r) : {gsplit(J.c7.b(f, J.cut(r)), f <> _) == f <> _ : List<&2, String>}
      c7b(f, J.cut(r))
    case J.Cut{+f, +r, False{}}:
      {==}

law c7_split:
  for +body: String
  {gsplit(J.c7(body), B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}

def c7_split(body):
  %cut_split(body) : {gsplit(J.c7.a(J.cut(body)), _) == _ : List<&2, String>}
  c7a(J.cut(body))

# INFO's END check in place
# =========================

def ok32(+x: Bool, +y: Bool) -> {J.ikeyT.ok3(x, y, False{}) == J.ikey.ok2(x, y) : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} _:
      {==}

def cutk_f(+h: Char, +c: J.Cut) -> {J.Cut.f(J.cut.k(h, c)) == SCon{h, J.Cut.f(c)} : String}:
  match c:
    case J.Cut{+f, +r, +ok}:
      {==}

law cutf_cons:
  for +h: Char
  for +t: String
  for +hb: {Char.is_eq(h, '\t') == False{} : Bool}
  {J.Cut.f(J.cut(SCon{h, t})) == SCon{h, J.Cut.f(J.cut(t))} : String}

def cutf_cons(h, t, hb):
  match t:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), False{}, hb) : {J.Cut.f(J.cut.go(SNil{}, _, h)) == SCon{h, J.Cut.f(J.cut(SNil{}))} : String}
      {==}
    case SCon{+c, +t2}:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), False{}, hb) : {J.Cut.f(J.cut.go(SCon{c, t2}, _, h)) == SCon{h, J.Cut.f(J.cut(SCon{c, t2}))} : String}
      cutk_f(h, J.cut.go(t2, Char.is_eq(c, '\t'), c))

def ikt.k(+z: Bool, +h: Char, +t: String, +Y: String, +ih: {J.ikeyT(t) == J.ikey(Y) : String}) ->
  {J.ikeyT.go(SCon{h, t}, z) == J.ikey.go(SCon{h, Y}, z) : String}:
  match z:
    case True{}:
      %Equal.sym(String, J.ikeyT(t), J.ikey(Y), ih) : {SCon{h, _} == SCon{h, J.ikey(Y)} : String}
      {==}
    case False{}:
      {==}

def ikt.f(+x: Bool, +y: Bool, +s: String) -> {J.ikeyT.go(s, J.ikeyT.ok3(x, y, True{})) == J.ikey(SNil{}) : String}:
  match x y s:
    case _ _ SNil{}:
      {==}
    case False{} False{} SCon{+h, +t}:
      {==}
    case False{} True{} SCon{+h, +t}:
      {==}
    case True{} _ SCon{+h, +t}:
      {==}

def ikt.tab(+t: String, +h: Char, +hb: {Char.is_eq(h, '\t') == True{} : Bool}) -> {J.ikeyT(SCon{h, t}) == J.ikey(J.Cut.f(J.cut(SCon{h, t}))) : String}:
  match t:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), True{}, hb) :
        {J.ikeyT.go(SCon{h, SNil{}}, J.ikeyT.ok3(Char.is_eq(h, ';'), Char.is_eq(h, '='), _)) == J.ikey(J.Cut.f(J.cut.go(SNil{}, _, h))) : String}
      ikt.f(Char.is_eq(h, ';'), Char.is_eq(h, '='), SCon{h, SNil{}})
    case SCon{+c, +t2}:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), True{}, hb) :
        {J.ikeyT.go(SCon{h, SCon{c, t2}}, J.ikeyT.ok3(Char.is_eq(h, ';'), Char.is_eq(h, '='), _)) == J.ikey(J.Cut.f(J.cut.go(SCon{c, t2}, _, h))) : String}
      ikt.f(Char.is_eq(h, ';'), Char.is_eq(h, '='), SCon{h, SCon{c, t2}})

def ikt.b(+b: Bool, +h: Char, +t: String, +hb: {Char.is_eq(h, '\t') == b : Bool}, +ih: {J.ikeyT(t) == J.ikey(J.Cut.f(J.cut(t))) : String}) ->
  {J.ikeyT(SCon{h, t}) == J.ikey(J.Cut.f(J.cut(SCon{h, t}))) : String}:
  match b:
    case True{}:
      ikt.tab(t, h, hb)
    case False{}:
      %Equal.sym(String, J.Cut.f(J.cut(SCon{h, t})), SCon{h, J.Cut.f(J.cut(t))}, cutf_cons(h, t, hb)) : {J.ikeyT(SCon{h, t}) == J.ikey(_) : String}
      %Equal.sym(Bool, Char.is_eq(h, '\t'), False{}, hb) :
        {J.ikeyT.go(SCon{h, t}, J.ikeyT.ok3(Char.is_eq(h, ';'), Char.is_eq(h, '='), _)) == J.ikey(SCon{h, J.Cut.f(J.cut(t))}) : String}
      %Equal.sym(Bool, J.ikeyT.ok3(Char.is_eq(h, ';'), Char.is_eq(h, '='), False{}), J.ikey.ok2(Char.is_eq(h, ';'), Char.is_eq(h, '=')), ok32(Char.is_eq(h, ';'), Char.is_eq(h, '='))) :
        {J.ikeyT.go(SCon{h, t}, _) == J.ikey(SCon{h, J.Cut.f(J.cut(t))}) : String}
      ikt.k(J.ikey.ok2(Char.is_eq(h, ';'), Char.is_eq(h, '=')), h, t, J.Cut.f(J.cut(t)), ih)

# The key ikeyT reads is the key of INFO cut off at the tab.
law ikeyT_cut:
  for +s: String
  {J.ikeyT(s) == J.ikey(J.Cut.f(J.cut(s))) : String}

def ikeyT_cut(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      ikt.b(Char.is_eq(h, '\t'), h, t, {==}, ikeyT_cut(t))

def scan.none(+h: Char, +Y: String, +st: Bool, +k: Bool, +hk: {Bool.not(String.eq(J.ikey(SCon{h, Y}), "END")) == True{} : Bool}) ->
  {J.scan(SCon{h, Y}, True{}) == J.scan(Y, Char.is_eq(h, ';')) : List<&2, Maybe<&2, Nat>>}:
  %Equal.sym(Bool, String.eq(J.ikey(SCon{h, Y}), "END"), False{}, P.not_true(String.eq(J.ikey(SCon{h, Y}), "END"), hk)) :
    {J.scan.put(J.end_val(_, SCon{h, Y}), J.scan(Y, Char.is_eq(h, ';'))) == J.scan(Y, Char.is_eq(h, ';')) : List<&2, Maybe<&2, Nat>>}
  {==}

law noend_go:
  for +t: String
  for +h: Char
  for +b: Bool
  for +st: Bool
  for +hb: {Char.is_eq(h, '\t') == b : Bool}
  for +hn: {J.noend.go(t, h, b, st) == True{} : Bool}
  {J.scan(J.Cut.f(J.cut(SCon{h, t})), st) == Nil{} : List<&2, Maybe<&2, Nat>>}

def noend_go(t, h, b, st, hb, hn):
  match t b st:
    case SNil{} True{} _:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), True{}, hb) : {J.scan(J.Cut.f(J.cut.go(SNil{}, _, h)), st) == Nil{} : List<&2, Maybe<&2, Nat>>}
      {==}
    case SCon{+c, +t2} True{} _:
      %Equal.sym(Bool, Char.is_eq(h, '\t'), True{}, hb) : {J.scan(J.Cut.f(J.cut.go(SCon{c, t2}, _, h)), st) == Nil{} : List<&2, Maybe<&2, Nat>>}
      {==}
    case SNil{} False{} True{}:
      +hk = Equal.trans(Bool, Bool.not(String.eq(J.ikey(SCon{h, SNil{}}), "END")), Bool.not(String.eq(J.ikeyT(SCon{h, SNil{}}), "END")), True{},
        Equal.cong(String, Bool, z => Bool.not(String.eq(z, "END")), J.ikey(SCon{h, SNil{}}), J.ikeyT(SCon{h, SNil{}}),
          Equal.sym(String, J.ikeyT(SCon{h, SNil{}}), J.ikey(SCon{h, SNil{}}),
            Equal.trans(String, J.ikeyT(SCon{h, SNil{}}), J.ikey(J.Cut.f(J.cut(SCon{h, SNil{}}))), J.ikey(SCon{h, SNil{}}), ikeyT_cut(SCon{h, SNil{}}),
              Equal.cong(String, String, z => J.ikey(z), J.Cut.f(J.cut(SCon{h, SNil{}})), SCon{h, SNil{}}, cutf_cons(h, SNil{}, hb))))), hn)
      %Equal.sym(String, J.Cut.f(J.cut(SCon{h, SNil{}})), SCon{h, SNil{}}, cutf_cons(h, SNil{}, hb)) : {J.scan(_, True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}
      %Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(SCon{h, SNil{}}, True{}), J.scan(SNil{}, Char.is_eq(h, ';')), scan.none(h, SNil{}, True{}, True{}, hk)) : {_ == Nil{} : List<&2, Maybe<&2, Nat>>}
      {==}
    case SNil{} False{} False{}:
      %Equal.sym(String, J.Cut.f(J.cut(SCon{h, SNil{}})), SCon{h, SNil{}}, cutf_cons(h, SNil{}, hb)) : {J.scan(_, False{}) == Nil{} : List<&2, Maybe<&2, Nat>>}
      {==}
    case SCon{+h2, +t2} False{} True{}:
      +t = {SCon{h2, t2} : String}
      +Y = J.Cut.f(J.cut(t))
      +k1 = Bool.not(String.eq(J.ikeyT(SCon{h, t}), "END"))
      +k2 = J.noend.go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'))
      +hk = Equal.trans(Bool, Bool.not(String.eq(J.ikey(SCon{h, Y}), "END")), k1, True{},
        Equal.cong(String, Bool, z => Bool.not(String.eq(z, "END")), J.ikey(SCon{h, Y}), J.ikeyT(SCon{h, t}),
          Equal.sym(String, J.ikeyT(SCon{h, t}), J.ikey(SCon{h, Y}),
            Equal.trans(String, J.ikeyT(SCon{h, t}), J.ikey(J.Cut.f(J.cut(SCon{h, t}))), J.ikey(SCon{h, Y}), ikeyT_cut(SCon{h, t}),
              Equal.cong(String, String, z => J.ikey(z), J.Cut.f(J.cut(SCon{h, t})), SCon{h, Y}, cutf_cons(h, t, hb))))),
        P.and_true_l(k1, k2, hn))
      %Equal.sym(String, J.Cut.f(J.cut(SCon{h, t})), SCon{h, Y}, cutf_cons(h, t, hb)) : {J.scan(_, True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}
      %Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(SCon{h, Y}, True{}), J.scan(Y, Char.is_eq(h, ';')), scan.none(h, Y, True{}, True{}, hk)) : {_ == Nil{} : List<&2, Maybe<&2, Nat>>}
      noend_go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'), {==}, P.and_true_r(k1, k2, hn))
    case SCon{+h2, +t2} False{} False{}:
      +t = {SCon{h2, t2} : String}
      %Equal.sym(String, J.Cut.f(J.cut(SCon{h, t})), SCon{h, J.Cut.f(J.cut(t))}, cutf_cons(h, t, hb)) : {J.scan(_, False{}) == Nil{} : List<&2, Maybe<&2, Nat>>}
      noend_go(t2, h2, Char.is_eq(h2, '\t'), Char.is_eq(h, ';'), {==}, hn)

law noend_scan:
  for +r: String
  for +hn: {J.noend(r) == True{} : Bool}
  {J.scan(J.Cut.f(J.cut(r)), True{}) == Nil{} : List<&2, Maybe<&2, Nat>>}

def noend_scan(r, hn):
  match r:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      noend_go(t, h, Char.is_eq(h, '\t'), True{}, {==}, hn)

def ie.k(+ne: Bool, +r: String, +e: Nat, +hne: {J.noend(r) == ne : Bool}) ->
  {J.end_ok(J.info.if(ne, r), e) == J.end_ok(J.Cut.f(J.cut(r)), e) : Bool}:
  match ne:
    case True{}:
      %Equal.sym(List<&2, Maybe<&2, Nat>>, J.scan(J.Cut.f(J.cut(r)), True{}), Nil{}, noend_scan(r, hne)) :
        {True{} == B.Info.end_ok.go(_, e) : Bool}
      {==}
    case False{}:
      {==}

# INFO as the machine keeps it passes the END check exactly when INFO does.
law info_end:
  for +r: String
  for +e: Nat
  {J.end_ok(J.info.if(J.noend(r), r), e) == J.end_ok(J.Cut.f(J.cut(r)), e) : Bool}

def info_end(r, e):
  ie.k(J.noend(r), r, e, {==})

# The machine's fields agree with the line's
# ==========================================

def PG(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +x: String) -> List<&2, String>:
  [f0, f1, f2, f3, f4, f5, f6, x]

def FG(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +y: String, +T: List<&2, String>) -> List<&2, String>:
  f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> y <> T

law sh_mal:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +x: String
  for +y: String
  for +T: List<&2, String>
  {B.Rec.malformed(PG(f0, f1, f2, f3, f4, f5, f6, x)) == B.Rec.malformed(FG(f0, f1, f2, f3, f4, f5, f6, y, T)) : Bool}

def sh_mal(f0, f1, f2, f3, f4, f5, f6, x, y, T):
  %Equal.sym(Bool, Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+List.length(&2, String, T), 8n), False{}, lt8(List.length(&2, String, T))) :
    {B.Rec.malformed(PG(f0, f1, f2, f3, f4, f5, f6, x)) ==
      (((_ || String.is_empty(f0)) || Maybe.is_none(&2, Nat, B.Pos.read(f1))) || Bool.not(B.Text.is_letters(f3))) || B.Text.any_empty(String.split(f4, ',')) : Bool}
  {==}

def sh_jgo(+b: Bool, +s: Bool, +P0: List<&2, String>, +F0: List<&2, String>, +body: String, +hp: {B.Rec.pos(P0) == B.Rec.pos(F0) : Nat}) ->
  {J.judge_in.go(b, s, None{}, P0, body) == J.judge_in.go(b, s, None{}, F0, body) : Maybe<&2, B.Res>}:
  match b s:
    case True{} _:
      %Equal.sym(Nat, B.Rec.pos(P0), B.Rec.pos(F0), hp) : {Some{B.Res{B.Broken{}, _, body, False{}}} == Some{B.Res{B.Broken{}, B.Rec.pos(F0), body, False{}}} : Maybe<&2, B.Res>}
      {==}
    case False{} True{}:
      %Equal.sym(Nat, B.Rec.pos(P0), B.Rec.pos(F0), hp) : {Some{B.Res{B.Skipped{}, _, body, False{}}} == Some{B.Res{B.Skipped{}, B.Rec.pos(F0), body, False{}}} : Maybe<&2, B.Res>}
      {==}
    case False{} False{}:
      {==}

def sh_fgo(+b: Bool, +s: Bool, +a: Maybe<&2, J.Ans>, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +x: String, +y: String,
  +T: List<&2, String>, +body: String,
  +hx: {J.end_ok(x, Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(f1), 0n), String.length(f3)), 1n)) == J.end_ok(y, Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(f1), 0n), String.length(f3)), 1n)) : Bool}) ->
  {J.fast.go(b, s, a, PG(f0, f1, f2, f3, f4, f5, f6, x), body) == J.fast.go(b, s, a, FG(f0, f1, f2, f3, f4, f5, f6, y, T), body) : J.Fast}:
  match b s a:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} None{}:
      {==}
    case False{} False{} Some{J.Unknown{}}:
      {==}
    case False{} False{} Some{J.Known{+clen, +off, +raw}}:
      +e = Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(f1), 0n), String.length(f3)), 1n)
      +pos = Maybe.default(&2, Nat, B.Pos.read(f1), 0n)
      %Equal.sym(Bool, J.end_ok(x, e), J.end_ok(y, e), hx) : {J.fast.found(_, B.Allele.read(f3), B.Alleles.read(String.split(f4, ',')), clen, off, B.Bases.of_fasta(raw), pos, f1, f3, f4, body)
        == J.fast.found(J.end_ok(y, e), B.Allele.read(f3), B.Alleles.read(String.split(f4, ',')), clen, off, B.Bases.of_fasta(raw), pos, f1, f3, f4, body) : J.Fast}
      {==}

# What the machine reads of a line, from its fields as pfs keeps them.
def PK(+g: J.C7, +body: String) -> List<&2, String>:
  J.pfs.g(g, body)

law judge_none:
  for +body: String
  {J.judge_fs(None{}, J.pfs(body), body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}

def jn.k(+g: J.C7, +body: String, +hg: {gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}) ->
  {J.judge_fs(None{}, J.pfs.g(g, body), body) == J.judge_in(None{}, body) : Maybe<&2, B.Res>}:
  match g:
    case J.Short{}:
      {==}
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      +x = J.info.if(J.noend(r), r)
      +y = J.Cut.f(J.cut(r))
      +T = ctail(J.cut(r))
      +F = B.Rec.fields(body)
      +hF = Equal.trans(Strs(), F, f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), FG(f0, f1, f2, f3, f4, f5, f6, y, T),
        Equal.sym(Strs(), f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), F, hg),
        Equal.cong(Strs(), Strs(), z => f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> z, String.split(r, '\t'), y <> T, split_ft(r)))
      %Equal.sym(Strs(), F, FG(f0, f1, f2, f3, f4, f5, f6, y, T), hF) : {J.judge_fs(None{}, PG(f0, f1, f2, f3, f4, f5, f6, x), body) == J.judge_fs(None{}, _, body) : Maybe<&2, B.Res>}
      %Equal.sym(Bool, B.Rec.malformed(PG(f0, f1, f2, f3, f4, f5, f6, x)), B.Rec.malformed(FG(f0, f1, f2, f3, f4, f5, f6, y, T)), sh_mal(f0, f1, f2, f3, f4, f5, f6, x, y, T)) :
        {J.judge_in.go(_, B.Rec.out_of_scope(PG(f0, f1, f2, f3, f4, f5, f6, x)), None{}, PG(f0, f1, f2, f3, f4, f5, f6, x), body) == J.judge_fs(None{}, FG(f0, f1, f2, f3, f4, f5, f6, y, T), body) : Maybe<&2, B.Res>}
      sh_jgo(B.Rec.malformed(FG(f0, f1, f2, f3, f4, f5, f6, y, T)), B.Rec.out_of_scope(FG(f0, f1, f2, f3, f4, f5, f6, y, T)),
        PG(f0, f1, f2, f3, f4, f5, f6, x), FG(f0, f1, f2, f3, f4, f5, f6, y, T), body, {==})

def judge_none(body):
  jn.k(J.c7(body), body, c7_split(body))

def pf.i(+i: Nat, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +x: String, +T: List<&2, String>, +h: {Nat.is_lt(i, 7n) == True{} : Bool}) ->
  {B.Rec.field(PG(f0, f1, f2, f3, f4, f5, f6, x), i) == B.Rec.field(f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> T, i) : String}:
  match i:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 1n+1n+1n+1n+1n+1n+1n+j:
      Empty.absurd({B.Rec.field(PG(f0, f1, f2, f3, f4, f5, f6, x), 7n+j) == B.Rec.field(f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> T, 7n+j) : String},
        P.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, P.lt_zero(j)), h)))

def pf.k(+g: J.C7, +body: String, +i: Nat, +h: {Nat.is_lt(i, 7n) == True{} : Bool}, +hg: {gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}) ->
  {B.Rec.field(J.pfs.g(g, body), i) == B.Rec.field(B.Rec.fields(body), i) : String}:
  match g:
    case J.Short{}:
      {==}
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      %hg : {B.Rec.field(J.pfs.g(J.Got{f0, f1, f2, f3, f4, f5, f6, r}, body), i) == B.Rec.field(_, i) : String}
      pf.i(i, f0, f1, f2, f3, f4, f5, f6, J.info.if(J.noend(r), r), String.split(r, '\t'), h)

law pfs_field:
  for +body: String
  for +i: Nat
  for +h: {Nat.is_lt(i, 7n) == True{} : Bool}
  {B.Rec.field(J.pfs(body), i) == B.Rec.field(B.Rec.fields(body), i) : String}

def pfs_field(body, i, h):
  pf.k(J.c7(body), body, i, h, c7_split(body))

law pfs_pos:
  for +body: String
  {B.Rec.pos(J.pfs(body)) == B.Rec.pos(B.Rec.fields(body)) : Nat}

def pfs_pos(body):
  %Equal.sym(String, B.Rec.field(J.pfs(body), 1n), B.Rec.field(B.Rec.fields(body), 1n), pfs_field(body, 1n, {==})) :
    {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == B.Rec.pos(B.Rec.fields(body)) : Nat}
  {==}

def RES(+p: Nat, +body: String) -> Maybe<&2, B.Res>:
  Some{B.Res{B.Normalized{}, p, body, False{}}}

law same_var_sound:
  for +v: B.Var
  for +w: B.Var
  for +e: {B.Rec.same_var(v, w) == True{} : Bool}
  {w == v : B.Var}

def same_var_sound(v, w, e):
  match v w:
    case B.Var{+p, +r, +x} B.Var{+q, +s, +y}:
      +e12 = P.and_true_l(Bool.and(Nat.is_eq(p, q), B.Bases.eq(r, s)), B.Alleles.eq(x, y), e)
      +hp = P.eq_sound(p, q, P.and_true_l(Nat.is_eq(p, q), B.Bases.eq(r, s), e12))
      +hr = VL.bases_sound(r, s, P.and_true_r(Nat.is_eq(p, q), B.Bases.eq(r, s), e12))
      +hx = VL.alleles_sound(x, y, P.and_true_r(Bool.and(Nat.is_eq(p, q), B.Bases.eq(r, s)), B.Alleles.eq(x, y), e))
      %Equal.sym(Nat, p, q, hp) : {B.Var{q, s, y} == B.Var{_, r, x} : B.Var}
      %Equal.sym(List<&2, B.Base>, r, s, hr) : {B.Var{q, s, y} == B.Var{q, _, x} : B.Var}
      %Equal.sym(List<&2, List<&2, B.Base>>, x, y, hx) : {B.Var{q, s, y} == B.Var{q, s, _} : B.Var}
      {==}

def RBG(+fs: List<&2, String>, +x1: String, +x3: String, +x4: String, +x7: String) -> String:
  String.join(B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(fs, 1n, x1), 3n, x3), 4n, x4), 7n, x7), "\t")

# The record rewritten for itself is its text, when POS, REF and ALT are
# written as rebuild writes them.
law rebuild_same:
  for +fs: List<&2, String>
  for +p: Nat
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +body: String
  for +hj: {String.join(fs, "\t") == body : String}
  for +ht: {J.same.text(B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), B.Rec.field(fs, 4n), B.Var{p, r, a}) == True{} : Bool}
  {B.Rec.rebuild(fs, B.Var{p, r, a}, B.Var{p, r, a}) == body : String}

def rebuild_same(fs, p, r, a, body, hj, ht):
  +s1 = String.eq(Nat.show(p), B.Rec.field(fs, 1n))
  +s3 = String.eq(B.Allele.show(r), B.Rec.field(fs, 3n))
  +s4 = String.eq(String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n))
  +h13 = P.and_true_l(Bool.and(s1, s3), s4, ht)
  +e1 = Q.str_eq_sound(Nat.show(p), B.Rec.field(fs, 1n), P.and_true_l(s1, s3, h13))
  +e3 = Q.str_eq_sound(B.Allele.show(r), B.Rec.field(fs, 3n), P.and_true_r(s1, s3, h13))
  +e4 = Q.str_eq_sound(String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n), P.and_true_r(Bool.and(s1, s3), s4, ht))
  +nr = List.length(&2, B.Base, r)
  %Equal.sym(Bool, Nat.is_eq(p, p), True{}, P.eq_refl(p)) :
    {RBG(fs, Nat.show(p), B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.info(Bool.not(Bool.and(_, Nat.is_eq(nr, nr))), B.Rec.field(fs, 7n), B.Var{p, r, a})) == body : String}
  %Equal.sym(Bool, Nat.is_eq(nr, nr), True{}, P.eq_refl(nr)) :
    {RBG(fs, Nat.show(p), B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.info(Bool.not(Bool.and(True{}, _)), B.Rec.field(fs, 7n), B.Var{p, r, a})) == body : String}
  %Equal.sym(String, Nat.show(p), B.Rec.field(fs, 1n), e1) :
    {RBG(fs, _, B.Allele.show(r), String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(String, B.Allele.show(r), B.Rec.field(fs, 3n), e3) :
    {RBG(fs, B.Rec.field(fs, 1n), _, String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(String, String.join(B.Alleles.show(a), ","), B.Rec.field(fs, 4n), e4) :
    {RBG(fs, B.Rec.field(fs, 1n), B.Rec.field(fs, 3n), _, B.Rec.field(fs, 7n)) == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 1n, B.Rec.field(fs, 1n)), fs, RR.put_same(fs, 1n, B.Rec.field(fs, 1n), {==})) :
    {String.join(B.Rec.put(B.Rec.put(B.Rec.put(_, 3n, B.Rec.field(fs, 3n)), 4n, B.Rec.field(fs, 4n)), 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 3n, B.Rec.field(fs, 3n)), fs, RR.put_same(fs, 3n, B.Rec.field(fs, 3n), {==})) :
    {String.join(B.Rec.put(B.Rec.put(_, 4n, B.Rec.field(fs, 4n)), 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 4n, B.Rec.field(fs, 4n)), fs, RR.put_same(fs, 4n, B.Rec.field(fs, 4n), {==})) :
    {String.join(B.Rec.put(_, 7n, B.Rec.field(fs, 7n)), "\t") == body : String}
  %Equal.sym(Strs(), B.Rec.put(fs, 7n, B.Rec.field(fs, 7n)), fs, RR.put_same(fs, 7n, B.Rec.field(fs, 7n), {==})) :
    {String.join(_, "\t") == body : String}
  hj

# What a J.Fast result says judge_in gives (p: the record's POS).
def fr_res(f: J.Fast, +p: Nat, +body: String) -> Maybe<&2, B.Res>:
  match f:
    case J.Same{}:
      RES(p, body)
    case J.Other{m}:
      m

def Fs(+body: String) -> List<&2, String>:
  B.Rec.fields(body)

def V0(+body: String, +r: List<&2, B.Base>, +a: List<&2, List<&2, B.Base>>) -> B.Var:
  B.Var{B.Rec.pos(Fs(body)), r, a}

law k_normk:
  for +ok: Bool
  for +w: B.Var
  for +body: String
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  for +hok: {Bool.and(B.Rec.same_var(V0(body, r, a), w), J.same.text(B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), V0(body, r, a))) == ok : Bool}
  {fr_res(J.fast.norm.k(ok, V0(body, r, a), w, body), B.Rec.pos(Fs(body)), body) == J.found.norm(Some{w}, Fs(body), V0(body, r, a)) : Maybe<&2, B.Res>}

def k_normk(ok, w, body, r, a, hok):
  match ok:
    case False{}:
      {==}
    case True{}:
      +F = Fs(body)
      +p = B.Rec.pos(F)
      +v = V0(body, r, a)
      +sv = B.Rec.same_var(v, w)
      +tx = J.same.text(B.Rec.field(F, 1n), B.Rec.field(F, 3n), B.Rec.field(F, 4n), v)
      +hsv = P.and_true_l(sv, tx, hok)
      %Equal.sym(Bool, sv, True{}, hsv) :
        {RES(p, body) == Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(F, v, w), B.Rec.stale.if(_, F)}} : Maybe<&2, B.Res>}
      %Equal.sym(B.Var, w, v, same_var_sound(v, w, hsv)) :
        {RES(p, body) == Some{B.Res{B.Normalized{}, B.Var.pos(_), B.Rec.rebuild(F, v, _), False{}}} : Maybe<&2, B.Res>}
      %Equal.sym(String, B.Rec.rebuild(F, v, v), body, rebuild_same(F, p, r, a, body, RR.join_split(body, '\t'), P.and_true_r(sv, tx, hok))) :
        {RES(p, body) == Some{B.Res{B.Normalized{}, p, _, False{}}} : Maybe<&2, B.Res>}
      {==}

law k_norm:
  for +m: Maybe<&2, B.Var>
  for +body: String
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  {fr_res(J.fast.norm(m, B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), V0(body, r, a), body), B.Rec.pos(Fs(body)), body)
    == J.found.norm(m, Fs(body), V0(body, r, a)) : Maybe<&2, B.Res>}

def k_norm(m, body, r, a):
  match m:
    case None{}:
      {==}
    case Some{+w}:
      +v = V0(body, r, a)
      k_normk(Bool.and(B.Rec.same_var(v, w), J.same.text(B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), v)), w, body, r, a, {==})

law k_ref:
  for +ok: Maybe<&2, Bool>
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +body: String
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  {fr_res(J.fast.ref(ok, off, bases, B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), V0(body, r, a), B.Rec.pos(Fs(body)), body), B.Rec.pos(Fs(body)), body)
    == J.found.ref(ok, off, bases, Fs(body), body, V0(body, r, a)) : Maybe<&2, B.Res>}

def k_ref(ok, off, bases, body, r, a):
  match ok:
    case None{}:
      {==}
    case Some{False{}}:
      {==}
    case Some{True{}}:
      k_norm(V.var_in(off, bases, V0(body, r, a)), body, r, a)

law k_problem:
  for +z: Bool
  for +d: Bool
  for +clen: Nat
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +body: String
  for +r: List<&2, B.Base>
  for +a: List<&2, List<&2, B.Base>>
  {fr_res(J.fast.problem(z, d, clen, off, bases, B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), V0(body, r, a), B.Rec.pos(Fs(body)), body), B.Rec.pos(Fs(body)), body)
    == J.found.problem(z, d, clen, off, bases, Fs(body), body, V0(body, r, a)) : Maybe<&2, B.Res>}

def k_problem(z, d, clen, off, bases, body, r, a):
  match z d:
    case True{} _:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      k_ref(J.ref_check(clen, off, bases, Nat.sub(B.Rec.pos(Fs(body)), 1n), r), off, bases, body, r, a)

law k_found:
  for +e: Bool
  for +rr: Maybe<&2, List<&2, B.Base>>
  for +aa: Maybe<&2, List<&2, List<&2, B.Base>>>
  for +clen: Nat
  for +off: Nat
  for +bases: List<&2, B.Base>
  for +body: String
  {fr_res(J.fast.found(e, rr, aa, clen, off, bases, B.Rec.pos(Fs(body)), B.Rec.field(Fs(body), 1n), B.Rec.field(Fs(body), 3n), B.Rec.field(Fs(body), 4n), body), B.Rec.pos(Fs(body)), body)
    == J.found(e, rr, aa, clen, off, bases, Fs(body), body) : Maybe<&2, B.Res>}

def k_found(e, rr, aa, clen, off, bases, body):
  match e rr aa:
    case False{} _ _:
      {==}
    case True{} Some{+ref} Some{+alts}:
      k_problem(Nat.is_eq(B.Rec.pos(Fs(body)), 0n), B.Alleles.distinct(ref <> alts), clen, off, bases, body, ref, alts)
    case True{} Some{ref} None{}:
      {==}
    case True{} None{} _:
      {==}

law k_go:
  for +b: Bool
  for +s: Bool
  for +a: Maybe<&2, J.Ans>
  for +body: String
  {fr_res(J.fast.go(b, s, a, Fs(body), body), B.Rec.pos(Fs(body)), body) == J.judge_in.go(b, s, a, Fs(body), body) : Maybe<&2, B.Res>}

def k_go(b, s, a, body):
  match b s a:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} None{}:
      {==}
    case False{} False{} Some{J.Unknown{}}:
      {==}
    case False{} False{} Some{J.Known{+clen, +off, +raw}}:
      +F = Fs(body)
      +ref = B.Rec.field(F, 3n)
      +e = Nat.sub(Nat.add(B.Rec.pos(F), String.length(ref)), 1n)
      k_found(J.end_ok(B.Rec.field(F, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(F)), clen, off, B.Bases.of_fasta(raw), body)

def fj.k(+g: J.C7, +a: Maybe<&2, J.Ans>, +body: String, +hg: {gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}) ->
  {J.fast(a, J.pfs.g(g, body), body) == J.fast(a, B.Rec.fields(body), body) : J.Fast}:
  match g:
    case J.Short{}:
      {==}
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      +x = J.info.if(J.noend(r), r)
      +y = J.Cut.f(J.cut(r))
      +T = ctail(J.cut(r))
      +F = B.Rec.fields(body)
      +hF = Equal.trans(Strs(), F, f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), FG(f0, f1, f2, f3, f4, f5, f6, y, T),
        Equal.sym(Strs(), f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> String.split(r, '\t'), F, hg),
        Equal.cong(Strs(), Strs(), z => f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> z, String.split(r, '\t'), y <> T, split_ft(r)))
      %Equal.sym(Strs(), F, FG(f0, f1, f2, f3, f4, f5, f6, y, T), hF) : {J.fast(a, PG(f0, f1, f2, f3, f4, f5, f6, x), body) == J.fast(a, _, body) : J.Fast}
      %Equal.sym(Bool, B.Rec.malformed(PG(f0, f1, f2, f3, f4, f5, f6, x)), B.Rec.malformed(FG(f0, f1, f2, f3, f4, f5, f6, y, T)), sh_mal(f0, f1, f2, f3, f4, f5, f6, x, y, T)) :
        {J.fast.go(_, B.Rec.out_of_scope(PG(f0, f1, f2, f3, f4, f5, f6, x)), a, PG(f0, f1, f2, f3, f4, f5, f6, x), body) == J.fast(a, FG(f0, f1, f2, f3, f4, f5, f6, y, T), body) : J.Fast}
      sh_fgo(B.Rec.malformed(FG(f0, f1, f2, f3, f4, f5, f6, y, T)), B.Rec.out_of_scope(FG(f0, f1, f2, f3, f4, f5, f6, y, T)), a, f0, f1, f2, f3, f4, f5, f6, x, y, T, body,
        info_end(r, Nat.sub(Nat.add(Maybe.default(&2, Nat, B.Pos.read(f1), 0n), String.length(f3)), 1n)))

# J.fast on the machine's fields says what judge_in gives.
law fast_judge:
  for +a: Maybe<&2, J.Ans>
  for +body: String
  {fr_res(J.fast(a, J.pfs(body), body), B.Rec.pos(B.Rec.fields(body)), body) == J.judge_in(a, body) : Maybe<&2, B.Res>}

def fast_judge(a, body):
  +F = Fs(body)
  %Equal.sym(J.Fast, J.fast(a, J.pfs(body), body), J.fast(a, F, body), fj.k(J.c7(body), a, body, c7_split(body))) :
    {fr_res(_, B.Rec.pos(F), body) == J.judge_in(a, body) : Maybe<&2, B.Res>}
  k_go(B.Rec.malformed(F), B.Rec.out_of_scope(F), a, body)
