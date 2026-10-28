import Base
import ./types.bend as B
import ./norm_line.bend as J
import ./proof_base.bend as P

# String facts copied from proof_fast.bend (which imports LAWS.bend, whose
# open laws would count here): J.cut against String.split at tabs, and
# J.noend passing means INFO, cut at its tab, has no END entry for J.scan.

def Strs() -> Data:
  List<&2, String>

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
