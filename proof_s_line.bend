import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_b_alleles_list.bend as LS
import ./proof_b_alleles_loop.bend as AL
import ./proof_s_w.bend as W
import ./proof_s_wt.bend as WT
import ./proof_s_cut.bend as K
import ./proof_s_read.bend as RD
import ./proof_s_tok.bend as TK
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_seq.bend as Q
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-fields@0.1.1.0/fields.bend as FC
import lawful-fields@0.1.1.0/LAWS.bend as FL
import lawful-fields@0.1.1.0/PROOF.bend as FP
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# What B.Rec.parts reads of a line, against what the byte splitter's driver
# (norm_split.bend's go.*) tests: the line's body and terminator
# (B.Text.line), its fields, its ALTs, and that it is not MALFORMED. Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

def Ss() -> Data:
  List<&2, String>

def Rgs() -> Data:
  List<&2, NS.Rg>

def X(+len: U32, +t: AT.Tree<U32>) -> L32():
  D.view(C.BT(len, t))

# ---------------------------------------------------------------------------
# Strings: the last char
# ---------------------------------------------------------------------------

law rev_snoc:
  for +u: String
  for +c: Char
  for +acc: String
  {String.reverse.go(String.append(u, SCon{c, SNil{}}), acc) == SCon{c, String.reverse.go(u, acc)} : String}

def rev_snoc(u, c, acc):
  match u:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      rev_snoc(r, c, SCon{h, acc})

def ec.k(+c: Bool, +acc: String) -> {String.starts_with.go.if(SNil{}, acc, c) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ends_cr(+u: String, +x: U32) -> {String.ends_with(String.append(u, SCon{Chr{x}, SNil{}}), "\r") == U32.is_eq(x, 13) : Bool}:
  %Equal.sym(String, String.reverse.go(String.append(u, SCon{Chr{x}, SNil{}}), SNil{}), SCon{Chr{x}, String.reverse.go(u, SNil{})}, rev_snoc(u, Chr{x}, SNil{})) :
    {String.starts_with(_, "\r") == U32.is_eq(x, 13) : Bool}
  ec.k(U32.is_eq(x, 13), String.reverse.go(u, SNil{}))

def tk0(+v: String) -> {String.take(v, 0n) == "" : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      {==}

law take_app:
  for +u: String
  for +v: String
  {String.take(String.append(u, v), String.length(u)) == u : String}

def take_app(u, v):
  match u:
    case SNil{}:
      tk0(v)
    case SCon{+h, +r}:
      %Equal.sym(String, String.take(String.append(r, v), String.length(r)), r, take_app(r, v)) : {SCon{h, _} == SCon{h, r} : String}
      {==}

law len_snoc:
  for +u: String
  for +c: Char
  {String.length(String.append(u, SCon{c, SNil{}})) == 1n+String.length(u) : Nat}

def len_snoc(u, c):
  match u:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(Nat, String.length(String.append(r, SCon{c, SNil{}})), 1n+String.length(r), len_snoc(r, c)) : {1n+_ == 1n+1n+String.length(r) : Nat}
      {==}

# ---------------------------------------------------------------------------
# The line before its LF: B.Text.line's body and terminator as ranges
# ---------------------------------------------------------------------------

def U1(+lf: U32) -> U32:
  (lf - 1 : U32)

def TXR(+len: U32, +t: AT.Tree<U32>, +a: U32, +z: U32) -> String:
  WT.TX(len, t, NS.Rg{a, z})

def lf_u(+lf: U32, +h1: {Nat.is_le(1n, n(lf)) == True{} : Bool}) -> {1n+n(U1(lf)) == n(lf) : Nat}:
  %Equal.sym(Nat, n(U1(lf)), Nat.sub(n(lf), 1n), W.nsub(1, lf, h1)) : {1n+_ == n(lf) : Nat}
  %N.add_one(Nat.sub(n(lf), 1n)) : {_ == n(lf) : Nat}
  %N.add_comm(1n, Nat.sub(n(lf), 1n)) : {_ == n(lf) : Nat}
  N.le_sub_add(1n, n(lf), h1)

def one_le(+s: U32, +lf: U32, +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}) -> {Nat.is_le(1n, n(lf)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(1n, n(lf)), Nat.is_lt(0n, n(lf)), True{}, N.le_succ_lt(0n, n(lf)),
    N.le_lt_trans(0n, n(s), n(lf), N.le_zero_l(n(s)), hsl))

def u_lt(+lf: U32, +E: {1n+n(U1(lf)) == n(lf) : Nat}) -> {Nat.is_lt(n(U1(lf)), n(lf)) == True{} : Bool}:
  %E : {Nat.is_lt(n(U1(lf)), _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(n(U1(lf)), 1n+n(U1(lf))), Nat.is_le(n(U1(lf)), n(U1(lf))), True{}, N.lt_succ_iff(n(U1(lf)), n(U1(lf))), N.le_refl(n(U1(lf))))

def s_le_u(+s: U32, +lf: U32, +E: {1n+n(U1(lf)) == n(lf) : Nat}, +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}) -> {Nat.is_le(n(s), n(U1(lf))) == True{} : Bool}:
  +h = {%Equal.sym(Nat, 1n+n(U1(lf)), n(lf), E) : {Nat.is_lt(n(s), _) == True{} : Bool}; hsl : {Nat.is_lt(n(s), 1n+n(U1(lf))) == True{} : Bool}}
  Equal.trans(Bool, Nat.is_le(n(s), n(U1(lf))), Nat.is_lt(n(s), 1n+n(U1(lf))), True{}, Equal.sym(Bool, Nat.is_lt(n(s), 1n+n(U1(lf))), Nat.is_le(n(s), n(U1(lf))), N.lt_succ_iff(n(s), n(U1(lf)))), h)

def ult(+a: U32, +len: U32, +h: {Nat.is_lt(n(a), n(len)) == True{} : Bool}) -> {U32.is_lt(a, len) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(a, len), Nat.is_lt(n(a), n(len)), True{}, U.is_lt_to_nat(a, len), h)

# The byte before the LF alone.
def sl_last(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +lf: U32,
  +E: {1n+n(U1(lf)) == n(lf) : Nat}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  {W.SL(len, t, U1(lf), lf) == [C.AT(len, t, U1(lf))] : L32()}:
  +u = U1(lf)
  +hut = ult(u, len, N.lt_trans(n(u), n(lf), n(len), u_lt(lf, E), hlf))
  +eu1 = U.to_nat_inj((u + 1 : U32), lf, Equal.trans(Nat, n((u + 1 : U32)), Nat.add(n(u), 1n), n(lf), W.inc_n(len, t, d, u, hl, hut),
    Equal.trans(Nat, Nat.add(n(u), 1n), 1n+n(u), n(lf), N.add_one(n(u)), E)))
  %eu1 : {W.SL(len, t, u, _) == [C.AT(len, t, u)] : L32()}
  WT.sl_one(len, t, d, u, hl, hut)

# The text before the LF: the text before its last byte, then that byte.
def last_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  {TXR(len, t, s, lf) == String.append(TXR(len, t, s, U1(lf)), SCon{Chr{C.AT(len, t, U1(lf))}, SNil{}}) : String}:
  +u = U1(lf)
  +E = lf_u(lf, one_le(s, lf, hsl))
  %Equal.sym(String, NR.chars(W.SL(len, t, s, lf)), String.append(NR.chars(W.SL(len, t, s, u)), NR.chars(W.SL(len, t, u, lf))),
    WT.tx_app(len, t, s, u, lf, s_le_u(s, lf, E, hsl), N.lt_to_le(n(u), n(lf), u_lt(lf, E)))) :
    {_ == String.append(TXR(len, t, s, u), SCon{Chr{C.AT(len, t, u)}, SNil{}}) : String}
  %Equal.sym(L32(), W.SL(len, t, u, lf), [C.AT(len, t, u)], sl_last(len, t, d, hl, lf, E, hlf)) :
    {String.append(NR.chars(W.SL(len, t, s, u)), NR.chars(_)) == String.append(TXR(len, t, s, u), SCon{Chr{C.AT(len, t, u)}, SNil{}}) : String}
  {==}

# The LF alone.
def t_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +lf: U32,
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, +h10: {C.AT(len, t, lf) == 10 : U32}) ->
  {TXR(len, t, lf, (lf + 1 : U32)) == "\n" : String}:
  %Equal.sym(L32(), W.SL(len, t, lf, (lf + 1 : U32)), [C.AT(len, t, lf)], WT.sl_one(len, t, d, lf, hl, ult(lf, len, hlf))) :
    {NR.chars(_) == "\n" : String}
  %Equal.sym(U32, C.AT(len, t, lf), 10, h10) : {NR.chars([_]) == "\n" : String}
  {==}

# CR LF.
def t_crlf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +h10: {C.AT(len, t, lf) == 10 : U32}, +h13: {C.AT(len, t, U1(lf)) == 13 : U32}) ->
  {TXR(len, t, U1(lf), (lf + 1 : U32)) == "\r\n" : String}:
  +u = U1(lf)
  +E = lf_u(lf, one_le(s, lf, hsl))
  +e1 = W.inc_n(len, t, d, lf, hl, ult(lf, len, hlf))
  +hle = {%Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), e1) : {Nat.is_le(n(lf), _) == True{} : Bool}; N.le_add_r(n(lf), 1n) : {Nat.is_le(n(lf), n((lf + 1 : U32))) == True{} : Bool}}
  %Equal.sym(String, NR.chars(W.SL(len, t, u, (lf + 1 : U32))), String.append(NR.chars(W.SL(len, t, u, lf)), NR.chars(W.SL(len, t, lf, (lf + 1 : U32)))),
    WT.tx_app(len, t, u, lf, (lf + 1 : U32), N.lt_to_le(n(u), n(lf), u_lt(lf, E)), hle)) : {_ == "\r\n" : String}
  %Equal.sym(String, TXR(len, t, lf, (lf + 1 : U32)), "\n", t_lf(len, t, d, hl, lf, hlf, h10)) : {String.append(NR.chars(W.SL(len, t, u, lf)), _) == "\r\n" : String}
  %Equal.sym(L32(), W.SL(len, t, u, lf), [C.AT(len, t, u)], sl_last(len, t, d, hl, lf, E, hlf)) : {String.append(NR.chars(_), "\n") == "\r\n" : String}
  %Equal.sym(U32, C.AT(len, t, u), 13, h13) : {String.append(NR.chars([_]), "\n") == "\r\n" : String}
  {==}

# The body's end: before the CR when the line ends with CR LF.
def BEk(+c: Bool, +x: U32, +lf: U32) -> U32:
  Bool.pick(U32, c && U32.is_eq(x, 13), (lf - 1 : U32), lf)

def XC(+len: U32, +t: AT.Tree<U32>, +c: Bool, +lf: U32) -> U32:
  C.AT(len, t, Bool.pick(U32, c, (lf - 1 : U32), lf))

def BE(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32) -> U32:
  BEk(U32.is_lt(s, lf), XC(len, t, U32.is_lt(s, lf), lf), lf)

def LINE(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32, +be: U32) -> B.Line:
  B.Line{TXR(len, t, s, be), TXR(len, t, be, (lf + 1 : U32))}

def line.c(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +h10: {C.AT(len, t, lf) == 10 : U32}, +c: Bool, +e: {U32.is_eq(C.AT(len, t, U1(lf)), 13) == c : Bool}) ->
  {B.Text.line(TXR(len, t, s, lf)) == LINE(len, t, s, lf, Bool.pick(U32, c, U1(lf), lf)) : B.Line}:
  match c:
    case True{}:
      +u = U1(lf)
      +P = TXR(len, t, s, lf)
      +Q = TXR(len, t, s, u)
      +P1 = String.append(Q, SCon{Chr{C.AT(len, t, u)}, SNil{}})
      +el = last_t(len, t, d, hl, s, lf, hsl, hlf)
      +ex = U.is_eq_true(C.AT(len, t, u), 13, e)
      +P2 = String.append(Q, "\r")
      +eP = Equal.trans(String, P, P1, P2, el, Equal.cong(U32, String, x => String.append(Q, SCon{Chr{x}, SNil{}}), C.AT(len, t, u), 13, ex))
      %Equal.sym(String, TXR(len, t, u, (lf + 1 : U32)), "\r\n", t_crlf(len, t, d, hl, s, lf, hsl, hlf, h10, ex)) : {B.Text.line(P) == B.Line{Q, _} : B.Line}
      %Equal.sym(String, P, P2, eP) : {B.Text.line(_) == B.Line{Q, "\r\n"} : B.Line}
      %Equal.sym(Bool, String.ends_with(P2, "\r"), True{}, ends_cr(Q, 13)) : {B.Text.line.if(_, P2) == B.Line{Q, "\r\n"} : B.Line}
      %Equal.sym(Nat, String.length(P2), 1n+String.length(Q), len_snoc(Q, '\r')) : {B.Line{String.take(P2, Nat.sub(_, 1n)), "\r\n"} == B.Line{Q, "\r\n"} : B.Line}
      %Equal.sym(Nat, Nat.sub(String.length(Q), 0n), String.length(Q), N.sub_zero(String.length(Q))) : {B.Line{String.take(P2, _), "\r\n"} == B.Line{Q, "\r\n"} : B.Line}
      %Equal.sym(String, String.take(P2, String.length(Q)), Q, take_app(Q, "\r")) : {B.Line{_, "\r\n"} == B.Line{Q, "\r\n"} : B.Line}
      {==}
    case False{}:
      +u = U1(lf)
      +P = TXR(len, t, s, lf)
      +Q = TXR(len, t, s, u)
      +P1 = String.append(Q, SCon{Chr{C.AT(len, t, u)}, SNil{}})
      +el = last_t(len, t, d, hl, s, lf, hsl, hlf)
      +ef = {%Equal.sym(String, P, P1, el) : {String.ends_with(_, "\r") == False{} : Bool};
        %Equal.sym(Bool, String.ends_with(P1, "\r"), U32.is_eq(C.AT(len, t, u), 13), ends_cr(Q, C.AT(len, t, u))) : {_ == False{} : Bool};
        e : {String.ends_with(P, "\r") == False{} : Bool}}
      %Equal.sym(String, TXR(len, t, lf, (lf + 1 : U32)), "\n", t_lf(len, t, d, hl, lf, hlf, h10)) : {B.Text.line(P) == B.Line{P, _} : B.Line}
      %Equal.sym(Bool, String.ends_with(P, "\r"), False{}, ef) : {B.Text.line.if(_, P) == B.Line{P, "\n"} : B.Line}
      {==}

def line.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +h10: {C.AT(len, t, lf) == 10 : U32}, +c: Bool, +e: {U32.is_lt(s, lf) == c : Bool}) ->
  {B.Text.line(TXR(len, t, s, lf)) == LINE(len, t, s, lf, BEk(c, XC(len, t, c, lf), lf)) : B.Line}:
  match c:
    case True{}:
      +hn = Equal.trans(Bool, Nat.is_lt(n(s), n(lf)), U32.is_lt(s, lf), True{}, Equal.sym(Bool, U32.is_lt(s, lf), Nat.is_lt(n(s), n(lf)), U.is_lt_to_nat(s, lf)), e)
      line.c(len, t, d, hl, s, lf, hn, hlf, h10, U32.is_eq(C.AT(len, t, U1(lf)), 13), {==})
    case False{}:
      +hn = Equal.trans(Bool, Nat.is_lt(n(s), n(lf)), U32.is_lt(s, lf), False{}, Equal.sym(Bool, U32.is_lt(s, lf), Nat.is_lt(n(s), n(lf)), U.is_lt_to_nat(s, lf)), e)
      %Equal.sym(String, TXR(len, t, s, lf), "", WT.tx_nil(len, t, s, lf, hsl, N.not_lt_le(n(s), n(lf), hn))) : {B.Text.line(_) == B.Line{_, TXR(len, t, lf, (lf + 1 : U32))} : B.Line}
      %Equal.sym(String, TXR(len, t, lf, (lf + 1 : U32)), "\n", t_lf(len, t, d, hl, lf, hlf, h10)) : {B.Text.line("") == B.Line{"", _} : B.Line}
      {==}

# The line before its LF (at lf, below len): its body ends at BE, its
# terminator runs from BE through the LF.
law line_t:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +s: U32
  for +lf: U32
  for +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}
  for +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +h10: {C.AT(len, t, lf) == 10 : U32}
  {B.Text.line(TXR(len, t, s, lf)) == LINE(len, t, s, lf, BE(len, t, s, lf)) : B.Line}

def line_t(len, t, d, hl, s, lf, hsl, hlf, h10):
  line.k(len, t, d, hl, s, lf, hsl, hlf, h10, U32.is_lt(s, lf), {==})

# ---------------------------------------------------------------------------
# Ranges in bounds
# ---------------------------------------------------------------------------

def ule(+bb: U32, +a: U32, +z: U32, +hp: {W.PV(bb, NS.Rg{a, z}) == True{} : Bool}) -> {U32.is_le(a, z) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(a, z), Nat.is_le(n(a), n(z)), True{}, U.is_le_to_nat(a, z), W.pv_a(bb, a, z, hp))

# The range k of xs is in bounds (True past the end).
def PVAT(+bb: U32, xs: Rgs(), +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      match k:
        case 0n:
          W.PV(bb, x)
        case 1n+p:
          PVAT(bb, r, p)

law pv_at:
  for +bb: U32
  for +xs: Rgs()
  for +k: Nat
  for +h: {K.ALLPV(bb, xs) == True{} : Bool}
  {PVAT(bb, xs, k) == True{} : Bool}

def pv_at(bb, xs, k, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      match k:
        case 0n:
          N.and_true_l(W.PV(bb, x), K.ALLPV(bb, r), h)
        case 1n+p:
          pv_at(bb, r, p, N.and_true_r(W.PV(bb, x), K.ALLPV(bb, r), h))

# A range with a byte in it is not empty text.
def tx_ne(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +a: U32, +z: U32,
  +hzl: {Nat.is_le(n(z), n(len)) == True{} : Bool}, +hjz: {Nat.is_lt(n(a), n(z)) == True{} : Bool}) ->
  {String.is_empty(WT.TX(len, t, NS.Rg{a, z})) == False{} : Bool}:
  %Equal.sym(String, WT.TX(len, t, NS.Rg{a, z}), NR.chars(D.slice(RD.X(len, t), n(a), Nat.sub(n(z), n(a)))), RD.tx_eq(len, t, a, z, N.lt_to_le(n(a), n(z), hjz))) :
    {String.is_empty(_) == False{} : Bool}
  %Equal.sym(L32(), D.slice(RD.X(len, t), n(a), Nat.sub(n(z), n(a))), C.AT(len, t, a) <> D.slice(RD.X(len, t), n((a + 1 : U32)), Nat.sub(n(z), n((a + 1 : U32)))),
    RD.sl_cons(len, t, d, a, z, hl, hzl, hjz)) : {String.is_empty(NR.chars(_)) == False{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# B.Rec.parts of a line whose fields and ALTs are ranges
# ---------------------------------------------------------------------------

def FS7(+f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +rest: Rgs()) -> Rgs():
  Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, rest}}}}}}}

def PT(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +o0: Bool, +fs: Rgs(), +alts: Rgs()) -> B.Parts:
  B.Parts.of(B.Rec.pieces.go(K.TXS(len, t, alts), K.TXS(len, t, fs), defs, o0, List.length(&2, NS.Rg, alts), 1n))

law txs_len:
  for +len: U32
  for +t: AT.Tree<U32>
  for +xs: Rgs()
  {List.length(&2, String, K.TXS(len, t, xs)) == List.length(&2, NS.Rg, xs) : Nat}

def txs_len(len, t, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Nat, List.length(&2, String, K.TXS(len, t, r)), List.length(&2, NS.Rg, r), txs_len(len, t, r)) : {1n+_ == 1n+List.length(&2, NS.Rg, r) : Nat}
      {==}

# No ALT is empty.
law ne_any:
  for +xs: Rgs()
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hps: {K.ALLPV(len, xs) == True{} : Bool}
  for +hn: {NS.nonempty(xs) == True{} : Bool}
  {B.Text.any_empty(K.TXS(len, t, xs)) == False{} : Bool}

def ne_any(xs, len, t, d, hl, hps, hn):
  match xs:
    case Nil{}:
      {==}
    case Con{NS.Rg{+a, +z}, +r}:
      +hpa = N.and_true_l(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, r), hps)
      +hpr = N.and_true_r(W.PV(len, NS.Rg{a, z}), K.ALLPV(len, r), hps)
      +hna = N.and_true_l(U32.is_lt(a, z), NS.nonempty(r), hn)
      +hnr = N.and_true_r(U32.is_lt(a, z), NS.nonempty(r), hn)
      +hz = Equal.trans(Bool, Nat.is_lt(n(a), n(z)), U32.is_lt(a, z), True{}, Equal.sym(Bool, U32.is_lt(a, z), Nat.is_lt(n(a), n(z)), U.is_lt_to_nat(a, z)), hna)
      %Equal.sym(Bool, String.is_empty(WT.TX(len, t, NS.Rg{a, z})), False{}, tx_ne(len, t, d, hl, a, z, W.pv_z(len, a, z, hpa), hz)) :
        {Bool.or(_, B.Text.any_empty(K.TXS(len, t, r))) == False{} : Bool}
      ne_any(r, len, t, d, hl, hpr, hnr)

def lt8(+k: Nat) -> {Nat.is_lt(1n+1n+1n+1n+1n+1n+1n+1n+k, 8n) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

def or5(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +e: Bool,
  +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}, +hc: {c == False{} : Bool}, +hd: {d == False{} : Bool}, +he: {e == False{} : Bool}) ->
  {Bool.or(Bool.or(Bool.or(Bool.or(a, b), c), d), e) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(Bool.or(Bool.or(Bool.or(_, b), c), d), e) == False{} : Bool}
  %Equal.sym(Bool, b, False{}, hb) : {Bool.or(Bool.or(Bool.or(_, c), d), e) == False{} : Bool}
  %Equal.sym(Bool, c, False{}, hc) : {Bool.or(Bool.or(_, d), e) == False{} : Bool}
  %Equal.sym(Bool, d, False{}, hd) : {Bool.or(_, e) == False{} : Bool}
  he

# Not MALFORMED: eight fields or more, CHROM not empty, POS a number, REF
# letters, no ALT empty.
def mal_f(+len: U32, +t: AT.Tree<U32>, +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +x: NS.Rg, +r: Rgs(), +alts: Rgs(),
  +ha: {K.TXS(len, t, alts) == String.split(WT.TX(len, t, f4), ',') : Ss()},
  +h0: {String.is_empty(WT.TX(len, t, f0)) == False{} : Bool},
  +h1: {Maybe.is_none(&2, Nat, B.Pos.read(WT.TX(len, t, f1))) == False{} : Bool},
  +h3: {B.Text.is_letters(WT.TX(len, t, f3)) == True{} : Bool},
  +he: {B.Text.any_empty(K.TXS(len, t, alts)) == False{} : Bool}) ->
  {B.Rec.malformed(K.TXS(len, t, FS7(f0, f1, f2, f3, f4, f5, f6, Con{x, r}))) == False{} : Bool}:
  +h3n = {%Equal.sym(Bool, B.Text.is_letters(WT.TX(len, t, f3)), True{}, h3) : {Bool.not(_) == False{} : Bool}; {==} : {Bool.not(B.Text.is_letters(WT.TX(len, t, f3))) == False{} : Bool}}
  +he2 = {%ha : {B.Text.any_empty(_) == False{} : Bool}; he : {B.Text.any_empty(String.split(WT.TX(len, t, f4), ',')) == False{} : Bool}}
  or5(Nat.is_lt(List.length(&2, String, K.TXS(len, t, FS7(f0, f1, f2, f3, f4, f5, f6, Con{x, r}))), 8n), String.is_empty(WT.TX(len, t, f0)),
    Maybe.is_none(&2, Nat, B.Pos.read(WT.TX(len, t, f1))), Bool.not(B.Text.is_letters(WT.TX(len, t, f3))), B.Text.any_empty(String.split(WT.TX(len, t, f4), ',')),
    lt8(List.length(&2, String, K.TXS(len, t, r))), h0, h1, h3n, he2)

# A line that is not MALFORMED, with two or more ALTs, none equal up to case:
# one record per ALT (B.Rec.pieces).
def parts_eq(+len: U32, +t: AT.Tree<U32>, +defs: B.Defs, +os: Bool, +ow: Nat, +o0: Bool, +oa: Ss(), +body: String,
  +f0: NS.Rg, +f1: NS.Rg, +f2: NS.Rg, +f3: NS.Rg, +f4: NS.Rg, +f5: NS.Rg, +f6: NS.Rg, +x: NS.Rg, +r: Rgs(), +alts: Rgs(),
  +hf: {B.Rec.fields(body) == K.TXS(len, t, FS7(f0, f1, f2, f3, f4, f5, f6, Con{x, r})) : Ss()},
  +ha: {K.TXS(len, t, alts) == String.split(WT.TX(len, t, f4), ',') : Ss()},
  +h0: {String.is_empty(WT.TX(len, t, f0)) == False{} : Bool},
  +h1: {Maybe.is_none(&2, Nat, B.Pos.read(WT.TX(len, t, f1))) == False{} : Bool},
  +h3: {B.Text.is_letters(WT.TX(len, t, f3)) == True{} : Bool},
  +he: {B.Text.any_empty(K.TXS(len, t, alts)) == False{} : Bool},
  +h2: {Nat.is_le(2n, List.length(&2, NS.Rg, alts)) == True{} : Bool},
  +hd: {B.Alts.distinct(K.TXS(len, t, alts)) == True{} : Bool},
  +hcr: {B.Text.has_cr(body) == False{} : Bool}) ->
  {B.Rec.parts(defs, B.Opts{os, ow, True{}, o0, oa}, body) == PT(len, t, defs, o0, FS7(f0, f1, f2, f3, f4, f5, f6, Con{x, r}), alts) : B.Parts}:
  +FS = FS7(f0, f1, f2, f3, f4, f5, f6, Con{x, r})
  +TF = K.TXS(len, t, FS)
  +TA = K.TXS(len, t, alts)
  +P = PT(len, t, defs, o0, FS, alts)
  %Equal.sym(Bool, B.Text.has_cr(body), False{}, hcr) :
    {B.Rec.parts.if(Bool.and(Bool.not(B.Rec.malformed(B.Rec.fields(body))), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(body))))), _, defs, o0, B.Rec.fields(body)) == P : B.Parts}
  %Equal.sym(Ss(), B.Rec.fields(body), TF, hf) :
    {B.Rec.parts.if(Bool.and(Bool.not(B.Rec.malformed(_)), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(_)))), False{}, defs, o0, _) == P : B.Parts}
  %Equal.sym(Bool, B.Rec.malformed(TF), False{}, mal_f(len, t, f0, f1, f2, f3, f4, f5, f6, x, r, alts, ha, h0, h1, h3, he)) :
    {B.Rec.parts.if(Bool.and(Bool.not(_), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(TF)))), False{}, defs, o0, TF) == P : B.Parts}
  %ha : {B.Rec.parts.if(Nat.is_le(2n, List.length(&2, String, _)), False{}, defs, o0, TF) == P : B.Parts}
  %Equal.sym(Nat, List.length(&2, String, TA), List.length(&2, NS.Rg, alts), txs_len(len, t, alts)) : {B.Rec.parts.if(Nat.is_le(2n, _), False{}, defs, o0, TF) == P : B.Parts}
  %Equal.sym(Bool, Nat.is_le(2n, List.length(&2, NS.Rg, alts)), True{}, h2) : {B.Rec.parts.if(_, False{}, defs, o0, TF) == P : B.Parts}
  %ha : {B.Rec.parts.split(B.Alts.distinct(_), _, TF, defs, o0) == P : B.Parts}
  %Equal.sym(Bool, B.Alts.distinct(TA), True{}, hd) : {B.Rec.parts.split(_, TA, TF, defs, o0) == P : B.Parts}
  %Equal.sym(Nat, List.length(&2, String, TA), List.length(&2, NS.Rg, alts), txs_len(len, t, alts)) : {B.Parts.of(B.Rec.pieces.go(TA, TF, defs, o0, _, 1n)) == P : B.Parts}
  {==}
