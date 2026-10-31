import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./proof_s_line.bend as SL
import ./proof_s_drv.bend as DR
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# The line's terminator, as the byte splitter's check sees it (proof_s_drv's
# CRT: its range is two bytes long): CR LF exactly when the check says so,
# else LF. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# (a + 1) - (a - 1) is 2 when a >= 1.
def two(+a: Nat, +h1: {Nat.is_le(1n, a) == True{} : Bool}) -> {Nat.sub(Nat.add(a, 1n), Nat.sub(a, 1n)) == 2n : Nat}:
  match a:
    case 0n:
      Empty.absurd({Nat.sub(Nat.add(0n, 1n), Nat.sub(0n, 1n)) == 2n : Nat}, N.false_ne_true(h1))
    case 1n+b:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, N.sub_zero(b)) : {Nat.sub(1n+Nat.add(b, 1n), _) == 2n : Nat}
      %N.add_succ(b, 1n) : {Nat.sub(_, b) == 2n : Nat}
      N.sub_add_l(b, 2n)

def sub1_le(+a: Nat, +h1: {Nat.is_le(1n, a) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, 1n), a) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.sub(0n, 1n), 0n) == True{} : Bool}, N.false_ne_true(h1))
    case 1n+b:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, N.sub_zero(b)) : {Nat.is_le(_, 1n+b) == True{} : Bool}
      N.lt_to_le(b, 1n+b, Equal.trans(Bool, Nat.is_lt(b, 1n+b), Nat.is_le(b, b), True{}, N.lt_succ_iff(b, b), N.le_refl(b)))

# The range lf .. lf+1 is one byte long.
def crt_lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +lf: U32,
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) -> {DR.CRT(NS.Rg{lf, (lf + 1 : U32)}) == False{} : Bool}:
  +e1 = LP.inc_len(len, t, d, lf, hl, hlf)
  +hle = {%Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), e1) : {Nat.is_le(n(lf), _) == True{} : Bool}; N.le_add_r(n(lf), 1n) : {Nat.is_le(n(lf), n((lf + 1 : U32))) == True{} : Bool}}
  %Equal.sym(Bool, U32.is_eq(((lf + 1 : U32) - lf : U32), 2), Nat.is_eq(n(((lf + 1 : U32) - lf : U32)), n(2)), U.is_eq_to_nat(((lf + 1 : U32) - lf : U32), 2)) : {_ == False{} : Bool}
  %Equal.sym(Nat, n(((lf + 1 : U32) - lf : U32)), Nat.sub(n((lf + 1 : U32)), n(lf)), LP.sub_u((lf + 1 : U32), lf, hle)) : {Nat.is_eq(_, 2n) == False{} : Bool}
  %Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), e1) : {Nat.is_eq(Nat.sub(_, n(lf)), 2n) == False{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(n(lf), 1n), n(lf)), 1n, N.sub_add_l(n(lf), 1n)) : {Nat.is_eq(_, 2n) == False{} : Bool}
  {==}

# The range lf-1 .. lf+1 is two bytes long.
def crt_crlf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +lf: U32,
  +h1: {Nat.is_le(1n, n(lf)) == True{} : Bool},
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) -> {DR.CRT(NS.Rg{(lf - 1 : U32), (lf + 1 : U32)}) == True{} : Bool}:
  +e1 = LP.inc_len(len, t, d, lf, hl, hlf)
  +em = LP.sub_u(lf, 1, h1)
  +hle = {%Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), e1) : {Nat.is_le(n((lf - 1 : U32)), _) == True{} : Bool};
    %Equal.sym(Nat, n((lf - 1 : U32)), Nat.sub(n(lf), 1n), em) : {Nat.is_le(_, Nat.add(n(lf), 1n)) == True{} : Bool};
    N.le_trans(Nat.sub(n(lf), 1n), n(lf), Nat.add(n(lf), 1n), sub1_le(n(lf), h1), N.le_add_r(n(lf), 1n)) : {Nat.is_le(n((lf - 1 : U32)), n((lf + 1 : U32))) == True{} : Bool}}
  %Equal.sym(Bool, U32.is_eq(((lf + 1 : U32) - (lf - 1 : U32) : U32), 2), Nat.is_eq(n(((lf + 1 : U32) - (lf - 1 : U32) : U32)), n(2)), U.is_eq_to_nat(((lf + 1 : U32) - (lf - 1 : U32) : U32), 2)) : {_ == True{} : Bool}
  %Equal.sym(Nat, n(((lf + 1 : U32) - (lf - 1 : U32) : U32)), Nat.sub(n((lf + 1 : U32)), n((lf - 1 : U32))), LP.sub_u((lf + 1 : U32), (lf - 1 : U32), hle)) : {Nat.is_eq(_, 2n) == True{} : Bool}
  %Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), e1) : {Nat.is_eq(Nat.sub(_, n((lf - 1 : U32))), 2n) == True{} : Bool}
  %Equal.sym(Nat, n((lf - 1 : U32)), Nat.sub(n(lf), 1n), em) : {Nat.is_eq(Nat.sub(Nat.add(n(lf), 1n), _), 2n) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(n(lf), 1n), Nat.sub(n(lf), 1n)), 2n, two(n(lf), h1)) : {Nat.is_eq(_, 2n) == True{} : Bool}
  {==}

def T1(+len: U32, +t: AT.Tree<U32>, +be: U32, +lf: U32) -> Type:
  {SL.TXR(len, t, be, (lf + 1 : U32)) == Bool.pick(String, DR.CRT(NS.Rg{be, (lf + 1 : U32)}), "\r\n", "\n") : String}

def tc.lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +lf: U32,
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, +h10: {C.AT(len, t, lf) == 10 : U32}) -> T1(len, t, lf, lf):
  %Equal.sym(Bool, DR.CRT(NS.Rg{lf, (lf + 1 : U32)}), False{}, crt_lf(len, t, d, hl, lf, hlf)) :
    {SL.TXR(len, t, lf, (lf + 1 : U32)) == Bool.pick(String, _, "\r\n", "\n") : String}
  SL.t_lf(len, t, d, hl, lf, hlf, h10)

def tc.c(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hsl: {Nat.is_lt(n(s), n(lf)) == True{} : Bool}, +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, +h10: {C.AT(len, t, lf) == 10 : U32},
  +c2: Bool, +e2: {U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13) == c2 : Bool}) ->
  T1(len, t, Bool.pick(U32, c2, (lf - 1 : U32), lf), lf):
  match c2:
    case False{}:
      tc.lf(len, t, d, hl, lf, hlf, h10)
    case True{}:
      %Equal.sym(Bool, DR.CRT(NS.Rg{(lf - 1 : U32), (lf + 1 : U32)}), True{}, crt_crlf(len, t, d, hl, lf, SL.one_le(s, lf, hsl), hlf)) :
        {SL.TXR(len, t, (lf - 1 : U32), (lf + 1 : U32)) == Bool.pick(String, _, "\r\n", "\n") : String}
      SL.t_crlf(len, t, d, hl, s, lf, hsl, hlf, h10, U.is_eq_true(C.AT(len, t, (lf - 1 : U32)), 13, e2))

def tc.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}, +s: U32, +lf: U32,
  +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}, +h10: {C.AT(len, t, lf) == 10 : U32},
  +c: Bool, +e: {U32.is_lt(s, lf) == c : Bool}) ->
  T1(len, t, SL.BEk(c, SL.XC(len, t, c, lf), lf), lf):
  match c:
    case False{}:
      tc.lf(len, t, d, hl, lf, hlf, h10)
    case True{}:
      tc.c(len, t, d, hl, s, lf, Equal.trans(Bool, Nat.is_lt(n(s), n(lf)), U32.is_lt(s, lf), True{}, Equal.sym(Bool, U32.is_lt(s, lf), Nat.is_lt(n(s), n(lf)), U.is_lt_to_nat(s, lf)), e),
        hlf, h10, U32.is_eq(C.AT(len, t, (lf - 1 : U32)), 13), {==})

# The line before the LF at lf: its terminator is CR LF exactly when the
# check's range says two bytes.
law term_cr:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hl: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +s: U32
  for +lf: U32
  for +hsl: {Nat.is_le(n(s), n(lf)) == True{} : Bool}
  for +hlf: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}
  for +h10: {C.AT(len, t, lf) == 10 : U32}
  {B.Line.term(B.Text.line(SL.TXR(len, t, s, lf))) == Bool.pick(String, DR.CRT(DR.TE(len, t, s, lf)), "\r\n", "\n") : String}

def term_cr(len, t, d, hl, s, lf, hsl, hlf, h10):
  %Equal.sym(B.Line, B.Text.line(SL.TXR(len, t, s, lf)), SL.LINE(len, t, s, lf, SL.BE(len, t, s, lf)), SL.line_t(len, t, d, hl, s, lf, hsl, hlf, h10)) :
    {B.Line.term(_) == Bool.pick(String, DR.CRT(DR.TE(len, t, s, lf)), "\r\n", "\n") : String}
  tc.k(len, t, d, hl, s, lf, hlf, h10, U32.is_lt(s, lf), {==})
