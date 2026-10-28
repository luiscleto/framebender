import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./bytes_enc.bend as E

# Tools for adv_ok (proof_b_adv.bend): a good state (S.WF) taken apart and
# put together. WF is a chain of 9 tests joined by && (left to right).
# Every variable is reusable.

def C9(+m: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool) -> Bool:
  Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8)

def bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law ft:
  for e: {False{} == True{} : Bool}
  Empty

def ft(e):
  %e : bdisc(_)
  Unit{}

law and_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft(e))

law and_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ft(e))

law and_tt:
  for +a: Bool
  for +b: Bool
  for +ea: {a == True{} : Bool}
  for +eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_tt(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

law or_l:
  for +a: Bool
  for +b: Bool
  for +e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_l(a, b, e):
  %Equal.sym(Bool, a, True{}, e) : {Bool.or(_, b) == True{} : Bool}
  {==}

law or_r:
  for +a: Bool
  for +b: Bool
  for +e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_r(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law not_f:
  for +a: Bool
  for +e: {a == False{} : Bool}
  {Bool.not(a) == True{} : Bool}

def not_f(a, e):
  %Equal.sym(Bool, a, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

law lt_add1:
  for +x: Nat
  {Nat.is_lt(x, Nat.add(x, 1n)) == True{} : Bool}

def lt_add1(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      lt_add1(p)

# Each other test of a chain that holds.
# The 9 tests of a good state.
def W0(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, +md, src, pd, eof, back, wp, asked, fneed}:
      S.md_ok(md)

def W1(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, pd, eof, back, wp, asked, fneed}:
      S.srcs_ok(src)

def W2(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, +pd, eof, back, wp, asked, fneed}:
      P.pd_ok(pd)

def W3(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, +pd, eof, back, wp, asked, fneed}:
      P.nolf(P.pdtext(pd))

def W4(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, +pd, eof, back, wp, asked, fneed}:
      S.src_empty(src) || String.is_empty(P.pdtext(pd))

def W5(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, +pd, +eof, back, wp, asked, fneed}:
      Bool.not(eof) || (String.is_empty(P.pdtext(pd)) && S.ends_lf(P.srcstext(src)))

def W6(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, pd, eof, back, +wp, asked, fneed}:
      PC.wp_ok(fa, wp)

def W7(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, +md, src, pd, eof, back, +wp, asked, fneed}:
      S.mb_win(md, wp)

def W8(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, pd, eof, back, wp, asked, fneed}:
      E.all_bytes(S.opts_args(o))

law wf_c9:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {S.WF(fa, p) == C9(W0(fa, p), W1(fa, p), W2(fa, p), W3(fa, p), W4(fa, p), W5(fa, p), W6(fa, p), W7(fa, p), W8(fa, p)) : Bool}

def wf_c9(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

# Each test of a chain that holds.
law c9_0:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {m == True{} : Bool}

def c9_0(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  match m:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft(h))

law c9_1:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a1 == True{} : Bool}

def c9_1(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(m, a1, and_l(Bool.and(m, a1), a2, and_l(Bool.and(Bool.and(m, a1), a2), a3, and_l(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4, and_l(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h))))))))

law c9_2:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a2 == True{} : Bool}

def c9_2(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(m, a1), a2, and_l(Bool.and(Bool.and(m, a1), a2), a3, and_l(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4, and_l(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h)))))))

law c9_3:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a3 == True{} : Bool}

def c9_3(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(m, a1), a2), a3, and_l(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4, and_l(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h))))))

law c9_4:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a4 == True{} : Bool}

def c9_4(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4, and_l(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h)))))

law c9_5:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a5 == True{} : Bool}

def c9_5(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h))))

law c9_6:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a6 == True{} : Bool}

def c9_6(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h)))

law c9_7:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a7 == True{} : Bool}

def c9_7(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7, and_l(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h))

law c9_8:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  {a8 == True{} : Bool}

def c9_8(m, a1, a2, a3, a4, a5, a6, a7, a8, h):
  and_r(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(m, a1), a2), a3), a4), a5), a6), a7), a8, h)

law c9_mk:
  for +m: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +a8: Bool
  for +h0: {m == True{} : Bool}
  for +h1: {a1 == True{} : Bool}
  for +h2: {a2 == True{} : Bool}
  for +h3: {a3 == True{} : Bool}
  for +h4: {a4 == True{} : Bool}
  for +h5: {a5 == True{} : Bool}
  for +h6: {a6 == True{} : Bool}
  for +h7: {a7 == True{} : Bool}
  for +h8: {a8 == True{} : Bool}
  {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}

def c9_mk(m, a1, a2, a3, a4, a5, a6, a7, a8, h0, h1, h2, h3, h4, h5, h6, h7, h8):
  %Equal.sym(Bool, m, True{}, h0) : {C9(_, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a1, True{}, h1) : {C9(True{}, _, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a2, True{}, h2) : {C9(True{}, True{}, _, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a3, True{}, h3) : {C9(True{}, True{}, True{}, _, a4, a5, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a4, True{}, h4) : {C9(True{}, True{}, True{}, True{}, _, a5, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a5, True{}, h5) : {C9(True{}, True{}, True{}, True{}, True{}, _, a6, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a6, True{}, h6) : {C9(True{}, True{}, True{}, True{}, True{}, True{}, _, a7, a8) == True{} : Bool}
  %Equal.sym(Bool, a7, True{}, h7) : {C9(True{}, True{}, True{}, True{}, True{}, True{}, True{}, _, a8) == True{} : Bool}
  %Equal.sym(Bool, a8, True{}, h8) : {C9(True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, _) == True{} : Bool}
  {==}

# The first and the 8th test (both about the run's mode) replaced by others
# that hold.
law c9_m:
  for +m: Bool
  for +m2: Bool
  for +a1: Bool
  for +a2: Bool
  for +a3: Bool
  for +a4: Bool
  for +a5: Bool
  for +a6: Bool
  for +a7: Bool
  for +b7: Bool
  for +a8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  for +hm: {m2 == True{} : Bool}
  for +h7: {b7 == True{} : Bool}
  {C9(m2, a1, a2, a3, a4, a5, a6, b7, a8) == True{} : Bool}

def c9_m(m, m2, a1, a2, a3, a4, a5, a6, a7, b7, a8, h, hm, h7):
  c9_mk(m2, a1, a2, a3, a4, a5, a6, b7, a8, hm, c9_1(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_2(m, a1, a2, a3, a4, a5, a6, a7, a8, h),
    c9_3(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_4(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_5(m, a1, a2, a3, a4, a5, a6, a7, a8, h),
    c9_6(m, a1, a2, a3, a4, a5, a6, a7, a8, h), h7, c9_8(m, a1, a2, a3, a4, a5, a6, a7, a8, h))
