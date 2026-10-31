import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./bytes_enc.bend as E
import ./LAWS.bend as L
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

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
    case S.StP{o, +md, src, pd, eof, back, wp, asked, fneed, +dfs}:
      S.md_ok(md)

def W1(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, pd, eof, back, wp, asked, fneed, +dfs}:
      S.srcs_ok(src)

def W2(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, +pd, eof, back, wp, asked, fneed, +dfs}:
      P.pd_ok(pd)

def W3(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, +pd, eof, back, wp, asked, fneed, +dfs}:
      P.nolf(P.pdtext(pd))

def W4(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, +pd, eof, back, wp, asked, fneed, +dfs}:
      S.src_empty(src) || String.is_empty(P.pdtext(pd))

def W5(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, +src, +pd, +eof, back, wp, asked, fneed, +dfs}:
      Bool.not(eof) || (String.is_empty(P.pdtext(pd)) && S.ends_lf(P.srcstext(src)))

def W6(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, md, src, pd, eof, back, +wp, asked, fneed, +dfs}:
      PC.wp_ok(fa, wp)

def W7(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, +md, src, pd, eof, back, +wp, asked, fneed, +dfs}:
      S.mb_win(md, wp)

# The options' arguments are bytes; record sources (-m) come first, while
# the run has counted their line.
def W8(+fa: List<&2, B.Contig>, +p: S.StP) -> Bool:
  match p:
    case S.StP{o, +md, +src, pd, eof, back, wp, asked, fneed, +dfs}:
      E.all_bytes(S.opts_args(o)) && S.recs_first(src) && S.recs_run(md, src)

# The options' arguments are bytes (the first part of the 9th test).
law W8_args:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +h: {W8(fa, p) == True{} : Bool}
  {E.all_bytes(S.opts_args(S.StP.o(p))) == True{} : Bool}

def W8_args(fa, p, h):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      and_l(E.all_bytes(S.opts_args(o)), S.recs_first(src), and_l(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(src)), S.recs_run(md, src), h))

law wf_c9:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {S.WF(fa, p) == C9(W0(fa, p), W1(fa, p), W2(fa, p), W3(fa, p), W4(fa, p), W5(fa, p), W6(fa, p), W7(fa, p), W8(fa, p)) : Bool}

def wf_c9(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
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

# The same, with the 9th test replaced too (it reads the run: recs_run).
law c9_m8:
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
  for +b8: Bool
  for +h: {C9(m, a1, a2, a3, a4, a5, a6, a7, a8) == True{} : Bool}
  for +hm: {m2 == True{} : Bool}
  for +h7: {b7 == True{} : Bool}
  for +h8: {b8 == True{} : Bool}
  {C9(m2, a1, a2, a3, a4, a5, a6, b7, b8) == True{} : Bool}

def c9_m8(m, m2, a1, a2, a3, a4, a5, a6, a7, b7, a8, b8, h, hm, h7, h8):
  c9_mk(m2, a1, a2, a3, a4, a5, a6, b7, b8, hm, c9_1(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_2(m, a1, a2, a3, a4, a5, a6, a7, a8, h),
    c9_3(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_4(m, a1, a2, a3, a4, a5, a6, a7, a8, h), c9_5(m, a1, a2, a3, a4, a5, a6, a7, a8, h),
    c9_6(m, a1, a2, a3, a4, a5, a6, a7, a8, h), h7, h8)

# Less of the input's own text left is less work left (S.less).
law less_lt:
  for +p2: S.StP
  for +p: S.StP
  for +h: {Nat.is_lt(S.measure(p2), S.measure(p)) == True{} : Bool}
  {S.less(p2, p) == True{} : Bool}

def less_lt(p2, p, h):
  %Equal.sym(Bool, Nat.is_lt(S.measure(p2), S.measure(p)), True{}, h) :
    {Bool.or(_, Bool.and(Nat.is_eq(S.measure(p2), S.measure(p)), Nat.is_lt(S.mrec(S.StP.src(p2)), S.mrec(S.StP.src(p))))) == True{} : Bool}
  {==}

# No record source among sps (-m): its text is all plain, and none waits.
law plain_nr:
  for +sps: List<&2, P.SrcP>
  for +h: {S.no_recs(sps) == True{} : Bool}
  {S.plain(sps) == sps : List<&2, P.SrcP>}

def plain_nr(sps, h):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      {==}
    case Con{P.SLP{+q}, +r}:
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      Empty.absurd({S.plain(Con{P.SPP{len, t, d, at}, r}) == Con{P.SPP{len, t, d, at}, r} : List<&2, P.SrcP>}, ft(h))
    case Con{P.SRP{+l}, +r}:
      Empty.absurd({S.plain(Con{P.SRP{l}, r}) == Con{P.SRP{l}, r} : List<&2, P.SrcP>}, ft(h))

law recs_nr:
  for +sps: List<&2, P.SrcP>
  for +h: {S.no_recs(sps) == True{} : Bool}
  {S.recs(sps) == Nil{} : List<&2, P.SrcP>}

def recs_nr(sps, h):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      {==}
    case Con{P.SLP{+q}, +r}:
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      Empty.absurd({S.recs(Con{P.SPP{len, t, d, at}, r}) == Nil{} : List<&2, P.SrcP>}, ft(h))
    case Con{P.SRP{+l}, +r}:
      Empty.absurd({S.recs(Con{P.SRP{l}, r}) == Nil{} : List<&2, P.SrcP>}, ft(h))

# After a plain byte source, no record source (the 9th test).
law W8_nr:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +rest: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +h: {W8(fa, S.StP{o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  {S.no_recs(rest) == True{} : Bool}

def W8_nr(fa, o, md, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, dfs, h):
  and_r(E.all_bytes(S.opts_args(o)), S.no_recs(rest), and_l(Bool.and(E.all_bytes(S.opts_args(o)), S.no_recs(rest)), S.recs_run(md, Con{P.SBP{len, t, d, at}, rest}), h))

law nr_first:
  for +sps: List<&2, P.SrcP>
  for +h: {S.no_recs(sps) == True{} : Bool}
  {S.recs_first(sps) == True{} : Bool}

def nr_first(sps, h):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      h
    case Con{P.SLP{+q}, +r}:
      h
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      Empty.absurd({S.recs_first(Con{P.SPP{len, t, d, at}, r}) == True{} : Bool}, ft(h))
    case Con{P.SRP{+l}, +r}:
      Empty.absurd({S.recs_first(Con{P.SRP{l}, r}) == True{} : Bool}, ft(h))

law recs_run_nr:
  for +md: S.MdP
  for +sps: List<&2, P.SrcP>
  for +h: {S.no_recs(sps) == True{} : Bool}
  {S.recs_run(md, sps) == True{} : Bool}

def recs_run_nr(md, sps, h):
  %Equal.sym(List<&2, P.SrcP>, S.recs(sps), Nil{}, recs_nr(sps, h)) :
    {Bool.or(List.is_empty(&2, P.SrcP, _), Bool.and(R.RunSt.inbody(S.smd(md)), Nat.is_le(1n, R.RunSt.n(S.smd(md))))) == True{} : Bool}
  {==}

# The 9th test after the first source (a plain byte source) is dropped, in
# any mode.
law W8_tl:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +md2: S.MdP
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +rest: List<&2, P.SrcP>
  for +pd: P.PdP
  for +pd2: P.PdP
  for +eof: Bool
  for +eof2: Bool
  for +back: Nat
  for +back2: Nat
  for +wp: PC.WP
  for +wp2: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +asked2: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  for +dfs: B.Defs
  for +dfs2: B.Defs
  for +h: {W8(fa, S.StP{o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  {W8(fa, S.StP{o, md2, rest, pd2, eof2, back2, wp2, asked2, fneed2, dfs2}) == True{} : Bool}

def W8_tl(fa, o, md, md2, len, t, d, at, rest, pd, pd2, eof, eof2, back, back2, wp, wp2, asked, asked2, fneed, fneed2, dfs, dfs2, h):
  +nr = W8_nr(fa, o, md, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, dfs, h)
  and_tt(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(rest)), S.recs_run(md2, rest),
    and_tt(E.all_bytes(S.opts_args(o)), S.recs_first(rest), W8_args(fa, S.StP{o, md, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed, dfs}, h), nr_first(rest, nr)),
    recs_run_nr(md2, rest, nr))

# A byte-mode state with the same run, definitions, text still to come and
# records waiting stands for the same report.
law rep_keep_mb:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +dfs: B.Defs
  for +q: S.StP
  for +p: S.StP
  for +eq: {S.StP.md(q) == S.MBP{rp} : S.MdP}
  for +ep: {S.StP.md(p) == S.MBP{rp} : S.MdP}
  for +eo: {S.StP.o(q) == S.StP.o(p) : B.Opts}
  for +ed: {S.StP.dfs(q) == S.StP.dfs(p) : B.Defs}
  for +eqi: {S.intext(q, cs) == S.intext(p, cs) : String}
  for +eqr: {S.recs(S.StP.src(q)) == S.recs(S.StP.src(p)) : List<&2, P.SrcP>}
  {S.report(fa, cs, O, N, q) == S.report(fa, cs, O, N, p) : R.Report}

def rep_keep_mb(fa, cs, O, N, o, rp, dfs, q, p, eq, ep, eo, ed, eqi, eqr):
  %Equal.sym(S.MdP, S.StP.md(q), S.MBP{rp}, eq) : {S.report.md(_, fa, cs, O, N, q) == S.report(fa, cs, O, N, p) : R.Report}
  %Equal.sym(S.MdP, S.StP.md(p), S.MBP{rp}, ep) : {S.report.md(S.MBP{rp}, fa, cs, O, N, q) == S.report.md(_, fa, cs, O, N, p) : R.Report}
  +Lq = B.Text.lines(S.intext(q, cs))
  %Equal.sym(String, S.intext(q, cs), S.intext(p, cs), eqi) :
    {R.finish(L.run.go(B.Text.lines(_), fa, L.defs.go(B.Text.lines(_), R.RunSt.inbody(S.smd(S.StP.md(q))), S.StP.dfs(q)), S.StP.o(q),
      S.RG(S.recs(S.StP.src(q)), fa, L.defs.go(B.Text.lines(_), R.RunSt.inbody(S.smd(S.StP.md(q))), S.StP.dfs(q)), S.StP.o(q), S.pre(O, N, S.smd(S.StP.md(q))))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  %Equal.sym(S.MdP, S.StP.md(q), S.MBP{rp}, eq) :
    {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(q)), S.StP.o(q),
      S.RG(S.recs(S.StP.src(q)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(q)), S.StP.o(q), S.pre(O, N, S.smd(_)))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  %Equal.sym(B.Opts, S.StP.o(q), S.StP.o(p), eo) :
    {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), S.StP.dfs(q)), _,
      S.RG(S.recs(S.StP.src(q)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), S.StP.dfs(q)), _, S.pre(O, N, P.specRun(rp)))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  %Equal.sym(B.Defs, S.StP.dfs(q), S.StP.dfs(p), ed) :
    {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), _), S.StP.o(p),
      S.RG(S.recs(S.StP.src(q)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), _), S.StP.o(p), S.pre(O, N, P.specRun(rp)))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  %Equal.sym(List<&2, P.SrcP>, S.recs(S.StP.src(q)), S.recs(S.StP.src(p)), eqr) :
    {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), S.StP.dfs(p)), S.StP.o(p),
      S.RG(_, fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(P.specRun(rp)), S.StP.dfs(p)), S.StP.o(p), S.pre(O, N, P.specRun(rp)))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  %ep :
    {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(p)), S.StP.o(p),
      S.RG(S.recs(S.StP.src(p)), fa, L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(p)), S.StP.o(p), S.pre(O, N, S.smd(_)))))
     == S.report.md(S.MBP{rp}, fa, cs, O, N, p) : R.Report}
  {==}

# S.Moved
# =======

# A step that keeps the run and the text still to come (up to eqi) moved
# no line.
# The definitions of the text still to come (S.DEFS) are the same for two
# states with the same text, mode and definitions read.
def defs_keep(+p: S.StP, +q: S.StP, +cs: List<&2, String>,
  +eqi: {S.intext(q, cs) == S.intext(p, cs) : String},
  +emd: {S.StP.md(q) == S.StP.md(p) : S.MdP},
  +edf: {S.StP.dfs(q) == S.StP.dfs(p) : B.Defs}) ->
  {S.DEFS(q, cs) == S.DEFS(p, cs) : B.Defs}:
  %Equal.sym(String, S.intext(q, cs), S.intext(p, cs), eqi) : {L.defs.go(B.Text.lines(_), R.RunSt.inbody(S.smd(S.StP.md(q))), S.StP.dfs(q)) == S.DEFS(p, cs) : B.Defs}
  %Equal.sym(S.MdP, S.StP.md(q), S.StP.md(p), emd) : {L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(q)) == S.DEFS(p, cs) : B.Defs}
  %Equal.sym(B.Defs, S.StP.dfs(q), S.StP.dfs(p), edf) : {L.defs.go(B.Text.lines(S.intext(p, cs)), R.RunSt.inbody(S.smd(S.StP.md(p))), _) == S.DEFS(p, cs) : B.Defs}
  {==}

def moved_keep(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +rp: P.RunP, +p: S.StP, +q: S.StP,
  +eqi: {S.intext(q, cs) == S.intext(p, cs) : String},
  +eqr: {S.recs(S.StP.src(q)) == S.recs(S.StP.src(p)) : List<&2, P.SrcP>},
  +emd: {S.StP.md(q) == S.StP.md(p) : S.MdP},
  +edf: {S.StP.dfs(q) == S.StP.dfs(p) : B.Defs}) ->
  S.Moved.md(S.MBP{rp}, S.MBP{rp}, fa, cs, p, q):
  +D = S.DEFS(p, cs)
  (Nil{}, (Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), S.intext(p, cs), S.intext(q, cs), Equal.sym(String, S.intext(q, cs), S.intext(p, cs), eqi)),
    ({%Equal.sym(List<&2, P.SrcP>, S.recs(S.StP.src(q)), S.recs(S.StP.src(p)), eqr) : {P.settle(S.RG(_, fa, D, S.StP.o(p), P.specRun(rp))) == P.settle(S.RG(S.recs(S.StP.src(p)), fa, D, S.StP.o(p), P.specRun(rp))) : R.RunSt}
    {==} : {P.settle(S.RG(S.recs(S.StP.src(q)), fa, D, S.StP.o(p), P.specRun(rp))) == P.settle(S.RG(S.recs(S.StP.src(p)), fa, D, S.StP.o(p), P.specRun(rp))) : R.RunSt}},
    defs_keep(p, q, cs, eqi, emd, edf))))

# A step from the String mode claims only that the definitions are kept.
def moved_ms(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +s: R.RunSt, +qs: List<&2, String>, +ql: Nat, +code: Maybe<&2, Nat>, m2: S.MdP, +p: S.StP, +q: S.StP,
  +hd: {S.DEFS(q, cs) == S.DEFS(p, cs) : B.Defs}) ->
  S.Moved.md(S.MSP{s, qs, ql, code}, m2, fa, cs, p, q):
  match m2:
    case S.MBP{rp}:
      hd
    case S.MSP{s2, qs2, ql2, code2}:
      hd

# S.Kept
# ======

# A step that keeps the sources as they are keeps the first one's buffer.
def kept_same(+src: List<&2, P.SrcP>) -> S.Kept.s(src, src):
  match src:
    case Nil{}:
      Unit{}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      h => (at, {==})
    case Con{P.SLP{+q}, +rest}:
      Unit{}
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      {==}
    case Con{P.SRP{+l}, +rest}:
      {==}

# The same for a state p whose sources are those of q (in either mode).
def kept_md(+m: S.MdP, +src: List<&2, P.SrcP>) -> S.Kept.md(m, src, src):
  match m:
    case S.MBP{+rp}:
      kept_same(src)
    case S.MSP{+s, +qs, +ql, +code}:
      Unit{}
