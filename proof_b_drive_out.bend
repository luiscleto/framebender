import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_run.bend as PR
import ./proof_b_frame_fr.bend as FR
import ./proof_b_enc.bend as ENC
import ./proof_b_lit.bend as LIT
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-words/proof_nat.bend as N

# Helpers for proof_b_drive.bend: the end of a step (Norm.out) hands out
# what the run wrote and said, keeping a good state that stands for the
# same report with the handed-out text and messages moved to the driver's
# side (O, N).

# S.WF
# ====

# S.WF of a state, as the chain of its nine tests (&& is left-nested):
# md_ok, srcs_ok, pd_ok, nolf, src/pd, eof, wp_ok, mb_win, the arguments.
def X8(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool) -> Bool:
  a && b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8

def Y1(+a: Bool, +b1: Bool) -> Bool:
  a && b1

def Y2(+a: Bool, +b1: Bool, +b2: Bool) -> Bool:
  a && b1 && b2

def Y3(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool) -> Bool:
  a && b1 && b2 && b3

def Y4(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool) -> Bool:
  a && b1 && b2 && b3 && b4

def Y5(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool) -> Bool:
  a && b1 && b2 && b3 && b4 && b5

def Y6(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool) -> Bool:
  a && b1 && b2 && b3 && b4 && b5 && b6

def Y7(+a: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool) -> Bool:
  a && b1 && b2 && b3 && b4 && b5 && b6 && b7

law x8_a:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {a == True{} : Bool}

def x8_a(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  +h4 = PB.and_true_l(Y4(a, b1, b2, b3, b4), b5, h5)
  +h3 = PB.and_true_l(Y3(a, b1, b2, b3), b4, h4)
  +h2 = PB.and_true_l(Y2(a, b1, b2), b3, h3)
  +h1 = PB.and_true_l(Y1(a, b1), b2, h2)
  +h0 = PB.and_true_l(a, b1, h1)
  h0

law x9_1:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b1 == True{} : Bool}

def x9_1(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  +h4 = PB.and_true_l(Y4(a, b1, b2, b3, b4), b5, h5)
  +h3 = PB.and_true_l(Y3(a, b1, b2, b3), b4, h4)
  +h2 = PB.and_true_l(Y2(a, b1, b2), b3, h3)
  +h1 = PB.and_true_l(Y1(a, b1), b2, h2)
  PB.and_true_r(a, b1, h1)

law x9_2:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b2 == True{} : Bool}

def x9_2(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  +h4 = PB.and_true_l(Y4(a, b1, b2, b3, b4), b5, h5)
  +h3 = PB.and_true_l(Y3(a, b1, b2, b3), b4, h4)
  +h2 = PB.and_true_l(Y2(a, b1, b2), b3, h3)
  PB.and_true_r(Y1(a, b1), b2, h2)

law x9_3:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b3 == True{} : Bool}

def x9_3(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  +h4 = PB.and_true_l(Y4(a, b1, b2, b3, b4), b5, h5)
  +h3 = PB.and_true_l(Y3(a, b1, b2, b3), b4, h4)
  PB.and_true_r(Y2(a, b1, b2), b3, h3)

law x9_4:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b4 == True{} : Bool}

def x9_4(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  +h4 = PB.and_true_l(Y4(a, b1, b2, b3, b4), b5, h5)
  PB.and_true_r(Y3(a, b1, b2, b3), b4, h4)

law x9_5:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b5 == True{} : Bool}

def x9_5(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  +h5 = PB.and_true_l(Y5(a, b1, b2, b3, b4, b5), b6, h6)
  PB.and_true_r(Y4(a, b1, b2, b3, b4), b5, h5)

law x9_6:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b6 == True{} : Bool}

def x9_6(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  +h6 = PB.and_true_l(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)
  PB.and_true_r(Y5(a, b1, b2, b3, b4, b5), b6, h6)

law x9_7:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b7 == True{} : Bool}

def x9_7(a, b1, b2, b3, b4, b5, b6, b7, b8, h):
  +h7 = PB.and_true_l(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)
  PB.and_true_r(Y6(a, b1, b2, b3, b4, b5, b6), b7, h7)

law x9_8:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h: {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  {b8 == True{} : Bool}

def x9_8(a, b1, b2, b3, b4, b5, b6, b7, b8, h):

  PB.and_true_r(Y7(a, b1, b2, b3, b4, b5, b6, b7), b8, h)

law x9_mk:
  for +a: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +ha: {a == True{} : Bool}
  for +hb1: {b1 == True{} : Bool}
  for +hb2: {b2 == True{} : Bool}
  for +hb3: {b3 == True{} : Bool}
  for +hb4: {b4 == True{} : Bool}
  for +hb5: {b5 == True{} : Bool}
  for +hb6: {b6 == True{} : Bool}
  for +hb7: {b7 == True{} : Bool}
  for +hb8: {b8 == True{} : Bool}
  {X8(a, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}

def x9_mk(a, b1, b2, b3, b4, b5, b6, b7, b8, ha, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8):
  %Equal.sym(Bool, a, True{}, ha) : {X8(_, b1, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b1, True{}, hb1) : {X8(True{}, _, b2, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b2, True{}, hb2) : {X8(True{}, True{}, _, b3, b4, b5, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b3, True{}, hb3) : {X8(True{}, True{}, True{}, _, b4, b5, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b4, True{}, hb4) : {X8(True{}, True{}, True{}, True{}, _, b5, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b5, True{}, hb5) : {X8(True{}, True{}, True{}, True{}, True{}, _, b6, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b6, True{}, hb6) : {X8(True{}, True{}, True{}, True{}, True{}, True{}, _, b7, b8) == True{} : Bool}
  %Equal.sym(Bool, b7, True{}, hb7) : {X8(True{}, True{}, True{}, True{}, True{}, True{}, True{}, _, b8) == True{} : Bool}
  %Equal.sym(Bool, b8, True{}, hb8) : {X8(True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, _) == True{} : Bool}
  {==}

# A good state's run is good.
law wf_md:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  {S.md_ok(S.StP.md(p)) == True{} : Bool}

def wf_md(fa, p, hw):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      x8_a(S.md_ok(md), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)),
        S.src_empty(src) || String.is_empty(P.pdtext(pd)),
        Bool.not(eof) || (String.is_empty(P.pdtext(pd)) && S.ends_lf(P.srcstext(src))),
        PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)

# A good state with a good run put in its place is good (mb_win holds for it).
law wf_set_md:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +md2: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hm: {S.md_ok(md2) == True{} : Bool}
  for +hmw: {S.mb_win(md2, wp) == True{} : Bool}
  {S.WF(fa, S.StP{o, md2, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}

def wf_set_md(fa, o, md, md2, src, pd, eof, back, wp, asked, fneed, hw, hm, hmw):
  +b1 = S.srcs_ok(src)
  +b2 = P.pd_ok(pd)
  +b3 = P.nolf(P.pdtext(pd))
  +b4 = Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd)))
  +b5 = Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src))))
  +b6 = PC.wp_ok(fa, wp)
  +b8 = E.all_bytes(S.opts_args(o))
  +a = S.md_ok(md)
  +b7 = S.mb_win(md, wp)
  x9_mk(S.md_ok(md2), b1, b2, b3, b4, b5, b6, S.mb_win(md2, wp), b8, hm,
    x9_1(a, b1, b2, b3, b4, b5, b6, b7, b8, hw), x9_2(a, b1, b2, b3, b4, b5, b6, b7, b8, hw), x9_3(a, b1, b2, b3, b4, b5, b6, b7, b8, hw),
    x9_4(a, b1, b2, b3, b4, b5, b6, b7, b8, hw), x9_5(a, b1, b2, b3, b4, b5, b6, b7, b8, hw), x9_6(a, b1, b2, b3, b4, b5, b6, b7, b8, hw),
    hmw, x9_8(a, b1, b2, b3, b4, b5, b6, b7, b8, hw))

# The byte mode's mb_win reads only the window.
law wf_mbw:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  {S.mb_win.k(wp) == True{} : Bool}

def wf_mbw(fa, o, rp, src, pd, eof, back, wp, asked, fneed, hw):
  x9_7(PR.RunInv(rp), S.srcs_ok(src), P.pd_ok(pd), P.nolf(P.pdtext(pd)),
    Bool.or(S.src_empty(src), String.is_empty(P.pdtext(pd))),
    Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(src)))),
    PC.wp_ok(fa, wp), S.mb_win.k(wp), E.all_bytes(S.opts_args(o)), hw)

# Text
# ====

law chars_nr:
  for +xs: List<&2, U32>
  {E.chars(xs) == NR.chars(xs) : String}

def chars_nr(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      %chars_nr(t) : {SCon{Chr{x}, E.chars(t)} == SCon{Chr{x}, _} : String}
      {==}

# What was handed out moves in front: the state's report is the same.
law pre_clear:
  for +O: String
  for +N: List<&2, B.Note>
  for +st: R.RunSt
  {S.pre(String.append(O, P.RunSt.out(st)), List.append(&2, B.Note, N, P.RunSt.notes(st)), P.clear(st)) == S.pre(O, N, st) : R.RunSt}

def pre_clear(O, N, st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      %Equal.sym(String, String.append(String.append(O, o), ""), String.append(O, o), PN.str_nil(String.append(O, o))) :
        {R.RunSt{n, i, h, c, e, l, b, k, _, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), x} == R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x} : R.RunSt}
      %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), List.append(&2, B.Note, N, ns), PB.append_nil(B.Note, List.append(&2, B.Note, N, ns))) :
        {R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), _, x} == R.RunSt{n, i, h, c, e, l, b, k, String.append(O, o), List.append(&2, B.Note, N, ns), x} : R.RunSt}
      {==}

# The bytes left in the sources
# =============================

def lsum(+sps: List<&2, P.SrcP>) -> U32:
  match sps:
    case Nil{}:
      0
    case Con{P.SBP{+len, t, d, +at}, +rest}:
      ((len - at : U32) + lsum(rest) : U32)
    case Con{P.SLP{p}, +rest}:
      (0 + lsum(rest) : U32)

law left_eq:
  for +sps: List<&2, P.SrcP>
  {Norm.left(P.mkSrcs(sps)) == (P.mkSrcs(sps), lsum(sps)) : List<&1, Norm.Src> & U32}

def left_eq(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), lsum(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SB{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SBP{len, t, d, at}) <> P.mkSrcs(rest), ((len - at : U32) + lsum(rest) : U32)) : List<&1, Norm.Src> & U32}
      {==}
    case Con{P.SLP{+q}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), lsum(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SL{q}, 0), _) == (Norm.SL{q} <> P.mkSrcs(rest), (0 + lsum(rest) : U32)) : List<&1, Norm.Src> & U32}
      {==}

# The end of a step
# =================

# The spec's run over the lines still to come from p (S.report's run).
def L2(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, st: R.RunSt) -> R.RunSt:
  L.run.go(B.Text.lines(S.intext(p, cs)), fa, S.StP.o(p), st)

# The byte run has not stopped (the String mode: always).
def live(m: S.MdP) -> Bool:
  match m:
    case S.MBP{rp}:
      Bool.not(P.RunP.x(rp))
    case S.MSP{s, qs, ql, c}:
      True{}

law not_true:
  for +x: Bool
  for +h: {Bool.not(x) == True{} : Bool}
  {x == False{} : Bool}

def not_true(x, h):
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(h))
    case False{}:
      {==}

law live_of:
  for +md: S.MdP
  for +h: {S.stopped(md) == False{} : Bool}
  {live(md) == True{} : Bool}

def live_of(md, h):
  match md:
    case S.MBP{+rp}:
      %Equal.sym(Bool, P.RunP.x(rp), False{}, h) : {Bool.not(_) == True{} : Bool}
      {==}
    case S.MSP{+s, +qs, +ql, +c}:
      {==}

# The run's mode: bytes (True) or String.
def mode(m: S.MdP) -> Bool:
  match m:
    case S.MBP{rp}:
      True{}
    case S.MSP{s, qs, ql, c}:
      False{}

# mb_reqs reads only the mode.
law mbr_mode:
  for +md1: S.MdP
  for +md2: S.MdP
  for +r: List<&2, Pr.Req>
  for +h: {mode(md1) == mode(md2) : Bool}
  for +h2: {S.mb_reqs(md2, r) == True{} : Bool}
  {S.mb_reqs(md1, r) == True{} : Bool}

def mbr_mode(md1, md2, r, h, h2):
  match md1 md2:
    case S.MBP{+a} S.MBP{+b}:
      h2
    case S.MSP{+s, +qs, +ql, +c} _:
      {==}
    case S.MBP{+a} S.MSP{+s, +qs, +ql, +c}:
      Empty.absurd({S.mb_reqs(S.MBP{a}, r) == True{} : Bool}, PB.true_ne_false(h))

# What a step's end leads to, for a good state p: the step's buffer reads as
# text t; the new state p2 is good, stands for the same report with t and
# the step's messages moved to the driver's side, and keeps the input, what
# was asked, and whether the run is in the body; next is nx.
def OutG(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +nx: Pr.Next, s: Norm.Step) -> Type:
  match s:
    case Norm.Step{st, b, ns, nx2}:
      &t: String -> &p2: S.StP -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({st == S.mkSt(fa, p2) : Norm.St}
        & ({S.WF(fa, p2) == True{} : Bool}
        & ({S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == S.report(fa, cs, O, N, p) : R.Report}
        & ({nx2 == nx : Pr.Next}
        & ({S.StP.src(p2) == S.StP.src(p) : List<&2, P.SrcP>}
        & ({S.StP.eof(p2) == S.StP.eof(p) : Bool}
        & ({S.StP.asked(p2) == S.StP.asked(p) : Maybe<&2, List<&2, Pr.Req>>}
        & ({mode(S.StP.md(p2)) == mode(S.StP.md(p)) : Bool}
        & {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool})))))))))

law clear_inbody:
  for +st: R.RunSt
  {R.RunSt.inbody(P.clear(st)) == R.RunSt.inbody(st) : Bool}

def clear_inbody(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law ib_spec:
  for +rp: P.RunP
  {R.RunSt.inbody(P.specRun(rp)) == P.RunP.i(rp) : Bool}

def ib_spec(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# Nothing collected and nothing handed out: still nothing collected.
law gm_f:
  for +O: String
  for +N: List<&2, B.Note>
  for +x: Bool
  for +t: String
  for +ns: List<&2, B.Note>
  for +ht: {t == "" : String}
  for +hns: {ns == Nil{} : List<&2, B.Note>}
  for +hE: {Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {Bool.or(x, Bool.and(String.is_empty(String.append(O, t)), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, ns)))) == True{} : Bool}

def gm_f(O, N, x, t, ns, ht, hns, hE):
  %Equal.sym(String, t, "", ht) :
    {Bool.or(x, Bool.and(String.is_empty(String.append(O, _)), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, ns)))) == True{} : Bool}
  %Equal.sym(List<&2, B.Note>, ns, Nil{}, hns) :
    {Bool.or(x, Bool.and(String.is_empty(String.append(O, "")), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, _)))) == True{} : Bool}
  %Equal.sym(String, String.append(O, ""), O, PN.str_nil(O)) :
    {Bool.or(x, Bool.and(String.is_empty(_), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, Nil{})))) == True{} : Bool}
  %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, N, Nil{}), N, PB.append_nil(B.Note, N)) :
    {Bool.or(x, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, _))) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), True{}, hE) :
    {Bool.or(x, _) == True{} : Bool}
  FR.or_true_r(x)

law gm_f2:
  for +O: String
  for +N: List<&2, B.Note>
  for +rp: P.RunP
  for +x: Bool
  for he: {P.RunSt.out(P.specRun(rp)) == "" : String} & {P.RunSt.notes(P.specRun(rp)) == Nil{} : List<&2, B.Note>}
  for +hE: {Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)) == True{} : Bool}
  {Bool.or(x, Bool.and(String.is_empty(String.append(O, P.RunSt.out(P.specRun(rp)))), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, P.RunSt.notes(P.specRun(rp)))))) == True{} : Bool}

def gm_f2(O, N, rp, x, he, hE):
  (+ho, +hn) = he
  gm_f(O, N, x, P.RunSt.out(P.specRun(rp)), P.RunSt.notes(P.specRun(rp)), ho, hn, hE)

# The guard after a byte-mode step's end.
law gm:
  for +c: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +rp: P.RunP
  for +rp2: P.RunP
  for +hc: {R.RunSt.inbody(P.specRun(rp)) == c : Bool}
  for +hi: {PR.RunInv(rp) == True{} : Bool}
  for +esp: {P.specRun(rp2) == P.clear(P.specRun(rp)) : R.RunSt}
  for +hg: {Bool.or(c, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  {Bool.or(R.RunSt.inbody(P.specRun(rp2)), Bool.and(String.is_empty(String.append(O, P.RunSt.out(P.specRun(rp)))), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, P.RunSt.notes(P.specRun(rp)))))) == True{} : Bool}

def gm(c, O, N, rp, rp2, hc, hi, esp, hg, hx):
  match c:
    case True{}:
      +SP = P.specRun(rp)
      +eib = Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp2)), R.RunSt.inbody(P.clear(SP)), True{},
        Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.specRun(rp2), P.clear(SP), esp),
        Equal.trans(Bool, R.RunSt.inbody(P.clear(SP)), R.RunSt.inbody(SP), True{}, clear_inbody(SP), hc))
      %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp2)), True{}, eib) :
        {Bool.or(_, Bool.and(String.is_empty(String.append(O, P.RunSt.out(SP))), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, P.RunSt.notes(SP))))) == True{} : Bool}
      {==}
    case False{}:
      +hin = Equal.trans(Bool, P.RunP.i(rp), R.RunSt.inbody(P.specRun(rp)), False{}, Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), ib_spec(rp)), hc)
      gm_f2(O, N, rp, R.RunSt.inbody(P.specRun(rp2)), PR.run_head_empty(rp, hi, hin, hx), hg)

# The byte mode: run_take hands out the bytes written and the messages.
def TakeR(+rp: P.RunP, +left: U32) -> Type:
  &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> &rp2: P.RunP ->
  ({NR.take(P.mkRun(rp), left) == ((C.BT(ol, ot), P.RunSt.notes(P.specRun(rp))), P.mkRun(rp2)) : (D.Bytes & List<&2, B.Note>) & NR.Run}
  & ({D.ok(C.BT(ol, ot), d) == True{} : Bool}
  & ({NR.chars(D.view(C.BT(ol, ot))) == P.RunSt.out(P.specRun(rp)) : String}
  & ({PR.RunInv(rp2) == True{} : Bool}
  & ({P.specRun(rp2) == P.clear(P.specRun(rp)) : R.RunSt}
  & {P.RunP.ow(rp2) == 0 : U32})))))

law out_mb.k:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hns: {P.RunP.x(rp) == False{} : Bool}
  for tk: TakeR(rp, lsum(src))
  OutG(fa, cs, O, N, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}), nx))

def out_mb.k(fa, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, hns, tk):
  (+ol, tk1) = tk
  (+ot, tk2) = tk1
  (+d, tk3) = tk2
  (+rp2, tk4) = tk3
  (+e1, tk5) = tk4
  (+eok, tk6) = tk5
  (+ech, tk7) = tk6
  (+einv, tk8) = tk7
  (+esp, eow) = tk8
  +Pp = {S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed} : S.StP}
  +P2 = {S.StP{o, S.MBP{rp2}, src, pd, eof, back, wp, asked, fneed} : S.StP}
  +SP = P.specRun(rp)
  +ns = P.RunSt.notes(SP)
  +t = P.RunSt.out(SP)
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), lsum(src)), left_eq(src)) :
    OutG(fa, cs, O, N, Pp, nx, Norm.out.left(o, Norm.MB{P.mkRun(rp)}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx))
  %Equal.sym((D.Bytes & List<&2, B.Note>) & NR.Run, NR.take(P.mkRun(rp), lsum(src)), ((C.BT(ol, ot), ns), P.mkRun(rp2)), e1) :
    OutG(fa, cs, O, N, Pp, nx, Norm.out.k(Norm.md.take.k(_), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx))
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{t},
    ENC.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), t,
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), t, chars_nr(D.view(C.BT(ol, ot))), ech)))
  +wf2 = wf_set_md(fa, o, S.MBP{rp}, S.MBP{rp2}, src, pd, eof, back, wp, asked, fneed, hw, einv, wf_mbw(fa, o, rp, src, pd, eof, back, wp, asked, fneed, hw))
  +O2 = String.append(O, t)
  +N2 = List.append(&2, B.Note, N, ns)
  +erep = Equal.trans(R.Report, R.finish(L2(fa, cs, Pp, S.pre(O2, N2, P.specRun(rp2)))), R.finish(L2(fa, cs, Pp, S.pre(O2, N2, P.clear(SP)))), R.finish(L2(fa, cs, Pp, S.pre(O, N, SP))),
    Equal.cong(R.RunSt, R.Report, z => R.finish(L2(fa, cs, Pp, S.pre(O2, N2, z))), P.specRun(rp2), P.clear(SP), esp),
    Equal.cong(R.RunSt, R.Report, z => R.finish(L2(fa, cs, Pp, z)), S.pre(O2, N2, P.clear(SP)), S.pre(O, N, SP), pre_clear(O, N, SP)))
  +hg2 = gm(R.RunSt.inbody(SP), O, N, rp, rp2, {==}, wf_md(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}, hw), esp, hg, hns)
  (t, (P2, (eout, ({==}, (wf2, (erep, ({==}, ({==}, ({==}, ({==}, ({==}, hg2)))))))))))


# md_ok of the String mode: six tests, left-nested.
def Z6(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool) -> Bool:
  c1 && c2 && c3 && c4 && c5 && c6

def Z2(+c1: Bool, +c2: Bool) -> Bool:
  c1 && c2

def Z3(+c1: Bool, +c2: Bool, +c3: Bool) -> Bool:
  c1 && c2 && c3

def Z4(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool) -> Bool:
  c1 && c2 && c3 && c4

def Z5(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, +c5: Bool) -> Bool:
  c1 && c2 && c3 && c4 && c5

law z6_1:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c1 == True{} : Bool}

def z6_1(c1, c2, c3, c4, c5, c6, h):
  +h5 = PB.and_true_l(Z5(c1, c2, c3, c4, c5), c6, h)
  +h4 = PB.and_true_l(Z4(c1, c2, c3, c4), c5, h5)
  +h3 = PB.and_true_l(Z3(c1, c2, c3), c4, h4)
  +h2 = PB.and_true_l(Z2(c1, c2), c3, h3)
  +h1 = PB.and_true_l(c1, c2, h2)
  h1

law z6_2:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c2 == True{} : Bool}

def z6_2(c1, c2, c3, c4, c5, c6, h):
  +h5 = PB.and_true_l(Z5(c1, c2, c3, c4, c5), c6, h)
  +h4 = PB.and_true_l(Z4(c1, c2, c3, c4), c5, h5)
  +h3 = PB.and_true_l(Z3(c1, c2, c3), c4, h4)
  +h2 = PB.and_true_l(Z2(c1, c2), c3, h3)
  PB.and_true_r(c1, c2, h2)

law z6_3:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c3 == True{} : Bool}

def z6_3(c1, c2, c3, c4, c5, c6, h):
  +h5 = PB.and_true_l(Z5(c1, c2, c3, c4, c5), c6, h)
  +h4 = PB.and_true_l(Z4(c1, c2, c3, c4), c5, h5)
  +h3 = PB.and_true_l(Z3(c1, c2, c3), c4, h4)
  PB.and_true_r(Z2(c1, c2), c3, h3)

law z6_4:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c4 == True{} : Bool}

def z6_4(c1, c2, c3, c4, c5, c6, h):
  +h5 = PB.and_true_l(Z5(c1, c2, c3, c4, c5), c6, h)
  +h4 = PB.and_true_l(Z4(c1, c2, c3, c4), c5, h5)
  PB.and_true_r(Z3(c1, c2, c3), c4, h4)

law z6_5:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c5 == True{} : Bool}

def z6_5(c1, c2, c3, c4, c5, c6, h):
  +h5 = PB.and_true_l(Z5(c1, c2, c3, c4, c5), c6, h)
  PB.and_true_r(Z4(c1, c2, c3, c4), c5, h5)

law z6_6:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +h: {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}
  {c6 == True{} : Bool}

def z6_6(c1, c2, c3, c4, c5, c6, h):

  PB.and_true_r(Z5(c1, c2, c3, c4, c5), c6, h)

law z6_mk:
  for +c1: Bool
  for +c2: Bool
  for +c3: Bool
  for +c4: Bool
  for +c5: Bool
  for +c6: Bool
  for +hc1: {c1 == True{} : Bool}
  for +hc2: {c2 == True{} : Bool}
  for +hc3: {c3 == True{} : Bool}
  for +hc4: {c4 == True{} : Bool}
  for +hc5: {c5 == True{} : Bool}
  for +hc6: {c6 == True{} : Bool}
  {Z6(c1, c2, c3, c4, c5, c6) == True{} : Bool}

def z6_mk(c1, c2, c3, c4, c5, c6, hc1, hc2, hc3, hc4, hc5, hc6):
  %Equal.sym(Bool, c1, True{}, hc1) : {Z6(_, c2, c3, c4, c5, c6) == True{} : Bool}
  %Equal.sym(Bool, c2, True{}, hc2) : {Z6(True{}, _, c3, c4, c5, c6) == True{} : Bool}
  %Equal.sym(Bool, c3, True{}, hc3) : {Z6(True{}, True{}, _, c4, c5, c6) == True{} : Bool}
  %Equal.sym(Bool, c4, True{}, hc4) : {Z6(True{}, True{}, True{}, _, c5, c6) == True{} : Bool}
  %Equal.sym(Bool, c5, True{}, hc5) : {Z6(True{}, True{}, True{}, True{}, _, c6) == True{} : Bool}
  %Equal.sym(Bool, c6, True{}, hc6) : {Z6(True{}, True{}, True{}, True{}, True{}, _) == True{} : Bool}
  {==}

# Strings
# =======

law cut_eta:
  for +c: Norm.Cut2
  {c == Norm.Cut2{Norm.Cut2.now(c), Norm.Cut2.later(c)} : Norm.Cut2}

def cut_eta(c):
  match c:
    case Norm.Cut2{+a, +b}:
      {==}

law bytes_r:
  for +a: String
  for +b: String
  for +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}
  {E.is_bytes(b) == True{} : Bool}

def bytes_r(a, b, h):
  match a:
    case SNil{}:
      h
    case SCon{+c, +t}:
      bytes_r(t, b, PB.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(t, b)), h))

law bytes_l:
  for +a: String
  for +b: String
  for +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}
  {E.is_bytes(a) == True{} : Bool}

def bytes_l(a, b, h):
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h1 = PB.and_true_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(t, b)), h)
      +h2 = bytes_l(t, b, PB.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(t, b)), h))
      %Equal.sym(Bool, U32.is_lt(Char.to_u32(c), 256), True{}, h1) : {Bool.and(_, E.is_bytes(t)) == True{} : Bool}
      %Equal.sym(Bool, E.is_bytes(t), True{}, h2) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

law emp_l:
  for +a: String
  for +b: String
  for +h: {String.is_empty(String.append(a, b)) == True{} : Bool}
  {a == "" : String}

def emp_l(a, b, h):
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Empty.absurd({SCon{c, t} == "" : String}, PB.false_ne_true(h))

law emp_r:
  for +a: String
  for +b: String
  for +h: {String.is_empty(String.append(a, b)) == True{} : Bool}
  {String.is_empty(b) == True{} : Bool}

def emp_r(a, b, h):
  match a:
    case SNil{}:
      h
    case SCon{+c, +t}:
      Empty.absurd({String.is_empty(b) == True{} : Bool}, PB.false_ne_true(h))

law nil_of:
  for +ns: List<&2, B.Note>
  for +h: {List.is_empty(&2, B.Note, ns) == True{} : Bool}
  {ns == Nil{} : List<&2, B.Note>}

def nil_of(ns, h):
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, B.Note>}, PB.false_ne_true(h))

# The String mode's end of a step
# ===============================

# The queue's split keeps the guard's text test: outside the body nothing is
# queued, so nothing is left either.
law later_ok:
  for +i: Bool
  for +NW: String
  for +LT: String
  for +Q: String
  for +hs: {String.append(NW, LT) == Q : String}
  for +h5: {Bool.or(i, String.is_empty(Q)) == True{} : Bool}
  {Bool.or(i, String.is_empty(LT)) == True{} : Bool}

def later_ok(i, NW, LT, Q, hs, h5):
  match i:
    case True{}:
      {==}
    case False{}:
      emp_r(NW, LT, %Equal.sym(String, String.append(NW, LT), Q, hs) : {String.is_empty(_) == True{} : Bool}; h5)

# The guard after a String-mode step: outside the body nothing is queued
# and nothing noted, so nothing is handed out.
law gms:
  for +i: Bool
  for +O: String
  for +N: List<&2, B.Note>
  for +NW: String
  for +LT: String
  for +Q: String
  for +ns: List<&2, B.Note>
  for +hs: {String.append(NW, LT) == Q : String}
  for +h5: {Bool.or(i, String.is_empty(Q)) == True{} : Bool}
  for +h6: {Bool.or(i, List.is_empty(&2, B.Note, ns)) == True{} : Bool}
  for +hg: {Bool.or(i, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  {Bool.or(i, Bool.and(String.is_empty(String.append(O, NW)), List.is_empty(&2, B.Note, List.append(&2, B.Note, N, ns)))) == True{} : Bool}

def gms(i, O, N, NW, LT, Q, ns, hs, h5, h6, hg):
  match i:
    case True{}:
      {==}
    case False{}:
      gm_f(O, N, False{}, NW, ns, emp_l(NW, LT, %Equal.sym(String, String.append(NW, LT), Q, hs) : {String.is_empty(_) == True{} : Bool}; h5), nil_of(ns, h6), hg)

# The report after a String-mode step, run by run (the queue split as NW, LT).
law rep_ms:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Maybe<&2, Nat>
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +NW: String
  for +LT: String
  for +hs: {String.append(NW, LT) == Norm.cat(List.reverse(&2, String, qs)) : String}
  {S.report(fa, cs, String.append(O, NW), List.append(&2, B.Note, N, ns), S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [LT], String.length(LT), code}, src, pd, eof, back, wp, asked, fneed})
    == S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}) : R.Report}

def rep_ms(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, NW, LT, hs):
  match code:
    case Some{+cc}:
      +Q = Norm.cat(List.reverse(&2, String, qs))
      +eo = Equal.trans(String, String.append(String.append(O, NW), LT), String.append(O, String.append(NW, LT)), String.append(O, Q),
        PN.str_assoc(O, NW, LT), Equal.cong(String, String, z => String.append(O, z), String.append(NW, LT), Q, hs))
      +en = PB.append_nil(B.Note, List.append(&2, B.Note, N, ns))
      %Equal.sym(String, String.append(String.append(O, NW), LT), String.append(O, Q), eo) :
        {R.Report{_, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), cc} == R.Report{String.append(O, Q), List.append(&2, B.Note, N, ns), cc} : R.Report}
      %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), List.append(&2, B.Note, N, ns), en) :
        {R.Report{String.append(O, Q), _, cc} == R.Report{String.append(O, Q), List.append(&2, B.Note, N, ns), cc} : R.Report}
      {==}
    case None{}:
      +Q = Norm.cat(List.reverse(&2, String, qs))
      +eo = Equal.trans(String, String.append(String.append(O, NW), LT), String.append(O, String.append(NW, LT)), String.append(O, Q),
        PN.str_assoc(O, NW, LT), Equal.cong(String, String, z => String.append(O, z), String.append(NW, LT), Q, hs))
      +en = PB.append_nil(B.Note, List.append(&2, B.Note, N, ns))
      +ls = B.Text.lines(S.intext(S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed}, cs))
      %Equal.sym(String, String.append(String.append(O, NW), LT), String.append(O, Q), eo) :
        {R.finish(L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, _, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), x})) == R.finish(L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, String.append(O, Q), List.append(&2, B.Note, N, ns), x})) : R.Report}
      %Equal.sym(List<&2, B.Note>, List.append(&2, B.Note, List.append(&2, B.Note, N, ns), Nil{}), List.append(&2, B.Note, N, ns), en) :
        {R.finish(L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, String.append(O, Q), _, x})) == R.finish(L.run.go(ls, fa, o, R.RunSt{n, i, h, c, e, l, b, k, String.append(O, Q), List.append(&2, B.Note, N, ns), x})) : R.Report}
      {==}

law out_ms.k:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Maybe<&2, Nat>
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hs: {String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) == Norm.cat(List.reverse(&2, String, qs)) : String}
  for os: &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) == C.BT(ol, ot) : D.Bytes}
    & ({D.ok(C.BT(ol, ot), d) == True{} : Bool} & {NR.chars(D.view(C.BT(ol, ot))) == Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)) : String}))
  OutG(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}), nx))

def out_ms.k(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, hs, os):
  (+ol, os1) = os
  (+ot, os2) = os1
  (+d, os3) = os2
  (+e1, os4) = os3
  (+eok, ech) = os4
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), lsum(src)), left_eq(src)) :
    OutG(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out.left(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx))
  %Equal.sym(Norm.Cut2, Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), Norm.Cut2{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))}, cut_eta(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) :
    OutG(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out.k(Norm.ms.take.c(_, R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, code), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx))
  %Equal.sym(D.Bytes, NR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), C.BT(ol, ot), e1) :
    OutG(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out.k(((_, ns), Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))], String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), code}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, nx))
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))},
    ENC.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)),
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), chars_nr(D.view(C.BT(ol, ot))), ech)))
  +hmd = wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, hw)
  +hmd2 = z6_mk(Nat.is_eq(String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)))), E.is_bytes(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}), String.is_empty(o2),
    Bool.or(i, String.is_empty(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)))), Bool.or(i, True{}),
    N.eq_refl(String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)))),
    bytes_r(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), %Equal.sym(String, String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), Norm.cat(List.reverse(&2, String, qs)), hs) : {E.is_bytes(_) == True{} : Bool}; z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)),
    z6_3(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), z6_4(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd),
    later_ok(i, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.cat(List.reverse(&2, String, qs)), hs, z6_5(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)),
    FR.or_true_r(i))
  +wf2 = wf_set_md(fa, o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))], String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), code}, src, pd, eof, back, wp, asked, fneed, hw, hmd2, {==})
  (Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), (S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))], String.length(Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), code}, src, pd, eof, back, wp, asked, fneed}, (eout, ({==}, (wf2, (rep_ms(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), hs),
    ({==}, ({==}, ({==}, ({==}, ({==}, gms(i, O, N, Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.cat(List.reverse(&2, String, qs)), ns, hs, z6_5(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), z6_6(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), hg))))))))))))

law out_ms.k0:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Maybe<&2, Nat>
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}) == True{} : Bool}
  for tw: {String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))) == Norm.cat(List.reverse(&2, String, qs)) : String} & {Norm.len_le(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), 1073741824) == True{} : Bool}
  OutG(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, nx, Norm.out(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}), nx))

def out_ms.k0(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, tw):
  (+hs, hl) = tw
  +hmd = wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, code}, src, pd, eof, back, wp, asked, fneed}, hw)
  out_ms.k(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, hs,
    PR.of_str(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), bytes_l(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), %Equal.sym(String, String.append(Norm.Cut2.now(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824)), Norm.Cut2.later(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824))), Norm.cat(List.reverse(&2, String, qs)), hs) : {E.is_bytes(_) == True{} : Bool}; z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)), hl))

# The end of a step from any good state.
law out_ok:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +nx: Pr.Next
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hns: {live(S.StP.md(p)) == True{} : Bool}
  OutG(fa, cs, O, N, p, nx, Norm.out(S.mkSt(fa, p), nx))

def out_ok(fa, cs, O, N, p, nx, hw, hg, hns):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      out_mb.k(fa, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, not_true(P.RunP.x(rp), hns),
        PR.run_take(rp, lsum(src), wf_md(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed}, hw)))
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      out_ms.k0(fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, code, src, pd, eof, back, wp, asked, fneed, nx, hw, hg, LIT.take_w_ok(Norm.cat(List.reverse(&2, String, qs)), 1073741824))

# A step's guarantee with the eof flag and nothing asked (the assembly's)
# ========================================================================

def StepG2(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, st: Norm.Step) -> Type:
  match st:
    case Norm.Step{s, b, ns, Pr.More{}}:
      &t: String -> &p2: S.StP -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == S.mkSt(fa, p2) : Norm.St}
        & ({S.WF(fa, p2) == True{} : Bool} & ({S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
        & ({S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
        & ({DR.more_ok(fa, p2) == True{} : Bool} & {ef == False{} : Bool}))))))
    case Norm.Step{s, b, ns, Pr.Ask{rs}}:
      &t: String -> &p2: S.StP -> ({E.out(b) == Some{t} : Maybe<&2, String>} & ({s == S.mkSt(fa, p2) : Norm.St}
        & ({S.WF(fa, p2) == True{} : Bool} & ({S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
        & ({E.reqs_ok(rs) == True{} : Bool} & ({rs == S.rq(rs) : List<&2, Pr.Req>} & ({S.mb_reqs(S.StP.md(p2), rs) == True{} : Bool}
        & ({S.StP.asked(p2) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
        & ({S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool} & {S.StP.eof(p2) == ef : Bool})))))))))
    case Norm.Step{s, b, ns, Pr.Finish{c}}:
      &t: String -> ({E.out(b) == Some{t} : Maybe<&2, String>} & {R.Report{String.append(O, t), List.append(&2, B.Note, N, ns), c} == T : R.Report})


law sg2w.m2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for -st: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +p2: S.StP
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +wf: {S.WF(fa, p2) == True{} : Bool}
  for +rep: {S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for mp: {S.src_empty(S.StP.src(p2)) == True{} : Bool} & {S.StP.eof(p2) == False{} : Bool}
  DR.StepG(fa, T, cs, O, N, Norm.Step{st, b, ns, Pr.More{}})

def sg2w.m2(fa, T, cs, O, N, st, b, ns, t, p2, eout, est, wf, rep, gd, mp):
  (hse, heo) = mp
  (t, (p2, (eout, (est, (wf, (rep, (hse, (heo, gd))))))))

# StepG2 gives DD.StepG.
law mo_mk:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +hw: {w == True{} : Bool}
  for +hse: {se == True{} : Bool}
  for +hne: {ne == True{} : Bool}
  for +hno: {no == True{} : Bool}
  {w && se && ne && no == True{} : Bool}

def mo_mk(w, se, ne, no, hw, hse, hne, hno):
  %Equal.sym(Bool, w, True{}, hw) : {_ && se && ne && no == True{} : Bool}
  %Equal.sym(Bool, se, True{}, hse) : {True{} && _ && ne && no == True{} : Bool}
  %Equal.sym(Bool, ne, True{}, hne) : {True{} && True{} && _ && no == True{} : Bool}
  %Equal.sym(Bool, no, True{}, hno) : {True{} && True{} && True{} && _ == True{} : Bool}
  {==}

law mo_parts:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {se == True{} : Bool} & {ne == True{} : Bool}

def mo_parts(w, se, ne, no, h):
  +h3 = PB.and_true_l(w && se && ne, no, h)
  (PB.and_true_r(w, se, PB.and_true_l(w && se, ne, h3)), PB.and_true_r(w && se, ne, h3))

law not_t:
  for +x: Bool
  for +h: {Bool.not(x) == True{} : Bool}
  {x == False{} : Bool}

def not_t(x, h):
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(h))
    case False{}:
      {==}

law sg2w.more:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for mp: {S.src_empty(S.StP.src(p2)) == True{} : Bool} & {Bool.not(S.StP.eof(p2)) == True{} : Bool}
  {S.src_empty(S.StP.src(p2)) == True{} : Bool} & {S.StP.eof(p2) == False{} : Bool}

def sg2w.more(fa, p2, mp):
  (hse, hne) = mp
  (hse, not_t(S.StP.eof(p2), hne))

law sg2w:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for s: Norm.Step
  for h: StepG2(fa, T, cs, O, N, ef, s)
  DR.StepG(fa, T, cs, O, N, s)

def sg2w(fa, T, cs, O, N, ef, s, h):
  match s:
    case Norm.Step{st, b, ns, Pr.More{}}:
      (+t, h1) = h
      (+p2, h2) = h1
      (eout, h3) = h2
      (est, h4) = h3
      (wf, h5) = h4
      (rep, h6) = h5
      (gd, h7) = h6
      (hmo, hef) = h7
      sg2w.m2(fa, T, cs, O, N, st, b, ns, t, p2, eout, est, wf, rep, gd,
        sg2w.more(fa, p2, mo_parts(S.WF(fa, p2), S.src_empty(S.StP.src(p2)), Bool.not(S.StP.eof(p2)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p2)), hmo)))
    case Norm.Step{st, b, ns, Pr.Ask{+rs}}:
      (+t, h1) = h
      (+p2, h2) = h1
      (eout, h3) = h2
      (est, h4) = h3
      (wf, h5) = h4
      (rep, h6) = h5
      (hq, h7) = h6
      (hrq, h8) = h7
      (hmr, h9) = h8
      (hask, h10) = h9
      (gd, heof) = h10
      (t, (p2, (eout, (est, (wf, (rep, (hq, (hrq, (hmr, (hask, gd))))))))))
    case Norm.Step{st, b, ns, Pr.Finish{+c}}:
      h

# From the end of a step (OutG) to the step's guarantee (DR.StepG)
# ==============================================================

def ask_rs(nx: Pr.Next) -> List<&2, Pr.Req>:
  match nx:
    case Pr.Ask{q}:
      q
    case _:
      Nil{}

def is_ask(nx: Pr.Next) -> Bool:
  match nx:
    case Pr.Ask{q}:
      True{}
    case _:
      False{}

def is_more(nx: Pr.Next) -> Bool:
  match nx:
    case Pr.More{}:
      True{}
    case _:
      False{}

# From the end of a step (OutG) to the step's guarantee
# ========================================================

law mbr_nil:
  for +md: S.MdP
  {S.mb_reqs(md, Nil{}) == True{} : Bool}

def mbr_nil(md):
  match md:
    case S.MBP{+rp}:
      {==}
    case S.MSP{+s, +qs, +ql, +c}:
      {==}

law out_ask:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +r: List<&2, Pr.Req>
  for s: Norm.Step
  for og: OutG(fa, cs, O, N, p, Pr.Ask{r}, s)
  for +hT: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hq: {E.reqs_ok(r) == True{} : Bool}
  for +hrq: {r == S.rq(r) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), r) == True{} : Bool}
  for +hask: {S.StP.asked(p) == S.asked_of(r) : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  StepG2(fa, T, cs, O, N, ef, s)

def out_ask(fa, T, cs, O, N, p, r, s, og, hT, hq, hrq, hmr, hask, ef, hef):
  match s:
    case Norm.Step{st, b, ns, Pr.Ask{+rs}}:
      (+t, og1) = og
      (+p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (+enx, og7) = og6
      (esrc, og8) = og7
      (eeof, og9) = og8
      (eask, og10) = og9
      (+emode, eg) = og10
      +ers = Equal.cong(Pr.Next, List<&2, Pr.Req>, z => ask_rs(z), Pr.Ask{rs}, Pr.Ask{r}, enx)
      (t, (p2, (eout, (est, (wf, (Equal.trans(R.Report, S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2), S.report(fa, cs, O, N, p), T, erep, hT),
        (%Equal.sym(List<&2, Pr.Req>, rs, r, ers) : {E.reqs_ok(_) == True{} : Bool}; hq,
        (%Equal.sym(List<&2, Pr.Req>, rs, r, ers) : {_ == S.rq(_) : List<&2, Pr.Req>}; hrq,
        (%Equal.sym(List<&2, Pr.Req>, rs, r, ers) : {S.mb_reqs(S.StP.md(p2), _) == True{} : Bool}; mbr_mode(S.StP.md(p2), S.StP.md(p), r, emode, hmr),
        (%Equal.sym(List<&2, Pr.Req>, rs, r, ers) : {S.StP.asked(p2) == S.asked_of(_) : Maybe<&2, List<&2, Pr.Req>>};
          Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), S.asked_of(r), eask, hask),
        (eg, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))))))))))))
    case Norm.Step{st, b, ns, Pr.More{}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(StepG2(fa, T, cs, O, N, ef, Norm.Step{st, b, ns, Pr.More{}}),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => is_ask(z), Pr.More{}, Pr.Ask{r}, enx)))
    case Norm.Step{st, b, ns, Pr.Finish{c}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(StepG2(fa, T, cs, O, N, ef, Norm.Step{st, b, ns, Pr.Finish{c}}),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => is_ask(z), Pr.Finish{c}, Pr.Ask{r}, enx)))

law out_more:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for s: Norm.Step
  for og: OutG(fa, cs, O, N, p, Pr.More{}, s)
  for +hT: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hsrc: {S.src_empty(S.StP.src(p)) == True{} : Bool}
  for +heof: {S.StP.eof(p) == False{} : Bool}
  for +hask0: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  StepG2(fa, T, cs, O, N, ef, s)

def out_more(fa, T, cs, O, N, p, s, og, hT, hsrc, heof, hask0, ef, hef):
  match s:
    case Norm.Step{st, b, ns, Pr.More{}}:
      (+t, og1) = og
      (+p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (+wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      (esrc, og8) = og7
      (eeof, og9) = og8
      (eask, og10) = og9
      (emode, eg) = og10
      +hse2 = Equal.trans(Bool, S.src_empty(S.StP.src(p2)), S.src_empty(S.StP.src(p)), True{}, Equal.cong(List<&2, P.SrcP>, Bool, z => S.src_empty(z), S.StP.src(p2), S.StP.src(p), esrc), hsrc)
      +heo2 = Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), False{}, eeof, heof)
      +hno2 = Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, hask0)
      (t, (p2, (eout, (est, (wf, (Equal.trans(R.Report, S.report(fa, cs, String.append(O, t), List.append(&2, B.Note, N, ns), p2), S.report(fa, cs, O, N, p), T, erep, hT),
        (eg, (mo_mk(S.WF(fa, p2), S.src_empty(S.StP.src(p2)), Bool.not(S.StP.eof(p2)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p2)), wf, hse2,
            Equal.cong(Bool, Bool, z => Bool.not(z), S.StP.eof(p2), False{}, heo2),
            Equal.cong(Maybe<&2, List<&2, Pr.Req>>, Bool, z => Maybe.is_none(&2, List<&2, Pr.Req>, z), S.StP.asked(p2), None{}, hno2)),
          Equal.trans(Bool, ef, S.StP.eof(p), False{}, Equal.sym(Bool, S.StP.eof(p), ef, hef), heof)))))))))
    case Norm.Step{st, b, ns, Pr.Ask{rs}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(StepG2(fa, T, cs, O, N, ef, Norm.Step{st, b, ns, Pr.Ask{rs}}),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => is_more(z), Pr.Ask{rs}, Pr.More{}, enx)))
    case Norm.Step{st, b, ns, Pr.Finish{c}}:
      (t, og1) = og
      (p2, og2) = og1
      (eout, og3) = og2
      (est, og4) = og3
      (wf, og5) = og4
      (erep, og6) = og5
      (enx, og7) = og6
      Empty.absurd(StepG2(fa, T, cs, O, N, ef, Norm.Step{st, b, ns, Pr.Finish{c}}),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => is_more(z), Pr.Finish{c}, Pr.More{}, enx)))

