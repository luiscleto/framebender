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
import ./proof_b_run.bend as PR
import ./proof_b_frame.bend as FR
import ./proof_b_frame_fr.bend as FF
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_str.bend as T
import ./proof_b_alleles_list.bend as AL
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A line of a byte source handled in the byte mode (norm.bend's done.b):
# the source moves past the line's LF, the run makes one L.line_step (up to
# what settle forgets), and the state is good again and stands for the same
# report. Every variable is reusable.

def StM(+dfs: B.Defs, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def SB(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> P.SrcP:
  P.SBP{len, t, d, at}

# A record of a split line (SPP, hold) or a line of the input (SBP).
def SXP(+hold: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> P.SrcP:
  match hold:
    case True{}:
      P.SPP{len, t, d, at}
    case False{}:
      P.SBP{len, t, d, at}

# The run a state holds while a record of a split line waits: the line it
# came from counted (norm_seq.bend's sp.b unticks it before the record's
# step, which counts it again).
def tick_p(+rp: P.RunP) -> P.RunP:
  match rp:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      P.RunP{1n+n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}

def RTP(+hold: Bool, +rp: P.RunP) -> P.RunP:
  match hold:
    case True{}:
      tick_p(rp)
    case False{}:
      rp

# A record of a split line is not empty (norm_seq.bend's sp.b drops an
# exhausted record buffer before its line paths).
def HNE(+hold: Bool, +len: U32, +at: U32) -> Data:
  {Bool.or(Bool.not(hold), U32.is_lt(at, len)) == True{} : Bool}

# The source's text: the line, its LF, the rest.
def SPLIT(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32) -> Data:
  {P.srctext(SB(len, t, d, at)) == String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", P.srctext(SB(len, t, d, (lf + 1 : U32))))) : String}

# Sources
# =======

def srcs_next(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hs: SPLIT(len, t, d, at, lf),
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +h: {S.srcs_ok(Con{SB(len, t, d, at), rest}) == True{} : Bool}) ->
  {S.srcs_ok(Con{SB(len, t, d, (lf + 1 : U32)), rest}) == True{} : Bool}:
  match rest:
    case Nil{}:
      W.and_tt(D.ok(C.BT(len, t), d), U32.is_le((lf + 1 : U32), len), W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), h), hle)
    case Con{+sp2, +r2}:
      +A = P.btext(len, t, at, (lf - at : U32))
      +S1 = P.srctext(SB(len, t, d, (lf + 1 : U32)))
      +ok0 = P.src_ok(SB(len, t, d, at))
      +lf0 = S.ends_lf(P.srctext(SB(len, t, d, at)))
      +h01 = W.and_l(Bool.and(ok0, lf0), S.srcs_ok(Con{sp2, r2}), h)
      +hlf = {%hs : {S.ends_lf(_) == True{} : Bool}; W.and_r(ok0, lf0, h01) : {S.ends_lf(String.append(A, String.append("\n", S1))) == True{} : Bool}}
      W.and_tt(Bool.and(P.src_ok(SB(len, t, d, (lf + 1 : U32))), S.ends_lf(S1)), S.srcs_ok(Con{sp2, r2}),
        W.and_tt(P.src_ok(SB(len, t, d, (lf + 1 : U32))), S.ends_lf(S1),
          W.and_tt(D.ok(C.BT(len, t), d), U32.is_le((lf + 1 : U32), len), W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), W.and_l(ok0, lf0, h01)), hle),
          T.lf_suf("\n", S1, T.lf_suf(A, String.append("\n", S1), hlf))),
        W.and_r(Bool.and(ok0, lf0), S.srcs_ok(Con{sp2, r2}), h))


# The first source of good sources is good.
def srcs_head(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +h: {S.srcs_ok(Con{SB(len, t, d, at), rest}) == True{} : Bool}) ->
  {P.src_ok(SB(len, t, d, at)) == True{} : Bool}:
  match rest:
    case Nil{}:
      h
    case Con{+sp2, +r2}:
      W.and_l(P.src_ok(SB(len, t, d, at)), S.ends_lf(P.srctext(SB(len, t, d, at))), W.and_l(Bool.and(P.src_ok(SB(len, t, d, at)), S.ends_lf(P.srctext(SB(len, t, d, at)))), S.srcs_ok(Con{sp2, r2}), h))

# The same for a record buffer or a byte source (hold).
def srcs_head_h(+hold: Bool, +rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +h: {S.srcs_ok(Con{SXP(hold, len, t, d, at), rest}) == True{} : Bool}) ->
  {P.src_ok(SB(len, t, d, at)) == True{} : Bool}:
  match hold:
    case False{}:
      srcs_head(rest, len, t, d, at, h)
    case True{}:
      match rest:
        case Nil{}:
          h
        case Con{+sp2, +r2}:
          W.and_l(P.src_ok(P.SPP{len, t, d, at}), S.ends_lf(P.srctext(P.SPP{len, t, d, at})), W.and_l(Bool.and(P.src_ok(P.SPP{len, t, d, at}), S.ends_lf(P.srctext(P.SPP{len, t, d, at}))), S.srcs_ok(Con{sp2, r2}), h))

# After the end of the file, the sources' text ends with an LF.
def eof_next(+eof: Bool, +rest: List<&2, P.SrcP>, +pd: P.PdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hs: SPLIT(len, t, d, at, lf),
  +h: {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Con{SB(len, t, d, at), rest})))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Con{SB(len, t, d, (lf + 1 : U32)), rest})))) == True{} : Bool}:
  match eof:
    case False{}:
      {==}
    case True{}:
      +A = P.btext(len, t, at, (lf - at : U32))
      +S1 = P.srctext(SB(len, t, d, (lf + 1 : U32)))
      +R0 = P.srcstext(rest)
      +EP = String.is_empty(P.pdtext(pd))
      +LF = S.ends_lf(String.append(P.srctext(SB(len, t, d, at)), R0))
      +h2 = {%hs : {S.ends_lf(String.append(_, R0)) == True{} : Bool}; W.and_r(EP, LF, h) : {S.ends_lf(String.append(String.append(A, String.append("\n", S1)), R0)) == True{} : Bool}}
      +h3 = {%LSS.sassoc(A, String.append("\n", S1), R0) : {S.ends_lf(_) == True{} : Bool};
        h2 : {S.ends_lf(String.append(A, String.append("\n", String.append(S1, R0)))) == True{} : Bool}}
      W.and_tt(EP, S.ends_lf(String.append(S1, R0)), W.and_l(EP, LF, h),
        T.lf_suf("\n", String.append(S1, R0), T.lf_suf(A, String.append("\n", String.append(S1, R0)), h3)))

# The text still to come: the line, its LF, then the next state's.
law itx:
  for +dfs: B.Defs
  for +o: B.Opts
  for +md: S.MdP
  for +md2: S.MdP
  for +rest: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +back2: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +asked2: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  for +cs: List<&2, String>
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +lf: U32
  for +hs: SPLIT(len, t, d, at, lf)
  {String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", S.intext(StM(dfs, o, md2, Con{SB(len, t, d, (lf + 1 : U32)), rest}, pd, eof, back2, wp, asked2, fneed2), cs))) == S.intext(StM(dfs, o, md, Con{SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed), cs) : String}

def itx(dfs,o, md, md2, rest, pd, eof, back, back2, wp, asked, asked2, fneed, fneed2, cs, len, t, d, at, lf, hs):
  +A = P.btext(len, t, at, (lf - at : U32))
  +S1 = P.srctext(SB(len, t, d, (lf + 1 : U32)))
  +R0 = P.srcstext(rest)
  +X = String.append(P.pdtext(pd), S.concat_if(eof, cs))
  %Equal.sym(String, P.srctext(SB(len, t, d, at)), String.append(A, String.append("\n", S1)), hs) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(String.append(_, R0), X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append("\n", S1)), R0), String.append(A, String.append(String.append("\n", S1), R0)), LSS.sassoc(A, String.append("\n", S1), R0)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == String.append(_, X) : String}
  %Equal.sym(String, String.append(String.append(A, String.append(String.append("\n", S1), R0)), X), String.append(A, String.append(String.append(String.append("\n", S1), R0), X)), LSS.sassoc(A, String.append(String.append("\n", S1), R0), X)) : {String.append(A, String.append("\n", String.append(String.append(S1, R0), X))) == _ : String}
  {==}

# The report
# ==========

def PPs(+hold: Bool, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  StM(dfs, o, S.MBP{RTP(hold, rp)}, Con{SXP(hold, len, t, d, at), rest}, pd, eof, back, wp, asked, fneed)

# The state after the line (done.b).
def P2(+hold: Bool, +dfs: B.Defs, +o: B.Opts, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: PC.WP) -> S.StP:
  StM(dfs, o, S.MBP{rp2}, Con{SXP(hold, len, t, d, (lf + 1 : U32)), rest}, pd, eof, 0n, wp, None{}, False{})

# What a run picture stands for keeps its fields.
law ib_spec:
  for +rp: P.RunP
  {R.RunSt.inbody(P.specRun(rp)) == P.RunP.i(rp) : Bool}

def ib_spec(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law halt_spec:
  for +rp: P.RunP
  {R.RunSt.halt(P.specRun(rp)) == P.RunP.x(rp) : Bool}

def halt_spec(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law ib_settle:
  for +st: R.RunSt
  {R.RunSt.inbody(P.settle(st)) == R.RunSt.inbody(st) : Bool}

def ib_settle(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}

# After a line's step from a run that had not stopped: in the body exactly
# when before it or at the #CHROM line (the run picture up to settle).
def ib_next(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +l: B.Line,
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), l)) : R.RunSt}) ->
  {R.RunSt.inbody(P.specRun(rp2)) == Bool.or(R.RunSt.inbody(P.specRun(rp)), R.is_chrom_line(B.Line.body(l))) : Bool}:
  +LS = L.line_step(fa, dfs, o, P.specRun(rp), l)
  Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp2)), R.RunSt.inbody(LS), Bool.or(R.RunSt.inbody(P.specRun(rp)), R.is_chrom_line(B.Line.body(l))),
    Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp2)), R.RunSt.inbody(P.settle(P.specRun(rp2))), R.RunSt.inbody(LS),
      Equal.sym(Bool, R.RunSt.inbody(P.settle(P.specRun(rp2))), R.RunSt.inbody(P.specRun(rp2)), ib_settle(P.specRun(rp2))),
      Equal.trans(Bool, R.RunSt.inbody(P.settle(P.specRun(rp2))), R.RunSt.inbody(P.settle(LS)), R.RunSt.inbody(LS),
        Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.settle(P.specRun(rp2)), P.settle(LS), hrun), ib_settle(LS))),
    FF.ib_line(fa, dfs, o, P.specRun(rp), l, Equal.trans(Bool, R.RunSt.halt(P.specRun(rp)), P.RunP.x(rp), False{}, halt_spec(rp), hx)))

# The report: the line moved into the run (the definitions: in the body the
# machine's, dfs; after a header line, dfs with the line's added, dfs2).
def rep_line(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hr: {S.report(fa, cs, O, N, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: SPLIT(len, t, d, at, lf),
  +hlc: {B.Text.lines(String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs)))) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))} : List<&2, B.Line>},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs}) ->
  {S.report(fa, cs, O, N, P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == T : R.Report}:
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +IT2 = S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs)
  +LS2 = B.Text.lines(IT2)
  +st = P.specRun(rp)
  +st2 = P.specRun(rp2)
  +i0 = R.RunSt.inbody(st)
  +D1 = L.defs.go(Con{l, LS2}, i0, dfs)
  +LSt = L.line_step(fa, dfs, o, st, l)
  %Equal.sym(Bool, R.RunSt.inbody(st2), Bool.or(i0, R.is_chrom_line(B.Line.body(l))), ib_next(dfs, fa, o, rp, rp2, l, hx, hrun)) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, _, dfs2), o, S.pre(O, N, st2))) == T : R.Report}
  %Equal.sym(B.Defs, dfs2, Bool.pick(B.Defs, i0, dfs, B.Defs.line(dfs, B.Line.body(l))), hd) :
    {R.finish(L.run.go(LS2, fa, L.defs.go(LS2, Bool.or(i0, R.is_chrom_line(B.Line.body(l))), _), o, S.pre(O, N, st2))) == T : R.Report}
  %FR.settle_inv(D1, LS2, fa, o, S.pre(O, N, st2)) : {_ == T : R.Report}
  %Equal.sym(R.RunSt, P.settle(S.pre(O, N, st2)), S.pre(O, N, P.settle(st2)), FR.settle_pre(O, N, st2)) : {R.finish(L.run.go(LS2, fa, D1, o, _)) == T : R.Report}
  %Equal.sym(R.RunSt, P.settle(st2), P.settle(LSt), hrun) : {R.finish(L.run.go(LS2, fa, D1, o, S.pre(O, N, _))) == T : R.Report}
  %FR.settle_pre(O, N, LSt) : {R.finish(L.run.go(LS2, fa, D1, o, _)) == T : R.Report}
  %Equal.sym(R.Report, R.finish(L.run.go(LS2, fa, D1, o, P.settle(S.pre(O, N, LSt)))), R.finish(L.run.go(LS2, fa, D1, o, S.pre(O, N, LSt))), FR.settle_inv(D1, LS2, fa, o, S.pre(O, N, LSt))) : {_ == T : R.Report}
  %FF.ls_defs(fa, Con{l, LS2}, dfs, o, st, l) : {R.finish(L.run.go(LS2, fa, D1, o, S.pre(O, N, _))) == T : R.Report}
  %FR.step_pre(D1, fa, o, O, N, st, l, hg) : {R.finish(L.run.go(LS2, fa, D1, o, _)) == T : R.Report}
  %Equal.trans(List<&2, B.Line>, B.Text.lines(S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs)), B.Text.lines(String.append(A, String.append("\n", IT2))), Con{l, LS2},
      Equal.cong(String, List<&2, B.Line>, x => B.Text.lines(x), S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs), String.append(A, String.append("\n", IT2)),
        Equal.sym(String, String.append(A, String.append("\n", IT2)), S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs),
          itx(dfs, o, S.MBP{rp}, S.MBP{rp2}, rest, pd, eof, back, 0n, wp, asked, None{}, fneed, False{}, cs, len, t, d, at, lf, hs))),
      hlc) :
    {R.finish(L.run.go(_, fa, L.defs.go(_, i0, dfs), o, S.pre(O, N, st))) == T : R.Report}
  hr

# The measure
# ===========

law sub_le0:
  for +x: Nat
  for +y: Nat
  {Nat.is_le(Nat.sub(x, y), x) == True{} : Bool}

def sub_le0(x, y):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      N.le_refl(1n+p)
    case 1n+p 1n+q:
      N.le_trans(Nat.sub(p, q), p, 1n+p, sub_le0(p, q), N.le_add_l(p, 1n))

law sub_anti:
  for +L0: Nat
  for +a: Nat
  for +f: Nat
  for +h: {Nat.is_le(a, f) == True{} : Bool}
  {Nat.is_le(Nat.sub(L0, f), Nat.sub(L0, a)) == True{} : Bool}

def sub_anti(L0, a, f, h):
  match L0 a f:
    case 0n _ _:
      {==}
    case 1n+l 0n 0n:
      N.le_refl(1n+l)
    case 1n+l 0n 1n+g:
      N.le_trans(Nat.sub(l, g), l, 1n+l, sub_le0(l, g), N.le_add_l(l, 1n))
    case 1n+l 1n+b 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+l, 0n), Nat.sub(l, b)) == True{} : Bool}, W.ft(h))
    case 1n+l 1n+b 1n+g:
      sub_anti(l, b, g, h)


law u2n:
  for +a: U32
  for +b: U32
  for +h: {U32.is_le(a, b) == True{} : Bool}
  {Nat.is_le(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}

def u2n(a, b, h):
  %U.is_le_to_nat(a, b) : {_ == True{} : Bool}
  h

law lt_sub1:
  for +L0: Nat
  for +a: Nat
  for +f: Nat
  for +hal: {Nat.is_le(a, f) == True{} : Bool}
  for +hlt: {Nat.is_lt(f, L0) == True{} : Bool}
  {Nat.is_lt(Nat.sub(L0, Nat.add(f, 1n)), Nat.sub(L0, a)) == True{} : Bool}

def lt_sub1(L0, a, f, hal, hlt):
  +X = Nat.sub(L0, Nat.add(f, 1n))
  N.lt_le_trans(X, Nat.sub(L0, f), Nat.sub(L0, a),
    %Equal.sym(Nat, Nat.sub(L0, f), 1n+X, AL.sub_lt(L0, f, hlt)) : {Nat.is_lt(X, _) == True{} : Bool};
    %Equal.sym(Bool, Nat.is_lt(X, 1n+X), Nat.is_le(X, X), N.lt_succ_iff(X, X)) : {_ == True{} : Bool};
    N.le_refl(X),
    sub_anti(L0, a, f, hal))

def meas_line(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +hat: {U32.is_le(at, len) == True{} : Bool},
  +hinc: {n((lf + 1 : U32)) == Nat.add(n(lf), 1n) : Nat}) ->
  {Nat.is_lt(S.measure(P2(False{}, dfs, o, rp2, len, t, d, lf, rest, pd, eof, wp)), S.measure(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed))) == True{} : Bool}:
  +M = S.msrc(rest)
  +x1 = n((len - (lf + 1 : U32) : U32))
  +x2 = n((len - at : U32))
  +k1 = {%Equal.sym(Nat, x1, Nat.sub(n(len), n((lf + 1 : U32))), LP.sub_u(len, (lf + 1 : U32), u2n((lf + 1 : U32), len, hle))) : {Nat.is_lt(_, x2) == True{} : Bool};
    %Equal.sym(Nat, x2, Nat.sub(n(len), n(at)), LP.sub_u(len, at, u2n(at, len, hat))) : {Nat.is_lt(Nat.sub(n(len), n((lf + 1 : U32))), _) == True{} : Bool};
    %Equal.sym(Nat, n((lf + 1 : U32)), Nat.add(n(lf), 1n), hinc) : {Nat.is_lt(Nat.sub(n(len), _), Nat.sub(n(len), n(at))) == True{} : Bool};
    lt_sub1(n(len), n(at), n(lf), hal, hlt) : {Nat.is_lt(x1, x2) == True{} : Bool}}
  N.lt_add_mono_r(1n, Nat.add(Nat.add(x1, 2n), M), Nat.add(Nat.add(x2, 2n), M),
    N.lt_add_mono_r(M, Nat.add(x1, 2n), Nat.add(x2, 2n), N.lt_add_mono_r(2n, x1, x2, k1)))

# A line moves the definitions from the run's state to the text after it
# (S.DEFS stays): after a header line, dfs2 holds that line's.
def defs_line(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs},
  +hls: {B.Text.lines(S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs)) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))} : List<&2, B.Line>}) ->
  {S.DEFS(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs) == S.DEFS(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs) : B.Defs}:
  +l = B.Text.line(P.btext(len, t, at, (lf - at : U32)))
  +LS2 = B.Text.lines(S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))
  +i0 = R.RunSt.inbody(P.specRun(rp))
  %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp2)), Bool.or(i0, R.is_chrom_line(B.Line.body(l))), ib_next(dfs, fa, o, rp, rp2, l, hx, hrun)) :
    {L.defs.go(LS2, _, dfs2) == S.DEFS(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs) : B.Defs}
  %Equal.sym(B.Defs, dfs2, Bool.pick(B.Defs, i0, dfs, B.Defs.line(dfs, B.Line.body(l))), hd) :
    {L.defs.go(LS2, Bool.or(i0, R.is_chrom_line(B.Line.body(l))), _) == S.DEFS(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs) : B.Defs}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs)), Con{l, LS2}, hls) : {L.defs.go(LS2, Bool.or(i0, R.is_chrom_line(B.Line.body(l))), Bool.pick(B.Defs, i0, dfs, B.Defs.line(dfs, B.Line.body(l)))) == L.defs.go(_, i0, dfs) : B.Defs}
  {==}

# What the line did (S.Moved): the line, taken from the front of the text
# still to come, moved into the run.
def moved_line(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hs: SPLIT(len, t, d, at, lf),
  +hlc: {B.Text.lines(String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs)))) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))} : List<&2, B.Line>},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs}) ->
  S.Moved(fa, cs, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)):
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +IT2 = S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs)
  +LS = B.Text.lines(S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs))
  +hls = Equal.trans(List<&2, B.Line>, LS, B.Text.lines(String.append(A, String.append("\n", IT2))), Con{l, B.Text.lines(IT2)},
      Equal.cong(String, List<&2, B.Line>, x => B.Text.lines(x), S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs), String.append(A, String.append("\n", IT2)),
        Equal.sym(String, String.append(A, String.append("\n", IT2)), S.intext(PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs),
          itx(dfs, o, S.MBP{rp}, S.MBP{rp2}, rest, pd, eof, back, 0n, wp, asked, None{}, fneed, False{}, cs, len, t, d, at, lf, hs))),
      hlc)
  (Con{l, Nil{}},
    (hls,
    ({%Equal.sym(R.RunSt, L.line_step(fa, L.defs.go(LS, R.RunSt.inbody(P.specRun(rp)), dfs), o, P.specRun(rp), l), L.line_step(fa, dfs, o, P.specRun(rp), l), FF.ls_defs(fa, LS, dfs, o, P.specRun(rp), l)) :
       {P.settle(P.specRun(rp2)) == P.settle(_) : R.RunSt};
     hrun : {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, L.defs.go(LS, R.RunSt.inbody(P.specRun(rp)), dfs), o, P.specRun(rp), l)) : R.RunSt}},
    defs_line(dfs, dfs2, fa, cs, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hx, hrun, hd, hls))))

# The line is done (done.b): Went, with the source past the line's LF; the
# definitions dfs2: the line's added after a header line (Cx.line), as hd says.
def went_line(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: SPLIT(len, t, d, at, lf),
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +hlc: {B.Text.lines(String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs)))) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(S.intext(P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))} : List<&2, B.Line>},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hinc: {n((lf + 1 : U32)) == Nat.add(n(lf), 1n) : Nat},
  +hi2: {S.md_ok(S.MBP{rp2}) == True{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hg2: {S.guard(O, N, P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs}) ->
  S.AdvG(fa, T, cs, O, N, PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs2}}):
  +p = PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +q = P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +m0 = S.md_ok(S.MBP{rp})
  +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +hat = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), srcs_head(rest, len, t, d, at, h1))
  (q,
    ({==},
    (W.c9_mk(S.md_ok(S.MBP{rp2}), W.W1(fa, q), a2, a3, a4, W.W5(fa, q), a6, a7, a8, hi2,
        srcs_next(rest, len, t, d, at, lf, hs, hle, h1),
        W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
        eof_next(eof, rest, pd, len, t, d, at, lf, hs, W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)),
        W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)),
    (rep_line(dfs, dfs2, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hr, hg, hs, hlc, hrun, hx, hd),
    (W.less_lt(q, p, meas_line(dfs, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hal, hlt, hle, hat, hinc)), ({==}, ({==}, (hg2, ({==}, (moved_line(dfs, dfs2, fa, cs, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hs, hlc, hrun, hx, hd), hk => ((lf + 1 : U32), {==})))))))))))
