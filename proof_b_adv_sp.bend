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
import ./proof_b_frame.bend as FR
import ./proof_b_frame_fr.bend as FF
import ./proof_b_rundefs.bend as RD
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_str.bend as T
import ./proof_b_adv_wf.bend as W
import ./proof_b_rg.bend as RG
import ./proof_s_inj.bend as INJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_tostr.bend as TS
import ./proof_b_alleles_list.bend as AL
import ./proof_b_lines.bend as LN
import ./proof_b_adv_part.bend as DPT
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# A record of a split line read from its buffer (an SP source) in the byte
# mode: handled as a body line from the run unticked (norm_seq.bend's sp.b),
# then the source moves past it (done.b with hold: Src.of gives SP again).
# The state after stands for the same report: the record moved from the
# records waiting (S.RG) into the run. Every variable is reusable.

def Ls() -> Data:
  List<&2, B.Line>

# A line's step from a run in the body stays in the body.
def ib_ls.k(+dfs: B.Defs, +xh: Bool, +i: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o0: String, +ns: List<&2, B.Note>, +l: B.Line,
  +hi: {i == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, i, h, c, e, la, b, k, o0, ns, xh}, l)) == True{} : Bool}:
  match xh i:
    case True{} _:
      hi
    case False{} True{}:
      +fs = B.Rec.fields(B.Line.body(l))
      FF.ib_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, R.RunSt{1n+n, True{}, h, c, e, la, b, k, o0, ns, False{}}, o, l, B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
    case False{} False{}:
      Empty.absurd({R.RunSt.inbody(L.line_step(fa, dfs, o, R.RunSt{n, False{}, h, c, e, la, b, k, o0, ns, False{}}, l)) == True{} : Bool}, N.false_ne_true(hi))

def ib_ls(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +s: R.RunSt, +l: B.Line, +hi: {R.RunSt.inbody(s) == True{} : Bool}) ->
  {R.RunSt.inbody(L.line_step(fa, dfs, o, s, l)) == True{} : Bool}:
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +k, +o0, +ns, +xh}:
      ib_ls.k(dfs, xh, i, fa, o, n, h, c, e, la, b, k, o0, ns, l, hi)

# A body line keeps the line count.
law n_pieces:
  for +ps: List<&2, String>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +term: String
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.n(L.pieces_in(ps, fa, o, st, term, at, inpos)) == R.RunSt.n(st) : Nat}

def n_piece.k(+h: Bool, +p: String, +fa: List<&2, B.Contig>, +o: B.Opts, +st: R.RunSt, +term: String, +at: B.At, +inpos: Nat) ->
  {R.RunSt.n(L.piece_in(h, p, fa, o, st, term, at, inpos)) == R.RunSt.n(st) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      INJ.body_n(L.judge(fa, p), st, o, B.Line{p, term}, at, inpos)

def n_pieces(ps, fa, o, st, term, at, inpos):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +s1 = L.piece_in(R.RunSt.halt(st), p, fa, o, st, term, at, inpos)
      Equal.trans(Nat, R.RunSt.n(L.pieces_in(t, fa, o, s1, term, at, inpos)), R.RunSt.n(s1), R.RunSt.n(st),
        n_pieces(t, fa, o, s1, term, at, inpos), n_piece.k(R.RunSt.halt(st), p, fa, o, st, term, at, inpos))

def n_unsplit.k(+b: Bool, +r: B.Res, +c: B.Code, +o: B.Opts, +st: R.RunSt, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {R.RunSt.n(Bool.pick(R.RunSt, b, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))) == R.RunSt.n(st) : Nat}:
  match b:
    case True{}:
      INJ.body_n(r, st, o, l, at, inpos)
    case False{}:
      INJ.problem_n(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)

law n_body_in:
  for +pt: B.Parts
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +at: B.At
  for +inpos: Nat
  {R.RunSt.n(L.body_in(pt, fa, o, st, l, at, inpos)) == R.RunSt.n(st) : Nat}

def n_body_in(pt, fa, o, st, l, at, inpos):
  match pt:
    case B.Whole{}:
      INJ.body_n(L.judge(fa, B.Line.body(l)), st, o, l, at, inpos)
    case B.Pieces{+ps}:
      n_pieces(ps, fa, o, st, B.Line.term(l), at, inpos)
    case B.Unsplit{+c}:
      n_unsplit.k(L.stops(L.judge(fa, B.Line.body(l)), R.Opts.strict(o)), L.judge(fa, B.Line.body(l)), c, o, st, l, at, inpos)

# A record from a run in the body, not stopped, at line 1+k: the run after
# it is in the body, at line 1+k again.
def rec_k(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +k: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +kk: R.Cnt, +so: String, +ns: List<&2, B.Note>, +l: B.Line) ->
  {R.RunSt.n(L.line_step(fa, dfs, o, Norm.rs_untick(R.RunSt{1n+k, True{}, h, c, e, la, b, kk, so, ns, False{}}), l)) == 1n+k : Nat}:
  +fs = B.Rec.fields(B.Line.body(l))
  +s1 = {R.RunSt{1n+Nat.sub(k, 0n), True{}, h, c, e, la, b, kk, so, ns, False{}} : R.RunSt}
  Equal.trans(Nat, R.RunSt.n(L.body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, o, s1, l, B.At{1n+Nat.sub(k, 0n), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))), 1n+Nat.sub(k, 0n), 1n+k,
    n_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, o, s1, l, B.At{1n+Nat.sub(k, 0n), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(k, 0n), k, N.sub_zero(k)))

law rec_n:
  for +fa: List<&2, B.Contig>
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +l: B.Line
  for +k: Nat
  for +hx: {R.RunSt.halt(st) == False{} : Bool}
  for +hi: {R.RunSt.inbody(st) == True{} : Bool}
  for +hn: {R.RunSt.n(st) == 1n+k : Nat}
  {R.RunSt.n(L.line_step(fa, dfs, o, Norm.rs_untick(st), l)) == 1n+k : Nat}

def rec_n(fa, dfs, o, st, l, k, hx, hi, hn):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) : {R.RunSt.n(L.line_step(fa, dfs, o, Norm.rs_untick(R.RunSt{n, i, h, c, e, la, b, kk, so, ns, _}), l)) == 1n+k : Nat}
      %Equal.sym(Bool, i, True{}, hi) : {R.RunSt.n(L.line_step(fa, dfs, o, Norm.rs_untick(R.RunSt{n, _, h, c, e, la, b, kk, so, ns, False{}}), l)) == 1n+k : Nat}
      %Equal.sym(Nat, n, 1n+k, hn) : {R.RunSt.n(L.line_step(fa, dfs, o, Norm.rs_untick(R.RunSt{_, True{}, h, c, e, la, b, kk, so, ns, False{}}), l)) == 1n+k : Nat}
      rec_k(fa, dfs, o, k, h, c, e, la, b, kk, so, ns, l)

def ib_ut(+st: R.RunSt) -> {R.RunSt.inbody(Norm.rs_untick(st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      {==}

def halt_ut(+st: R.RunSt) -> {R.RunSt.halt(Norm.rs_untick(st)) == R.RunSt.halt(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      {==}

def n_settle(+st: R.RunSt) -> {R.RunSt.n(P.settle(st)) == R.RunSt.n(st) : Nat}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      match x:
        case False{}:
          {==}
        case True{}:
          {==}

def ib_settle(+st: R.RunSt) -> {R.RunSt.inbody(P.settle(st)) == R.RunSt.inbody(st) : Bool}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      match x:
        case False{}:
          {==}
        case True{}:
          {==}

# The sources and the end of the file, past the record (as for a byte source).
def srcs_next_p(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +h: {S.srcs_ok(Con{P.SPP{len, t, d, at}, rest}) == True{} : Bool}) ->
  {S.srcs_ok(Con{P.SPP{len, t, d, (lf + 1 : U32)}, rest}) == True{} : Bool}:
  match rest:
    case Nil{}:
      W.and_tt(D.ok(C.BT(len, t), d), U32.is_le((lf + 1 : U32), len), W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), h), hle)
    case Con{+sp2, +r2}:
      +A = P.btext(len, t, at, (lf - at : U32))
      +S1 = P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})
      +ok0 = P.src_ok(P.SPP{len, t, d, at})
      +lf0 = S.ends_lf(P.srctext(P.SPP{len, t, d, at}))
      +h01 = W.and_l(Bool.and(ok0, lf0), S.srcs_ok(Con{sp2, r2}), h)
      +hlf = {%hs : {S.ends_lf(_) == True{} : Bool}; W.and_r(ok0, lf0, h01) : {S.ends_lf(String.append(A, String.append("\n", S1))) == True{} : Bool}}
      W.and_tt(Bool.and(P.src_ok(P.SPP{len, t, d, (lf + 1 : U32)}), S.ends_lf(S1)), S.srcs_ok(Con{sp2, r2}),
        W.and_tt(P.src_ok(P.SPP{len, t, d, (lf + 1 : U32)}), S.ends_lf(S1),
          W.and_tt(D.ok(C.BT(len, t), d), U32.is_le((lf + 1 : U32), len), W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), W.and_l(ok0, lf0, h01)), hle),
          T.lf_suf("\n", S1, T.lf_suf(A, String.append("\n", S1), hlf))),
        W.and_r(Bool.and(ok0, lf0), S.srcs_ok(Con{sp2, r2}), h))

def eof_next_p(+eof: Bool, +rest: List<&2, P.SrcP>, +pd: P.PdP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +h: {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Con{P.SPP{len, t, d, at}, rest})))) == True{} : Bool}) ->
  {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Con{P.SPP{len, t, d, (lf + 1 : U32)}, rest})))) == True{} : Bool}:
  match eof:
    case False{}:
      {==}
    case True{}:
      +A = P.btext(len, t, at, (lf - at : U32))
      +S1 = P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})
      +R0 = P.srcstext(rest)
      +EP = String.is_empty(P.pdtext(pd))
      +LF = S.ends_lf(String.append(P.srctext(P.SPP{len, t, d, at}), R0))
      +h2 = {%hs : {S.ends_lf(String.append(_, R0)) == True{} : Bool}; W.and_r(EP, LF, h) : {S.ends_lf(String.append(String.append(A, String.append("\n", S1)), R0)) == True{} : Bool}}
      +h3 = {%LSS.sassoc(A, String.append("\n", S1), R0) : {S.ends_lf(_) == True{} : Bool};
        h2 : {S.ends_lf(String.append(A, String.append("\n", String.append(S1, R0)))) == True{} : Bool}}
      W.and_tt(EP, S.ends_lf(String.append(S1, R0)), W.and_l(EP, LF, h),
        T.lf_suf("\n", String.append(S1, R0), T.lf_suf(A, String.append("\n", String.append(S1, R0)), h3)))


# ---------------------------------------------------------------------------
# The run of a record's state
# ---------------------------------------------------------------------------

def tp_spec(+rp: P.RunP) -> {P.specRun(LI.tick_p(rp)) == R.tick(P.specRun(rp)) : R.RunSt}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def tp_mk(+rp: P.RunP) -> {P.mkRun(LI.tick_p(rp)) == NR.tick(P.mkRun(rp)) : NR.Run}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def tp_ib(+rp: P.RunP) -> {R.RunSt.inbody(P.specRun(LI.tick_p(rp))) == P.RunP.i(rp) : Bool}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# A record's step from the counted run is the line's step from the run.
def rs_sp(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +l: B.Line,
  +hx: {P.RunP.x(rp) == False{} : Bool}) ->
  {S.rstep(fa, dfs, o, P.specRun(LI.tick_p(rp)), l) == L.line_step(fa, dfs, o, P.specRun(rp), l) : R.RunSt}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l0, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) :
        {S.rstep(fa, dfs, o, P.specRun(LI.tick_p(P.RunP{n, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, _})), l) == L.line_step(fa, dfs, o, P.specRun(P.RunP{n, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, _}), l) : R.RunSt}
      Equal.cong(Nat, R.RunSt, z => L.line_step(fa, dfs, o, P.specRun(P.RunP{z, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), l), Nat.sub(n, 0n), n, N.sub_zero(n))

# The same with O and N in front.
def rs_spp(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +O: String, +N: List<&2, B.Note>, +rp: P.RunP, +l: B.Line,
  +hx: {P.RunP.x(rp) == False{} : Bool}) ->
  {S.rstep(fa, dfs, o, S.pre(O, N, P.specRun(LI.tick_p(rp))), l) == L.line_step(fa, dfs, o, S.pre(O, N, P.specRun(rp)), l) : R.RunSt}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l0, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) :
        {S.rstep(fa, dfs, o, S.pre(O, N, P.specRun(LI.tick_p(P.RunP{n, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, _}))), l) == L.line_step(fa, dfs, o, S.pre(O, N, P.specRun(P.RunP{n, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, _})), l) : R.RunSt}
      Equal.cong(Nat, R.RunSt, z => L.line_step(fa, dfs, o, S.pre(O, N, P.specRun(P.RunP{z, i, h, c, cbl, cbt, e, l0, f, b, bn, tl, k, obl, obt, ow, ns, False{}})), l), Nat.sub(n, 0n), n, N.sub_zero(n))

# ---------------------------------------------------------------------------
# A record read from its buffer (done.b with hold)
# ---------------------------------------------------------------------------

# The state with a record at at (the run: the machine's before the record's
# step, rp, counted once more), and the state after it.
def PS(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  LI.StM(dfs, o, S.MBP{LI.tick_p(rp)}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)

def QS(+dfs2: B.Defs, +o: B.Opts, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +wp: PC.WP) -> S.StP:
  LI.StM(dfs2, o, S.MBP{rp2}, Con{P.SPP{len, t, d, (lf + 1 : U32)}, rest}, pd, eof, 0n, wp, None{}, False{})

# The record's lines: the record, then the records after it.
def lines_sp(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}) ->
  {B.Text.lines(P.srctext(P.SPP{len, t, d, at})) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))} : Ls()}:
  +A = P.btext(len, t, at, (lf - at : U32))
  +S1 = P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})
  Equal.trans(Ls(), B.Text.lines(P.srctext(P.SPP{len, t, d, at})), B.Text.lines(String.append(A, String.append("\n", S1))), Con{B.Text.line(A), B.Text.lines(S1)},
    Equal.cong(String, Ls(), x => B.Text.lines(x), P.srctext(P.SPP{len, t, d, at}), String.append(A, String.append("\n", S1)), hs),
    LSS.lines_cons(A, S1, hn))

# The definitions in the body are the machine's.
def defs_in(+LS: Ls(), +dfs: B.Defs, +i: Bool, +hi: {i == True{} : Bool}) -> {L.defs.go(LS, i, dfs) == dfs : B.Defs}:
  Equal.trans(B.Defs, L.defs.go(LS, i, dfs), L.defs.go(LS, True{}, dfs), dfs,
    Equal.cong(Bool, B.Defs, z => L.defs.go(LS, z, dfs), i, True{}, hi), FF.defs_done(LS, dfs))

# The report: the record moved from the records waiting into the run.
def rep_sp(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hr: {S.report(fa, cs, O, N, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hl: {B.Text.lines(P.srctext(P.SPP{len, t, d, at})) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))} : Ls()},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hi: {P.RunP.i(rp) == True{} : Bool},
  +hi2: {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool},
  +hd: {dfs2 == dfs : B.Defs}) ->
  {S.report(fa, cs, O, N, QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == T : R.Report}:
  +l = B.Text.line(P.btext(len, t, at, (lf - at : U32)))
  +L1 = B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))
  +LS = B.Text.lines(S.intext(PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs))
  +R0 = S.recs(rest)
  +RS1 = {Con{P.SPP{len, t, d, (lf + 1 : U32)}, R0} : List<&2, P.SrcP>}
  +st0 = P.specRun(LI.tick_p(rp))
  +s = P.specRun(rp)
  +st2 = P.specRun(rp2)
  +LSt = L.line_step(fa, dfs, o, s, l)
  +hib = Equal.trans(Bool, R.RunSt.inbody(s), P.RunP.i(rp), True{}, LI.ib_spec(rp), hi)
  +hg0 = {%Equal.sym(Bool, R.RunSt.inbody(s), True{}, hib) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
    {==} : {Bool.or(R.RunSt.inbody(s), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}}
  %Equal.sym(Bool, R.RunSt.inbody(st2), True{}, hi2) :
    {R.finish(L.run.go(LS, fa, L.defs.go(LS, _, dfs2), o, S.RG(RS1, fa, L.defs.go(LS, _, dfs2), o, S.pre(O, N, st2)))) == T : R.Report}
  %Equal.sym(B.Defs, L.defs.go(LS, True{}, dfs2), dfs2, FF.defs_done(LS, dfs2)) :
    {R.finish(L.run.go(LS, fa, _, o, S.RG(RS1, fa, _, o, S.pre(O, N, st2)))) == T : R.Report}
  %Equal.sym(B.Defs, dfs2, dfs, hd) :
    {R.finish(L.run.go(LS, fa, _, o, S.RG(RS1, fa, _, o, S.pre(O, N, st2)))) == T : R.Report}
  %RG.rep_settle(LS, fa, dfs, o, RS1, S.pre(O, N, st2)) : {_ == T : R.Report}
  %Equal.sym(R.RunSt, P.settle(S.pre(O, N, st2)), S.pre(O, N, P.settle(st2)), FR.settle_pre(O, N, st2)) : {RG.REP(LS, fa, dfs, o, RS1, _) == T : R.Report}
  %Equal.sym(R.RunSt, P.settle(st2), P.settle(LSt), hrun) : {RG.REP(LS, fa, dfs, o, RS1, S.pre(O, N, _)) == T : R.Report}
  %FR.settle_pre(O, N, LSt) : {RG.REP(LS, fa, dfs, o, RS1, _) == T : R.Report}
  %Equal.sym(R.Report, RG.REP(LS, fa, dfs, o, RS1, P.settle(S.pre(O, N, LSt))), RG.REP(LS, fa, dfs, o, RS1, S.pre(O, N, LSt)), RG.rep_settle(LS, fa, dfs, o, RS1, S.pre(O, N, LSt))) : {_ == T : R.Report}
  %FR.step_pre(dfs, fa, o, O, N, s, l, hg0) : {RG.REP(LS, fa, dfs, o, RS1, _) == T : R.Report}
  %rs_spp(fa, dfs, o, O, N, rp, l, hx) : {RG.REP(LS, fa, dfs, o, RS1, _) == T : R.Report}
  %hl : {R.finish(L.run.go(LS, fa, dfs, o, S.RG(R0, fa, dfs, o, S.rgo(_, fa, dfs, o, S.pre(O, N, st0))))) == T : R.Report}
  %defs_in(LS, dfs, R.RunSt.inbody(st0), Equal.trans(Bool, R.RunSt.inbody(st0), P.RunP.i(rp), True{}, tp_ib(rp), hi)) :
    {R.finish(L.run.go(LS, fa, _, o, S.RG(R0, fa, _, o, S.rgo(B.Text.lines(P.srctext(P.SPP{len, t, d, at})), fa, _, o, S.pre(O, N, st0))))) == T : R.Report}
  hr

# A line's step from a run in the body, not stopped, counts the line.
def n_ls.k(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +n0: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +la: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +kk: R.Cnt, +so: String, +ns: List<&2, B.Note>, +l: B.Line) ->
  {R.RunSt.n(L.line_step(fa, dfs, o, R.RunSt{n0, True{}, h, c, e, la, b, kk, so, ns, False{}}, l)) == 1n+n0 : Nat}:
  +fs = B.Rec.fields(B.Line.body(l))
  +s1 = {R.RunSt{1n+n0, True{}, h, c, e, la, b, kk, so, ns, False{}} : R.RunSt}
  n_body_in(B.Rec.parts(dfs, o, B.Line.body(l)), fa, o, s1, l, B.At{1n+n0, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))

def n_ls(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +st: R.RunSt, +l: B.Line,
  +hx: {R.RunSt.halt(st) == False{} : Bool},
  +hi: {R.RunSt.inbody(st) == True{} : Bool}) ->
  {R.RunSt.n(L.line_step(fa, dfs, o, st, l)) == 1n+R.RunSt.n(st) : Nat}:
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +la, +b, +kk, +so, +ns, +x}:
      %Equal.sym(Bool, x, False{}, hx) : {R.RunSt.n(L.line_step(fa, dfs, o, R.RunSt{n, i, h, c, e, la, b, kk, so, ns, _}, l)) == 1n+n : Nat}
      %Equal.sym(Bool, i, True{}, hi) : {R.RunSt.n(L.line_step(fa, dfs, o, R.RunSt{n, _, h, c, e, la, b, kk, so, ns, False{}}, l)) == 1n+n : Nat}
      n_ls.k(fa, dfs, o, n, h, c, e, la, b, kk, so, ns, l)

# Less work: as much of the input's own text, a shorter record buffer.
def meas_sp(+dfs: B.Defs, +dfs2: B.Defs, +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hal: {Nat.is_le(LI.n(at), LI.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(lf), LI.n(len)) == True{} : Bool},
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +hat: {U32.is_le(at, len) == True{} : Bool},
  +hinc: {LI.n((lf + 1 : U32)) == Nat.add(LI.n(lf), 1n) : Nat}) ->
  {S.less(QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool}:
  +M = S.measure(PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed))
  +MR = S.mrec(rest)
  +x1 = LI.n((len - (lf + 1 : U32) : U32))
  +x2 = LI.n((len - at : U32))
  +k1 = {%Equal.sym(Nat, x1, Nat.sub(LI.n(len), LI.n((lf + 1 : U32))), LP.sub_u(len, (lf + 1 : U32), LI.u2n((lf + 1 : U32), len, hle))) : {Nat.is_lt(_, x2) == True{} : Bool};
    %Equal.sym(Nat, x2, Nat.sub(LI.n(len), LI.n(at)), LP.sub_u(len, at, LI.u2n(at, len, hat))) : {Nat.is_lt(Nat.sub(LI.n(len), LI.n((lf + 1 : U32))), _) == True{} : Bool};
    %Equal.sym(Nat, LI.n((lf + 1 : U32)), Nat.add(LI.n(lf), 1n), hinc) : {Nat.is_lt(Nat.sub(LI.n(len), _), Nat.sub(LI.n(len), LI.n(at))) == True{} : Bool};
    LI.lt_sub1(LI.n(len), LI.n(at), LI.n(lf), hal, hlt) : {Nat.is_lt(x1, x2) == True{} : Bool}}
  W.or_r(Nat.is_lt(M, M), Bool.and(Nat.is_eq(M, M), Nat.is_lt(Nat.add(Nat.add(x1, 2n), MR), Nat.add(Nat.add(x2, 2n), MR))),
    W.and_tt(Nat.is_eq(M, M), Nat.is_lt(Nat.add(Nat.add(x1, 2n), MR), Nat.add(Nat.add(x2, 2n), MR)), N.eq_refl(M),
      N.lt_add_mono_r(MR, Nat.add(x1, 2n), Nat.add(x2, 2n), N.lt_add_mono_r(2n, x1, x2, k1))))

# The records waiting, settled: the record's step moved into the run.
def mv_sp(+fa: List<&2, B.Contig>, +dfs: B.Defs, +D: B.Defs, +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +R0: List<&2, P.SrcP>,
  +hD: {D == dfs : B.Defs},
  +hl: {B.Text.lines(P.srctext(P.SPP{len, t, d, at})) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))} : Ls()},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool}) ->
  {P.settle(S.RG(Con{P.SPP{len, t, d, (lf + 1 : U32)}, R0}, fa, D, o, P.specRun(rp2))) == P.settle(S.RG(Con{P.SPP{len, t, d, at}, R0}, fa, D, o, P.specRun(LI.tick_p(rp)))) : R.RunSt}:
  +l = B.Text.line(P.btext(len, t, at, (lf - at : U32)))
  +RS1 = {Con{P.SPP{len, t, d, (lf + 1 : U32)}, R0} : List<&2, P.SrcP>}
  +st0 = P.specRun(LI.tick_p(rp))
  +st2 = P.specRun(rp2)
  +LSt = L.line_step(fa, dfs, o, P.specRun(rp), l)
  %Equal.sym(B.Defs, D, dfs, hD) :
    {P.settle(S.RG(RS1, fa, _, o, st2)) == P.settle(S.RG(Con{P.SPP{len, t, d, at}, R0}, fa, _, o, st0)) : R.RunSt}
  %Equal.sym(Ls(), B.Text.lines(P.srctext(P.SPP{len, t, d, at})), Con{l, B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))}, hl) :
    {P.settle(S.RG(RS1, fa, dfs, o, st2)) == P.settle(S.RG(R0, fa, dfs, o, S.rgo(_, fa, dfs, o, st0))) : R.RunSt}
  %Equal.sym(R.RunSt, S.rstep(fa, dfs, o, st0, l), LSt, rs_sp(fa, dfs, o, rp, l, hx)) :
    {P.settle(S.RG(RS1, fa, dfs, o, st2)) == P.settle(S.RG(RS1, fa, dfs, o, _)) : R.RunSt}
  Equal.trans(R.RunSt, P.settle(S.RG(RS1, fa, dfs, o, st2)), P.settle(S.RG(RS1, fa, dfs, o, P.settle(st2))), P.settle(S.RG(RS1, fa, dfs, o, LSt)),
    Equal.sym(R.RunSt, P.settle(S.RG(RS1, fa, dfs, o, P.settle(st2))), P.settle(S.RG(RS1, fa, dfs, o, st2)), RG.rg_settle(RS1, fa, dfs, o, st2)),
    Equal.trans(R.RunSt, P.settle(S.RG(RS1, fa, dfs, o, P.settle(st2))), P.settle(S.RG(RS1, fa, dfs, o, P.settle(LSt))), P.settle(S.RG(RS1, fa, dfs, o, LSt)),
      Equal.cong(R.RunSt, R.RunSt, z => P.settle(S.RG(RS1, fa, dfs, o, z)), P.settle(st2), P.settle(LSt), hrun),
      RG.rg_settle(RS1, fa, dfs, o, LSt)))

# What the record did (S.Moved): no line of the input's own text; the
# record moved from the records waiting into the run.
def moved_sp(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hl: {B.Text.lines(P.srctext(P.SPP{len, t, d, at})) == Con{B.Text.line(P.btext(len, t, at, (lf - at : U32))), B.Text.lines(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)}))} : Ls()},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hi: {P.RunP.i(rp) == True{} : Bool},
  +hi2b: {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool},
  +hd2: {dfs2 == dfs : B.Defs}) ->
  S.Moved(fa, cs, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)):
  +LS = B.Text.lines(S.intext(PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs))
  +LS2 = B.Text.lines(S.intext(QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs))
  +st0 = P.specRun(LI.tick_p(rp))
  +hd0 = defs_in(LS, dfs, R.RunSt.inbody(st0), Equal.trans(Bool, R.RunSt.inbody(st0), P.RunP.i(rp), True{}, tp_ib(rp), hi))
  (Nil{}, ({==},
    (mv_sp(fa, dfs, L.defs.go(LS, R.RunSt.inbody(st0), dfs), o, rp, rp2, len, t, d, at, lf, S.recs(rest), hd0, hl, hrun, hx),
     Equal.trans(B.Defs, L.defs.go(LS2, R.RunSt.inbody(P.specRun(rp2)), dfs2), dfs, L.defs.go(LS, R.RunSt.inbody(st0), dfs),
       Equal.trans(B.Defs, L.defs.go(LS2, R.RunSt.inbody(P.specRun(rp2)), dfs2), dfs2, dfs, defs_in(LS2, dfs2, R.RunSt.inbody(P.specRun(rp2)), hi2b), hd2),
       Equal.sym(B.Defs, L.defs.go(LS, R.RunSt.inbody(st0), dfs), dfs, hd0)))))

# The 9th test after the record: the records still come first, from a run
# in the body that has counted their line.
def w8_sp(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +h8: {W.W8(fa, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hi: {P.RunP.i(rp) == True{} : Bool}) ->
  {W.W8(fa, QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == True{} : Bool}:
  +A = P.btext(len, t, at, (lf - at : U32))
  +l = B.Text.line(A)
  +S0 = P.srctext(P.SPP{len, t, d, at})
  +S1 = P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})
  +AB = E.all_bytes(S.opts_args(o))
  +RF0 = Bool.and(S.rtok(S0), S.recs_first(rest))
  +st0 = P.specRun(LI.tick_p(rp))
  +RR0 = Bool.and(R.RunSt.inbody(st0), Nat.is_le(1n, R.RunSt.n(st0)))
  +s = P.specRun(rp)
  +st2 = P.specRun(rp2)
  +LSt = L.line_step(fa, dfs, o, s, l)
  +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
  +hrf = W.and_r(AB, RF0, h01)
  +hrt0 = W.and_l(S.rtok(S0), S.recs_first(rest), hrf)
  +hlf0 = {%hs : {S.ends_lf(_) == True{} : Bool}; W.and_l(S.ends_lf(S0), S.all_one(B.Text.lines(S0)), hrt0) : {S.ends_lf(String.append(A, String.append("\n", S1))) == True{} : Bool}}
  +ho1 = W.and_r(S.one_alt(l), S.all_one(B.Text.lines(S1)),
    {%lines_sp(len, t, d, at, lf, hs, hn) : {S.all_one(_) == True{} : Bool}; W.and_r(S.ends_lf(S0), S.all_one(B.Text.lines(S0)), hrt0) :
      {S.all_one(Con{l, B.Text.lines(S1)}) == True{} : Bool}})
  +hlf1 = T.lf_suf("\n", S1, T.lf_suf(A, String.append("\n", S1), hlf0))
  +hib = Equal.trans(Bool, R.RunSt.inbody(s), P.RunP.i(rp), True{}, LI.ib_spec(rp), hi)
  +hxs = Equal.trans(Bool, R.RunSt.halt(s), P.RunP.x(rp), False{}, LI.halt_spec(rp), hx)
  +hi2 = Equal.trans(Bool, R.RunSt.inbody(st2), R.RunSt.inbody(LSt), True{},
    Equal.trans(Bool, R.RunSt.inbody(st2), R.RunSt.inbody(P.settle(st2)), R.RunSt.inbody(LSt),
      Equal.sym(Bool, R.RunSt.inbody(P.settle(st2)), R.RunSt.inbody(st2), ib_settle(st2)),
      Equal.trans(Bool, R.RunSt.inbody(P.settle(st2)), R.RunSt.inbody(P.settle(LSt)), R.RunSt.inbody(LSt),
        Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.settle(st2), P.settle(LSt), hrun), ib_settle(LSt))),
    ib_ls(dfs, fa, o, s, l, hib))
  +hn2 = Equal.trans(Nat, R.RunSt.n(st2), R.RunSt.n(LSt), 1n+R.RunSt.n(s),
    Equal.trans(Nat, R.RunSt.n(st2), R.RunSt.n(P.settle(st2)), R.RunSt.n(LSt),
      Equal.sym(Nat, R.RunSt.n(P.settle(st2)), R.RunSt.n(st2), n_settle(st2)),
      Equal.trans(Nat, R.RunSt.n(P.settle(st2)), R.RunSt.n(P.settle(LSt)), R.RunSt.n(LSt),
        Equal.cong(R.RunSt, Nat, z => R.RunSt.n(z), P.settle(st2), P.settle(LSt), hrun), n_settle(LSt))),
    n_ls(fa, dfs, o, s, l, hxs, hib))
  W.and_tt(Bool.and(AB, Bool.and(S.rtok(S1), S.recs_first(rest))), Bool.and(R.RunSt.inbody(st2), Nat.is_le(1n, R.RunSt.n(st2))),
    W.and_tt(AB, Bool.and(S.rtok(S1), S.recs_first(rest)), W.and_l(AB, RF0, h01),
      W.and_tt(S.rtok(S1), S.recs_first(rest), W.and_tt(S.ends_lf(S1), S.all_one(B.Text.lines(S1)), hlf1, ho1), W.and_r(S.rtok(S0), S.recs_first(rest), hrf))),
    W.and_tt(R.RunSt.inbody(st2), Nat.is_le(1n, R.RunSt.n(st2)), hi2,
      {%Equal.sym(Nat, R.RunSt.n(st2), 1n+R.RunSt.n(s), hn2) : {Nat.is_le(1n, _) == True{} : Bool}; N.le_add_r(1n, R.RunSt.n(s)) : {Nat.is_le(1n, R.RunSt.n(st2)) == True{} : Bool}}))

# The record is in the body: its state's run is (WF, 9th test).
def ib_sp(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +h8: {W.W8(fa, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool}) ->
  {P.RunP.i(rp) == True{} : Bool}:
  +AB = E.all_bytes(S.opts_args(o))
  +RF0 = Bool.and(S.rtok(P.srctext(P.SPP{len, t, d, at})), S.recs_first(rest))
  +st0 = P.specRun(LI.tick_p(rp))
  +RR0 = Bool.and(R.RunSt.inbody(st0), Nat.is_le(1n, R.RunSt.n(st0)))
  Equal.trans(Bool, P.RunP.i(rp), R.RunSt.inbody(st0), True{}, Equal.sym(Bool, R.RunSt.inbody(st0), P.RunP.i(rp), tp_ib(rp)),
    W.and_l(R.RunSt.inbody(st0), Nat.is_le(1n, R.RunSt.n(st0)), W.and_r(Bool.and(AB, RF0), RR0, h8)))

# The first source of good sources is good (a record buffer).
def srcs_head_p(+rest: List<&2, P.SrcP>, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +h: {S.srcs_ok(Con{P.SPP{len, t, d, at}, rest}) == True{} : Bool}) ->
  {P.src_ok(P.SPP{len, t, d, at}) == True{} : Bool}:
  match rest:
    case Nil{}:
      h
    case Con{+sp2, +r2}:
      W.and_l(P.src_ok(P.SPP{len, t, d, at}), S.ends_lf(P.srctext(P.SPP{len, t, d, at})), W.and_l(Bool.and(P.src_ok(P.SPP{len, t, d, at}), S.ends_lf(P.srctext(P.SPP{len, t, d, at}))), S.srcs_ok(Con{sp2, r2}), h))

# The record is done (done.b with hold): Went, with the record buffer past
# the record's LF.
def went_sp(+dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(lf), LI.n(len)) == True{} : Bool},
  +hinc: {LI.n((lf + 1 : U32)) == Nat.add(LI.n(lf), 1n) : Nat},
  +hi2: {S.md_ok(S.MBP{rp2}) == True{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hg2: {S.guard(O, N, QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs}) ->
  S.AdvG(fa, T, cs, O, N, PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.SP{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs2}}):
  +p = PS(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +q = QS(dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +m0 = S.md_ok(S.MBP{LI.tick_p(rp)})
  +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +hi = ib_sp(dfs, fa, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, h8)
  +hat = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), srcs_head_p(rest, len, t, d, at, h1))
  +l = B.Text.line(P.btext(len, t, at, (lf - at : U32)))
  +hib = Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), True{}, LI.ib_spec(rp), hi)
  +hd2 = Equal.trans(B.Defs, dfs2, Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(l))), dfs, hd,
    Equal.cong(Bool, B.Defs, z => Bool.pick(B.Defs, z, dfs, B.Defs.line(dfs, B.Line.body(l))), R.RunSt.inbody(P.specRun(rp)), True{}, hib))
  +hl = lines_sp(len, t, d, at, lf, hs, hn)
  +hi2b = Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp2)), R.RunSt.inbody(P.specRun(rp2)), True{}, {==},
    W.and_l(R.RunSt.inbody(P.specRun(rp2)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp2))),
      W.and_r(Bool.and(E.all_bytes(S.opts_args(o)), Bool.and(S.rtok(P.srctext(P.SPP{len, t, d, (lf + 1 : U32)})), S.recs_first(rest))), Bool.and(R.RunSt.inbody(P.specRun(rp2)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp2)))),
        w8_sp(dfs, dfs2, fa, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hs, hn, h8, hrun, hx, hi))))
  (q,
    ({==},
    (W.c9_mk(S.md_ok(S.MBP{rp2}), W.W1(fa, q), a2, a3, a4, W.W5(fa, q), a6, a7, W.W8(fa, q), hi2,
        srcs_next_p(rest, len, t, d, at, lf, hs, hle, h1),
        W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
        eof_next_p(eof, rest, pd, len, t, d, at, lf, hs, W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)),
        W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
        w8_sp(dfs, dfs2, fa, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hs, hn, h8, hrun, hx, hi)),
    (rep_sp(dfs, dfs2, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hr, hl, hrun, hx, hi, hi2b, hd2),
    (meas_sp(dfs, dfs2, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hal, hlt, hle, hat, hinc),
    ({==}, ({==}, (hg2, ({==}, (moved_sp(dfs, dfs2, fa, cs, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hl, hrun, hx, hi, hi2b, hd2), {==}))))))))))

# A line done (done.b), from a byte source (hold False: proof_b_adv_line.bend's
# went_line) or a record buffer (hold True: went_sp).
def went_h(+hold: Bool, +dfs: B.Defs, +dfs2: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, lf),
  +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool},
  +hn: {P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(LI.n(at), LI.n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(LI.n(lf), LI.n(len)) == True{} : Bool},
  +hinc: {LI.n((lf + 1 : U32)) == Nat.add(LI.n(lf), 1n) : Nat},
  +hi2: {S.md_ok(S.MBP{rp2}) == True{} : Bool},
  +hrun: {P.settle(P.specRun(rp2)) == P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (lf - at : U32))))) : R.RunSt},
  +hg2: {S.guard(O, N, LI.P2(hold, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hd: {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (lf - at : U32)))))) : B.Defs}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.done.b(o, (P.mkRun(rp2), C.BT(len, t)), (lf + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs2, hold}, PC.mkWin(fa, wp))):
  match hold:
    case False{}:
      LI.went_line(dfs, dfs2, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hs, hle,
        LSS.lines_cons(P.btext(len, t, at, (lf - at : U32)), S.intext(LI.P2(False{}, dfs2, o, rp2, len, t, d, lf, rest, pd, eof, wp), cs), hn),
        hal, hlt, hinc, hi2, hrun, hg2, hx, hd)
    case True{}:
      went_sp(dfs, dfs2, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hw, hr, hs, hle, hn, hal, hlt, hinc, hi2, hrun, hg2, hx, hd)

def tp_x(+rp: P.RunP) -> {P.RunP.x(LI.tick_p(rp)) == P.RunP.x(rp) : Bool}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# The line goes to the String mode (to_str): the run as the state holds it
# (with hold: counted again), the source as it was.
def tostr_h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +back2: Nat, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.to_str(o, P.mkRun(rp), C.BT(len, t), at, back2, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed2)):
  match hold:
    case False{}:
      TS.to_ms_went(dfs, fa, T, cs, O, N, o, rp, Con{P.SBP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed, back2, fneed2, hw, hr, hg, hx)
    case True{}:
      %tp_mk(rp) :
        S.AdvG(fa, T, cs, O, N, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.Went{Norm.St{o, Norm.to_ms(_), Con{Norm.SP{C.BT(len, t), at}, P.mkSrcs(rest)}, P.mkPd(pd), eof, back2, PC.mkWin(fa, wp), None{}, fneed2, dfs}})
      TS.to_ms_went(dfs, fa, T, cs, O, N, o, LI.tick_p(rp), Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed, back2, fneed2, hw, hr, hg,
        Equal.trans(Bool, P.RunP.x(LI.tick_p(rp)), P.RunP.x(rp), False{}, tp_x(rp), hx))

# A text of length 1+k is not empty.
def len_ne(+s: String, +k: Nat, +h: {String.length(s) == 1n+k : Nat}) -> {String.is_empty(s) == False{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({String.is_empty(SNil{}) == False{} : Bool}, N.zero_ne_succ(k, h))
    case SCon{+c, +r}:
      {==}

# A record buffer with a byte left holds some text.
def ne_sp(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hlt: {U32.is_lt(at, len) == True{} : Bool}) ->
  {String.is_empty(P.srctext(P.SPP{len, t, d, at})) == False{} : Bool}:
  +V = D.view(C.BT(len, t))
  +hl = Equal.trans(Bool, Nat.is_lt(U32.to_nat(at), U32.to_nat(len)), U32.is_lt(at, len), True{}, Equal.sym(Bool, U32.is_lt(at, len), Nat.is_lt(U32.to_nat(at), U32.to_nat(len)), U.is_lt_to_nat(at, len)), hlt)
  len_ne(P.srctext(P.SPP{len, t, d, at}), Nat.sub(U32.to_nat(len), Nat.add(U32.to_nat(at), 1n)),
    Equal.trans(Nat, String.length(NR.chars(List.drop(&2, U32, V, U32.to_nat(at)))), List.length(&2, U32, List.drop(&2, U32, V, U32.to_nat(at))), 1n+Nat.sub(U32.to_nat(len), Nat.add(U32.to_nat(at), 1n)),
      LSS.length_chars(List.drop(&2, U32, V, U32.to_nat(at))),
      Equal.trans(Nat, List.length(&2, U32, List.drop(&2, U32, V, U32.to_nat(at))), Nat.sub(List.length(&2, U32, V), U32.to_nat(at)), 1n+Nat.sub(U32.to_nat(len), Nat.add(U32.to_nat(at), 1n)),
        LP.len_drop(V, U32.to_nat(at)),
        {%Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(len), O.view_size_t(len, t, d, hok)) : {Nat.sub(_, U32.to_nat(at)) == 1n+Nat.sub(U32.to_nat(len), Nat.add(U32.to_nat(at), 1n)) : Nat};
         AL.sub_lt(U32.to_nat(len), U32.to_nat(at), hl) : {Nat.sub(List.length(&2, U32, V), U32.to_nat(at)) == 1n+Nat.sub(U32.to_nat(len), Nat.add(U32.to_nat(at), 1n)) : Nat}})))

def part_sp.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hlt: {U32.is_lt(at, len) == True{} : Bool},
  +hlf: {S.ends_lf(P.srctext(P.SPP{len, t, d, at})) == True{} : Bool},
  sn: DPT.SNW(len, t, d, at)) -> Empty:
  match sn:
    case (hn, hsa):
      W.ft(Equal.trans(Bool, False{}, String.is_empty(P.srctext(P.SPP{len, t, d, at})), True{}, Equal.sym(Bool, String.is_empty(P.srctext(P.SPP{len, t, d, at})), False{}, ne_sp(len, t, d, at, hok, hlt)), T.nolf_lf(P.srctext(P.SPP{len, t, d, at}), hn, hlf)))

# A record buffer always holds an LF from at: the partial line's path is not
# taken (the record ends with an LF, and holds a byte at at).
def part_sp(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hjf: {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +hne: LI.HNE(True{}, len, at)) -> Empty:
  +p = LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{LI.tick_p(rp)})
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +X = P.srctext(P.SPP{len, t, d, at})
  +hso = srcs_head_p(rest, len, t, d, at, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +AB = E.all_bytes(S.opts_args(o))
  +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
  +st0 = P.specRun(LI.tick_p(rp))
  +RR0 = Bool.and(R.RunSt.inbody(st0), Nat.is_le(1n, R.RunSt.n(st0)))
  +hlf = W.and_l(S.ends_lf(X), S.all_one(B.Text.lines(X)), W.and_l(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, W.and_l(Bool.and(AB, RF0), RR0, h8))))
  part_sp.k(len, t, d, at, hok, hne, hlf, LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, LI.n(len), D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10), hjf)))

# The partial line's path (dec.part), from a byte source (proof_b_adv_part.bend)
# or a record buffer (not taken).
def part_h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hjf: {LI.n(len) == D.first(D.view(C.BT(len, t)), LI.n(at), LI.n(len), 10) : Nat},
  +hne: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, BY.len(C.BT(len, t)), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed2)):
  match hold:
    case False{}:
      DPT.part(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hjf)
    case True{}:
      Empty.absurd(S.AdvG(fa, T, cs, O, N, LI.PPs(True{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
        Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, BY.len(C.BT(len, t)), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp), fneed2)),
        part_sp(dfs, fa, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hw, hjf, hne))

# The machine's run and source for a line not handled yet, as the state
# holds them (norm_seq.bend's retick and Src.of).
def rt_eq(+hold: Bool, +rp: P.RunP) -> {Norm.retick(hold, P.mkRun(rp)) == P.mkRun(LI.RTP(hold, rp)) : NR.Run}:
  match hold:
    case True{}:
      Equal.sym(NR.Run, P.mkRun(LI.tick_p(rp)), NR.tick(P.mkRun(rp)), tp_mk(rp))
    case False{}:
      {==}

def so_eq(+hold: Bool, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> {Norm.Src.of(hold, C.BT(len, t), at) == P.mkSrc(LI.SXP(hold, len, t, d, at)) : Norm.Src}:
  match hold:
    case True{}:
      {==}
    case False{}:
      {==}

# A state with the line not handled yet, as the machine builds it (retick,
# Src.of) and as the hold state pictures it.
def st_eq_h(+hold: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +dfs: B.Defs) ->
  {Norm.St{o, Norm.MB{Norm.retick(hold, P.mkRun(rp))}, Con{Norm.Src.of(hold, C.BT(len, t), at), P.mkSrcs(rest)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs} == S.mkSt(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) : Norm.St}:
  match hold:
    case False{}:
      {==}
    case True{}:
      Equal.cong(NR.Run, Norm.St, z => Norm.St{o, Norm.MB{z}, Con{Norm.SP{C.BT(len, t), at}, P.mkSrcs(rest)}, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}, NR.tick(P.mkRun(rp)), P.mkRun(LI.tick_p(rp)),
        Equal.sym(NR.Run, P.mkRun(LI.tick_p(rp)), NR.tick(P.mkRun(rp)), tp_mk(rp)))

def x_h(+hold: Bool, +rp: P.RunP, +hx: {P.RunP.x(rp) == False{} : Bool}) -> {P.RunP.x(LI.RTP(hold, rp)) == False{} : Bool}:
  match hold:
    case False{}:
      hx
    case True{}:
      Equal.trans(Bool, P.RunP.x(LI.tick_p(rp)), P.RunP.x(rp), False{}, tp_x(rp), hx)

def tp_inv(+rp: P.RunP) -> {RD.RunInv(LI.tick_p(rp)) == RD.RunInv(rp) : Bool}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# The run's invariant does not look at the line count.
def inv_h(+hold: Bool, +rp: P.RunP, +h: {RD.RunInv(LI.RTP(hold, rp)) == True{} : Bool}) -> {RD.RunInv(rp) == True{} : Bool}:
  match hold:
    case False{}:
      h
    case True{}:
      Equal.trans(Bool, RD.RunInv(rp), RD.RunInv(LI.tick_p(rp)), True{}, Equal.sym(Bool, RD.RunInv(LI.tick_p(rp)), RD.RunInv(rp), tp_inv(rp)), h)

# ---------------------------------------------------------------------------
# A record buffer with no record left (sp.b's done case): dropped
# ---------------------------------------------------------------------------

law sub_lez:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.sub(a, b) == 0n : Nat}

def sub_lez(a, b, h):
  match a b:
    case 0n _:
      {==}
    case 1n+(+ap) 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, W.ft(h))
    case 1n+(+ap) 1n+(+bp):
      sub_lez(ap, bp, h)

def len0(+s: String, +h: {String.length(s) == 0n : Nat}) -> {s == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Empty.absurd({SCon{c, r} == "" : String}, N.succ_ne_zero(String.length(r), h))

# A record buffer read to its end holds no text.
def em_sp(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hle: {U32.is_le(len, at) == True{} : Bool}) ->
  {P.srctext(P.SPP{len, t, d, at}) == "" : String}:
  +V = D.view(C.BT(len, t))
  +hl = Equal.trans(Bool, Nat.is_le(U32.to_nat(len), U32.to_nat(at)), U32.is_le(len, at), True{}, Equal.sym(Bool, U32.is_le(len, at), Nat.is_le(U32.to_nat(len), U32.to_nat(at)), U.is_le_to_nat(len, at)), hle)
  len0(P.srctext(P.SPP{len, t, d, at}),
    Equal.trans(Nat, String.length(NR.chars(List.drop(&2, U32, V, U32.to_nat(at)))), List.length(&2, U32, List.drop(&2, U32, V, U32.to_nat(at))), 0n,
      LSS.length_chars(List.drop(&2, U32, V, U32.to_nat(at))),
      Equal.trans(Nat, List.length(&2, U32, List.drop(&2, U32, V, U32.to_nat(at))), Nat.sub(List.length(&2, U32, V), U32.to_nat(at)), 0n,
        LP.len_drop(V, U32.to_nat(at)),
        {%Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(len), O.view_size_t(len, t, d, hok)) : {Nat.sub(_, U32.to_nat(at)) == 0n : Nat};
         sub_lez(U32.to_nat(len), U32.to_nat(at), hl) : {Nat.sub(List.length(&2, U32, V), U32.to_nat(at)) == 0n : Nat}})))

def lt2(+x: Nat) -> {Nat.is_lt(0n, Nat.add(x, 2n)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def SD(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  LI.StM(dfs, o, S.MBP{rp}, Con{P.SPP{len, t, d, at}, rest}, pd, eof, back, wp, asked, fneed)

def sp_done(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hle: {U32.is_le(len, at) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed, dfs}}):
  +p = SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +q = LI.StM(dfs, o, S.MBP{rp}, rest, pd, eof, back, wp, None{}, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +X = P.srctext(P.SPP{len, t, d, at})
  +h1 = W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +hso = srcs_head_p(rest, len, t, d, at, h1)
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hX = em_sp(len, t, d, at, hok, hle)
  +EP = String.is_empty(P.pdtext(pd))
  +h4 = W.c9_4(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +h5 = W.c9_5(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +h8 = W.c9_8(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw)
  +AB = E.all_bytes(S.opts_args(o))
  +RF0 = Bool.and(S.rtok(X), S.recs_first(rest))
  +RR0 = Bool.and(R.RunSt.inbody(P.specRun(rp)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp))))
  +h01 = W.and_l(Bool.and(AB, RF0), RR0, h8)
  +w8 = W.and_tt(Bool.and(AB, S.recs_first(rest)), S.recs_run(S.MBP{rp}, rest),
    W.and_tt(AB, S.recs_first(rest), W.and_l(AB, RF0, h01), W.and_r(S.rtok(X), S.recs_first(rest), W.and_r(AB, RF0, h01))),
    W.or_r(List.is_empty(&2, P.SrcP, S.recs(rest)), RR0, W.and_r(Bool.and(AB, RF0), RR0, h8)))
  w5 = {%Equal.sym(String, X, "", hX) :
      {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(String.append(_, P.srcstext(rest))))) == True{} : Bool} -> {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    (h => h) : {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(String.append(X, P.srcstext(rest))))) == True{} : Bool} -> {Bool.or(Bool.not(eof), Bool.and(EP, S.ends_lf(P.srcstext(rest)))) == True{} : Bool}}
  +M = S.measure(p)
  +MR = S.mrec(rest)
  +x1 = U32.to_nat((len - at : U32))
  (q,
    ({==},
    (W.c9_mk(m0, W.W1(fa, q), a2, a3, W.W4(fa, q), W.W5(fa, q), a6, a7, W.W8(fa, q), W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
        DPT.srcs_tl(rest, P.SPP{len, t, d, at}, h1),
        W.c9_2(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_3(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw),
        W.or_r(S.src_empty(rest), EP, h4),
        w5(h5),
        W.c9_6(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), W.c9_7(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw), w8),
    ({%hX :
        {R.finish(L.run.go(B.Text.lines(S.intext(p, cs)), fa, S.DEFS(p, cs), o, S.RG(S.recs(rest), fa, S.DEFS(p, cs), o, S.rgo(B.Text.lines(_), fa, S.DEFS(p, cs), o, S.pre(O, N, P.specRun(rp)))))) == T : R.Report};
      hr : {S.report(fa, cs, O, N, q) == T : R.Report}},
    (W.or_r(Nat.is_lt(M, M), Bool.and(Nat.is_eq(M, M), Nat.is_lt(MR, Nat.add(Nat.add(x1, 2n), MR))),
        W.and_tt(Nat.is_eq(M, M), Nat.is_lt(MR, Nat.add(Nat.add(x1, 2n), MR)), N.eq_refl(M), N.lt_add_mono_r(MR, 0n, Nat.add(x1, 2n), lt2(x1)))),
    ({==}, ({==}, (hg, ({==}, ((Nil{}, ({==},
      {%Equal.sym(String, X, "", hX) :
          {P.settle(S.RG(S.recs(rest), fa, S.DEFS(p, cs), o, P.specRun(rp))) == P.settle(S.RG(S.recs(rest), fa, S.DEFS(p, cs), o, S.rgo(B.Text.lines(_), fa, S.DEFS(p, cs), o, P.specRun(rp)))) : R.RunSt};
        {==} : {P.settle(S.RG(S.recs(rest), fa, S.DEFS(p, cs), o, P.specRun(rp))) == P.settle(S.RG(S.recs(rest), fa, S.DEFS(p, cs), o, S.rgo(B.Text.lines(X), fa, S.DEFS(p, cs), o, P.specRun(rp)))) : R.RunSt}}, {==})), {==}))))))))))

# ---------------------------------------------------------------------------
# A record's run: the state's, its line not counted (norm_run.bend's untick)
# ---------------------------------------------------------------------------

def untick_p(+rp: P.RunP) -> P.RunP:
  match rp:
    case P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      P.RunP{Nat.sub(n, 1n), i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}

def ut_mk(+rp: P.RunP) -> {NR.untick(P.mkRun(rp)) == P.mkRun(untick_p(rp)) : NR.Run}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# A run that has counted a line is the count before it, counted.
def tu_eq(+rp: P.RunP, +hn: {Nat.is_le(1n, P.RunP.n(rp)) == True{} : Bool}) -> {LI.tick_p(untick_p(rp)) == rp : P.RunP}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      match n:
        case 0n:
          Empty.absurd({LI.tick_p(untick_p(P.RunP{0n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x})) == P.RunP{0n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x} : P.RunP}, W.ft(hn))
        case 1n+m:
          Equal.cong(Nat, P.RunP, z => P.RunP{1n+z, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, Nat.sub(m, 0n), m, N.sub_zero(m))

def ut_x(+rp: P.RunP) -> {P.RunP.x(untick_p(rp)) == P.RunP.x(rp) : Bool}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def ut_ow(+rp: P.RunP) -> {P.RunP.ow(untick_p(rp)) == P.RunP.ow(rp) : U32}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def ut_obl(+rp: P.RunP) -> {P.RunP.obl(untick_p(rp)) == P.RunP.obl(rp) : U32}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def nsp(+rp: P.RunP) -> {R.RunSt.n(P.specRun(rp)) == P.RunP.n(rp) : Nat}:
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# A record waiting: its line counted (WF, 9th test).
def n_sp(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool}) ->
  {Nat.is_le(1n, P.RunP.n(rp)) == True{} : Bool}:
  +p = SD(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +h8 = W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  +AB = E.all_bytes(S.opts_args(o))
  +RF0 = Bool.and(S.rtok(P.srctext(P.SPP{len, t, d, at})), S.recs_first(rest))
  +RR0 = Bool.and(R.RunSt.inbody(P.specRun(rp)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp))))
  {%nsp(rp) : {Nat.is_le(1n, _) == True{} : Bool};
   W.and_r(R.RunSt.inbody(P.specRun(rp)), Nat.is_le(1n, R.RunSt.n(P.specRun(rp))), W.and_r(Bool.and(AB, RF0), RR0, h8)) : {Nat.is_le(1n, P.RunP.n(rp)) == True{} : Bool}}

# A record left: at < len.
def ult(+len: U32, +at: U32, +h: {U32.is_le(len, at) == False{} : Bool}) -> {U32.is_lt(at, len) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(at, len), Nat.is_lt(U32.to_nat(at), U32.to_nat(len)), True{}, U.is_lt_to_nat(at, len),
    N.not_le_lt(U32.to_nat(len), U32.to_nat(at), Equal.trans(Bool, Nat.is_le(U32.to_nat(len), U32.to_nat(at)), U32.is_le(len, at), False{}, Equal.sym(Bool, U32.is_le(len, at), Nat.is_le(U32.to_nat(len), U32.to_nat(at)), U.is_le_to_nat(len, at)), h)))
