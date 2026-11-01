import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_b_lines_str.bend as LSS
import ./proof_b_cut_str.bend as CS
import ./proof_b_cache_lem.bend as X
import ./proof_b_lit.bend as LT
import ./proof_fast.bend as PF
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_tostr.bend as TS
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_ib.bend as IB
import ./proof_b_adv_wr.bend as WR
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_msx.bend as MSX
import ./proof_b_adv_injr.bend as IR
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as NN
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_b_judge_bytes.bend as JB

# adv_ok on a body line the fast path did not take (norm.bend slow): the
# verdict (pb-cache's vd_ok), then the record written (VRes, VSame), the switch
# to the String mode when it does not fit, or the reads asked (VWant). Every
# variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# Missing (stated here, notes/bytes_proofs_adv.md)
# ---------------------------------------------------------------------------

# The judge's text is bytes, for a record of bytes and a reference of bytes
# (run_body_line's hb).
def judge_bytes(+fa: List<&2, B.Contig>, +body: String,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge(fa, body))) == True{} : Bool}:
  JB.judge_bytes(fa, body, hb, hbd)

# ---------------------------------------------------------------------------
# The line's CHROM field: bytes, and no longer than the line
# ---------------------------------------------------------------------------

law hd_push:
  for +c: Char
  for +ps: List<&2, String>
  {B.Rec.field(String.split.push(c, ps), 0n) == SCon{c, B.Rec.field(ps, 0n)} : String}

def hd_push(c, ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      {==}

def spb.k(+cut: Bool, +c: Char, +r: String, +sep: Char,
  +hc: {U32.is_lt(Char.to_u32(c), 256) == True{} : Bool},
  +ih: {E.is_bytes(B.Rec.field(String.split(r, sep), 0n)) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.field(String.split.fin(c, String.split(r, sep), cut), 0n)) == True{} : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, B.Rec.field(String.split.push(c, String.split(r, sep)), 0n), SCon{c, B.Rec.field(String.split(r, sep), 0n)}, hd_push(c, String.split(r, sep))) :
        {E.is_bytes(_) == True{} : Bool}
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(B.Rec.field(String.split(r, sep), 0n)), hc, ih)

def sp_bytes(+s: String, +sep: Char, +h: {E.is_bytes(s) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.field(String.split(s, sep), 0n)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      spb.k(Char.is_eq(c, sep), c, r, sep, W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), h),
        sp_bytes(r, sep, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), h)))

def spl.k(+cut: Bool, +c: Char, +r: String, +sep: Char,
  +ih: {Nat.is_le(String.length(B.Rec.field(String.split(r, sep), 0n)), String.length(r)) == True{} : Bool}) ->
  {Nat.is_le(String.length(B.Rec.field(String.split.fin(c, String.split(r, sep), cut), 0n)), 1n+String.length(r)) == True{} : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, B.Rec.field(String.split.push(c, String.split(r, sep)), 0n), SCon{c, B.Rec.field(String.split(r, sep), 0n)}, hd_push(c, String.split(r, sep))) :
        {Nat.is_le(String.length(_), 1n+String.length(r)) == True{} : Bool}
      ih

def sp_len(+s: String, +sep: Char) ->
  {Nat.is_le(String.length(B.Rec.field(String.split(s, sep), 0n)), String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      spl.k(Char.is_eq(c, sep), c, r, sep, sp_len(r, sep))

law lt_split:
  for +l: B.Line
  {B.Line.text(l) == String.append(B.Line.body(l), B.Line.term(l)) : String}

def lt_split(l):
  match l:
    case B.Line{+bd, +tm}:
      {==}

def bytes_app_l(+a: String, +b: String, +h: {E.is_bytes(String.append(a, b)) == True{} : Bool}) ->
  {E.is_bytes(a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      W.and_tt(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(r, b)), h),
        bytes_app_l(r, b, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(String.append(r, b)), h)))

def body_bytes(+A: String, +hby: {E.is_bytes(A) == True{} : Bool}) ->
  {E.is_bytes(B.Line.body(Norm.line(A))) == True{} : Bool}:
  bytes_app_l(B.Line.body(Norm.line(A)), B.Line.term(Norm.line(A)),
    %lt_split(Norm.line(A)) : {E.is_bytes(_) == True{} : Bool}; WR.line_bytes(A, hby))

def bl.k(+cr: Bool, +A: String) ->
  {Nat.is_le(String.length(B.Line.body(B.Text.line.if(cr, A))), String.length(A)) == True{} : Bool}:
  match cr:
    case True{}:
      NN.le_trans(String.length(String.take(A, Nat.sub(String.length(A), 1n))), Nat.sub(String.length(A), 1n), String.length(A),
        X.take_len_le(A, Nat.sub(String.length(A), 1n)), LI.sub_le0(String.length(A), 1n))
    case False{}:
      NN.le_refl(String.length(A))

def body_len(+A: String) -> {Nat.is_le(String.length(B.Line.body(Norm.line(A))), String.length(A)) == True{} : Bool}:
  bl.k(Norm.ends_cr(A), A)

def f0_bytes(+A: String, +hby: {E.is_bytes(A) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.field(J.pfs(B.Line.body(Norm.line(A))), 0n)) == True{} : Bool}:
  %Equal.sym(String, B.Rec.field(J.pfs(B.Line.body(Norm.line(A))), 0n), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n), PF.pfs_field(B.Line.body(Norm.line(A)), 0n, {==})) :
    {E.is_bytes(_) == True{} : Bool}
  sp_bytes(B.Line.body(Norm.line(A)), '\t', body_bytes(A, hby))

# The line's text from at to j has j - at bytes.
def a_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool}) ->
  {String.length(P.btext(len, t, at, (j - at : U32))) == n((j - at : U32)) : Nat}:
  +X0 = D.view(C.BT(len, t))
  +sl = D.slice(X0, n(at), n((j - at : U32)))
  +hfit = {%Equal.sym(Nat, n((j - at : U32)), Nat.sub(n(j), n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(n(at), _), List.length(&2, U32, X0)) == True{} : Bool};
    %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(j), n(at))), n(j), NN.le_sub_add(n(at), n(j), hal)) : {Nat.is_le(_, List.length(&2, U32, X0)) == True{} : Bool};
    %LP.len_x(len, t, d, hok) : {Nat.is_le(n(j), _) == True{} : Bool};
    NN.lt_to_le(n(j), n(len), hlt) : {Nat.is_le(Nat.add(n(at), n((j - at : U32))), List.length(&2, U32, X0)) == True{} : Bool}}
  Equal.trans(Nat, String.length(NR.chars(sl)), List.length(&2, U32, sl), n((j - at : U32)), LSS.length_chars(sl), LP.slice_len(X0, n(at), n((j - at : U32)), hfit))

# A word not above y is at most y (y kept abstract).
def not_lt_u(+y: U32, +x: U32, +h: {U32.is_lt(y, x) == False{} : Bool}) -> {Nat.is_le(n(x), n(y)) == True{} : Bool}:
  NN.not_lt_le(n(y), n(x), %U.is_lt_to_nat(y, x) : {_ == False{} : Bool}; h)

def f0_len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +w: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hsm: {U32.is_lt(w, (j - at : U32)) == False{} : Bool}) ->
  {Norm.len_le(B.Rec.field(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 0n), w) == True{} : Bool}:
  +F0 = B.Rec.field(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 0n)
  +l1 = {%Equal.sym(String, F0, B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 0n), PF.pfs_field(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), 0n, {==})) : {Nat.is_le(String.length(_), String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))) == True{} : Bool};
    sp_len(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), '\t') : {Nat.is_le(String.length(F0), String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))) == True{} : Bool}}
  +l3 = {%a_len(len, t, d, at, j, hok, hal, hlt) : {Nat.is_le(String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), _) == True{} : Bool};
    body_len(P.btext(len, t, at, (j - at : U32))) : {Nat.is_le(String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), n((j - at : U32))) == True{} : Bool}}
  LT.le_len_le(F0, w, NN.le_trans(String.length(F0), String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), n(w), l1,
    NN.le_trans(String.length(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), n((j - at : U32)), n(w), l3, not_lt_u(w, (j - at : U32), hsm))))

def hsm_le(+y: U32, +x: U32, +h: {U32.is_lt(y, x) == False{} : Bool}) -> {U32.is_le(x, y) == True{} : Bool}:
  LP.le_u(x, y, not_lt_u(y, x, h))

# ---------------------------------------------------------------------------
# The reads asked: their contig is the line's CHROM
# ---------------------------------------------------------------------------

def mb_fc(+rs: List<&2, Pr.Req>, +c: String,
  +hf: {MSX.fst_c(rs) == Some{c} : Maybe<&2, String>},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcl: {Norm.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_reqs.k(rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({S.mb_reqs.k(Nil{}) == True{} : Bool}, W.ft(Equal.cong(Maybe<&2, String>, Bool, m => Maybe.is_some(&2, String, m), None{}, Some{c}, hf)))
    case Con{Pr.Req{+c1, +a1, +b1}, +tl}:
      +ec = Equal.cong(Maybe<&2, String>, String, m => Maybe.default(&2, String, m, ""), Some{c1}, Some{c}, hf)
      %Equal.sym(String, c1, c, ec) : {Bool.and(E.is_bytes(_), Norm.len_le(_, 268435456)) == True{} : Bool}
      W.and_tt(E.is_bytes(c), Norm.len_le(c, 268435456), hcb, hcl)

def ao(+rs: List<&2, Pr.Req>, +hl: {Nat.is_le(1n, List.length(&2, Pr.Req, rs)) == True{} : Bool}) ->
  {Some{rs} == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}:
  match rs:
    case Nil{}:
      Empty.absurd({Some{Nil{}} == S.asked_of(Nil{}) : Maybe<&2, List<&2, Pr.Req>>}, W.ft(hl))
    case Con{+r, +tl}:
      {==}

def SL.vw(+hold: Bool, +dfs: B.Defs, +reqs: List<&2, Pr.Req>, +b2: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  h: MSX.RQOK(reqs) & {MSX.fst_c(reqs) == Some{B.Rec.field(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 0n)} : Maybe<&2, String>},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.want.b(o, P.mkRun(rp), C.BT(len, t), at, b2, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), reqs, fneed2)):
  match h:
    case (q, hfc):
      match q:
        case (hok2, q2):
          match q2:
            case (hrq, hl):
              +hm = mb_fc(reqs, B.Rec.field(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), 0n), hfc, f0_bytes(P.btext(len, t, at, (j - at : U32)), hby),
                f0_len(len, t, d, at, j, 268435456, W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(S.md_ok(S.MBP{LI.RTP(hold, rp)}), W.W1(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W2(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W3(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W4(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W5(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W6(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W7(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), W.W8(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)), hw))), hal, hlt, hsm))
              (LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, b2, wp, Some{reqs}, fneed2), (HX.st_eq_h(hold, fa, o, rp, len, t, d, at, rest, pd, eof, b2, wp, Some{reqs}, fneed2, dfs), (hw, (hr, (hok2, (hrq, (ao(reqs, hl), (HX.x_h(hold, rp, hx), (hm, ({==}, (hg, ({==}, (W.moved_keep(fa, cs, LI.RTP(hold, rp), LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, b2, wp, Some{reqs}, fneed2), {==}, {==}, {==}, {==}), W.kept_same(Con{LI.SXP(hold, len, t, d, at), rest}))))))))))))))

# ---------------------------------------------------------------------------
# A record written: the spec's step, then the source steps
# ---------------------------------------------------------------------------

# The spec's step on a body line (not stopped, in the body).
law body_step_g:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == True{} : Bool}
  for +hpw: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(A))) == B.Whole{} : B.Parts}
  {L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) == R.body_line(L.judge(fa, B.Line.body(Norm.line(A))), R.tick(P.specRun(rp)), o, Norm.line(A),
    B.At{1n+P.RunP.n(rp), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A))))) : R.RunSt}

def body_step_g(dfs, fa, o, rp, A, hx, hin, hpw):
  +st = P.specRun(rp)
  +l = Norm.line(A)
  +bd = B.Line.body(l)
  +fs = B.Rec.fields(bd)
  +tl = B.Text.line(A)
  +ft = B.Rec.fields(B.Line.body(tl))
  +RHS = R.body_line(L.judge(fa, bd), R.tick(st), o, l, B.At{1n+P.RunP.n(rp), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, WR.halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, dfs, o, st, tl) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), True{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
    {L.line_in(_, fa, dfs, o, R.tick(st), tl) == RHS : R.RunSt}
  %Equal.sym(B.Parts, B.Rec.parts(dfs, o, B.Line.body(tl)), B.Whole{}, hpw) :
    {L.body_in(_, fa, o, R.tick(st), tl, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(ft, 0n), B.Rec.field(ft, 1n)}, B.Rec.pos(ft)) == RHS : R.RunSt}
  %LN.line_eq(A) : {R.body_line(L.judge(fa, B.Line.body(_)), R.tick(st), o, _, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(_)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(_)))) == RHS : R.RunSt}
  %Equal.sym(Nat, R.RunSt.n(R.tick(st)), 1n+P.RunP.n(rp), Equal.trans(Nat, R.RunSt.n(R.tick(st)), 1n+R.RunSt.n(st), 1n+P.RunP.n(rp), FH.tick_n(st),
      Equal.cong(Nat, Nat, z => 1n+z, R.RunSt.n(st), P.RunP.n(rp), FH.n_spec(rp)))) :
    {R.body_line(L.judge(fa, bd), R.tick(st), o, l, B.At{_, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  {==}

# The spec's step on a line, as the record r written stands for it.
def BLX(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +A: String, +r: B.Res) -> Data:
  {R.body_line(r, R.tick(P.specRun(rp)), o, Norm.line(A), B.At{1n+P.RunP.n(rp), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A))))) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt}

# A whole line: its outcome r (judge's) stands for the step.
def blx_j(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +A: String, +r: B.Res,
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hpw: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(A))) == B.Whole{} : B.Parts},
  +hrj: {r == L.judge(fa, B.Line.body(Norm.line(A))) : B.Res}) -> BLX(fa, dfs, o, rp, A, r):
  +l = Norm.line(A)
  +fs = B.Rec.fields(B.Line.body(l))
  %Equal.sym(B.Res, r, L.judge(fa, B.Line.body(l)), hrj) : {R.body_line(_, R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt}
  Equal.sym(R.RunSt, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), R.body_line(L.judge(fa, B.Line.body(l)), R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)),
    body_step_g(dfs, fa, o, rp, A, hx, hin, hpw))


def SL.went(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +rp1: P.RunP, +rp2: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(R.body_line(r, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))))) : R.RunSt},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.Src.of(hold, C.BT(len, t), (j + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, PC.mkWin(fa, wp), None{}, False{}, dfs}}):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +bd = B.Line.body(l)
  +fs = J.pfs(bd)
  +fr = B.Rec.fields(bd)
  +E1 = {%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) :
      {R.body_line(r, _, o, l, Norm.at_of(P.RunP.n(rp1), fs), B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt};
    %Equal.sym(Nat, P.RunP.n(rp1), 1n+P.RunP.n(rp), n1) :
      {R.body_line(r, R.tick(P.specRun(rp)), o, l, B.At{_, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt};
    %Equal.sym(String, B.Rec.field(fs, 0n), B.Rec.field(fr, 0n), PF.pfs_field(bd, 0n, {==})) :
      {R.body_line(r, R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), _, B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt};
    %Equal.sym(String, B.Rec.field(fs, 1n), B.Rec.field(fr, 1n), PF.pfs_field(bd, 1n, {==})) :
      {R.body_line(r, R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), B.Rec.field(fr, 0n), _}, B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt};
    %Equal.sym(Nat, B.Rec.pos(fs), B.Rec.pos(fr), PF.pfs_pos(bd)) :
      {R.body_line(r, R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), B.Rec.field(fr, 0n), B.Rec.field(fr, 1n)}, _) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt};
    hbl : {R.body_line(r, P.specRun(rp1), o, l, Norm.at_of(P.RunP.n(rp1), fs), B.Rec.pos(fs)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt}}
  +BLs = R.body_line(r, P.specRun(rp1), o, l, Norm.at_of(P.RunP.n(rp1), fs), B.Rec.pos(fs))
  +hrun = Equal.trans(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BLs), P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32))))),
    sp2, Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), BLs, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))), E1))
  +hib = {%FH.inbody_settle(P.specRun(rp2)) : {_ == True{} : Bool};
    %Equal.sym(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BLs), sp2) : {R.RunSt.inbody(_) == True{} : Bool};
    %Equal.sym(Bool, R.RunSt.inbody(P.settle(BLs)), R.RunSt.inbody(BLs), FH.inbody_settle(BLs)) : {_ == True{} : Bool};
    %Equal.sym(Bool, R.RunSt.inbody(BLs), R.RunSt.inbody(P.specRun(rp1)), IB.ib_body_line(r, P.specRun(rp1), o, l, Norm.at_of(P.RunP.n(rp1), fs), B.Rec.pos(fs))) : {_ == True{} : Bool};
    %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp1)), P.RunP.i(rp1), WR.ib_spec(rp1)) : {_ == True{} : Bool};
    hin1 : {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool}}
  +hd = {%Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), True{}, Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
      {dfs == Bool.pick(B.Defs, _, dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32)))))) : B.Defs}; {==} :
    {dfs == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32)))))) : B.Defs}}
  HX.went_h(hold, dfs, dfs, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hs, hle, hn, hal, hlt, hinc, i2, hrun,
    W.or_l(R.RunSt.inbody(P.specRun(rp2)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hib), hx, hd)

def DW(+rp1: P.RunP, +o: B.Opts, +len: U32, +t: AT.Tree<U32>, +at: U32, +j: U32, +r: B.Res, x: NR.Run & D.Bytes) -> Type:
  &p2: P.RunP -> ({x == (P.mkRun(p2), C.BT(len, t)) : NR.Run & D.Bytes}
  & ({PR.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(r, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))))) : R.RunSt}))


def SL.same.d(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}),
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  dw: DW(rp1, o, len, t, at, j, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.same_done(o, (P.mkRun(rp1), P.RunP.n(rp1)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.same_done(P.mkRun(rp1), o, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
              SL.went(hold, dfs, B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hbl, rp1, rp2, s1, n1, hin1, i2, sp2, hnr)

def SL.same.t(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}),
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.same_done(o, NR.Run.n(NR.tick(P.mkRun(rp))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.same_done(o, NR.Run.n(_), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.same_done(o, _, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  SL.same.d(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, rp1, s1, n1, hin1, PR.run_same_done(rp1, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hsl, hfl, hal, hlt), hbig1, hk, hcb, hcl), hnr)

def SL.same(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}),
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.same_done(o, Norm.ticked(P.mkRun(rp)), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          SL.same.t(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, rp1, et, i1, s1, n1, obl1, hnr)

def SL.body.d(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +hres: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  dw: DW(rp1, o, len, t, at, j, r, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body_done(r, o, (P.mkRun(rp1), P.RunP.n(rp1)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match dw:
    case (+rp2, q):
      match q:
        case (edn, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.body_line(r, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), C.BT(len, t), at, FH.KK(at, j)), (P.mkRun(rp2), C.BT(len, t)), edn) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, _, (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
              SL.went(hold, dfs, r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hbl, rp1, rp2, s1, n1, hin1, i2, sp2, hnr)

def SL.body.t(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hfit: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +hres: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body_done(r, o, NR.Run.n(NR.tick(P.mkRun(rp))), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
  +hfl = Equal.sym(Nat, n(j), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  +hk = FH.k_le_z(len, t, d, at, j, 268435456, 268435457, hok, hal, hlt, hsm_le(268435456, (j - at : U32), hsm), {==})
  +hcb = f0_bytes(P.btext(len, t, at, (j - at : U32)), hby)
  +hcl = f0_len(len, t, d, at, j, 268435456, hok, hal, hlt, hsm)
  +hfit1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {Norm.res_fits(r, l, (1073741824 - _ : U32)) == True{} : Bool}; hfit : {Norm.res_fits(r, l, (1073741824 - P.RunP.obl(rp1) : U32)) == True{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.body_done(r, o, NR.Run.n(_), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.body_done(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  SL.body.d(hold, dfs, r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, hres, rp1, s1, n1, hin1, PR.run_body_line(rp1, r, o, l, Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), len, t, d, at, FH.KK(at, j), i1, hin1, hx1, hok, FH.k_fit(len, t, d, at, j, hok, hal, hlt), FH.k_text(len, t, d, at, j, hok, hsl, hfl, hal, hlt), hbig1, hk, hfit1, hres, hcb, hcl), hnr)

def SL.body(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hfit: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +hres: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body_done(r, o, Norm.ticked(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          SL.body.t(hold, dfs, r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hfit, hbl, hres, rp1, et, i1, s1, n1, obl1, hnr)

# ---------------------------------------------------------------------------
# The verdict's cases
# ---------------------------------------------------------------------------

law oblen_eq:
  for +rp: P.RunP
  {Norm.Run.oblen(P.mkRun(rp)) == (P.mkRun(rp), P.RunP.obl(rp)) : NR.Run & U32}

def oblen_eq(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def SL.fit(+hold: Bool, +dfs: B.Defs, +fits: Bool, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +hres: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +ef: {Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)) == fits : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.fits(fits, r, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match fits:
    case False{}:
      HX.tostr_h(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, back, False{}, hw, hr, hg, hx)
    case True{}:
      SL.body(hold, dfs, r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, ef, hbl, hres, PR.run_tick(rp, hi), hnr)

def SL.vr(+hold: Bool, +dfs: B.Defs, +r: B.Res, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hbl: BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r),
  +hres: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.body.res(r, o, Norm.Run.oblen(P.mkRun(rp)), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  %Equal.sym(NR.Run & U32, Norm.Run.oblen(P.mkRun(rp)), (P.mkRun(rp), P.RunP.obl(rp)), oblen_eq(rp)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.body.res(r, o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp)))
  SL.fit(hold, dfs, Norm.res_fits(r, Norm.line(P.btext(len, t, at, (j - at : U32))), (1073741824 - P.RunP.obl(rp) : U32)), r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, hres, {==}, hnr)

def SL.v(+hold: Bool, +dfs: B.Defs, +v: MSX.VdP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hpw: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Whole{} : B.Parts},
  hk: MSX.vdOK(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, MSX.mkVd(fa, wp, v))):
  match v:
    case MSX.VRP{+r}:
      +hj = {hk : {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res}}
      +hres = {%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hj) : {E.is_bytes(P.res_text(_)) == True{} : Bool}; judge_bytes(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, body_bytes(P.btext(len, t, at, (j - at : U32)), hby)) : {E.is_bytes(P.res_text(r)) == True{} : Bool}}
      SL.vr(hold, dfs, r, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, blx_j(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), r, hx, hin, hpw, hj), hres, hnr)
    case MSX.VSP{}:
      SL.same(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, blx_j(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}, hx, hin, hpw, hk), PR.run_tick(rp, hi), hnr)
    case MSX.VWP{+reqs, +b2}:
      SL.vw(hold, dfs, reqs, b2, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hk, hnr)

def SL.vd(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hpw: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Whole{} : B.Parts},
  h: MSX.VdG(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))))):
  match h:
    case (+v, q):
      match q:
        case (ev, hk):
          %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), ev) :
            S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, _))
          SL.v(hold, dfs, v, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hpw, hk, hnr)


# ---------------------------------------------------------------------------
# A line -m refuses (code c): its outcome when that stops the run, else the
# problem c (LAWS.bend's unsplit_in)
# ---------------------------------------------------------------------------

law stops_eq:
  for +r: B.Res
  for +s: Bool
  {Norm.stops(r, s) == L.stops(r, s) : Bool}

def stops_eq(r, s):
  match r:
    case B.Res{B.Broken{}, +k, +x, +y}:
      {==}
    case B.Res{B.NoContig{}, +k, +x, +y}:
      {==}
    case B.Res{B.Problem{+c}, +k, +x, +y}:
      {==}
    case B.Res{B.Skipped{}, +k, +x, +y}:
      {==}
    case B.Res{B.Normalized{}, +k, +x, +y}:
      {==}

def bl_pick(s: Bool, +r: B.Res, +c: B.Code, +k: Nat, +b: String, +st: R.RunSt, o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat) ->
  {R.body_line(Bool.pick(B.Res, s, r, B.Res{B.Problem{c}, k, b, False{}}), st, o, l, at, inpos) ==
    Bool.pick(R.RunSt, s, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos)) : R.RunSt}:
  match s:
    case True{}:
      {==}
    case False{}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              {==}
            case False{}:
              {==}

# The spec's step on a line -m refuses.
law body_step_u:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +c: B.Code
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == True{} : Bool}
  for +hpu: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(A))) == B.Unsplit{c} : B.Parts}
  {L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) == L.unsplit_in(L.judge(fa, B.Line.body(Norm.line(A))), c, o, R.tick(P.specRun(rp)), Norm.line(A),
    B.At{1n+P.RunP.n(rp), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A))))) : R.RunSt}

def body_step_u(dfs, fa, o, rp, A, c, hx, hin, hpu):
  +st = P.specRun(rp)
  +l = Norm.line(A)
  +bd = B.Line.body(l)
  +fs = B.Rec.fields(bd)
  +tl = B.Text.line(A)
  +ft = B.Rec.fields(B.Line.body(tl))
  +RHS = L.unsplit_in(L.judge(fa, bd), c, o, R.tick(st), l, B.At{1n+P.RunP.n(rp), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs))
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, WR.halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, dfs, o, st, tl) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), True{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
    {L.line_in(_, fa, dfs, o, R.tick(st), tl) == RHS : R.RunSt}
  %Equal.sym(B.Parts, B.Rec.parts(dfs, o, B.Line.body(tl)), B.Unsplit{c}, hpu) :
    {L.body_in(_, fa, o, R.tick(st), tl, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(ft, 0n), B.Rec.field(ft, 1n)}, B.Rec.pos(ft)) == RHS : R.RunSt}
  %LN.line_eq(A) : {L.unsplit_in(L.judge(fa, B.Line.body(_)), c, o, R.tick(st), _, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(_)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(_)))) == RHS : R.RunSt}
  %Equal.sym(Nat, R.RunSt.n(R.tick(st)), 1n+P.RunP.n(rp), Equal.trans(Nat, R.RunSt.n(R.tick(st)), 1n+R.RunSt.n(st), 1n+P.RunP.n(rp), FH.tick_n(st),
      Equal.cong(Nat, Nat, z => 1n+z, R.RunSt.n(st), P.RunP.n(rp), FH.n_spec(rp)))) :
    {L.unsplit_in(L.judge(fa, bd), c, o, R.tick(st), l, B.At{_, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  {==}

# The record the machine writes for a refused line stands for the step.
def blx_u(+fa: List<&2, B.Contig>, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +A: String, +c: B.Code,
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hpu: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(A))) == B.Unsplit{c} : B.Parts}) ->
  BLX(fa, dfs, o, rp, A, Norm.unsplit.res(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(A))), B.Line.body(Norm.line(A)), L.judge(fa, B.Line.body(Norm.line(A))))):
  +l = Norm.line(A)
  +bd = B.Line.body(l)
  +fs = B.Rec.fields(bd)
  +so = R.Opts.strict(o)
  +jr = L.judge(fa, bd)
  +st1 = R.tick(P.specRun(rp))
  +at1 = {B.At{1n+P.RunP.n(rp), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
  +X = R.body_line(jr, st1, o, l, at1, B.Rec.pos(fs))
  +Y = R.problem_line(so, st1, R.Opts.w(o), c, l, at1, B.Rec.pos(fs))
  Equal.trans(R.RunSt, R.body_line(Norm.unsplit.res(c, so, J.pfs(bd), bd, jr), st1, o, l, at1, B.Rec.pos(fs)), Bool.pick(R.RunSt, Norm.stops(jr, so), X, Y), L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)),
    bl_pick(Norm.stops(jr, so), jr, c, B.Rec.pos(J.pfs(bd)), bd, st1, o, l, at1, B.Rec.pos(fs)),
    {(%Equal.sym(Bool, Norm.stops(jr, so), L.stops(jr, so), stops_eq(jr, so)) : {Bool.pick(R.RunSt, _, X, Y) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt};
      Equal.sym(R.RunSt, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), L.unsplit_in(jr, c, o, st1, l, at1, B.Rec.pos(fs)), body_step_u(dfs, fa, o, rp, A, c, hx, hin, hpu))) :
      {Bool.pick(R.RunSt, Norm.stops(jr, so), X, Y) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt}})

def hres_u(s: Bool, +r: B.Res, +c: B.Code, +k: Nat, +b: String,
  +hj: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  +hb: {E.is_bytes(b) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(Bool.pick(B.Res, s, r, B.Res{B.Problem{c}, k, b, False{}}))) == True{} : Bool}:
  match s:
    case True{}:
      hj
    case False{}:
      hb

# The verdict on a refused line (norm_seq.bend's vd.unsplit), pictured.
def vdU(+c: B.Code, +strict: Bool, +body: String, v: MSX.VdP) -> MSX.VdP:
  match v:
    case MSX.VRP{+r}:
      MSX.VRP{Norm.unsplit.res(c, strict, J.pfs(body), body, r)}
    case MSX.VSP{}:
      MSX.VRP{B.Res{B.Problem{c}, B.Rec.pos(J.pfs(body)), body, False{}}}
    case MSX.VWP{+reqs, +b}:
      MSX.VWP{reqs, b}

def vdu_eq(+fa: List<&2, B.Contig>, +wp: PC.WP, +c: B.Code, +strict: Bool, +body: String, v: MSX.VdP) ->
  {Norm.vd.unsplit(c, strict, J.pfs(body), body, MSX.mkVd(fa, wp, v)) == MSX.mkVd(fa, wp, vdU(c, strict, body, v)) : Norm.Vd}:
  match v:
    case MSX.VRP{+r}:
      {==}
    case MSX.VSP{}:
      {==}
    case MSX.VWP{+reqs, +b}:
      {==}

def SL.vu(+hold: Bool, +dfs: B.Defs, +c: B.Code, +v: MSX.VdP, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hpu: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Unsplit{c} : B.Parts},
  hk: MSX.vdOK(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, MSX.mkVd(fa, wp, vdU(c, R.Opts.strict(o), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)))):
  match v:
    case MSX.VRP{+r}:
      +hj = {hk : {r == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res}}
      +so = R.Opts.strict(o)
      +ru = Norm.unsplit.res(c, so, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), r)
      +hbl = {(%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hj) : BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), Norm.unsplit.res(c, so, J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), _)); blx_u(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), c, hx, hin, hpu)) : BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), ru)}
      +hjb = judge_bytes(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, body_bytes(P.btext(len, t, at, (j - at : U32)), hby))
      +hres = {(%Equal.sym(B.Res, r, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hj) : {E.is_bytes(P.res_text(Bool.pick(B.Res, Norm.stops(_, so), _, B.Res{B.Problem{c}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}}))) == True{} : Bool};
          hres_u(Norm.stops(L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), so), L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), c, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hjb, body_bytes(P.btext(len, t, at, (j - at : U32)), hby))) : {E.is_bytes(P.res_text(ru)) == True{} : Bool}}
      SL.vr(hold, dfs, ru, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, hres, hnr)
    case MSX.VSP{}:
      +nr = {B.Res{B.Normalized{}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}} : B.Res}
      +hj = {hk : {nr == L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) : B.Res}}
      +ru = {B.Res{B.Problem{c}, B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), False{}} : B.Res}
      +hbl = {(%Equal.sym(B.Res, nr, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hj) : BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), Norm.unsplit.res(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), _)); blx_u(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), c, hx, hin, hpu)) : BLX(fa, dfs, o, rp, P.btext(len, t, at, (j - at : U32)), ru)}
      SL.vr(hold, dfs, ru, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hbl, body_bytes(P.btext(len, t, at, (j - at : U32)), hby), hnr)
    case MSX.VWP{+reqs, +b2}:
      SL.vw(hold, dfs, reqs, b2, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hk, hnr)

def SL.vdu(+hold: Bool, +dfs: B.Defs, +c: B.Code, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hpu: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Unsplit{c} : B.Parts},
  h: MSX.VdG(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back,
      Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))))))):
  match h:
    case (+v, q):
      match q:
        case (ev, hk):
          %Equal.sym(Norm.Vd, Norm.verdict(back, PC.mkWin(fa, wp), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), MSX.mkVd(fa, wp, v), ev) :
            S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), _)))
          %Equal.sym(Norm.Vd, Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), MSX.mkVd(fa, wp, v)), MSX.mkVd(fa, wp, vdU(c, R.Opts.strict(o), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)), vdu_eq(fa, wp, c, R.Opts.strict(o), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), v)) :
            S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.slow.vd(o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, fneed2, back, _))
          SL.vu(hold, dfs, c, v, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hpu, hk, hnr)

# A body line on the slow path (proof_b_adv_dec.bend's dec.slow).
# Without -m every line is whole.
law nosplit_whole:
  for +dfs: B.Defs
  for +o: B.Opts
  for +b: String
  for +h: {R.Opts.split(o) == False{} : Bool}
  {B.Rec.parts(dfs, o, b) == B.Whole{} : B.Parts}

def nosplit_whole(dfs, o, b, h):
  match o:
    case B.Opts{+s, +w, +sp, +o0, +a}:
      %Equal.sym(Bool, sp, False{}, h) : {B.Rec.parts.if(Bool.and(Bool.and(_, Bool.not(B.Rec.malformed(B.Rec.fields(b)))), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(B.Rec.fields(b))))), B.Text.has_cr(b), dfs, o0, B.Rec.fields(b)) == B.Whole{} : B.Parts}
      {==}

def tl_eq(+A: String, +x: B.Parts, +dfs: B.Defs, +o: B.Opts, +h: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(A))) == x : B.Parts}) ->
  {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(A))) == x : B.Parts}:
  %LN.line_eq(A) : {B.Rec.parts(dfs, o, B.Line.body(_)) == x : B.Parts}
  h

def bb_eq(+A: String, +h: {E.is_bytes(B.Line.body(Norm.line(A))) == True{} : Bool}) -> {E.is_bytes(B.Line.body(B.Text.line(A))) == True{} : Bool}:
  %LN.line_eq(A) : {E.is_bytes(B.Line.body(_)) == True{} : Bool}
  h

# A split line's records go in front (from the input's own lines; a record
# of a split line has one ALT and is not split again).
def slow.inj(hold: Bool, +dfs: B.Defs, +ps: List<&2, String>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hp: {B.Rec.parts(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32))))) == B.Pieces{ps} : B.Parts},
  tk: WR.TKW(rp)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.inject.r(o, P.mkRun(rp), C.BT(len, t), j, ps, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp))):
  match hold:
    case True{}:
      +p = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
      +h8 = W.c9_8(W.W0(fa, p), W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
      +AB = E.all_bytes(S.opts_args(o))
      +RF = S.recs_first(Con{P.SPP{len, t, d, at}, rest})
      +RR = S.recs_run(S.MBP{LI.RTP(True{}, rp)}, Con{P.SPP{len, t, d, at}, rest})
      +hrf = W.and_r(AB, RF, W.and_l(Bool.and(AB, RF), RR, h8))
      Empty.absurd(S.AdvG(fa, T, cs, O, N, p, Norm.inject.r(o, P.mkRun(rp), C.BT(len, t), j, ps, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32)))), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, True{}}, PC.mkWin(fa, wp))),
        IR.sp_abs(dfs, o, len, t, d, at, j, rest, ps, hrf, hp, (hs, (hn, (hle, hby)))))
    case False{}:
      (+rp1, q) = tk
      (et, q2) = q
      (i1, q3) = q2
      (s1, q4) = q3
      %Equal.sym(B.Line, Norm.line(P.btext(len, t, at, (j - at : U32))), B.Text.line(P.btext(len, t, at, (j - at : U32))), LN.line_eq(P.btext(len, t, at, (j - at : U32)))) :
        S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.inject.r(o, P.mkRun(rp), C.BT(len, t), j, ps, B.Line.term(_), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp)))
      IR.went_injr(dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, ps, hw, hr, hs, hn, hle, hal, hlt, hsl, hinc, hx, hin, et, i1, s1, hp,
        bb_eq(P.btext(len, t, at, (j - at : U32)), body_bytes(P.btext(len, t, at, (j - at : U32)), hby)))

def slow.pk(pt: B.Parts, +hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hv: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hpt: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == pt : B.Parts},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.slow.parts.k(pt, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), PC.mkWin(fa, wp), fneed2)):
  match pt:
    case B.Whole{}:
      SL.vd(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, tl_eq(P.btext(len, t, at, (j - at : U32)), B.Whole{}, dfs, o, hpt), MSX.vd_ok(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, hv), hnr)
    case B.Pieces{+ps}:
      slow.inj(hold, dfs, ps, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hsl, tl_eq(P.btext(len, t, at, (j - at : U32)), B.Pieces{ps}, dfs, o, hpt), PR.run_tick(rp, hi))
    case B.Unsplit{+c}:
      SL.vdu(hold, dfs, c, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, tl_eq(P.btext(len, t, at, (j - at : U32)), B.Unsplit{c}, dfs, o, hpt), MSX.vd_ok(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, hv), hnr)

def slow.sp(sp: Bool, +hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hsl: {U32.is_le(at, len) == True{} : Bool},
  +hv: {PC.wp_ok(fa, wp) == True{} : Bool},
  +hsp: {R.Opts.split(o) == sp : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.slow.split(sp, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed2)):
  match sp:
    case False{}:
      SL.vd(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, nosplit_whole(dfs, o, B.Line.body(B.Text.line(P.btext(len, t, at, (j - at : U32)))), hsp), MSX.vd_ok(fa, wp, back, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32)))), hb, hv), hnr)
    case True{}:
      slow.pk(B.Rec.parts(dfs, o, B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hv, {==}, hnr)

def slow(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.slow(back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, PC.mkWin(fa, wp), fneed2)):
  +p = LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{LI.RTP(hold, rp)})
  +hso = LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hsl = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hv = W.c9_6(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  slow.sp(R.Opts.split(o), hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hok, hsl, hv, {==}, hnr)

