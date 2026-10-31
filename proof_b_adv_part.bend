import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_lines.bend as LN
import ./proof_b_lines_str.bend as LSS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_str.bend as TS
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as NN

# adv_ok when a byte source holds no LF from at (norm.bend part.len): its
# bytes go to the line end and the source is dropped. Either that text is
# empty (another source follows, whose text starts on a line, or the input
# has ended), or it is the last source before the end and pend was empty.
# Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

law s_app_nil:
  for +s: String
  {String.append(s, "") == s : String}

def s_app_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      %Equal.sym(String, String.append(r, ""), r, s_app_nil(r)) : {SCon{h, _} == SCon{h, r} : String}
      {==}

def empty_eq(+s: String, +h: {String.is_empty(s) == True{} : Bool}) -> {s == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      Empty.absurd({SCon{c, r} == "" : String}, W.ft(h))

def srcs_tl(+rest: List<&2, P.SrcP>, +sp: P.SrcP, +h: {S.srcs_ok(Con{sp, rest}) == True{} : Bool}) ->
  {S.srcs_ok(rest) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      W.and_r(Bool.and(P.src_ok(sp), S.ends_lf(P.srctext(sp))), S.srcs_ok(Con{a, b}), h)

law meas_drop:
  for +x: Nat
  for +m: Nat
  {Nat.is_lt(Nat.add(m, 1n), Nat.add(Nat.add(Nat.add(x, 2n), m), 1n)) == True{} : Bool}

def meas_drop(x, m):
  +K = Nat.add(x, 2n)
  +lt1 = {%Equal.sym(Bool, Nat.is_lt(m, 1n+m), Nat.is_le(m, m), NN.lt_succ_iff(m, m)) : {_ == True{} : Bool}; NN.le_refl(m) : {Nat.is_lt(m, Nat.add(1n, m)) == True{} : Bool}}
  +le1 = NN.le_add_mono_r(m, 1n, K, NN.le_trans(1n, 2n, K, {==}, NN.le_add_l(2n, x)))
  NN.lt_add_mono_r(1n, m, Nat.add(K, m), NN.lt_le_trans(m, Nat.add(1n, m), Nat.add(K, m), lt1, le1))

# The dropped text is empty.
def DP.e(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String},
  +hE: {String.is_empty(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), P.mkPd(pd2), eof, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}}):
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hS = empty_eq(P.srctext(P.SBP{len, t, d, at}), hE)
  +hA = Equal.trans(String, P.btext(len, t, at, (len - at : U32)), P.srctext(P.SBP{len, t, d, at}), "", Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa), hS)
  +q = {S.StP{o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed2, dfs} : S.StP}
  +h3 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {P.nolf(_) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {P.nolf(String.append(P.pdtext(pd), _)) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), s_app_nil(P.pdtext(pd))) : {P.nolf(_) == True{} : Bool};
    W.c9_3(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {P.nolf(P.pdtext(pd2)) == True{} : Bool}}
  +hpe = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.is_empty(_) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {String.is_empty(String.append(P.pdtext(pd), _)) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), s_app_nil(P.pdtext(pd))) : {String.is_empty(_) == True{} : Bool};
    W.c9_4(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {String.is_empty(P.pdtext(pd2)) == True{} : Bool}}
  +h5 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(_), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(String.append(P.pdtext(pd), _)), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), s_app_nil(P.pdtext(pd))) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(_), S.ends_lf(P.srcstext(rest)))) == True{} : Bool};
    %hS : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(_, P.srcstext(rest))))) == True{} : Bool};
    W.c9_5(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw) : {Bool.or(Bool.not(eof), Bool.and(String.is_empty(P.pdtext(pd2)), S.ends_lf(P.srcstext(rest)))) == True{} : Bool}}
  +h8 = W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  +hnr = W.W8_nr(fa, o, S.MBP{rp}, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, dfs, h8)
  +eqr = W.recs_nr(rest, hnr)
  +eqi = {%Equal.sym(List<&2, P.SrcP>, S.plain(rest), rest, W.plain_nr(rest, hnr)) : {String.append(P.srcstext(_), String.append(P.pdtext(pd2), S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {String.append(P.srcstext(rest), String.append(String.append(P.pdtext(pd), _), S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), s_app_nil(P.pdtext(pd))) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), "", hS) : {String.append(P.srcstext(rest), String.append(P.pdtext(pd), S.concat_if(eof, cs))) == String.append(String.append(_, P.srcstext(rest)), String.append(P.pdtext(pd), S.concat_if(eof, cs))) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  (q, ({==}, (W.c9_mk(m0, W.W1(fa, q), W.W2(fa, q), W.W3(fa, q), W.W4(fa, q), W.W5(fa, q), W.W6(fa, p), W.W7(fa, p), W.W8(fa, q),
      W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), srcs_tl(rest, P.SBP{len, t, d, at}, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)), hpd2, h3, W.or_r(S.src_empty(rest), String.is_empty(P.pdtext(pd2)), hpe), h5, W.c9_6(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw),
      W.W8_tl(fa, o, S.MBP{rp}, S.MBP{rp}, len, t, d, at, rest, pd, pd2, eof, eof, back, back, wp, wp, asked, None{}, fneed, fneed2, dfs, dfs, h8)),
    (Equal.trans(R.Report, S.report(fa, cs, O, N, q), S.report(fa, cs, O, N, p), T,
      W.rep_keep_mb(fa, cs, O, N, o, rp, dfs, q, p, {==}, {==}, {==}, {==}, eqi, eqr), hr),
    (W.less_lt(q, p, meas_drop(n((len - at : U32)), S.msrc(rest))), ({==}, ({==}, (hg, ({==}, (W.moved_keep(fa, cs, rp, p, q, eqi, eqr, {==}, {==}), hk => Empty.absurd((&at2: U32 -> {S.plain(rest) == Con{P.SBP{len, t, d, at2}, rest} : List<&2, P.SrcP>}), NN.true_ne_false(Equal.trans(Bool, True{}, P.nolf(P.srctext(P.SBP{len, t, d, at})), False{}, Equal.sym(Bool, P.nolf(P.srctext(P.SBP{len, t, d, at})), True{}, hn), hk)))))))))))))

# The last source, before the end: pend was empty and takes its text.
def DP.nn(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pd2), False{}, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}}):
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hP = empty_eq(P.pdtext(pd), W.c9_4(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +q = {S.StP{o, S.MBP{rp}, Nil{}, pd2, False{}, back, wp, None{}, fneed2, dfs} : S.StP}
  +hnA = {%hsa : {P.nolf(_) == True{} : Bool}; hn : {P.nolf(P.btext(len, t, at, (len - at : U32))) == True{} : Bool}}
  +h3 = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {P.nolf(_) == True{} : Bool};
    LSS.nolf_app(P.pdtext(pd), P.btext(len, t, at, (len - at : U32)), W.c9_3(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), hnA) : {P.nolf(P.pdtext(pd2)) == True{} : Bool}}
  +Y0 = S.concat_if(False{}, cs)
  +eqi = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(_, Y0) == S.intext(p, cs) : String};
    %Equal.sym(String, P.pdtext(pd), "", hP) : {String.append(String.append(_, P.btext(len, t, at, (len - at : U32))), Y0) == String.append(String.append(P.srctext(P.SBP{len, t, d, at}), ""), String.append(_, Y0)) : String};
    %Equal.sym(String, String.append(P.srctext(P.SBP{len, t, d, at}), ""), P.srctext(P.SBP{len, t, d, at}), s_app_nil(P.srctext(P.SBP{len, t, d, at}))) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  (q, ({==}, (W.c9_mk(m0, W.W1(fa, q), W.W2(fa, q), W.W3(fa, q), W.W4(fa, q), W.W5(fa, q), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p),
      W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), {==}, hpd2, h3, {==}, {==}, W.c9_6(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_7(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)),
    (Equal.trans(R.Report, S.report(fa, cs, O, N, q), S.report(fa, cs, O, N, p), T,
      W.rep_keep_mb(fa, cs, O, N, o, rp, dfs, q, p, {==}, {==}, {==}, {==}, eqi, {==}), hr),
    (W.less_lt(q, p, meas_drop(n((len - at : U32)), 0n)), ({==}, ({==}, (hg, ({==}, (W.moved_keep(fa, cs, rp, p, q, eqi, {==}, {==}, {==}), hk => Empty.absurd((&at2: U32 -> {Nil{} == Con{P.SBP{len, t, d, at2}, Nil{}} : List<&2, P.SrcP>}), NN.true_ne_false(Equal.trans(Bool, True{}, P.nolf(P.srctext(P.SBP{len, t, d, at})), False{}, Equal.sym(Bool, P.nolf(P.srctext(P.SBP{len, t, d, at})), True{}, hn), hk)))))))))))))

def DP.n(+dfs: B.Defs, +eof: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pd2), eof, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}}):
  match eof:
    case False{}:
      DP.nn(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)
    case True{}:
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, True{}, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hl0 = W.and_r(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(P.srctext(P.SBP{len, t, d, at}), "")), W.c9_5(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
      +hlS = {%s_app_nil(P.srctext(P.SBP{len, t, d, at})) : {S.ends_lf(_) == True{} : Bool}; hl0 : {S.ends_lf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}}
      DP.e(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, Nil{}, pd, True{}, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx, TS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))

def DP.r(+dfs: B.Defs, +rest: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +hpd2: {P.pd_ok(pd2) == True{} : Bool},
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), P.mkPd(pd2), eof, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}}):
  match rest:
    case Nil{}:
      DP.n(dfs, eof, fa, T, cs, O, N, o, rp, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)
    case Con{+sp2, +r2}:
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Con{sp2, r2}, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hlS = W.and_r(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at})), W.and_l(Bool.and(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at}))), S.srcs_ok(Con{sp2, r2}), W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)))
      DP.e(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, Con{sp2, r2}, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx, TS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))

def PAW(+pd: P.PdP, +len: U32, +t: AT.Tree<U32>, +at: U32) -> Type:
  &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)) == P.mkPd(pp2) : Norm.Pd}
  & ({P.pd_ok(pp2) == True{} : Bool}
  & {P.pdtext(pp2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}))

def DP.pa(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  pa: PAW(pd, len, t, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), eof, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}}):
  match pa:
    case (+pd2, q):
      match q:
        case (eadd, q2):
          match q2:
            case (hpd2, htx):
              %Equal.sym(Norm.Pd, Norm.pend.add(P.mkPd(pd), C.BT(len, t), at, (len - at : U32)), P.mkPd(pd2), eadd) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp)}, P.mkSrcs(rest), _, eof, back, PC.mkWin(fa, wp), None{}, fneed2, dfs}})
              DP.r(dfs, rest, fa, T, cs, O, N, o, rp, len, t, d, at, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, pd2, hpd2, htx)

def SNW(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32) -> Type:
  {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool} & {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String}

def DP.sn(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  sn: SNW(len, t, d, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, (C.BT(len, t), len), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed2)):
  match sn:
    case (hn, hsa):
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hfit = {%Equal.sym(Nat, n((len - at : U32)), Nat.sub(n(len), n(at)), LP.sub_u(len, at, LI.u2n(at, len, hs))) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool};
        %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(len), n(at))), n(len), NN.le_sub_add(n(at), n(len), LI.u2n(at, len, hs))) : {Nat.is_le(_, n(len)) == True{} : Bool};
        NN.le_refl(n(len)) : {Nat.is_le(Nat.add(n(at), n((len - at : U32))), n(len)) == True{} : Bool}}
      DP.pa(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hn, hsa, LN.pend_add(pd, len, t, d, at, (len - at : U32), W.c9_2(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw), hok, hfit))

# The byte source holds no LF from at (proof_b_adv_dec.bend's dec.part).
def part(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hjf: {n(len) == D.first(D.view(C.BT(len, t)), n(at), n(len), 10) : Nat}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, BY.len(C.BT(len, t)), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}, PC.mkWin(fa, wp), fneed2)):
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hso = LI.srcs_head(rest, len, t, d, at, W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  DP.sn(dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hok, hs, LN.src_nolf(len, t, d, at, hok, hs, Equal.sym(Nat, n(len), D.first(D.view(C.BT(len, t)), n(at), n(len), 10), hjf)))

# ---------------------------------------------------------------------------
# The text still to come is the same (for the budget's c.dec)
# ---------------------------------------------------------------------------

def DP.te(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String},
  +hE: {String.is_empty(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}) ->
  {S.intext(S.StP{o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed2, dfs}, cs) == S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs) : String}:
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +hS = empty_eq(P.srctext(P.SBP{len, t, d, at}), hE)
  +hA = Equal.trans(String, P.btext(len, t, at, (len - at : U32)), P.srctext(P.SBP{len, t, d, at}), "", Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa), hS)
  +q = {S.StP{o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed2, dfs} : S.StP}
  +m0 = S.md_ok(S.MBP{rp})
  +h8 = W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
  +hnr = W.W8_nr(fa, o, S.MBP{rp}, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, dfs, h8)
  +eqi = {%Equal.sym(List<&2, P.SrcP>, S.plain(rest), rest, W.plain_nr(rest, hnr)) : {String.append(P.srcstext(_), String.append(P.pdtext(pd2), S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.btext(len, t, at, (len - at : U32)), "", hA) : {String.append(P.srcstext(rest), String.append(String.append(P.pdtext(pd), _), S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, String.append(P.pdtext(pd), ""), P.pdtext(pd), s_app_nil(P.pdtext(pd))) : {String.append(P.srcstext(rest), String.append(_, S.concat_if(eof, cs))) == S.intext(p, cs) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), "", hS) : {String.append(P.srcstext(rest), String.append(P.pdtext(pd), S.concat_if(eof, cs))) == String.append(String.append(_, P.srcstext(rest)), String.append(P.pdtext(pd), S.concat_if(eof, cs))) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  eqi

def DP.tn(+dfs: B.Defs, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  {S.intext(S.StP{o, S.MBP{rp}, Nil{}, pd2, False{}, back, wp, None{}, fneed2, dfs}, cs) == S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed), cs) : String}:
  +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, False{}, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{rp})
  +hP = empty_eq(P.pdtext(pd), W.c9_4(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +q = {S.StP{o, S.MBP{rp}, Nil{}, pd2, False{}, back, wp, None{}, fneed2, dfs} : S.StP}
  +Y0 = S.concat_if(False{}, cs)
  +eqi = {%Equal.sym(String, P.pdtext(pd2), String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))), htx) : {String.append(_, Y0) == S.intext(p, cs) : String};
    %Equal.sym(String, P.pdtext(pd), "", hP) : {String.append(String.append(_, P.btext(len, t, at, (len - at : U32))), Y0) == String.append(String.append(P.srctext(P.SBP{len, t, d, at}), ""), String.append(_, Y0)) : String};
    %Equal.sym(String, String.append(P.srctext(P.SBP{len, t, d, at}), ""), P.srctext(P.SBP{len, t, d, at}), s_app_nil(P.srctext(P.SBP{len, t, d, at}))) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    %Equal.sym(String, P.srctext(P.SBP{len, t, d, at}), P.btext(len, t, at, (len - at : U32)), hsa) : {String.append(P.btext(len, t, at, (len - at : U32)), Y0) == String.append(_, Y0) : String};
    {==} : {S.intext(q, cs) == S.intext(p, cs) : String}}
  eqi

def DP.tq.n(+dfs: B.Defs, +eof: Bool, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  {S.intext(S.StP{o, S.MBP{rp}, Nil{}, pd2, eof, back, wp, None{}, fneed2, dfs}, cs) == S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, eof, back, wp, asked, fneed), cs) : String}:
  match eof:
    case False{}:
      DP.tn(dfs, fa, cs, o, rp, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hn, hsa, pd2, htx)
    case True{}:
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Nil{}, pd, True{}, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hl0 = W.and_r(String.is_empty(P.pdtext(pd)), S.ends_lf(String.append(P.srctext(P.SBP{len, t, d, at}), "")), W.c9_5(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
      +hlS = {%s_app_nil(P.srctext(P.SBP{len, t, d, at})) : {S.ends_lf(_) == True{} : Bool}; hl0 : {S.ends_lf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}}
      DP.te(dfs, fa, cs, o, rp, len, t, d, at, Nil{}, pd, True{}, back, wp, asked, fneed, fneed2, hw, hn, hsa, pd2, htx, TS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))

# The source's text from at moves to the line end: the text to come is kept.
def DP.tq(+dfs: B.Defs, +rest: List<&2, P.SrcP>, +fa: List<&2, B.Contig>, +cs: List<&2, String>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hn: {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool},
  +hsa: {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String},
  +pd2: P.PdP,
  +htx: {P.pdtext(pd2) == String.append(P.pdtext(pd), P.btext(len, t, at, (len - at : U32))) : String}) ->
  {S.intext(S.StP{o, S.MBP{rp}, rest, pd2, eof, back, wp, None{}, fneed2, dfs}, cs) == S.intext(LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), cs) : String}:
  match rest:
    case Nil{}:
      DP.tq.n(dfs, eof, fa, cs, o, rp, len, t, d, at, pd, back, wp, asked, fneed, fneed2, hw, hn, hsa, pd2, htx)
    case Con{+sp2, +r2}:
      +p = LI.PPs(False{}, dfs, o, rp, len, t, d, at, Con{sp2, r2}, pd, eof, back, wp, asked, fneed)
      +m0 = S.md_ok(S.MBP{rp})
      +hlS = W.and_r(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at})), W.and_l(Bool.and(P.src_ok(P.SBP{len, t, d, at}), S.ends_lf(P.srctext(P.SBP{len, t, d, at}))), S.srcs_ok(Con{sp2, r2}), W.c9_1(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)))
      DP.te(dfs, fa, cs, o, rp, len, t, d, at, Con{sp2, r2}, pd, eof, back, wp, asked, fneed, fneed2, hw, hn, hsa, pd2, htx, TS.nolf_lf(P.srctext(P.SBP{len, t, d, at}), hn, hlS))
