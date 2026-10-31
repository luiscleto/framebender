import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./bytes_enc.bend as E
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PRD
import ./proof_b_run_inv.bend as PI
import ./proof_b_enc.bend as ENC
import ./proof_b_simdefs.bend as S
import ./proof_b_frame.bend as FRM
import ./proof_b_drive_out.bend as DO
import ./proof_base.bend as PB
import ./proof_e_defs.bend as SD
import ./proof_e_seg.bend as SG
import ./proof_e_merge.bend as MG
import ./proof_e_wrap_spec.bend as SP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Helpers for proof_e_wrap.bend (area E1): the merge of a clean piece, on
# the spec: the merged run, with the true run's whole buffer handed out
# before it, stands for the true run over the piece's lines (areas B and C).

# The true run's output buffer reads as its text.
law ob_out:
  for +rp: P.RunP
  for +hi: {PRD.RunInv(rp) == True{} : Bool}
  {E.out(C.BT(P.RunP.obl(rp), MG.RunP.obt(rp))) == Some{P.obtext(rp)} : Maybe<&2, String>}

def ob_out(rp, hi):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +d = PRD.tdepth(obt)
      Equal.trans(Maybe<&2, String>, E.out(C.BT(obl, obt)), Some{E.chars(D.view(C.BT(obl, obt)))}, Some{NR.chars(D.view(C.BT(obl, obt)))},
        ENC.out_ok(obl, obt, d, hok, C.ok_d(obl, obt, d, hok)),
        Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(obl, obt))), NR.chars(D.view(C.BT(obl, obt))), DO.chars_nr(D.view(C.BT(obl, obt)))))

law i_merge:
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  {P.RunP.i(MG.mergeP(c0, s, t)) == True{} : Bool}

def i_merge(c0, s, t):
  match s t:
    case P.RunP{+sn, +si, +sh, +sc, +scbl, +scbt, +se, +sl, +sf, +sb, +sbn, +stl, +sk, +sobl, +sobt, +sow, +sns, +sx} P.RunP{+tn, +ti, +th, +tc, +tcbl, +tcbt, +te, +tl, +tf, +tb, +tbn, +ttl, +tk, +tobl, +tobt, +tow, +tns, +tx}:
      {==}

law x_merge:
  for +c0: String
  for +s: P.RunP
  for +t: P.RunP
  {P.RunP.x(MG.mergeP(c0, s, t)) == False{} : Bool}

def x_merge(c0, s, t):
  match s t:
    case P.RunP{+sn, +si, +sh, +sc, +scbl, +scbt, +se, +sl, +sf, +sb, +sbn, +stl, +sk, +sobl, +sobt, +sow, +sns, +sx} P.RunP{+tn, +ti, +th, +tc, +tcbl, +tcbt, +te, +tl, +tf, +tb, +tbn, +ttl, +tk, +tobl, +tobt, +tow, +tns, +tx}:
      {==}

# A task that read no line is never merged: segok wants T to have read lines.
law segok_rs0:
  for +w: Nat
  for +c0: String
  for +l: Nat
  for +sx: R.RunSt
  {SD.segok(w, c0, l, sx, SD.rs0(c0, l)) == False{} : Bool}

def segok_rs0(w, c0, l, sx):
  match sx:
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +o, +ns, False{}}:
      {==}
    case R.RunSt{+n, True{}, +h, +c, +e, +la, +b, +k, +o, +ns, True{}}:
      {==}
    case R.RunSt{+n, False{}, +h, +c, +e, +la, +b, +k, +o, +ns, +x}:
      {==}

# The segment lemma on the task's lines (none: segok fails, as T read none).
law mg_lines:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +lsT: List<&2, B.Line>
  for +R2: List<&2, B.Line>
  for +S0: R.RunSt
  for +hfc: {SD.first_chrom(List.append(&2, B.Line, lsT, R2)) == Some{c0} : Maybe<&2, String>}
  for +hk: {SD.segok(R.Opts.w(o), c0, l, S0, L.run.go(lsT, fa, dfs, o, SD.rs0(c0, l))) == True{} : Bool}
  {P.settle(L.run.go(lsT, fa, dfs, o, S0)) == P.settle(SD.shiftS(c0, S0, L.run.go(lsT, fa, dfs, o, SD.rs0(c0, l)))) : R.RunSt}

def mg_lines(dfs,fa, o, c0, l, lsT, R2, S0, hfc, hk):
  match lsT:
    case Nil{}:
      Empty.absurd({P.settle(L.run.go(Nil{}, fa, dfs, o, S0)) == P.settle(SD.shiftS(c0, S0, L.run.go(Nil{}, fa, dfs, o, SD.rs0(c0, l)))) : R.RunSt},
        PB.false_ne_true(Equal.trans(Bool, False{}, SD.segok(R.Opts.w(o), c0, l, S0, SD.rs0(c0, l)), True{}, Equal.sym(Bool, SD.segok(R.Opts.w(o), c0, l, S0, SD.rs0(c0, l)), False{}, segok_rs0(R.Opts.w(o), c0, l, S0)), hk)))
    case Con{+x, +t}:
      SG.seg(dfs, fa, o, c0, l, S0, x <> t, hfc, hk)

# The report after the merge (lsT: the task's lines; R2: the lines after
# them; S0: the true run with what the driver collected in front).
law mg_rep_k:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c0: String
  for +l: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +rp2: P.RunP
  for +rpT: P.RunP
  for +lsT: List<&2, B.Line>
  for +R2: List<&2, B.Line>
  for +T: R.Report
  for +hr3: {R.finish(L.run.go(List.append(&2, B.Line, lsT, R2), fa, dfs, o, S.pre(O, N, P.specRun(rp2)))) == T : R.Report}
  for +hfc: {SD.first_chrom(List.append(&2, B.Line, lsT, R2)) == Some{c0} : Maybe<&2, String>}
  for +hsT: {P.settle(P.specRun(rpT)) == P.settle(L.run.go(lsT, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}
  for +hsg: {SD.segok(R.Opts.w(o), c0, l, P.specRun(rp2), P.specRun(rpT)) == True{} : Bool}
  for +hms: {P.settle(S.pre(P.obtext(rp2), List.reverse(&2, B.Note, MG.RunP.ns(rp2)), P.specRun(MG.mergeP(c0, rp2, rpT)))) == P.settle(SD.shiftS(c0, P.specRun(rp2), P.specRun(rpT))) : R.RunSt}
  for +hxT: {P.RunP.x(rpT) == False{} : Bool}
  {R.finish(L.run.go(R2, fa, dfs, o, S.pre(String.append(O, P.obtext(rp2)), List.append(&2, B.Note, N, List.reverse(&2, B.Note, MG.RunP.ns(rp2))), P.specRun(MG.mergeP(c0, rp2, rpT))))) == T : R.Report}

def mg_rep_k(dfs,fa, o, c0, l, O, N, rp2, rpT, lsT, R2, T, hr3, hfc, hsT, hsg, hms, hxT):
  +w = R.Opts.w(o)
  +S2 = P.specRun(rp2)
  +ST = P.specRun(rpT)
  +S0 = S.pre(O, N, S2)
  +TT = L.run.go(lsT, fa, dfs, o, SD.rs0(c0, l))
  +t = P.obtext(rp2)
  +ns = List.reverse(&2, B.Note, MG.RunP.ns(rp2))
  +SM = P.specRun(MG.mergeP(c0, rp2, rpT))
  +NEW = S.pre(String.append(O, t), List.append(&2, B.Note, N, ns), SM)
  +hsgT = Equal.trans(Bool, SD.segok(w, c0, l, S2, TT), SD.segok(w, c0, l, S2, P.settle(TT)), True{},
    Equal.sym(Bool, SD.segok(w, c0, l, S2, P.settle(TT)), SD.segok(w, c0, l, S2, TT), SP.segok_settle(w, c0, l, S2, TT)),
    Equal.trans(Bool, SD.segok(w, c0, l, S2, P.settle(TT)), SD.segok(w, c0, l, S2, P.settle(ST)), True{},
      Equal.cong(R.RunSt, Bool, z => SD.segok(w, c0, l, S2, z), P.settle(TT), P.settle(ST), Equal.sym(R.RunSt, P.settle(ST), P.settle(TT), hsT)),
      Equal.trans(Bool, SD.segok(w, c0, l, S2, P.settle(ST)), SD.segok(w, c0, l, S2, ST), True{}, SP.segok_settle(w, c0, l, S2, ST), hsg)))
  +hk = Equal.trans(Bool, SD.segok(w, c0, l, S0, TT), SD.segok(w, c0, l, S2, TT), True{}, SP.segok_pre(w, c0, l, O, N, S2, TT), hsgT)
  +hxST = Equal.trans(Bool, R.RunSt.halt(ST), P.RunP.x(rpT), False{}, SP.spec_halt(rpT), hxT)
  +hxTT = Equal.trans(Bool, R.RunSt.halt(TT), R.RunSt.halt(P.settle(TT)), False{}, Equal.sym(Bool, R.RunSt.halt(P.settle(TT)), R.RunSt.halt(TT), SP.settle_halt(TT)),
    Equal.trans(Bool, R.RunSt.halt(P.settle(TT)), R.RunSt.halt(P.settle(ST)), False{},
      Equal.cong(R.RunSt, Bool, z => R.RunSt.halt(z), P.settle(TT), P.settle(ST), Equal.sym(R.RunSt, P.settle(ST), P.settle(TT), hsT)),
      Equal.trans(Bool, R.RunSt.halt(P.settle(ST)), R.RunSt.halt(ST), False{}, SP.settle_halt(ST), hxST)))
  +e1 = mg_lines(dfs, fa, o, c0, l, lsT, R2, S0, hfc, hk)
  +e2 = SP.shift_settle(c0, S0, TT, hxTT)
  +e3 = Equal.cong(R.RunSt, R.RunSt, z => P.settle(SD.shiftS(c0, S0, z)), P.settle(TT), P.settle(ST), Equal.sym(R.RunSt, P.settle(ST), P.settle(TT), hsT))
  +e4 = SP.shift_settle(c0, S0, ST, hxST)
  +e5 = Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), SD.shiftS(c0, S0, ST), S.pre(O, N, SD.shiftS(c0, S2, ST)), Equal.sym(R.RunSt, S.pre(O, N, SD.shiftS(c0, S2, ST)), SD.shiftS(c0, S0, ST), SP.pre_shift(c0, O, N, S2, ST)))
  +e6 = FRM.settle_pre(O, N, SD.shiftS(c0, S2, ST))
  +e7 = Equal.cong(R.RunSt, R.RunSt, z => S.pre(O, N, z), P.settle(SD.shiftS(c0, S2, ST)), P.settle(S.pre(t, ns, SM)), Equal.sym(R.RunSt, P.settle(S.pre(t, ns, SM)), P.settle(SD.shiftS(c0, S2, ST)), hms))
  +e8 = Equal.sym(R.RunSt, P.settle(S.pre(O, N, S.pre(t, ns, SM))), S.pre(O, N, P.settle(S.pre(t, ns, SM))), FRM.settle_pre(O, N, S.pre(t, ns, SM)))
  +e9 = Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), S.pre(O, N, S.pre(t, ns, SM)), NEW, Equal.sym(R.RunSt, NEW, S.pre(O, N, S.pre(t, ns, SM)), SP.pre_pre(O, N, t, ns, SM)))
  +hset = Equal.trans(R.RunSt, P.settle(L.run.go(lsT, fa, dfs, o, S0)), P.settle(SD.shiftS(c0, S0, TT)), P.settle(NEW), e1,
    Equal.trans(R.RunSt, P.settle(SD.shiftS(c0, S0, TT)), P.settle(SD.shiftS(c0, S0, P.settle(TT))), P.settle(NEW), Equal.sym(R.RunSt, P.settle(SD.shiftS(c0, S0, P.settle(TT))), P.settle(SD.shiftS(c0, S0, TT)), e2),
    Equal.trans(R.RunSt, P.settle(SD.shiftS(c0, S0, P.settle(TT))), P.settle(SD.shiftS(c0, S0, P.settle(ST))), P.settle(NEW), e3,
    Equal.trans(R.RunSt, P.settle(SD.shiftS(c0, S0, P.settle(ST))), P.settle(SD.shiftS(c0, S0, ST)), P.settle(NEW), e4,
    Equal.trans(R.RunSt, P.settle(SD.shiftS(c0, S0, ST)), P.settle(S.pre(O, N, SD.shiftS(c0, S2, ST))), P.settle(NEW), e5,
    Equal.trans(R.RunSt, P.settle(S.pre(O, N, SD.shiftS(c0, S2, ST))), S.pre(O, N, P.settle(SD.shiftS(c0, S2, ST))), P.settle(NEW), e6,
    Equal.trans(R.RunSt, S.pre(O, N, P.settle(SD.shiftS(c0, S2, ST))), S.pre(O, N, P.settle(S.pre(t, ns, SM))), P.settle(NEW), e7,
    Equal.trans(R.RunSt, S.pre(O, N, P.settle(S.pre(t, ns, SM))), P.settle(S.pre(O, N, S.pre(t, ns, SM))), P.settle(NEW), e8, e9))))))))
  Equal.trans(R.Report, R.finish(L.run.go(R2, fa, dfs, o, NEW)), R.finish(L.run.go(R2, fa, dfs, o, L.run.go(lsT, fa, dfs, o, S0))), T,
    SP.fin_settle(dfs, R2, fa, o, NEW, L.run.go(lsT, fa, dfs, o, S0), Equal.sym(R.RunSt, P.settle(L.run.go(lsT, fa, dfs, o, S0)), P.settle(NEW), hset)),
    Equal.trans(R.Report, R.finish(L.run.go(R2, fa, dfs, o, L.run.go(lsT, fa, dfs, o, S0))), R.finish(L.run.go(List.append(&2, B.Line, lsT, R2), fa, dfs, o, S0)), T,
      Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(R2, fa, dfs, o, L.run.go(lsT, fa, dfs, o, S0)), L.run.go(List.append(&2, B.Line, lsT, R2), fa, dfs, o, S0),
        Equal.sym(R.RunSt, L.run.go(List.append(&2, B.Line, lsT, R2), fa, dfs, o, S0), L.run.go(R2, fa, dfs, o, L.run.go(lsT, fa, dfs, o, S0)), SP.go_app(dfs, lsT, R2, fa, o, S0))),
      hr3))
