import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./tan.bend as V
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_window_defs.bend as WS
import ./proof_fast.bend as PF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_cut.bend as CU
import ./proof_b_end.bend as PE
import ./proof_b_end_key.bend as EK
import ./proof_b_alleles.bend as AA
import ./proof_b_lines_str.bend as LSS
import ./proof_b_alleles_list.bend as AL
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_judge.bend as JG
import ./proof_b_adv_wr.bend as WR
import ./proof_b_lines.bend as LN
import ./proof_b_alleles_loop.bend as ALP
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import ./proof_b_run.bend as PR
import ./proof_b_adv_ib.bend as IB
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_mw.bend as MW
import ./proof_s_multi.bend as MU
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_b_adv_hit.bend as FH
import ./proof_b_skip.bend as SK

# The out-of-scope line's hit (norm_seq.bend's skip.hit), its verdict and
# its run step: generated from proof_b_adv_hit.bend's fast hit (fhit.*), the
# window's facts dropped, the verdict Skipped (proof_b_skip.bend's
# skip_judge), the run's NR.skip_done.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

law body_step_s:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +p: Nat
  for +chrom: String
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == True{} : Bool}
  for +hj: {L.judge(fa, B.Line.body(Norm.line(A))) == SK.RS(B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A)))), B.Line.body(Norm.line(A))) : B.Res}
  for +hpos: {B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(A)))) == p : Nat}
  for +hf0: {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 0n) == chrom : String}
  for +hf1: {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A))), 1n) == Nat.show(p) : String}
  for +hw0: {B.Rec.parts(dfs, o, B.Line.body(Norm.line(A))) == B.Whole{} : B.Parts}
  {L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) == R.body_line(SK.RS(p, B.Line.body(Norm.line(A))), R.tick(P.specRun(rp)), o, Norm.line(A), B.At{1n+P.RunP.n(rp), chrom, Nat.show(p)}, p) : R.RunSt}

def body_step_s(dfs, fa, o, rp, A, p, chrom, hx, hin, hj, hpos, hf0, hf1, hw0):
  +st = P.specRun(rp)
  +l = Norm.line(A)
  +bd = B.Line.body(l)
  +fs = B.Rec.fields(bd)
  +RHS = R.body_line(SK.RS(p, bd), R.tick(st), o, l, B.At{1n+P.RunP.n(rp), chrom, Nat.show(p)}, p)
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, WR.halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, dfs, o, st, B.Text.line(A)) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), True{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
    {L.line_in(_, fa, dfs, o, R.tick(st), B.Text.line(A)) == RHS : R.RunSt}
  %LN.line_eq(A) : {L.body_in(B.Rec.parts(dfs, o, B.Line.body(_)), fa, o, R.tick(st), _, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(_)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(_)))) == RHS : R.RunSt}
  %Equal.sym(B.Parts, B.Rec.parts(dfs, o, bd), B.Whole{}, hw0) : {L.body_in(_, fa, o, R.tick(st), l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  %Equal.sym(B.Res, L.judge(fa, bd), SK.RS(B.Rec.pos(fs), bd), hj) :
    {R.body_line(_, R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs)) == RHS : R.RunSt}
  %Equal.sym(Nat, B.Rec.pos(fs), p, hpos) :
    {R.body_line(SK.RS(_, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, _) == RHS : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 0n), chrom, hf0) :
    {R.body_line(SK.RS(p, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), _, B.Rec.field(fs, 1n)}, p) == RHS : R.RunSt}
  %Equal.sym(String, B.Rec.field(fs, 1n), Nat.show(p), hf1) :
    {R.body_line(SK.RS(p, bd), R.tick(st), o, l, B.At{R.RunSt.n(R.tick(st)), chrom, _}, p) == RHS : R.RunSt}
  %Equal.sym(Nat, R.RunSt.n(R.tick(st)), 1n+P.RunP.n(rp), Equal.trans(Nat, R.RunSt.n(R.tick(st)), 1n+R.RunSt.n(st), 1n+P.RunP.n(rp), FH.tick_n(st),
      Equal.cong(Nat, Nat, z => 1n+z, R.RunSt.n(st), P.RunP.n(rp), FH.n_spec(rp)))) :
    {R.body_line(SK.RS(p, bd), R.tick(st), o, l, B.At{_, chrom, Nat.show(p)}, p) == RHS : R.RunSt}
  {==}

law fs_s:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: U32
  for +pos: U32
  for +e0: U32
  for +e1: U32
  for +e2: U32
  for +e3: U32
  for +e4: U32
  for +e5: U32
  for +e6: U32
  for +e7: U32
  for +lf: U32
  for +i: Nat
  for +hi: {Nat.is_lt(i, 7n) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(s, len) == True{} : Bool}
  for +hp: SK.SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
  {B.Rec.field(FH.FS(len, t, s, lf), i) == B.Rec.field([FH.FLD(len, t, n(s), n(e0)), FH.FLD(len, t, CU.nx(e0), n(e1)), FH.FLD(len, t, CU.nx(e1), n(e2)), FH.FLD(len, t, CU.nx(e2), n(e3)), FH.FLD(len, t, CU.nx(e3), n(e4)), FH.FLD(len, t, CU.nx(e4), n(e5)), FH.FLD(len, t, CU.nx(e5), n(e6)), B.Rec.field(J.pfs(FH.BODY(len, t, s, lf)), 7n)], i) : String}

def fs_s(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, i, hi, hok, hs, hp):
  +body = FH.BODY(len, t, s, lf)
  %PF.pfs_field(body, i, hi) : {_ == B.Rec.field([FH.FLD(len, t, n(s), n(e0)), FH.FLD(len, t, CU.nx(e0), n(e1)), FH.FLD(len, t, CU.nx(e1), n(e2)), FH.FLD(len, t, CU.nx(e2), n(e3)), FH.FLD(len, t, CU.nx(e3), n(e4)), FH.FLD(len, t, CU.nx(e4), n(e5)), FH.FLD(len, t, CU.nx(e5), n(e6)), B.Rec.field(J.pfs(FH.BODY(len, t, s, lf)), 7n)], i) : String}
  Equal.cong(List<&2, String>, String, z => B.Rec.field(z, i), J.pfs(body), [FH.FLD(len, t, n(s), n(e0)), FH.FLD(len, t, CU.nx(e0), n(e1)), FH.FLD(len, t, CU.nx(e1), n(e2)), FH.FLD(len, t, CU.nx(e2), n(e3)), FH.FLD(len, t, CU.nx(e3), n(e4)), FH.FLD(len, t, CU.nx(e4), n(e5)), FH.FLD(len, t, CU.nx(e5), n(e6)), B.Rec.field(J.pfs(FH.BODY(len, t, s, lf)), 7n)],
    SK.skip_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))

law hpos_s:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: U32
  for +pos: U32
  for +e0: U32
  for +e1: U32
  for +e2: U32
  for +e3: U32
  for +e4: U32
  for +e5: U32
  for +e6: U32
  for +e7: U32
  for +lf: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(s, len) == True{} : Bool}
  for +hp: SK.SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)
  {B.Rec.pos(FH.FS(len, t, s, lf)) == n(pos) : Nat}

def hpos_s(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp):
  %Equal.sym(String, B.Rec.field(FH.FS(len, t, s, lf), 1n), B.Rec.field([FH.FLD(len, t, n(s), n(e0)), FH.FLD(len, t, CU.nx(e0), n(e1)), FH.FLD(len, t, CU.nx(e1), n(e2)), FH.FLD(len, t, CU.nx(e2), n(e3)), FH.FLD(len, t, CU.nx(e3), n(e4)), FH.FLD(len, t, CU.nx(e4), n(e5)), FH.FLD(len, t, CU.nx(e5), n(e6)), B.Rec.field(J.pfs(FH.BODY(len, t, s, lf)), 7n)], 1n), fs_s(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 1n, {==}, hok, hs, hp)) : {Maybe.default(&2, Nat, B.Pos.read(_), 0n) == n(pos) : Nat}
  %Equal.sym(Maybe<&2, Nat>, B.Pos.read(FH.FLD(len, t, CU.nx(e0), n(e1))), Some{n(pos)}, PJ.pp_read(len, t, pos, e0, e1, SK.skip_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))) : {Maybe.default(&2, Nat, _, 0n) == n(pos) : Nat}
  {==}

def BL0s(+o: B.Opts, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32, +pos: U32, +chrom: String) -> R.RunSt:
  R.body_line(SK.RS(n(pos), B.Line.body(Norm.line(FH.AofL(len, t, at, lf)))), P.specRun(rp1), o, Norm.line(FH.AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))

def shit.w(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +rp2: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hfl: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(BL0s(o, rp1, len, t, at, lf, pos, P.btext(len, t, at, (e0 - at : U32)))) : R.RunSt},
  sl: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(FH.AofL(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(FH.AofL(len, t, at, lf)) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.Src.of(hold, C.BT(len, t), (lf + 1 : U32)), P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, CD.mkWin(fa, wp), None{}, False{}, dfs}}):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          match q2:
            case (hle, hby):
              +A = FH.AofL(len, t, at, lf)
              +l = Norm.line(A)
              +X = xs(len, t)
              +chrom = P.btext(len, t, at, (e0 - at : U32))
              +bd = B.Line.body(l)
              +hfa = FH.btext_fld(len, t, at, lf, hal)
              +hs0 = PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
              +hj = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {L.judge(fa, B.Line.body(Norm.line(_))) == SK.RS(B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(_)))), B.Line.body(Norm.line(_))) : B.Res};
                SK.skip_judge(fa, len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp, hse) : {L.judge(fa, bd) == SK.RS(B.Rec.pos(B.Rec.fields(bd)), bd) : B.Res}}
              +hpos = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.pos(B.Rec.fields(B.Line.body(Norm.line(_)))) == n(pos) : Nat};
                hpos_s(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp) : {B.Rec.pos(B.Rec.fields(bd)) == n(pos) : Nat}}
              +hf0 = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(_))), 0n) == chrom : String};
                %Equal.sym(String, chrom, FH.FLD(len, t, n(at), n(e0)), FH.btext_fld(len, t, at, e0, hs0)) : {B.Rec.field(FH.FS(len, t, at, lf), 0n) == _ : String};
                fs_s(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 0n, {==}, hok, hs, hp) : {B.Rec.field(B.Rec.fields(bd), 0n) == chrom : String}}
              +hf1 = {%Equal.sym(String, A, CU.fld(X, n(at), n(lf)), hfa) : {B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(_))), 1n) == Nat.show(n(pos)) : String};
                %Equal.sym(String, Nat.show(n(pos)), FH.FLD(len, t, CU.nx(e0), n(e1)), PJ.pp_show(len, t, pos, e0, e1, SK.skip_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))) : {B.Rec.field(FH.FS(len, t, at, lf), 1n) == _ : String};
                fs_s(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, 1n, {==}, hok, hs, hp) : {B.Rec.field(B.Rec.fields(bd), 1n) == Nat.show(n(pos)) : String}}
              +E1 = {%Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.body_line(SK.RS(n(pos), bd), _, o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt};
                %Equal.sym(Nat, P.RunP.n(rp1), 1n+P.RunP.n(rp), n1) : {R.body_line(SK.RS(n(pos), bd), R.tick(P.specRun(rp)), o, l, B.At{_, chrom, Nat.show(n(pos))}, n(pos)) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt};
                Equal.sym(R.RunSt, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), R.body_line(SK.RS(n(pos), bd), R.tick(P.specRun(rp)), o, l, B.At{1n+P.RunP.n(rp), chrom, Nat.show(n(pos))}, n(pos)), body_step_s(dfs, fa, o, rp, A, n(pos), chrom, hx, hin, hj, hpos, hf0, hf1, MW.hw_line(dfs, o, len, t, d, hok, at, lf, hs, hfl, hal, hlt, hmv))) :
                {BL0s(o, rp1, len, t, at, lf, pos, chrom) == L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) : R.RunSt}}
              +hrun = Equal.trans(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BL0s(o, rp1, len, t, at, lf, pos, chrom)), P.settle(L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A))),
                sp2, Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), BL0s(o, rp1, len, t, at, lf, pos, chrom), L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), E1))
              +BLs = R.body_line(SK.RS(n(pos), bd), P.specRun(rp1), o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))
              +hib = {%FH.inbody_settle(P.specRun(rp2)) : {_ == True{} : Bool};
                %Equal.sym(R.RunSt, P.settle(P.specRun(rp2)), P.settle(BL0s(o, rp1, len, t, at, lf, pos, chrom)), sp2) : {R.RunSt.inbody(_) == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(P.settle(BLs)), R.RunSt.inbody(BLs), FH.inbody_settle(BLs)) : {_ == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(BLs), R.RunSt.inbody(P.specRun(rp1)), IB.ib_body_line(SK.RS(n(pos), bd), P.specRun(rp1), o, l, B.At{P.RunP.n(rp1), chrom, Nat.show(n(pos))}, n(pos))) : {_ == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp1)), P.RunP.i(rp1), WR.ib_spec(rp1)) : {_ == True{} : Bool};
                hin1 : {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool}}
              +Xd = B.Defs.line(dfs, B.Line.body(B.Text.line(A)))
              +hd = {%Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), True{}, Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), True{}, WR.ib_spec(rp), hin)) :
                  {dfs == Bool.pick(B.Defs, _, dfs, Xd) : B.Defs};
                {==} : {dfs == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, Xd) : B.Defs}}
              HX.went_h(hold,dfs, dfs, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hsp, hle, hn, hal, hlt, LP.inc_len(len, t, d, lf, hok, hlt), i2, hrun,
                W.or_l(R.RunSt.inbody(P.specRun(rp2)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hib), hx, hd)

# ALT's end is inside the buffer.
def e4_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e4), n(len)) == True{} : Bool}:
  +hlx = PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h7l = PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h67 = PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h56 = PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h45 = PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  N.lt_to_le(n(e4), n(len), N.lt_trans(n(e4), n(e5), n(len), h45, N.lt_trans(n(e5), n(e6), n(len), h56, N.lt_trans(n(e6), n(e7), n(len), h67, N.le_lt_trans(n(e7), n(lf), n(len), h7l, hlx)))))

# CHROM's end is inside the buffer.
def e0_le(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: SK.SKIP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e0), n(len)) == True{} : Bool}:
  +h01 = PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h12 = PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h23 = PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +h34x = PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  N.lt_to_le(n(e0), n(len), N.lt_le_trans(n(e0), n(e4), n(len), N.lt_trans(n(e0), n(e1), n(e4), h01, N.lt_trans(n(e1), n(e2), n(e4), h12, N.lt_trans(n(e2), n(e3), n(e4), h23, h34x))), e4_le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp)))

def shit.d(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(lf), n(len)) == True{} : Bool},
  +hfl: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  fd: &p2: P.RunP -> ({NR.skip_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), n(pos), C.BT(len, t), at, FH.KK(at, lf)) == (P.mkRun(p2), C.BT(len, t)) : NR.Run & D.Bytes}
  & ({PR.RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Skipped{}, n(pos), B.Line.body(Norm.line(FH.AofL(len, t, at, lf))), False{}}, P.specRun(rp1), o, Norm.line(FH.AofL(len, t, at, lf)), B.At{P.RunP.n(rp1), P.btext(len, t, at, (e0 - at : U32)), Nat.show(n(pos))}, n(pos))) : R.RunSt})),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.skip.hit(o, (P.mkRun(rp1), P.RunP.n(rp1)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  match fd:
    case (+rp2, q):
      match q:
        case (efd, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.skip_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), n(pos), C.BT(len, t), at, FH.KK(at, lf)), (P.mkRun(rp2), C.BT(len, t)), efd) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, _, (lf + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
              shit.w(hold, dfs, fa, T, cs, O, N, o, rp, rp1, rp2, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf,
                hw, hr, hg, hx, hin, hok, hs, hmv, hp, hse, hal, hlt, hfl, s1, n1, hin1, i2, sp2,
                LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt), hnr)

# The hit with the line's tick done (rp1).
def shit.t(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32},
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.skip.hit(o, NR.Run.n(NR.tick(P.mkRun(rp))), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
  +A = FH.AofL(len, t, at, lf)
  +l = Norm.line(A)
  +chrom = P.btext(len, t, at, (e0 - at : U32))
  +hfl = PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hlt = PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, SK.skip_lf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hok, hs, hp))
  +hjr = FH.j_range(len, t, d, at, lf, hok, hs, Equal.sym(Nat, D.first(xs(len, t), n(at), n(len), 10), n(lf), hfl))
  +hal = W.and_l(Nat.is_le(n(at), n(lf)), Nat.is_le(n(lf), n(len)), hjr)
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hc1 = Equal.trans(Maybe<&2, String>, P.RunP.c(rp1), P.RunP.c(rp), Some{chrom}, FH.c_tick(rp, rp1, s1), hcr)
  +hbig1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(536870912, _) == False{} : Bool}; hbig : {U32.is_le(536870912, P.RunP.obl(rp1)) == False{} : Bool}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.skip.hit(o, NR.Run.n(_), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.skip.hit(o, _, pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp)))
  shit.d(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hmv, hp, hse, hcr, hsm, rp1, s1, n1, hin1, hal, hlt, hfl,
    PR.run_skip_done(rp1, o, l, n(pos), chrom, len, t, d, at, FH.KK(at, lf), i1, hin1, hx1, hok,
      FH.k_fit(len, t, d, at, lf, hok, hal, hlt), FH.k_text(len, t, d, at, lf, hok, hs, hfl, hal, hlt), hc1, hbig1,
      FH.k_le_z(len, t, d, at, lf, 268435456, 268435457, hok, hal, hlt, hsm, {==})), hnr)

def shit(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: CD.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32,
  +hw: {S.WF(fa, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool}, +hmv: {MU.MW(o, len, t, at) == True{} : Bool},
  +hp: SK.SKIP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  tk: WR.TKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.skip.hit(o, Norm.ticked(P.mkRun(rp)), pos, at, lf, C.BT(len, t), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}, CD.mkWin(fa, wp))):
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
                          shit.t(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, hw, hr, hg, hi, hx, hin, hbig, hok, hs, hmv, hp, hse, hcr, hsm, rp1, et, i1, s1, n1, obl1, hnr)
