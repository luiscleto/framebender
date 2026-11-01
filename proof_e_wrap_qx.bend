import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_b_drive_pump.bend as DP
import lawful-bytes@0.1.1.0/bytes.bend as BY
import ./proof_base.bend as PB
import ./proof_b_run.bend as RN
import ./proof_e_qif.bend as QI
import ./proof_e_qif_fed.bend as F
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_e_wrap_base.bend as WB

# Helpers for proof_e_wrap.bend (area E1): a step of Q keeps its options and,
# when it asks for more, has not stopped. Code level for out, finish and
# idle; along AdvG (with area A's options clause) for the pump; then go, and
# a step given an answer. (Generated from a source with an {WB.st_o(WB.step_st(s)) == o : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool} macro:
# {st_o(step_st(s)) == o} & {live_k(step_nx(s), st_stop(step_st(s))) == True}.)

# out, finish, idle
# =================

law outk_mb_xs:
  for +dfs: B.Defs
  for p: D.Bytes & D.Bytes
  for r: NR.Run
  for +o: B.Opts
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +h: {WB.live_k(nx, WB.run_x(r)) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, dfs, nx))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, dfs, nx)), WB.st_stop(WB.step_st(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, dfs, nx)))) == True{} : Bool}

def outk_mb_xs(dfs,p, r, o, src, pend, eof, back, win, asked, fneed, nx, h):
  match p r:
    case (out, ob) NR.Run{n, i, hh, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, x}:
      ({==}, h)

law outk_ms_xs:
  for +dfs: B.Defs
  for c: Norm.Cut2
  for +s: R.RunSt
  for +ns: List<&2, B.Note>
  for +code: Maybe<&2, Nat>
  for +o: B.Opts
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +h: {WB.live_k(nx, R.RunSt.halt(s) || Maybe.is_some(&2, Nat, code)) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, dfs, nx))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, dfs, nx)), WB.st_stop(WB.step_st(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, dfs, nx)))) == True{} : Bool}

def outk_ms_xs(dfs,c, s, ns, code, o, src, pend, eof, back, win, asked, fneed, nx, h):
  match c:
    case Norm.Cut2{now, later}:
      ({==}, h)

law ol_xs:
  for +dfs: B.Defs
  for +o: B.Opts
  for md: Norm.Md
  for p: List<&1, Norm.Src> & U32
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +nx: Pr.Next
  for +h: {WB.live_k(nx, WB.md_stop(md)) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, dfs, nx))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, dfs, nx)), WB.st_stop(WB.step_st(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, dfs, nx)))) == True{} : Bool}

def ol_xs(dfs,o, md, p, pend, eof, back, win, asked, fneed, nx, h):
  match md:
    case Norm.MB{NR.Run{nn, i, hh, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, +x}}:
      match p:
        case (src, +n):
          outk_mb_xs(dfs, NR.take.if(U32.is_zero(ow), ow, n, ob), NR.Run{nn, i, hh, c, cb, e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, x}, o, src, pend, eof, back, win, asked, fneed, nx, h)
    case Norm.MS{R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, +rns, +rx}, qs, ql, +code}:
      match p:
        case (src, +n):
          outk_ms_xs(dfs, Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, Nil{}, rx}, rns, code, o, src, pend, eof, back, win, asked, fneed, nx, h)

law out_xs:
  for st: Norm.St
  for +nx: Pr.Next
  for +h: {WB.live_k(nx, WB.st_stop(st)) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.out(st, nx))) == WB.st_o(st) : B.Opts} & {WB.live_k(WB.step_nx(Norm.out(st, nx)), WB.st_stop(WB.step_st(Norm.out(st, nx)))) == True{} : Bool}

def out_xs(st, nx, h):
  match st:
    case Norm.St{+o, md, src, pend, eof, +back, win, asked, +fneed, +dfs}:
      ol_xs(dfs, o, md, Norm.left(src), pend, eof, back, win, asked, fneed, nx, h)

law xs_o:
  for -s: Norm.Step
  for +o1: B.Opts
  for +o2: B.Opts
  for +he: {o1 == o2 : B.Opts}
  for h: {WB.st_o(WB.step_st(s)) == o1 : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool}
  {WB.st_o(WB.step_st(s)) == o2 : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool}

def xs_o(s, o1, o2, he, h):
  %he : {WB.st_o(WB.step_st(s)) == _ : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool}
  h

law finmb_x:
  for +dfs: B.Defs
  for +o: B.Opts
  for p: NR.Run & Nat
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {WB.st_o(WB.step_st(Norm.fin.mb(o, p, src, pend, eof, back, win, asked, fneed, dfs))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.fin.mb(o, p, src, pend, eof, back, win, asked, fneed, dfs)), WB.st_stop(WB.step_st(Norm.fin.mb(o, p, src, pend, eof, back, win, asked, fneed, dfs)))) == True{} : Bool}

def finmb_x(dfs,o, p, src, pend, eof, back, win, asked, fneed):
  match p:
    case (run, +code):
      out_xs(Norm.St{o, Norm.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, Pr.Finish{code}, {==})

law finmsgo_x:
  for +dfs: B.Defs
  for fits: Bool
  for +o: B.Opts
  for s: R.RunSt
  for qs: List<&2, String>
  for +ql: Nat
  for +code: Nat
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {WB.st_o(WB.step_st(Norm.fin.ms.go(fits, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.fin.ms.go(fits, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs)), WB.st_stop(WB.step_st(Norm.fin.ms.go(fits, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs)))) == True{} : Bool}

def finmsgo_x(dfs,fits, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed):
  match fits:
    case True{}:
      out_xs(Norm.St{o, Norm.MS{s, qs, ql, Some{code}}, src, pend, eof, back, win, asked, fneed, dfs}, Pr.Finish{code}, {==})
    case False{}:
      out_xs(Norm.St{o, Norm.MS{s, qs, ql, Some{code}}, src, pend, eof, back, win, asked, fneed, dfs}, Pr.Ask{Nil{}}, {==})

law finms_x:
  for +dfs: B.Defs
  for rep: R.Report
  for +o: B.Opts
  for s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {WB.st_o(WB.step_st(Norm.fin.ms(rep, o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.fin.ms(rep, o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs)), WB.st_stop(WB.step_st(Norm.fin.ms(rep, o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs)))) == True{} : Bool}

def finms_x(dfs,rep, o, s, qs, ql, src, pend, eof, back, win, asked, fneed):
  match rep s:
    case R.Report{+out, ns, +code} R.RunSt{n, i, h, c, e, l, b, k, o2, ns0, x}:
      finmsgo_x(dfs, Norm.len_le(Norm.cat(List.reverse(&2, String, out <> qs)), 1073741824), o, R.RunSt{n, i, h, c, e, l, b, k, "", ns, x}, out <> qs, Nat.add(ql, String.length(out)), code, src, pend, eof, back, win, asked, fneed)

law finish_x:
  for st: Norm.St
  {WB.st_o(WB.step_st(Norm.finish(st))) == WB.st_o(st) : B.Opts} & {WB.live_k(WB.step_nx(Norm.finish(st)), WB.st_stop(WB.step_st(Norm.finish(st)))) == True{} : Bool}

def finish_x(st):
  match st:
    case Norm.St{+o, Norm.MB{run}, src, pend, eof, +back, win, asked, +fneed, +dfs}:
      finmb_x(dfs, o, NR.finish(run, R.Opts.w(o)), src, pend, eof, back, win, asked, fneed)
    case Norm.St{+o, Norm.MS{+s, +qs, +ql, None{}}, src, pend, eof, +back, win, asked, +fneed, +dfs}:
      finms_x(dfs, R.finish(s), o, s, qs, ql, src, pend, eof, back, win, asked, fneed)
    case Norm.St{+o, Norm.MS{s, +qs, +ql, Some{+code}}, src, pend, eof, +back, win, asked, +fneed, +dfs}:
      finmsgo_x(dfs, Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824), o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed)

law idle_x:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for +hst: {S.stopped(S.StP.md(p2)) == False{} : Bool}
  {WB.st_o(WB.step_st(Norm.idle(S.mkSt(fa, p2)))) == S.StP.o(p2) : B.Opts} & {WB.live_k(WB.step_nx(Norm.idle(S.mkSt(fa, p2))), WB.st_stop(WB.step_st(Norm.idle(S.mkSt(fa, p2))))) == True{} : Bool}

def idle_x(fa, p2, hst):
  match p2:
    case S.StP{+o, +md, +src, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      finish_x(S.mkSt(fa, S.StP{o, md, src, pd, True{}, back, wp, asked, fneed, dfs}))
    case S.StP{+o, +md, +src, +pd, False{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, src, pd, False{}, back, wp, asked, fneed, dfs} : S.StP}
      out_xs(S.mkSt(fa, q), Pr.More{},
        Equal.cong(Bool, Bool, z => Bool.not(z), WB.st_stop(S.mkSt(fa, q)), False{}, Equal.trans(Bool, WB.st_stop(S.mkSt(fa, q)), S.stopped(md), False{}, WB.stop_mk(fa, q), hst)))

# The pump, along AdvG
# ====================

law ostep:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for +o: B.Opts
  for +eo: {S.StP.o(p2) == o : B.Opts}
  {WB.st_o(S.mkSt(fa, p2)) == o : B.Opts}

def ostep(fa, p2, o, eo):
  Equal.trans(B.Opts, WB.st_o(S.mkSt(fa, p2)), S.StP.o(p2), o, WB.o_mk(fa, p2), eo)

# What pump_x says of a step.
def PX(-s: Norm.Step, +o0: B.Opts) -> Type:
  {WB.st_o(WB.step_st(s)) == o0 : B.Opts} & {WB.live_k(WB.step_nx(s), WB.st_stop(WB.step_st(s))) == True{} : Bool}

def IHX(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +o0: B.Opts) -> Type:
  @q: S.StP -> @a: Norm.Adv -> S.AdvG(fa, T, cs, O, N, q, a) -> {S.StP.o(q) == o0 : B.Opts} -> PX(Norm.pump(g, a), o0)

# pump.r (the records' fuel) ends with an Adv from a state with the options.
law pump_xr:
  for +f2: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  for +g: Nat
  for +o0: B.Opts
  for +heo: {S.StP.o(p) == o0 : B.Opts}
  for ih: IHX(g, fa, T, cs, O, N, o0)
  PX(Norm.pump(g, Norm.pump.r(f2, a)), o0)

def pump_xr(f2, a, fa, T, cs, O, N, p, hb, ag, g, o0, heo, ih):
  match f2 a:
    case 1n+h Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (+eg, a8) = a7
      (+eo, mvk) = a8
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PX(Norm.pump(g, Norm.pump.r(h, Norm.advance(_))), o0)
      pump_xr(h, Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg), g, o0,
        Equal.trans(B.Opts, S.StP.o(p2), S.StP.o(p), o0, eo, heo), ih)
    case 0n Norm.Went{st}:
      ih(p, Norm.Went{st}, ag, heo)
    case _ Norm.Want{st, +r}:
      ih(p, Norm.Want{st, r}, ag, heo)
    case _ Norm.Idle{st}:
      ih(p, Norm.Idle{st}, ag, heo)
    case _ Norm.Ended{st}:
      ih(p, Norm.Ended{st}, ag, heo)
    case _ Norm.Yield{st}:
      ih(p, Norm.Yield{st}, ag, heo)

law pump_x:
  for +f: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  {WB.st_o(WB.step_st(Norm.pump(f, a))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.pump(f, a)), WB.st_stop(WB.step_st(Norm.pump(f, a)))) == True{} : Bool}

def pump_x(f, a, fa, T, cs, O, N, p, hb, ag):
  match f a:
    case 0n Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (elt, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      (eo, mvk) = a8
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : {WB.st_o(WB.step_st(Norm.out(_, Pr.Ask{Nil{}}))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.out(_, Pr.Ask{Nil{}})), WB.st_stop(WB.step_st(Norm.out(_, Pr.Ask{Nil{}})))) == True{} : Bool}
      xs_o(Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), WB.st_o(S.mkSt(fa, p2)), S.StP.o(p), ostep(fa, p2, S.StP.o(p), eo), out_xs(S.mkSt(fa, p2), Pr.Ask{Nil{}}, {==}))
    case 1n+g Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (elt, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (+eg, a8) = a7
      (eo, mvk) = a8
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PX(Norm.pump(g, Norm.pump.fill(Norm.fuel.st(_))), S.StP.o(p))
      %Equal.sym(Norm.St & Nat, Norm.fuel.st(S.mkSt(fa, p2)), (S.mkSt(fa, p2), DP.fuelN(S.StP.src(p2))), DP.fst_eq(fa, p2)) :
        PX(Norm.pump(g, Norm.pump.fill(_)), S.StP.o(p))
      pump_xr(DP.fuelN(S.StP.src(p2)), Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg), g, S.StP.o(p), eo,
        +q => a3 => agq => +hoq => xs_o(Norm.pump(g, a3), S.StP.o(q), S.StP.o(p), hoq, pump_x(g, a3, fa, T, cs, O, N, q, hb, agq)))
    case _ Norm.Want{st, +r}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (eq, a5) = a4
      (erq, a6) = a5
      (eask, a7) = a6
      (ens, a8) = a7
      (emr, a9) = a8
      (eeof, a10) = a9
      (eg, a11) = a10
      (eo, mvk) = a11
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : {WB.st_o(WB.step_st(Norm.out(_, Pr.Ask{r}))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.out(_, Pr.Ask{r})), WB.st_stop(WB.step_st(Norm.out(_, Pr.Ask{r})))) == True{} : Bool}
      xs_o(Norm.out(S.mkSt(fa, p2), Pr.Ask{r}), WB.st_o(S.mkSt(fa, p2)), S.StP.o(p), ostep(fa, p2, S.StP.o(p), eo), out_xs(S.mkSt(fa, p2), Pr.Ask{r}, {==}))
    case _ Norm.Idle{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (esrc, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (+ens, a8) = a7
      (eg, a9) = a8
      (eo, mvk) = a9
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : {WB.st_o(WB.step_st(Norm.idle(_))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.idle(_)), WB.st_stop(WB.step_st(Norm.idle(_)))) == True{} : Bool}
      xs_o(Norm.idle(S.mkSt(fa, p2)), S.StP.o(p2), S.StP.o(p), eo, idle_x(fa, p2, ens))
    case _ Norm.Ended{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (eask, a5) = a4
      (estop, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      (eo, kp) = a8
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : {WB.st_o(WB.step_st(Norm.finish(_))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.finish(_)), WB.st_stop(WB.step_st(Norm.finish(_)))) == True{} : Bool}
      xs_o(Norm.finish(S.mkSt(fa, p2)), WB.st_o(S.mkSt(fa, p2)), S.StP.o(p), ostep(fa, p2, S.StP.o(p), eo), finish_x(S.mkSt(fa, p2)))
    case _ Norm.Yield{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (eask, a5) = a4
      (ens, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      (eo, kp) = a8
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : {WB.st_o(WB.step_st(Norm.out(_, Pr.Ask{Nil{}}))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.out(_, Pr.Ask{Nil{}})), WB.st_stop(WB.step_st(Norm.out(_, Pr.Ask{Nil{}})))) == True{} : Bool}
      xs_o(Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), WB.st_o(S.mkSt(fa, p2)), S.StP.o(p), ostep(fa, p2, S.StP.o(p), eo), out_xs(S.mkSt(fa, p2), Pr.Ask{Nil{}}, {==}))

# go from a good state (any report: the extras do not depend on it).
law go_x:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.go(S.mkSt(fa, p)))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(S.mkSt(fa, p))), WB.st_stop(WB.step_st(Norm.go(S.mkSt(fa, p))))) == True{} : Bool}

def go_x(fa, cs, O, N, p, hb, hw, hg):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(src)), (P.mkSrcs(src), DP.fuelN(src)), DP.fuel_eq(src)) :
        {WB.st_o(WB.step_st(Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)), WB.st_stop(WB.step_st(Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)))) == True{} : Bool}
      pump_x(1n+Nat.add(DP.fuelN(src), 1n), Norm.advance(S.mkSt(fa, q)), fa, S.report(fa, cs, O, N, q), cs, O, N, q, hb,
        SA.adv_ok(fa, S.report(fa, cs, O, N, q), cs, O, N, q, hb, hw, {==}, hg))

# A step given answers or a piece
# ===============================

law guard_md:
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +p2: S.StP
  for +emd: {S.StP.md(p2) == S.StP.md(p) : S.MdP}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  {S.guard(O, N, p2) == True{} : Bool}

def guard_md(O, N, p, p2, emd, hg):
  Equal.trans(Bool, S.guard(O, N, p2), S.guard(O, N, p), True{},
    Equal.cong(S.MdP, Bool, z => R.RunSt.inbody(S.smd(z)) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)), S.StP.md(p2), S.StP.md(p), emd), hg)

law ref_x2:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for sw: &p2: S.StP -> ({Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)) == S.mkSt(fa, p2) : Norm.St}
    & ({S.WF(fa, p2) == True{} : Bool} & ({S.StP.md(p2) == S.StP.md(p) : S.MdP} & ({S.StP.o(p2) == S.StP.o(p) : B.Opts}
    & ({S.StP.src(p2) == S.StP.src(p) : List<&2, P.SrcP>} & ({QI.StP.pd(p2) == QI.StP.pd(p) : P.PdP} & ({S.StP.eof(p2) == S.StP.eof(p) : Bool}
    & {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>})))))))
  {WB.st_o(WB.step_st(Norm.go(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs))))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)))), WB.st_stop(WB.step_st(Norm.go(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)))))) == True{} : Bool}

def ref_x2(fa, O, N, p, rs, hb, hg, sw):
  (+p2, s1) = sw
  (e, s2) = s1
  (+wf2, s3) = s2
  (+emd, s4) = s3
  (eo, s5) = s4
  %Equal.sym(Norm.St, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), S.mkSt(fa, p2), e) : {WB.st_o(WB.step_st(Norm.go(_))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(_)), WB.st_stop(WB.step_st(Norm.go(_)))) == True{} : Bool}
  xs_o(Norm.go(S.mkSt(fa, p2)), S.StP.o(p2), S.StP.o(p), eo, go_x(fa, Nil{}, O, N, p2, hb, wf2, guard_md(O, N, p, p2, emd, hg)))

# A step given the truthful answers to what a good state asked.
law ref_x:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hp: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  {WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})))) == True{} : Bool}

def ref_x(fa, O, N, p, rs, hb, hw, ha, hq, hp, hmr, hg):
  ref_x2(fa, O, N, p, rs, hb, hg, QI.set_win_ok(fa, p, rs, hb, hw, ha, hq, hp, hmr))

# The fed state, then go.
law fed_x:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +c: String
  for +q: S.StP
  for -X: Norm.St
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hg: {S.guard(O, N, q) == True{} : Bool}
  for f: F.Fed(fa, c, q, X)
  {WB.st_o(WB.step_st(Norm.go(X))) == S.StP.o(q) : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(X)), WB.st_stop(WB.step_st(Norm.go(X)))) == True{} : Bool}

def fed_x(fa, O, N, c, q, X, hb, hg, f):
  (+p1, f1) = f
  (e, f2) = f1
  (+hw, f3) = f2
  (+hmd, f4) = f3
  (eo, f5) = f4
  %Equal.sym(Norm.St, X, S.mkSt(fa, p1), e) : {WB.st_o(WB.step_st(Norm.go(_))) == S.StP.o(q) : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(_)), WB.st_stop(WB.step_st(Norm.go(_)))) == True{} : Bool}
  xs_o(Norm.go(S.mkSt(fa, p1)), S.StP.o(p1), S.StP.o(q), eo, go_x(fa, Nil{}, O, N, p1, hb, hw, guard_md(O, N, q, p1, hmd, hg)))

law chunk_mb_x:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +c: String
  for +o: B.Opts
  for +rp: P.RunP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  for r: &p2: P.RunP -> ({NR.reserve(P.mkRun(rp), len) == P.mkRun(p2) : NR.Run}
    & ({RN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(rp) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))
  {WB.st_o(WB.step_st(Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))), WB.st_stop(WB.step_st(Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))))) == True{} : Bool}

def chunk_mb_x(dfs,fa, O, N, c, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv, r):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (+hs, ho) = r3
  +md = {S.MBP{rp} : S.MdP}
  +md2 = {S.MBP{rp2} : S.MdP}
  +hw2 = DO.x9_mk(S.md_ok(md2), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md2, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hi2, DO.x9_1(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_4(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw))
  +q2 = {S.StP{o, md2, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +hg2 = Equal.trans(Bool, S.guard(O, N, q2), S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), True{},
    Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)), P.specRun(rp2), P.specRun(rp), hs), hg)
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), len), P.mkRun(rp2), e) :
    {WB.st_o(WB.step_st(Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))), WB.st_stop(WB.step_st(Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs))))) == True{} : Bool}
  fed_x(fa, O, N, c, q2, Norm.feed.k(o, S.mkMd(md2), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs), hb, hg2,
    F.core(dfs, fa, c, len, t, d, o, md2, pd, back, wp, fneed, hw2, hok, hv))



law chunk_md_x:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +c: String
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hg: {S.guard(O, N, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  {WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Pr.Chunk{C.BT(len, t)}))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Pr.Chunk{C.BT(len, t)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Pr.Chunk{C.BT(len, t)})))) == True{} : Bool}

def chunk_md_x(dfs,fa, O, N, c, o, md, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv):
  match md:
    case S.MBP{+rp}:
      chunk_mb_x(dfs, fa, O, N, c, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv,
        RN.run_reserve(rp, len, DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw)))
    case S.MSP{+s, +qs, +ql, +code}:
      +q = {S.StP{o, S.MSP{s, qs, ql, code}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      fed_x(fa, O, N, c, q, Norm.feed.k(o, S.mkMd(S.MSP{s, qs, ql, code}), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs), hb, hg,
        F.core(dfs, fa, c, len, t, d, o, S.MSP{s, qs, ql, code}, pd, back, wp, fneed, hw, hok, hv))



# A dirty piece's step, from a state waiting for more.
law chunk_x:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +c: String
  for +p: S.StP
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
  {WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)}))) == S.StP.o(p) : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)})))) == True{} : Bool}

def chunk_x(fa, O, N, c, p, len, t, d, hb, hm, hg, hok, hv):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd({WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})))) == True{} : Bool},
        PB.false_ne_true(WB.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd({WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})))) == True{} : Bool},
        PB.false_ne_true(WB.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd({WB.st_o(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}))) == o : B.Opts} & {WB.live_k(WB.step_nx(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})), WB.st_stop(WB.step_st(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)})))) == True{} : Bool},
        PB.false_ne_true(WB.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      chunk_md_x(dfs, fa, O, N, c, o, md, pd, back, wp, fneed, len, t, d, hb, WB.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hg, hok, hv)
