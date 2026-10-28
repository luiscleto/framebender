import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ./norm_run.bend as NR
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD

# Helpers for proof_e_wrap.bend (area E1): Q's step with no batch after it,
# Q's state looked at by the wrapper (quiet, opts), and list facts.

# Q's step, no batch
# ==================

# A step of Q that keeps phase B's guarantee is a wrapper step with no batch.
law g2_none:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for s: Norm.Step
  for h: DO.StepG2(fa, T, cs, O, N, ef, s)
  WD.StepGW(fa, T, cs, O, N, ef, W.wrap(s, W.BNone{}))

def g2_none(fa, T, cs, O, N, ef, s, h):
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
      (t, (WD.WPic{p2, WD.BNoneP{}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BNone{}}, st, S.mkSt(fa, p2), est),
        ({==}, (gd, (rep, (hmo, hef))))))))
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
      (t, (WD.WPic{p2, WD.BNoneP{}}, (eout, (Equal.cong(Norm.St, W.St, z => W.St{z, W.BNone{}}, st, S.mkSt(fa, p2), est),
        ({==}, (gd, (rep, (wf, (hq, (hrq, (hmr, (hask, heof))))))))))))
    case Norm.Step{st, b, ns, Pr.Finish{+c}}:
      h

# Q's state, looked at
# ====================

def mdb(+m: S.MdP) -> Bool:
  match m:
    case S.MBP{+rp}:
      P.RunP.i(rp) && Bool.not(P.RunP.x(rp))
    case S.MSP{s, qs, ql, code}:
      False{}

def srcb(+sps: List<&2, P.SrcP>) -> Bool:
  match sps:
    case Nil{}:
      True{}
    case Con{sp, t}:
      False{}

def pdb(+pd: P.PdP) -> Bool:
  match pd:
    case P.PBP{len, t, d}:
      True{}
    case P.PSP{s}:
      False{}

# W.quiet's test on a picture.
def qb(+p: S.StP) -> Bool:
  match p:
    case S.StP{o, +md, +src, +pd, +eof, back, wp, +asked, +fneed}:
      mdb(md) && srcb(src) && pdb(pd) && Bool.not(eof) && Bool.not(fneed) && W.is_none(asked)

law md_ok_mk:
  for +md: S.MdP
  {(S.mkMd(md), mdb(md)) == W.md.ok(S.mkMd(md)) : Norm.Md & Bool}

def md_ok_mk(md):
  match md:
    case S.MBP{P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}}:
      {==}
    case S.MSP{+s, +qs, +ql, +code}:
      {==}

law src_nil_mk:
  for +src: List<&2, P.SrcP>
  {(P.mkSrcs(src), srcb(src)) == W.is_nil.src(P.mkSrcs(src)) : List<&1, Norm.Src> & Bool}

def src_nil_mk(src):
  match src:
    case Nil{}:
      {==}
    case Con{+sp, +t}:
      {==}

law pb_mk:
  for +pd: P.PdP
  {(P.mkPd(pd), pdb(pd)) == W.is_pb(P.mkPd(pd)) : Norm.Pd & Bool}

def pb_mk(pd):
  match pd:
    case P.PBP{+len, +t, +d}:
      {==}
    case P.PSP{+s}:
      {==}

law quiet_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {(S.mkSt(fa, p), qb(p)) == W.quiet(S.mkSt(fa, p)) : Norm.St & Bool}

def quiet_mk(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      %md_ok_mk(md) : {(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), qb(S.StP{o, md, src, pd, eof, back, wp, asked, fneed})) == W.quiet.k(o, _, W.is_nil.src(P.mkSrcs(src)), W.is_pb(P.mkPd(pd)), eof, back, PC.mkWin(fa, wp), asked, fneed) : Norm.St & Bool}
      %src_nil_mk(src) : {(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), qb(S.StP{o, md, src, pd, eof, back, wp, asked, fneed})) == W.quiet.k(o, (S.mkMd(md), mdb(md)), _, W.is_pb(P.mkPd(pd)), eof, back, PC.mkWin(fa, wp), asked, fneed) : Norm.St & Bool}
      %pb_mk(pd) : {(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed}), qb(S.StP{o, md, src, pd, eof, back, wp, asked, fneed})) == W.quiet.k(o, (S.mkMd(md), mdb(md)), (P.mkSrcs(src), srcb(src)), _, eof, back, PC.mkWin(fa, wp), asked, fneed) : Norm.St & Bool}
      {==}

law qb_stop:
  for +p: S.StP
  for +h: {qb(p) == True{} : Bool}
  {S.stopped(S.StP.md(p)) == False{} : Bool}

def qb_stop(p, h):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      +h5 = PB.and_true_l(mdb(S.MBP{rp}) && srcb(src) && pdb(pd) && Bool.not(eof) && Bool.not(fneed), W.is_none(asked), h)
      +h4 = PB.and_true_l(mdb(S.MBP{rp}) && srcb(src) && pdb(pd) && Bool.not(eof), Bool.not(fneed), h5)
      +h3 = PB.and_true_l(mdb(S.MBP{rp}) && srcb(src) && pdb(pd), Bool.not(eof), h4)
      +h2 = PB.and_true_l(mdb(S.MBP{rp}) && srcb(src), pdb(pd), h3)
      +h1 = PB.and_true_l(mdb(S.MBP{rp}), srcb(src), h2)
      DO.not_true(P.RunP.x(rp), PB.and_true_r(P.RunP.i(rp), Bool.not(P.RunP.x(rp)), h1))
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      Empty.absurd({S.stopped(S.MSP{s, qs, ql, code}) == False{} : Bool}, PB.false_ne_true(h))

law opts_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {(S.mkSt(fa, p), S.StP.o(p)) == W.opts(S.mkSt(fa, p)) : Norm.St & B.Opts}

def opts_mk(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

# more_ok's four tests (as proof_b_drive_step.bend's, which imports the pump).
def M3(+w: Bool, +se: Bool, +ne: Bool) -> Bool:
  w && se && ne

law mo_se:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {se == True{} : Bool}

def mo_se(w, se, ne, no, h):
  PB.and_true_r(w, se, PB.and_true_l(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h)))

law mo_ne:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {ne == True{} : Bool}

def mo_ne(w, se, ne, no, h):
  PB.and_true_r(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h))

law mo_no:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {no == True{} : Bool}

def mo_no(w, se, ne, no, h):
  PB.and_true_r(M3(w, se, ne), no, h)

law mo_w:
  for +w: Bool
  for +se: Bool
  for +ne: Bool
  for +no: Bool
  for +h: {w && se && ne && no == True{} : Bool}
  {w == True{} : Bool}

def mo_w(w, se, ne, no, h):
  PB.and_true_l(w, se, PB.and_true_l(Bool.and(w, se), ne, PB.and_true_l(M3(w, se, ne), no, h)))

# more_ok carries over to a state with the same input, end flag and asked.
law more_keep:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +p2: S.StP
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +wf: {S.WF(fa, p2) == True{} : Bool}
  for +esrc: {S.StP.src(p2) == S.StP.src(p) : List<&2, P.SrcP>}
  for +eeof: {S.StP.eof(p2) == S.StP.eof(p) : Bool}
  for +eask: {S.StP.asked(p2) == S.StP.asked(p) : Maybe<&2, List<&2, Pr.Req>>}
  {DR.more_ok(fa, p2) == True{} : Bool}

def more_keep(fa, p, p2, hm, wf, esrc, eeof, eask):
  +w = S.WF(fa, p)
  +se = S.src_empty(S.StP.src(p))
  +ne = Bool.not(S.StP.eof(p))
  +no = Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p))
  DO.mo_mk(S.WF(fa, p2), S.src_empty(S.StP.src(p2)), Bool.not(S.StP.eof(p2)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p2)), wf,
    Equal.trans(Bool, S.src_empty(S.StP.src(p2)), se, True{}, Equal.cong(List<&2, P.SrcP>, Bool, z => S.src_empty(z), S.StP.src(p2), S.StP.src(p), esrc), mo_se(w, se, ne, no, hm)),
    Equal.trans(Bool, Bool.not(S.StP.eof(p2)), ne, True{}, Equal.cong(Bool, Bool, z => Bool.not(z), S.StP.eof(p2), S.StP.eof(p), eeof), mo_ne(w, se, ne, no, hm)),
    Equal.trans(Bool, Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p2)), no, True{}, Equal.cong(Maybe<&2, List<&2, Pr.Req>>, Bool, z => Maybe.is_none(&2, List<&2, Pr.Req>, z), S.StP.asked(p2), S.StP.asked(p), eask), mo_no(w, se, ne, no, hm)))

# Lists
# =====

law rev_encs:
  for +xs: List<&2, String>
  for +acc: List<&2, String>
  {W.rev_b(PT.encs(xs), PT.encs(acc)) == PT.encs(List.reverse.go(&2, String, xs, acc)) : List<&1, D.Bytes>}

def rev_encs(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      rev_encs(t, x <> acc)

# Norm.out keeps the options and whether the run stopped (code level)
# ===================================================================

def run_x(r: NR.Run) -> Bool:
  match r:
    case NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}:
      x

def md_stop(md: Norm.Md) -> Bool:
  match md:
    case Norm.MB{r}:
      run_x(r)
    case Norm.MS{s, qs, ql, code}:
      R.RunSt.halt(s) || Maybe.is_some(&2, Nat, code)

def st_stop(st: Norm.St) -> Bool:
  match st:
    case Norm.St{o, md, src, pend, eof, back, win, asked, fneed}:
      md_stop(md)

def st_o(st: Norm.St) -> B.Opts:
  match st:
    case Norm.St{o, md, src, pend, eof, back, win, asked, fneed}:
      o

def step_st(s: Norm.Step) -> Norm.St:
  match s:
    case Norm.Step{st, b, ns, nx}:
      st

def step_nx(s: Norm.Step) -> Pr.Next:
  match s:
    case Norm.Step{st, b, ns, nx}:
      nx

law stop_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {st_stop(S.mkSt(fa, p)) == S.stopped(S.StP.md(p)) : Bool}

def stop_mk(fa, p):
  match p:
    case S.StP{+o, S.MBP{P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

law o_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {st_o(S.mkSt(fa, p)) == S.StP.o(p) : B.Opts}

def o_mk(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

law outk_mb:
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
  for nx: Pr.Next
  {(st_stop(step_st(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, nx))), (st_o(step_st(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, nx))), step_nx(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, nx)))) == (run_x(r), (o, nx)) : Bool & (B.Opts & Pr.Next)}

def outk_mb(p, r, o, src, pend, eof, back, win, asked, fneed, nx):
  match p r:
    case (out, ob) NR.Run{n, i, h, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, x}:
      {==}

law outk_ms:
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
  for nx: Pr.Next
  {(st_stop(step_st(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, nx))), (st_o(step_st(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, nx))), step_nx(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, nx)))) == (R.RunSt.halt(s) || Maybe.is_some(&2, Nat, code), (o, nx)) : Bool & (B.Opts & Pr.Next)}

def outk_ms(c, s, ns, code, o, src, pend, eof, back, win, asked, fneed, nx):
  match c:
    case Norm.Cut2{now, later}:
      {==}

law ol_x:
  for +o: B.Opts
  for md: Norm.Md
  for p: List<&1, Norm.Src> & U32
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for nx: Pr.Next
  {(st_stop(step_st(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, nx))), (st_o(step_st(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, nx))), step_nx(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, nx)))) == (md_stop(md), (o, nx)) : Bool & (B.Opts & Pr.Next)}

def ol_x(o, md, p, pend, eof, back, win, asked, fneed, nx):
  match md:
    case Norm.MB{NR.Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, +x}}:
      match p:
        case (src, +n):
          outk_mb(NR.take.if(U32.is_zero(ow), ow, n, ob), NR.Run{nn, i, h, c, cb, e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, x}, o, src, pend, eof, back, win, asked, fneed, nx)
    case Norm.MS{R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, +rns, +rx}, qs, ql, +code}:
      match p:
        case (src, +n):
          outk_ms(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, Nil{}, rx}, rns, code, o, src, pend, eof, back, win, asked, fneed, nx)

law out_x:
  for st: Norm.St
  for nx: Pr.Next
  {(st_stop(step_st(Norm.out(st, nx))), (st_o(step_st(Norm.out(st, nx))), step_nx(Norm.out(st, nx)))) == (st_stop(st), (st_o(st), nx)) : Bool & (B.Opts & Pr.Next)}

def out_x(st, nx):
  match st:
    case Norm.St{+o, md, src, pend, eof, +back, win, asked, +fneed}:
      ol_x(o, md, Norm.left(src), pend, eof, back, win, asked, fneed, nx)

def fst_b(q: Bool & (B.Opts & Pr.Next)) -> Bool:
  (a, b) = q
  a

def snd_o(q: Bool & (B.Opts & Pr.Next)) -> B.Opts:
  (a, b) = q
  (o, n) = b
  o

def thd_n(q: Bool & (B.Opts & Pr.Next)) -> Pr.Next:
  (a, b) = q
  (o, n) = b
  n

# Q.out from a picture whose run has not stopped: the state after has not.
law out_stop:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for nx: Pr.Next
  for +hl: {S.stopped(S.StP.md(p)) == False{} : Bool}
  {st_stop(step_st(Norm.out(S.mkSt(fa, p), nx))) == False{} : Bool}

def out_stop(fa, p, nx, hl):
  Equal.trans(Bool, st_stop(step_st(Norm.out(S.mkSt(fa, p), nx))), st_stop(S.mkSt(fa, p)), False{},
    Equal.cong(Bool & (B.Opts & Pr.Next), Bool, z => fst_b(z), (st_stop(step_st(Norm.out(S.mkSt(fa, p), nx))), (st_o(step_st(Norm.out(S.mkSt(fa, p), nx))), step_nx(Norm.out(S.mkSt(fa, p), nx)))), (st_stop(S.mkSt(fa, p)), (st_o(S.mkSt(fa, p)), nx)), out_x(S.mkSt(fa, p), nx)),
    Equal.trans(Bool, st_stop(S.mkSt(fa, p)), S.stopped(S.StP.md(p)), False{}, stop_mk(fa, p), hl))

# Q.out keeps the options.
law out_o:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for nx: Pr.Next
  {st_o(step_st(Norm.out(S.mkSt(fa, p), nx))) == S.StP.o(p) : B.Opts}

def out_o(fa, p, nx):
  Equal.trans(B.Opts, st_o(step_st(Norm.out(S.mkSt(fa, p), nx))), st_o(S.mkSt(fa, p)), S.StP.o(p),
    Equal.cong(Bool & (B.Opts & Pr.Next), B.Opts, z => snd_o(z), (st_stop(step_st(Norm.out(S.mkSt(fa, p), nx))), (st_o(step_st(Norm.out(S.mkSt(fa, p), nx))), step_nx(Norm.out(S.mkSt(fa, p), nx)))), (st_stop(S.mkSt(fa, p)), (st_o(S.mkSt(fa, p)), nx)), out_x(S.mkSt(fa, p), nx)),
    o_mk(fa, p))

# A state known by a picture: its stop flag and options are the picture's.
law stop_pic:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for -st: Norm.St
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +h: {st_stop(st) == False{} : Bool}
  {S.stopped(S.StP.md(p2)) == False{} : Bool}

def stop_pic(fa, p2, st, est, h):
  Equal.trans(Bool, S.stopped(S.StP.md(p2)), st_stop(S.mkSt(fa, p2)), False{}, Equal.sym(Bool, st_stop(S.mkSt(fa, p2)), S.stopped(S.StP.md(p2)), stop_mk(fa, p2)),
    Equal.trans(Bool, st_stop(S.mkSt(fa, p2)), st_stop(st), False{}, Equal.cong(Norm.St, Bool, z => st_stop(z), S.mkSt(fa, p2), st, Equal.sym(Norm.St, st, S.mkSt(fa, p2), est)), h))

law o_pic:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for -st: Norm.St
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +o: B.Opts
  for +h: {st_o(st) == o : B.Opts}
  {S.StP.o(p2) == o : B.Opts}

def o_pic(fa, p2, st, est, o, h):
  Equal.trans(B.Opts, S.StP.o(p2), st_o(S.mkSt(fa, p2)), o, Equal.sym(B.Opts, st_o(S.mkSt(fa, p2)), S.StP.o(p2), o_mk(fa, p2)),
    Equal.trans(B.Opts, st_o(S.mkSt(fa, p2)), st_o(st), o, Equal.cong(Norm.St, B.Opts, z => st_o(z), S.mkSt(fa, p2), st, Equal.sym(Norm.St, st, S.mkSt(fa, p2), est)), h))

# A step guarantee's eof flag, rewritten.
law g2_ef:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +e1: Bool
  for +e2: Bool
  for s: Norm.Step
  for +he: {e1 == e2 : Bool}
  for h: DO.StepG2(fa, T, cs, O, N, e1, s)
  DO.StepG2(fa, T, cs, O, N, e2, s)

def g2_ef(fa, T, cs, O, N, e1, e2, s, he, h):
  %he : DO.StepG2(fa, T, cs, O, N, _, s)
  h

# A step's "has not stopped when it asks for more".
def live_k(nx: Pr.Next, +stop: Bool) -> Bool:
  match nx:
    case Pr.More{}:
      Bool.not(stop)
    case _:
      True{}

# Q's line count (the String mode: 0), as W.q.n reads it.
def nbm(+m: S.MdP) -> Nat:
  match m:
    case S.MBP{+rp}:
      P.RunP.n(rp)
    case S.MSP{s, qs, ql, code}:
      0n

law qn_mk:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {(S.mkSt(fa, p), nbm(S.StP.md(p))) == W.q.n(S.mkSt(fa, p)) : Norm.St & Nat}

def qn_mk(fa, p):
  match p:
    case S.StP{+o, S.MBP{P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

law and2:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {a && b == True{} : Bool}

def and2(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {_ && b == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {True{} && _ == True{} : Bool}
  {==}
