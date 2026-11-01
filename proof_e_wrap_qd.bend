import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
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
import ./proof_b_drive_pump.bend as DP
import lawful-bytes@0.1.1.0/bytes.bend as BY
import ./proof_base.bend as PB
import ./proof_b_run.bend as RN
import ./proof_e_qif.bend as QI
import ./proof_e_qif_fed.bend as F
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_qx.bend as QX
import ./proof_b_enc.bend as EN

# Helpers for proof_e_wrap.bend (area E1, -m): a step of Q keeps the header
# definitions of the text still to come (S.DEFS), which the threads machine
# gives Q's tasks. The step's state is read at code level (st_defs: S.DEFS
# on Norm.St, equal to it on pictures, mk_defs), so the fact joins phase B's
# step guarantee (DO.StepG2) without changing it. Along AdvG for the pump
# (its Moved, and the definitions clause of Ended and Yield), as
# proof_e_wrap_qx.bend does for the options. A step that ends the run
# (Finish) claims nothing.

# S.DEFS on the code's state
# ==========================

def src_text(s: Norm.Src) -> String:
  match s:
    case Norm.SB{b, +at}:
      NR.chars(List.drop(&2, U32, D.view(b), U32.to_nat(at)))
    case Norm.SL{+p}:
      p ++ "\n"
    case Norm.SP{b, +at}:
      NR.chars(List.drop(&2, U32, D.view(b), U32.to_nat(at)))
    case Norm.SR{+l}:
      B.Line.text(l)

def srcs_text(src: List<&1, Norm.Src>) -> String:
  match src:
    case Nil{}:
      ""
    case Con{s, t}:
      src_text(s) ++ srcs_text(t)

# The sources after the records of a split line (S.plain).
def plain_c(src: List<&1, Norm.Src>) -> List<&1, Norm.Src>:
  match src:
    case Nil{}:
      Nil{}
    case Con{Norm.SP{b, at}, r}:
      plain_c(r)
    case Con{Norm.SR{l}, r}:
      plain_c(r)
    case Con{Norm.SB{b, +at}, r}:
      Con{Norm.SB{b, at}, r}
    case Con{Norm.SL{+q}, r}:
      Con{Norm.SL{q}, r}

def pd_text(pd: Norm.Pd) -> String:
  match pd:
    case Norm.PB{b}:
      NR.chars(D.view(b))
    case Norm.PS{+s}:
      s

def md_ib(md: Norm.Md) -> Bool:
  match md:
    case Norm.MB{NR.Run{nn, +i, h, c, cb, e, l, f, b, bn, tl, k, ob, ow, ns, x}}:
      i
    case Norm.MS{s, qs, ql, code}:
      R.RunSt.inbody(s)

def st_defs(st: Norm.St, +cs: List<&2, String>) -> B.Defs:
  match st:
    case Norm.St{o, md, src, pend, +eof, back, win, asked, fneed, +dfs}:
      L.defs.go(B.Text.lines(srcs_text(plain_c(src)) ++ (pd_text(pend) ++ S.concat_if(eof, cs))), md_ib(md), dfs)

law src_one:
  for +sp: P.SrcP
  for +X: String
  {src_text(P.mkSrc(sp)) ++ X == P.srctext(sp) ++ X : String}

def src_one(sp, X):
  match sp:
    case P.SBP{+len, +t, +d, +at}:
      {==}
    case P.SLP{+q}:
      {==}
    case P.SPP{+len, +t, +d, +at}:
      {==}
    case P.SRP{+l}:
      {==}

law srcs_all:
  for +r: List<&2, P.SrcP>
  {srcs_text(P.mkSrcs(r)) == P.srcstext(r) : String}

def srcs_all(r):
  match r:
    case Nil{}:
      {==}
    case Con{+sp, +t}:
      %Equal.sym(String, srcs_text(P.mkSrcs(t)), P.srcstext(t), srcs_all(t)) : {src_text(P.mkSrc(sp)) ++ _ == P.srcstext(Con{sp, t}) : String}
      src_one(sp, P.srcstext(t))

law srcs_eq:
  for +src: List<&2, P.SrcP>
  {srcs_text(plain_c(P.mkSrcs(src))) == P.srcstext(S.plain(src)) : String}

def srcs_eq(src):
  match src:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +r}:
      srcs_all(Con{P.SBP{len, t, d, at}, r})
    case Con{P.SLP{+q}, +r}:
      srcs_all(Con{P.SLP{q}, r})
    case Con{P.SPP{+len, +t, +d, +at}, +r}:
      srcs_eq(r)
    case Con{P.SRP{+l}, +r}:
      srcs_eq(r)

law pd_eq:
  for +pd: P.PdP
  {pd_text(P.mkPd(pd)) == P.pdtext(pd) : String}

def pd_eq(pd):
  match pd:
    case P.PBP{+len, +t, +d}:
      {==}
    case P.PSP{+s}:
      {==}

law ib_mb:
  for +rp: P.RunP
  {md_ib(S.mkMd(S.MBP{rp})) == R.RunSt.inbody(S.smd(S.MBP{rp})) : Bool}

def ib_mb(rp):
  match rp:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law ib_ms:
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Maybe<&2, Nat>
  {md_ib(S.mkMd(S.MSP{s, qs, ql, code})) == R.RunSt.inbody(S.smd(S.MSP{s, qs, ql, code})) : Bool}

def ib_ms(s, qs, ql, code):
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law ib_eq:
  for +md: S.MdP
  {md_ib(S.mkMd(md)) == R.RunSt.inbody(S.smd(md)) : Bool}

def ib_eq(md):
  match md:
    case S.MBP{+rp}:
      ib_mb(rp)
    case S.MSP{+s, +qs, +ql, +code}:
      ib_ms(s, qs, ql, code)

# On a pictured state, st_defs is S.DEFS.
law mk_defs:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +cs: List<&2, String>
  {st_defs(S.mkSt(fa, p), cs) == S.DEFS(p, cs) : B.Defs}

def mk_defs(fa, p, cs):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +R0 = S.concat_if(eof, cs)
      +q = {S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      %Equal.sym(String, srcs_text(plain_c(P.mkSrcs(src))), P.srcstext(S.plain(src)), srcs_eq(src)) :
        {L.defs.go(B.Text.lines(_ ++ (pd_text(P.mkPd(pd)) ++ R0)), md_ib(S.mkMd(md)), dfs) == S.DEFS(q, cs) : B.Defs}
      %Equal.sym(String, pd_text(P.mkPd(pd)), P.pdtext(pd), pd_eq(pd)) :
        {L.defs.go(B.Text.lines(P.srcstext(S.plain(src)) ++ (_ ++ R0)), md_ib(S.mkMd(md)), dfs) == S.DEFS(q, cs) : B.Defs}
      %Equal.sym(Bool, md_ib(S.mkMd(md)), R.RunSt.inbody(S.smd(md)), ib_eq(md)) :
        {L.defs.go(B.Text.lines(P.srcstext(S.plain(src)) ++ (P.pdtext(pd) ++ R0)), _, dfs) == S.DEFS(q, cs) : B.Defs}
      {==}

# What a step says: unless it ends the run, its state's definitions are D.
def PD(-s: Norm.Step, +cs: List<&2, String>, +D: B.Defs) -> Type:
  {WD.dsel(WB.step_nx(s), st_defs(WB.step_st(s), cs), D) == D : B.Defs}

def dsel_k(+nx: Pr.Next, +d1: B.Defs, +d2: B.Defs, +h: {d1 == d2 : B.Defs}) -> {WD.dsel(nx, d1, d2) == d2 : B.Defs}:
  match nx:
    case Pr.More{}:
      h
    case Pr.Ask{+rs}:
      h
    case Pr.Finish{+c}:
      {==}

law pd_rw:
  for -s: Norm.Step
  for +cs: List<&2, String>
  for +D1: B.Defs
  for +D2: B.Defs
  for +he: {D1 == D2 : B.Defs}
  for h: PD(s, cs, D1)
  PD(s, cs, D2)

def pd_rw(s, cs, D1, D2, he, h):
  %he : PD(s, cs, _)
  h

# Two states with the same mode, definitions read and text still to come.
def defs_text(+p: S.StP, +q: S.StP, +cs1: List<&2, String>, +cs2: List<&2, String>,
  +eqi: {S.intext(q, cs2) == S.intext(p, cs1) : String},
  +emd: {S.StP.md(q) == S.StP.md(p) : S.MdP},
  +edf: {S.StP.dfs(q) == S.StP.dfs(p) : B.Defs}) ->
  {S.DEFS(q, cs2) == S.DEFS(p, cs1) : B.Defs}:
  %Equal.sym(String, S.intext(q, cs2), S.intext(p, cs1), eqi) : {L.defs.go(B.Text.lines(_), R.RunSt.inbody(S.smd(S.StP.md(q))), S.StP.dfs(q)) == S.DEFS(p, cs1) : B.Defs}
  %Equal.sym(S.MdP, S.StP.md(q), S.StP.md(p), emd) : {L.defs.go(B.Text.lines(S.intext(p, cs1)), R.RunSt.inbody(S.smd(_)), S.StP.dfs(q)) == S.DEFS(p, cs1) : B.Defs}
  %Equal.sym(B.Defs, S.StP.dfs(q), S.StP.dfs(p), edf) : {L.defs.go(B.Text.lines(S.intext(p, cs1)), R.RunSt.inbody(S.smd(S.StP.md(p))), _) == S.DEFS(p, cs1) : B.Defs}
  {==}

# Moved keeps the definitions in every mode.
def moved_md(+m: S.MdP, +m2: S.MdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +p2: S.StP, mv: S.Moved.md(m, m2, fa, cs, p, p2)) ->
  {S.DEFS(p2, cs) == S.DEFS(p, cs) : B.Defs}:
  match m m2:
    case S.MBP{+rp} S.MBP{+rp2}:
      (ls, r1) = mv
      (h1, r2) = r1
      (h2, h3) = r2
      h3
    case S.MBP{+rp} S.MSP{+s, +qs, +ql, +code}:
      mv
    case S.MSP{+s, +qs, +ql, +code} S.MBP{+rp2}:
      mv
    case S.MSP{+s, +qs, +ql, +code} S.MSP{+s2, +qs2, +ql2, +code2}:
      mv

def moved_defs(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p: S.StP, +p2: S.StP, mv: S.Moved(fa, cs, p, p2)) ->
  {S.DEFS(p2, cs) == S.DEFS(p, cs) : B.Defs}:
  moved_md(S.StP.md(p), S.StP.md(p2), fa, cs, p, p2, mv)

# out, finish, idle
# =================

def leftN(+sps: List<&2, P.SrcP>) -> U32:
  match sps:
    case Nil{}:
      0
    case Con{P.SBP{+len, t, d, +at}, +rest}:
      ((len - at : U32) + leftN(rest) : U32)
    case Con{P.SLP{q}, +rest}:
      (0 + leftN(rest) : U32)
    case Con{P.SPP{+len, t, d, +at}, +rest}:
      ((len - at : U32) + leftN(rest) : U32)
    case Con{P.SRP{l}, +rest}:
      (0 + leftN(rest) : U32)

law left_eq:
  for +sps: List<&2, P.SrcP>
  {Norm.left(P.mkSrcs(sps)) == (P.mkSrcs(sps), leftN(sps)) : List<&1, Norm.Src> & U32}

def left_eq(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), leftN(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SB{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SBP{len, t, d, at}) <> P.mkSrcs(rest), leftN(P.SBP{len, t, d, at} <> rest)) : List<&1, Norm.Src> & U32}
      {==}
    case Con{P.SLP{+q}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), leftN(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SL{q}, 0), _) == (Norm.SL{q} <> P.mkSrcs(rest), leftN(P.SLP{q} <> rest)) : List<&1, Norm.Src> & U32}
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), leftN(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SP{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SPP{len, t, d, at}) <> P.mkSrcs(rest), leftN(P.SPP{len, t, d, at} <> rest)) : List<&1, Norm.Src> & U32}
      {==}
    case Con{P.SRP{+l}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(rest)), (P.mkSrcs(rest), leftN(rest)), left_eq(rest)) :
        {Norm.left.cons((Norm.SR{l}, 0), _) == (Norm.SR{l} <> P.mkSrcs(rest), leftN(P.SRP{l} <> rest)) : List<&1, Norm.Src> & U32}
      {==}

# What out hands to the driver next.
law out_nx_mb:
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
  for dfs: B.Defs
  for +nx: Pr.Next
  {WB.step_nx(Norm.out.k(Norm.md.take.k(NR.take.fin(p, r)), o, src, pend, eof, back, win, asked, fneed, dfs, nx)) == nx : Pr.Next}

def out_nx_mb(p, r, o, src, pend, eof, back, win, asked, fneed, dfs, nx):
  match p r:
    case (out, ob) NR.Run{n, i, hh, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, x}:
      {==}

law out_nx_ms:
  for c: Norm.Cut2
  for s: R.RunSt
  for ns: List<&2, B.Note>
  for code: Maybe<&2, Nat>
  for +o: B.Opts
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for dfs: B.Defs
  for +nx: Pr.Next
  {WB.step_nx(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, src, pend, eof, back, win, asked, fneed, dfs, nx)) == nx : Pr.Next}

def out_nx_ms(c, s, ns, code, o, src, pend, eof, back, win, asked, fneed, dfs, nx):
  match c:
    case Norm.Cut2{now, later}:
      {==}

law out_nx_l:
  for +o: B.Opts
  for md: Norm.Md
  for p: List<&1, Norm.Src> & U32
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for dfs: B.Defs
  for +nx: Pr.Next
  {WB.step_nx(Norm.out.left(o, md, p, pend, eof, back, win, asked, fneed, dfs, nx)) == nx : Pr.Next}

def out_nx_l(o, md, p, pend, eof, back, win, asked, fneed, dfs, nx):
  match md:
    case Norm.MB{NR.Run{nn, i, hh, c, cb, e, l, f, b, bn, tl, k, ob, +ow, ns, x}}:
      match p:
        case (src, +n):
          out_nx_mb(NR.take.if(U32.is_zero(ow), ow, n, ob), NR.Run{nn, i, hh, c, cb, e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, x}, o, src, pend, eof, back, win, asked, fneed, dfs, nx)
    case Norm.MS{R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, rns, rx}, qs, ql, code}:
      match p:
        case (src, +n):
          out_nx_ms(Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, Nil{}, rx}, rns, code, o, src, pend, eof, back, win, asked, fneed, dfs, nx)

law out_nx:
  for st: Norm.St
  for +nx: Pr.Next
  {WB.step_nx(Norm.out(st, nx)) == nx : Pr.Next}

def out_nx(st, nx):
  match st:
    case Norm.St{+o, md, src, pend, eof, +back, win, asked, +fneed, dfs}:
      out_nx_l(o, md, Norm.left(src), pend, eof, back, win, asked, fneed, dfs, nx)

# A step that ends the run claims nothing.
law fin_l:
  for st: Norm.St
  for +code: Nat
  for +cs: List<&2, String>
  for +D: B.Defs
  PD(Norm.out(st, Pr.Finish{code}), cs, D)

def fin_l(st, code, cs, D):
  %Equal.sym(Pr.Next, WB.step_nx(Norm.out(st, Pr.Finish{code})), Pr.Finish{code}, out_nx(st, Pr.Finish{code})) :
    {WD.dsel(_, st_defs(WB.step_st(Norm.out(st, Pr.Finish{code})), cs), D) == D : B.Defs}
  {==}

# out keeps the definitions.
law outk_mb_st:
  for +fa: List<&2, B.Contig>
  for pq: D.Bytes & D.Bytes
  for r: NR.Run
  for +o: B.Opts
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +nx: Pr.Next
  for +cs: List<&2, String>
  {st_defs(WB.step_st(Norm.out.k(Norm.md.take.k(NR.take.fin(pq, r)), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, nx)), cs) == st_defs(Norm.St{o, Norm.MB{r}, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}, cs) : B.Defs}

def outk_mb_st(fa, pq, r, o, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs):
  match pq r:
    case (out, ob) NR.Run{n, i, hh, c, cb, e, l, f, b, bn, tl, k, o0, ow, ns, x}:
      {==}

law outk_ms_st:
  for +fa: List<&2, B.Contig>
  for c: Norm.Cut2
  for +s: R.RunSt
  for +ns: List<&2, B.Note>
  for +code: Maybe<&2, Nat>
  for +qs: List<&2, String>
  for +ql: Nat
  for +o: B.Opts
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +nx: Pr.Next
  for +cs: List<&2, String>
  {st_defs(WB.step_st(Norm.out.k(Norm.ms.take.c(c, s, ns, code), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, nx)), cs) == st_defs(Norm.St{o, Norm.MS{s, qs, ql, code}, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}, cs) : B.Defs}

def outk_ms_st(fa, c, s, ns, code, qs, ql, o, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs):
  match c:
    case Norm.Cut2{now, later}:
      {==}

law out_st3:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +nx: Pr.Next
  for +cs: List<&2, String>
  for +n: U32
  {st_defs(WB.step_st(Norm.out.k(Norm.md.take(S.mkMd(md), n), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, nx)), cs) == st_defs(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), cs) : B.Defs}

def out_st3(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs, n):
  match md:
    case S.MBP{P.RunP{+rn, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}}:
      outk_mb_st(fa, NR.take.if(U32.is_zero(ow), ow, n, C.BT(obl, obt)), NR.Run{rn, i, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, BY.empty(0n), ow, ns, x}, o, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs)
    case S.MSP{R.RunSt{+rn, +ri, +rh, +rc, +re, +rl, +rb, +rk, +ro, +rns, +rx}, +qs, +ql, +code}:
      outk_ms_st(fa, Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), R.RunSt{rn, ri, rh, rc, re, rl, rb, rk, ro, Nil{}, rx}, rns, code, qs, ql, o, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs)

law out_st2:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +nx: Pr.Next
  for +cs: List<&2, String>
  {st_defs(WB.step_st(Norm.out(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), nx)), cs) == st_defs(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), cs) : B.Defs}

def out_st2(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs):
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), leftN(src)), left_eq(src)) :
    {st_defs(WB.step_st(Norm.out.left(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, nx)), cs) == st_defs(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), cs) : B.Defs}
  out_st3(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs, leftN(src))

law out_st:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +nx: Pr.Next
  for +cs: List<&2, String>
  {st_defs(WB.step_st(Norm.out(S.mkSt(fa, p), nx)), cs) == st_defs(S.mkSt(fa, p), cs) : B.Defs}

def out_st(fa, p, nx, cs):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      out_st2(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, nx, cs)

# out from a pictured state whose definitions are D.
law dk_out:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +nx: Pr.Next
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(p, cs) == D : B.Defs}
  PD(Norm.out(S.mkSt(fa, p), nx), cs, D)

def dk_out(fa, p, nx, cs, D, h):
  +d1 = st_defs(WB.step_st(Norm.out(S.mkSt(fa, p), nx)), cs)
  +ed = Equal.trans(B.Defs, d1, st_defs(S.mkSt(fa, p), cs), D, out_st(fa, p, nx, cs), Equal.trans(B.Defs, st_defs(S.mkSt(fa, p), cs), S.DEFS(p, cs), D, mk_defs(fa, p, cs), h))
  %Equal.sym(Pr.Next, WB.step_nx(Norm.out(S.mkSt(fa, p), nx)), nx, out_nx(S.mkSt(fa, p), nx)) : {WD.dsel(_, d1, D) == D : B.Defs}
  dsel_k(nx, d1, D, ed)

law finmb_d:
  for +o: B.Opts
  for pq: NR.Run & Nat
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for dfs: B.Defs
  for +cs: List<&2, String>
  for +D: B.Defs
  PD(Norm.fin.mb(o, pq, src, pend, eof, back, win, asked, fneed, dfs), cs, D)

def finmb_d(o, pq, src, pend, eof, back, win, asked, fneed, dfs, cs, D):
  match pq:
    case (run, +code):
      fin_l(Norm.St{o, Norm.MB{run}, src, pend, eof, back, win, asked, fneed, dfs}, code, cs, D)

law finmsgo_d:
  for +fa: List<&2, B.Contig>
  for +fits: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(S.StP{o, S.MSP{s, qs, ql, Some{code}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs) == D : B.Defs}
  PD(Norm.fin.ms.go(fits, o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs), cs, D)

def finmsgo_d(fa, fits, o, s, qs, ql, code, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h):
  match fits:
    case True{}:
      fin_l(S.mkSt(fa, S.StP{o, S.MSP{s, qs, ql, Some{code}}, src, pd, eof, back, wp, asked, fneed, dfs}), code, cs, D)
    case False{}:
      dk_out(fa, S.StP{o, S.MSP{s, qs, ql, Some{code}}, src, pd, eof, back, wp, asked, fneed, dfs}, Pr.Ask{Nil{}}, cs, D, h)

law finms_d:
  for +fa: List<&2, B.Contig>
  for rep: R.Report
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(S.StP{o, S.MSP{s, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs) == D : B.Defs}
  PD(Norm.fin.ms(rep, o, s, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs), cs, D)

def finms_d(fa, rep, o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h):
  match rep s:
    case R.Report{+out, +ns, +code} R.RunSt{+n, +i, +h0, +c, +e, +l, +b, +k, +o2, +ns0, +x}:
      finmsgo_d(fa, Norm.len_le(Norm.cat(List.reverse(&2, String, out <> qs)), 1073741824), o, R.RunSt{n, i, h0, c, e, l, b, k, "", ns, x}, out <> qs, Nat.add(ql, String.length(out)), code,
        src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h)

law finish_md:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +md: S.MdP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}, cs) == D : B.Defs}
  PD(Norm.finish(S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs})), cs, D)

def finish_md(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h):
  match md:
    case S.MBP{+rp}:
      finmb_d(o, NR.finish(P.mkRun(rp), R.Opts.w(o)), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, cs, D)
    case S.MSP{+s, +qs, +ql, None{}}:
      finms_d(fa, R.finish(s), o, s, qs, ql, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h)
    case S.MSP{+s, +qs, +ql, Some{+code}}:
      finmsgo_d(fa, Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824), o, s, qs, ql, code, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h)

law finish_d:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(p, cs) == D : B.Defs}
  PD(Norm.finish(S.mkSt(fa, p)), cs, D)

def finish_d(fa, p, cs, D, h):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      finish_md(fa, o, md, src, pd, eof, back, wp, asked, fneed, dfs, cs, D, h)

law idle_d:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {S.DEFS(p, cs) == D : B.Defs}
  PD(Norm.idle(S.mkSt(fa, p)), cs, D)

def idle_d(fa, p, cs, D, h):
  match p:
    case S.StP{+o, +md, +src, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      finish_d(fa, S.StP{o, md, src, pd, True{}, back, wp, asked, fneed, dfs}, cs, D, h)
    case S.StP{+o, +md, +src, +pd, False{}, +back, +wp, +asked, +fneed, +dfs}:
      dk_out(fa, S.StP{o, md, src, pd, False{}, back, wp, asked, fneed, dfs}, Pr.More{}, cs, D, h)

# The pump, along AdvG
# ====================

def IHD(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +D: B.Defs) -> Type:
  @q: S.StP -> @a: Norm.Adv -> S.AdvG(fa, T, cs, O, N, q, a) -> {S.DEFS(q, cs) == D : B.Defs} -> PD(Norm.pump(g, a), cs, D)

law pump_dr:
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
  for +D: B.Defs
  for +hd: {S.DEFS(p, cs) == D : B.Defs}
  for ih: IHD(g, fa, T, cs, O, N, D)
  PD(Norm.pump(g, Norm.pump.r(f2, a)), cs, D)

def pump_dr(f2, a, fa, T, cs, O, N, p, hb, ag, g, D, hd, ih):
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
      (eo, mvk) = a8
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.pump(g, Norm.pump.r(h, Norm.advance(_))), cs, D)
      pump_dr(h, Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg), g, D,
        Equal.trans(B.Defs, S.DEFS(p2, cs), S.DEFS(p, cs), D, moved_defs(fa, cs, p, p2, mv), hd), ih)
    case 0n Norm.Went{st}:
      ih(p, Norm.Went{st}, ag, hd)
    case _ Norm.Want{st, +r}:
      ih(p, Norm.Want{st, r}, ag, hd)
    case _ Norm.Idle{st}:
      ih(p, Norm.Idle{st}, ag, hd)
    case _ Norm.Ended{st}:
      ih(p, Norm.Ended{st}, ag, hd)
    case _ Norm.Yield{st}:
      ih(p, Norm.Yield{st}, ag, hd)

law pump_d:
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
  PD(Norm.pump(f, a), cs, S.DEFS(p, cs))

def pump_d(f, a, fa, T, cs, O, N, p, hb, ag):
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
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.out(_, Pr.Ask{Nil{}}), cs, S.DEFS(p, cs))
      dk_out(fa, p2, Pr.Ask{Nil{}}, cs, S.DEFS(p, cs), moved_defs(fa, cs, p, p2, mv))
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
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.pump(g, Norm.pump.fill(Norm.fuel.st(_))), cs, S.DEFS(p, cs))
      %Equal.sym(Norm.St & Nat, Norm.fuel.st(S.mkSt(fa, p2)), (S.mkSt(fa, p2), DP.fuelN(S.StP.src(p2))), DP.fst_eq(fa, p2)) :
        PD(Norm.pump(g, Norm.pump.fill(_)), cs, S.DEFS(p, cs))
      pump_dr(DP.fuelN(S.StP.src(p2)), Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg), g, S.DEFS(p, cs),
        moved_defs(fa, cs, p, p2, mv),
        +q => a3 => agq => +hq => pd_rw(Norm.pump(g, a3), cs, S.DEFS(q, cs), S.DEFS(p, cs), hq, pump_d(g, a3, fa, T, cs, O, N, q, hb, agq)))
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
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.out(_, Pr.Ask{r}), cs, S.DEFS(p, cs))
      dk_out(fa, p2, Pr.Ask{r}, cs, S.DEFS(p, cs), moved_defs(fa, cs, p, p2, mv))
    case _ Norm.Idle{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (esrc, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (ens, a8) = a7
      (eg, a9) = a8
      (eo, mvk) = a9
      (mv, kp) = mvk
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.idle(_), cs, S.DEFS(p, cs))
      idle_d(fa, p2, cs, S.DEFS(p, cs), moved_defs(fa, cs, p, p2, mv))
    case _ Norm.Ended{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (eask, a5) = a4
      (estop, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      (eo, dkp) = a8
      (hdd, kp) = dkp
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.finish(_), cs, S.DEFS(p, cs))
      finish_d(fa, p2, cs, S.DEFS(p, cs), hdd)
    case _ Norm.Yield{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (eask, a5) = a4
      (ens, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      (eo, dkp) = a8
      (hdd, kp) = dkp
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : PD(Norm.out(_, Pr.Ask{Nil{}}), cs, S.DEFS(p, cs))
      dk_out(fa, p2, Pr.Ask{Nil{}}, cs, S.DEFS(p, cs), hdd)

# go from a good state.
law go_d:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  PD(Norm.go(S.mkSt(fa, p)), cs, S.DEFS(p, cs))

def go_d(fa, cs, O, N, p, hb, hw, hg):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(src)), (P.mkSrcs(src), DP.fuelN(src)), DP.fuel_eq(src)) :
        PD(Norm.go.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs), cs, S.DEFS(q, cs))
      pump_d(1n+Nat.add(DP.fuelN(src), 1n), Norm.advance(S.mkSt(fa, q)), fa, S.report(fa, cs, O, N, q), cs, O, N, q, hb,
        SA.adv_ok(fa, S.report(fa, cs, O, N, q), cs, O, N, q, hb, hw, {==}, hg))

# A step given answers or a piece
# ===============================

law sw_defs:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for as: List<&1, Pr.Ans>
  for +cs: List<&2, String>
  {st_defs(Norm.set_win(S.mkSt(fa, p), as), cs) == st_defs(S.mkSt(fa, p), cs) : B.Defs}

def sw_defs(fa, p, as, cs):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      {==}

law ref_d2:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +cs: List<&2, String>
  for sw: &p2: S.StP -> ({Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)) == S.mkSt(fa, p2) : Norm.St}
    & ({S.WF(fa, p2) == True{} : Bool} & ({S.StP.md(p2) == S.StP.md(p) : S.MdP} & ({S.StP.o(p2) == S.StP.o(p) : B.Opts}
    & ({S.StP.src(p2) == S.StP.src(p) : List<&2, P.SrcP>} & ({QI.StP.pd(p2) == QI.StP.pd(p) : P.PdP} & ({S.StP.eof(p2) == S.StP.eof(p) : Bool}
    & {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>})))))))
  PD(Norm.go(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs))), cs, S.DEFS(p, cs))

def ref_d2(fa, O, N, p, rs, hb, hg, cs, sw):
  (+p2, s1) = sw
  (+e, s2) = s1
  (+wf2, s3) = s2
  (+emd, s4) = s3
  +hd = Equal.trans(B.Defs, S.DEFS(p2, cs), st_defs(S.mkSt(fa, p2), cs), S.DEFS(p, cs), Equal.sym(B.Defs, st_defs(S.mkSt(fa, p2), cs), S.DEFS(p2, cs), mk_defs(fa, p2, cs)),
    Equal.trans(B.Defs, st_defs(S.mkSt(fa, p2), cs), st_defs(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), cs), S.DEFS(p, cs),
      Equal.cong(Norm.St, B.Defs, z => st_defs(z, cs), S.mkSt(fa, p2), Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), Equal.sym(Norm.St, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), S.mkSt(fa, p2), e)),
      Equal.trans(B.Defs, st_defs(Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), cs), st_defs(S.mkSt(fa, p), cs), S.DEFS(p, cs), sw_defs(fa, p, M.truths(fa, rs), cs), mk_defs(fa, p, cs))))
  %Equal.sym(Norm.St, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), S.mkSt(fa, p2), e) : PD(Norm.go(_), cs, S.DEFS(p, cs))
  pd_rw(Norm.go(S.mkSt(fa, p2)), cs, S.DEFS(p2, cs), S.DEFS(p, cs), hd, go_d(fa, cs, O, N, p2, hb, wf2, QX.guard_md(O, N, p, p2, emd, hg)))

# A step given the truthful answers to what a good state asked.
law ref_d:
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
  for +cs: List<&2, String>
  PD(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), cs, S.DEFS(p, cs))

def ref_d(fa, O, N, p, rs, hb, hw, ha, hq, hp, hmr, hg, cs):
  ref_d2(fa, O, N, p, rs, hb, hg, cs, QI.set_win_ok(fa, p, rs, hb, hw, ha, hq, hp, hmr))

# The fed state, then go.
law fed_d:
  for +fa: List<&2, B.Contig>
  for +O: String
  for +N: List<&2, B.Note>
  for +c: String
  for +q: S.StP
  for -X: Norm.St
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hg: {S.guard(O, N, q) == True{} : Bool}
  for f: F.Fed(fa, c, q, X)
  for +cs: List<&2, String>
  PD(Norm.go(X), cs, S.DEFS(q, c <> cs))

def fed_d(fa, O, N, c, q, X, hb, hg, f, cs):
  (+p1, f1) = f
  (e, f2) = f1
  (+hw, f3) = f2
  (+hmd, f4) = f3
  (eo, f5) = f4
  (ea, f6) = f5
  (eef, f7) = f6
  (+edf, f8) = f7
  (er, ftx) = f8
  %Equal.sym(Norm.St, X, S.mkSt(fa, p1), e) : PD(Norm.go(_), cs, S.DEFS(q, c <> cs))
  pd_rw(Norm.go(S.mkSt(fa, p1)), cs, S.DEFS(p1, cs), S.DEFS(q, c <> cs), defs_text(q, p1, c <> cs, cs, ftx(cs), hmd, edf),
    go_d(fa, cs, O, N, p1, hb, hw, QX.guard_md(O, N, q, p1, hmd, hg)))

law chunk_mb_d:
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
  for +cs: List<&2, String>
  PD(Norm.go(Norm.feed.k(o, Norm.MB{NR.reserve(P.mkRun(rp), len)}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)), cs, S.DEFS(S.StP{o, S.MBP{rp}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}, c <> cs))

def chunk_mb_d(dfs, fa, O, N, c, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv, r, cs):
  (+rp2, r1) = r
  (+e, r2) = r1
  (+hi2, r3) = r2
  (+hs, ho) = r3
  +md = {S.MBP{rp} : S.MdP}
  +md2 = {S.MBP{rp2} : S.MdP}
  +hw2 = DO.x9_mk(S.md_ok(md2), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md2, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hi2, DO.x9_1(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_2(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_4(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_5(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_6(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_7(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw), DO.x9_8(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw))
  +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +q2 = {S.StP{o, md2, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
  +hg2 = Equal.trans(Bool, S.guard(O, N, q2), S.guard(O, N, q), True{},
    Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z) || (String.is_empty(O) && List.is_empty(&2, B.Note, N)), P.specRun(rp2), P.specRun(rp), hs), hg)
  +hd = {Equal.cong(R.RunSt, B.Defs, z => L.defs.go(B.Text.lines(S.intext(q, c <> cs)), R.RunSt.inbody(z), dfs), P.specRun(rp2), P.specRun(rp), hs) :
    {S.DEFS(q2, c <> cs) == S.DEFS(q, c <> cs) : B.Defs}}
  %Equal.sym(NR.Run, NR.reserve(P.mkRun(rp), len), P.mkRun(rp2), e) :
    PD(Norm.go(Norm.feed.k(o, Norm.MB{_}, Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)), cs, S.DEFS(q, c <> cs))
  pd_rw(Norm.go(Norm.feed.k(o, S.mkMd(md2), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs)), cs, S.DEFS(q2, c <> cs), S.DEFS(q, c <> cs), hd,
    fed_d(fa, O, N, c, q2, Norm.feed.k(o, S.mkMd(md2), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs), hb, hg2,
      F.core(dfs, fa, c, len, t, d, o, md2, pd, back, wp, fneed, hw2, hok, hv), cs))

law chunk_md_d:
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
  for +cs: List<&2, String>
  PD(Norm.step(S.mkSt(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}), Pr.Chunk{C.BT(len, t)}), cs, S.DEFS(S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs}, c <> cs))

def chunk_md_d(dfs, fa, O, N, c, o, md, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv, cs):
  match md:
    case S.MBP{+rp}:
      chunk_mb_d(dfs, fa, O, N, c, o, rp, pd, back, wp, fneed, len, t, d, hb, hw, hg, hok, hv,
        RN.run_reserve(rp, len, DO.x8_a(S.md_ok(S.MBP{rp}), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(S.MBP{rp}, wp), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(md, Nil{})), hw)), cs)
    case S.MSP{+s, +qs, +ql, +code}:
      +q = {S.StP{o, S.MSP{s, qs, ql, code}, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      fed_d(fa, O, N, c, q, Norm.feed.k(o, S.mkMd(S.MSP{s, qs, ql, code}), Nil{}, C.BT(len, t), Norm.Pd.len(P.mkPd(pd)), False{}, back, PC.mkWin(fa, wp), None{}, fneed, dfs), hb, hg,
        F.core(dfs, fa, c, len, t, d, o, S.MSP{s, qs, ql, code}, pd, back, wp, fneed, hw, hok, hv), cs)

# A piece's step, from a state waiting for more.
law chunk_d:
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
  for +cs: List<&2, String>
  PD(Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)}), cs, S.DEFS(p, c <> cs))

def chunk_d(fa, O, N, c, p, len, t, d, hb, hm, hg, hok, hv, cs):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(PD(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}), cs, S.DEFS(q, c <> cs)),
        PB.false_ne_true(WB.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed, dfs} : S.StP}
      Empty.absurd(PD(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}), cs, S.DEFS(q, c <> cs)),
        PB.false_ne_true(WB.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed, dfs} : S.StP}
      Empty.absurd(PD(Norm.step(S.mkSt(fa, q), Pr.Chunk{C.BT(len, t)}), cs, S.DEFS(q, c <> cs)),
        PB.false_ne_true(WB.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed, +dfs}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed, dfs} : S.StP}
      chunk_md_d(dfs, fa, O, N, c, o, md, pd, back, wp, fneed, len, t, d, hb, WB.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hg, hok, hv, cs)

# A step's guarantee and its definitions: Q's new state has them.
law pd_pic:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for -st: Norm.St
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +cs: List<&2, String>
  for +D: B.Defs
  for +h: {st_defs(st, cs) == D : B.Defs}
  {S.DEFS(p2, cs) == D : B.Defs}

def pd_pic(fa, p2, st, est, cs, D, h):
  +h2 = {%est : {st_defs(_, cs) == D : B.Defs}; h : {st_defs(S.mkSt(fa, p2), cs) == D : B.Defs}}
  Equal.trans(B.Defs, S.DEFS(p2, cs), st_defs(S.mkSt(fa, p2), cs), D, Equal.sym(B.Defs, st_defs(S.mkSt(fa, p2), cs), S.DEFS(p2, cs), mk_defs(fa, p2, cs)), h2)

# PD, as g2_none takes it.
def pd_hd(+fa: List<&2, B.Contig>, -s: Norm.Step, +cs: List<&2, String>, +D: B.Defs, h: PD(s, cs, D), +ef: Bool) ->
  @p2: S.StP -> {WB.step_st(s) == S.mkSt(fa, p2) : Norm.St} -> {ef == False{} : Bool} -> {WD.dsel(WB.step_nx(s), S.DEFS(p2, cs), D) == D : B.Defs}:
  +p2 => +e => hf =>
    {%Equal.trans(B.Defs, st_defs(WB.step_st(s), cs), st_defs(S.mkSt(fa, p2), cs), S.DEFS(p2, cs), Equal.cong(Norm.St, B.Defs, z => st_defs(z, cs), WB.step_st(s), S.mkSt(fa, p2), e), mk_defs(fa, p2, cs)) :
       {WD.dsel(WB.step_nx(s), _, D) == D : B.Defs};
     h : {WD.dsel(WB.step_nx(s), S.DEFS(p2, cs), D) == D : B.Defs}}

# A piece's step (the piece as the driver gives it), from a state waiting for more.
def chunk_enc_d2(+fa: List<&2, B.Contig>, +O: String, +N: List<&2, B.Note>, +c: String, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +cs: List<&2, String>,
  r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))) ->
  PD(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), cs, S.DEFS(p, c <> cs)):
  (+hok, r1) = r
  (+hv, r2) = r1
  %Equal.sym(D.Bytes, E.enc(c), C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), EN.enc_bt(c)) :
    PD(Norm.step(S.mkSt(fa, p), Pr.Chunk{_}), cs, S.DEFS(p, c <> cs))
  chunk_d(fa, O, N, c, p, U32.from_nat(String.length(c)), EN.enc_t(c), E.depth(String.length(c)), hb, hm, hg, hok, hv, cs)

def chunk_enc_d(+fa: List<&2, B.Contig>, +O: String, +N: List<&2, B.Note>, +c: String, +p: S.StP,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  +cs: List<&2, String>) ->
  PD(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), cs, S.DEFS(p, c <> cs)):
  chunk_enc_d2(fa, O, N, c, p, hb, hm, hg, cs, EN.enc_ok(c, hcb, hcn))
