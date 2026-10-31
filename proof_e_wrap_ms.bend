import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_base.bend as PB
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY

# Helpers for proof_e_wrap.bend (area E1): once Q is in the String mode,
# advance keeps it there (code level): a clean piece met in the String mode
# never merges.

def md_ms(md: Norm.Md) -> Bool:
  match md:
    case Norm.MB{r}:
      False{}
    case Norm.MS{s, qs, ql, code}:
      True{}

def st_ms(st: Norm.St) -> Bool:
  match st:
    case Norm.St{o, md, src, pend, eof, back, win, asked, fneed, +dfs}:
      md_ms(md)

def adv_ms(a: Norm.Adv) -> Bool:
  match a:
    case Norm.Went{st}:
      st_ms(st)
    case Norm.Want{st, r}:
      st_ms(st)
    case Norm.Idle{st}:
      st_ms(st)
    case Norm.Ended{st}:
      st_ms(st)
    case Norm.Yield{st}:
      st_ms(st)

def is_msp(+m: S.MdP) -> Bool:
  match m:
    case S.MBP{rp}:
      False{}
    case S.MSP{s, qs, ql, code}:
      True{}

law ms_out:
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  {md_ms(Norm.ms.out(s, qs, ql)) == True{} : Bool}

def ms_out(s, qs, ql):
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law ms_done:
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for cx: Norm.Cx
  for win: Norm.Win
  {adv_ms(Norm.ms.done(o, s, qs, ql, cx, win)) == True{} : Bool}

def ms_done(o, s, qs, ql, cx, win):
  match cx:
    case Norm.Cx{rest, pend, eof, dfs, hold}:
      ms_out(s, qs, ql)

law ms_want_k:
  for +ls: Norm.Ls
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for +reqs: List<&2, Pr.Req>
  for dfs: B.Defs
  {adv_ms(Norm.ms.want.k(ls, o, s, qs, ql, rest, pend, eof, back, win, reqs, dfs)) == True{} : Bool}

def ms_want_k(ls, o, s, qs, ql, rest, pend, eof, back, win, reqs, dfs):
  match ls:
    case Norm.LsT{+p}:
      {==}
    case Norm.LsR{+l}:
      {==}

law ms_want:
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for cx: Norm.Cx
  for win: Norm.Win
  for +reqs: List<&2, Pr.Req>
  for +back: Nat
  {adv_ms(Norm.ms.want(o, s, qs, ql, ls, cx, win, reqs, back)) == True{} : Bool}

def ms_want(o, s, qs, ql, ls, cx, win, reqs, back):
  match cx:
    case Norm.Cx{rest, pend, eof, dfs, hold}:
      ms_want_k(ls, o, s, qs, ql, rest, pend, eof, back, win, reqs, dfs)

law ms_body:
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +l: B.Line
  for +fs: List<&2, String>
  for cx: Norm.Cx
  for v: Norm.Vd
  {adv_ms(Norm.ms.body(o, s, qs, ql, ls, l, fs, cx, v)) == True{} : Bool}

def ms_body(o, s, qs, ql, ls, l, fs, cx, v):
  match v:
    case Norm.VRes{win, +r}:
      ms_done(o, R.body_line(r, R.tick(s), o, l, Norm.at_of(R.RunSt.n(R.tick(s)), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case Norm.VSame{win}:
      ms_done(o, R.body_line(B.Res{B.Normalized{}, B.Rec.pos(fs), B.Line.body(l), False{}}, R.tick(s), o, l, Norm.at_of(R.RunSt.n(R.tick(s)), fs), B.Rec.pos(fs)), qs, ql, cx, win)
    case Norm.VWant{win, +reqs, +back}:
      ms_want(o, s, qs, ql, ls, cx, win, reqs, back)

law ms_parts_k:
  for +pt: B.Parts
  for cx: Norm.Cx
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +l: B.Line
  for +back: Nat
  for win: Norm.Win
  {adv_ms(Norm.ms.parts.k(pt, cx, o, s, qs, ql, ls, l, back, win)) == True{} : Bool}

def ms_parts_k(pt, cx, o, s, qs, ql, ls, l, back, win):
  match pt:
    case B.Whole{}:
      ms_body(o, s, qs, ql, ls, l, J.pfs(B.Line.body(l)), cx, Norm.verdict(back, win, J.pfs(B.Line.body(l)), B.Line.body(l)))
    case B.Pieces{+ps}:
      ms_done(o, R.tick(s), qs, ql, Norm.Cx.push(cx, ps, B.Line.term(l)), win)
    case B.Unsplit{+c}:
      ms_body(o, s, qs, ql, ls, l, J.pfs(B.Line.body(l)), cx, Norm.vd.unsplit(c, R.Opts.strict(o), J.pfs(B.Line.body(l)), B.Line.body(l), Norm.verdict(back, win, J.pfs(B.Line.body(l)), B.Line.body(l))))

law ms_split:
  for +split: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +l: B.Line
  for +back: Nat
  for cx: Norm.Cx
  for win: Norm.Win
  {adv_ms(Norm.ms.split(split, o, s, qs, ql, ls, l, back, cx, win)) == True{} : Bool}

def ms_split(split, o, s, qs, ql, ls, l, back, cx, win):
  match split:
    case False{}:
      ms_body(o, s, qs, ql, ls, l, J.pfs(B.Line.body(l)), cx, Norm.verdict(back, win, J.pfs(B.Line.body(l)), B.Line.body(l)))
    case True{}:
      match cx:
        case Norm.Cx{rest, pend, eof, +dfs, hold}:
          ms_parts_k(B.Rec.parts(dfs, o, B.Line.body(l)), Norm.Cx{rest, pend, eof, dfs, hold}, o, s, qs, ql, ls, l, back, win)

law ms_line_k:
  for +inbody: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +l: B.Line
  for +back: Nat
  for cx: Norm.Cx
  for win: Norm.Win
  {adv_ms(Norm.ms.line.k(inbody, o, s, qs, ql, ls, l, back, cx, win)) == True{} : Bool}

def ms_line_k(inbody, o, s, qs, ql, ls, l, back, cx, win):
  match inbody:
    case False{}:
      ms_done(o, R.head_line(R.is_chrom_line(B.Line.body(l)), R.tick(s), o, l), qs, ql, Norm.Cx.line(cx, B.Line.body(l)), win)
    case True{}:
      ms_split(R.Opts.split(o), o, s, qs, ql, ls, l, back, cx, win)

law ms_line:
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +ls: Norm.Ls
  for +back: Nat
  for cx: Norm.Cx
  for win: Norm.Win
  {adv_ms(Norm.ms.line(o, s, qs, ql, ls, back, cx, win)) == True{} : Bool}

def ms_line(o, s, qs, ql, ls, back, cx, win):
  match s:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +out, +ns, +x}:
      ms_line_k(i, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, x}, qs, ql, ls, Norm.Ls.line(ls), back, cx, win)

law ms_part_len:
  for +dfs: B.Defs
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +at: U32
  for r: D.Bytes & U32
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for +fneed: Bool
  for +hold: Bool
  {adv_ms(Norm.ms.part.len(o, s, qs, ql, at, r, rest, pend, eof, back, win, fneed, dfs, hold)) == True{} : Bool}

def ms_part_len(dfs, o, s, qs, ql, at, r, rest, pend, eof, back, win, fneed, hold):
  match r:
    case (b, +len):
      {==}

law ms_sb_k:
  for +dfs: B.Defs
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +at: U32
  for +lf: U32
  for pr: D.Bytes & String
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for +hold: Bool
  {adv_ms(Norm.ms.sb.k(o, s, qs, ql, at, lf, pr, rest, pend, eof, back, win, dfs, hold)) == True{} : Bool}

def ms_sb_k(dfs, o, s, qs, ql, at, lf, pr, rest, pend, eof, back, win, hold):
  match pr:
    case (b, +t):
      ms_line(o, s, qs, ql, Norm.ls.of(hold, t), back, Norm.Cx{Norm.Src.of(hold, b, (lf + 1 : U32)) <> rest, pend, eof, dfs, hold}, win)

law ms_sb_if:
  for +dfs: B.Defs
  for +part: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for b: D.Bytes
  for +at: U32
  for +lf: U32
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for +fneed: Bool
  for +hold: Bool
  {adv_ms(Norm.ms.sb.if(part, o, s, qs, ql, b, at, lf, rest, pend, eof, back, win, fneed, dfs, hold)) == True{} : Bool}

def ms_sb_if(dfs, part, o, s, qs, ql, b, at, lf, rest, pend, eof, back, win, fneed, hold):
  match part:
    case True{}:
      ms_part_len(dfs, o, s, qs, ql, at, BY.len(b), rest, pend, eof, back, win, fneed, hold)
    case False{}:
      ms_sb_k(dfs, o, s, qs, ql, at, lf, Norm.text(b, at, (lf - at : U32)), rest, pend, eof, back, win, hold)

law ms_sb:
  for +dfs: B.Defs
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +at: U32
  for t: NF.Tb
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for +fneed: Bool
  for +hold: Bool
  {adv_ms(Norm.ms.sb(o, s, qs, ql, at, t, rest, pend, eof, back, win, fneed, dfs, hold)) == True{} : Bool}

def ms_sb(dfs, o, s, qs, ql, at, t, rest, pend, eof, back, win, fneed, hold):
  match t:
    case NF.Tb{b, +j, +part, x}:
      ms_sb_if(dfs, part, o, s, qs, ql, b, at, j, rest, pend, eof, back, win, fneed, hold)

law ms_spif:
  for +dfs: B.Defs
  for +done: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for b: D.Bytes
  for +at: U32
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {adv_ms(Norm.sp.s.if(done, o, s, qs, ql, b, at, rest, pend, eof, back, win, asked, fneed, dfs)) == True{} : Bool}

def ms_spif(dfs, done, o, s, qs, ql, b, at, rest, pend, eof, back, win, asked, fneed):
  match done:
    case True{}:
      {==}
    case False{}:
      ms_sb(dfs, o, Norm.rs_untick(s), qs, ql, at, NF.lf(b, at), rest, pend, eof, back, win, fneed, True{})

law ms_sps:
  for +dfs: B.Defs
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for r: D.Bytes & U32
  for +at: U32
  for rest: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {adv_ms(Norm.sp.s(o, s, qs, ql, r, at, rest, pend, eof, back, win, asked, fneed, dfs)) == True{} : Bool}

def ms_sps(dfs, o, s, qs, ql, r, at, rest, pend, eof, back, win, asked, fneed):
  match r:
    case (b, +len):
      ms_spif(dfs, U32.is_le(len, at), o, s, qs, ql, b, at, rest, pend, eof, back, win, asked, fneed)

law ms_src:
  for +dfs: B.Defs
  for src: List<&1, Norm.Src>
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {adv_ms(Norm.ms.src(src, o, s, qs, ql, pend, eof, back, win, asked, fneed, dfs)) == True{} : Bool}

def ms_src(dfs, src, o, s, qs, ql, pend, eof, back, win, asked, fneed):
  match src:
    case Nil{}:
      {==}
    case Norm.SB{b, +at} <> rest:
      ms_sb(dfs, o, s, qs, ql, at, NF.lf(b, at), rest, pend, eof, back, win, fneed, False{})
    case Norm.SL{+p} <> rest:
      ms_line(o, s, qs, ql, Norm.LsT{p}, back, Norm.Cx{rest, pend, eof, dfs, False{}}, win)
    case Norm.SR{+l} <> rest:
      ms_line(o, Norm.rs_untick(s), qs, ql, Norm.LsR{l}, back, Norm.Cx{rest, pend, eof, dfs, True{}}, win)
    case Norm.SP{b, +at} <> rest:
      ms_sps(dfs, o, s, qs, ql, BY.len(b), at, rest, pend, eof, back, win, asked, fneed)

law ms_full:
  for +dfs: B.Defs
  for +full: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {adv_ms(Norm.ms.full(full, o, s, qs, ql, src, pend, eof, back, win, asked, fneed, dfs)) == True{} : Bool}

def ms_full(dfs,full, o, s, qs, ql, src, pend, eof, back, win, asked, fneed):
  match full:
    case True{}:
      {==}
    case False{}:
      ms_src(dfs, src, o, s, qs, ql, pend, eof, back, win, asked, fneed)

law ms_adv:
  for +dfs: B.Defs
  for +halt: Bool
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +code: Maybe<&2, Nat>
  for src: List<&1, Norm.Src>
  for pend: Norm.Pd
  for eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {adv_ms(Norm.ms.adv(halt, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed, dfs)) == True{} : Bool}

def ms_adv(dfs,halt, o, s, qs, ql, code, src, pend, eof, back, win, asked, fneed):
  match halt code:
    case _ Some{+c}:
      {==}
    case True{} None{}:
      {==}
    case False{} None{}:
      ms_full(dfs, Nat.is_le(Norm.lim(), ql), o, s, qs, ql, src, pend, eof, back, win, asked, fneed)

# From a picture in the String mode, advance stays in it.
law adv_keep_ms:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +h: {is_msp(S.StP.md(p)) == True{} : Bool}
  {adv_ms(Norm.advance(S.mkSt(fa, p))) == True{} : Bool}

def adv_keep_ms(fa, p, h):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      Empty.absurd({adv_ms(Norm.advance(S.mkSt(fa, S.StP{o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed, dfs}))) == True{} : Bool}, PB.false_ne_true(h))
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      ms_adv(dfs, R.RunSt.halt(s), o, s, qs, ql, code, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed)

law ms_md:
  for +md: S.MdP
  for +h: {md_ms(S.mkMd(md)) == True{} : Bool}
  {is_msp(md) == True{} : Bool}

def ms_md(md, h):
  match md:
    case S.MBP{+rp}:
      h
    case S.MSP{+s, +qs, +ql, +code}:
      {==}

law ms_pic2:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for +h: {st_ms(S.mkSt(fa, p2)) == True{} : Bool}
  {is_msp(S.StP.md(p2)) == True{} : Bool}

def ms_pic2(fa, p2, h):
  match p2:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      ms_md(md, h)

# A state the advance gave, pictured: still in the String mode.
law ms_pic:
  for +fa: List<&2, B.Contig>
  for +p2: S.StP
  for -st: Norm.St
  for +est: {st == S.mkSt(fa, p2) : Norm.St}
  for +h: {st_ms(st) == True{} : Bool}
  {is_msp(S.StP.md(p2)) == True{} : Bool}

def ms_pic(fa, p2, st, est, h):
  ms_pic2(fa, p2, Equal.trans(Bool, st_ms(S.mkSt(fa, p2)), st_ms(st), True{}, Equal.cong(Norm.St, Bool, z => st_ms(z), S.mkSt(fa, p2), st, Equal.sym(Norm.St, st, S.mkSt(fa, p2), est)), h))
