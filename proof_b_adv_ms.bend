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
import ./proof_b_adv_wf.bend as W
import ./proof_base.bend as PB

# The String mode's picture after a line (norm.bend's ms.out): the run
# state's out moved in front of qs. Every variable is reusable.

def msO(st: R.RunSt, +qs: List<&2, String>, +ql: Nat) -> S.MdP:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, +o, ns, x}:
      S.MSP{R.RunSt{n, i, h, c, e, l, b, k, "", ns, x}, o <> qs, Nat.add(ql, String.length(o)), None{}}

def Strs() -> Data:
  List<&2, String>

law mk_msO:
  for +st: R.RunSt
  for +qs: Strs()
  for +ql: Nat
  {S.mkMd(msO(st, qs, ql)) == Norm.ms.out(st, qs, ql) : Norm.Md}

def mk_msO(st, qs, ql):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

# What a picture's state stands for, its report and its measure, with the
# String-mode part given by msO (rep_msO and meas_msO are stated new == old,
# for rewriting).
law smd_msO0:
  for +st: R.RunSt
  {S.smd(msO(st, Nil{}, 0n)) == st : R.RunSt}

def smd_msO0(st):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

def StM(+dfs: B.Defs, +o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}

def ITX(+src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +cs: Strs()) -> String:
  String.append(P.srcstext(S.plain(src)), String.append(P.pdtext(pd), S.concat_if(eof, cs)))

law rep_msO:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +cs: Strs()
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +st: R.RunSt
  for +qs: Strs()
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {R.finish(L.run.go(B.Text.lines(S.intext(StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed), cs)), fa, S.DEFS(StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed), cs), o,
    S.RG(S.recs(src), fa, S.DEFS(StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed), cs), o, S.pre(O, N, S.smd(msO(st, qs, ql)))))) == S.report(fa, cs, O, N, StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed)) : R.Report}

def rep_msO(dfs,fa, cs, O, N, o, st, qs, ql, src, pd, eof, back, wp, asked, fneed):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}

law meas_msO:
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +qs: Strs()
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {S.msrc(src) == S.measure(StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed)) : Nat}

def meas_msO(dfs,o, st, qs, ql, src, pd, eof, back, wp, asked, fneed):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +so, +ns, +x}:
      {==}

law asked_msO:
  for +dfs: B.Defs
  for +o: B.Opts
  for +st: R.RunSt
  for +qs: Strs()
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  {S.StP.asked(StM(dfs, o, msO(st, qs, ql), src, pd, eof, back, wp, asked, fneed)) == asked : Maybe<&2, List<&2, Pr.Req>>}

def asked_msO(dfs,o, st, qs, ql, src, pd, eof, back, wp, asked, fneed):
  {==}

# The String mode a byte run switches to is good: its texts are bytes, and
# before the #CHROM line it wrote nothing.
law mdok_msO0:
  for +st: R.RunSt
  for +hb: {P.st_bytes(st) == True{} : Bool}
  for +hh: {Bool.or(R.RunSt.inbody(st), String.is_empty(P.RunSt.out(st))) == True{} : Bool}
  for +hn: {Bool.or(R.RunSt.inbody(st), List.is_empty(&2, B.Note, P.RunSt.notes(st))) == True{} : Bool}
  {S.md_ok(msO(st, Nil{}, 0n)) == True{} : Bool}

def mdok_msO0(st, hb, hh, hn):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      +hhb = W.and_l(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hb)
      +s0 = {R.RunSt{n, i, h, c, e, l, b, k, "", ns, x} : R.RunSt}
      +A1 = Bool.and(Nat.is_eq(String.length(o), String.length(o)), E.is_bytes(o))
      +A2 = Bool.and(A1, P.st_bytes(s0))
      +A3 = Bool.and(A2, String.is_empty(""))
      +A4 = Bool.and(A3, Bool.or(i, String.is_empty(o)))
      W.and_tt(A4, Bool.or(i, List.is_empty(&2, B.Note, ns)),
        W.and_tt(A3, Bool.or(i, String.is_empty(o)),
          W.and_tt(A2, String.is_empty(""),
            W.and_tt(A1, P.st_bytes(s0),
              W.and_tt(Nat.is_eq(String.length(o), String.length(o)), E.is_bytes(o), PB.eq_refl(String.length(o)), W.and_r(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hb)),
              W.and_tt(Bool.and(E.is_bytes(h), P.items_bytes(b)), True{}, hhb, {==})),
            {==}),
          hh),
        hn)

# The String mode's windows are not restricted (mb_win).
law mbw_msO:
  for +st: R.RunSt
  for +qs: Strs()
  for +ql: Nat
  for +wp: PC.WP
  {S.mb_win(msO(st, qs, ql), wp) == True{} : Bool}

def mbw_msO(st, qs, ql, wp):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

# A step into the String mode claims only that the definitions are kept
# (S.Moved).
def moved_msO(+fa: List<&2, B.Contig>, +cs: Strs(), m: S.MdP, +p: S.StP, +p2: S.StP, st: R.RunSt, +qs: Strs(), +ql: Nat,
  +hd: {S.DEFS(p2, cs) == S.DEFS(p, cs) : B.Defs}) -> S.Moved.md(m, msO(st, qs, ql), fa, cs, p, p2):
  match m st:
    case S.MBP{rp} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      hd
    case S.MSP{s, qs2, ql2, code} R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      hd
