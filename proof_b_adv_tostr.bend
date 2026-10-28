import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_ms.bend as MS
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# The byte run switches to the String mode (norm.bend's to_ms, from
# mb.rs, mb.src, to_str): Went with the String mode's picture msO of the
# run's spec state. Every variable is reusable.

def StM(+o: B.Opts, +md: S.MdP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  S.StP{o, md, src, pd, eof, back, wp, asked, fneed}

# ---------------------------------------------------------------------------
# A run that has not halted is in the body, or has written and noted nothing
# (the run area's run_head_empty)
# ---------------------------------------------------------------------------

law ib_spec:
  for +rp: P.RunP
  {R.RunSt.inbody(P.specRun(rp)) == P.RunP.i(rp) : Bool}

def ib_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

def HE(+p: P.RunP) -> Type:
  {P.RunSt.out(P.specRun(p)) == "" : String} & {P.RunSt.notes(P.specRun(p)) == Nil{} : List<&2, B.Note>}

def he_out(+p: P.RunP, h: HE(p)) -> {String.is_empty(P.RunSt.out(P.specRun(p))) == True{} : Bool}:
  match h:
    case (a, b):
      %Equal.sym(String, P.RunSt.out(P.specRun(p)), "", a) : {String.is_empty(_) == True{} : Bool}
      {==}

def he_notes(+p: P.RunP, h: HE(p)) -> {List.is_empty(&2, B.Note, P.RunSt.notes(P.specRun(p))) == True{} : Bool}:
  match h:
    case (a, b):
      %Equal.sym(List<&2, B.Note>, P.RunSt.notes(P.specRun(p)), Nil{}, b) : {List.is_empty(&2, B.Note, _) == True{} : Bool}
      {==}

def hdr_out(+i: Bool, +p: P.RunP, +hi: {PR.RunInv(p) == True{} : Bool}, +hx: {P.RunP.x(p) == False{} : Bool}, +ei: {P.RunP.i(p) == i : Bool}) ->
  {Bool.or(R.RunSt.inbody(P.specRun(p)), String.is_empty(P.RunSt.out(P.specRun(p)))) == True{} : Bool}:
  match i:
    case True{}:
      W.or_l(R.RunSt.inbody(P.specRun(p)), String.is_empty(P.RunSt.out(P.specRun(p))), Equal.trans(Bool, R.RunSt.inbody(P.specRun(p)), P.RunP.i(p), True{}, ib_spec(p), ei))
    case False{}:
      W.or_r(R.RunSt.inbody(P.specRun(p)), String.is_empty(P.RunSt.out(P.specRun(p))), he_out(p, PR.run_head_empty(p, hi, ei, hx)))

def hdr_notes(+i: Bool, +p: P.RunP, +hi: {PR.RunInv(p) == True{} : Bool}, +hx: {P.RunP.x(p) == False{} : Bool}, +ei: {P.RunP.i(p) == i : Bool}) ->
  {Bool.or(R.RunSt.inbody(P.specRun(p)), List.is_empty(&2, B.Note, P.RunSt.notes(P.specRun(p)))) == True{} : Bool}:
  match i:
    case True{}:
      W.or_l(R.RunSt.inbody(P.specRun(p)), List.is_empty(&2, B.Note, P.RunSt.notes(P.specRun(p))), Equal.trans(Bool, R.RunSt.inbody(P.specRun(p)), P.RunP.i(p), True{}, ib_spec(p), ei))
    case False{}:
      W.or_r(R.RunSt.inbody(P.specRun(p)), List.is_empty(&2, B.Note, P.RunSt.notes(P.specRun(p))), he_notes(p, PR.run_head_empty(p, hi, ei, hx)))

# ---------------------------------------------------------------------------
# The byte run switches to the String mode
# ---------------------------------------------------------------------------

def P2ms(+o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +fneed: Bool) -> S.StP:
  StM(o, MS.msO(P.specRun(rp), Nil{}, 0n), src, pd, eof, back, wp, None{}, fneed)

law to_ms_eq:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +hi: {PR.RunInv(rp) == True{} : Bool}
  {Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed} == S.mkSt(fa, P2ms(o, rp, src, pd, eof, back, wp, fneed)) : Norm.St}

def to_ms_eq(fa, o, rp, src, pd, eof, back, wp, fneed, hi):
  +sr = P.specRun(rp)
  %Equal.sym(Norm.Md, S.mkMd(MS.msO(sr, Nil{}, 0n)), Norm.ms.out(sr, Nil{}, 0n), MS.mk_msO(sr, Nil{}, 0n)) :
    {Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed} == Norm.St{o, _, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed} : Norm.St}
  %Equal.sym(R.RunSt, NR.to_spec(P.mkRun(rp)), sr, PR.run_to_spec(rp, hi)) :
    {Norm.St{o, Norm.ms.out(_, Nil{}, 0n), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed} == Norm.St{o, Norm.ms.out(sr, Nil{}, 0n), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), None{}, fneed} : Norm.St}
  {==}

law to_ms_rep:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +back2: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  for +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report}
  {S.report(fa, cs, O, N, P2ms(o, rp, src, pd, eof, back2, wp, fneed2)) == T : R.Report}

def to_ms_rep(fa, T, cs, O, N, o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2, hr):
  +sr = P.specRun(rp)
  %MS.rep_msO(fa, cs, O, N, o, sr, Nil{}, 0n, src, pd, eof, back2, wp, None{}, fneed2) : {_ == T : R.Report}
  %Equal.sym(R.RunSt, S.smd(MS.msO(sr, Nil{}, 0n)), sr, MS.smd_msO0(sr)) :
    {R.finish(L.run.go(B.Text.lines(MS.ITX(src, pd, eof, cs)), fa, o, S.pre(O, N, _))) == T : R.Report}
  hr

law to_ms_lt:
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +back2: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  {Nat.is_lt(S.measure(P2ms(o, rp, src, pd, eof, back2, wp, fneed2)), S.measure(StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed))) == True{} : Bool}

def to_ms_lt(o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2):
  %MS.meas_msO(o, P.specRun(rp), Nil{}, 0n, src, pd, eof, back2, wp, None{}, fneed2) :
    {Nat.is_lt(_, Nat.add(S.msrc(src), 1n)) == True{} : Bool}
  W.lt_add1(S.msrc(src))

law to_ms_guard:
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +rp: P.RunP
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +back2: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +fneed2: Bool
  for +hg: {S.guard(O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool}
  {S.guard(O, N, P2ms(o, rp, src, pd, eof, back2, wp, fneed2)) == True{} : Bool}

def to_ms_guard(O, N, o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2, hg):
  %Equal.sym(R.RunSt, S.smd(MS.msO(P.specRun(rp), Nil{}, 0n)), P.specRun(rp), MS.smd_msO0(P.specRun(rp))) : {Bool.or(R.RunSt.inbody(_), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  hg

def to_ms_went(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +src: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +back2: Nat, +fneed2: Bool,
  +hw: {S.WF(fa, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed), Norm.Went{Norm.St{o, Norm.to_ms(P.mkRun(rp)), P.mkSrcs(src), P.mkPd(pd), eof, back2, PC.mkWin(fa, wp), None{}, fneed2}}):
  +PP = StM(o, S.MBP{rp}, src, pd, eof, back, wp, asked, fneed)
  +hi = W.c9_0(S.md_ok(S.MBP{rp}), W.W1(fa, PP), W.W2(fa, PP), W.W3(fa, PP), W.W4(fa, PP), W.W5(fa, PP), W.W6(fa, PP), W.W7(fa, PP), W.W8(fa, PP), hw)
  +sr = P.specRun(rp)
  +hm = MS.mdok_msO0(sr, PR.run_bytes(rp, hi), hdr_out(P.RunP.i(rp), rp, hi, hx, {==}), hdr_notes(P.RunP.i(rp), rp, hi, hx, {==}))
  (P2ms(o, rp, src, pd, eof, back2, wp, fneed2),
    (to_ms_eq(fa, o, rp, src, pd, eof, back2, wp, fneed2, hi),
    (W.c9_m(S.md_ok(S.MBP{rp}), S.md_ok(MS.msO(sr, Nil{}, 0n)), W.W1(fa, PP), W.W2(fa, PP), W.W3(fa, PP), W.W4(fa, PP), W.W5(fa, PP), W.W6(fa, PP), W.W7(fa, PP), S.mb_win(MS.msO(sr, Nil{}, 0n), wp), W.W8(fa, PP), hw, hm, MS.mbw_msO(sr, Nil{}, 0n, wp)),
    (to_ms_rep(fa, T, cs, O, N, o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2, hr),
    (to_ms_lt(o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2), ({==}, ({==}, to_ms_guard(O, N, o, rp, src, pd, eof, back, back2, wp, asked, fneed, fneed2, hg))))))))

