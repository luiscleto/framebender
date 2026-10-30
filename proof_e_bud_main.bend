import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_base.bend as PB
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_bud_none.bend as BNo
import ./proof_e_bud_phase.bend as PH
import ./proof_e_mach_inv.bend as IV
import ./proof_e_mach_dup.bend as DU

# Phase E, area E2: each driver step lowers the potential by 1 + its reads
# (the assembly's continuation API.KontW), by the batch's phase.

law chunk_x:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for hi: WD.InvW(fa, T, c <> cs, O, N, x, Pr.More{}, False{})
  for +hbi: {BD.biW(WD.mkWSt(fa, x), c <> cs) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, x), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, x), c <> cs, False{}, Pr.More{}, O), O, N)

def chunk_x(fa, T, c, cs, O, N, x, hb, hi, hbi, hcb, hcn):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (hmo, hef) = i3
      BNo.none_chunk(fa, T, c, cs, O, N, p, hb, hmo, a3, a2, hbi, hcb, hcn)
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      (hmo, i5) = i4
      (hstp, i6) = i5
      (hef, hk) = i6
      PH.col_chunk(fa, T, c, cs, O, N, p, hs, k, hb, hmo, hstp, a2, a3, a1, hk, hbi, hcb, hcn)
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), c <> cs, False{}, Pr.More{}, O), O, N), IV.more_ask(PT.reqs_of(ps), nxe))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), c <> cs, False{}, Pr.More{}, O), O, N), IV.more_ask(Nil{}, nxe))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (qn, i4) = i3
      (nim, i5) = i4
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), c <> cs, False{}, Pr.More{}, O), O, N), PB.true_ne_false(nim))

# A piece of the file (the driver's More, pieces left).
law bud_chunkW:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for hi: WD.InvW(fa, T, c <> cs, O, N, x, Pr.More{}, False{})
  for +hbi: {BD.biW(WD.mkWSt(fa, x), c <> cs) == True{} : Bool}
  for +htx: {API.txt(c <> cs) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, x), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, x), c <> cs, False{}, Pr.More{}, O), O, N)

def bud_chunkW(fa, T, c, cs, O, N, x, hb, hi, hbi, htx):
  +hA = PB.and_true_l(Bool.and(E.is_bytes(c), E.all_bytes(cs)), Bool.and(E.le31(String.length(c)), E.pieces_ok(cs)), htx)
  +hP = PB.and_true_r(Bool.and(E.is_bytes(c), E.all_bytes(cs)), Bool.and(E.le31(String.length(c)), E.pieces_ok(cs)), htx)
  +hcb = PB.and_true_l(E.is_bytes(c), E.all_bytes(cs), hA)
  +hcn = PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(cs), hP)
  chunk_x(fa, T, c, cs, O, N, x, hb, hi, hbi, hcb, hcn)

law eof_x:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for hi: WD.InvW(fa, T, Nil{}, O, N, x, Pr.More{}, False{})
  for +hbi: {BD.biW(WD.mkWSt(fa, x), Nil{}) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, x), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, x), Nil{}, False{}, Pr.More{}, O), O, N)

def eof_x(fa, T, O, N, x, hb, hi, hbi):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (hmo, hef) = i3
      BNo.none_eof(fa, T, O, N, p, hb, hmo, a3, a2, hbi)
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      (hmo, i5) = i4
      (hstp, i6) = i5
      (hef, hk) = i6
      PH.col_eof(fa, T, O, N, p, hs, k, hb, hmo, hstp, a2, a3, a1, hk, hbi)
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Nil{}, False{}, Pr.More{}, O), O, N), IV.more_ask(PT.reqs_of(ps), nxe))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Nil{}, False{}, Pr.More{}, O), O, N), IV.more_ask(Nil{}, nxe))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (qn, i4) = i3
      (nim, i5) = i4
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Nil{}, False{}, Pr.More{}, O), O, N), PB.true_ne_false(nim))

# The end of the file (the driver's More, no piece left).
law bud_eofW:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for hi: WD.InvW(fa, T, Nil{}, O, N, x, Pr.More{}, False{})
  for +hbi: {BD.biW(WD.mkWSt(fa, x), Nil{}) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, x), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, x), Nil{}, False{}, Pr.More{}, O), O, N)

def bud_eofW(fa, T, O, N, x, hb, hi, hbi):
  eof_x(fa, T, O, N, x, hb, hi, hbi)

# The truthful answers to an Ask (ef: the driver's end-of-file flag).
law bud_refW:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +rs: List<&2, Pr.Req>
  for +ef: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for hi: WD.InvW(fa, T, cs, O, N, x, Pr.Ask{rs}, ef)
  for +hbi: {BD.biW(WD.mkWSt(fa, x), cs) == True{} : Bool}
  for +htx: {API.txt(cs) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, x), Pr.Ref{M.truths(fa, rs)}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, x), cs, ef, Pr.Ask{rs}, O), O, N)

def bud_refW(fa, T, cs, O, N, x, rs, ef, hb, hi, hbi, htx):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (hw, i4) = i3
      (hq, i5) = i4
      (hrq, i6) = i5
      (hmr, i7) = i6
      (hask, heof) = i7
      BNo.none_ref(fa, T, cs, O, N, p, rs, ef, hb, hw, a3, hask, hq, hrq, hmr, a2, hbi)
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      Empty.absurd(API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Pr.Ref{M.truths(fa, rs)}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), cs, ef, Pr.Ask{rs}, O), O, N), IV.more_ask(rs, Equal.sym(Pr.Next, Pr.Ask{rs}, Pr.More{}, nxe)))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      (hmo, i5) = i4
      (hstp, i6) = i5
      (hqo, i7) = i6
      (hps, he) = i7
      +hrs = Equal.cong(Pr.Next, List<&2, Pr.Req>, z => IV.askrs(z), Pr.Ask{rs}, Pr.Ask{PT.reqs_of(ps)}, nxe)
      %Equal.sym(List<&2, Pr.Req>, rs, PT.reqs_of(ps), hrs) :
        API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Ref{M.truths(fa, _)}), cs, ef, List.length(&2, Pr.Req, _), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), cs, ef, Pr.Ask{_}, O), O, N)
      PH.ask_ref(fa, T, cs, O, N, p, ps, e, ef, hb, hmo, hstp, a2, a3, a1, DU.pcsok_dup(ps, cs, hps), he, hbi)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (nxe, i4) = i3
      (hmo, i5) = i4
      (hstp, i6) = i5
      (hps, i7) = i6
      (hbo, he) = i7
      +hrs = Equal.cong(Pr.Next, List<&2, Pr.Req>, z => IV.askrs(z), Pr.Ask{rs}, Pr.Ask{Nil{}}, nxe)
      %Equal.sym(List<&2, Pr.Req>, rs, Nil{}, hrs) :
        API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Ref{M.truths(fa, _)}), cs, ef, List.length(&2, Pr.Req, _), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), cs, ef, Pr.Ask{_}, O), O, N)
      PH.combf_ref(fa, T, cs, O, N, p, ps, xs, e, ef, hb, hmo, hstp, a2, a3, a1, hps, DU.batchok_dup(fa, S.StP.o(p), ps, xs, cs, hbo), he, hbi)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (a1, i1) = hi
      (a2, i2) = i1
      (a3, i3) = i2
      (qn, i4) = i3
      (hw, q1) = qn
      (hq, q2) = q1
      (hrq, q3) = q2
      (hmr, q4) = q3
      (hask, heof) = q4
      (nim, i5) = i4
      (hps, i6) = i5
      (hbo, he) = i6
      PH.combt_ref(fa, T, cs, O, N, p, ps, xs, e, rs, ef, hb, hw, hask, hq, hrq, hmr, a2, a3, hbo, he, hbi)
