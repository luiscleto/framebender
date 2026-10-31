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
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_seq.bend as WS
import ./proof_e_wrap_clean.bend as CL

# Helpers for proof_e_wrap.bend (area E1): the combine, one piece per step:
# the batch's end, a dirty piece (Q), or a clean one (merged when it fits).

# The combine from a good Q state waiting for more, with the batch's pieces
# ps (their results xs) still to go before cs.
def comb_next_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool, +p: S.StP, +ps: List<&2, PT.Pc>, +xs: List<&2, PT.TOutP>, +e: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hm: {DR.more_ok(fa, p) == True{} : Bool},
  +hl: {S.stopped(S.StP.md(p)) == False{} : Bool},
  +hg: {S.guard(O, N, p) == True{} : Bool},
  +hr: {S.report(fa, List.append(&2, String, PT.texts(ps), cs), O, N, p) == T : R.Report},
  +hby: {E.all_bytes(PT.texts(ps)) && E.pieces_ok(PT.texts(ps)) == True{} : Bool},
  hps: PT.PcsOK(ps, cs),
  hbo: PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs),
  he: WD.EofOK(e, ef, cs),
  +hdd: {S.DEFS(p, List.append(&2, String, PT.texts(ps), cs)) == dfs : B.Defs}) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.comb.next(PT.mkTOuts(fa, ps, xs), S.mkSt(fa, p), e)):
  match ps xs:
    case Nil{} Nil{}:
      WS.comb_end(dfs, fa, T, cs, O, N, ef, p, e, hb, hm, hl, hg, hr, he, hdd)
    case Con{PT.Pc{+c, +rs, +ok, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TDirtyP{}}, +xt}:
      (hpc, hpt) = hps
      (hto, hbt) = hbo
      (+hok, h1) = hto
      (+hv, hres) = h1
      +ha = PB.and_true_l(E.all_bytes(c <> PT.texts(pt)), E.pieces_ok(c <> PT.texts(pt)), hby)
      +hp = PB.and_true_r(E.all_bytes(c <> PT.texts(pt)), E.pieces_ok(c <> PT.texts(pt)), hby)
      WS.comb_dirty(dfs, fa, T, cs, O, N, ef, p, c, pt, xt, e, len, t, d, hb, hm, hg, hr,
        PB.and_true_l(E.is_bytes(c), E.all_bytes(PT.texts(pt)), ha), PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(PT.texts(pt)), hp),
        WB.and2(E.all_bytes(PT.texts(pt)), E.pieces_ok(PT.texts(pt)), PB.and_true_r(E.is_bytes(c), E.all_bytes(PT.texts(pt)), ha), PB.and_true_r(E.le31(String.length(c)), E.pieces_ok(PT.texts(pt)), hp)),
        hok, hv, hpt, hbt, he, hdd)
    case Con{PT.Pc{+c, +rs, True{}, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TCleanP{PT.TcP{+rp, +pd, +wp}}}, +xt}:
      (hpc, hpt) = hps
      (hto, hbt) = hbo
      (+hok, h1) = hto
      (+hv, htc) = h1
      +ha = PB.and_true_l(E.all_bytes(c <> PT.texts(pt)), E.pieces_ok(c <> PT.texts(pt)), hby)
      +hp = PB.and_true_r(E.all_bytes(c <> PT.texts(pt)), E.pieces_ok(c <> PT.texts(pt)), hby)
      CL.comb_clean(dfs, fa, T, cs, O, N, ef, p, c, rs, k, c0, l, pt, xt, e, len, t, d, rp, pd, wp, hb, hm, hl, hg, hr,
        PB.and_true_l(E.is_bytes(c), E.all_bytes(PT.texts(pt)), ha), PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(PT.texts(pt)), hp),
        WB.and2(E.all_bytes(PT.texts(pt)), E.pieces_ok(PT.texts(pt)), PB.and_true_r(E.is_bytes(c), E.all_bytes(PT.texts(pt)), ha), PB.and_true_r(E.le31(String.length(c)), E.pieces_ok(PT.texts(pt)), hp)),
        hok, hv, hpc, htc, hpt, hbt, he, hdd)
    case Con{PT.Pc{+c, +rs, False{}, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, PT.TCleanP{+x}}, +xt}:
      (hto, hbt) = hbo
      (+hok, h1) = hto
      (+hv, hres) = h1
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, ef, W.comb.next(PT.mkTOuts(fa, PT.Pc{c, rs, False{}, k, c0, l} <> pt, PT.TOutP{len, t, d, PT.TCleanP{x}} <> xt), S.mkSt(fa, p), e)), hres)
    case Nil{} Con{+y, +xt}:
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, ef, W.comb.next(PT.mkTOuts(fa, Nil{}, y <> xt), S.mkSt(fa, p), e)), hbo)
    case Con{+x, +pt} Nil{}:
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, ef, W.comb.next(PT.mkTOuts(fa, x <> pt, Nil{}), S.mkSt(fa, p), e)), hbo)
