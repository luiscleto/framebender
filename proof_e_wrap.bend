import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_e_wrap_defs.bend as WD
import ./proof_b_drive.bend as DV
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_comb.bend as WC
import ./proof_e_wrap_seq.bend as WS
import ./proof_e_wrap_col.bend as WL

# Phase E, area "wrap" (E1): each step of the parallel machine keeps a good
# state standing for the same report (definitions: proof_e_wrap_defs.bend;
# notes/parallel_proofs.md, "Area E"). The proofs use phase B's lemmas on Q
# (proof_b_drive.bend, proof_b_drive_step.bend, proof_b_drive_out.bend,
# proof_b_sim.bend), and areas B (proof_e_seg.bend), C (proof_e_merge.bend),
# D (proof_e_task.bend) and F (proof_e_qif.bend).

# ---------------------------------------------------------------------------
# Start
# ---------------------------------------------------------------------------

law start_k:
  for b: Norm.Begin
  {WD.wstart_st(W.start.k(b)) == W.St{DR.start_st(b), W.BNone{}} : W.St} & {WD.wstart_paths(W.start.k(b)) == DR.start_paths(b) : Maybe<&2, DR.Paths>}

def start_k(b):
  match b:
    case Norm.Begin{st, +r, +v}:
      ({==}, {==})
    case Norm.Usage{}:
      ({==}, {==})

def wstart_go(+fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>,
  so: &p: S.StP -> ({DR.start_st(Norm.start(argv)) == S.mkSt(fa, p) : Norm.St}
    & ({DR.start_paths(Norm.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
    & ({DR.more_ok(fa, p) == True{} : Bool}
    & ({S.report(fa, cs, "", Nil{}, p) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}
    & {S.guard("", Nil{}, p) == True{} : Bool})))),
  sk: {WD.wstart_st(W.start.k(Norm.start(argv))) == W.St{DR.start_st(Norm.start(argv)), W.BNone{}} : W.St} & {WD.wstart_paths(W.start.k(Norm.start(argv))) == DR.start_paths(Norm.start(argv)) : Maybe<&2, DR.Paths>}) ->
  &x: WD.WPic -> ({WD.wstart_st(W.start(argv)) == WD.mkWSt(fa, x) : W.St}
  & ({WD.wstart_paths(W.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  & WD.InvW(fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}))):
  (+p, s1) = so
  (e1, s2) = s1
  (ep, s3) = s2
  (hm, s4) = s3
  (hr, hg) = s4
  (k1, k2) = sk
  (WD.WPic{p, WD.BNoneP{}},
    (Equal.trans(W.St, WD.wstart_st(W.start.k(Norm.start(argv))), W.St{DR.start_st(Norm.start(argv)), W.BNone{}}, W.St{S.mkSt(fa, p), W.BNone{}}, k1,
      Equal.cong(Norm.St, W.St, z => W.St{z, W.BNone{}}, DR.start_st(Norm.start(argv)), S.mkSt(fa, p), e1)),
    (Equal.trans(Maybe<&2, DR.Paths>, WD.wstart_paths(W.start.k(Norm.start(argv))), DR.start_paths(Norm.start(argv)), Some{DR.Paths{ref, vcfpath}}, k2, ep),
    ({==}, (hg, (hr, (hm, {==})))))))

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# A piece of the file (the driver's More, pieces left).
def wstep_chunk(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WD.WPic,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(fa, T, c <> cs, O, N, x, Pr.More{}, False{}),
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hcs: {E.all_bytes(cs) && E.pieces_ok(cs) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, x), Pr.Chunk{E.enc(c)})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hm, hef) = hph
      WL.none_chunk(fa, T, c, cs, O, N, p, hb, hm, hrep, hcb, hcn, hg)
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      (hm, f2) = f1
      (hl, f3) = f2
      (hef, hk) = f3
      WL.col_add_k(fa, T, c, cs, O, N, p, hs, k, Nat.is_le(W.kmax(), 1n+k) || U32.is_lt(U32.from_nat(String.length(c)), W.minp()), hb, hm, hl, hg, hrep, hby, hcb, hcn, hk, {==})
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{PT.reqs_of(ps)}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{Nil{}}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (hnm, f2) = f1
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Chunk{E.enc(c)})),
        PB.true_ne_false(hnm))

# The end of the file (the driver's More, no piece left).
def wstep_eof(+fa: List<&2, B.Contig>, +T: R.Report, +O: String, +N: List<&2, B.Note>, +x: WD.WPic,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(fa, T, Nil{}, O, N, x, Pr.More{}, False{})) ->
  WD.StepGW(fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, x), Pr.Eof{})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hm, hef) = hph
      WB.g2_none(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{}), DS.step_eof_h2(fa, T, O, N, p, hb, hm, hrep, hg))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      (hm, f2) = f1
      (hl, f3) = f2
      (hef, hk) = f3
      WL.col_eof(fa, T, O, N, p, hs, k, hb, hm, hl, hg, hrep, hby)
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Eof{})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{PT.reqs_of(ps)}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Eof{})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{Nil{}}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (hnm, f2) = f1
      Empty.absurd(WD.StepGW(fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Eof{})),
        PB.true_ne_false(hnm))

# The truthful answers to an Ask (ef: the driver's end-of-file flag, as is).
def wstep_ref(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WD.WPic, +rs: List<&2, Pr.Req>, +ef: Bool,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(fa, T, cs, O, N, x, Pr.Ask{rs}, ef),
  hcs: {E.all_bytes(cs) && E.pieces_ok(cs) == True{} : Bool}) ->
  WD.StepGW(fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, x), Pr.Ref{M.truths(fa, rs)})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (+hw, q1) = hph
      (+hq, q2) = q1
      (+hp, q3) = q2
      (+hmr, q4) = q3
      (+ha, hef) = q4
      WB.g2_none(fa, T, cs, O, N, ef, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
        WB.g2_ef(fa, T, cs, O, N, S.StP.eof(p), ef, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), hef,
          DS.step_ref_h2(fa, T, cs, O, N, p, rs, hb, hw, hrep, ha, hq, hp, hmr, hg)))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Pr.Ref{M.truths(fa, rs)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_more(z), Pr.Ask{rs}, Pr.More{}, hnx)))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      (hm, f2) = f1
      (hl, f3) = f2
      (hq, f4) = f3
      (hps, he) = f4
      %Equal.sym(List<&2, Pr.Req>, rs, PT.reqs_of(ps), Equal.cong(Pr.Next, List<&2, Pr.Req>, z => DO.ask_rs(z), Pr.Ask{rs}, Pr.Ask{PT.reqs_of(ps)}, hnx)) :
        WD.StepGW(fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Ref{M.truths(fa, _)}))
      WL.ask_ref(fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hrep, hby, hps, he)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      (hm, f2) = f1
      (hl, f3) = f2
      (hps, f4) = f3
      (hbo, he) = f4
      WC.comb_next_ok(fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hl, hg, hrep, hby, hps, hbo, he)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hby, h1) = hi
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (+hw, q1) = hqn
      (+hq, q2) = q1
      (+hp, q3) = q2
      (+hmr, q4) = q3
      (+ha, hef) = q4
      (hnm, f2) = f1
      (hps, f3) = f2
      (hbo, he) = f3
      WS.seq_ref(fa, T, cs, O, N, ef, p, ps, xs, e, rs, hb, hw, hrep, ha, hq, hp, hmr, hef, hg, hby, hps, hbo, he)

# The program starts waiting for input, standing for the spec's whole run.
def wstart(+fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>,
  ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  hab: {E.all_bytes(argv) == True{} : Bool}) ->
  &x: WD.WPic -> ({WD.wstart_st(W.start(argv)) == WD.mkWSt(fa, x) : W.St}
  & ({WD.wstart_paths(W.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  & WD.InvW(fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}))):
  wstart_go(fa, argv, o, ref, vcfpath, cs, DV.start_ok(fa, argv, o, ref, vcfpath, cs, ha, hab), start_k(Norm.start(argv)))
