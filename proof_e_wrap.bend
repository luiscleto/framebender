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
import ./proof_e_wrap_qd.bend as QD
import ./proof_b_drive_start.bend as DST
import ./proof_b_drive_chunk.bend as DC

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
  for +dfs: B.Defs
  for b: Norm.Begin
  {WD.wstart_st(dfs, W.start.k(b)) == W.St{DR.start_st(dfs, b), W.BNone{}} : W.St} & {WD.wstart_paths(W.start.k(b)) == DR.start_paths(b) : Maybe<&2, DR.Paths>}

def start_k(dfs,b):
  match b:
    case Norm.Begin{st, +r, +v}:
      ({==}, {==})
    case Norm.Usage{}:
      ({==}, {==})

def wstart_go(+dfs: B.Defs, +fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>,
  so: DST.StartGD(dfs, fa, argv, o, ref, vcfpath, cs),
  sk: {WD.wstart_st(L.defs(String.concat(cs)), W.start.k(Norm.start(argv))) == W.St{DR.start_st(dfs, Norm.start(argv)), W.BNone{}} : W.St} & {WD.wstart_paths(W.start.k(Norm.start(argv))) == DR.start_paths(Norm.start(argv)) : Maybe<&2, DR.Paths>}) ->
  &x: WD.WPic -> ({WD.wstart_st(L.defs(String.concat(cs)), W.start(argv)) == WD.mkWSt(fa, x) : W.St}
  & ({WD.wstart_paths(W.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  & WD.InvW(L.defs(String.concat(cs)), fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, L.defs(String.concat(cs)), o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}))):
  (+p, s1) = so
  (e1, s2) = s1
  (ep, s3) = s2
  (hm, s4) = s3
  (hr, s5) = s4
  (hg, hd) = s5
  (k1, k2) = sk
  +D = L.defs(String.concat(cs))
  (WD.WPic{p, WD.BNoneP{}},
    (Equal.trans(W.St, WD.wstart_st(D, W.start.k(Norm.start(argv))), W.St{DR.start_st(dfs, Norm.start(argv)), W.BNone{}}, W.St{S.mkSt(fa, p), W.BNone{}}, k1,
      Equal.cong(Norm.St, W.St, z => W.St{z, W.BNone{}}, DR.start_st(dfs, Norm.start(argv)), S.mkSt(fa, p), e1)),
    (Equal.trans(Maybe<&2, DR.Paths>, WD.wstart_paths(W.start.k(Norm.start(argv))), DR.start_paths(Norm.start(argv)), Some{DR.Paths{ref, vcfpath}}, k2, ep),
    (WD.eofd_any(S.StP.eof(p), S.DEFS(p, cs), D, hd), ({==}, (hg, (hr, (hm, {==}))))))))

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# Q waiting for more has not seen the end of the file.
def eof_mo(+fa: List<&2, B.Contig>, +p: S.StP, +hm: {DR.more_ok(fa, p) == True{} : Bool}) -> {S.StP.eof(p) == False{} : Bool}:
  DO.not_true(S.StP.eof(p), WB.mo_ne(S.WF(fa, p), S.src_empty(S.StP.src(p)), Bool.not(S.StP.eof(p)), Maybe.is_none(&2, List<&2, Pr.Req>, S.StP.asked(p)), hm))

# A piece of the file (the driver's More, pieces left).
def wstep_chunk(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WD.WPic,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(dfs, fa, T, c <> cs, O, N, x, Pr.More{}, False{}),
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hcs: {E.all_bytes(cs) && E.pieces_ok(cs) == True{} : Bool}) ->
  WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, x), Pr.Chunk{E.enc(c)})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (+hm, hef) = hph
      WL.none_chunk(dfs, fa, T, c, cs, O, N, p, hb, hm, hrep, hcb, hcn, hg, WD.eofd_get(S.StP.eof(p), S.DEFS(p, c <> cs), dfs, eof_mo(fa, p, hm), hdd0))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (+hdf, f0) = hph
      (hnx, f1) = f0
      (+hm, f2) = f1
      (hl, f3) = f2
      (hef, hk) = f3
      %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
        WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step.q(W.BCol{PT.encs(hs), k}, _, Pr.Chunk{E.enc(c)}))
      %Equal.sym(B.Defs, S.StP.dfs(p), dfs, hdf) :
        WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step.q(W.BCol{PT.encs(hs), k}, (S.mkSt(fa, p), _), Pr.Chunk{E.enc(c)}))
      WL.col_add_k(dfs, fa, T, c, cs, O, N, p, hs, k, Nat.is_le(W.kmax(), 1n+k) || U32.is_lt(U32.from_nat(String.length(c)), W.minp()), hb, hm, hl, hg, hrep, hby, hcb, hcn, hk, {==},
        hdf, WD.eofd_get(S.StP.eof(p), S.DEFS(p, List.append(&2, String, List.reverse(&2, String, hs), c <> cs)), dfs, eof_mo(fa, p, hm), hdd0))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hdf, f0) = hph
      (hnx, f1) = f0
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{PT.reqs_of(ps)}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Chunk{E.enc(c)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{Nil{}}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (hnm, f2) = f1
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, False{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Chunk{E.enc(c)})),
        PB.true_ne_false(hnm))

# The end of the file (the driver's More, no piece left).
def wstep_eof(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +O: String, +N: List<&2, B.Note>, +x: WD.WPic,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(dfs, fa, T, Nil{}, O, N, x, Pr.More{}, False{})) ->
  WD.StepGW(dfs, fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, x), Pr.Eof{})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hm, hef) = hph
      %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
        WD.StepGW(dfs, fa, T, Nil{}, O, N, True{}, W.step.q(W.BNone{}, _, Pr.Eof{}))
      WB.g2_none(dfs, fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{}), DS.step_eof_h2(fa, T, O, N, p, hb, hm, hrep, hg),
        WB.hd_eof(dfs, fa, Nil{}, Norm.step(S.mkSt(fa, p), Pr.Eof{})))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hdf, f0) = hph
      (hnx, f1) = f0
      (+hm, f2) = f1
      (hl, f3) = f2
      (hef, hk) = f3
      WL.col_eof(dfs, fa, T, O, N, p, hs, k, hb, hm, hl, hg, hrep, hby,
        hdf, WD.eofd_get(S.StP.eof(p), S.DEFS(p, List.append(&2, String, List.reverse(&2, String, hs), Nil{})), dfs, eof_mo(fa, p, hm), hdd0))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hdf, f0) = hph
      (hnx, f1) = f0
      Empty.absurd(WD.StepGW(dfs, fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Eof{})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{PT.reqs_of(ps)}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      Empty.absurd(WD.StepGW(dfs, fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, False{}}}), Pr.Eof{})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_ask(z), Pr.More{}, Pr.Ask{Nil{}}, hnx)))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (hnm, f2) = f1
      Empty.absurd(WD.StepGW(dfs, fa, T, Nil{}, O, N, True{}, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BCombP{ps, xs, e, True{}}}), Pr.Eof{})),
        PB.true_ne_false(hnm))

# EofD, as an implication on the driver's flag (Q's flag is the driver's).
def eofd_imp2(+ef: Bool, +d: B.Defs, +dfs: B.Defs, h: WD.EofD(ef, d, dfs)) -> {ef == False{} : Bool} -> {d == dfs : B.Defs}:
  match ef:
    case True{}:
      hf => Empty.absurd({d == dfs : B.Defs}, PB.true_ne_false(hf))
    case False{}:
      hf => h

def eofd_imp(+e: Bool, +ef: Bool, +d: B.Defs, +dfs: B.Defs, +he: {e == ef : Bool}, h: WD.EofD(e, d, dfs)) -> {ef == False{} : Bool} -> {d == dfs : B.Defs}:
  eofd_imp2(ef, d, dfs, {%he : WD.EofD(_, d, dfs); h : WD.EofD(ef, d, dfs)})

# PD from a state whose definitions are D before the end of the file.
def pd_hd_ef(+fa: List<&2, B.Contig>, -s: Norm.Step, +cs: List<&2, String>, +Dp: B.Defs, +D: B.Defs, h: QD.PD(s, cs, Dp), +ef: Bool, hx: {ef == False{} : Bool} -> {Dp == D : B.Defs}) ->
  @p2: S.StP -> {WB.step_st(s) == S.mkSt(fa, p2) : Norm.St} -> {ef == False{} : Bool} -> {WD.dsel(WB.step_nx(s), S.DEFS(p2, cs), D) == D : B.Defs}:
  +p2 => +e => +hf =>
    {%Equal.trans(B.Defs, QD.st_defs(WB.step_st(s), cs), QD.st_defs(S.mkSt(fa, p2), cs), S.DEFS(p2, cs), Equal.cong(Norm.St, B.Defs, z => QD.st_defs(z, cs), WB.step_st(s), S.mkSt(fa, p2), e), QD.mk_defs(fa, p2, cs)) :
       {WD.dsel(WB.step_nx(s), _, D) == D : B.Defs};
     QD.pd_rw(s, cs, Dp, D, hx(hf), h) : {WD.dsel(WB.step_nx(s), S.DEFS(p2, cs), D) == D : B.Defs}}

# The truthful answers to an Ask (ef: the driver's end-of-file flag, as is).
def wstep_ref(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +x: WD.WPic, +rs: List<&2, Pr.Req>, +ef: Bool,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hi: WD.InvW(dfs, fa, T, cs, O, N, x, Pr.Ask{rs}, ef),
  hcs: {E.all_bytes(cs) && E.pieces_ok(cs) == True{} : Bool}) ->
  WD.StepGW(dfs, fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, x), Pr.Ref{M.truths(fa, rs)})):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (+hg, h2) = h1
      (hrep, hph) = h2
      (+hw, q1) = hph
      (+hq, q2) = q1
      (+hp, q3) = q2
      (+hmr, q4) = q3
      (+ha, hef0) = q4
      +hef = {hef0 : {S.StP.eof(p) == ef : Bool}}
      +hbb = {hb : {PC.fa_bytes(fa) == True{} : Bool}}
      %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
        WD.StepGW(dfs, fa, T, cs, O, N, ef, W.step.q(W.BNone{}, _, Pr.Ref{M.truths(fa, rs)}))
      WB.g2_none(dfs, fa, T, cs, O, N, ef, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
        WB.g2_ef(fa, T, cs, O, N, S.StP.eof(p), ef, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), hef,
          DS.step_ref_h2(fa, T, cs, O, N, p, rs, hbb, hw, hrep, ha, hq, hp, hmr, hg)),
        pd_hd_ef(fa, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), cs, S.DEFS(p, cs), dfs, QD.ref_d(fa, O, N, p, rs, hbb, hw, ha, hq, hp, hmr, hg, cs), ef,
          eofd_imp(S.StP.eof(p), ef, S.DEFS(p, cs), dfs, hef, hdd0)))
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hdf, f0) = hph
      (hnx, f1) = f0
      Empty.absurd(WD.StepGW(dfs, fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BColP{hs, k}}), Pr.Ref{M.truths(fa, rs)})),
        PB.false_ne_true(Equal.cong(Pr.Next, Bool, z => DO.is_more(z), Pr.Ask{rs}, Pr.More{}, hnx)))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (+hdf, f0) = hph
      (hnx, f1) = f0
      (+hm, f2) = f1
      (hl, f3) = f2
      (hq, f4) = f3
      (hps, he) = f4
      +hdd = WD.eofd_get(S.StP.eof(p), S.DEFS(p, List.append(&2, String, PT.texts(ps), cs)), dfs, eof_mo(fa, p, hm), hdd0)
      %Equal.sym(List<&2, Pr.Req>, rs, PT.reqs_of(ps), Equal.cong(Pr.Next, List<&2, Pr.Req>, z => DO.ask_rs(z), Pr.Ask{rs}, Pr.Ask{PT.reqs_of(ps)}, hnx)) :
        WD.StepGW(dfs, fa, T, cs, O, N, ef, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BAskP{ps, e}}), Pr.Ref{M.truths(fa, _)}))
      WL.ask_ref(dfs, fa, T, cs, O, N, ef, p, ps, e, hb, hm, hl, hg, hrep, hby, hps, he, hdf, hdd)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hnx, f1) = hph
      (+hm, f2) = f1
      (hl, f3) = f2
      (hps, f4) = f3
      (hbo, he) = f4
      %Equal.sym(Norm.St & B.Defs, W.dfs_of(S.mkSt(fa, p)), (S.mkSt(fa, p), S.StP.dfs(p)), WL.dfs_eq(fa, p)) :
        WD.StepGW(dfs, fa, T, cs, O, N, ef, W.step.q(W.BComb{PT.mkTOuts(fa, ps, xs), e, False{}}, _, Pr.Ref{M.truths(fa, rs)}))
      WC.comb_next_ok(dfs, fa, T, cs, O, N, ef, p, ps, xs, e, hb, hm, hl, hg, hrep, hby, hps, hbo, he,
        WD.eofd_get(S.StP.eof(p), S.DEFS(p, List.append(&2, String, PT.texts(ps), cs)), dfs, eof_mo(fa, p, hm), hdd0))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (hdd0, h0) = hi
      (hby, h1) = h0
      (hg, h2) = h1
      (hrep, hph) = h2
      (hqn, f1) = hph
      (+hw, q1) = hqn
      (+hq, q2) = q1
      (+hp, q3) = q2
      (+hmr, q4) = q3
      (+ha, hef0) = q4
      (hnm, f2) = f1
      (hps, f3) = f2
      (hbo, he) = f3
      +hef = {hef0 : {S.StP.eof(p) == False{} : Bool}}
      WS.seq_ref(dfs, fa, T, cs, O, N, ef, p, ps, xs, e, rs, hb, hw, hrep, ha, hq, hp, hmr, hef, hg, hby, hps, hbo, he,
        WD.eofd_get(S.StP.eof(p), S.DEFS(p, List.append(&2, String, PT.texts(ps), cs)), dfs, hef, hdd0))

# The program starts waiting for input, standing for the spec's whole run
# (dfs: the file's header definitions, which the threads machine's tasks get).
def wstart(+dfs: B.Defs, +fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>,
  ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>},
  hab: {E.all_bytes(argv) == True{} : Bool},
  +hdl: {dfs == L.defs(String.concat(cs)) : B.Defs}) ->
  &x: WD.WPic -> ({WD.wstart_st(dfs, W.start(argv)) == WD.mkWSt(fa, x) : W.St}
  & ({WD.wstart_paths(W.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  & WD.InvW(dfs, fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, dfs, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{}))):
  %Equal.sym(B.Defs, dfs, L.defs(String.concat(cs)), hdl) :
    &x: WD.WPic -> ({WD.wstart_st(_, W.start(argv)) == WD.mkWSt(fa, x) : W.St}
    & ({WD.wstart_paths(W.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
    & WD.InvW(_, fa, R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, _, o, R.start_st())), cs, "", Nil{}, x, Pr.More{}, False{})))
  wstart_go(L.defs(String.concat(cs)), fa, argv, o, ref, vcfpath, cs, DST.start_ok_gd(L.defs(String.concat(cs)), fa, argv, o, ref, vcfpath, cs, ha, hab), start_k(L.defs(String.concat(cs)), Norm.start(argv)))
