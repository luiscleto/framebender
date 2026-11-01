import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_sim.bend as SA
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_fin.bend as DF
import ./proof_b_drive_finms.bend as FMS
import ./proof_base.bend as PB
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Helpers for proof_b_drive.bend: pump_ok. Norm.pump handles lines while
# advance says Went (each lowers S.measure, or keeps it and lowers the
# records' S.mrec: with the two fuels, neither runs out: LX), then
# ends the step: out with an Ask (Want, Yield), idle (Idle: More, or the end
# of the run at the end of the file), or finish (Ended).

# The end of the run
# ==================

law or_false:
  for +x: Bool
  for +h: {Bool.or(x, False{}) == True{} : Bool}
  {x == True{} : Bool}

def or_false(x, h):
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PB.false_ne_true(h))

# A stopped run (Ended) finishes with the report.
law ended_go:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hs: {S.stopped(S.StP.md(p)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, p)))

def ended_go(fa, T, cs, O, N, p, hw, hr, hs, hg, ha, ef, hef):
  match p:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      DF.fin_mb(dfs, fa, T, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hw, hg, hr,
        DF.nl_halt(dfs, fa, cs, O, N, o, rp, src, pd, eof, back, wp, asked, fneed, hs), ef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, Some{+cc}}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      FMS.fin_ms_some(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha, ef, hef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, None{}}, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      FMS.fin_ms_none(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha,
        FMS.nl_halt_ms(dfs, fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, or_false(x, hs)), ef, hef)

# Idle: More before the end of the file, else the end of the run.
law idle_go:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +hsrc: {S.src_empty(S.StP.src(p)) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hns: {S.stopped(S.StP.md(p)) == False{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(S.mkSt(fa, p)))

def idle_go(fa, T, cs, O, N, p, hw, hr, hsrc, hg, hns, ha, ef, hef):
  match p:
    case S.StP{+o, +md, +src, +pd, False{}, +back, +wp, +asked, +fneed, +dfs}:
      +p2 = {S.StP{o, md, src, pd, False{}, back, wp, asked, fneed, dfs} : S.StP}
      DO.out_more(fa, T, cs, O, N, p2, Norm.out(S.mkSt(fa, p2), Pr.More{}), DO.out_ok(fa, cs, O, N, p2, Pr.More{}, hw, hg, DO.live_of(S.StP.md(p2), hns)), hr, hsrc, {==}, ha, ef, hef)
    case S.StP{+o, S.MBP{+rp}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      DF.fin_mb(dfs, fa, T, cs, O, N, o, rp, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hg, hr,
        DF.nl_eof_mb(dfs, fa, cs, O, N, o, rp, pd, back, wp, asked, fneed, hw), ef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, Some{+cc}}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      FMS.fin_ms_some(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hr, hg, ha, ef, hef)
    case S.StP{+o, S.MSP{R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o2, +ns, +x}, +qs, +ql, None{}}, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      FMS.fin_ms_none(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, Nil{}, pd, True{}, back, wp, asked, fneed, hw, hr, hg, ha,
        FMS.nl_eof_ms(dfs, fa, cs, O, N, o, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, pd, back, wp, asked, fneed, hw), ef, hef)
    case S.StP{+o, +md, Con{+x, +t}, +pd, True{}, +back, +wp, +asked, +fneed, +dfs}:
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(S.mkSt(fa, S.StP{o, md, Con{x, t}, pd, True{}, back, wp, asked, fneed, dfs}))), PB.false_ne_true(hsrc))

# The pump
# ========

law fuel_le:
  for +m2: Nat
  for +m: Nat
  for +f: Nat
  for +hlt: {Nat.is_lt(m2, m) == True{} : Bool}
  for +hf: {Nat.is_le(m, 1n+f) == True{} : Bool}
  {Nat.is_le(m2, f) == True{} : Bool}

def fuel_le(m2, m, f, hlt, hf):
  Equal.trans(Bool, Nat.is_le(m2, f), Nat.is_lt(m2, 1n+f), True{},
    Equal.sym(Bool, Nat.is_lt(m2, 1n+f), Nat.is_le(m2, f), N.lt_succ_iff(m2, f)),
    N.lt_le_trans(m2, m, 1n+f, hlt, hf))

# The fuel go computes: each source's bytes left plus two (with -m, the
# records of split lines count too). It bounds the measure and the records'.
def fuelN(+sps: List<&2, P.SrcP>) -> Nat:
  match sps:
    case Nil{}:
      0n
    case Con{P.SBP{+len, t, d, +at}, +rest}:
      Nat.add(Nat.add(U32.to_nat((len - at : U32)), 2n), fuelN(rest))
    case Con{P.SLP{q}, +rest}:
      Nat.add(Nat.add(U32.to_nat(0), 2n), fuelN(rest))
    case Con{P.SPP{+len, t, d, +at}, +rest}:
      Nat.add(Nat.add(U32.to_nat((len - at : U32)), 2n), fuelN(rest))
    case Con{P.SRP{l}, +rest}:
      Nat.add(Nat.add(U32.to_nat(0), 2n), fuelN(rest))

law fuel_eq:
  for +sps: List<&2, P.SrcP>
  {Norm.fuel.src(P.mkSrcs(sps)) == (P.mkSrcs(sps), fuelN(sps)) : List<&1, Norm.Src> & Nat}

def fuel_eq(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), fuelN(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SB{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SBP{len, t, d, at}) <> P.mkSrcs(rest), fuelN(P.SBP{len, t, d, at} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}
    case Con{P.SLP{+q}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), fuelN(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SL{q}, 0), _) == (Norm.SL{q} <> P.mkSrcs(rest), fuelN(P.SLP{q} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), fuelN(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SP{C.BT(len, t), at}, (len - at : U32)), _) == (P.mkSrc(P.SPP{len, t, d, at}) <> P.mkSrcs(rest), fuelN(P.SPP{len, t, d, at} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}
    case Con{P.SRP{+l}, +rest}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(rest)), (P.mkSrcs(rest), fuelN(rest)), fuel_eq(rest)) :
        {Norm.fuel.cons((Norm.SR{l}, 0), _) == (Norm.SR{l} <> P.mkSrcs(rest), fuelN(P.SRP{l} <> rest)) : List<&1, Norm.Src> & Nat}
      {==}

law fst_eq:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  {Norm.fuel.st(S.mkSt(fa, p)) == (S.mkSt(fa, p), fuelN(S.StP.src(p))) : Norm.St & Nat}

def fst_eq(fa, p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs}:
      %Equal.sym(List<&1, Norm.Src> & Nat, Norm.fuel.src(P.mkSrcs(src)), (P.mkSrcs(src), fuelN(src)), fuel_eq(src)) :
        {Norm.fuel.st.k(o, S.mkMd(md), _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs) == (S.mkSt(fa, S.StP{o, md, src, pd, eof, back, wp, asked, fneed, dfs}), fuelN(src)) : Norm.St & Nat}
      {==}

law add_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  for +hcd: {Nat.is_le(c, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}

def add_mono(a, b, c, d, hab, hcd):
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), N.le_add_mono_r(c, a, b, hab), N.le_add_mono_l(b, c, d, hcd))

law mrec_le:
  for +sps: List<&2, P.SrcP>
  {Nat.is_le(S.mrec(sps), fuelN(sps)) == True{} : Bool}

def mrec_le(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      add_mono(0n, Nat.add(U32.to_nat((len - at : U32)), 2n), S.mrec(rest), fuelN(rest), N.le_zero_l(Nat.add(U32.to_nat((len - at : U32)), 2n)), mrec_le(rest))
    case Con{P.SLP{+q}, +rest}:
      add_mono(0n, Nat.add(U32.to_nat(0), 2n), S.mrec(rest), fuelN(rest), N.le_zero_l(Nat.add(U32.to_nat(0), 2n)), mrec_le(rest))
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      add_mono(Nat.add(U32.to_nat((len - at : U32)), 2n), Nat.add(U32.to_nat((len - at : U32)), 2n), S.mrec(rest), fuelN(rest), N.le_refl(Nat.add(U32.to_nat((len - at : U32)), 2n)), mrec_le(rest))
    case Con{P.SRP{+l}, +rest}:
      add_mono(2n, Nat.add(U32.to_nat(0), 2n), S.mrec(rest), fuelN(rest), N.le_refl(2n), mrec_le(rest))

law msrc_le:
  for +sps: List<&2, P.SrcP>
  {Nat.is_le(S.msrc(sps), fuelN(sps)) == True{} : Bool}

def msrc_le(sps):
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +t, +d, +at}, +rest}:
      add_mono(Nat.add(U32.to_nat((len - at : U32)), 2n), Nat.add(U32.to_nat((len - at : U32)), 2n), S.msrc(rest), fuelN(rest), N.le_refl(Nat.add(U32.to_nat((len - at : U32)), 2n)), msrc_le(rest))
    case Con{P.SLP{+q}, +rest}:
      add_mono(2n, Nat.add(U32.to_nat(0), 2n), S.msrc(rest), fuelN(rest), N.le_refl(2n), msrc_le(rest))
    case Con{P.SPP{+len, +t, +d, +at}, +rest}:
      add_mono(0n, Nat.add(U32.to_nat((len - at : U32)), 2n), S.msrc(rest), fuelN(rest), N.le_zero_l(Nat.add(U32.to_nat((len - at : U32)), 2n)), msrc_le(rest))
    case Con{P.SRP{+l}, +rest}:
      add_mono(0n, Nat.add(U32.to_nat(0), 2n), S.msrc(rest), fuelN(rest), N.le_zero_l(Nat.add(U32.to_nat(0), 2n)), msrc_le(rest))

# The pump's invariant: the measure m within the input's fuel f1, and below
# it or the records' measure r within the records' fuel f2 (lexicographic).
def LXN(+m: Nat, +r: Nat, +f1: Nat, +f2: Nat) -> Bool:
  Nat.is_le(m, f1) && (Nat.is_lt(m, f1) || Nat.is_le(r, f2))

def LX(+p: S.StP, +f1: Nat, +f2: Nat) -> Bool:
  LXN(S.measure(p), S.mrec(S.StP.src(p)), f1, f2)

law aor:
  for +a: Bool
  for +c: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, Bool.or(c, b)) == True{} : Bool}

def aor(a, c, b, ha, hb):
  match c:
    case True{}:
      %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
      hb

law aol:
  for +a: Bool
  for +c: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hc: {c == True{} : Bool}
  {Bool.and(a, Bool.or(c, b)) == True{} : Bool}

def aol(a, c, b, ha, hc):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, Bool.or(c, b)) == True{} : Bool}
  %Equal.sym(Bool, c, True{}, hc) : {Bool.and(True{}, Bool.or(_, b)) == True{} : Bool}
  {==}

# A step with records' fuel left (m and r: before; m2 and r2: after).
law lx_s2:
  for +m: Nat
  for +r: Nat
  for +r2: Nat
  for +f1: Nat
  for +h: Nat
  for +c: Bool
  for +hc: {Nat.is_lt(m, f1) == c : Bool}
  for +hle: {Nat.is_le(m, f1) == True{} : Bool}
  for +hor: {Bool.or(c, Nat.is_le(r, 1n+h)) == True{} : Bool}
  for +hr: {Nat.is_lt(r2, r) == True{} : Bool}
  {LXN(m, r2, f1, h) == True{} : Bool}

def lx_s2(m, r, r2, f1, h, c, hc, hle, hor, hr):
  match c:
    case True{}:
      aol(Nat.is_le(m, f1), Nat.is_lt(m, f1), Nat.is_le(r2, h), hle, hc)
    case False{}:
      aor(Nat.is_le(m, f1), Nat.is_lt(m, f1), Nat.is_le(r2, h), hle, fuel_le(r2, r, h, hr, hor))

law lx_s1:
  for +m: Nat
  for +r: Nat
  for +m2: Nat
  for +r2: Nat
  for +f1: Nat
  for +h: Nat
  for +a: Bool
  for +ha: {Nat.is_lt(m2, m) == a : Bool}
  for +hle: {Nat.is_le(m, f1) == True{} : Bool}
  for +hor: {Bool.or(Nat.is_lt(m, f1), Nat.is_le(r, 1n+h)) == True{} : Bool}
  for +hl: {Bool.or(a, Bool.and(Nat.is_eq(m2, m), Nat.is_lt(r2, r))) == True{} : Bool}
  {LXN(m2, r2, f1, h) == True{} : Bool}

def lx_s1(m, r, m2, r2, f1, h, a, ha, hle, hor, hl):
  match a:
    case True{}:
      +hlt = N.lt_le_trans(m2, m, f1, ha, hle)
      aol(Nat.is_le(m2, f1), Nat.is_lt(m2, f1), Nat.is_le(r2, h), N.lt_to_le(m2, f1, hlt), hlt)
    case False{}:
      +heq = N.eq_sound(m2, m, PB.and_true_l(Nat.is_eq(m2, m), Nat.is_lt(r2, r), hl))
      %Equal.sym(Nat, m2, m, heq) : {LXN(_, r2, f1, h) == True{} : Bool}
      lx_s2(m, r, r2, f1, h, Nat.is_lt(m, f1), {==}, hle, hor, PB.and_true_r(Nat.is_eq(m2, m), Nat.is_lt(r2, r), hl))

law lx_step:
  for +m: Nat
  for +r: Nat
  for +m2: Nat
  for +r2: Nat
  for +f1: Nat
  for +h: Nat
  for +hI: {LXN(m, r, f1, 1n+h) == True{} : Bool}
  for +hl: {Bool.or(Nat.is_lt(m2, m), Bool.and(Nat.is_eq(m2, m), Nat.is_lt(r2, r))) == True{} : Bool}
  {LXN(m2, r2, f1, h) == True{} : Bool}

def lx_step(m, r, m2, r2, f1, h, hI, hl):
  lx_s1(m, r, m2, r2, f1, h, Nat.is_lt(m2, m), {==},
    PB.and_true_l(Nat.is_le(m, f1), Bool.or(Nat.is_lt(m, f1), Nat.is_le(r, 1n+h)), hI),
    PB.and_true_r(Nat.is_le(m, f1), Bool.or(Nat.is_lt(m, f1), Nat.is_le(r, 1n+h)), hI), hl)

# The records' fuel spent: refilled with n >= r2, the input's goes down.
law lt_g:
  for +m2: Nat
  for +g: Nat
  for +h: {Nat.is_lt(m2, 1n+g) == True{} : Bool}
  {Nat.is_le(m2, g) == True{} : Bool}

def lt_g(m2, g, h):
  Equal.trans(Bool, Nat.is_le(m2, g), Nat.is_lt(m2, 1n+g), True{}, Equal.sym(Bool, Nat.is_lt(m2, 1n+g), Nat.is_le(m2, g), N.lt_succ_iff(m2, g)), h)

law lx_f2:
  for +m: Nat
  for +r: Nat
  for +r2: Nat
  for +g: Nat
  for +c: Bool
  for +hc: {Nat.is_lt(m, 1n+g) == c : Bool}
  for +hor: {Bool.or(c, Nat.is_le(r, 0n)) == True{} : Bool}
  for +hr: {Nat.is_lt(r2, r) == True{} : Bool}
  {Nat.is_le(m, g) == True{} : Bool}

def lx_f2(m, r, r2, g, c, hc, hor, hr):
  match c:
    case True{}:
      lt_g(m, g, hc)
    case False{}:
      Empty.absurd({Nat.is_le(m, g) == True{} : Bool}, PB.false_ne_true(
        Equal.trans(Bool, False{}, Nat.is_lt(r2, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r2, 0n), False{}, N.lt_zero(r2)), N.lt_le_trans(r2, r, 0n, hr, hor))))

law lx_f1:
  for +m: Nat
  for +r: Nat
  for +m2: Nat
  for +r2: Nat
  for +g: Nat
  for +a: Bool
  for +ha: {Nat.is_lt(m2, m) == a : Bool}
  for +hle: {Nat.is_le(m, 1n+g) == True{} : Bool}
  for +hor: {Bool.or(Nat.is_lt(m, 1n+g), Nat.is_le(r, 0n)) == True{} : Bool}
  for +hl: {Bool.or(a, Bool.and(Nat.is_eq(m2, m), Nat.is_lt(r2, r))) == True{} : Bool}
  {Nat.is_le(m2, g) == True{} : Bool}

def lx_f1(m, r, m2, r2, g, a, ha, hle, hor, hl):
  match a:
    case True{}:
      lt_g(m2, g, N.lt_le_trans(m2, m, 1n+g, ha, hle))
    case False{}:
      +heq = N.eq_sound(m2, m, PB.and_true_l(Nat.is_eq(m2, m), Nat.is_lt(r2, r), hl))
      %Equal.sym(Nat, m2, m, heq) : {Nat.is_le(_, g) == True{} : Bool}
      lx_f2(m, r, r2, g, Nat.is_lt(m, 1n+g), {==}, hor, PB.and_true_r(Nat.is_eq(m2, m), Nat.is_lt(r2, r), hl))

law lx_fill:
  for +m: Nat
  for +r: Nat
  for +m2: Nat
  for +r2: Nat
  for +g: Nat
  for +n: Nat
  for +hI: {LXN(m, r, 1n+g, 0n) == True{} : Bool}
  for +hl: {Bool.or(Nat.is_lt(m2, m), Bool.and(Nat.is_eq(m2, m), Nat.is_lt(r2, r))) == True{} : Bool}
  for +hn: {Nat.is_le(r2, n) == True{} : Bool}
  {LXN(m2, r2, g, n) == True{} : Bool}

def lx_fill(m, r, m2, r2, g, n, hI, hl, hn):
  aor(Nat.is_le(m2, g), Nat.is_lt(m2, g), Nat.is_le(r2, n),
    lx_f1(m, r, m2, r2, g, Nat.is_lt(m2, m), {==},
      PB.and_true_l(Nat.is_le(m, 1n+g), Bool.or(Nat.is_lt(m, 1n+g), Nat.is_le(r, 0n)), hI),
      PB.and_true_r(Nat.is_le(m, 1n+g), Bool.or(Nat.is_lt(m, 1n+g), Nat.is_le(r, 0n)), hI), hl), hn)

law or_lf:
  for +x: Bool
  for +y: Bool
  for +hx: {x == False{} : Bool}
  for +h: {Bool.or(x, y) == True{} : Bool}
  {y == True{} : Bool}

def or_lf(x, y, hx, h):
  match x:
    case True{}:
      Empty.absurd({y == True{} : Bool}, PB.false_ne_true(Equal.sym(Bool, True{}, False{}, hx)))
    case False{}:
      h

# Both fuels spent: no step can go lower.
law lx_z1:
  for +m: Nat
  for +r: Nat
  for +m2: Nat
  for +r2: Nat
  for +a: Bool
  for +ha: {Nat.is_lt(m2, m) == a : Bool}
  for +hle: {Nat.is_le(m, 0n) == True{} : Bool}
  for +hor: {Bool.or(Nat.is_lt(m, 0n), Nat.is_le(r, 0n)) == True{} : Bool}
  for +hl: {Bool.or(a, Bool.and(Nat.is_eq(m2, m), Nat.is_lt(r2, r))) == True{} : Bool}
  Empty

def lx_z1(m, r, m2, r2, a, ha, hle, hor, hl):
  match a:
    case True{}:
      PB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(m2, 0n), True{}, Equal.sym(Bool, Nat.is_lt(m2, 0n), False{}, N.lt_zero(m2)), N.lt_le_trans(m2, m, 0n, ha, hle)))
    case False{}:
      +hr = PB.and_true_r(Nat.is_eq(m2, m), Nat.is_lt(r2, r), hl)
      +hr0 = or_lf(Nat.is_lt(m, 0n), Nat.is_le(r, 0n), N.lt_zero(m), hor)
      PB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(r2, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r2, 0n), False{}, N.lt_zero(r2)), N.lt_le_trans(r2, r, 0n, hr, hr0)))

def is_went(a: Norm.Adv) -> Bool:
  match a:
    case Norm.Went{st}:
      True{}
    case _:
      False{}

# A step that is not Went ends the pump, with any fuel.
law pump_other:
  for +f: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  for +hnw: {is_went(a) == False{} : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(f, a))

def pump_other(f, a, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, hnw):
  match f a:
    case 0n Norm.Went{st}:
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(0n, Norm.Went{st})), PB.false_ne_true(Equal.sym(Bool, True{}, False{}, hnw)))
    case 1n+g Norm.Went{st}:
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(1n+g, Norm.Went{st})), PB.false_ne_true(Equal.sym(Bool, True{}, False{}, hnw)))
    case _ Norm.Want{st, +r}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+eq, a5) = a4
      (+erq, a6) = a5
      (eask, a7) = a6
      (ens, a8) = a7
      (emr, a9) = a8
      (eeof, a10) = a9
      (eg, a11) = a10
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.out(_, Pr.Ask{r}))
      DO.out_ask(fa, T, cs, O, N, p2, r, Norm.out(S.mkSt(fa, p2), Pr.Ask{r}), DO.out_ok(fa, cs, O, N, p2, Pr.Ask{r}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, eq, erq, emr, eask,
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Idle{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+esrc, a5) = a4
      (eask, a6) = a5
      (eeof, a7) = a6
      (ens, a8) = a7
      (eg, a9) = a8
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.idle(_))
      idle_go(fa, T, cs, O, N, p2, wf2, er2, esrc, eg, ens, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Ended{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (eask, a5) = a4
      (+estop, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(_))
      ended_go(fa, T, cs, O, N, p2, wf2, er2, estop, eg, Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))
    case _ Norm.Yield{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+eask, a5) = a4
      (ens, a6) = a5
      (eeof, a7) = a6
      (eg, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.out(_, Pr.Ask{Nil{}}))
      DO.out_ask(fa, T, cs, O, N, p2, Nil{}, Norm.out(S.mkSt(fa, p2), Pr.Ask{Nil{}}), DO.out_ok(fa, cs, O, N, p2, Pr.Ask{Nil{}}, wf2, eg, DO.live_of(S.StP.md(p2), ens)), er2, {==}, {==}, DO.mbr_nil(S.StP.md(p2)),
        Equal.trans(Maybe<&2, List<&2, Pr.Req>>, S.StP.asked(p2), S.StP.asked(p), None{}, eask, ha),
        ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef))

# The pump's induction on its input's fuel g (pump.r's on the records').
def IHP(+g: Nat, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +ef: Bool) -> Type:
  @q: S.StP -> @a: Norm.Adv -> {LX(q, g, 0n) == True{} : Bool} -> {S.StP.asked(q) == None{} : Maybe<&2, List<&2, Pr.Req>> } -> {S.StP.eof(q) == ef : Bool} ->
    S.AdvG(fa, T, cs, O, N, q, a) -> DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(g, a))

law pumpR:
  for +f2: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  for +g: Nat
  for +hI: {LX(p, g, f2) == True{} : Bool}
  for ih: IHP(g, fa, T, cs, O, N, ef)
  DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(g, Norm.pump.r(f2, a)))

def pumpR(f2, a, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, g, hI, ih):
  match f2 a:
    case 1n+h Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+elt, a5) = a4
      (+eask2, a6) = a5
      (+eeof, a7) = a6
      (+eg2, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(g, Norm.pump.r(h, Norm.advance(_))))
      pumpR(h, Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, eask2, ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef),
        SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg2), g,
        lx_step(S.measure(p), S.mrec(S.StP.src(p)), S.measure(p2), S.mrec(S.StP.src(p2)), g, h, hI, elt), ih)
    case 0n Norm.Went{st}:
      ih(p, Norm.Went{st}, hI, ha, hef, ag)
    case _ Norm.Want{st, +r}:
      pump_other(g, Norm.Want{st, r}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Idle{st}:
      pump_other(g, Norm.Idle{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Ended{st}:
      pump_other(g, Norm.Ended{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Yield{st}:
      pump_other(g, Norm.Yield{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})

law pumpL:
  for +f: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  for +hI: {LX(p, f, 0n) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(f, a))

def pumpL(f, a, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, hI):
  match f a:
    case 0n Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (wf2, a3) = a2
      (er2, a4) = a3
      (+elt, a5) = a4
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(0n, Norm.Went{st})),
        lx_z1(S.measure(p), S.mrec(S.StP.src(p)), S.measure(p2), S.mrec(S.StP.src(p2)), Nat.is_lt(S.measure(p2), S.measure(p)), {==},
          PB.and_true_l(Nat.is_le(S.measure(p), 0n), Bool.or(Nat.is_lt(S.measure(p), 0n), Nat.is_le(S.mrec(S.StP.src(p)), 0n)), hI),
          PB.and_true_r(Nat.is_le(S.measure(p), 0n), Bool.or(Nat.is_lt(S.measure(p), 0n), Nat.is_le(S.mrec(S.StP.src(p)), 0n)), hI), elt))
    case 1n+g Norm.Went{st}:
      (+p2, a1) = ag
      (est, a2) = a1
      (+wf2, a3) = a2
      (+er2, a4) = a3
      (+elt, a5) = a4
      (+eask2, a6) = a5
      (+eeof, a7) = a6
      (+eg2, a8) = a7
      %Equal.sym(Norm.St, st, S.mkSt(fa, p2), est) : DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(g, Norm.pump.fill(Norm.fuel.st(_))))
      %Equal.sym(Norm.St & Nat, Norm.fuel.st(S.mkSt(fa, p2)), (S.mkSt(fa, p2), fuelN(S.StP.src(p2))), fst_eq(fa, p2)) :
        DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(g, Norm.pump.fill(_)))
      pumpR(fuelN(S.StP.src(p2)), Norm.advance(S.mkSt(fa, p2)), fa, T, cs, O, N, p2, hb, eask2, ef, Equal.trans(Bool, S.StP.eof(p2), S.StP.eof(p), ef, eeof, hef),
        SA.adv_ok(fa, T, cs, O, N, p2, hb, wf2, er2, eg2), g,
        lx_fill(S.measure(p), S.mrec(S.StP.src(p)), S.measure(p2), S.mrec(S.StP.src(p2)), g, fuelN(S.StP.src(p2)), hI, elt, mrec_le(S.StP.src(p2))),
        +q => a => +hq => +haq => +heq => agq => pumpL(g, a, fa, T, cs, O, N, q, hb, haq, ef, heq, agq, hq))
    case _ Norm.Want{st, +r}:
      pump_other(f, Norm.Want{st, r}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Idle{st}:
      pump_other(f, Norm.Idle{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Ended{st}:
      pump_other(f, Norm.Ended{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})
    case _ Norm.Yield{st}:
      pump_other(f, Norm.Yield{st}, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, {==})

law lx_init:
  for +p: S.StP
  for +f: Nat
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  {LX(p, 1n+f, 0n) == True{} : Bool}

def lx_init(p, f, hf):
  +hlt = Equal.trans(Bool, Nat.is_lt(S.measure(p), 1n+f), Nat.is_le(S.measure(p), f), True{}, N.lt_succ_iff(S.measure(p), f), hf)
  aol(Nat.is_le(S.measure(p), 1n+f), Nat.is_lt(S.measure(p), 1n+f), Nat.is_le(S.mrec(S.StP.src(p)), 0n), N.lt_to_le(S.measure(p), 1n+f, hlt), hlt)

law pump_go:
  for +f: Nat
  for a: Norm.Adv
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {S.StP.eof(p) == ef : Bool}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  for ag: S.AdvG(fa, T, cs, O, N, p, a)
  DO.StepG2(fa, T, cs, O, N, ef, Norm.pump(1n+f, a))

def pump_go(f, a, fa, T, cs, O, N, p, hb, ha, ef, hef, hf, ag):
  pumpL(1n+f, a, fa, T, cs, O, N, p, hb, ha, ef, hef, ag, lx_init(p, f, hf))

# The pump with the step's eof flag and nothing asked in More (StepG2).
law pump_ok_h2:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +f: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  DO.StepG2(fa, T, cs, O, N, S.StP.eof(p), Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))))

def pump_ok_h2(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf):
  pump_go(f, Norm.advance(S.mkSt(fa, p)), fa, T, cs, O, N, p, hb, ha, S.StP.eof(p), {==}, hf, SA.adv_ok(fa, T, cs, O, N, p, hb, hw, hr, hg))

# pump_ok, as proof_b_drive.bend states it.
law pump_ok_h:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +f: Nat
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hf: {Nat.is_le(S.measure(p), f) == True{} : Bool}
  DR.StepG(fa, T, cs, O, N, Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))))

def pump_ok_h(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf):
  DO.sg2w(fa, T, cs, O, N, S.StP.eof(p), Norm.pump(1n+f, Norm.advance(S.mkSt(fa, p))), pump_ok_h2(fa, T, cs, O, N, p, f, hb, hw, hr, ha, hg, hf))
