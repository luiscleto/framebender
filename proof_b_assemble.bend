import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./proof_b_mdefs.bend as MQ
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DD
import ./proof_b_drive.bend as DRV
import ./proof_b_budget_api.bend as API
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_step.bend as DS
import ./proof_base.bend as PB
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-bytes@0.1.0.0/defs.bend as D
import ./proof_b_fa_bytes.bend as FB
import ./proof_b_drive_chunk.bend as DC

# The law machine, assembled (notes/bytes_proofs_drive.md, "Assembly"): the
# driver (MACHINE.bend's drive, dstep, absorb, result) keeps an invariant
# Good: the machine's state is pictured by a good p standing for the report
# T with what the driver collected (the simulation, proof_b_drive.bend), and
# reads + need <= the bound, need <= the fuel left (the budget,
# proof_b_budget_api.bend). Each driver step keeps Good with one less fuel,
# so drive reaches the stopped state with the report.

# ---------------------------------------------------------------------------
# A step's guarantee, with what the assembly needs on top of DD.StepG
# ---------------------------------------------------------------------------

# DO.StepG2 (proof_b_drive_out.bend) is DD.StepG plus: More's state has
# nothing asked (more_ok) and the step's eof flag ef is False; Ask's state
# has eof ef (False after a piece, True after the end of the file, as before
# for an answer). sg_chunk waits for pb-lines' step_chunk_h2 (notes).
def sg_chunk(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)})):
  DC.step_chunk_h2(fa, T, c, cs, O, N, p, hb, hm, hr, hcb, hcn, hg)

def sg_eof(+fa: List<&2, B.Contig>, +T: R.Report, +O: String, +N: List<&2, B.Note>, +p: S.StP,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DD.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DO.StepG2(fa, T, Nil{}, O, N, True{}, Norm.step(S.mkSt(fa, p), Pr.Eof{})):
  DS.step_eof_h2(fa, T, O, N, p, hb, hm, hr, hg)

def sg_ref(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +rs: List<&2, Pr.Req>,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  hr: {S.report(fa, cs, O, N, p) == T : R.Report},
  ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  hq: {E.reqs_ok(rs) == True{} : Bool},
  hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool}) ->
  DO.StepG2(fa, T, cs, O, N, S.StP.eof(p), Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)})):
  DS.step_ref_h2(fa, T, cs, O, N, p, rs, hb, hw, hr, ha, hq, hp, hmr, hg)

# The FASTA's contigs are bytes when the file is (B.Fasta.parse keeps the
# letters it reads). Open: a spec-level fact about parse (notes).
def fa_bytes_parse(+fasta: String, hb: {E.is_bytes(fasta) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.parse(fasta)) == True{} : Bool}:
  FB.fa_bytes_parse(fasta, hb)

# ---------------------------------------------------------------------------
# The driver's invariant
# ---------------------------------------------------------------------------

def txt(+cs: List<&2, String>) -> Bool:
  E.all_bytes(cs) && E.pieces_ok(cs)

def GoodN(+fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, st: Norm.St, nx: Pr.Next, +dcs: List<&2, String>, +de: Bool, +rd: Nat, +g: Bool, +out: String, +notes: List<&2, B.Note>) -> Type:
  match nx:
    case Pr.Finish{c}:
      {g == True{} : Bool} & ({R.Report{out, notes, c} == T : R.Report} & ({Nat.is_le(Nat.add(rd, 1n), lim) == True{} : Bool} & {Nat.is_le(1n, f) == True{} : Bool}))
    case Pr.More{}:
      &p: S.StP -> ({st == S.mkSt(fa, p) : Norm.St} & ({DD.more_ok(fa, p) == True{} : Bool}
        & ({S.report(fa, dcs, out, notes, p) == T : R.Report} & ({S.guard(out, notes, p) == True{} : Bool}
        & ({g == True{} : Bool} & ({de == False{} : Bool} & ({txt(dcs) == True{} : Bool}
        & ({API.bi(fa, T, p, dcs, de, Pr.More{}, out) == True{} : Bool}
        & ({Nat.is_le(Nat.add(rd, API.need(fa, T, p, dcs, de, Pr.More{}, out)), lim) == True{} : Bool}
        & {Nat.is_le(API.need(fa, T, p, dcs, de, Pr.More{}, out), f) == True{} : Bool})))))))))
    case Pr.Ask{rs}:
      &p: S.StP -> ({st == S.mkSt(fa, p) : Norm.St} & ({S.WF(fa, p) == True{} : Bool}
        & ({S.report(fa, dcs, out, notes, p) == T : R.Report} & ({E.reqs_ok(rs) == True{} : Bool} & ({rs == S.rq(rs) : List<&2, Pr.Req>}
        & ({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool} & ({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
        & ({S.guard(out, notes, p) == True{} : Bool} & ({g == True{} : Bool} & ({Bool.or(Bool.not(de), S.StP.eof(p)) == True{} : Bool}
        & ({txt(dcs) == True{} : Bool} & ({API.bi(fa, T, p, dcs, de, Pr.Ask{rs}, out) == True{} : Bool}
        & ({Nat.is_le(Nat.add(rd, API.need(fa, T, p, dcs, de, Pr.Ask{rs}, out)), lim) == True{} : Bool}
        & {Nat.is_le(API.need(fa, T, p, dcs, de, Pr.Ask{rs}, out), f) == True{} : Bool})))))))))))))

def GoodD(+fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, st: Norm.St, +nx: Pr.Next, +dcs: List<&2, String>, +de: Bool, +rd: Nat, +g: Bool, +out: String, +notes: List<&2, B.Note>, done: Maybe<&2, Nat>) -> Type:
  match done:
    case Some{c}:
      {g == True{} : Bool} & ({R.Report{out, notes, c} == T : R.Report} & {Nat.is_le(rd, lim) == True{} : Bool})
    case None{}:
      GoodN(fa, T, lim, f, st, nx, dcs, de, rd, g, out, notes)

# Good(fa, T, lim, f, d): the driver state d leads to the report T within
# the bound lim and the fuel f.
def Good(+fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, d: MQ.DSt) -> Type:
  match d:
    case MQ.DSt{st, nx, dcs, de, rd, g, out, notes, done}:
      GoodD(fa, T, lim, f, st, nx, dcs, de, rd, g, out, notes, done)

# After one driver step from fuel f: nothing at 0 (a good state that has not
# stopped has fuel left), else Good with one less.
def StepR(+fa: List<&2, B.Contig>, +T: R.Report, +lim: Nat, +f: Nat, d: MQ.DSt) -> Type:
  match f:
    case 0n:
      Empty
    case 1n+h:
      Good(fa, T, lim, h, d)

# ---------------------------------------------------------------------------
# Arithmetic of the budget
# ---------------------------------------------------------------------------

law sum1:
  for +n2: Nat
  for +R: Nat
  {Nat.add(n2, Nat.add(R, 1n)) == 1n+Nat.add(n2, R) : Nat}

def sum1(n2, R):
  Equal.trans(Nat, Nat.add(n2, Nat.add(R, 1n)), Nat.add(n2, 1n+R), 1n+Nat.add(n2, R),
    Equal.cong(Nat, Nat, z => Nat.add(n2, z), Nat.add(R, 1n), 1n+R, N.add_one(R)), N.add_succ(n2, R))

# reads + need stays within the bound.
law ar_lim:
  for +rd: Nat
  for +R: Nat
  for +n2: Nat
  for +n1: Nat
  for +lim: Nat
  for +hd: {Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), n1) == True{} : Bool}
  for +hl: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(rd, R), n2), lim) == True{} : Bool}

def ar_lim(rd, R, n2, n1, lim, hd, hl):
  +h1 = N.le_trans(Nat.add(R, n2), Nat.add(n2, R), Nat.add(n2, Nat.add(R, 1n)),
    %N.add_comm(R, n2) : {Nat.is_le(Nat.add(R, n2), _) == True{} : Bool}; N.le_refl(Nat.add(R, n2)),
    N.le_add_mono_l(n2, R, Nat.add(R, 1n), N.le_add_r(R, 1n)))
  +h2 = N.le_trans(Nat.add(R, n2), Nat.add(n2, Nat.add(R, 1n)), n1, h1, hd)
  +h3 = N.le_add_mono_l(rd, Nat.add(R, n2), n1, h2)
  %Equal.sym(Nat, Nat.add(Nat.add(rd, R), n2), Nat.add(rd, Nat.add(R, n2)), N.add_assoc(rd, R, n2)) : {Nat.is_le(_, lim) == True{} : Bool}
  N.le_trans(Nat.add(rd, Nat.add(R, n2)), Nat.add(rd, n1), lim, h3, hl)

# need fits the fuel left.
law ar_fuel:
  for +R: Nat
  for +n2: Nat
  for +n1: Nat
  for +f: Nat
  for +hd: {Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), n1) == True{} : Bool}
  for +hf: {Nat.is_le(n1, 1n+f) == True{} : Bool}
  {Nat.is_le(n2, f) == True{} : Bool}

def ar_fuel(R, n2, n1, f, hd, hf):
  +h1 = N.le_trans(Nat.add(n2, Nat.add(R, 1n)), n1, 1n+f, hd, hf)
  +h2 = Equal.trans(Bool, Nat.is_le(1n+Nat.add(n2, R), 1n+f), Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), 1n+f), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+f), 1n+Nat.add(n2, R), Nat.add(n2, Nat.add(R, 1n)), Equal.sym(Nat, Nat.add(n2, Nat.add(R, 1n)), 1n+Nat.add(n2, R), sum1(n2, R))), h1)
  N.le_trans(n2, Nat.add(n2, R), f, N.le_add_r(n2, R), h2)

# No fuel left is impossible while need is positive.
law ar_zero:
  for +R: Nat
  for +n2: Nat
  for +n1: Nat
  for +hd: {Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), n1) == True{} : Bool}
  for +hf: {Nat.is_le(n1, 0n) == True{} : Bool}
  Empty

def ar_zero(R, n2, n1, hd, hf):
  +h1 = N.le_trans(Nat.add(n2, Nat.add(R, 1n)), n1, 0n, hd, hf)
  PB.false_ne_true(Equal.trans(Bool, False{}, Nat.is_le(Nat.add(n2, Nat.add(R, 1n)), 0n), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, 0n), 1n+Nat.add(n2, R), Nat.add(n2, Nat.add(R, 1n)), Equal.sym(Nat, Nat.add(n2, Nat.add(R, 1n)), 1n+Nat.add(n2, R), sum1(n2, R))), h1))

# The end: need >= reads + 2 as a drop to a need of 1.
law fin_drop:
  for +R: Nat
  for +n1: Nat
  for +h: {Nat.is_le(Nat.add(R, 2n), n1) == True{} : Bool}
  {Nat.is_le(Nat.add(1n, Nat.add(R, 1n)), n1) == True{} : Bool}

def fin_drop(R, n1, h):
  %N.add_succ(R, 1n) : {Nat.is_le(_, n1) == True{} : Bool}
  h

law le_pred:
  for +rd: Nat
  for +lim: Nat
  for +h: {Nat.is_le(Nat.add(rd, 1n), lim) == True{} : Bool}
  {Nat.is_le(rd, lim) == True{} : Bool}

def le_pred(rd, lim, h):
  N.le_trans(rd, Nat.add(rd, 1n), lim, N.le_add_r(rd, 1n), h)

law de_false:
  for +de: Bool
  for +ef: Bool
  for +hde: {Bool.or(Bool.not(de), ef) == True{} : Bool}
  for +hef: {ef == False{} : Bool}
  {de == False{} : Bool}

def de_false(de, ef, hde, hef):
  match de:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(%hef : {Bool.or(False{}, _) == True{} : Bool}; hde))
    case False{}:
      {==}

law and_tt:
  for +G: Bool
  for +hG: {G == True{} : Bool}
  {Bool.and(G, True{}) == True{} : Bool}

def and_tt(G, hG):
  %Equal.sym(Bool, G, True{}, hG) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# ---------------------------------------------------------------------------
# One driver step: the budget's part, as continuations
# ---------------------------------------------------------------------------

# For every picture p2 of the step's next state (More or Ask): pb-cut's
# invariant and the drop of need (API.bud_*).
def Kont(+fa: List<&2, B.Contig>, +T: R.Report, s: Norm.Step, +cs2: List<&2, String>, +de2: Bool, +R: Nat, +n1: Nat, +O: String, +N: List<&2, B.Note>) -> Type:
  @p2: S.StP -> @nx2: Pr.Next -> @t: String -> {API.sst(s) == S.mkSt(fa, p2) : Norm.St} -> {API.snx(s) == nx2 : Pr.Next}
    -> {API.sout(s) == Some{t} : Maybe<&2, String>} -> {S.WF(fa, p2) == True{} : Bool}
    -> {S.report(fa, cs2, String.append(O, t), List.append(&2, B.Note, N, API.sns(s)), p2) == T : R.Report}
    -> {S.guard(String.append(O, t), List.append(&2, B.Note, N, API.sns(s)), p2) == True{} : Bool}
    -> ({API.bi(fa, T, p2, cs2, de2, nx2, String.append(O, t)) == True{} : Bool}
      & {Nat.is_le(Nat.add(API.need(fa, T, p2, cs2, de2, nx2, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool})

# When the step ends the run (API.bud_*_fin).
def KFin(s: Norm.Step, +R: Nat, +n1: Nat) -> Type:
  @code: Nat -> {API.snx(s) == Pr.Finish{code} : Pr.Next} -> {Nat.is_le(Nat.add(R, 2n), n1) == True{} : Bool}

# The driver absorbs a step whose next is More
# ============================================

law am_more.k:
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +p2: S.StP
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == S.mkSt(fa, p2) : Norm.St}
  for +hmo: {DD.more_ok(fa, p2) == True{} : Bool}
  for +rep: {S.report(fa, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +hef: {ef == False{} : Bool}
  for +bi2: {API.bi(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)) == True{} : Bool}
  for +drop: {Nat.is_le(Nat.add(API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  Good(fa, T, lim, h, MQ.absorb(Norm.Step{st2, b, ns, Pr.More{}}, cs2, de2, rd2, G, O, N))

def am_more.k(h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, t, p2, hfu, eout, est, hmo, rep, gd, hef, bi2, drop):
  %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(fa, T, lim, h, MQ.absorb.k(st2, Pr.More{}, cs2, de2, rd2, G, MQ.absorb.out(_, O), N, ns))
  (p2, (est, (hmo, (rep, (gd, (and_tt(G, hG), (de_false(de2, ef, hde, hef), (htx, (bi2,
    (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t))), lim) == True{} : Bool}; ar_lim(rd, R, API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)), n1, lim, drop, hlim),
    ar_fuel(R, API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)), n1, h, drop, hfu)))))))))))

law am_more:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +t: String
  for +p2: S.StP
  for +hfu: {Nat.is_le(n1, f) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == S.mkSt(fa, p2) : Norm.St}
  for +hmo: {DD.more_ok(fa, p2) == True{} : Bool}
  for +rep: {S.report(fa, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +hef: {ef == False{} : Bool}
  for bud: {API.bi(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)) == True{} : Bool} & {Nat.is_le(Nat.add(API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.absorb(Norm.Step{st2, b, ns, Pr.More{}}, cs2, de2, rd2, G, O, N))

def am_more(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, t, p2, hfu, eout, est, hmo, rep, gd, hef, bud):
  match f:
    case 0n:
      (bi2, drop) = bud
      ar_zero(R, API.need(fa, T, p2, cs2, de2, Pr.More{}, String.append(O, t)), n1, drop, hfu)
    case 1n+h:
      (bi2, drop) = bud
      am_more.k(h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, t, p2, hfu, eout, est, hmo, rep, gd, hef, bi2, drop)

# ... whose next is Ask
# =====================

law am_ask.k:
  for +h: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +rs2: List<&2, Pr.Req>
  for +t: String
  for +p2: S.StP
  for +hfu: {Nat.is_le(n1, 1n+h) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == S.mkSt(fa, p2) : Norm.St}
  for +wf: {S.WF(fa, p2) == True{} : Bool}
  for +rep: {S.report(fa, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +hq: {E.reqs_ok(rs2) == True{} : Bool}
  for +hrq: {rs2 == S.rq(rs2) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p2), rs2) == True{} : Bool}
  for +hask: {S.StP.asked(p2) == S.asked_of(rs2) : Maybe<&2, List<&2, Pr.Req>>}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +heof: {S.StP.eof(p2) == ef : Bool}
  for +bi2: {API.bi(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)) == True{} : Bool}
  for +drop: {Nat.is_le(Nat.add(API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  Good(fa, T, lim, h, MQ.absorb(Norm.Step{st2, b, ns, Pr.Ask{rs2}}, cs2, de2, rd2, G, O, N))

def am_ask.k(h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, rs2, t, p2, hfu, eout, est, wf, rep, hq, hrq, hmr, hask, gd, heof, bi2, drop):
  %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(fa, T, lim, h, MQ.absorb.k(st2, Pr.Ask{rs2}, cs2, de2, rd2, G, MQ.absorb.out(_, O), N, ns))
  (p2, (est, (wf, (rep, (hq, (hrq, (hmr, (hask, (gd, (and_tt(G, hG),
    (%Equal.sym(Bool, S.StP.eof(p2), ef, heof) : {Bool.or(Bool.not(de2), _) == True{} : Bool}; hde,
    (htx, (bi2,
    (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t))), lim) == True{} : Bool}; ar_lim(rd, R, API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), n1, lim, drop, hlim),
    ar_fuel(R, API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), n1, h, drop, hfu)))))))))))))))

law am_ask:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +rs2: List<&2, Pr.Req>
  for +t: String
  for +p2: S.StP
  for +hfu: {Nat.is_le(n1, f) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +est: {st2 == S.mkSt(fa, p2) : Norm.St}
  for +wf: {S.WF(fa, p2) == True{} : Bool}
  for +rep: {S.report(fa, cs2, String.append(O, t), List.append(&2, B.Note, N, ns), p2) == T : R.Report}
  for +hq: {E.reqs_ok(rs2) == True{} : Bool}
  for +hrq: {rs2 == S.rq(rs2) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p2), rs2) == True{} : Bool}
  for +hask: {S.StP.asked(p2) == S.asked_of(rs2) : Maybe<&2, List<&2, Pr.Req>>}
  for +gd: {S.guard(String.append(O, t), List.append(&2, B.Note, N, ns), p2) == True{} : Bool}
  for +heof: {S.StP.eof(p2) == ef : Bool}
  for bud: {API.bi(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)) == True{} : Bool} & {Nat.is_le(Nat.add(API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), Nat.add(R, 1n)), n1) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.absorb(Norm.Step{st2, b, ns, Pr.Ask{rs2}}, cs2, de2, rd2, G, O, N))

def am_ask(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, rs2, t, p2, hfu, eout, est, wf, rep, hq, hrq, hmr, hask, gd, heof, bud):
  match f:
    case 0n:
      (bi2, drop) = bud
      ar_zero(R, API.need(fa, T, p2, cs2, de2, Pr.Ask{rs2}, String.append(O, t)), n1, drop, hfu)
    case 1n+h:
      (bi2, drop) = bud
      am_ask.k(h, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, rs2, t, p2, hfu, eout, est, wf, rep, hq, hrq, hmr, hask, gd, heof, bi2, drop)

# ... whose next is Finish
# ========================

law am_fin:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for -st2: Norm.St
  for -b: D.Bytes
  for +ns: List<&2, B.Note>
  for +c: Nat
  for +t: String
  for +hfu: {Nat.is_le(n1, f) == True{} : Bool}
  for +eout: {E.out(b) == Some{t} : Maybe<&2, String>}
  for +rep: {R.Report{String.append(O, t), List.append(&2, B.Note, N, ns), c} == T : R.Report}
  for +hfin: {Nat.is_le(Nat.add(R, 2n), n1) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.absorb(Norm.Step{st2, b, ns, Pr.Finish{c}}, cs2, de2, rd2, G, O, N))

def am_fin(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, c, t, hfu, eout, rep, hfin):
  match f:
    case 0n:
      ar_zero(R, 1n, n1, fin_drop(R, n1, hfin), hfu)
    case 1n+h:
      +drop = fin_drop(R, n1, hfin)
      %Equal.sym(Maybe<&2, String>, E.out(b), Some{t}, eout) : Good(fa, T, lim, h, MQ.absorb.k(st2, Pr.Finish{c}, cs2, de2, rd2, G, MQ.absorb.out(_, O), N, ns))
      (and_tt(G, hG), (rep, (%Equal.sym(Nat, rd2, Nat.add(rd, R), hrd) : {Nat.is_le(Nat.add(_, 1n), lim) == True{} : Bool}; ar_lim(rd, R, 1n, n1, lim, drop, hlim), ar_fuel(R, 1n, n1, h, drop, hfu))))

# Any step, from its guarantee and the budget
# ===========================================

law absorb_ok:
  for s: Norm.Step
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +cs2: List<&2, String>
  for +de2: Bool
  for +rd: Nat
  for +rd2: Nat
  for +R: Nat
  for +n1: Nat
  for +O: String
  for +N: List<&2, B.Note>
  for +ef: Bool
  for +G: Bool
  for +hG: {G == True{} : Bool}
  for +hrd: {rd2 == Nat.add(rd, R) : Nat}
  for +hde: {Bool.or(Bool.not(de2), ef) == True{} : Bool}
  for +htx: {txt(cs2) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, n1), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(n1, f) == True{} : Bool}
  for sg: DO.StepG2(fa, T, cs2, O, N, ef, s)
  for kb: Kont(fa, T, s, cs2, de2, R, n1, O, N)
  for kf: KFin(s, R, n1)
  StepR(fa, T, lim, f, MQ.absorb(s, cs2, de2, rd2, G, O, N))

def absorb_ok(s, f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, hfu, sg, kb, kf):
  match s:
    case Norm.Step{st2, b, ns, Pr.More{}}:
      (+t, g1) = sg
      (+p2, g2) = g1
      (+eout, g3) = g2
      (+est, g4) = g3
      (+wf, g5) = g4
      (+rep, g6) = g5
      (+gd, g7) = g6
      (hmo, hef) = g7
      am_more(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, t, p2, hfu, eout, est, hmo, rep, gd, hef, kb(p2, Pr.More{}, t, est, {==}, eout, wf, rep, gd))
    case Norm.Step{st2, b, ns, Pr.Ask{+rs2}}:
      (+t, g1) = sg
      (+p2, g2) = g1
      (+eout, g3) = g2
      (+est, g4) = g3
      (+wf, g5) = g4
      (+rep, g6) = g5
      (+hq, g7) = g6
      (+hrq, g8) = g7
      (+hmr, g9) = g8
      (+hask, g10) = g9
      (+gd, heof) = g10
      am_ask(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, rs2, t, p2, hfu, eout, est, wf, rep, hq, hrq, hmr, hask, gd, heof, kb(p2, Pr.Ask{rs2}, t, est, {==}, eout, wf, rep, gd))
    case Norm.Step{st2, b, ns, Pr.Finish{+c}}:
      (+t, g1) = sg
      (eout, rep) = g1
      am_fin(f, fa, T, lim, cs2, de2, rd, rd2, R, n1, O, N, ef, G, hG, hrd, hde, htx, hlim, st2, b, ns, c, t, hfu, eout, rep, kf(c, {==}))

# ---------------------------------------------------------------------------
# The driver's steps, by kind
# ---------------------------------------------------------------------------

law and_mk:
  for +a: Bool
  for +b: Bool
  for +ha: {a == True{} : Bool}
  for +hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_mk(a, b, ha, hb):
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# A piece of the file (More, pieces left).
law k_chunk:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: Norm.St
  for +c: String
  for +ct: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +p: S.StP
  for +est: {st == S.mkSt(fa, p) : Norm.St}
  for +hmo: {DD.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> ct, out, notes, p) == T : R.Report}
  for +hgd: {S.guard(out, notes, p) == True{} : Bool}
  for +hg: {g == True{} : Bool}
  for +hde0: {de == False{} : Bool}
  for +htx: {txt(c <> ct) == True{} : Bool}
  for +hbi: {API.bi(fa, T, p, c <> ct, de, Pr.More{}, out) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, API.need(fa, T, p, c <> ct, de, Pr.More{}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(API.need(fa, T, p, c <> ct, de, Pr.More{}, out), f) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.More{}, c <> ct, de, rd, g, out, notes, None{}}))

def k_chunk(f, fa, T, lim, hbfa, st, c, ct, de, rd, g, out, notes, p, est, hmo, hr, hgd, hg, hde0, htx, hbi, hlim, hfu):
  match de:
    case True{}:
      Empty.absurd(StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.More{}, c <> ct, True{}, rd, g, out, notes, None{}})), PB.true_ne_false(hde0))
    case False{}:
      +hA = PB.and_true_l(Bool.and(E.is_bytes(c), E.all_bytes(ct)), Bool.and(E.le31(String.length(c)), E.pieces_ok(ct)), htx)
      +hP = PB.and_true_r(Bool.and(E.is_bytes(c), E.all_bytes(ct)), Bool.and(E.le31(String.length(c)), E.pieces_ok(ct)), htx)
      +hcb = PB.and_true_l(E.is_bytes(c), E.all_bytes(ct), hA)
      +hcn = PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(ct), hP)
      +htx2 = and_mk(E.all_bytes(ct), E.pieces_ok(ct), PB.and_true_r(E.is_bytes(c), E.all_bytes(ct), hA), PB.and_true_r(E.le31(String.length(c)), E.pieces_ok(ct), hP))
      +n1 = API.need(fa, T, p, c <> ct, False{}, Pr.More{}, out)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p), est) : StepR(fa, T, lim, f, MQ.absorb(Norm.step(_, Pr.Chunk{E.enc(c)}), ct, False{}, rd, g, out, notes))
      absorb_ok(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), f, fa, T, lim, ct, False{}, rd, rd, 0n, n1, out, notes, False{}, g, hg,
        Equal.sym(Nat, Nat.add(rd, 0n), rd, N.add_zero(rd)), {==}, htx2, hlim, hfu,
        sg_chunk(fa, T, c, ct, out, notes, p, hbfa, hmo, hr, hcb, hcn, hgd),
        p2 => nx2 => t => hst => hnx => hout => hw2 => hr2 => hg2 => API.bud_chunk(fa, T, c, ct, out, notes, p, p2, nx2, t, hbfa, hmo, hr, hgd, hbi, hcb, hcn, hst, hnx, hout, hw2, hr2, hg2),
        code => hnx => API.bud_chunk_fin(fa, T, c, ct, out, notes, p, code, hbfa, hmo, hr, hgd, hbi, hcb, hcn, hnx))

# The end of the file (More, no piece left).
law k_eof:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: Norm.St
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +p: S.StP
  for +est: {st == S.mkSt(fa, p) : Norm.St}
  for +hmo: {DD.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, out, notes, p) == T : R.Report}
  for +hgd: {S.guard(out, notes, p) == True{} : Bool}
  for +hg: {g == True{} : Bool}
  for +hde0: {de == False{} : Bool}
  for +hbi: {API.bi(fa, T, p, Nil{}, de, Pr.More{}, out) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, API.need(fa, T, p, Nil{}, de, Pr.More{}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(API.need(fa, T, p, Nil{}, de, Pr.More{}, out), f) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.More{}, Nil{}, de, rd, g, out, notes, None{}}))

def k_eof(f, fa, T, lim, hbfa, st, de, rd, g, out, notes, p, est, hmo, hr, hgd, hg, hde0, hbi, hlim, hfu):
  match de:
    case True{}:
      Empty.absurd(StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.More{}, Nil{}, True{}, rd, g, out, notes, None{}})), PB.true_ne_false(hde0))
    case False{}:
      +n1 = API.need(fa, T, p, Nil{}, False{}, Pr.More{}, out)
      %Equal.sym(Norm.St, st, S.mkSt(fa, p), est) : StepR(fa, T, lim, f, MQ.absorb(Norm.step(_, Pr.Eof{}), Nil{}, True{}, rd, g, out, notes))
      absorb_ok(Norm.step(S.mkSt(fa, p), Pr.Eof{}), f, fa, T, lim, Nil{}, True{}, rd, rd, 0n, n1, out, notes, True{}, g, hg,
        Equal.sym(Nat, Nat.add(rd, 0n), rd, N.add_zero(rd)), {==}, {==}, hlim, hfu,
        sg_eof(fa, T, out, notes, p, hbfa, hmo, hr, hgd),
        p2 => nx2 => t => hst => hnx => hout => hw2 => hr2 => hg2 => API.bud_eof(fa, T, out, notes, p, p2, nx2, t, hbfa, hmo, hr, hgd, hbi, hst, hnx, hout, hw2, hr2, hg2),
        code => hnx => API.bud_eof_fin(fa, T, out, notes, p, code, hbfa, hmo, hr, hgd, hbi, hnx))

law and2:
  for +g: Bool
  for +q: Bool
  for +hg: {g == True{} : Bool}
  for +hq: {q == True{} : Bool}
  {Bool.and(g, q) == True{} : Bool}

def and2(g, q, hg, hq):
  and_mk(g, q, hg, hq)

# The answers to an Ask.
law k_ask:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: Norm.St
  for +rs: List<&2, Pr.Req>
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +p: S.StP
  for +est: {st == S.mkSt(fa, p) : Norm.St}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, dcs, out, notes, p) == T : R.Report}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hrq: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hask: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hgd: {S.guard(out, notes, p) == True{} : Bool}
  for +hg: {g == True{} : Bool}
  for +hlink: {Bool.or(Bool.not(de), S.StP.eof(p)) == True{} : Bool}
  for +htx: {txt(dcs) == True{} : Bool}
  for +hbi: {API.bi(fa, T, p, dcs, de, Pr.Ask{rs}, out) == True{} : Bool}
  for +hlim: {Nat.is_le(Nat.add(rd, API.need(fa, T, p, dcs, de, Pr.Ask{rs}, out)), lim) == True{} : Bool}
  for +hfu: {Nat.is_le(API.need(fa, T, p, dcs, de, Pr.Ask{rs}, out), f) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.Ask{rs}, dcs, de, rd, g, out, notes, None{}}))

def k_ask(f, fa, T, lim, hbfa, st, rs, dcs, de, rd, g, out, notes, p, est, hw, hr, hq, hrq, hmr, hask, hgd, hg, hlink, htx, hbi, hlim, hfu):
  +n1 = API.need(fa, T, p, dcs, de, Pr.Ask{rs}, out)
  %Equal.sym(Norm.St, st, S.mkSt(fa, p), est) :
    StepR(fa, T, lim, f, MQ.absorb(Norm.step(_, Pr.Ref{M.truths(fa, rs)}), dcs, de, Nat.add(rd, List.length(&2, Pr.Req, rs)), Bool.and(g, E.reqs_ok(rs)), out, notes))
  absorb_ok(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), f, fa, T, lim, dcs, de, rd, Nat.add(rd, List.length(&2, Pr.Req, rs)), List.length(&2, Pr.Req, rs), n1, out, notes,
    S.StP.eof(p), Bool.and(g, E.reqs_ok(rs)), and2(g, E.reqs_ok(rs), hg, hq), {==}, hlink, htx, hlim, hfu,
    sg_ref(fa, T, dcs, out, notes, p, rs, hbfa, hw, hr, hask, hq, hrq, hmr, hgd),
    p2 => nx2 => t => hst => hnx => hout => hw2 => hr2 => hg2 => API.bud_ref(fa, T, dcs, de, rs, out, notes, p, p2, nx2, t, hbfa, hw, hr, hask, hq, hrq, hmr, hgd, hbi, hst, hnx, hout, hw2, hr2, hg2),
    code => hnx => API.bud_ref_fin(fa, T, dcs, de, rs, out, notes, p, code, hbfa, hw, hr, hask, hq, hrq, hmr, hgd, hbi, hnx))

# The machine said Finish: the driver stops.
law k_fin:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for -st: Norm.St
  for +c: Nat
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +hg: {g == True{} : Bool}
  for +hrep: {R.Report{out, notes, c} == T : R.Report}
  for +hl: {Nat.is_le(Nat.add(rd, 1n), lim) == True{} : Bool}
  for +hf1: {Nat.is_le(1n, f) == True{} : Bool}
  StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, Pr.Finish{c}, dcs, de, rd, g, out, notes, None{}}))

def k_fin(f, fa, T, lim, st, c, dcs, de, rd, g, out, notes, hg, hrep, hl, hf1):
  match f:
    case 0n:
      PB.false_ne_true(hf1)
    case 1n+h:
      (hg, (hrep, le_pred(rd, lim, hl)))

# ---------------------------------------------------------------------------
# The drive
# ---------------------------------------------------------------------------

law step_good:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for -st: Norm.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for gd: Good(fa, T, lim, f, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, None{}})
  StepR(fa, T, lim, f, MQ.dstep(fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}))

def step_good(f, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd):
  match nx dcs:
    case Pr.Finish{+c} _:
      (hg, g1) = gd
      (hrep, g2) = g1
      (hl, hf1) = g2
      k_fin(f, fa, T, lim, st, c, dcs, de, rd, g, out, notes, hg, hrep, hl, hf1)
    case Pr.More{} Nil{}:
      (+p, g1) = gd
      (est, g2) = g1
      (hmo, g3) = g2
      (hr, g4) = g3
      (hgd, g5) = g4
      (hg, g6) = g5
      (hde0, g7) = g6
      (htx, g8) = g7
      (hbi, g9) = g8
      (hlim, hfu) = g9
      k_eof(f, fa, T, lim, hbfa, st, de, rd, g, out, notes, p, est, hmo, hr, hgd, hg, hde0, hbi, hlim, hfu)
    case Pr.More{} Con{+c, +ct}:
      (+p, g1) = gd
      (est, g2) = g1
      (hmo, g3) = g2
      (hr, g4) = g3
      (hgd, g5) = g4
      (hg, g6) = g5
      (hde0, g7) = g6
      (htx, g8) = g7
      (hbi, g9) = g8
      (hlim, hfu) = g9
      k_chunk(f, fa, T, lim, hbfa, st, c, ct, de, rd, g, out, notes, p, est, hmo, hr, hgd, hg, hde0, htx, hbi, hlim, hfu)
    case Pr.Ask{+rs} _:
      (+p, g1) = gd
      (est, g2) = g1
      (hw, g3) = g2
      (hr, g4) = g3
      (hq, g5) = g4
      (hrq, g6) = g5
      (hmr, g7) = g6
      (hask, g8) = g7
      (hgd, g9) = g8
      (hg, g10) = g9
      (hlink, g11) = g10
      (htx, g12) = g11
      (hbi, g13) = g12
      (hlim, hfu) = g13
      k_ask(f, fa, T, lim, hbfa, st, rs, dcs, de, rd, g, out, notes, p, est, hw, hr, hq, hrq, hmr, hask, hgd, hg, hlink, htx, hbi, hlim, hfu)

# A stopped driver stays as it is.
law drive_done:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for -st: Norm.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +c: Nat
  {MQ.drive(f, fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}) == MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}} : MQ.DSt}

def drive_done(f, fa, st, nx, dcs, de, rd, g, out, notes, c):
  match f nx:
    case 0n _:
      {==}
    case 1n+h Pr.More{}:
      drive_done(h, fa, st, Pr.More{}, dcs, de, rd, g, out, notes, c)
    case 1n+h Pr.Ask{+rs}:
      drive_done(h, fa, st, Pr.Ask{rs}, dcs, de, rd, g, out, notes, c)
    case 1n+h Pr.Finish{+cc}:
      drive_done(h, fa, st, Pr.Finish{cc}, dcs, de, rd, g, out, notes, c)

law done_res:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for -st: Norm.St
  for +nx: Pr.Next
  for +dcs: List<&2, String>
  for +de: Bool
  for +rd: Nat
  for +g: Bool
  for +out: String
  for +notes: List<&2, B.Note>
  for +c: Nat
  for gd: Good(fa, T, lim, f, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}})
  {MQ.result(MQ.drive(f, fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}), lim) == Some{T} : Maybe<&2, R.Report>}

def done_res(f, fa, T, lim, st, nx, dcs, de, rd, g, out, notes, c, gd):
  (hg, g1) = gd
  (hrep, hk) = g1
  %Equal.sym(MQ.DSt, MQ.drive(f, fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}), MQ.DSt{st, nx, dcs, de, rd, g, out, notes, Some{c}}, drive_done(f, fa, st, nx, dcs, de, rd, g, out, notes, c)) :
    {MQ.result(_, lim) == Some{T} : Maybe<&2, R.Report>}
  %Equal.sym(Bool, g, True{}, hg) : {MQ.result.if(Bool.and(_, Nat.is_le(rd, lim)), R.Report{out, notes, c}) == Some{T} : Maybe<&2, R.Report>}
  %Equal.sym(Bool, Nat.is_le(rd, lim), True{}, hk) : {MQ.result.if(Bool.and(True{}, _), R.Report{out, notes, c}) == Some{T} : Maybe<&2, R.Report>}
  Equal.cong(R.Report, Maybe<&2, R.Report>, z => Some{z}, R.Report{out, notes, c}, T, hrep)

# The drive ends with the report, given a good state and fuel for it.
law drive_ok:
  for +f: Nat
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +lim: Nat
  for +hbfa: {PC.fa_bytes(fa) == True{} : Bool}
  for d: MQ.DSt
  for gd: Good(fa, T, lim, f, d)
  {MQ.result(MQ.drive(f, fa, d), lim) == Some{T} : Maybe<&2, R.Report>}

def drive_ok(f, fa, T, lim, hbfa, d, gd):
  match f d:
    case _ MQ.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, Some{+c}}:
      done_res(f, fa, T, lim, st, nx, dcs, de, rd, g, out, notes, c, gd)
    case 0n MQ.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, None{}}:
      Empty.absurd({MQ.result(MQ.drive(0n, fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}), lim) == Some{T} : Maybe<&2, R.Report>},
        step_good(0n, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd))
    case 1n+h MQ.DSt{st, +nx, +dcs, +de, +rd, +g, +out, +notes, None{}}:
      drive_ok(h, fa, T, lim, hbfa, MQ.dstep(fa, MQ.DSt{st, nx, dcs, de, rd, g, out, notes, None{}}),
        step_good(1n+h, fa, T, lim, hbfa, st, nx, dcs, de, rd, g, out, notes, gd))

# ---------------------------------------------------------------------------
# The law machine
# ---------------------------------------------------------------------------

law machine_go3:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  for +est: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  for +hmo: {DD.more_ok(B.Fasta.parse(fasta), p) == True{} : Bool}
  for +hr: {S.report(B.Fasta.parse(fasta), cs, "", Nil{}, p) == L.run(fasta, vcf, o) : R.Report}
  for +hgd: {S.guard("", Nil{}, p) == True{} : Bool}
  for +hbi: {API.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}
  for +hn: {Nat.is_le(API.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}
  {MQ.launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_go3(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hb, est, hmo, hr, hgd, hbi, hn):
  +hfb = PB.and_true_r(E.all_bytes(argv), Bool.and(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs))), hb)
  +htx = PB.and_true_r(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs)), hfb)
  +hbfa = fa_bytes_parse(fasta, PB.and_true_l(E.is_bytes(fasta), Bool.and(E.all_bytes(cs), E.pieces_ok(cs)), hfb))
  +est0 = AB.subst(Maybe<&2, B.Cfg>, x => {DD.start_st(dfs, Norm.start.of(x)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha, est)
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {MQ.launch(Norm.start.of(_), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}
  %Equal.sym(Maybe<&2, R.Report>, MQ.result(MQ.drive(M.bound(argv, fasta, vcf, cs), B.Fasta.parse(fasta), MQ.DSt{DD.start_st(dfs, Norm.start.of(Some{B.Cfg{o, ref, vcfpath}})), Pr.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}}), M.bound(argv, fasta, vcf, cs)), Some{L.run(fasta, vcf, o)},
    drive_ok(M.bound(argv, fasta, vcf, cs), B.Fasta.parse(fasta), L.run(fasta, vcf, o), M.bound(argv, fasta, vcf, cs), hbfa, MQ.DSt{DD.start_st(dfs, Norm.start.of(Some{B.Cfg{o, ref, vcfpath}})), Pr.More{}, cs, False{}, 0n, True{}, "", Nil{}, None{}},
      (p, (est0, (hmo, (hr, (hgd, ({==}, ({==}, (htx, (hbi, (hn, hn)))))))))))) :
    {MQ.launch.of(_, ref, vcfpath) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}
  {==}

law machine_go2:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  for +est: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  for +hmo: {DD.more_ok(B.Fasta.parse(fasta), p) == True{} : Bool}
  for +hr: {S.report(B.Fasta.parse(fasta), cs, "", Nil{}, p) == L.run(fasta, vcf, o) : R.Report}
  for +hgd: {S.guard("", Nil{}, p) == True{} : Bool}
  for bud: {API.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}
    & {Nat.is_le(API.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}
  {MQ.launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_go2(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hb, est, hmo, hr, hgd, bud):
  (hbi, hn) = bud
  machine_go3(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hb, est, hmo, hr, hgd, hbi, hn)

law machine_go:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  for so: &p: S.StP -> ({DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
    & ({DD.start_paths(Norm.start(argv)) == Some{DD.Paths{ref, vcfpath}} : Maybe<&2, DD.Paths>}
    & ({DD.more_ok(B.Fasta.parse(fasta), p) == True{} : Bool}
    & ({S.report(B.Fasta.parse(fasta), cs, "", Nil{}, p) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), B.Fasta.parse(fasta), dfs, o, R.start_st())) : R.Report}
    & {S.guard("", Nil{}, p) == True{} : Bool}))))
  {MQ.launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_go(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb, so):
  ?TODO


# The law machine (MACHINE.bend), with every variable reusable.
law machine_h:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(argv, fasta, cs) == True{} : Bool}
  {MQ.launch(Norm.start(argv), argv, fasta, vcf, cs) == Some{M.Launch{ref, vcfpath, L.run(fasta, vcf, o)}} : Maybe<&2, M.Launch>}

def machine_h(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, ha, hf, h, hb):
  ?TODO

