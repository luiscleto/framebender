import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_frame_fr.bend as FF
import ./proof_e_defs.bend as SD
import ./proof_b_enc.bend as EN
import ./proof_e_task_buf.bend as BUF
import ./proof_e_task_loop.bend as LP
import ./proof_e_task_start.bend as ST
import ./proof_e_task_win.bend as WN
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_grow.bend as G
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-bytes@0.1.0.0/proof_find.bend as FD
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_sz.bend as SZ
import ./proof_b_lit.bend as PL
import ./proof_e_task_piece.bend as PI
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area D (task): one task (norm_par.bend's task) on a piece with
# reads: the loop from the start picture, which hands the piece back (phase
# F: there is no copy).

# The lines of the piece after k followed by the text cs.
def LA(+c: String, +k: U32, +cs: List<&2, String>) -> List<&2, B.Line>:
  B.Text.lines(String.append(NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat((k + 1 : U32)))), String.concat(cs)))

def PD0() -> P.PdP:
  P.PBP{0, G.tnew(0n, 0), 0n}

# The start picture: the run, the piece from k + 1, an empty line end, the
# first window.
def P0(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +tr: AT.Tree<U32>, +d: Nat, +k: U32, +wp: PC.WP) -> S.StP:
  S.StP{o, S.MBP{rp}, [P.SBP{len, tr, d, (k + 1 : U32)}], P.PBP{0, G.tnew(0n, 0), 0n}, False{}, 0n, wp, None{}, False{}, dfs}

def app_nil(+s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.append(t, ""), t, app_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

def inv0(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +rp: P.RunP, +len: U32, +tr: AT.Tree<U32>, +d: Nat, +wp: PC.WP,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), len) == True{} : Bool},
  +hinv: {RD.RunInv(rp) == True{} : Bool},
  +hib: {R.RunSt.inbody(P.specRun(rp)) == True{} : Bool},
  +hset: {P.settle(P.specRun(rp)) == P.settle(SD.rs0(c0, l)) : R.RunSt},
  +hw: {Bool.and(PC.wp_ok(fa, wp), S.mb_win.k(wp)) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool}) ->
  LP.Inv(dfs, fa, o, cs, c0, l, LA(c, k, cs), S.report(fa, cs, "", Nil{}, P0(dfs, o, rp, len, tr, d, k, wp)), P0(dfs, o, rp, len, tr, d, k, wp)):
  +SRC = {[P.SBP{len, tr, d, (k + 1 : U32)}] : List<&2, P.SrcP>}
  +hwp = BUF.andl(PC.wp_ok(fa, wp), S.mb_win.k(wp), hw)
  +hmb = BUF.andr(PC.wp_ok(fa, wp), S.mb_win.k(wp), hw)
  +hwf = {
    %Equal.sym(Bool, RD.RunInv(rp), True{}, hinv) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(_, Bool.and(D.ok(C.BT(len, tr), d), U32.is_le((k + 1 : U32), len))), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), PC.wp_ok(fa, wp)), S.mb_win.k(wp)), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    %Equal.sym(Bool, D.ok(C.BT(len, tr), d), True{}, hok) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, Bool.and(_, U32.is_le((k + 1 : U32), len))), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), PC.wp_ok(fa, wp)), S.mb_win.k(wp)), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    %Equal.sym(Bool, U32.is_le((k + 1 : U32), len), True{}, hk1) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, Bool.and(True{}, _)), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), PC.wp_ok(fa, wp)), S.mb_win.k(wp)), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    %Equal.sym(Bool, PC.wp_ok(fa, wp), True{}, hwp) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, Bool.and(True{}, True{})), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), _), S.mb_win.k(wp)), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    %Equal.sym(Bool, S.mb_win.k(wp), True{}, hmb) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, Bool.and(True{}, True{})), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), True{}), _), Bool.and(Bool.and(E.all_bytes(S.opts_args(o)), S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    %Equal.sym(Bool, E.all_bytes(S.opts_args(o)), True{}, hab) :
      {Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(Bool.and(True{}, Bool.and(True{}, True{})), P.pd_ok(PD0())), P.nolf(P.pdtext(PD0()))),
        Bool.or(S.src_empty(SRC), String.is_empty(P.pdtext(PD0())))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(PD0())), S.ends_lf(P.srcstext(SRC))))), True{}), True{}), Bool.and(Bool.and(_, S.recs_first(Nil{})), S.recs_run(S.MBP{rp}, Nil{}))) == True{} : Bool}
    {==} : {S.WF(fa, P0(dfs, o, rp, len, tr, d, k, wp)) == True{} : Bool}}
  +hgd = {
    %Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), True{}, hib) : {Bool.or(_, Bool.and(String.is_empty(""), List.is_empty(&2, B.Note, Nil{}))) == True{} : Bool}
    {==} : {S.guard("", Nil{}, P0(dfs, o, rp, len, tr, d, k, wp)) == True{} : Bool}}
  +V = D.view(C.BT(len, tr))
  +A = NR.chars(List.drop(&2, U32, V, U32.to_nat((k + 1 : U32))))
  +eLA = {
    %hv : {B.Text.lines(String.append(NR.chars(List.drop(&2, U32, _, U32.to_nat((k + 1 : U32)))), String.concat(cs))) == B.Text.lines(S.intext(P0(dfs, o, rp, len, tr, d, k, wp), cs)) : List<&2, B.Line>}
    %app_nil(A) : {B.Text.lines(String.append(_, String.concat(cs))) == B.Text.lines(S.intext(P0(dfs, o, rp, len, tr, d, k, wp), cs)) : List<&2, B.Line>}
    {==} : {LA(c, k, cs) == List.append(&2, B.Line, Nil{}, B.Text.lines(S.intext(P0(dfs, o, rp, len, tr, d, k, wp), cs))) : List<&2, B.Line>}}
  +LS0 = B.Text.lines(S.intext(P0(dfs, o, rp, len, tr, d, k, wp), cs))
  +dd = Equal.trans(B.Defs, L.defs.go(LS0, R.RunSt.inbody(P.specRun(rp)), dfs), L.defs.go(LS0, True{}, dfs), dfs,
    Equal.cong(Bool, B.Defs, z => L.defs.go(LS0, z, dfs), R.RunSt.inbody(P.specRun(rp)), True{}, hib), FF.defs_done(LS0, dfs))
  (hwf, ({==}, (hgd, ({==}, ({==}, (Nil{}, (eLA, (dd, hset))))))))



# ---------------------------------------------------------------------------
# One task
# ---------------------------------------------------------------------------

# A task's result, given that the piece had reads (ok) or not (as
# proof_e_task.bend's TResOK).
def ROK(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c0: String, +l: Nat, +LA0: List<&2, B.Line>, +r: LP.LR, +ok: Bool) -> Type:
  match r ok:
    case LP.LDirty{} _:
      Unit
    case LP.LClean{+rp, +pd, +wp} True{}:
      LP.LRok(dfs, fa, o, cs, c0, l, LA0, LP.LClean{rp, pd, wp})
    case LP.LClean{rp, pd, wp} False{}:
      Empty
    case LP.LAgain{l2, wp, sp} _:
      Empty

# A task's result: its piece's buffer, and a result that is dirty or clean
# from the phantom l (the plan's, or the key of the task's second run).
def OneG(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +ok: Bool, +k: U32, +c0: String, -tout: W.TOut) -> Type:
  &len: U32 -> &t: AT.Tree<U32> -> &d: Nat -> &l: Nat -> &r: LP.LR ->
    ({tout == W.TOut{C.BT(len, t), LP.mkLR(fa, k, c0, l, r)} : W.TOut}
    & ({D.ok(C.BT(len, t), d) == True{} : Bool}
    & ({D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}
    & ROK(dfs, fa, o, cs, c0, l, LA(c, k, cs), r, ok))))

def L0(+c: String) -> U32:
  U32.from_nat(String.length(c))

def ENC(+c: String) -> Type:
  {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
    & ({D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
    & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
    & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))

# The piece itself, dirty.
def dirty_enc(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +ok: Bool, +k: U32, +c0: String, +l: Nat,
  en: ENC(c)) ->
  OneG(dfs, fa, o, cs, c, ok, k, c0, W.TOut{E.enc(c), W.TDirty{}}):
  (hok, e1) = en
  (hv, e2) = e1
  (L0(c), (EN.enc_t(c), (E.depth(String.length(c)), (l, (LP.LDirty{},
    (Equal.cong(D.Bytes, W.TOut, z => W.TOut{z, W.TDirty{}}, E.enc(c), C.BT(L0(c), EN.enc_t(c)), EN.enc_bt(c)), (hok, (hv, Unit{}))))))))

# One run of the task's loop from the phantom l, with the windows wp1 and
# sps (task.run1): the loop from the start picture (no copy: the loop hands
# the piece back).
def run1_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat, +rs: U32,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +wp1: PC.WP, +sps: List<&2, PC.WP>, +EL: U32,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), len) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  r0: ST.R0G(c0, l, rs),
  +hw: {LP.wins_ok(fa, wp1 <> sps) == True{} : Bool}) ->
  LP.LoopG(dfs, fa, o, cs, c0, l, LA(c, k, cs), k, len, tr, W.task.run1(o, C.BT(len, tr), len, k, PC.mkWin(fa, wp1), LP.mkWins(fa, sps), EL, c0, l, rs, dfs)):
  (+rp0, q1) = r0
  (+er0, q2) = q1
  (+hinv, q3) = q2
  (+hset, hib) = q3
  +F = Nat.add(U32.to_nat(len), 8n)
  +X1 = Bool.and(PC.wp_ok(fa, wp1), S.mb_win.k(wp1))
  +hw1 = BUF.andl(X1, LP.wins_ok(fa, sps), hw)
  +hsp = BUF.andr(X1, LP.wins_ok(fa, sps), hw)
  %Equal.sym(NR.Run, W.task.run0(c0, l, rs), P.mkRun(rp0), er0) :
    LP.LoopG(dfs, fa, o, cs, c0, l, LA(c, k, cs), k, len, tr, W.task.loop(F, W.task.next(Q.St{o, Q.MB{_}, [Q.SB{C.BT(len, tr), (k + 1 : U32)}], Q.PB{BY.empty(0n)}, False{}, 0n, PC.mkWin(fa, wp1), None{}, False{}, dfs}, W.PIn{}, LP.mkWins(fa, sps), EL, len), EL, len, k, c0, l))
  %Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, G.tnew(0n, 0)), G.empty_eq(0n)) :
    LP.LoopG(dfs, fa, o, cs, c0, l, LA(c, k, cs), k, len, tr, W.task.loop(F, W.task.next(Q.St{o, Q.MB{P.mkRun(rp0)}, [Q.SB{C.BT(len, tr), (k + 1 : U32)}], Q.PB{_}, False{}, 0n, PC.mkWin(fa, wp1), None{}, False{}, dfs}, W.PIn{}, LP.mkWins(fa, sps), EL, len), EL, len, k, c0, l))
  LP.start_ok(dfs, F, fa, o, cs, c0, l, LA(c, k, cs), k, S.report(fa, cs, "", Nil{}, P0(dfs, o, rp0, len, tr, d, k, wp1)), len, tr, d, EL, hok, hL, P0(dfs, o, rp0, len, tr, d, k, wp1), sps, (k + 1 : U32), hfa,
    inv0(dfs, fa, o, cs, c, k, c0, l, rp0, len, tr, d, wp1, hok, hv, hk1, hinv, hib, hset, hw1, hab), {==}, hsp)

# The second run's result: a second stop against the phantom is dirty.
def final_r(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l2: Nat,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +r: LP.LR,
  h: LP.LRok(dfs, fa, o, cs, c0, l2, LA(c, k, cs), r)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.final(W.TOut{C.BT(len, tr), LP.mkLR(fa, k, c0, l2, r)})):
  match r:
    case LP.LDirty{}:
      (len, (tr, (d, (l2, (LP.LDirty{}, ({==}, (hok, (hv, Unit{}))))))))
    case LP.LClean{+rp, +pd, +wp}:
      (len, (tr, (d, (l2, (LP.LClean{rp, pd, wp}, ({==}, (hok, (hv, h))))))))
    case LP.LAgain{+l3, +wp, +sp}:
      (len, (tr, (d, (l2, (LP.LDirty{}, ({==}, (hok, (hv, Unit{}))))))))

def final_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l2: Nat,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat,
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  -tout: W.TOut,
  lg: LP.LoopG(dfs, fa, o, cs, c0, l2, LA(c, k, cs), k, len, tr, tout)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.final(tout)):
  (+r, g1) = lg
  (e, h) = g1
  %Equal.sym(W.TOut, tout, W.TOut{C.BT(len, tr), LP.mkLR(fa, k, c0, l2, r)}, e) : OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.final(_))
  final_r(dfs, fa, o, cs, c, k, c0, l2, len, tr, d, hok, hv, r, h)

# The first run's result: clean or dirty as it is; stopped against the
# phantom, the task runs again from the key it stopped at.
def retry_r(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +EL: U32,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hq: {Q.len_le(c0, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), len) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  +r: LP.LR,
  h: LP.LRok(dfs, fa, o, cs, c0, l, LA(c, k, cs), r)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.retry(o, len, k, EL, c0, dfs, W.TOut{C.BT(len, tr), LP.mkLR(fa, k, c0, l, r)})):
  match r:
    case LP.LDirty{}:
      (len, (tr, (d, (l, (LP.LDirty{}, ({==}, (hok, (hv, Unit{}))))))))
    case LP.LClean{+rp, +pd, +wp}:
      (len, (tr, (d, (l, (LP.LClean{rp, pd, wp}, ({==}, (hok, (hv, h))))))))
    case LP.LAgain{+l2, +wp, +sp}:
      final_ok(dfs, fa, o, cs, c, k, c0, l2, len, tr, d, hok, hv, W.task.run1(o, C.BT(len, tr), len, k, PC.mkWin(fa, wp), LP.mkWins(fa, sp), EL, c0, l2, W.task.res(o, len), dfs),
        run1_ok(dfs, fa, o, cs, c, k, c0, l2, W.task.res(o, len), len, tr, d, wp, sp, EL, hfa, hab, hok, hv, hk1, hL, ST.run0_ok(c0, l2, W.task.res(o, len), hb0, hq), h))

def retry_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +len: U32, +tr: AT.Tree<U32>, +d: Nat, +EL: U32,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hq: {Q.len_le(c0, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), len) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  -tout: W.TOut,
  lg: LP.LoopG(dfs, fa, o, cs, c0, l, LA(c, k, cs), k, len, tr, tout)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.retry(o, len, k, EL, c0, dfs, tout)):
  (+r, g1) = lg
  (e, h) = g1
  %Equal.sym(W.TOut, tout, W.TOut{C.BT(len, tr), LP.mkLR(fa, k, c0, l, r)}, e) : OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.retry(o, len, k, EL, c0, dfs, _))
  retry_r(dfs, fa, o, cs, c, k, c0, l, len, tr, d, EL, hfa, hab, hb0, hq, hok, hv, hk1, hL, r, h)

def WOK(+fa: List<&2, B.Contig>, +R1: Pr.Req) -> Type:
  {W.task.win(R1, M.truths.one(fa, R1)) == PC.mkWin(fa, WN.WPR(fa, R1)) : Q.Win}
  & {Bool.and(PC.wp_ok(fa, WN.WPR(fa, R1)), S.mb_win.k(WN.WPR(fa, R1))) == True{} : Bool}

def wins1(+fa: List<&2, B.Contig>, +wp: PC.WP, +h: {Bool.and(PC.wp_ok(fa, wp), S.mb_win.k(wp)) == True{} : Bool}) ->
  {LP.wins_ok(fa, [wp]) == True{} : Bool}:
  %Equal.sym(Bool, Bool.and(PC.wp_ok(fa, wp), S.mb_win.k(wp)), True{}, h) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def wins2(+fa: List<&2, B.Contig>, +w1: PC.WP, +w2: PC.WP,
  +h1: {Bool.and(PC.wp_ok(fa, w1), S.mb_win.k(w1)) == True{} : Bool},
  +h2: {Bool.and(PC.wp_ok(fa, w2), S.mb_win.k(w2)) == True{} : Bool}) ->
  {LP.wins_ok(fa, [w1, w2]) == True{} : Bool}:
  %Equal.sym(Bool, Bool.and(PC.wp_ok(fa, w1), S.mb_win.k(w1)), True{}, h1) : {Bool.and(_, LP.wins_ok(fa, [w2])) == True{} : Bool}
  wins1(fa, w2, h2)

# The task runs on the piece from the start picture, with the piece's last
# LF as rlf finds it, and again if its first run stopped against the phantom.
def oneC(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +R1: Pr.Req, +R2: Pr.Req, +len: U32, +tr: AT.Tree<U32>, +d: Nat,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hq: {Q.len_le(c0, 268435456) == True{} : Bool},
  +hok: {D.ok(C.BT(len, tr), d) == True{} : Bool},
  +hv: {D.view(C.BT(len, tr)) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), len) == True{} : Bool},
  +hL: {U32.is_lt(len, 1073741824) == True{} : Bool},
  w1: WOK(fa, R1),
  w2: WOK(fa, R2)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.last(o, len, W.task.wins2([R1, R2], M.truths.one(fa, R1), M.truths.one(fa, R2)), k, c0, l, W.rlf(C.BT(len, tr), len, (k + 1 : U32)), dfs)):
  (+we1, hw1) = w1
  (+we2, hw2) = w2
  +WP1 = WN.WPR(fa, R1)
  +WP2 = WN.WPR(fa, R2)
  +EL = Pair.fst(U32, Bool, BUF.RL(len, tr, len, (k + 1 : U32)))
  +FL = Pair.snd(U32, Bool, BUF.RL(len, tr, len, (k + 1 : U32)))
  %Equal.sym(D.Bytes & (U32 & Bool), W.rlf(C.BT(len, tr), len, (k + 1 : U32)), (C.BT(len, tr), (EL, FL)), BUF.rlf_b(len, tr, len, (k + 1 : U32))) :
    OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.last(o, len, W.task.wins2([R1, R2], M.truths.one(fa, R1), M.truths.one(fa, R2)), k, c0, l, _, dfs))
  %Equal.sym(Q.Win, W.task.win(R1, M.truths.one(fa, R1)), PC.mkWin(fa, WP1), we1) :
    OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.start(o, C.BT(len, tr), len, k, W.task.wins([_, W.task.win(R2, M.truths.one(fa, R2))]), EL, c0, l, dfs))
  %Equal.sym(Q.Win, W.task.win(R2, M.truths.one(fa, R2)), PC.mkWin(fa, WP2), we2) :
    OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.start(o, C.BT(len, tr), len, k, W.task.wins([PC.mkWin(fa, WP1), _]), EL, c0, l, dfs))
  retry_ok(dfs, fa, o, cs, c, k, c0, l, len, tr, d, EL, hfa, hab, hb0, hq, hok, hv, hk1, hL,
    W.task.run1(o, C.BT(len, tr), len, k, PC.mkWin(fa, WP1), LP.mkWins(fa, [WP2]), EL, c0, l, W.task.res(o, len), dfs),
    run1_ok(dfs, fa, o, cs, c, k, c0, l, W.task.res(o, len), len, tr, d, WP1, [WP2], EL, hfa, hab, hok, hv, hk1, hL, ST.run0_ok(c0, l, W.task.res(o, len), hb0, hq), wins2(fa, WP1, WP2, hw1, hw2)))

def oneB(+dfs: B.Defs, +q2: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +R1: Pr.Req, +R2: Pr.Req,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hq: {Q.len_le(c0, 268435456) == True{} : Bool},
  +hq2: {U32.is_lt(L0(c), 1073741824) == q2 : Bool},
  +hok: {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool},
  +hv: {D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>},
  +hk1: {U32.is_le((k + 1 : U32), L0(c)) == True{} : Bool},
  w1: WOK(fa, R1),
  w2: WOK(fa, R2)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.len.if(q2, o, C.BT(L0(c), EN.enc_t(c)), L0(c), W.task.wins2([R1, R2], M.truths.one(fa, R1), M.truths.one(fa, R2)), k, c0, l, dfs)):
  match q2:
    case False{}:
      (L0(c), (EN.enc_t(c), (E.depth(String.length(c)), (l, (LP.LDirty{}, ({==}, (hok, (hv, Unit{}))))))))
    case True{}:
      oneC(dfs, fa, o, cs, c, k, c0, l, R1, R2, L0(c), EN.enc_t(c), E.depth(String.length(c)), hfa, hab, hb0, hq, hok, hv, hk1, hq2, w1, w2)

def oneQ(+dfs: B.Defs, +q: Bool, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +R1: Pr.Req, +R2: Pr.Req,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hq: {Q.len_le(c0, 268435456) == q : Bool},
  +hk1: {U32.is_le((k + 1 : U32), L0(c)) == True{} : Bool},
  en: ENC(c),
  w1: WOK(fa, R1),
  w2: WOK(fa, R2)) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.go(q, o, E.enc(c), [R1, R2], M.truths.one(fa, R1), M.truths.one(fa, R2), k, c0, l, dfs)):
  match q:
    case False{}:
      dirty_enc(dfs, fa, o, cs, c, True{}, k, c0, l, en)
    case True{}:
      (+hok, e1) = en
      (+hv, e2) = e1
      %Equal.sym(D.Bytes, E.enc(c), C.BT(L0(c), EN.enc_t(c)), EN.enc_bt(c)) :
        OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task.len(o, BY.len(_), W.task.wins2([R1, R2], M.truths.one(fa, R1), M.truths.one(fa, R2)), k, c0, l, dfs))
      oneB(dfs, U32.is_lt(L0(c), 1073741824), fa, o, cs, c, k, c0, l, R1, R2, hfa, hab, hb0, hq, {==}, hok, hv, hk1, w1, w2)

# A task on a piece with two reads, run with their truthful answers.
def one_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +k: U32, +c0: String, +l: Nat,
  +c1: String, +x1: Nat, +y1: Nat, +c2: String, +x2: Nat, +y2: Nat,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {E.le31(String.length(c)) == True{} : Bool},
  +hrs: {BUF.rs_ok2([Pr.Req{c1, x1, y1}, Pr.Req{c2, x2, y2}]) == True{} : Bool},
  +hb0: {E.is_bytes(c0) == True{} : Bool},
  +hk1: {U32.is_lt((k + 1 : U32), L0(c)) == True{} : Bool}) ->
  OneG(dfs, fa, o, cs, c, True{}, k, c0, W.task(o, E.enc(c), True{}, [Pr.Req{c1, x1, y1}, Pr.Req{c2, x2, y2}], M.truths.one(fa, Pr.Req{c1, x1, y1}), M.truths.one(fa, Pr.Req{c2, x2, y2}), k, c0, l, dfs)):
  +A = Bool.and(E.le31(Nat.sub(y1, x1)), E.is_bytes(c1))
  +Bq = Bool.and(Bool.and(E.le31(Nat.sub(y2, x2)), E.is_bytes(c2)), True{})
  +ha = BUF.andl(A, Bq, hrs)
  +hb = BUF.andl(Bool.and(E.le31(Nat.sub(y2, x2)), E.is_bytes(c2)), True{}, BUF.andr(A, Bq, hrs))
  oneQ(dfs, Q.len_le(c0, 268435456), fa, o, cs, c, k, c0, l, Pr.Req{c1, x1, y1}, Pr.Req{c2, x2, y2}, hfa, hab, hb0, {==},
    PI.ult_le((k + 1 : U32), L0(c), hk1), EN.enc_ok(c, hcb, hcn),
    WN.win1(fa, c1, x1, y1, hfa, BUF.andl(E.le31(Nat.sub(y1, x1)), E.is_bytes(c1), ha), BUF.andr(E.le31(Nat.sub(y1, x1)), E.is_bytes(c1), ha)),
    WN.win1(fa, c2, x2, y2, hfa, BUF.andl(E.le31(Nat.sub(y2, x2)), E.is_bytes(c2), hb), BUF.andr(E.le31(Nat.sub(y2, x2)), E.is_bytes(c2), hb)))

# A task on a piece without reads is the piece, dirty.
def one_no(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +cs: List<&2, String>, +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat,
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {E.le31(String.length(c)) == True{} : Bool}) ->
  OneG(dfs, fa, o, cs, c, False{}, k, c0, W.task(o, E.enc(c), False{}, rs, Pr.Unknown{}, Pr.Unknown{}, k, c0, l, dfs)):
  dirty_enc(dfs, fa, o, cs, c, False{}, k, c0, l, EN.enc_ok(c, hcb, hcn))
