import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PR
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_e_defs.bend as SD
import ./proof_b_enc.bend as EN
import ./proof_e_task_buf.bend as BUF
import ./proof_e_task_piece.bend as PI
import ./proof_e_task_loop.bend as LPP
import ./proof_e_task_one.bend as ON
import lawful-halves@0.1.0.0/proof_all.bend as HA
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-halves@0.1.0.0/defs.bend as HD
import lawful-halves@0.1.0.0/halves.bend as HH

# Phase E, area "task": a batch's plan and tasks (notes/parallel_proofs.md).
# A batch's pieces arrive as E.enc of their texts; the plan hands each back
# with its reads; the tasks, run with the truthful answers, give each piece's
# buffer and either nothing (dirty) or a good run that stands for the spec's
# run of the piece's lines from SD.rs0(c0, l).

# ---------------------------------------------------------------------------
# Pictures
# ---------------------------------------------------------------------------

# A planned piece: its text, its reads, whether it has reads (a complete line
# after its first LF k), k, the first line's CHROM c0 and the phantom key l.
type Pc is Data:
  Pc{c: String, rs: List<&2, Pr.Req>, ok: Bool, k: U32, c0: String, l: Nat}

def mkPl(+p: Pc) -> W.Pl:
  match p:
    case Pc{+c, rs, ok, k, c0, l}:
      W.Pl{E.enc(c), rs, ok, k, c0, l}

def mkPls(+ps: List<&2, Pc>) -> List<&1, W.Pl>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      mkPl(p) <> mkPls(t)

def Pc.c(p: Pc) -> String:
  match p:
    case Pc{c, rs, ok, k, c0, l}:
      c

def Pc.rs(p: Pc) -> List<&2, Pr.Req>:
  match p:
    case Pc{c, rs, ok, k, c0, l}:
      rs

# The pieces' texts, and all their reads in order.
def texts(+ps: List<&2, Pc>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      Pc.c(p) <> texts(t)

def reqs_of(+ps: List<&2, Pc>) -> List<&2, Pr.Req>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      List.append(&2, Pr.Req, Pc.rs(p), reqs_of(t))

def encs(+cs: List<&2, String>) -> List<&1, D.Bytes>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      E.enc(c) <> encs(t)

# Each read is at most 2^31 letters (so [r] is Norm.parts of it) and names a
# contig of bytes.
def rs_ok(+rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Pr.Req{+c, +a, +b} <> t:
      E.le31(Nat.sub(b, a)) && E.is_bytes(c) && rs_ok(t)

def two(+rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case a <> b <> Nil{}:
      True{}
    case _:
      False{}

# The text of a piece after byte k (the task's input).
def after(+c: String, +k: U32) -> String:
  NR.chars(List.drop(&2, U32, E.codes(c), U32.to_nat((k + 1 : U32))))

# What the plan guarantees of a piece followed by the text X: with reads,
# exactly two good ones, c0 is bytes and the CHROM of the first line after
# k, k + 1 is within the piece and k is its first LF; without, no reads. (No function inside, so a proof of
# it can be copied.)
def PcOK(+p: Pc, +X: String) -> Type:
  match p:
    case Pc{+c, +rs, True{}, +k, +c0, l}:
      {rs_ok(rs) && two(rs) == True{} : Bool}
        & ({E.is_bytes(c0) == True{} : Bool}
        & ({SD.first_chrom(B.Text.lines(String.append(after(c, k), X))) == Some{c0} : Maybe<&2, String>}
        & ({U32.is_lt((k + 1 : U32), U32.from_nat(String.length(c))) == True{} : Bool}
        & (&a: String -> ({c == String.append(a, String.append("\n", after(c, k))) : String} & {P.nolf(a) == True{} : Bool})))))
    case Pc{c, +rs, False{}, k, c0, l}:
      {rs == Nil{} : List<&2, Pr.Req>}

# Each piece followed by the later pieces' texts and dcs (as BatchOK).
def PcsOK(+ps: List<&2, Pc>, +dcs: List<&2, String>) -> Type:
  match ps:
    case Nil{}:
      Unit
    case +p <> t:
      PcOK(p, String.concat(List.append(&2, String, texts(t), dcs))) & PcsOK(t, dcs)

# A clean task's state: its run, the end of its last line, its window.
type TcP is Data:
  TcP{rp: P.RunP, pd: P.PdP, wp: PC.WP}

type TResP is Data:
  TDirtyP{}
  TCleanP{c: TcP}

# A task's result: the piece's buffer (len, t, depth d) and what it found.
type TOutP is Data:
  TOutP{len: U32, t: AT.Tree<U32>, d: Nat, r: TResP}

def mkTRes(+fa: List<&2, B.Contig>, +k: U32, +c0: String, +l: Nat, +r: TResP) -> W.TRes:
  match r:
    case TDirtyP{}:
      W.TDirty{}
    case TCleanP{TcP{+rp, +pd, +wp}}:
      W.TClean{W.Tc{P.mkRun(rp), P.mkPd(pd), PC.mkWin(fa, wp), k, c0, l}}

def mkTOut(+fa: List<&2, B.Contig>, +p: Pc, +x: TOutP) -> W.TOut:
  match p x:
    case Pc{c, rs, ok, +k, +c0, +l} TOutP{+len, +t, d, +r}:
      W.TOut{C.BT(len, t), mkTRes(fa, k, c0, l, r)}

def mkTOuts(+fa: List<&2, B.Contig>, +ps: List<&2, Pc>, +xs: List<&2, TOutP>) -> List<&1, W.TOut>:
  match ps xs:
    case +p <> pt +x <> xt:
      mkTOut(fa, p, x) <> mkTOuts(fa, pt, xt)
    case _ _:
      Nil{}

# What a clean task found, for the text cs that follows the piece: a good run
# in the body and line end, a truthful window, and the lines ls it handled
# (the piece's after k, up to the line end) moved into a run that stands for
# the spec's run of ls from the phantom state.
def TcOK(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, +k: U32, +c0: String, +l: Nat, +cs: List<&2, String>, +x: TcP) -> Type:
  match x:
    case TcP{+rp, +pd, +wp}:
      {PR.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool}
        & (&ls: List<&2, B.Line> -> ({B.Text.lines(String.append(after(c, k), String.concat(cs))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pd), String.concat(cs)))) : List<&2, B.Line>}
          & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}))

# (Only a piece with reads, ok, can have a clean result.)
def TResOK(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, ok: Bool, +k: U32, +c0: String, +l: Nat, +cs: List<&2, String>, +r: TResP) -> Type:
  match ok r:
    case _ TDirtyP{}:
      Unit
    case True{} TCleanP{+x}:
      TcOK(dfs, fa, o, c, k, c0, l, cs, x)
    case False{} TCleanP{x}:
      Empty

# A task's result for piece p, followed by the text cs: the buffer holds the
# piece's bytes; the result is as above.
def TOutOK(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +p: Pc, +cs: List<&2, String>, +x: TOutP) -> Type:
  match p x:
    case Pc{+c, rs, +ok, +k, +c0, +l} TOutP{+len, +t, +d, +r}:
      {D.ok(C.BT(len, t), d) == True{} : Bool} & ({D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>} & TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r))

# Every piece's result, each followed by the later pieces' texts and dcs.
def BatchOK(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, Pc>, +xs: List<&2, TOutP>, +dcs: List<&2, String>) -> Type:
  match ps xs:
    case Nil{} Nil{}:
      Unit
    case +p <> pt +x <> xt:
      TOutOK(dfs, fa, o, p, List.append(&2, String, texts(pt), dcs), x) & BatchOK(dfs, fa, o, pt, xt, dcs)
    case _ _:
      Empty

# ---------------------------------------------------------------------------
# Assembly (helpers that name this file's pictures; the rest is in
# proof_e_task_*.bend)
# ---------------------------------------------------------------------------

def rs_ok_eq(+rs: List<&2, Pr.Req>) -> {rs_ok(rs) == BUF.rs_ok2(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Pr.Req{+c, +a, +b} <> t:
      %Equal.sym(Bool, rs_ok(t), BUF.rs_ok2(t), rs_ok_eq(t)) :
        {Bool.and(Bool.and(E.le31(Nat.sub(b, a)), E.is_bytes(c)), _) == Bool.and(Bool.and(E.le31(Nat.sub(b, a)), E.is_bytes(c)), BUF.rs_ok2(t)) : Bool}
      {==}

def two_eq(+rs: List<&2, Pr.Req>) -> {two(rs) == BUF.two2(rs) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case a <> Nil{}:
      {==}
    case a <> b <> Nil{}:
      {==}
    case a <> b <> c <> t:
      {==}

def L0(+c: String) -> U32:
  U32.from_nat(String.length(c))

def pcok(+c: String, +rs: List<&2, Pr.Req>, +ok: Bool, +k: U32, +c0: String, +l: Nat, +X: String,
  h: PI.POK(c, L0(c), rs, ok, k, c0)) -> PcOK(Pc{c, rs, ok, k, c0, l}, X):
  match ok:
    case True{}:
      (h1, r00) = h
      (hc0, r0) = r00
      (hx, r) = r0
      +e = Equal.trans(Bool, Bool.and(rs_ok(rs), two(rs)), Bool.and(BUF.rs_ok2(rs), two(rs)), Bool.and(BUF.rs_ok2(rs), BUF.two2(rs)),
        Equal.cong(Bool, Bool, z => Bool.and(z, two(rs)), rs_ok(rs), BUF.rs_ok2(rs), rs_ok_eq(rs)),
        Equal.cong(Bool, Bool, z => Bool.and(BUF.rs_ok2(rs), z), two(rs), BUF.two2(rs), two_eq(rs)))
      (Equal.trans(Bool, Bool.and(rs_ok(rs), two(rs)), Bool.and(BUF.rs_ok2(rs), BUF.two2(rs)), True{}, e, h1), (hc0, (hx(X), r)))
    case False{}:
      h

# The plan of pieces c <> t, from c's piece lemma and t's plan.
def plan_cons.k(+c: String, +t: List<&2, String>, +dcs: List<&2, String>,
  +hb: {E.is_bytes(c) == True{} : Bool},
  pg: PI.PieceG(L0(c), EN.enc_t(c), c, W.plan.piece(C.BT(L0(c), EN.enc_t(c)))),
  ih: &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs))))) ->
  &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(c <> t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == c <> t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs)))):
  (+rs, g1) = pg
  (+ok, g2) = g1
  (+k, g3) = g2
  (+c0, g4) = g3
  (+l, g5) = g4
  (epl, g6) = g5
  (hrs, hpok) = g6
  (+pt, i1) = ih
  (eih, i2) = i1
  (etx, i3) = i2
  (hrq, hpcs) = i3
  +e = {
    %Equal.sym(D.Bytes, E.enc(c), C.BT(L0(c), EN.enc_t(c)), EN.enc_bt(c)) :
      {W.plan.reqs_all(W.plan.piece(_) <> W.plan.all(encs(t))) == (W.Pl{_, rs, ok, k, c0, l} <> mkPls(pt), List.append(&2, Pr.Req, rs, reqs_of(pt))) : List<&1, W.Pl> & List<&2, Pr.Req>}
    %Equal.sym(W.Pl, W.plan.piece(C.BT(L0(c), EN.enc_t(c))), W.Pl{C.BT(L0(c), EN.enc_t(c)), rs, ok, k, c0, l}, epl) :
      {W.plan.reqs_all(_ <> W.plan.all(encs(t))) == (W.Pl{C.BT(L0(c), EN.enc_t(c)), rs, ok, k, c0, l} <> mkPls(pt), List.append(&2, Pr.Req, rs, reqs_of(pt))) : List<&1, W.Pl> & List<&2, Pr.Req>}
    %Equal.sym(List<&1, W.Pl> & List<&2, Pr.Req>, W.plan.reqs_all(W.plan.all(encs(t))), (mkPls(pt), reqs_of(pt)), eih) :
      {W.plan.reqs_cons(W.Pl{C.BT(L0(c), EN.enc_t(c)), rs, ok, k, c0, l}, rs, _) == (W.Pl{C.BT(L0(c), EN.enc_t(c)), rs, ok, k, c0, l} <> mkPls(pt), List.append(&2, Pr.Req, rs, reqs_of(pt))) : List<&1, W.Pl> & List<&2, Pr.Req>}
    {==} : {W.plan.reqs_all(W.plan.all(encs(c <> t))) == (mkPls(Pc{c, rs, ok, k, c0, l} <> pt), reqs_of(Pc{c, rs, ok, k, c0, l} <> pt)) : List<&1, W.Pl> & List<&2, Pr.Req>}}
  (Pc{c, rs, ok, k, c0, l} <> pt,
    (e,
    (Equal.cong(List<&2, String>, List<&2, String>, z => c <> z, texts(pt), t, etx),
    (BUF.rs2_app(rs, reqs_of(pt), hrs, hrq),
    (pcok(c, rs, ok, k, c0, l, String.concat(List.append(&2, String, texts(pt), dcs)), hpok), hpcs)))))

def plan_cons(+c: String, +t: List<&2, String>, +dcs: List<&2, String>,
  +hb: {E.is_bytes(c) == True{} : Bool},
  hen: {D.ok(C.BT(L0(c), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
    & ({D.view(C.BT(L0(c), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
    & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
    & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat})),
  ih: &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs))))) ->
  &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(c <> t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == c <> t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs)))):
  (hok, hen2) = hen
  (hv, hen3) = hen2
  plan_cons.k(c, t, dcs, hb, PI.piece_t(L0(c), EN.enc_t(c), E.depth(String.length(c)), c, hok, hv), ih)

# plan_all's step (rec: plan_all on the later pieces).
def plan_step(+c: String, +t: List<&2, String>, +dcs: List<&2, String>,
  +hb: {E.all_bytes(c <> t) == True{} : Bool},
  +hn: {E.pieces_ok(c <> t) == True{} : Bool},
  rec: {E.all_bytes(t) == True{} : Bool} -> {E.pieces_ok(t) == True{} : Bool} ->
    &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs))))) ->
  &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(c <> t))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == c <> t : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs)))):
  +hb1 = BUF.andl(E.is_bytes(c), E.all_bytes(t), hb)
  +hn1 = BUF.andl(E.le31(String.length(c)), E.pieces_ok(t), hn)
  plan_cons(c, t, dcs, hb1, EN.enc_ok(c, hb1, hn1),
    rec(BUF.andr(E.is_bytes(c), E.all_bytes(t), hb), BUF.andr(E.le31(String.length(c)), E.pieces_ok(t), hn)))

# ---------------------------------------------------------------------------
# Assembly: the batch
# ---------------------------------------------------------------------------

def conv(+r: LPP.LR) -> TResP:
  match r:
    case LPP.LDirty{}:
      TDirtyP{}
    case LPP.LClean{+rp, +pd, +wp}:
      TCleanP{TcP{rp, pd, wp}}

def mk_conv(+fa: List<&2, B.Contig>, +k: U32, +c0: String, +l: Nat, +r: LPP.LR) -> {mkTRes(fa, k, c0, l, conv(r)) == LPP.mkLR(fa, k, c0, l, r) : W.TRes}:
  match r:
    case LPP.LDirty{}:
      {==}
    case LPP.LClean{+rp, +pd, +wp}:
      {==}

def tres_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, +ok: Bool, +k: U32, +c0: String, +l: Nat, +cs: List<&2, String>, +r: LPP.LR,
  h: ON.ROK(dfs, fa, o, cs, c0, l, ON.LA(c, k, cs), r, ok)) -> TResOK(dfs, fa, o, c, ok, k, c0, l, cs, conv(r)):
  match ok:
    case True{}:
      match r:
        case LPP.LDirty{}:
          Unit{}
        case LPP.LClean{+rp, +pd, +wp}:
          h
    case False{}:
      match r:
        case LPP.LDirty{}:
          Unit{}
        case LPP.LClean{+rp, +pd, +wp}:
          h

def and_in(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def BG(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, Pc>, +dcs: List<&2, String>, -ts: List<&1, W.TOut>) -> Type:
  &xs: List<&2, TOutP> -> ({ts == mkTOuts(fa, ps, xs) : List<&1, W.TOut>} & BatchOK(dfs, fa, o, ps, xs, dcs))

# A piece's task in front of the later pieces' tasks.
def fcons.k(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, +rs: List<&2, Pr.Req>, +ok: Bool, +k: U32, +c0: String, +l: Nat,
  +pt: List<&2, Pc>, +dcs: List<&2, String>, -tsk: W.TOut, -rest: List<&1, W.TOut>,
  g: ON.OneG(dfs, fa, o, List.append(&2, String, texts(pt), dcs), c, ok, k, c0, l, tsk),
  ih: BG(dfs, fa, o, pt, dcs, rest)) ->
  BG(dfs, fa, o, Pc{c, rs, ok, k, c0, l} <> pt, dcs, tsk <> rest):
  (+len, g1) = g
  (+t, g2) = g1
  (+d, g3) = g2
  (+r, g4) = g3
  (+eq, g5) = g4
  (+hok, g6) = g5
  (+hv, hr) = g6
  (+xt, i1) = ih
  (+ei, hbt) = i1
  +e = {
    %Equal.sym(List<&1, W.TOut>, rest, mkTOuts(fa, pt, xt), ei) :
      {tsk <> _ == mkTOut(fa, Pc{c, rs, ok, k, c0, l}, TOutP{len, t, d, conv(r)}) <> mkTOuts(fa, pt, xt) : List<&1, W.TOut>}
    %Equal.sym(W.TOut, tsk, W.TOut{C.BT(len, t), LPP.mkLR(fa, k, c0, l, r)}, eq) :
      {_ <> mkTOuts(fa, pt, xt) == mkTOut(fa, Pc{c, rs, ok, k, c0, l}, TOutP{len, t, d, conv(r)}) <> mkTOuts(fa, pt, xt) : List<&1, W.TOut>}
    %mk_conv(fa, k, c0, l, r) :
      {W.TOut{C.BT(len, t), _} <> mkTOuts(fa, pt, xt) == mkTOut(fa, Pc{c, rs, ok, k, c0, l}, TOutP{len, t, d, conv(r)}) <> mkTOuts(fa, pt, xt) : List<&1, W.TOut>}
    {==} : {tsk <> rest == mkTOuts(fa, Pc{c, rs, ok, k, c0, l} <> pt, TOutP{len, t, d, conv(r)} <> xt) : List<&1, W.TOut>}}
  (TOutP{len, t, d, conv(r)} <> xt, (e, ((hok, (hv, tres_ok(dfs, fa, o, c, ok, k, c0, l, List.append(&2, String, texts(pt), dcs), r, hr))), hbt)))

def TS(+dfs: B.Defs, +o: B.Opts, +fa: List<&2, B.Contig>, +ps: List<&2, Pc>) -> List<&1, HD.Task<&1, W.TOut>>:
  W.tasks(o, mkPls(ps), W.pairs(M.truths(fa, reqs_of(ps))), dfs)

# A piece with reads: exactly two (PcOK), run with their truthful answers.
def force_true(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat, +pt: List<&2, Pc>, +dcs: List<&2, String>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {E.le31(String.length(c)) == True{} : Bool},
  hpc: PcOK(Pc{c, rs, True{}, k, c0, l}, String.concat(List.append(&2, String, texts(pt), dcs))),
  ih: BG(dfs, fa, o, pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, pt)))) ->
  BG(dfs, fa, o, Pc{c, rs, True{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, rs, True{}, k, c0, l} <> pt))):
  match rs:
    case Nil{}:
      (h1, q1) = hpc
      Empty.absurd(BG(dfs, fa, o, Pc{c, Nil{}, True{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, Nil{}, True{}, k, c0, l} <> pt))), N.false_ne_true(h1))
    case +a <> Nil{}:
      (h1, q1) = hpc
      Empty.absurd(BG(dfs, fa, o, Pc{c, [a], True{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, [a], True{}, k, c0, l} <> pt))),
        N.false_ne_true(BUF.andr(rs_ok([a]), two([a]), h1)))
    case +a <> +b <> +cc <> +t:
      (h1, q1) = hpc
      Empty.absurd(BG(dfs, fa, o, Pc{c, a <> b <> cc <> t, True{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, a <> b <> cc <> t, True{}, k, c0, l} <> pt))),
        N.false_ne_true(BUF.andr(rs_ok(a <> b <> cc <> t), two(a <> b <> cc <> t), h1)))
    case Pr.Req{+c1, +x1, +y1} <> Pr.Req{+c2, +x2, +y2} <> Nil{}:
      (h1, q1) = hpc
      (+hb0, q2) = q1
      (hfc, q3) = q2
      (+hk1, hdec) = q3
      +RS = {[Pr.Req{c1, x1, y1}, Pr.Req{c2, x2, y2}] : List<&2, Pr.Req>}
      +hrs2 = Equal.trans(Bool, BUF.rs_ok2(RS), rs_ok(RS), True{}, Equal.sym(Bool, rs_ok(RS), BUF.rs_ok2(RS), rs_ok_eq(RS)), BUF.andl(rs_ok(RS), two(RS), h1))
      fcons.k(dfs, fa, o, c, RS, True{}, k, c0, l, pt, dcs,
        W.task(o, E.enc(c), True{}, RS, M.truths.one(fa, Pr.Req{c1, x1, y1}), M.truths.one(fa, Pr.Req{c2, x2, y2}), k, c0, l, dfs), HD.force(&1, W.TOut, TS(dfs, o, fa, pt)),
        ON.one_ok(dfs, fa, o, List.append(&2, String, texts(pt), dcs), c, k, c0, l, c1, x1, y1, c2, x2, y2, hb, hab, hcb, hcn, hrs2, hb0, hk1),
        ih)

# A piece without reads.
def force_false(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +c: String, +rs: List<&2, Pr.Req>, +k: U32, +c0: String, +l: Nat, +pt: List<&2, Pc>, +dcs: List<&2, String>,
  +hcb: {E.is_bytes(c) == True{} : Bool},
  +hcn: {E.le31(String.length(c)) == True{} : Bool},
  +hpc: {rs == Nil{} : List<&2, Pr.Req>},
  ih: BG(dfs, fa, o, pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, pt)))) ->
  BG(dfs, fa, o, Pc{c, rs, False{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, rs, False{}, k, c0, l} <> pt))):
  match rs:
    case Nil{}:
      fcons.k(dfs, fa, o, c, Nil{}, False{}, k, c0, l, pt, dcs,
        W.task(o, E.enc(c), False{}, Nil{}, Pr.Unknown{}, Pr.Unknown{}, k, c0, l, dfs), HD.force(&1, W.TOut, TS(dfs, o, fa, pt)),
        ON.one_no(dfs, fa, o, List.append(&2, String, texts(pt), dcs), c, Nil{}, k, c0, l, hcb, hcn),
        ih)
    case +a <> +t:
      Empty.absurd(BG(dfs, fa, o, Pc{c, a <> t, False{}, k, c0, l} <> pt, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, Pc{c, a <> t, False{}, k, c0, l} <> pt))),
        N.false_ne_true(Equal.cong(List<&2, Pr.Req>, Bool, z => List.is_empty(&2, Pr.Req, z), a <> t, Nil{}, hpc)))

def force_ok(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, Pc>, +dcs: List<&2, String>,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +hc: {Bool.and(E.all_bytes(texts(ps)), E.pieces_ok(texts(ps))) == True{} : Bool},
  hps: PcsOK(ps, dcs)) ->
  BG(dfs, fa, o, ps, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, ps))):
  match ps:
    case Nil{}:
      (Nil{}, ({==}, Unit{}))
    case Pc{+c, +rs, +ok, +k, +c0, +l} <> +pt:
      match ok:
        case True{}:
          (hpc, hpt) = hps
          +hA = BUF.andl(E.all_bytes(c <> texts(pt)), E.pieces_ok(c <> texts(pt)), hc)
          +hP = BUF.andr(E.all_bytes(c <> texts(pt)), E.pieces_ok(c <> texts(pt)), hc)
          +hct = and_in(E.all_bytes(texts(pt)), E.pieces_ok(texts(pt)), BUF.andr(E.is_bytes(c), E.all_bytes(texts(pt)), hA), BUF.andr(E.le31(String.length(c)), E.pieces_ok(texts(pt)), hP))
          force_true(dfs, fa, o, c, rs, k, c0, l, pt, dcs, hb, hab, BUF.andl(E.is_bytes(c), E.all_bytes(texts(pt)), hA), BUF.andl(E.le31(String.length(c)), E.pieces_ok(texts(pt)), hP),
            hpc, force_ok(dfs, fa, o, pt, dcs, hb, hab, hct, hpt))
        case False{}:
          (hpc, hpt) = hps
          +hA = BUF.andl(E.all_bytes(c <> texts(pt)), E.pieces_ok(c <> texts(pt)), hc)
          +hP = BUF.andr(E.all_bytes(c <> texts(pt)), E.pieces_ok(c <> texts(pt)), hc)
          +hct = and_in(E.all_bytes(texts(pt)), E.pieces_ok(texts(pt)), BUF.andr(E.is_bytes(c), E.all_bytes(texts(pt)), hA), BUF.andr(E.le31(String.length(c)), E.pieces_ok(texts(pt)), hP))
          force_false(dfs, fa, o, c, rs, k, c0, l, pt, dcs, BUF.andl(E.is_bytes(c), E.all_bytes(texts(pt)), hA), BUF.andl(E.le31(String.length(c)), E.pieces_ok(texts(pt)), hP),
            hpc, force_ok(dfs, fa, o, pt, dcs, hb, hab, hct, hpt))

def batch_k(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, Pc>, +dcs: List<&2, String>,
  fr: BG(dfs, fa, o, ps, dcs, HD.force(&1, W.TOut, TS(dfs, o, fa, ps)))) ->
  &xs: List<&2, TOutP> -> ({HH.all(&1, W.TOut, W.tasks(o, mkPls(ps), W.pairs(M.truths(fa, reqs_of(ps))), dfs)) == mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
    & BatchOK(dfs, fa, o, ps, xs, dcs)):
  (+xs, f1) = fr
  (+e, h) = f1
  (xs, (Equal.trans(List<&1, W.TOut>, HH.all(&1, W.TOut, TS(dfs, o, fa, ps)), HD.force(&1, W.TOut, TS(dfs, o, fa, ps)), mkTOuts(fa, ps, xs), HA.all_force(&1, W.TOut, TS(dfs, o, fa, ps)), e), h))

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# The plan of a batch: each piece handed back with its reads.
def plan_all(+cs: List<&2, String>, +dcs: List<&2, String>,
  hb: {E.all_bytes(cs) == True{} : Bool},
  hn: {E.pieces_ok(cs) == True{} : Bool}) ->
  &ps: List<&2, Pc> -> ({W.plan.reqs_all(W.plan.all(encs(cs))) == (mkPls(ps), reqs_of(ps)) : List<&1, W.Pl> & List<&2, Pr.Req>}
    & ({texts(ps) == cs : List<&2, String>} & ({E.reqs_ok(reqs_of(ps)) == True{} : Bool} & PcsOK(ps, dcs)))):
  match cs:
    case Nil{}:
      (Nil{}, ({==}, ({==}, ({==}, Unit{}))))
    case +c <> t:
      plan_step(c, t, dcs, hb, hn, h1 => h2 => plan_all(t, dcs, h1, h2))

# The batch's tasks, run in parallel with the truthful answers to its reads.
def batch(+dfs: B.Defs, +fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, Pc>, +dcs: List<&2, String>,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hab: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  hcs: {E.all_bytes(texts(ps)) && E.pieces_ok(texts(ps)) == True{} : Bool},
  hps: PcsOK(ps, dcs)) ->
  &xs: List<&2, TOutP> -> ({HH.all(&1, W.TOut, W.tasks(o, mkPls(ps), W.pairs(M.truths(fa, reqs_of(ps))), dfs)) == mkTOuts(fa, ps, xs) : List<&1, W.TOut>}
    & BatchOK(dfs, fa, o, ps, xs, dcs)):
  batch_k(dfs, fa, o, ps, dcs, force_ok(dfs, fa, o, ps, dcs, hb, hab, hcs, hps))
