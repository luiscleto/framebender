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
import ./proof_b_drive_out.bend as DO
import ./proof_e_qif_step.bend as QS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT

# Phase E, area "qif": what the parallel machine needs of norm.bend's machine
# (Q) beyond phase B's statements (notes/parallel_proofs.md, "Area F"):
# a piece given as any good buffer (a task's copy), W.feed_line (Q.feed
# without md.reserve, for the line across a boundary), and Q.set_win with
# truthful answers (for the boundary line's reads).

def StP.pd(p: S.StP) -> P.PdP:
  match p:
    case S.StP{o, md, src, pd, eof, back, wp, asked, fneed, +dfs}:
      pd

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# step_chunk (as DO.StepG2) for a piece given as the good buffer C.BT(len, t)
# of depth d holding c's bytes.
def step_chunk_pic(+fa: List<&2, B.Contig>, +T: R.Report, +c: String, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hm: {DR.more_ok(fa, p) == True{} : Bool},
  hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hg: {S.guard(O, N, p) == True{} : Bool},
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  DO.StepG2(fa, T, cs, O, N, False{}, Norm.step(S.mkSt(fa, p), Pr.Chunk{C.BT(len, t)})):
  QS.step_chunk_pic_h(fa, T, c, cs, O, N, p, len, t, d, hb, hm, hr, hg, hok, hv)

# W.feed_line: a good state waiting for more, given the piece c as a good
# buffer, is a good state p1 with the same run, nothing asked, not at the
# end of the file, and the text still to come with c moved in front of cs.
def feed_line_ok(+fa: List<&2, B.Contig>, +c: String, +p: S.StP, +len: U32, +t: AT.Tree<U32>, +d: Nat,
  hm: {DR.more_ok(fa, p) == True{} : Bool},
  hcb: {E.is_bytes(c) == True{} : Bool},
  hcn: {P.le31(String.length(c)) == True{} : Bool},
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hv: {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}) ->
  &p1: S.StP -> ({W.feed_line(S.mkSt(fa, p), C.BT(len, t)) == S.mkSt(fa, p1) : Norm.St}
    & ({S.WF(fa, p1) == True{} : Bool} & ({S.StP.md(p1) == S.StP.md(p) : S.MdP} & ({S.StP.o(p1) == S.StP.o(p) : B.Opts}
    & ({S.StP.asked(p1) == None{} : Maybe<&2, List<&2, Pr.Req>>} & ({S.StP.eof(p1) == False{} : Bool}
    & ({S.StP.dfs(p1) == S.StP.dfs(p) : B.Defs} & ({S.recs(S.StP.src(p1)) == S.recs(S.StP.src(p)) : List<&2, P.SrcP>}
    & (@cs: List<&2, String> -> {S.intext(p1, cs) == S.intext(p, c <> cs) : String}))))))))):
  QS.feed_line_h(fa, c, p, len, t, d, hm, hok, hv)

# Q.set_win with the truthful answers to what a good state asked: a good
# state with the same run, input and options, nothing asked.
def set_win_ok(+fa: List<&2, B.Contig>, +p: S.StP, +rs: List<&2, Pr.Req>,
  hb: {PC.fa_bytes(fa) == True{} : Bool},
  hw: {S.WF(fa, p) == True{} : Bool},
  ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>},
  hq: {E.reqs_ok(rs) == True{} : Bool},
  hp: {rs == S.rq(rs) : List<&2, Pr.Req>},
  hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}) ->
  &p2: S.StP -> ({Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)) == S.mkSt(fa, p2) : Norm.St}
    & ({S.WF(fa, p2) == True{} : Bool} & ({S.StP.md(p2) == S.StP.md(p) : S.MdP} & ({S.StP.o(p2) == S.StP.o(p) : B.Opts}
    & ({S.StP.src(p2) == S.StP.src(p) : List<&2, P.SrcP>} & ({StP.pd(p2) == StP.pd(p) : P.PdP} & ({S.StP.eof(p2) == S.StP.eof(p) : Bool}
    & {S.StP.asked(p2) == None{} : Maybe<&2, List<&2, Pr.Req>>}))))))):
  match p rs:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs} Nil{}:
      (S.StP{o, md, src, pd, eof, back, wp, None{}, fneed, dfs}, (QS.sw_nil(dfs, fa, o, md, src, pd, eof, back, wp, asked, fneed, ha),
        (hw, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed, +dfs} Con{Pr.Req{+c, +a, +b}, +t}:
      +hb2 = hb
      (S.StP{o, md, src, pd, eof, back, PC.wpOf(fa, c, a, Norm.last_b(t, b)), None{}, fneed, dfs}, (QS.sw_eq(dfs, fa, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb2, ha, hp),
        (QS.sw_wf(dfs, fa, o, md, src, pd, eof, back, wp, asked, fneed, c, a, b, t, hb2, hw, hmr), ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))
