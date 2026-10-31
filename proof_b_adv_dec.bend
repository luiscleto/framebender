import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_b_lines_str.bend as LSS
import ./proof_b_cut_str.bend as CS
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_tostr.bend as TS
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_wr.bend as WR
import ./proof_b_adv_part.bend as DPT
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_adv_nat.bend as LP
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-bytes@0.1.0.0/proof_list.bend as BL
import lawful-bytes@0.1.0.0/proof_ops.bend as O
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import ./proof_base.bend as PB
import ./proof_b_defs_line.bend as DL

# The byte mode's decoded path (norm.bend's decoded): a source with no
# complete line (to pend), a line of more than 2^28 bytes (to the String
# mode), a header line (held, or the #CHROM line), a body line on the slow
# path. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def CX(+hold: Bool, +dfs: B.Defs, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool) -> Norm.Cx:
  Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, hold}

def PPs(+hold: Bool, +dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  LI.PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)

# Computations on a pictured run and buffer
# =========================================

law inb_eq:
  for +rp: P.RunP
  {Norm.Run.inbody(P.mkRun(rp)) == (P.mkRun(rp), P.RunP.i(rp)) : NR.Run & Bool}

def inb_eq(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law inbody_spec:
  for +rp: P.RunP
  {R.RunSt.inbody(P.specRun(rp)) == P.RunP.i(rp) : Bool}

def inbody_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law halt_spec:
  for +rp: P.RunP
  {R.RunSt.halt(P.specRun(rp)) == P.RunP.x(rp) : Bool}

def halt_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law tick_inbody:
  for +st: R.RunSt
  {R.RunSt.inbody(R.tick(st)) == R.RunSt.inbody(st) : Bool}

def tick_inbody(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law head_false_i:
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {R.RunSt.inbody(R.head_line(False{}, st, o, l)) == R.RunSt.inbody(st) : Bool}

def head_false_i(st, o, l):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +la, +b, +k, +so, +ns, +x}:
      {==}

law tick_halt:
  for +st: R.RunSt
  {R.RunSt.halt(R.tick(st)) == R.RunSt.halt(st) : Bool}

def tick_halt(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

# Bytes s .. s+k-1 as text (norm.bend's text): the buffer is handed back.
law text_eq:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +s: U32
  for +k: U32
  for +h: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {Nat.is_le(Nat.add(n(s), n(k)), n(len)) == True{} : Bool}
  {Norm.text(C.BT(len, t), s, k) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}

def text_eq(len, t, d, s, k, h, hs):
  +SN = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(len, t), s, k))
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(len, t), s, k), (C.BT(len, t), SN), SM.to_list_pair_t(len, t, s, k)) :
    {Norm.text.k(_) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  %Equal.sym(List<&2, U32>, SN, D.slice(D.view(C.BT(len, t)), n(s), n(k)), SM.to_list_view_t(len, t, d, s, k, h, hs)) :
    {(C.BT(len, t), Norm.chars(_)) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  %Equal.sym(String, Norm.chars(D.slice(D.view(C.BT(len, t)), n(s), n(k))), NR.chars(D.slice(D.view(C.BT(len, t)), n(s), n(k))), LSS.chars_norm(D.slice(D.view(C.BT(len, t)), n(s), n(k)))) :
    {(C.BT(len, t), _) == (C.BT(len, t), P.btext(len, t, s, k)) : D.Bytes & String}
  {==}

# A header line held
# ==================

# The spec's step on a header line that is not the #CHROM line: a tick, then
# head_line holds it.
law hold_step:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == False{} : Bool}
  for +eisc: {R.is_chrom_line(B.Line.body(Norm.line(A))) == False{} : Bool}
  {L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)) == R.head_line(False{}, R.tick(P.specRun(rp)), o, Norm.line(A)) : R.RunSt}

def hold_step(dfs,fa, o, rp, A, hx, hin, eisc):
  +st = P.specRun(rp)
  +RHS = R.head_line(False{}, R.tick(st), o, Norm.line(A))
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, dfs, o, st, B.Text.line(A)) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), False{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), False{}, inbody_spec(rp), hin)) :
    {L.line_in(_, fa, dfs, o, R.tick(st), B.Text.line(A)) == RHS : R.RunSt}
  %LN.line_eq(A) : {R.head_line(R.is_chrom_line(B.Line.body(_)), R.tick(st), o, _) == RHS : R.RunSt}
  %Equal.sym(Bool, R.is_chrom_line(B.Line.body(Norm.line(A))), False{}, eisc) : {R.head_line(_, R.tick(st), o, Norm.line(A)) == RHS : R.RunSt}
  {==}

# The run after a tick keeps i and x.
law tick_i:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.i(rp1) == P.RunP.i(rp) : Bool}

def tick_i(rp, rp1, s1):
  %inbody_spec(rp1) : {_ == P.RunP.i(rp) : Bool}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.RunSt.inbody(_) == P.RunP.i(rp) : Bool}
  %Equal.sym(Bool, R.RunSt.inbody(R.tick(P.specRun(rp))), R.RunSt.inbody(P.specRun(rp)), tick_inbody(P.specRun(rp))) : {_ == P.RunP.i(rp) : Bool}
  inbody_spec(rp)

law tick_x:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.x(rp1) == P.RunP.x(rp) : Bool}

def tick_x(rp, rp1, s1):
  %halt_spec(rp1) : {_ == P.RunP.x(rp) : Bool}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.RunSt.halt(_) == P.RunP.x(rp) : Bool}
  %Equal.sym(Bool, R.RunSt.halt(R.tick(P.specRun(rp))), R.RunSt.halt(P.specRun(rp)), tick_halt(P.specRun(rp))) : {_ == P.RunP.x(rp) : Bool}
  halt_spec(rp)

law line_bytes:
  for +A: String
  for +hb: {E.is_bytes(A) == True{} : Bool}
  {E.is_bytes(B.Line.text(Norm.line(A))) == True{} : Bool}

def line_bytes(A, hb):
  %Equal.sym(String, B.Line.text(Norm.line(A)), A ++ "\n", CS.ltext_nl(A)) : {E.is_bytes(_) == True{} : Bool}
  LSS.bytes_app(A, "\n", hb, {==})

def HOLDG(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, rn: NR.Run) -> Type:
  S.AdvG(fa, T, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.done.b(o, (NR.head_line(False{}, rn, o, Norm.line(P.btext(len, t, at, (j - at : U32)))), C.BT(len, t)), (j + 1 : U32),
      Norm.Cx.line(CX(hold, dfs, rest, pd, eof), B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), PC.mkWin(fa, wp)))

# The run a state pictures (RTP) is in the body when the run is.
def rtp_ib(hold: Bool, rp: P.RunP) -> {R.RunSt.inbody(P.specRun(LI.RTP(hold, rp))) == R.RunSt.inbody(P.specRun(rp)) : Bool}:
  match hold:
    case False{}:
      {==}
    case True{}:
      match rp:
        case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
          {==}

def dec.hold.h(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +rp1: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == False{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +eisc: {R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == False{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  hh: &p2: P.RunP -> ({NR.head_line(False{}, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))) == P.mkRun(p2) : NR.Run}
    & ({PR.RunInv(p2) == True{} : Bool}
    & {P.specRun(p2) == R.head_line(False{}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt})),
  +hnr: LI.HNE(hold, len, at)) ->
  HOLDG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, P.mkRun(rp1)):
  match hh:
    case (+rp2, q):
      match q:
        case (e2, q2):
          match q2:
            case (i2c, sp2c):
              +i2 = Equal.trans(Bool, PR.RunInv(rp2), True{}, True{}, i2c, {==})
              +sp2 = Equal.trans(R.RunSt, P.specRun(rp2), R.head_line(False{}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), R.head_line(False{}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), sp2c, {==})
              +A = P.btext(len, t, at, (j - at : U32))
              +l = Norm.line(A)
              +dfs2 = Norm.defs.line(dfs, B.Line.body(l))
              +hrs = Equal.trans(R.RunSt, P.specRun(rp2), R.head_line(False{}, R.tick(P.specRun(rp)), o, l), L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)),
                %s1 : {P.specRun(rp2) == R.head_line(False{}, _, o, l) : R.RunSt}; sp2,
                Equal.sym(R.RunSt, L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), R.head_line(False{}, R.tick(P.specRun(rp)), o, l), hold_step(dfs, fa, o, rp, A, hx, hin, eisc)))
              +hd = {(%Equal.sym(Bool, R.RunSt.inbody(P.specRun(rp)), False{}, Equal.trans(Bool, R.RunSt.inbody(P.specRun(rp)), P.RunP.i(rp), False{}, inbody_spec(rp), hin)) :
                  {dfs2 == Bool.pick(B.Defs, _, dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(A)))) : B.Defs};
                %LN.line_eq(A) : {dfs2 == B.Defs.line(dfs, B.Line.body(_)) : B.Defs}; DL.line_eq(dfs, B.Line.body(l))) :
                {dfs2 == Bool.pick(B.Defs, R.RunSt.inbody(P.specRun(rp)), dfs, B.Defs.line(dfs, B.Line.body(B.Text.line(A)))) : B.Defs}}
              %Equal.sym(NR.Run, NR.head_line(False{}, P.mkRun(rp1), o, l), P.mkRun(rp2), e2) :
                S.AdvG(fa, T, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
                  Norm.done.b(o, (_, C.BT(len, t)), (j + 1 : U32), Norm.Cx.line(CX(hold, dfs, rest, pd, eof), B.Line.body(l)), PC.mkWin(fa, wp)))
              HX.went_h(hold, dfs, dfs2, fa, T, cs, O, N, o, rp, rp2, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hs, hle, hn, hal, hlt, hinc, i2,
                Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), P.specRun(rp2), L.line_step(fa, dfs, o, P.specRun(rp), B.Text.line(A)), hrs),
                %Equal.sym(R.RunSt, P.specRun(rp2), R.head_line(False{}, P.specRun(rp1), o, l), sp2) : {Bool.or(R.RunSt.inbody(_), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(R.head_line(False{}, P.specRun(rp1), o, l)), R.RunSt.inbody(P.specRun(rp1)), head_false_i(P.specRun(rp1), o, l)) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
                %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {Bool.or(R.RunSt.inbody(_), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
                %Equal.sym(Bool, R.RunSt.inbody(R.tick(P.specRun(rp))), R.RunSt.inbody(P.specRun(rp)), tick_inbody(P.specRun(rp))) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
                %rtp_ib(hold, rp) : {Bool.or(_, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool};
                hg, hx, hd)


def TICKW(+rp: P.RunP) -> Type:
  &p2: P.RunP -> ({NR.tick(P.mkRun(rp)) == P.mkRun(p2) : NR.Run}
  & ({PR.RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == R.tick(P.specRun(rp)) : R.RunSt}
  & ({P.RunP.n(p2) == 1n+P.RunP.n(rp) : Nat}
  & ({P.RunP.obl(p2) == P.RunP.obl(rp) : U32}
  & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))))

# A header line held: a tick, then head_line holds it (done.b).
def dec.hold(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == False{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +eisc: {R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == False{} : Bool},
  tk: TICKW(rp),
  +hnr: LI.HNE(hold, len, at)) ->
  HOLDG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, NR.tick(P.mkRun(rp))):
  match tk:
    case (+rp1, q):
      match q:
        case (e1, q2):
          match q2:
            case (i1c, q3):
              match q3:
                case (s1c, q4):
                  +i1 = Equal.trans(Bool, PR.RunInv(rp1), True{}, True{}, i1c, {==})
                  +s1 = Equal.trans(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), R.tick(P.specRun(rp)), s1c, {==})
                  +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
                  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), False{}, tick_i(rp, rp1, s1), hin)
                  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, tick_x(rp, rp1, s1), hx)
                  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), e1) :
                    HOLDG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, _)
                  dec.hold.h(hold, dfs, fa, T, cs, O, N, o, rp, rp1, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hx, hin, hs, hn, hle, hal, hlt, hinc, eisc, s1,
                    PR.run_head_hold(rp1, o, l, i1, hin1, hx1, line_bytes(P.btext(len, t, at, (j - at : U32)), hby)), hnr)

# The line's LF
# =============

def XS(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

law j_range:
  for +len: U32
  for +t: AT.Tree<U32>
  for +d: Nat
  for +at: U32
  for +j: U32
  for +hok: {D.ok(C.BT(len, t), d) == True{} : Bool}
  for +hs: {U32.is_le(at, len) == True{} : Bool}
  for +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat}
  {Bool.and(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len))) == True{} : Bool}

def j_range(len, t, d, at, j, hok, hs, hjf):
  %Equal.sym(Nat, n(j), D.first(XS(len, t), n(at), n(len), 10), hjf) : {Bool.and(Nat.is_le(n(at), _), Nat.is_le(_, n(len))) == True{} : Bool}
  BL.first_range(XS(len, t), n(at), n(len), 10, LI.u2n(at, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(n(len), _) == True{} : Bool}; N.le_refl(n(len)))

law j_lt:
  for +len: U32
  for +j: U32
  for +hle: {Nat.is_le(n(j), n(len)) == True{} : Bool}
  for +hne: {U32.is_eq(j, len) == False{} : Bool}
  {Nat.is_lt(n(j), n(len)) == True{} : Bool}

def j_lt(len, j, hle, hne):
  %N.le_succ_lt(n(j), n(len)) : {_ == True{} : Bool}
  PB.le_ne(n(j), n(len), hle, %U.is_eq_to_nat(j, len) : {_ == False{} : Bool}; hne)

# The decoded line (j: its LF; A: its text before the LF)
# =======================================================

def DG(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, a: Norm.Adv) -> Type:
  S.AdvG(fa, T, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), a)

# The #CHROM line (proof_b_adv_wr.bend).
def dec.write(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == False{} : Bool},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +eisc: {R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == True{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.head(True{}, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  WR.write(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, hsm, eisc, hnr)

# A body line on the slow path (proof_b_adv_slow.bend).
def dec.slow(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.slow(back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  SLW.slow(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hin, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hnr)

# A source with no complete line: its rest goes to pend (proof_b_adv_part.bend).
def dec.part(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hjf: {n(len) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.part.len(o, Norm.MB{P.mkRun(rp)}, back, at, BY.len(C.BT(len, t)), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  HX.part_h(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg, hjf, hnr)

def dec.head(+hold: Bool, +dfs: B.Defs, +isc: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hin: {P.RunP.i(rp) == False{} : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +eisc: {R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == isc : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.head(isc, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  match isc:
    case False{}:
      dec.hold(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, eisc, PR.run_tick(rp, hi), hnr)
    case True{}:
      dec.write(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, hsm, eisc, hnr)


def dec.go(+hold: Bool, +dfs: B.Defs, +i: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +ei: {P.RunP.i(rp) == i : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hs: LI.SPLIT(len, t, d, at, j),
  +hn: {P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hle: {U32.is_le((j + 1 : U32), len) == True{} : Bool},
  +hby: {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hinc: {n((j + 1 : U32)) == Nat.add(n(j), 1n) : Nat},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded.go(i, back, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  match i:
    case False{}:
      dec.head(hold, dfs, R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))), fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed,
        hb, hw, hr, hg, hi, hx, ei, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, {==}, hnr)
    case True{}:
      dec.slow(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, ei, hbig, hjf, hs, hn, hle, hby, hal, hlt, hinc, hsm, hnr)

def dec.in(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hal: {Nat.is_le(n(at), n(j)) == True{} : Bool},
  +hlt: {Nat.is_lt(n(j), n(len)) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (j - at : U32)) == False{} : Bool},
  sl: LI.SPLIT(len, t, d, at, j) & ({P.nolf(P.btext(len, t, at, (j - at : U32))) == True{} : Bool} & ({U32.is_le((j + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (j - at : U32))) == True{} : Bool})),
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded.in(back, o, Norm.Run.inbody(P.mkRun(rp)), at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  match sl:
    case (hsp, q):
      match q:
        case (hn, q2):
          match q2:
            case (hle, hby):
              +hfit = {%Equal.sym(Nat, n((j - at : U32)), Nat.sub(n(j), n(at)), LP.sub_u(j, at, hal)) : {Nat.is_le(Nat.add(n(at), _), n(len)) == True{} : Bool};
                %Equal.sym(Nat, Nat.add(n(at), Nat.sub(n(j), n(at))), n(j), N.le_sub_add(n(at), n(j), hal)) : {Nat.is_le(_, n(len)) == True{} : Bool};
                N.lt_to_le(n(j), n(len), hlt) : {Nat.is_le(Nat.add(n(at), n((j - at : U32))), n(len)) == True{} : Bool}}
              %Equal.sym(NR.Run & Bool, Norm.Run.inbody(P.mkRun(rp)), (P.mkRun(rp), P.RunP.i(rp)), inb_eq(rp)) :
                DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.decoded.in(back, o, _, at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2))
              %Equal.sym(D.Bytes & String, Norm.text(C.BT(len, t), at, (j - at : U32)), (C.BT(len, t), P.btext(len, t, at, (j - at : U32))), text_eq(len, t, d, at, (j - at : U32), hok, hfit)) :
                DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.decoded.k(P.RunP.i(rp), back, o, P.mkRun(rp), at, j, _, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2))
              dec.go(hold, dfs, P.RunP.i(rp), fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hbig, {==}, hjf,
                hsp, hn, hle, hby, hal, hlt, LP.inc_len(len, t, d, j, hok, hlt), hsm, hnr)

def dec.big(+hold: Bool, +dfs: B.Defs, +big: Bool, +j: U32, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +hne: {U32.is_eq(j, len) == False{} : Bool},
  +eb: {U32.is_lt(268435456, (j - at : U32)) == big : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded.big(big, back, o, P.mkRun(rp), at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  match big:
    case True{}:
      HX.tostr_h(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, back, fneed2, hw, hr, hg, hx)
    case False{}:
      +hjr = j_range(len, t, d, at, j, hok, hs, hjf)
      +hal = W.and_l(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr)
      +hlt = j_lt(len, j, W.and_r(Nat.is_le(n(at), n(j)), Nat.is_le(n(j), n(len)), hjr), hne)
      dec.in(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hbig, hok, hs, hjf, hal, hlt, eb,
        LN.src_line(len, t, d, at, j, hok, hs, Equal.sym(Nat, n(j), D.first(XS(len, t), n(at), n(len), 10), hjf), hlt), hnr)

def dec.if(+hold: Bool, +dfs: B.Defs, +part: Bool, +j: U32, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hjf: {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat},
  +ep: {U32.is_eq(j, len) == part : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded.if(part, back, o, P.mkRun(rp), at, j, C.BT(len, t), CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  match part:
    case True{}:
      dec.part(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hw, hr, hg,
        %U.is_eq_true(j, len, ep) : {n(_) == D.first(XS(len, t), n(at), n(len), 10) : Nat}; hjf, hnr)
    case False{}:
      dec.big(hold, dfs, U32.is_lt(268435456, (j - at : U32)), j, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hbig, hok, hs, hjf, ep, {==}, hnr)

def LFW(+len: U32, +t: AT.Tree<U32>, +at: U32) -> Type:
  &j: U32 -> ({NF.lf(C.BT(len, t), at) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
  & {n(j) == D.first(XS(len, t), n(at), n(len), 10) : Nat})

def dec.j(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  ex: LFW(len, t, at),
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  match ex:
    case (+j, q):
      match q:
        case (ej, hjfc):
          +hjf = Equal.trans(Nat, n(j), D.first(XS(len, t), n(at), n(len), 10), D.first(XS(len, t), n(at), n(len), 10), hjfc, {==})
          %Equal.sym(NF.Tb, NF.lf(C.BT(len, t), at), NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}}, ej) :
            DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, Norm.decoded.lf(back, o, P.mkRun(rp), at, _, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2))
          dec.if(hold, dfs, U32.is_eq(j, len), j, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hbig, hok, hs, hjf, {==}, hnr)

# The byte mode's decoded path, for a good state whose first source is a
# byte buffer and whose run goes on (fneed2: the flag the path keeps).
def dec(+hold: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool, +fneed2: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hnr: LI.HNE(hold, len, at)) ->
  DG(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed,
    Norm.decoded(back, o, P.mkRun(rp), C.BT(len, t), at, CX(hold, dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed2)):
  +p = PPs(hold, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{LI.RTP(hold, rp)})
  +a1 = W.W1(fa, p)
  +a2 = W.W2(fa, p)
  +a3 = W.W3(fa, p)
  +a4 = W.W4(fa, p)
  +a5 = W.W5(fa, p)
  +a6 = W.W6(fa, p)
  +a7 = W.W7(fa, p)
  +a8 = W.W8(fa, p)
  +hi = HX.inv_h(hold, rp, W.c9_0(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))
  +hso = LI.srcs_head_h(hold, rest, len, t, d, at, W.c9_1(m0, a1, a2, a3, a4, a5, a6, a7, a8, hw))
  +hok = W.and_l(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  +hs = W.and_r(D.ok(C.BT(len, t), d), U32.is_le(at, len), hso)
  dec.j(hold, dfs, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed2, hb, hw, hr, hg, hi, hx, hbig, hok, hs, LN.lf_ok(len, t, d, at, hok, hs), hnr)
