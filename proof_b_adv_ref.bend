import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_split.bend as NS
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as LN
import ./proof_fast.bend as PF
import ./proof_b_adv_wf.bend as W
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_sp.bend as HX
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_adv_dec.bend as DE
import ./proof_run_base.bend as RB
import ./proof_s_one.bend as OI
import ./proof_s_laws.bend as SLA
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# A line the byte splitter refuses (norm_seq.bend's split.out on Ref, ref.b):
# under -c e the String path; under -c w, when the window's contig is the
# line's CHROM (Win.on), the line passed through with its warning, as the
# String path's slow.vd writes it (body_done of the problem c); else the
# String path. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def MS() -> Data:
  Maybe<&2, String>

# ---------------------------------------------------------------------------
# The window's contig
# ---------------------------------------------------------------------------

# Win.on gives the window back with a flag; with the flag set, ch is a contig
# of the reference.
def WON(+fa: List<&2, B.Contig>, +wp: PC.WP, +ch: String) -> Type:
  &b: Bool -> ({Norm.Win.on(PC.mkWin(fa, wp), ch) == (PC.mkWin(fa, wp), b) : Norm.Win & Bool} &
    ({b == True{} : Bool} -> {Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}))

def won.k(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +ch: String, +m: MS(), +em: {B.Fasta.find(fa, c) == m : MS()}) -> WON(fa, PC.WPKnown{c, a, b}, ch):
  match m:
    case None{}:
      (False{}, ({%Equal.sym(MS(), B.Fasta.find(fa, c), None{}, em) : {Norm.Win.on(PC.mkWin.k(_, c, a, b, False{}), ch) == (PC.mkWin.k(_, c, a, b, False{}), False{}) : Norm.Win & Bool};
        {==} : {Norm.Win.on(PC.mkWin(fa, PC.WPKnown{c, a, b}), ch) == (PC.mkWin(fa, PC.WPKnown{c, a, b}), False{}) : Norm.Win & Bool}},
        h => Empty.absurd({Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}, N.false_ne_true(h))))
    case Some{+r}:
      (String.eq(ch, c), ({%Equal.sym(MS(), B.Fasta.find(fa, c), Some{r}, em) : {Norm.Win.on(PC.mkWin.k(_, c, a, b, False{}), ch) == (PC.mkWin.k(_, c, a, b, False{}), String.eq(ch, c)) : Norm.Win & Bool};
        {==} : {Norm.Win.on(PC.mkWin(fa, PC.WPKnown{c, a, b}), ch) == (PC.mkWin(fa, PC.WPKnown{c, a, b}), String.eq(ch, c)) : Norm.Win & Bool}},
        h => {%Equal.sym(String, ch, c, RB.str_eq_sound(ch, c, h)) : {Maybe.is_some(&2, String, B.Fasta.find(fa, _)) == True{} : Bool};
          %Equal.sym(MS(), B.Fasta.find(fa, c), Some{r}, em) : {Maybe.is_some(&2, String, _) == True{} : Bool};
          {==} : {Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}}))

def won.s(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +ch: String, +m: MS(), +em: {B.Fasta.find(fa, c) == m : MS()}) -> WON(fa, PC.WPStr{c, a, b}, ch):
  match m:
    case None{}:
      (False{}, ({%Equal.sym(MS(), B.Fasta.find(fa, c), None{}, em) : {Norm.Win.on(PC.mkWin.k(_, c, a, b, True{}), ch) == (PC.mkWin.k(_, c, a, b, True{}), False{}) : Norm.Win & Bool};
        {==} : {Norm.Win.on(PC.mkWin(fa, PC.WPStr{c, a, b}), ch) == (PC.mkWin(fa, PC.WPStr{c, a, b}), False{}) : Norm.Win & Bool}},
        h => Empty.absurd({Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}, N.false_ne_true(h))))
    case Some{+r}:
      (False{}, ({%Equal.sym(MS(), B.Fasta.find(fa, c), Some{r}, em) : {Norm.Win.on(PC.mkWin.k(_, c, a, b, True{}), ch) == (PC.mkWin.k(_, c, a, b, True{}), False{}) : Norm.Win & Bool};
        {==} : {Norm.Win.on(PC.mkWin(fa, PC.WPStr{c, a, b}), ch) == (PC.mkWin(fa, PC.WPStr{c, a, b}), False{}) : Norm.Win & Bool}},
        h => Empty.absurd({Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}, N.false_ne_true(h))))

def win_on(+fa: List<&2, B.Contig>, +wp: PC.WP, +ch: String) -> WON(fa, wp, ch):
  match wp:
    case PC.WPNone{}:
      (False{}, ({==}, h => Empty.absurd({Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}, N.false_ne_true(h))))
    case PC.WPUnk{+c}:
      (False{}, ({==}, h => Empty.absurd({Maybe.is_some(&2, String, B.Fasta.find(fa, ch)) == True{} : Bool}, N.false_ne_true(h))))
    case PC.WPKnown{+c, +a, +b}:
      won.k(fa, c, a, b, ch, B.Fasta.find(fa, c), {==})
    case PC.WPStr{+c, +a, +b}:
      won.s(fa, c, a, b, ch, B.Fasta.find(fa, c), {==})

# ---------------------------------------------------------------------------
# The whole line's outcome does not stop the run under -c w
# ---------------------------------------------------------------------------

def stp.p(+c: Maybe<&2, B.Code>, +fs: List<&2, String>, +bd: String, +seq: List<&2, B.Base>, +v: B.Var) ->
  {Norm.stops(L.problem(c, fs, bd, seq, v), False{}) == False{} : Bool}:
  match c:
    case Some{+k}:
      {==}
    case None{}:
      {==}

def stp.b(+e: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>, +fs: List<&2, String>, +bd: String, +seq: List<&2, B.Base>) ->
  {Norm.stops(L.judge.bases(e, r, a, fs, bd, seq), False{}) == False{} : Bool}:
  match r a:
    case Some{+ref} Some{+alts}:
      stp.p(L.checks(e, seq, B.Var{B.Rec.pos(fs), ref, alts}), fs, bd, seq, B.Var{B.Rec.pos(fs), ref, alts})
    case None{} Some{+alts}:
      {==}
    case Some{+ref} None{}:
      {==}
    case None{} None{}:
      {==}

def stp.c(+m: MS(), +fa: List<&2, B.Contig>, +fs: List<&2, String>, +bd: String,
  +em: {B.Fasta.find(fa, B.Rec.field(fs, 0n)) == m : MS()}, +hf: {Maybe.is_some(&2, String, B.Fasta.find(fa, B.Rec.field(fs, 0n))) == True{} : Bool}) ->
  {Norm.stops(L.judge.contig(m, fs, bd), False{}) == False{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Norm.stops(L.judge.contig(None{}, fs, bd), False{}) == False{} : Bool},
        N.false_ne_true({%Equal.sym(MS(), None{}, B.Fasta.find(fa, B.Rec.field(fs, 0n)), Equal.sym(MS(), B.Fasta.find(fa, B.Rec.field(fs, 0n)), None{}, em)) : {Maybe.is_some(&2, String, _) == True{} : Bool}; hf : {False{} == True{} : Bool}}))
    case Some{+raw}:
      +ref = B.Rec.field(fs, 3n)
      +e = Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)
      stp.b(B.Info.end_ok(B.Rec.field(fs, 7n), e), B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, bd, B.Bases.of_fasta(raw))

def stp.k(+sk: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +bd: String,
  +hf: {Maybe.is_some(&2, String, B.Fasta.find(fa, B.Rec.field(fs, 0n))) == True{} : Bool}) ->
  {Norm.stops(L.judge.shape(False{}, sk, fa, fs, bd), False{}) == False{} : Bool}:
  match sk:
    case True{}:
      {==}
    case False{}:
      stp.c(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fa, fs, bd, {==}, hf)

# A line that is not MALFORMED, its CHROM a contig of the reference: judge's
# outcome is not MALFORMED nor UNKNOWN_CHROM.
def stops_j(+fa: List<&2, B.Contig>, +bd: String,
  +hm: {B.Rec.malformed(B.Rec.fields(bd)) == False{} : Bool},
  +hf: {Maybe.is_some(&2, String, B.Fasta.find(fa, B.Rec.field(B.Rec.fields(bd), 0n))) == True{} : Bool}) ->
  {Norm.stops(L.judge(fa, bd), False{}) == False{} : Bool}:
  +fs = B.Rec.fields(bd)
  %Equal.sym(Bool, B.Rec.malformed(fs), False{}, hm) : {Norm.stops(L.judge.shape(_, B.Rec.out_of_scope(fs), fa, fs, bd), False{}) == False{} : Bool}
  stp.k(B.Rec.out_of_scope(fs), fa, fs, bd, hf)

# ---------------------------------------------------------------------------
# A refused line is not MALFORMED
# ---------------------------------------------------------------------------

def is_un(pt: B.Parts) -> Bool:
  match pt:
    case B.Unsplit{c}:
      True{}
    case _:
      False{}

def whole_un(-A: Type, +c: B.Code, +h: {B.Whole{} == B.Unsplit{c} : B.Parts}) -> A:
  Empty.absurd(A, N.false_ne_true(Equal.cong(B.Parts, Bool, z => is_un(z), B.Whole{}, B.Unsplit{c}, h)))

def pnm.k(+m: Bool, +dfs: B.Defs, +o: B.Opts, +bd: String, +c: B.Code,
  +em: {B.Rec.malformed(B.Rec.fields(bd)) == m : Bool},
  +hp: {B.Rec.parts(dfs, o, bd) == B.Unsplit{c} : B.Parts}) -> {B.Rec.malformed(B.Rec.fields(bd)) == False{} : Bool}:
  match m:
    case False{}:
      em
    case True{}:
      whole_un({B.Rec.malformed(B.Rec.fields(bd)) == False{} : Bool}, c,
        Equal.trans(B.Parts, B.Whole{}, B.Rec.parts(dfs, o, bd), B.Unsplit{c}, Equal.sym(B.Parts, B.Rec.parts(dfs, o, bd), B.Whole{}, SLA.whole_malformed(dfs, o, bd, em)), hp))

def parts_nm(+dfs: B.Defs, +o: B.Opts, +bd: String, +c: B.Code, +hp: {B.Rec.parts(dfs, o, bd) == B.Unsplit{c} : B.Parts}) ->
  {B.Rec.malformed(B.Rec.fields(bd)) == False{} : Bool}:
  pnm.k(B.Rec.malformed(B.Rec.fields(bd)), dfs, o, bd, c, {==}, hp)

# A record of a split line (one ALT) is not refused.
def one_not_unsplit(+dfs: B.Defs, +o: B.Opts, +bd: String, +c: B.Code,
  +h1: {Nat.is_lt(L.n_alts(bd), 2n) == True{} : Bool},
  +hp: {B.Rec.parts(dfs, o, bd) == B.Unsplit{c} : B.Parts}) -> Empty:
  whole_un(Empty, c, Equal.trans(B.Parts, B.Whole{}, B.Rec.parts(dfs, o, bd), B.Unsplit{c}, Equal.sym(B.Parts, B.Rec.parts(dfs, o, bd), B.Whole{}, OI.one_parts(dfs, o, bd, h1)), hp))

# ---------------------------------------------------------------------------
# The line passed through: what the String path writes for the problem c
# ---------------------------------------------------------------------------

def nt(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(h))
    case False{}:
      {==}

def O1(+st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>) -> B.Opts:
  B.Opts{st, w, True{}, o0, args}

def TA(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32) -> String:
  P.btext(len, t, at, (lf - at : U32))

# The line's body (B.Text.line) and its fields k.
def BDY(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32) -> String:
  B.Line.body(B.Text.line(TA(len, t, at, lf)))

def FK(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32, +k: Nat) -> String:
  B.Rec.field(B.Rec.fields(BDY(len, t, at, lf)), k)

def CXF(+dfs: B.Defs, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool) -> Norm.Cx:
  Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof, dfs, False{}}

def PPF(+dfs: B.Defs, +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool) -> S.StP:
  LI.PPs(False{}, dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)

# The pass-through is body_done of the problem c (CHROM and POS from the
# fields fs, as the String path reads them).
def ref_bd(+w: Nat, +o0: Bool, +args: List<&2, String>, p: NR.Run & Nat, +c: B.Code, +fs: List<&2, String>, +l: B.Line, +k: Nat, +x: String,
  -b: D.Bytes, +s: U32, +lf: U32, -cx: Norm.Cx, -win: Norm.Win) ->
  {Norm.ref.pos(O1(False{}, w, o0, args), p, c, B.Rec.field(fs, 0n), (b, B.Rec.field(fs, 1n)), s, lf, cx, win) ==
   Norm.body_done(B.Res{B.Problem{c}, k, x, False{}}, O1(False{}, w, o0, args), p, l, fs, s, lf, b, cx, win) : Norm.Adv}:
  match p:
    case (run, +nn):
      {==}

# A field of the line, as the String path's fields (J.pfs of Norm.line's body).
def fk_eq(+len: U32, +t: AT.Tree<U32>, +at: U32, +lf: U32, +k: Nat, +hk: {Nat.is_lt(k, 7n) == True{} : Bool}) ->
  {FK(len, t, at, lf, k) == B.Rec.field(J.pfs(B.Line.body(Norm.line(TA(len, t, at, lf)))), k) : String}:
  +A0 = TA(len, t, at, lf)
  %Equal.sym(String, B.Rec.field(J.pfs(B.Line.body(Norm.line(A0))), k), B.Rec.field(B.Rec.fields(B.Line.body(Norm.line(A0))), k), PF.pfs_field(B.Line.body(Norm.line(A0)), k, hk)) :
    {FK(len, t, at, lf, k) == _ : String}
  %Equal.sym(B.Line, Norm.line(A0), B.Text.line(A0), LN.line_eq(A0)) :
    {FK(len, t, at, lf, k) == B.Rec.field(B.Rec.fields(B.Line.body(_)), k) : String}
  {==}

def ref.pass(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code,
  +hpu: {B.Rec.parts(dfs, O1(False{}, w, o0, args), BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +hfc: {Maybe.is_some(&2, String, B.Fasta.find(fa, FK(len, t, at, lf, 0n))) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (lf - at : U32)) == False{} : Bool},
  +hsp: LI.SPLIT(len, t, d, at, lf), +hn: {P.nolf(TA(len, t, at, lf)) == True{} : Bool}, +hle: {U32.is_le((lf + 1 : U32), len) == True{} : Bool}, +hby: {E.is_bytes(TA(len, t, at, lf)) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.ref.pos(O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, FK(len, t, at, lf, 0n), (C.BT(len, t), FK(len, t, at, lf, 1n)), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  +o = O1(False{}, w, o0, args)
  +A0 = TA(len, t, at, lf)
  +l = Norm.line(A0)
  +bd = B.Line.body(l)
  +fs = J.pfs(bd)
  +p = PPF(dfs, o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
  +m0 = S.md_ok(S.MBP{LI.RTP(False{}, rp)})
  +hi = HX.inv_h(False{}, rp, W.c9_0(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw))
  +RPR = {B.Res{B.Problem{c}, B.Rec.pos(fs), bd, False{}} : B.Res}
  +hm2 = {%Equal.sym(B.Line, Norm.line(A0), B.Text.line(A0), LN.line_eq(A0)) : {B.Rec.malformed(B.Rec.fields(B.Line.body(_))) == False{} : Bool};
    parts_nm(dfs, o, BDY(len, t, at, lf), c, hpu) : {B.Rec.malformed(B.Rec.fields(bd)) == False{} : Bool}}
  +hf2 = {%Equal.sym(B.Line, Norm.line(A0), B.Text.line(A0), LN.line_eq(A0)) : {Maybe.is_some(&2, String, B.Fasta.find(fa, B.Rec.field(B.Rec.fields(B.Line.body(_)), 0n))) == True{} : Bool};
    hfc : {Maybe.is_some(&2, String, B.Fasta.find(fa, B.Rec.field(B.Rec.fields(bd), 0n))) == True{} : Bool}}
  +hst = stops_j(fa, bd, hm2, hf2)
  +hbl = {%Equal.sym(Bool, False{}, Norm.stops(L.judge(fa, bd), False{}), Equal.sym(Bool, Norm.stops(L.judge(fa, bd), False{}), False{}, hst)) :
      SLW.BLX(fa, dfs, o, rp, A0, Bool.pick(B.Res, _, L.judge(fa, bd), RPR));
    SLW.blx_u(fa, dfs, o, rp, A0, c, hx, hin, hpu) : SLW.BLX(fa, dfs, o, rp, A0, RPR)}
  %Equal.sym(String, FK(len, t, at, lf, 0n), B.Rec.field(fs, 0n), fk_eq(len, t, at, lf, 0n, {==})) :
    S.AdvG(fa, T, cs, O, N, p, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, _, (C.BT(len, t), FK(len, t, at, lf, 1n)), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
  %Equal.sym(String, FK(len, t, at, lf, 1n), B.Rec.field(fs, 1n), fk_eq(len, t, at, lf, 1n, {==})) :
    S.AdvG(fa, T, cs, O, N, p, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, B.Rec.field(fs, 0n), (C.BT(len, t), _), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
  %Equal.sym(Norm.Adv, Norm.ref.pos(o, Norm.ticked(P.mkRun(rp)), c, B.Rec.field(fs, 0n), (C.BT(len, t), B.Rec.field(fs, 1n)), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)),
    Norm.body_done(RPR, o, Norm.ticked(P.mkRun(rp)), l, fs, at, lf, C.BT(len, t), CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)),
    ref_bd(w, o0, args, Norm.ticked(P.mkRun(rp)), c, fs, l, B.Rec.pos(fs), bd, C.BT(len, t), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))) :
    S.AdvG(fa, T, cs, O, N, p, _)
  SLW.SL.body(False{}, dfs, RPR, fa, T, cs, O, N, o, rp, len, t, d, at, lf, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hi, hx, hin, hbig,
    Equal.sym(Nat, D.first(D.view(C.BT(len, t)), n(at), n(len), 10), n(lf), hfl), hsp, hn, hle, hby, hal, hlt, LP.inc_len(len, t, d, lf, hok, hlt), hsm, hok, hs,
    {==}, hbl, SLW.body_bytes(A0, hby), PR.run_tick(rp, hi), {==})

# ---------------------------------------------------------------------------
# The refused line's branch (-c w): through, or the String path
# ---------------------------------------------------------------------------

def SLP(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32) -> Type:
  LI.SPLIT(len, t, d, at, lf) & ({P.nolf(TA(len, t, at, lf)) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(TA(len, t, at, lf)) == True{} : Bool}))

def ref.sl(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code,
  +hpu: {B.Rec.parts(dfs, O1(False{}, w, o0, args), BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +hfc: {Maybe.is_some(&2, String, B.Fasta.find(fa, FK(len, t, at, lf, 0n))) == True{} : Bool},
  +hsm: {U32.is_lt(268435456, (lf - at : U32)) == False{} : Bool},
  sl: SLP(len, t, d, at, lf)) ->
  S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.ref.pos(O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, FK(len, t, at, lf, 0n), (C.BT(len, t), FK(len, t, at, lf, 1n)), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp))):
  (hsp, r1) = sl
  (hn, r2) = r1
  (hle, hby) = r2
  ref.pass(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, c, hpu, hfc, hsm, hsp, hn, hle, hby)

def ref.k(+ok: Bool, +bo: Bool, +big: Bool, +dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, O1(False{}, w, o0, args), BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), FK(len, t, at, lf, 1n)) : D.Bytes & String},
  +eok: {Bool.and(bo, Bool.not(big)) == ok : Bool},
  +ebig: {U32.is_lt(268435456, (lf - at : U32)) == big : Bool},
  imp: {bo == True{} : Bool} -> {Maybe.is_some(&2, String, B.Fasta.find(fa, FK(len, t, at, lf, 0n))) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.ref.if(ok, back, O1(False{}, w, o0, args), P.mkRun(rp), c, FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed)):
  match ok:
    case False{}:
      DE.dec(False{}, dfs, fa, T, cs, O, N, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig, {==})
    case True{}:
      +hbo = N.and_true_l(bo, Bool.not(big), eok)
      +hnb = nt(big, N.and_true_r(bo, Bool.not(big), eok))
      +hsm = Equal.trans(Bool, U32.is_lt(268435456, (lf - at : U32)), big, False{}, ebig, hnb)
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), f1), (C.BT(len, t), FK(len, t, at, lf, 1n)), h1) :
        S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.ref.pos(O1(False{}, w, o0, args), Norm.ticked(P.mkRun(rp)), c, FK(len, t, at, lf, 0n), _, at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp)))
      ref.sl(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl, c, hpu, imp(hbo), hsm,
        LN.src_line(len, t, d, at, lf, hok, hs, hfl, hlt))

def ref.won(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, O1(False{}, w, o0, args), BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), FK(len, t, at, lf, 1n)) : D.Bytes & String},
  q: WON(fa, wp, FK(len, t, at, lf, 0n))) ->
  S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.ref.on(Norm.Win.on(PC.mkWin(fa, wp), FK(len, t, at, lf, 0n)), U32.is_lt(268435456, (lf - at : U32)), back, O1(False{}, w, o0, args), P.mkRun(rp), c, FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, CXF(dfs, rest, pd, eof), fneed)):
  (+bo, q1) = q
  (eq, imp) = q1
  +big = U32.is_lt(268435456, (lf - at : U32))
  %Equal.sym(Norm.Win & Bool, Norm.Win.on(PC.mkWin(fa, wp), FK(len, t, at, lf, 0n)), (PC.mkWin(fa, wp), bo), eq) :
    S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
      Norm.ref.on(_, big, back, O1(False{}, w, o0, args), P.mkRun(rp), c, FK(len, t, at, lf, 0n), f1, C.BT(len, t), at, lf, CXF(dfs, rest, pd, eof), fneed))
  ref.k(Bool.and(bo, Bool.not(big)), bo, big, dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl,
    c, f1, hpu, h1, {==}, {==}, imp)

# A line the byte splitter refuses (code c; its CHROM and POS ranges f0, f1),
# from a byte source.
def ref.adv(+dfs: B.Defs, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +st: Bool, +w: Nat, +o0: Bool, +args: List<&2, String>, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, PPF(dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, PPF(dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, PPF(dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +lf: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hal: {Nat.is_le(U32.to_nat(at), U32.to_nat(lf)) == True{} : Bool},
  +hlt: {Nat.is_lt(U32.to_nat(lf), U32.to_nat(len)) == True{} : Bool},
  +hfl: {D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10) == U32.to_nat(lf) : Nat},
  +c: B.Code, +f0: NS.Rg, +f1: NS.Rg,
  +hpu: {B.Rec.parts(dfs, O1(st, w, o0, args), BDY(len, t, at, lf)) == B.Unsplit{c} : B.Parts},
  +h0: {NS.txt(C.BT(len, t), f0) == (C.BT(len, t), FK(len, t, at, lf, 0n)) : D.Bytes & String},
  +h1: {NS.txt(C.BT(len, t), f1) == (C.BT(len, t), FK(len, t, at, lf, 1n)) : D.Bytes & String}) ->
  S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(st, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.split.out(NS.Ref{C.BT(len, t), c, f0, f1}, back, O1(st, w, o0, args), P.mkRun(rp), at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed)):
  match st:
    case True{}:
      DE.dec(False{}, dfs, fa, T, cs, O, N, O1(True{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, fneed, hb, hw, hr, hg, hx, hbig, {==})
    case False{}:
      %Equal.sym(D.Bytes & String, NS.txt(C.BT(len, t), f0), (C.BT(len, t), FK(len, t, at, lf, 0n)), h0) :
        S.AdvG(fa, T, cs, O, N, PPF(dfs, O1(False{}, w, o0, args), rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
          Norm.ref.ch(_, back, O1(False{}, w, o0, args), P.mkRun(rp), c, f1, at, lf, CXF(dfs, rest, pd, eof), PC.mkWin(fa, wp), fneed))
      ref.won(dfs, fa, T, cs, O, N, w, o0, args, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, lf, hok, hs, hal, hlt, hfl,
        c, f1, hpu, h1, win_on(fa, wp, FK(len, t, at, lf, 0n)))
