import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
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
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# adv_ok on the #CHROM line in the byte mode (norm.bend head with isc True):
# the header written (run_head_write), or the switch to the String mode when
# it does not fit. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# The run's spec state
# ---------------------------------------------------------------------------

def sth(st: R.RunSt) -> String:
  match st:
    case R.RunSt{n0, i, h, c, e, l, b, k, o, ns, x}:
      h

law h_spec:
  for +rp: P.RunP
  {sth(P.specRun(rp)) == P.RunP.h(rp) : String}

def h_spec(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

law tick_h:
  for +st: R.RunSt
  {sth(R.tick(st)) == sth(st) : String}

def tick_h(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law h_tick:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.h(rp1) == P.RunP.h(rp) : String}

def h_tick(rp, rp1, s1):
  %h_spec(rp1) : {_ == P.RunP.h(rp) : String}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {sth(_) == P.RunP.h(rp) : String}
  %Equal.sym(String, sth(R.tick(P.specRun(rp))), sth(P.specRun(rp)), tick_h(P.specRun(rp))) : {_ == P.RunP.h(rp) : String}
  h_spec(rp)

law sb_h:
  for +st: R.RunSt
  for +h: {P.st_bytes(st) == True{} : Bool}
  {E.is_bytes(sth(st)) == True{} : Bool}

def sb_h(st, h):
  match st:
    case R.RunSt{+n0, +i, +hh, +c, +e, +l, +b, +k, +o, +ns, +x}:
      W.and_l(E.is_bytes(hh), P.items_bytes(b), W.and_l(Bool.and(E.is_bytes(hh), P.items_bytes(b)), E.is_bytes(o), h))

# The held header of a good run is bytes.
def hbytes(+rp: P.RunP, +hi: {PR.RunInv(rp) == True{} : Bool}) ->
  {E.is_bytes(P.RunP.h(rp)) == True{} : Bool}:
  %h_spec(rp) : {E.is_bytes(_) == True{} : Bool}
  sb_h(P.specRun(rp), PR.run_bytes(rp, hi))

law ib_spec:
  for +rp: P.RunP
  {R.RunSt.inbody(P.specRun(rp)) == P.RunP.i(rp) : Bool}

def ib_spec(rp):
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

law tick_ib:
  for +st: R.RunSt
  {R.RunSt.inbody(R.tick(st)) == R.RunSt.inbody(st) : Bool}

def tick_ib(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law tick_hl:
  for +st: R.RunSt
  {R.RunSt.halt(R.tick(st)) == R.RunSt.halt(st) : Bool}

def tick_hl(st):
  match st:
    case R.RunSt{+n0, +i, +h, +c, +e, +l, +b, +k, +o, +ns, +x}:
      {==}

law tk_i:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.i(rp1) == P.RunP.i(rp) : Bool}

def tk_i(rp, rp1, s1):
  %ib_spec(rp1) : {_ == P.RunP.i(rp) : Bool}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.RunSt.inbody(_) == P.RunP.i(rp) : Bool}
  %Equal.sym(Bool, R.RunSt.inbody(R.tick(P.specRun(rp))), R.RunSt.inbody(P.specRun(rp)), tick_ib(P.specRun(rp))) : {_ == P.RunP.i(rp) : Bool}
  ib_spec(rp)

law tk_x:
  for +rp: P.RunP
  for +rp1: P.RunP
  for +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt}
  {P.RunP.x(rp1) == P.RunP.x(rp) : Bool}

def tk_x(rp, rp1, s1):
  %halt_spec(rp1) : {_ == P.RunP.x(rp) : Bool}
  %Equal.sym(R.RunSt, P.specRun(rp1), R.tick(P.specRun(rp)), s1) : {R.RunSt.halt(_) == P.RunP.x(rp) : Bool}
  %Equal.sym(Bool, R.RunSt.halt(R.tick(P.specRun(rp))), R.RunSt.halt(P.specRun(rp)), tick_hl(P.specRun(rp))) : {_ == P.RunP.x(rp) : Bool}
  halt_spec(rp)

law head_true_i:
  for +st: R.RunSt
  for +o: B.Opts
  for +l: B.Line
  {R.RunSt.inbody(R.head_line(True{}, st, o, l)) == True{} : Bool}

def head_true_i(st, o, l):
  match st l:
    case R.RunSt{+n0, +i, +h, +c, +e, +la, +b, +k, +out, +ns, +x} B.Line{+bd, +term}:
      {==}

law rhead_eq:
  for +rp: P.RunP
  {Norm.Run.head(P.mkRun(rp)) == (P.mkRun(rp), Norm.len_le(P.RunP.h(rp), 268435456)) : NR.Run & Bool}

def rhead_eq(rp):
  match rp:
    case P.RunP{+n0, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      {==}

# The spec's step on the #CHROM line (not stopped, before the body).
law write_step:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +A: String
  for +hx: {P.RunP.x(rp) == False{} : Bool}
  for +hin: {P.RunP.i(rp) == False{} : Bool}
  for +eisc: {R.is_chrom_line(B.Line.body(Norm.line(A))) == True{} : Bool}
  {L.line_step(fa, o, P.specRun(rp), B.Text.line(A)) == R.head_line(True{}, R.tick(P.specRun(rp)), o, Norm.line(A)) : R.RunSt}

def write_step(fa, o, rp, A, hx, hin, eisc):
  +st = P.specRun(rp)
  +RHS = R.head_line(True{}, R.tick(st), o, Norm.line(A))
  %Equal.sym(Bool, R.RunSt.halt(st), False{}, Equal.trans(Bool, R.RunSt.halt(st), P.RunP.x(rp), False{}, halt_spec(rp), hx)) :
    {L.line_step.go(_, fa, o, st, B.Text.line(A)) == RHS : R.RunSt}
  %Equal.sym(Bool, R.RunSt.inbody(st), False{}, Equal.trans(Bool, R.RunSt.inbody(st), P.RunP.i(rp), False{}, ib_spec(rp), hin)) :
    {L.line_in(_, fa, o, R.tick(st), B.Text.line(A)) == RHS : R.RunSt}
  %LN.line_eq(A) : {R.head_line(R.is_chrom_line(B.Line.body(_)), R.tick(st), o, _) == RHS : R.RunSt}
  %Equal.sym(Bool, R.is_chrom_line(B.Line.body(Norm.line(A))), True{}, eisc) : {R.head_line(_, R.tick(st), o, Norm.line(A)) == RHS : R.RunSt}
  {==}

# ---------------------------------------------------------------------------
# The added lines are bytes
# ---------------------------------------------------------------------------

def cc.k(+b: Bool, +x: U32, +h: {U32.is_lt(x, 256) == True{} : Bool}) ->
  {U32.is_lt(Char.to_u32(Bool.pick(Char, b, ' ', Chr{x})), 256) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

def cc_bytes(+c: Char, +h: {U32.is_lt(Char.to_u32(c), 256) == True{} : Bool}) ->
  {U32.is_lt(Char.to_u32(R.clean.char(c)), 256) == True{} : Bool}:
  match c:
    case Chr{+x}:
      cc.k(Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)), x, h)

def clean_bytes(+s: String, +h: {E.is_bytes(s) == True{} : Bool}) ->
  {E.is_bytes(R.clean(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      W.and_tt(U32.is_lt(Char.to_u32(R.clean.char(c)), 256), E.is_bytes(R.clean(r)),
        cc_bytes(c, W.and_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), h)),
        clean_bytes(r, W.and_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(r), h)))

def at_bytes(+xs: List<&2, String>, +h: {E.all_bytes(xs) == True{} : Bool}) ->
  {E.is_bytes(R.args_text(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      LSS.bytes_app(" ", String.append(R.clean(x), R.args_text(r)), {==},
        LSS.bytes_app(R.clean(x), R.args_text(r), clean_bytes(x, W.and_l(E.is_bytes(x), E.all_bytes(r), h)), at_bytes(r, W.and_r(E.is_bytes(x), E.all_bytes(r), h))))

def added_bytes(+o: B.Opts, +term: String,
  +ha: {E.all_bytes(S.opts_args(o)) == True{} : Bool},
  +ht: {E.is_bytes(term) == True{} : Bool}) ->
  {E.is_bytes(R.added(o, term)) == True{} : Bool}:
  match o:
    case B.Opts{+sv, +w, +args}:
      +L2 = {"##framebender_normCommand=norm" : String}
      +R4 = String.append(R.args_text(args), term)
      +R3 = String.append(L2, R4)
      +R2 = String.append(term, R3)
      +R1 = String.append(R.version(), R2)
      LSS.bytes_app("##framebender_normVersion=", R1, {==},
        LSS.bytes_app(R.version(), R2, {==},
          LSS.bytes_app(term, R3, ht,
            LSS.bytes_app(L2, R4, {==},
              LSS.bytes_app(R.args_text(args), term, at_bytes(args, ha), ht)))))

def tb(+cr: Bool, +A: String) -> {E.is_bytes(B.Line.term(B.Text.line.if(cr, A))) == True{} : Bool}:
  match cr:
    case True{}:
      {==}
    case False{}:
      {==}

def term_bytes(+A: String) -> {E.is_bytes(B.Line.term(Norm.line(A))) == True{} : Bool}:
  tb(Norm.ends_cr(A), A)

def line_bytes(+A: String, +hb: {E.is_bytes(A) == True{} : Bool}) ->
  {E.is_bytes(B.Line.text(Norm.line(A))) == True{} : Bool}:
  %Equal.sym(String, B.Line.text(Norm.line(A)), A ++ "\n", CS.ltext_nl(A)) : {E.is_bytes(_) == True{} : Bool}
  LSS.bytes_app(A, "\n", hb, {==})

# ---------------------------------------------------------------------------
# The #CHROM line
# ---------------------------------------------------------------------------

def TKW(+rp: P.RunP) -> Type:
  &p2: P.RunP -> ({NR.tick(P.mkRun(rp)) == P.mkRun(p2) : NR.Run}
  & ({PR.RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == R.tick(P.specRun(rp)) : R.RunSt}
  & ({P.RunP.n(p2) == 1n+P.RunP.n(rp) : Nat}
  & ({P.RunP.obl(p2) == P.RunP.obl(rp) : U32}
  & {P.RunP.ow(p2) == P.RunP.ow(rp) : U32})))))

def wr.h(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
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
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  hh: &p2: P.RunP -> ({NR.head_line(True{}, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))) == P.mkRun(p2) : NR.Run}
    & ({PR.RunInv(p2) == True{} : Bool}
    & {P.specRun(p2) == R.head_line(True{}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))) : R.RunSt}))) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.done.b(o, (NR.head_line(True{}, P.mkRun(rp1), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), C.BT(len, t)), (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  match hh:
    case (+rp2, q):
      match q:
        case (e2, q2):
          match q2:
            case (i2c, sp2c):
              +i2 = Equal.trans(Bool, PR.RunInv(rp2), True{}, True{}, i2c, {==})
              +l = Norm.line(P.btext(len, t, at, (j - at : U32)))
              +sp2 = Equal.trans(R.RunSt, P.specRun(rp2), R.head_line(True{}, P.specRun(rp1), o, l), R.head_line(True{}, P.specRun(rp1), o, l), sp2c, {==})
              +IT2 = S.intext(LI.P2(o, rp2, len, t, d, j, rest, pd, eof, wp), cs)
              +hrs = Equal.trans(R.RunSt, P.specRun(rp2), R.head_line(True{}, R.tick(P.specRun(rp)), o, l), L.line_step(fa, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))),
                %s1 : {P.specRun(rp2) == R.head_line(True{}, _, o, l) : R.RunSt}; sp2,
                Equal.sym(R.RunSt, L.line_step(fa, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))), R.head_line(True{}, R.tick(P.specRun(rp)), o, l), write_step(fa, o, rp, P.btext(len, t, at, (j - at : U32)), hx, hin, eisc)))
              +hib = {%Equal.sym(R.RunSt, P.specRun(rp2), R.head_line(True{}, P.specRun(rp1), o, l), sp2) : {R.RunSt.inbody(_) == True{} : Bool};
                head_true_i(P.specRun(rp1), o, l) : {R.RunSt.inbody(P.specRun(rp2)) == True{} : Bool}}
              %Equal.sym(NR.Run, NR.head_line(True{}, P.mkRun(rp1), o, l), P.mkRun(rp2), e2) :
                S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, (_, C.BT(len, t)), (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp)))
              LI.went_line(fa, T, cs, O, N, o, rp, rp2, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hw, hr, hg, hs, hle,
                LN.lines_cons(P.btext(len, t, at, (j - at : U32)), IT2, hn), hal, hlt, hinc, i2,
                Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), P.specRun(rp2), L.line_step(fa, o, P.specRun(rp), B.Text.line(P.btext(len, t, at, (j - at : U32)))), hrs),
                W.or_l(R.RunSt.inbody(P.specRun(rp2)), Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N)), hib))

def wr.tick(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
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
  +hh: {Norm.len_le(P.RunP.h(rp), 268435456) == True{} : Bool},
  +hadd: {Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456) == True{} : Bool},
  +hl: {Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456) == True{} : Bool},
  tk: TKW(rp)) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.done.b(o, (NR.head_line(True{}, NR.tick(P.mkRun(rp)), o, Norm.line(P.btext(len, t, at, (j - at : U32)))), C.BT(len, t)), (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
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
                  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), False{}, tk_i(rp, rp1, s1), hin)
                  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, tk_x(rp, rp1, s1), hx)
                  +hh1 = {%Equal.sym(String, P.RunP.h(rp1), P.RunP.h(rp), h_tick(rp, rp1, s1)) : {Norm.len_le(_, 268435456) == True{} : Bool}; hh : {Norm.len_le(P.RunP.h(rp1), 268435456) == True{} : Bool}}
                  +p = LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)
                  +m0 = S.md_ok(S.MBP{rp})
                  +ha = W.c9_8(m0, W.W1(fa, p), W.W2(fa, p), W.W3(fa, p), W.W4(fa, p), W.W5(fa, p), W.W6(fa, p), W.W7(fa, p), W.W8(fa, p), hw)
                  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), e1) :
                    S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.done.b(o, (NR.head_line(True{}, _, o, l), C.BT(len, t)), (j + 1 : U32), Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp)))
                  wr.h(fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, hsm, eisc, rp1, s1,
                    PR.run_head_write(rp1, o, l, i1, hin1, hx1, hh1, hbytes(rp1, i1), line_bytes(P.btext(len, t, at, (j - at : U32)), hby),
                      added_bytes(o, B.Line.term(l), ha, term_bytes(P.btext(len, t, at, (j - at : U32)))), hl, hadd))

def wr.fits(+fits: Bool, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
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
  +ef: {Bool.and(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456)) == fits : Bool}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.head.fits(fits, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  match fits:
    case False{}:
      TS.to_ms_went(fa, T, cs, O, N, o, rp, Con{LI.SB(len, t, d, at), rest}, pd, eof, back, wp, asked, fneed, back, False{}, hw, hr, hg, hx)
    case True{}:
      wr.tick(fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, hsm, eisc,
        W.and_l(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456), W.and_l(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456), ef)),
        W.and_r(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456), W.and_l(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456), ef)),
        W.and_r(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456), ef),
        PR.run_tick(rp, hi))

# The #CHROM line (proof_b_adv_dec.bend's dec.write).
def write(+fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +j: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +wp: PC.WP, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed)) == True{} : Bool},
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
  +eisc: {R.is_chrom_line(B.Line.body(Norm.line(P.btext(len, t, at, (j - at : U32))))) == True{} : Bool}) ->
  S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed),
    Norm.head(True{}, o, P.mkRun(rp), Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp))):
  %Equal.sym(NR.Run & Bool, Norm.Run.head(P.mkRun(rp)), (P.mkRun(rp), Norm.len_le(P.RunP.h(rp), 268435456)), rhead_eq(rp)) :
    S.AdvG(fa, T, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, wp, asked, fneed), Norm.head.len(o, _, Norm.line(P.btext(len, t, at, (j - at : U32))), at, j, C.BT(len, t), back, Norm.Cx{P.mkSrcs(rest), P.mkPd(pd), eof}, PC.mkWin(fa, wp)))
  wr.fits(Bool.and(Bool.and(Norm.len_le(P.RunP.h(rp), 268435456), Norm.len_le(R.added(o, B.Line.term(Norm.line(P.btext(len, t, at, (j - at : U32))))), 268435456)), Norm.len_le(B.Line.text(Norm.line(P.btext(len, t, at, (j - at : U32)))), 268435456)), fa, T, cs, O, N, o, rp, len, t, d, at, j, rest, pd, eof, back, wp, asked, fneed, hb, hw, hr, hg, hi, hx, hin, hs, hn, hle, hby, hal, hlt, hinc, hsm, eisc, {==})
