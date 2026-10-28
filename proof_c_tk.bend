import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./tan.bend as V
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./bytes_enc.bend as E
import ./proof_window_defs.bend as WS
import ./proof_fast.bend as PF
import ./proof_run_base.bend as RBS
import ./proof_run_rec.bend as RRC
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import ./proof_b_cachedefs.bend as CD
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_cut.bend as CU
import ./proof_b_adv_line.bend as LI
import ./proof_b_adv_dec.bend as DE
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_wr.bend as WR
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_lines.bend as LN
import ./proof_b_cache.bend as CA
import ./proof_b_cache_hit.bend as H
import ./proof_b_enc.bend as EN
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_c_advf.bend as AF
import ./proof_c_hitl.bend as HL
import ./proof_c_tan.bend as TN
import ./proof_c_txt.bend as XT
import ./proof_c_text.bend as TX
import ./proof_c_text_w.bend as WW
import ./proof_c_judge.bend as CJ
import ./proof_c_run.bend as CR
import ./proof_c_take.bend as TK
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C: adv_ok's take, a line rewritten on its bytes (norm.bend fix.fits
# .. fix.out): the run's tick, NR.fix_done, then the source steps, as the
# String path's judge (LAWS.bend's L.judge, through proof_c_judge.bend's
# fix_res) and run.bend's body_line give. Every variable is reusable.

# Projections.
def pos0(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32, h: {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))) ->
  {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}:
  (x, y) = h
  x

def pos1(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32, h: {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))) ->
  {Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}:
  (x, y) = h
  (x2, y2) = y
  x2

def ae1(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}:
  (x, y) = h
  (x2, y2) = y
  x2

def ae4(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  (x4, y4) = y3
  (x5, y5) = y4
  x5

def inf1(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32, h: {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool})))) -> {B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  x2

def inf2(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32, h: {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool})))) -> {B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  x3

def inf3(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32, h: {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool})))) -> {B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  (x4, y4) = y3
  x4

def inf4(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32, h: {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool})))) -> {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  (x4, y4) = y3
  y4

def nv1(+len: U32, +t: AT.Tree<U32>, +r: String, +a: Nat, +b: Nat, +e2: U32, +e3: U32, +als: List<&2, NX.Ap>, +pos: U32, +k: U32, +tr: U32, +dl: Nat,
  h: {V.var_in(Q.n(U32.from_nat(Nat.min(a, String.length(r)))), Q.BF(Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos)) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>}
  & {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl) == True{} : Bool}) ->
  {V.var_in(Q.n(U32.from_nat(Nat.min(a, String.length(r)))), Q.BF(Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos)) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>}:
  (x, y) = h
  x

# The record unchanged in its variant would be the line itself.
def hns.k(+body: String, +f1: String, +f3: String, +f4: String, +v: B.Var, +w: B.Var, +bb: Bool,
  +hb: {Bool.and(B.Rec.same_var(v, w), J.same.text(f1, f3, f4, v)) == bb : Bool},
  +h1: {B.Rec.field(B.Rec.fields(body), 1n) == f1 : String},
  +h3: {B.Rec.field(B.Rec.fields(body), 3n) == f3 : String},
  +h4: {B.Rec.field(B.Rec.fields(body), 4n) == f4 : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(body), v, w), body) == False{} : Bool}) ->
  {bb == False{} : Bool}:
  match v bb:
    case B.Var{+p, +rr, +x} False{}:
      {==}
    case B.Var{+p, +rr, +x} True{}:
      +hsv = N.and_true_l(B.Rec.same_var(B.Var{p, rr, x}, w), J.same.text(f1, f3, f4, B.Var{p, rr, x}), hb)
      +hst = N.and_true_r(B.Rec.same_var(B.Var{p, rr, x}, w), J.same.text(f1, f3, f4, B.Var{p, rr, x}), hb)
      +hW = PF.same_var_sound(B.Var{p, rr, x}, w, hsv)
      +F = B.Rec.fields(body)
      +htx = {%Equal.sym(String, B.Rec.field(F, 1n), f1, h1) : {J.same.text(_, B.Rec.field(F, 3n), B.Rec.field(F, 4n), B.Var{p, rr, x}) == True{} : Bool};
        %Equal.sym(String, B.Rec.field(F, 3n), f3, h3) : {J.same.text(f1, _, B.Rec.field(F, 4n), B.Var{p, rr, x}) == True{} : Bool};
        %Equal.sym(String, B.Rec.field(F, 4n), f4, h4) : {J.same.text(f1, f3, _, B.Var{p, rr, x}) == True{} : Bool};
        hst : {J.same.text(B.Rec.field(F, 1n), B.Rec.field(F, 3n), B.Rec.field(F, 4n), B.Var{p, rr, x}) == True{} : Bool}}
      +hrb = PF.rebuild_same(F, p, rr, x, body, RRC.join_split(body, '\t'), htx)
      +hT = {%Equal.sym(B.Var, w, B.Var{p, rr, x}, hW) : {String.eq(B.Rec.rebuild(F, B.Var{p, rr, x}, _), body) == True{} : Bool};
        %Equal.sym(String, B.Rec.rebuild(F, B.Var{p, rr, x}, B.Var{p, rr, x}), body, hrb) : {String.eq(_, body) == True{} : Bool};
        RBS.str_eq_refl(body) : {String.eq(B.Rec.rebuild(F, B.Var{p, rr, x}, w), body) == True{} : Bool}}
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, String.eq(B.Rec.rebuild(F, B.Var{p, rr, x}, w), body), True{}, Equal.sym(Bool, String.eq(B.Rec.rebuild(F, B.Var{p, rr, x}, w), body), False{}, hne), hT)))

# No reserved key in INFO: not stale.
def hst.k(+sv: Bool, +fs: List<&2, String>,
  +h2: {B.Info.has(B.Rec.field(fs, 7n), "CIGAR") == False{} : Bool},
  +h3: {B.Info.has(B.Rec.field(fs, 7n), "HOMLEN") == False{} : Bool},
  +h4: {B.Info.has(B.Rec.field(fs, 7n), "HOMSEQ") == False{} : Bool},
  +h5: {B.Info.has(B.Rec.field(fs, 7n), "AA") == False{} : Bool}) ->
  {B.Rec.stale.if(sv, fs) == False{} : Bool}:
  match sv:
    case True{}:
      {==}
    case False{}:
      +I = B.Rec.field(fs, 7n)
      %Equal.sym(Bool, B.Info.has(I, "CIGAR"), False{}, h2) : {Bool.or(Bool.or(Bool.or(_, B.Info.has(I, "HOMLEN")), B.Info.has(I, "HOMSEQ")), B.Info.has(I, "AA")) == False{} : Bool}
      %Equal.sym(Bool, B.Info.has(I, "HOMLEN"), False{}, h3) : {Bool.or(Bool.or(Bool.or(False{}, _), B.Info.has(I, "HOMSEQ")), B.Info.has(I, "AA")) == False{} : Bool}
      %Equal.sym(Bool, B.Info.has(I, "HOMSEQ"), False{}, h4) : {Bool.or(Bool.or(Bool.or(False{}, False{}), _), B.Info.has(I, "AA")) == False{} : Bool}
      %Equal.sym(Bool, B.Info.has(I, "AA"), False{}, h5) : {Bool.or(Bool.or(Bool.or(False{}, False{}), False{}), _) == False{} : Bool}
      {==}

def hsm_lt(+x: U32, +h: {U32.is_le(x, 268435456) == True{} : Bool}) -> {U32.is_lt(268435456, x) == False{} : Bool}:
  +hn = Equal.trans(Bool, Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)), U32.is_le(x, 268435456), True{}, Equal.sym(Bool, U32.is_le(x, 268435456), Nat.is_le(U32.to_nat(x), U32.to_nat(268435456)), U.is_le_to_nat(x, 268435456)), h)
  %Equal.sym(Bool, U32.is_lt(268435456, x), Nat.is_lt(U32.to_nat(268435456), U32.to_nat(x)), U.is_lt_to_nat(268435456, x)) : {_ == False{} : Bool}
  N.le_not_lt(U32.to_nat(x), U32.to_nat(268435456), hn)

# REF's text, as the String path cuts it.
def f3eq(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Norm.chars(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))) == CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)) : String}:
  +hinc2 = LP.inc_len(len, t, d, e2, hok, TK.e2len(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +h3 = {%Equal.sym(Nat, U32.to_nat((e2 + 1 : U32)), Nat.add(U32.to_nat(e2), 1n), hinc2) : {Nat.is_le(_, U32.to_nat(e3)) == True{} : Bool}; C.succ_le(U32.to_nat(e2), U32.to_nat(e3), PJ.lf_23(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) : {Nat.is_le(U32.to_nat((e2 + 1 : U32)), U32.to_nat(e3)) == True{} : Bool}}
  %Equal.sym(Nat, U32.to_nat(AF.RL(e2, e3)), Nat.sub(U32.to_nat(e3), U32.to_nat((e2 + 1 : U32))), LP.sub_u(e3, (e2 + 1 : U32), h3)) :
    {Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), _)) == CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)) : String}
  %Equal.sym(Nat, U32.to_nat((e2 + 1 : U32)), Nat.add(U32.to_nat(e2), 1n), hinc2) :
    {Norm.chars(D.slice(D.view(C.BT(len, t)), _, Nat.sub(U32.to_nat(e3), _))) == CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)) : String}
  {==}

def wview(+r: String, +a: Nat, +b: Nat, h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}))) ->
  {D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}:
  (x, y) = h
  (x2, y2) = y
  x2

# The counters keep the shifts inside the window (NX.norm's facts).
def kok_w(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +r: String, +a: Nat, +b: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>}) ->
  {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl) == True{} : Bool}:
  TK.nv2(len, t, r, a, b, e2, e3, als, pos, k, tr, dl, TN.norm_var(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), E.depth(String.length(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl, hok, TK.wok(r, a, b, TK.wenc(r, a, b, hbr, hfs)), TK.ain(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), N.le_zero_l(List.length(&2, NX.Ap, Q.TL(als))), TK.wo1(r, a, b, pos, hfs, TK.pos2(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), TK.rc1(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc))), TK.wo2(r, a, b, pos, hfs, List.length(&2, B.Base, Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))), TK.rc2(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc)), TK.wlen(r, a, b, TK.wenc(r, a, b, hbr, hfs))), hz))

# The new POS as the code computes it is VW's.
def qq_k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up), +offu: U32, +k: U32, +tr: U32, +dl: Nat,
  +hk: {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, offu, k, tr, dl) == True{} : Bool}) ->
  {U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)) == Nat.add(Nat.sub(U32.to_nat(pos), U32.to_nat(k)), dl) : Nat}:
  +hk1 = N.and_true_l(Nat.is_le(Nat.add(Nat.add(U32.to_nat(k), U32.to_nat(offu)), 1n), U32.to_nat(pos)), Q.KL(PE.REF(e2, e3) <> Q.TL(als), tr, dl), hk)
  +hkl = N.and_true_r(Nat.is_le(Nat.add(Nat.add(U32.to_nat(k), U32.to_nat(offu)), 1n), U32.to_nat(pos)), Q.KL(PE.REF(e2, e3) <> Q.TL(als), tr, dl), hk)
  +hl = N.and_true_l(Nat.is_lt(Nat.add(U32.to_nat(tr), dl), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Q.KL(Q.TL(als), tr, dl), hkl)
  +hain = TK.ain(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)
  +hin1 = N.and_true_r(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len)), N.and_true_l(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain))
  +hd = N.lt_le_trans(dl, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), U32.to_nat(len), N.le_lt_trans(dl, Nat.add(U32.to_nat(tr), dl), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), N.le_add_l(dl, U32.to_nat(tr)), hl),
    N.le_trans(U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len), N.le_add_l(U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), U32.to_nat(NX.Ap.st(PE.REF(e2, e3)))), hin1))
  XT.qq_pos(len, t, d, pos, offu, k, dl, hok, hk1, TK.pos3(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), hd)

# The String path's judge of the line: the rewrite to NX.norm's variant.
def jres(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +fa: List<&2, B.Contig>, +c: String,
  +r: String, +a: Nat, +b: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hc0: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool}) ->
  {L.judge(fa, CU.lbody(D.view(C.BT(len, t)), at, lf)) == CJ.RW(Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), CU.lbody(D.view(C.BT(len, t)), at, lf)) : B.Res}:
  +hbf = Equal.trans(List<&2, B.Base>, Q.BF(Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))), Q.BF(E.codes(CD.letters(r, a, b))), B.Bases.of_fasta(CD.letters(r, a, b)),
    Equal.cong(List<&2, U32>, List<&2, B.Base>, z => Q.BF(z), D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))), E.codes(CD.letters(r, a, b)), wview(r, a, b, TK.wenc(r, a, b, hbr, hfs))), HL.bf_codes(CD.letters(r, a, b)))
  +hv = {%H.f31_eq(Nat.min(a, String.length(r)), N.and_true_l(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfs)) : {V.var_in(_, B.Bases.of_fasta(CD.letters(r, a, b)), B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>};
    %hbf : {V.var_in(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), _, B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>};
    nv1(len, t, r, a, b, e2, e3, als, pos, k, tr, dl, TN.norm_var(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), E.depth(String.length(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl, hok, TK.wok(r, a, b, TK.wenc(r, a, b, hbr, hfs)), TK.ain(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), N.le_zero_l(List.length(&2, NX.Ap, Q.TL(als))), TK.wo1(r, a, b, pos, hfs, TK.pos2(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), TK.rc1(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc))), TK.wo2(r, a, b, pos, hfs, List.length(&2, B.Base, Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))), TK.rc2(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc)), TK.wlen(r, a, b, TK.wenc(r, a, b, hbr, hfs))), hz)) : {V.var_in(Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>}}
  +hdist = AB.subst(List<&2, NX.Ap>, z => {B.Alleles.distinct(Q.BFS(Q.xs(len, t), z)) == True{} : Bool}, als, PE.REF(e2, e3) <> Q.TL(als), TK.ae0(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), ae4(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hain = TK.ain(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)
  +hA1 = N.and_true_l(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len)), N.and_true_l(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain))
  +hA2 = N.and_true_r(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len)), N.and_true_l(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain))
  +hat = N.and_true_r(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain)
  +hlX = {%LP.len_x(len, t, d, hok) : {Nat.is_le(U32.to_nat(len), _) == True{} : Bool}; N.le_refl(U32.to_nat(len)) : {Nat.is_le(U32.to_nat(len), List.length(&2, U32, D.view(C.BT(len, t)))) == True{} : Bool}}
  +hLT = N.and_true_r(Q.lets(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.ALS_L(D.view(C.BT(len, t)), Q.TL(als)), AF.af.l(len, t, e2, e3, lf, als, AF.alsf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hrl = AF.reflets(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)
  +hsl1 = HL.sl_ne(D.view(C.BT(len, t)), len, PE.REF(e2, e3), hA1, hA2, hlX)
  +hr = {%f3eq(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp) : {B.Allele.read(_) == Some{Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3)))} : Maybe<&2, List<&2, B.Base>>}; PE.read_bf(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3)), hrl) : {B.Allele.read(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3))) == Some{Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3)))} : Maybe<&2, List<&2, B.Base>>}}
  +hl = {%f3eq(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp) : {B.Text.is_letters(_) == True{} : Bool}; HL.lets_letters(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3)), hrl, hsl1) : {B.Text.is_letters(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3))) == True{} : Bool}}
  +hsp = ae1(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +ha = {%Equal.sym(List<&2, String>, String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ','), Q.STRS(D.view(C.BT(len, t)), Q.TL(als)), hsp) : {B.Alleles.read(_) == Some{Q.BFS(D.view(C.BT(len, t)), Q.TL(als))} : Maybe<&2, List<&2, List<&2, B.Base>>>};
    HL.read_strs(D.view(C.BT(len, t)), Q.TL(als), hLT) : {B.Alleles.read(String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ',')) == Some{Q.BFS(D.view(C.BT(len, t)), Q.TL(als))} : Maybe<&2, List<&2, List<&2, B.Base>>>}}
  +he = {%Equal.sym(List<&2, String>, String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ','), Q.STRS(D.view(C.BT(len, t)), Q.TL(als)), hsp) : {B.Text.any_empty(_) == False{} : Bool};
    HL.strs_ne(D.view(C.BT(len, t)), len, Q.TL(als), hat, hlX) : {B.Text.any_empty(String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ',')) == False{} : Bool}}
  +hn = {%Equal.sym(List<&2, String>, String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ','), Q.STRS(D.view(C.BT(len, t)), Q.TL(als)), hsp) : {B.Text.any_not_letters(_) == False{} : Bool};
    HL.strs_letters(D.view(C.BT(len, t)), len, Q.TL(als), hat, hlX, hLT) : {B.Text.any_not_letters(String.split(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), ',')) == False{} : Bool}}
  +hF1 = Equal.trans(String, B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 1n), B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 1n), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), Equal.sym(String, B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 1n), B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 1n), PF.pfs_field(CU.lbody(D.view(C.BT(len, t)), at, lf), 1n, {==})), Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 1n), J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hF3 = Equal.trans(String, B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 3n), B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 3n), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), Equal.sym(String, B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 3n), B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 3n), PF.pfs_field(CU.lbody(D.view(C.BT(len, t)), at, lf), 3n, {==})), Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 3n), J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hF4 = Equal.trans(String, B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 4n), B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 4n), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), Equal.sym(String, B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 4n), B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), 4n), PF.pfs_field(CU.lbody(D.view(C.BT(len, t)), at, lf), 4n, {==})), Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 4n), J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hneB = {%FH.btext_fld(len, t, at, lf, TK.slf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)) : {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(_))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(_))) == False{} : Bool};
    hne : {String.eq(B.Rec.rebuild(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}, Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), CU.lbody(D.view(C.BT(len, t)), at, lf)) == False{} : Bool}}
  +hns = hns.k(CU.lbody(D.view(C.BT(len, t)), at, lf), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}, Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl), Bool.and(B.Rec.same_var(B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}, Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), J.same.text(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))})), {==}, hF1, hF3, hF4, hneB)
  +hst = hst.k(B.Rec.same_var(B.Var{U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als))}, Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), inf1(len, t, at, lf, PE.fix_info(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), inf2(len, t, at, lf, PE.fix_info(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), inf3(len, t, at, lf, PE.fix_info(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), inf4(len, t, at, lf, PE.fix_info(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hs0 = PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +hch = Equal.trans(String, c, CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), WS.chrom_of(CU.lbody(D.view(C.BT(len, t)), at, lf)),
    Equal.trans(String, c, P.btext(len, t, at, (e0 - at : U32)), CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), Equal.sym(String, P.btext(len, t, at, (e0 - at : U32)), c, hc0), FH.btext_fld(len, t, at, e0, hs0)),
    Equal.trans(String, CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), 0n), WS.chrom_of(CU.lbody(D.view(C.BT(len, t)), at, lf)),
      Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), Equal.sym(List<&2, String>, J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))),
      PF.pfs_field(CU.lbody(D.view(C.BT(len, t)), at, lf), 0n, {==})))
  +ht = {%hch : {WS.truthful(fa, _, Some{J.Known{String.length(r), Nat.min(a, String.length(r)), CD.letters(r, a, b)}}) == True{} : Bool};
    %hf : {WS.truthful(fa, c, Some{CD.jtruth.k(_, a, b)}) == True{} : Bool};
    CA.jtruth_ok(fa, c, a, b) : {WS.truthful(fa, WS.chrom_of(CU.lbody(D.view(C.BT(len, t)), at, lf)), Some{J.Known{String.length(r), Nat.min(a, String.length(r)), CD.letters(r, a, b)}}) == True{} : Bool}}
  +hlt0 = {%U.is_lt_to_nat(at, e0) : {_ == True{} : Bool}; hse : {Nat.is_lt(U32.to_nat(at), U32.to_nat(e0)) == True{} : Bool}}
  +h0l = N.lt_to_le(U32.to_nat(e0), U32.to_nat(len), TK.e0len(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +h0 = FH.ne_chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at))),
    %Equal.sym(Nat, List.length(&2, U32, D.slice(D.view(C.BT(len, t)), U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at)))), Nat.sub(U32.to_nat(e0), U32.to_nat(at)), LP.slice_len(D.view(C.BT(len, t)), U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at)),
      %Equal.sym(Nat, Nat.add(U32.to_nat(at), Nat.sub(U32.to_nat(e0), U32.to_nat(at))), U32.to_nat(e0), N.le_sub_add(U32.to_nat(at), U32.to_nat(e0), hs0)) : {Nat.is_le(_, List.length(&2, U32, D.view(C.BT(len, t)))) == True{} : Bool};
      %LP.len_x(len, t, d, hok) : {Nat.is_le(U32.to_nat(e0), _) == True{} : Bool};
      h0l)) : {Nat.is_lt(0n, _) == True{} : Bool};
    LP.pos_sub(U32.to_nat(at), U32.to_nat(e0), hlt0))
  CJ.fix_res(fa, CU.lbody(D.view(C.BT(len, t)), at, lf), CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), U32.to_nat(pos), Q.BF(Q.SL(D.view(C.BT(len, t)), PE.REF(e2, e3))), Q.BFS(D.view(C.BT(len, t)), Q.TL(als)), String.length(r), Nat.min(a, String.length(r)), CD.letters(r, a, b), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl),
    PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), h0, pos0(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), TK.pos2(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), hr, ha, hl, he, hn, hdist, hv, hrc, hns, hst, ht)

# ---------------------------------------------------------------------------
# The take
# ---------------------------------------------------------------------------

# The run's step and the source's: SL.went, the judge being the rewrite.
def take.w(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +rp1: P.RunP, +rp2: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  +i2: {PR.RunInv(rp2) == True{} : Bool},
  +sp2: {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), B.At{P.RunP.n(rp1), P.btext(len, t, at, (e0 - at : U32)), Nat.show(U32.to_nat(pos))}, U32.to_nat(pos))) : R.RunSt},
  sx: LI.SPLIT(len, t, d, at, lf) & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool} & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool} & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}))) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.Went{Norm.St{o, Norm.MB{P.mkRun(rp2)}, Con{Norm.SB{C.BT(len, t), (lf + 1 : U32)}, P.mkSrcs(rest)}, P.mkPd(pd), eof, 0n, CD.mkWin(fa, CD.WPKnown{c, a, b}), None{}, False{}}}):
  match sx:
    case (hsp, q):
      match q:
        case (hn, q2):
          match q2:
            case (hle, hby):
              +jb = {%Equal.sym(String, P.btext(len, t, at, (lf - at : U32)), CU.ltext(D.view(C.BT(len, t)), at, lf), FH.btext_fld(len, t, at, lf, TK.slf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
                  {L.judge(fa, B.Line.body(Norm.line(_))) == B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(_))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}} : B.Res};
                %Equal.sym(Nat, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), Nat.add(Nat.sub(U32.to_nat(pos), U32.to_nat(k)), dl), qq_k(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl, kok_w(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, r, a, b, CA.find_bytes(fa, c, r, hb, hf), hrc, hfs, k, tr, dl, hz))) :
                  {L.judge(fa, CU.lbody(D.view(C.BT(len, t)), at, lf)) == B.Res{B.Normalized{}, _, B.Rec.rebuild(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), at, lf)), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}} : B.Res};
                jres(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, fa, c, r, a, b, CA.find_bytes(fa, c, r, hb, hf), hrc, hfs, k, tr, dl, hz, hf, hse, hc, hne) : {L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}} : B.Res}}
              +hrj = Equal.sym(B.Res, L.judge(fa, B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, jb)
              +sp3 = {%Equal.sym(String, P.btext(len, t, at, (lf - at : U32)), CU.ltext(D.view(C.BT(len, t)), at, lf), FH.btext_fld(len, t, at, lf, TK.slf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
                  {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(_)))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(_)))))) : R.RunSt};
                %Equal.sym(List<&2, String>, J.pfs(CU.lbody(D.view(C.BT(len, t)), at, lf)), [CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), ""], PE.fix_fields(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)) :
                  {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), Norm.at_of(P.RunP.n(rp1), _), B.Rec.pos(_))) : R.RunSt};
                %Equal.sym(Maybe<&2, Nat>, B.Pos.read(CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1))), Some{U32.to_nat(pos)}, pos0(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
                  {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), B.At{P.RunP.n(rp1), CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1))}, Maybe.default(&2, Nat, _, 0n))) : R.RunSt};
                %pos1(len, t, e0, e1, pos, PE.fix_pos(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)) :
                  {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), B.At{P.RunP.n(rp1), CU.fld(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(e0)), _}, U32.to_nat(pos))) : R.RunSt};
                %FH.btext_fld(len, t, at, e0, PJ.lf_s0(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
                  {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), B.At{P.RunP.n(rp1), _, Nat.show(U32.to_nat(pos))}, U32.to_nat(pos))) : R.RunSt};
                sp2 : {P.settle(P.specRun(rp2)) == P.settle(R.body_line(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, P.specRun(rp1), o, Norm.line(P.btext(len, t, at, (lf - at : U32))), Norm.at_of(P.RunP.n(rp1), J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32)))))), B.Rec.pos(J.pfs(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32)))))))) : R.RunSt}}
              SLW.SL.went(B.Res{B.Normalized{}, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), False{}}, fa, T, cs, O, N, o, rp, len, t, d, at, lf, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed, fneed, hb, hw, hr, hg, hi, hx, hin, hbig,
                Equal.sym(Nat, D.first(D.view(C.BT(len, t)), U32.to_nat(at), U32.to_nat(len), 10), U32.to_nat(lf), PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), hsp, hn, hle, hby, TK.slf(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)),
                LP.inc_len(len, t, d, lf, hok, PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), hsm_lt((lf - at : U32), hsm), hrj, rp1, rp2, s1, n1, hin1, i2, sp3)

# NR.fix_done's run, then the source steps.
def take.d(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +rp1: P.RunP,
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +hin1: {P.RunP.i(rp1) == True{} : Bool},
  fd: CR.FxG(rp1, o, Norm.line(P.btext(len, t, at, (lf - at : U32))), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), U32.to_nat(pos), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), P.btext(len, t, at, (e0 - at : U32)), sl, st, sl)) ->
  DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.out(o, NR.fix_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), U32.to_nat(pos), C.BT(sl, st), sl), lf, C.BT(len, t), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  match fd:
    case (+rp2, q):
      match q:
        case (efd, q2):
          match q2:
            case (i2, sp2):
              %Equal.sym(NR.Run & D.Bytes, NR.fix_done(P.mkRun(rp1), R.Opts.w(o), P.RunP.n(rp1), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), U32.to_nat(pos), C.BT(sl, st), sl), (P.mkRun(rp2), C.BT(sl, st)), efd) :
                DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.out(o, _, lf, C.BT(len, t), DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}))
              %Equal.sym(Norm.Win, Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}, CD.mkWin(fa, CD.WPKnown{c, a, b}), emk) :
                DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.done.b(o, (P.mkRun(rp2), C.BT(len, t)), (lf + 1 : U32), DE.CX(rest, pd, eof), _))
              take.w(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef, rp1, rp2, s1, n1, hin1, i2, sp2, LN.src_line(len, t, d, at, lf, hok, hs, PJ.lf_first(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_lt(len, t, at, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))

# After the run's tick (rp1).
def take.t(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  +rp1: P.RunP,
  +et: {NR.tick(P.mkRun(rp)) == P.mkRun(rp1) : NR.Run},
  +i1: {PR.RunInv(rp1) == True{} : Bool},
  +s1: {P.specRun(rp1) == R.tick(P.specRun(rp)) : R.RunSt},
  +n1: {P.RunP.n(rp1) == 1n+P.RunP.n(rp) : Nat},
  +obl1: {P.RunP.obl(rp1) == P.RunP.obl(rp) : U32}) ->
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.fits(True{}, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  +hin1 = Equal.trans(Bool, P.RunP.i(rp1), P.RunP.i(rp), True{}, WR.tk_i(rp, rp1, s1), hin)
  +hx1 = Equal.trans(Bool, P.RunP.x(rp1), P.RunP.x(rp), False{}, WR.tk_x(rp, rp1, s1), hx)
  +hc1 = Equal.trans(Maybe<&2, String>, P.RunP.c(rp1), P.RunP.c(rp), Some{P.btext(len, t, at, (e0 - at : U32))}, FH.c_tick(rp, rp1, s1), hcr)
  +hfit1 = {%Equal.sym(U32, P.RunP.obl(rp1), P.RunP.obl(rp), obl1) : {U32.is_le(sl, (1073741824 - _ : U32)) == True{} : Bool}; ef : {U32.is_le(sl, (1073741824 - P.RunP.obl(rp1) : U32)) == True{} : Bool}}
  +ht = {%Equal.sym(List<&2, U32>, D.slice(D.view(C.BT(sl, st)), U32.to_nat(0), U32.to_nat(sl)), D.view(C.BT(sl, st)), BF.view_all(sl, st, RD.tdepth(st), okw)) : {NR.chars(_) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.term(Norm.line(P.btext(len, t, at, (lf - at : U32))))) : String};
    TK.hpk_w(len, t, d, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, r, a, b, CA.find_bytes(fa, c, r, hb, hf), hrc, hfs, k, tr, dl, hz, sl, st, pk) : {P.btext(sl, st, 0, sl) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.term(Norm.line(P.btext(len, t, at, (lf - at : U32))))) : String}}
  %Equal.sym(NR.Run, NR.tick(P.mkRun(rp)), P.mkRun(rp1), et) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.tick(o, NR.Run.n(_), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}))
  %Equal.sym(NR.Run & Nat, NR.Run.n(P.mkRun(rp1)), (P.mkRun(rp1), P.RunP.n(rp1)), FH.runn_eq(rp1)) :
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.tick(o, _, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)}))
  take.d(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef, rp1, s1, n1, hin1,
    CR.run_fix_done(rp1, o, Norm.line(P.btext(len, t, at, (lf - at : U32))), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), U32.to_nat(pos), B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), P.btext(len, t, at, (e0 - at : U32)), sl, st, RD.tdepth(st), sl, i1, hin1, hx1, okw, N.le_refl(U32.to_nat(sl)), ht, hne, hc1, hfit1))

def take.k(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool},
  tk: WR.TKW(rp)) ->
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.fits(True{}, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  match tk:
    case (+rp1, q):
      match q:
        case (et, q2):
          match q2:
            case (i1, q3):
              match q3:
                case (s1, q4):
                  match q4:
                    case (n1, q5):
                      match q5:
                        case (obl1, ow1):
                          take.t(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef, rp1, et, i1, s1, n1, obl1)

# The take: the line rewritten on its bytes goes out (a body line of the
# String path's run, with the judge's rewrite).
def take(+c: String, +a: Nat, +b: Nat, +r: String, +fa: List<&2, B.Contig>, +T: R.Report, +cs: List<&2, String>, +O: String, +N: List<&2, B.Note>,
  +o: B.Opts, +rp: P.RunP, +len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +rest: List<&2, P.SrcP>, +pd: P.PdP, +eof: Bool, +back: Nat, +asked: Maybe<&2, List<&2, Pr.Req>>, +fneed: Bool,
  +hb: {CD.fa_bytes(fa) == True{} : Bool},
  +hw: {S.WF(fa, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hr: {S.report(fa, cs, O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == T : R.Report},
  +hg: {S.guard(O, N, LI.PPs(o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed)) == True{} : Bool},
  +hx: {P.RunP.x(rp) == False{} : Bool},
  +hbig: {U32.is_le(536870912, P.RunP.obl(rp)) == False{} : Bool},
  +hin: {P.RunP.i(rp) == True{} : Bool},
  +hi: {PR.RunInv(rp) == True{} : Bool},
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(at, len) == True{} : Bool},
  +pos: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hp: AF.FXP(len, t, at, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +hse: {U32.is_lt(at, e0) == True{} : Bool},
  +hcr: {P.RunP.c(rp) == Some{P.btext(len, t, at, (e0 - at : U32))} : Maybe<&2, String>},
  +hsm: {U32.is_le((lf - at : U32), 268435456) == True{} : Bool},
  +hf: {B.Fasta.find(fa, c) == Some{r} : Maybe<&2, String>},
  +hc: {P.btext(len, t, at, (e0 - at : U32)) == c : String},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +cbl: U32, +cbt: AT.Tree<U32>,
  +emk: {Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)} == CD.mkWin(fa, CD.WPKnown{c, a, b}) : Norm.Win},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), at, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String},
  +hne: {String.eq(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.body(Norm.line(P.btext(len, t, at, (lf - at : U32))))) == False{} : Bool},
  +ef: {U32.is_le(sl, (1073741824 - P.RunP.obl(rp) : U32)) == True{} : Bool}) ->
    DE.DG(fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, CD.WPKnown{c, a, b}, asked, fneed,
    Norm.fix.fits(True{}, back, o, P.mkRun(rp), U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), pos, at, lf, C.BT(len, t), C.BT(sl, st), sl, DE.CX(rest, pd, eof), Norm.WKnown{c, C.BT(cbl, cbt), a, b, String.length(r), Nat.min(a, String.length(r)), C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), U32.from_nat(Nat.min(a, String.length(r))), U32.from_nat(String.length(CD.letters(r, a, b))), Bool.pick(U32, Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))), U32.from_nat(String.length(r)), 0)})):
  take.k(c, a, b, r, fa, T, cs, O, N, o, rp, len, t, d, at, rest, pd, eof, back, asked, fneed, hb, hw, hr, hg, hx, hbig, hin, hi, hok, hs, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hp, hse, hcr, hsm, hf, hc, hrc, hfs, cbl, cbt, emk, k, tr, dl, hz, sl, st, okw, pk, hne, ef, PR.run_tick(rp, hi))
