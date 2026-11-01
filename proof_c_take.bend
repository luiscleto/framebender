import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm_fix.bend as NX
import ./norm_line.bend as J
import ./proof_b_defs.bend as P
import ./proof_b_cut.bend as CU
import ./proof_b_adv_proj.bend as PJ
import ./proof_b_adv_nat.bend as LP
import ./proof_b_adv_hit.bend as FH
import ./proof_b_adv_line.bend as LI
import ./proof_b_lines_str.bend as LSS
import ./proof_b_alleles_loop.bend as ALP
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_buf.bend as BF
import ./proof_b_bud_z4k.bend as Z
import ./proof_run_base.bend as RBS
import ./proof_fast.bend as PF
import ./proof_c_defs.bend as Q
import ./proof_c_pre.bend as PE
import ./proof_c_pre_als.bend as PA
import ./proof_c_advf.bend as AF
import ./proof_c_text.bend as TX
import ./proof_c_text_w.bend as WW
import ./proof_c_text_s.bend as TS
import ./proof_c_text_l.bend as TXL
import ./proof_c_txt.bend as XT
import ./proof_c_tan.bend as TN
import ./proof_c_hitl.bend as HL
import ./tan.bend as V
import ./bytes_enc.bend as E
import ./proof_b_cachedefs.bend as CD
import ./proof_b_cache.bend as CA
import ./proof_b_enc.bend as EN
import ./proof_b_cache_hit.bend as H
import ./proof_b_cache_lem.bend as XL
import ./proof_window_lists.bend as WL
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_list.bend as BL
import lawful-bytes@0.1.1.0/proof_same.bend as SMB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# Phase C: the bytes norm_fix.bend writes for a rewritten line are the
# String path's text for it (B.Rec.rebuild of the line's fields for the
# normalized variant, then the line's terminator); and when the new line's
# length or bytes differ from the line's, the new body is not the old one.
# Every variable is reusable.

def e4lf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_lt(U32.to_nat(e4), U32.to_nat(lf)) == True{} : Bool}:
  N.lt_le_trans(U32.to_nat(e4), U32.to_nat(e7), U32.to_nat(lf), N.lt_trans(U32.to_nat(e4), U32.to_nat(e5), U32.to_nat(e7), PJ.lf_45(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e5), U32.to_nat(e6), U32.to_nat(e7), PJ.lf_56(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_67(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))), PJ.lf_7l(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def e24(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_lt(U32.to_nat(e2), U32.to_nat(e4)) == True{} : Bool}:
  N.lt_trans(U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def e04(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_lt(U32.to_nat(e0), U32.to_nat(e4)) == True{} : Bool}:
  N.lt_trans(U32.to_nat(e0), U32.to_nat(e1), U32.to_nat(e4), PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_trans(U32.to_nat(e1), U32.to_nat(e2), U32.to_nat(e4), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), e24(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

def e0len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_lt(U32.to_nat(e0), U32.to_nat(len)) == True{} : Bool}:
  N.lt_le_trans(U32.to_nat(e0), U32.to_nat(e4), U32.to_nat(len), e04(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), AF.e4le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

def e2len(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_lt(U32.to_nat(e2), U32.to_nat(len)) == True{} : Bool}:
  N.lt_le_trans(U32.to_nat(e2), U32.to_nat(e4), U32.to_nat(len), e24(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), AF.e4le(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))

def slf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(U32.to_nat(s), U32.to_nat(lf)) == True{} : Bool}:
  N.le_trans(U32.to_nat(s), U32.to_nat(e0), U32.to_nat(lf), PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_to_le(U32.to_nat(e0), U32.to_nat(lf), N.lt_trans(U32.to_nat(e0), U32.to_nat(e4), U32.to_nat(lf), e04(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), e4lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))

# The line's LF.
def hlf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {List.get(&2, U32, D.view(C.BT(len, t)), U32.to_nat(lf)) == Some{10} : Maybe<&2, U32>}:
  ALP.has_get(D.view(C.BT(len, t)), U32.to_nat(lf), 10,
    %Equal.sym(Nat, U32.to_nat(lf), D.first(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(len), 10), Equal.sym(Nat, D.first(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(len), 10), U32.to_nat(lf), PJ.lf_first(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))) : {D.has(D.view(C.BT(len, t)), _, 10) == True{} : Bool};
    BL.first_hit(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(len), 10, LI.u2n(s, len, hs), %LP.len_x(len, t, d, hok) : {Nat.is_le(U32.to_nat(len), _) == True{} : Bool}; N.le_refl(U32.to_nat(len)),
      %Equal.sym(Nat, D.first(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(len), 10), U32.to_nat(lf), PJ.lf_first(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) : {Nat.is_lt(_, U32.to_nat(len)) == True{} : Bool}; PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))

# Bytes a .. e as the writer slices them (e + 1 - a of them, from a).
def pc(+len: U32, +t: AT.Tree<U32>, +d: Nat, +a: U32, +e: U32,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hae: {Nat.is_le(U32.to_nat(a), U32.to_nat(e)) == True{} : Bool},
  +hel: {Nat.is_lt(U32.to_nat(e), U32.to_nat(len)) == True{} : Bool}) ->
  {NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), U32.to_nat(((e + 1 : U32) - a : U32)))) == CU.fld(D.view(C.BT(len, t)), U32.to_nat(a), Nat.add(U32.to_nat(e), 1n)) : String}:
  +hinc = LP.inc_len(len, t, d, e, hok, hel)
  +ha1 = {%Equal.sym(Nat, U32.to_nat((e + 1 : U32)), Nat.add(U32.to_nat(e), 1n), hinc) : {Nat.is_le(U32.to_nat(a), _) == True{} : Bool}; N.le_trans(U32.to_nat(a), U32.to_nat(e), Nat.add(U32.to_nat(e), 1n), hae, N.le_add_r(U32.to_nat(e), 1n)) : {Nat.is_le(U32.to_nat(a), U32.to_nat((e + 1 : U32))) == True{} : Bool}}
  %Equal.sym(Nat, U32.to_nat(((e + 1 : U32) - a : U32)), Nat.sub(U32.to_nat((e + 1 : U32)), U32.to_nat(a)), LP.sub_u((e + 1 : U32), a, ha1)) :
    {NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), _)) == CU.fld(D.view(C.BT(len, t)), U32.to_nat(a), Nat.add(U32.to_nat(e), 1n)) : String}
  %Equal.sym(Nat, U32.to_nat((e + 1 : U32)), Nat.add(U32.to_nat(e), 1n), hinc) :
    {NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), Nat.sub(_, U32.to_nat(a)))) == CU.fld(D.view(C.BT(len, t)), U32.to_nat(a), Nat.add(U32.to_nat(e), 1n)) : String}
  Equal.sym(String, Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), Nat.sub(Nat.add(U32.to_nat(e), 1n), U32.to_nat(a)))), NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), Nat.sub(Nat.add(U32.to_nat(e), 1n), U32.to_nat(a)))), LSS.chars_norm(D.slice(D.view(C.BT(len, t)), U32.to_nat(a), Nat.sub(Nat.add(U32.to_nat(e), 1n), U32.to_nat(a)))))

def ltx(l: B.Line) -> {B.Line.text(l) == String.append(B.Line.body(l), B.Line.term(l)) : String}:
  match l:
    case B.Line{+b, +tm}:
      {==}

# The fields of a body whose first seven are g0 .. g6 (J.pfs, INFO kept as
# g7): g0 .. g4, field 5, and the rest.
def fsg(g: J.C7, +body: String, +g0: String, +g1: String, +g2: String, +g3: String, +g4: String, +g5: String, +g6: String, +g7: String,
  +hg: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>},
  +hp: {J.pfs.g(g, body) == [g0, g1, g2, g3, g4, g5, g6, g7] : List<&2, String>}) ->
  {B.Rec.fields(body) == TS.L7(g0, g1, g2, g3, g4, B.Rec.field(B.Rec.fields(body), 5n), List.drop(&2, String, B.Rec.fields(body), 6n)) : List<&2, String>}:
  match g:
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      +T = String.split(r, '\t')
      +PG = {[f0, f1, f2, f3, f4, f5, f6, J.info.if(J.noend(r), r)] : List<&2, String>}
      +GG = {[g0, g1, g2, g3, g4, g5, g6, g7] : List<&2, String>}
      +h0 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), PG, GG, hp)
      +h1 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 1n), PG, GG, hp)
      +h2 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 2n), PG, GG, hp)
      +h3 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 3n), PG, GG, hp)
      +h4 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 4n), PG, GG, hp)
      %hg : {_ == TS.L7(g0, g1, g2, g3, g4, B.Rec.field(_, 5n), List.drop(&2, String, _, 6n)) : List<&2, String>}
      %Equal.sym(String, f0, g0, h0) : {_ <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> T == g0 <> g1 <> g2 <> g3 <> g4 <> f5 <> f6 <> T : List<&2, String>}
      %Equal.sym(String, f1, g1, h1) : {g0 <> _ <> f2 <> f3 <> f4 <> f5 <> f6 <> T == g0 <> g1 <> g2 <> g3 <> g4 <> f5 <> f6 <> T : List<&2, String>}
      %Equal.sym(String, f2, g2, h2) : {g0 <> g1 <> _ <> f3 <> f4 <> f5 <> f6 <> T == g0 <> g1 <> g2 <> g3 <> g4 <> f5 <> f6 <> T : List<&2, String>}
      %Equal.sym(String, f3, g3, h3) : {g0 <> g1 <> g2 <> _ <> f4 <> f5 <> f6 <> T == g0 <> g1 <> g2 <> g3 <> g4 <> f5 <> f6 <> T : List<&2, String>}
      %Equal.sym(String, f4, g4, h4) : {g0 <> g1 <> g2 <> g3 <> _ <> f5 <> f6 <> T == g0 <> g1 <> g2 <> g3 <> g4 <> f5 <> f6 <> T : List<&2, String>}
      {==}
    case J.Short{}:
      %Equal.sym(List<&2, String>, B.Rec.fields(body), [g0, g1, g2, g3, g4, g5, g6, g7], hp) : {_ == TS.L7(g0, g1, g2, g3, g4, B.Rec.field(_, 5n), List.drop(&2, String, _, 6n)) : List<&2, String>}
      {==}

def fs_shape(+body: String, +g0: String, +g1: String, +g2: String, +g3: String, +g4: String, +g5: String, +g6: String, +g7: String,
  +hp: {J.pfs(body) == [g0, g1, g2, g3, g4, g5, g6, g7] : List<&2, String>}) ->
  {B.Rec.fields(body) == TS.L7(g0, g1, g2, g3, g4, B.Rec.field(B.Rec.fields(body), 5n), List.drop(&2, String, B.Rec.fields(body), 6n)) : List<&2, String>}:
  fsg(J.c7(body), body, g0, g1, g2, g3, g4, g5, g6, g7, PF.c7_split(body), hp)

# Projections of proof_c_pre.bend's conjunctions.
def tb0(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, h: {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}
  & {List.get(&2, U32, Q.xs(len, t), Q.n(e4)) == Some{9} : Maybe<&2, U32>})))) -> {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}:
  (a, r) = h
  a

def tb1(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, h: {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}
  & {List.get(&2, U32, Q.xs(len, t), Q.n(e4)) == Some{9} : Maybe<&2, U32>})))) -> {List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}:
  (a, r) = h
  (b, r2) = r
  b

def tb2(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, h: {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}
  & {List.get(&2, U32, Q.xs(len, t), Q.n(e4)) == Some{9} : Maybe<&2, U32>})))) -> {List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}:
  (a, r) = h
  (b, r2) = r
  (c, r3) = r2
  c

def tb3(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, h: {List.get(&2, U32, Q.xs(len, t), Q.n(e0)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e1)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e2)) == Some{9} : Maybe<&2, U32>}
  & ({List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}
  & {List.get(&2, U32, Q.xs(len, t), Q.n(e4)) == Some{9} : Maybe<&2, U32>})))) -> {List.get(&2, U32, Q.xs(len, t), Q.n(e3)) == Some{9} : Maybe<&2, U32>}:
  (a, r) = h
  (b, r2) = r
  (c, r3) = r2
  (e, r4) = r3
  e

def inf0(+len: U32, +t: AT.Tree<U32>, +s: U32, +lf: U32,
  h: {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "CIGAR") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMLEN") == False{} : Bool}
  & ({B.Info.has(PE.F7(len, t, s, lf), "HOMSEQ") == False{} : Bool}
  & {B.Info.has(PE.F7(len, t, s, lf), "AA") == False{} : Bool})))) ->
  {B.Info.has(PE.F7(len, t, s, lf), "END") == False{} : Bool}:
  (a, r) = h
  a

def pos3(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32,
  h: {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))) ->
  {U32.is_lt(pos, 1000000000) == True{} : Bool}:
  (a, r) = h
  (b, r2) = r
  (c, r3) = r2
  r3

def ae0(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}:
  (a, r) = h
  a

def ae2(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool, h: {als == PE.REF(e2, e3) <> Q.TL(als) : List<&2, NX.Ap>}
  & ({String.split(Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)), ',') == Q.STRS(Q.xs(len, t), Q.TL(als)) : List<&2, String>}
  & ({Q.ALS_IN(lf, als) == True{} : Bool}
  & ({Q.ALS_L(Q.xs(len, t), als) == True{} : Bool}
  & ({B.Alleles.distinct(Q.BFS(Q.xs(len, t), als)) == True{} : Bool}
  & {(String.eq(B.Allele.show(Q.BF(Q.SL(Q.xs(len, t), PE.REF(e2, e3)))), Q.fld(Q.xs(len, t), Q.nx(e2), Q.n(e3)))
      && String.eq(String.join(B.Alleles.show(Q.BFS(Q.xs(len, t), Q.TL(als))), ","), Q.fld(Q.xs(len, t), Q.nx(e3), Q.n(e4)))) == up : Bool}))))) ->
  {Q.ALS_IN(lf, als) == True{} : Bool}:
  (a, r) = h
  (b, r2) = r
  (c, r3) = r2
  c

# The writer's text (proof_c_text.bend's TXT) on the line's bytes is the
# record rewritten for Var{q, sb, y} with the line's terminator, when rs and
# as are the alleles' texts.
def new_text(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +wl: U32, +wt: AT.Tree<U32>, +q: Nat, +rs: String, +as: String, +v: B.Var, +sb: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>,
  +hrs: {rs == B.Allele.show(sb) : String},
  +has: {as == String.join(B.Alleles.show(y), ",") : String}) ->
  {TX.TXT(len, t, d, wl, wt, s, e0, e1, e2, e4, lf, q, rs, as) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), v, B.Var{q, sb, y}), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String}:
  +hfs = fs_shape(CU.lbody(D.view(C.BT(len, t)), s, lf), CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e4), 1n), U32.to_nat(e5)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e5), 1n), U32.to_nat(e6)), B.Rec.field(J.pfs(CU.lbody(D.view(C.BT(len, t)), s, lf)), 7n), PE.fix_fields(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +hin = AB.subst(List<&2, String>, z => {B.Info.has(B.Rec.field(z, 7n), "END") == False{} : Bool}, B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), s, lf)), TS.L7(CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(e0)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e0), 1n), U32.to_nat(e1)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e1), 1n), U32.to_nat(e2)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e2), 1n), U32.to_nat(e3)), CU.fld(D.view(C.BT(len, t)), Nat.add(U32.to_nat(e3), 1n), U32.to_nat(e4)), B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), s, lf)), 5n), List.drop(&2, String, B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), s, lf)), 6n)), hfs, inf0(len, t, s, lf, PE.fix_info(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +h5 = N.le_trans(U32.to_nat(e4), U32.to_nat(lf), Nat.add(U32.to_nat(lf), 1n), N.lt_to_le(U32.to_nat(e4), U32.to_nat(lf), e4lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.le_add_r(U32.to_nat(lf), 1n))
  +hlt = CU.line_text(D.view(C.BT(len, t)), s, lf, hlf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +TXE = TXL.tx_eq(D.view(C.BT(len, t)), CU.lline(D.view(C.BT(len, t)), s, lf), U32.to_nat(s), U32.to_nat(e0), U32.to_nat(e1), U32.to_nat(e2), U32.to_nat(e3), U32.to_nat(e4), Nat.add(U32.to_nat(lf), 1n), B.Rec.field(B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), s, lf)), 5n), List.drop(&2, String, B.Rec.fields(CU.lbody(D.view(C.BT(len, t)), s, lf)), 6n), v, q, sb, y,
    PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_01(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_23(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_34(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), h5,
    tb0(len, t, e0, e1, e2, e3, e4, PE.fix_tabs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), tb1(len, t, e0, e1, e2, e3, e4, PE.fix_tabs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), tb2(len, t, e0, e1, e2, e3, e4, PE.fix_tabs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), tb3(len, t, e0, e1, e2, e3, e4, PE.fix_tabs(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)),
    hlt, hfs, hin)
  %Equal.sym(String, P.btext(len, t, s, (lf - s : U32)), CU.ltext(D.view(C.BT(len, t)), s, lf), FH.btext_fld(len, t, s, lf, slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
    {TX.TXT(len, t, d, wl, wt, s, e0, e1, e2, e4, lf, q, rs, as) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(_))), v, B.Var{q, sb, y}), B.Line.term(Norm.line(_))) : String}
  %Equal.sym(String, NR.chars(D.slice(WW.V(len, t), U32.to_nat(s), U32.to_nat(TX.K1(s, e0)))), CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), Nat.add(U32.to_nat(e0), 1n)), pc(len, t, d, s, e0, hok, PJ.lf_s0(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), e0len(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
    {String.append(String.append(String.append(String.append(String.append(String.append(_, Nat.show(q)), NR.chars(D.slice(WW.V(len, t), U32.to_nat(e1), U32.to_nat(TX.K2(e1, e2))))), rs), "\t"), as), NR.chars(D.slice(WW.V(len, t), U32.to_nat(e4), U32.to_nat(TX.K3(e4, lf))))) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf))), v, B.Var{q, sb, y}), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))) : String}
  %Equal.sym(String, NR.chars(D.slice(WW.V(len, t), U32.to_nat(e1), U32.to_nat(TX.K2(e1, e2)))), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e1), Nat.add(U32.to_nat(e2), 1n)), pc(len, t, d, e1, e2, hok, N.lt_to_le(U32.to_nat(e1), U32.to_nat(e2), PJ.lf_12(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))), e2len(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
    {String.append(String.append(String.append(String.append(String.append(String.append(CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), Nat.add(U32.to_nat(e0), 1n)), Nat.show(q)), _), rs), "\t"), as), NR.chars(D.slice(WW.V(len, t), U32.to_nat(e4), U32.to_nat(TX.K3(e4, lf))))) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf))), v, B.Var{q, sb, y}), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))) : String}
  %Equal.sym(String, NR.chars(D.slice(WW.V(len, t), U32.to_nat(e4), U32.to_nat(TX.K3(e4, lf)))), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e4), Nat.add(U32.to_nat(lf), 1n)), pc(len, t, d, e4, lf, hok, N.lt_to_le(U32.to_nat(e4), U32.to_nat(lf), e4lf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))) :
    {String.append(String.append(String.append(String.append(String.append(String.append(CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), Nat.add(U32.to_nat(e0), 1n)), Nat.show(q)), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e1), Nat.add(U32.to_nat(e2), 1n))), rs), "\t"), as), _) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf))), v, B.Var{q, sb, y}), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))) : String}
  %Equal.sym(String, rs, B.Allele.show(sb), hrs) :
    {String.append(String.append(String.append(String.append(String.append(String.append(CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), Nat.add(U32.to_nat(e0), 1n)), Nat.show(q)), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e1), Nat.add(U32.to_nat(e2), 1n))), _), "\t"), as), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e4), Nat.add(U32.to_nat(lf), 1n))) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf))), v, B.Var{q, sb, y}), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))) : String}
  %Equal.sym(String, as, String.join(B.Alleles.show(y), ","), has) :
    {String.append(String.append(String.append(String.append(String.append(String.append(CU.fld(D.view(C.BT(len, t)), U32.to_nat(s), Nat.add(U32.to_nat(e0), 1n)), Nat.show(q)), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e1), Nat.add(U32.to_nat(e2), 1n))), B.Allele.show(sb)), "\t"), _), CU.fld(D.view(C.BT(len, t)), U32.to_nat(e4), Nat.add(U32.to_nat(lf), 1n))) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf))), v, B.Var{q, sb, y}), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))) : String}
  TXE

# The writer's text for the normalized alleles (pk's TXT) is the record
# rewritten for NX.norm's variant (VW) with the line's terminator.
def pk_text(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +wl: U32, +wt: AT.Tree<U32>, +wd: Nat,
  +hw: {D.ok(C.BT(wl, wt), wd) == True{} : Bool},
  +offu: U32, +k: U32, +tr: U32, +dl: Nat,
  +hk: {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, offu, k, tr, dl) == True{} : Bool},
  +ho: {Nat.is_le(Nat.sub(U32.to_nat(pos), 1n), Nat.add(U32.to_nat(offu), U32.to_nat(wl))) == True{} : Bool},
  +v: B.Var) ->
  {TX.TXT(len, t, d, wl, wt, s, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, wl, wt, PE.REF(e2, e3), k, tr, dl, pos, offu), TX.ACC(Q.TL(als), "", True{}, len, t, wl, wt, k, tr, dl, pos, offu)) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), v, Q.VW(Q.xs(len, t), Q.xs(wl, wt), PE.REF(e2, e3) <> Q.TL(als), pos, offu, k, tr, dl)), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String}:
  +hk1 = N.and_true_l(Nat.is_le(Nat.add(Nat.add(U32.to_nat(k), U32.to_nat(offu)), 1n), U32.to_nat(pos)), Q.KL(PE.REF(e2, e3) <> Q.TL(als), tr, dl), hk)
  +hkl = N.and_true_r(Nat.is_le(Nat.add(Nat.add(U32.to_nat(k), U32.to_nat(offu)), 1n), U32.to_nat(pos)), Q.KL(PE.REF(e2, e3) <> Q.TL(als), tr, dl), hk)
  +hl = N.and_true_l(Nat.is_lt(Nat.add(U32.to_nat(tr), dl), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Q.KL(Q.TL(als), tr, dl), hkl)
  +hkt = N.and_true_r(Nat.is_lt(Nat.add(U32.to_nat(tr), dl), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Q.KL(Q.TL(als), tr, dl), hkl)
  +hlen = PA.als_w(lf, len, als, ae2(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_to_le(U32.to_nat(lf), U32.to_nat(len), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))
  +hain = AB.subst(List<&2, NX.Ap>, z => {Q.ALS_IN(len, z) == True{} : Bool}, als, PE.REF(e2, e3) <> Q.TL(als), ae0(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), hlen)
  +hin1 = N.and_true_r(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len)), N.and_true_l(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain))
  +hat = N.and_true_r(Bool.and(Nat.is_le(1n, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), Nat.is_le(Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len))), Q.ALS_IN(len, Q.TL(als)), hain)
  +hd = N.lt_le_trans(dl, U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), U32.to_nat(len), N.le_lt_trans(dl, Nat.add(U32.to_nat(tr), dl), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), N.le_add_l(dl, U32.to_nat(tr)), hl),
    N.le_trans(U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), Nat.add(U32.to_nat(NX.Ap.st(PE.REF(e2, e3))), U32.to_nat(NX.Ap.ln(PE.REF(e2, e3)))), U32.to_nat(len), N.le_add_l(U32.to_nat(NX.Ap.ln(PE.REF(e2, e3))), U32.to_nat(NX.Ap.st(PE.REF(e2, e3)))), hin1))
  +hps = pos3(len, t, e0, e1, pos, PE.fix_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +hrs = XT.ala_show(len, t, d, wl, wt, wd, PE.REF(e2, e3), pos, offu, k, tr, dl, hok, hw, hin1, hk1, ho, hl)
  +has = XT.acc_join(len, t, d, wl, wt, wd, Q.TL(als), pos, offu, k, tr, dl, hok, hw, hat, hk1, ho, hkt)
  %XT.qq_pos(len, t, d, pos, offu, k, dl, hok, hk1, hps, hd) :
    {TX.TXT(len, t, d, wl, wt, s, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, wl, wt, PE.REF(e2, e3), k, tr, dl, pos, offu), TX.ACC(Q.TL(als), "", True{}, len, t, wl, wt, k, tr, dl, pos, offu)) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), v, B.Var{_, Q.BF(Q.ALK(Q.xs(len, t), Q.xs(wl, wt), pos, offu, PE.REF(e2, e3), k, tr, dl)), Q.ALKS(Q.xs(len, t), Q.xs(wl, wt), pos, offu, Q.TL(als), k, tr, dl)}), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String}
  new_text(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, wl, wt, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, wl, wt, PE.REF(e2, e3), k, tr, dl, pos, offu), TX.ACC(Q.TL(als), "", True{}, len, t, wl, wt, k, tr, dl, pos, offu), v, Q.BF(Q.ALK(Q.xs(len, t), Q.xs(wl, wt), pos, offu, PE.REF(e2, e3), k, tr, dl)), Q.ALKS(Q.xs(len, t), Q.xs(wl, wt), pos, offu, Q.TL(als), k, tr, dl), hrs, has)

# The line's body and terminator are its bytes s .. lf.
def bt_line(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {String.append(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32)))), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))) : String}:
  %Equal.sym(String, P.btext(len, t, s, (lf - s : U32)), CU.ltext(D.view(C.BT(len, t)), s, lf), FH.btext_fld(len, t, s, lf, slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))) :
    {String.append(B.Line.body(Norm.line(_)), B.Line.term(Norm.line(_))) == Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))) : String}
  Equal.trans(String, String.append(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf)), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))), B.Line.text(CU.lline(D.view(C.BT(len, t)), s, lf)), Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))),
    Equal.sym(String, B.Line.text(CU.lline(D.view(C.BT(len, t)), s, lf)), String.append(B.Line.body(CU.lline(D.view(C.BT(len, t)), s, lf)), B.Line.term(CU.lline(D.view(C.BT(len, t)), s, lf))), ltx(CU.lline(D.view(C.BT(len, t)), s, lf))),
    CU.line_text(D.view(C.BT(len, t)), s, lf, hlf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

# New text equal to the body: the written bytes are the line's.
def ne_view(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>, +NT: String,
  +hpk: {NR.chars(WW.V(sl, st)) == String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String},
  +he: {String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == True{} : Bool}) ->
  {D.view(C.BT(sl, st)) == D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))) : List<&2, U32>}:
  +hNT = RBS.str_eq_sound(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32)))), he)
  +h1 = Equal.trans(String, NR.chars(WW.V(sl, st)), String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))), String.append(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32)))), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))),
    hpk, Equal.cong(String, String, z => String.append(z, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))), NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32)))), hNT))
  +h2 = Equal.trans(String, NR.chars(WW.V(sl, st)), String.append(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32)))), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))), Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))), h1, bt_line(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +h3 = Equal.trans(String, NR.chars(WW.V(sl, st)), Norm.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))), NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))), h2, LSS.chars_norm(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))))
  Z.chars_inj(WW.V(sl, st), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), h3)

def hbx(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Nat.is_le(Nat.add(U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), List.length(&2, U32, D.view(C.BT(len, t)))) == True{} : Bool}:
  +hle2 = N.le_trans(U32.to_nat(s), U32.to_nat(lf), Nat.add(U32.to_nat(lf), 1n), slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), N.le_add_r(U32.to_nat(lf), 1n))
  %Equal.sym(Nat, Nat.add(U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), Nat.add(U32.to_nat(lf), 1n), N.le_sub_add(U32.to_nat(s), Nat.add(U32.to_nat(lf), 1n), hle2)) :
    {Nat.is_le(_, List.length(&2, U32, D.view(C.BT(len, t)))) == True{} : Bool}
  %LP.len_x(len, t, d, hok) : {Nat.is_le(Nat.add(U32.to_nat(lf), 1n), _) == True{} : Bool}
  C.succ_le(U32.to_nat(lf), U32.to_nat(len), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))

# Then the written length is the line's.
def core_m(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +hv: {D.view(C.BT(sl, st)) == D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))) : List<&2, U32>}) ->
  {U32.to_nat(sl) == Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)) : Nat}:
  +hlx = LP.len_x(sl, st, RD.tdepth(st), okw)
  +hcl = Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), D.view(C.BT(sl, st)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), hv)
  +hsl = LP.slice_len(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), hbx(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  Equal.trans(Nat, U32.to_nat(sl), List.length(&2, U32, D.view(C.BT(sl, st))), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), hlx,
    Equal.trans(Nat, List.length(&2, U32, D.view(C.BT(sl, st))), List.length(&2, U32, D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), hcl, hsl))

def kconv(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {U32.to_nat(((lf + 1 : U32) - s : U32)) == Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)) : Nat}:
  +hinc = LP.inc_len(len, t, d, lf, hok, PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
  +hle1 = AB.subst(Nat, z => {Nat.is_le(U32.to_nat(s), z) == True{} : Bool}, Nat.add(U32.to_nat(lf), 1n), U32.to_nat((lf + 1 : U32)), Equal.sym(Nat, U32.to_nat((lf + 1 : U32)), Nat.add(U32.to_nat(lf), 1n), hinc),
    N.le_trans(U32.to_nat(s), U32.to_nat(lf), Nat.add(U32.to_nat(lf), 1n), slf(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), N.le_add_r(U32.to_nat(lf), 1n)))
  Equal.trans(Nat, U32.to_nat(((lf + 1 : U32) - s : U32)), Nat.sub(U32.to_nat((lf + 1 : U32)), U32.to_nat(s)), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), LP.sub_u((lf + 1 : U32), s, hle1),
    Equal.cong(Nat, Nat, z => Nat.sub(z, U32.to_nat(s)), U32.to_nat((lf + 1 : U32)), Nat.add(U32.to_nat(lf), 1n), hinc))

def ne_len.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +NT: String,
  +hpk: {NR.chars(WW.V(sl, st)) == String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - s : U32)) == False{} : Bool},
  +b: Bool,
  +hb: {String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == b : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hm = core_m(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, ne_view(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, NT, hpk, hb))
      +hk = Equal.trans(Nat, U32.to_nat(sl), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), U32.to_nat(((lf + 1 : U32) - s : U32)), hm, Equal.sym(Nat, U32.to_nat(((lf + 1 : U32) - s : U32)), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), kconv(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)))
      +hT = Equal.trans(Bool, U32.is_eq(sl, ((lf + 1 : U32) - s : U32)), Nat.is_eq(U32.to_nat(sl), U32.to_nat(((lf + 1 : U32) - s : U32))), True{}, U.is_eq_to_nat(sl, ((lf + 1 : U32) - s : U32)),
        AB.subst(Nat, z => {Nat.is_eq(z, U32.to_nat(((lf + 1 : U32) - s : U32))) == True{} : Bool}, U32.to_nat(((lf + 1 : U32) - s : U32)), U32.to_nat(sl), Equal.sym(Nat, U32.to_nat(sl), U32.to_nat(((lf + 1 : U32) - s : U32)), hk), N.eq_refl(U32.to_nat(((lf + 1 : U32) - s : U32)))))
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, U32.is_eq(sl, ((lf + 1 : U32) - s : U32)), True{}, Equal.sym(Bool, U32.is_eq(sl, ((lf + 1 : U32) - s : U32)), False{}, hl), hT)))

# Lengths differ: the new text is not the line's body.
def ne_len_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +NT: String,
  +hpk: {NR.chars(WW.V(sl, st)) == String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - s : U32)) == False{} : Bool}) ->
  {String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == False{} : Bool}:
  ne_len.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, NT, hpk, hl, String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), {==})

def ne_eq.k(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +NT: String,
  +hpk: {NR.chars(WW.V(sl, st)) == String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - s : U32)) == True{} : Bool},
  +he: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), s, sl))) == False{} : Bool},
  +b: Bool,
  +hb: {String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == b : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +hv = ne_view(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, NT, hpk, hb)
      +hm = core_m(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, hv)
      +hj = {%Equal.sym(Nat, U32.to_nat(sl), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), hm) : {Nat.is_le(Nat.add(U32.to_nat(s), _), U32.to_nat(len)) == True{} : Bool};
        %Equal.sym(Nat, U32.to_nat(len), List.length(&2, U32, D.view(C.BT(len, t))), LP.len_x(len, t, d, hok)) : {Nat.is_le(Nat.add(U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), _) == True{} : Bool};
        hbx(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp) : {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sl)), D.size(C.BT(len, t))) == True{} : Bool}}
      +hsv = SMB.same_view_t(sl, st, len, t, RD.tdepth(st), d, 0, s, sl, okw, hok, N.le_refl(U32.to_nat(sl)), hj)
      +hA = Equal.trans(List<&2, U32>, D.slice(D.view(C.BT(sl, st)), U32.to_nat(0), U32.to_nat(sl)), D.view(C.BT(sl, st)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), BF.view_all(sl, st, RD.tdepth(st), okw), hv)
      +hB = Equal.cong(Nat, List<&2, U32>, z => D.slice(D.view(C.BT(len, t)), U32.to_nat(s), z), U32.to_nat(sl), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)), hm)
      +hLE = {%Equal.sym(List<&2, U32>, D.slice(D.view(C.BT(sl, st)), U32.to_nat(0), U32.to_nat(sl)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), hA) : {D.list_eq(_, D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(sl))) == True{} : Bool};
        %Equal.sym(List<&2, U32>, D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(sl)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), hB) : {D.list_eq(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s))), _) == True{} : Bool};
        BL.list_eq_refl(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), Nat.sub(Nat.add(U32.to_nat(lf), 1n), U32.to_nat(s)))) : {D.list_eq(D.slice(D.view(C.BT(sl, st)), U32.to_nat(0), U32.to_nat(sl)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(sl))) == True{} : Bool}}
      +hT = Equal.trans(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), s, sl))), D.list_eq(D.slice(D.view(C.BT(sl, st)), U32.to_nat(0), U32.to_nat(sl)), D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(sl))), True{}, hsv, hLE)
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), s, sl))), True{}, Equal.sym(Bool, Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), s, sl))), False{}, he), hT)))

# The bytes differ: the new text is not the line's body.
def ne_eq_t(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +sl: U32, +st: AT.Tree<U32>,
  +okw: {WW.OK(sl, st) == True{} : Bool},
  +NT: String,
  +hpk: {NR.chars(WW.V(sl, st)) == String.append(NT, B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String},
  +hl: {U32.is_eq(sl, ((lf + 1 : U32) - s : U32)) == True{} : Bool},
  +he: {Pair.snd(D.Bytes, Bool, Pair.snd(D.Bytes, D.Bytes & Bool, BY.same(C.BT(sl, st), 0, C.BT(len, t), s, sl))) == False{} : Bool}) ->
  {String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))) == False{} : Bool}:
  ne_eq.k(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, sl, st, okw, NT, hpk, hl, he, String.eq(NT, B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), {==})

# ---------------------------------------------------------------------------
# The window's facts (the cached letters, and a passed REF check)
# ---------------------------------------------------------------------------

def wl31(+r: String, +a: Nat, +b: Nat, +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}) ->
  {Norm.le31(String.length(CD.letters(r, a, b))) == True{} : Bool}:
  XL.le31_mono(String.length(CD.letters(r, a, b)), String.length(r), N.le_trans(String.length(CD.letters(r, a, b)), Nat.min(b, String.length(r)), String.length(r),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.min(b, String.length(r))) == True{} : Bool}, Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), String.length(CD.letters(r, a, b)), Equal.sym(Nat, String.length(CD.letters(r, a, b)), Nat.sub(Nat.min(b, String.length(r)), Nat.min(a, String.length(r))), CA.len_letters(r, a, b)), XL.sub_le(Nat.min(b, String.length(r)), Nat.min(a, String.length(r)))),
    H.min_le_r(b, String.length(r))), H.fits_le31(String.length(r), N.and_true_r(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfs)))

def wenc(+r: String, +a: Nat, +b: Nat, +hbr: {E.is_bytes(r) == True{} : Bool}, +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}) ->
  {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat})):
  EN.enc_ok(CD.letters(r, a, b), CA.letters_bytes(r, a, b, hbr), wl31(r, a, b, hfs))

def wok(+r: String, +a: Nat, +b: Nat, h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}))) ->
  {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}:
  (x, y) = h
  x

def wlen(+r: String, +a: Nat, +b: Nat, h: {D.ok(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), E.depth(String.length(CD.letters(r, a, b)))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))) == E.codes(CD.letters(r, a, b)) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(CD.letters(r, a, b))), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}))) ->
  {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  y3

def rc1(+r: String, +a: Nat, +b: Nat, +len: U32, +t: AT.Tree<U32>, +pos: U32, +e2: U32, +e3: U32, h: HL.RCC(Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))))) ->
  {Nat.is_le(Nat.min(a, String.length(r)), Nat.sub(U32.to_nat(pos), 1n)) == True{} : Bool}:
  (x, y) = h
  x

def rc2(+r: String, +a: Nat, +b: Nat, +len: U32, +t: AT.Tree<U32>, +pos: U32, +e2: U32, +e3: U32, h: HL.RCC(Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))))) ->
  {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), List.length(&2, B.Base, Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))))), Nat.add(Nat.min(a, String.length(r)), List.length(&2, B.Base, B.Bases.of_fasta(CD.letters(r, a, b))))) == True{} : Bool}:
  (x, y) = h
  y

def pos2(+len: U32, +t: AT.Tree<U32>, +e0: U32, +e1: U32, +pos: U32, h: {B.Pos.read(Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1))) == Some{Q.n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(Q.n(pos)) == Q.fld(Q.xs(len, t), Q.nx(e0), Q.n(e1)) : String}
  & ({Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}
  & {U32.is_lt(pos, 1000000000) == True{} : Bool}))) ->
  {Nat.is_eq(Q.n(pos), 0n) == False{} : Bool}:
  (x, y) = h
  (x2, y2) = y
  (x3, y3) = y2
  x3

def lt_sp(+x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      lt_sp(p)

def lt_pred(+x: Nat, +h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_lt(Nat.sub(x, 1n), x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, N.true_ne_false(h))
    case 1n+(+p):
      %Equal.sym(Nat, Nat.sub(p, 0n), p, N.sub_zero(p)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      lt_sp(p)

# The window starts before POS (norm_var's ho1) ...
def wo1(+r: String, +a: Nat, +b: Nat, +pos: U32, +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +hpz: {Nat.is_eq(U32.to_nat(pos), 0n) == False{} : Bool},
  +hc1: {Nat.is_le(Nat.min(a, String.length(r)), Nat.sub(U32.to_nat(pos), 1n)) == True{} : Bool}) ->
  {Nat.is_lt(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(pos)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), Nat.min(a, String.length(r)), H.f31_eq(Nat.min(a, String.length(r)), N.and_true_l(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfs))) :
    {Nat.is_lt(_, U32.to_nat(pos)) == True{} : Bool}
  N.le_lt_trans(Nat.min(a, String.length(r)), Nat.sub(U32.to_nat(pos), 1n), U32.to_nat(pos), hc1, lt_pred(U32.to_nat(pos), hpz))

# ... and reaches POS (ho2).
def wo2(+r: String, +a: Nat, +b: Nat, +pos: U32, +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool}, +lr: Nat,
  +hc2: {Nat.is_le(Nat.add(Nat.sub(U32.to_nat(pos), 1n), lr), Nat.add(Nat.min(a, String.length(r)), List.length(&2, B.Base, B.Bases.of_fasta(CD.letters(r, a, b))))) == True{} : Bool},
  +hwl: {U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))) == String.length(CD.letters(r, a, b)) : Nat}) ->
  {Nat.is_le(Nat.sub(U32.to_nat(pos), 1n), Nat.add(U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(Nat.min(a, String.length(r)))), Nat.min(a, String.length(r)), H.f31_eq(Nat.min(a, String.length(r)), N.and_true_l(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r)), hfs))) :
    {Nat.is_le(Nat.sub(U32.to_nat(pos), 1n), Nat.add(_, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(String.length(CD.letters(r, a, b)))), String.length(CD.letters(r, a, b)), hwl) :
    {Nat.is_le(Nat.sub(U32.to_nat(pos), 1n), Nat.add(Nat.min(a, String.length(r)), _)) == True{} : Bool}
  %WL.of_fasta_len(CD.letters(r, a, b)) :
    {Nat.is_le(Nat.sub(U32.to_nat(pos), 1n), Nat.add(Nat.min(a, String.length(r)), _)) == True{} : Bool}
  N.le_trans(Nat.sub(U32.to_nat(pos), 1n), Nat.add(Nat.sub(U32.to_nat(pos), 1n), lr), Nat.add(Nat.min(a, String.length(r)), List.length(&2, B.Base, B.Bases.of_fasta(CD.letters(r, a, b)))), N.le_add_r(Nat.sub(U32.to_nat(pos), 1n), lr), hc2)

def nv2(+len: U32, +t: AT.Tree<U32>, +r: String, +a: Nat, +b: Nat, +e2: U32, +e3: U32, +als: List<&2, NX.Ap>, +pos: U32, +k: U32, +tr: U32, +dl: Nat,
  h: {V.var_in(Q.n(U32.from_nat(Nat.min(a, String.length(r)))), Q.BF(Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos)) == Some{Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)} : Maybe<&2, B.Var>}
  & {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl) == True{} : Bool}) ->
  {Q.KOK(PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl) == True{} : Bool}:
  (x, y) = h
  y

# The ALS_IN of the alleles as REF and the ALTs, on the whole buffer.
def ain(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up)) ->
  {Q.ALS_IN(len, PE.REF(e2, e3) <> Q.TL(als)) == True{} : Bool}:
  +hlen = PA.als_w(lf, len, als, ae2(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), N.lt_to_le(U32.to_nat(lf), U32.to_nat(len), PJ.lf_lt(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf, AF.lfd(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))))
  AB.subst(List<&2, NX.Ap>, z => {Q.ALS_IN(len, z) == True{} : Bool}, als, PE.REF(e2, e3) <> Q.TL(als), ae0(len, t, e2, e3, e4, lf, als, up, PE.fix_als(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp)), hlen)

# The written bytes (pk) are the record rewritten with the line's
# terminator, the counters being NX.norm's on the window.
def hpk_w(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32, +pos: U32,
  +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, +als: List<&2, NX.Ap>, +up: Bool,
  +hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  +hs: {U32.is_le(s, len) == True{} : Bool},
  +hp: AF.FXP(len, t, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up),
  +r: String, +a: Nat, +b: Nat,
  +hbr: {E.is_bytes(r) == True{} : Bool},
  +hrc: {J.ref_check(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))) == Some{True{}} : Maybe<&2, Bool>},
  +hfs: {Bool.and(Norm.fits31(Nat.min(a, String.length(r))), Norm.fits31(String.length(r))) == True{} : Bool},
  +k: U32, +tr: U32, +dl: Nat,
  +hz: {Q.NZ(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r)))) == Some{Q.K3{k, tr, dl}} : Maybe<&2, Q.K3>},
  +sl: U32, +st: AT.Tree<U32>,
  +pk: {NR.chars(WW.V(sl, st)) == TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), s, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))) : String}) ->
  {NR.chars(WW.V(sl, st)) == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))) : String}:
  +hw = wok(r, a, b, wenc(r, a, b, hbr, hfs))
  +hwl = wlen(r, a, b, wenc(r, a, b, hbr, hfs))
  +hpz = pos2(len, t, e0, e1, pos, PE.fix_pos(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp))
  +h1 = wo1(r, a, b, pos, hfs, hpz, rc1(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc)))
  +h2 = wo2(r, a, b, pos, hfs, List.length(&2, B.Base, Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3))))), rc2(r, a, b, len, t, pos, e2, e3, HL.rc_cov(String.length(r), Nat.min(a, String.length(r)), B.Bases.of_fasta(CD.letters(r, a, b)), Nat.sub(U32.to_nat(pos), 1n), Q.BF(D.slice(D.view(C.BT(len, t)), U32.to_nat((e2 + 1 : U32)), U32.to_nat(AF.RL(e2, e3)))), hrc)), hwl)
  +hk = nv2(len, t, r, a, b, e2, e3, als, pos, k, tr, dl, TN.norm_var(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), E.depth(String.length(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl, hok, hw, ain(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp), N.le_zero_l(List.length(&2, NX.Ap, Q.TL(als))), h1, h2, hz))
  Equal.trans(String, NR.chars(WW.V(sl, st)), TX.TXT(len, t, d, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), s, e0, e1, e2, e4, lf, U32.to_nat(((pos - k : U32) + U32.from_nat(dl) : U32)), TX.ALA(len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), PE.REF(e2, e3), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r)))), TX.ACC(Q.TL(als), "", True{}, len, t, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), k, tr, dl, pos, U32.from_nat(Nat.min(a, String.length(r))))), String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(Norm.line(P.btext(len, t, s, (lf - s : U32))))), Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos), Q.VW(Q.xs(len, t), Q.xs(U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b))), PE.REF(e2, e3) <> Q.TL(als), pos, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl)), B.Line.term(Norm.line(P.btext(len, t, s, (lf - s : U32))))),
    pk, pk_text(len, t, d, s, pos, e0, e1, e2, e3, e4, e5, e6, e7, lf, als, up, hok, hs, hp, U32.from_nat(String.length(CD.letters(r, a, b))), EN.enc_t(CD.letters(r, a, b)), E.depth(String.length(CD.letters(r, a, b))), hw, U32.from_nat(Nat.min(a, String.length(r))), k, tr, dl, hk, h2, Q.V0(Q.xs(len, t), PE.REF(e2, e3) <> Q.TL(als), pos)))
