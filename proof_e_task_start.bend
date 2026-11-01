import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./norm_seq.bend as Q
import ./norm_run.bend as NR
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run.bend as PRN
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_num.bend as NM
import ./proof_b_run_sz.bend as SZ
import ./proof_b_cache_lem.bend as CL
import ./proof_e_defs.bend as SD
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_index.bend as I

# Phase E, area D (task): a task's start. Its run (task.run0) is a good run
# picture standing for the phantom state SD.rs0(c0, l).

def T0() -> AT.Tree<U32>:
  G.tnew(0n, 0)

def RPA(+c0: String, +l: Nat, +cl: U32, +ct: AT.Tree<U32>) -> P.RunP:
  P.RunP{0n, True{}, "", Some{c0}, cl, ct, Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, R.Cnt{0n, 0n, 0n, 0n}, 0, G.tnew(0n, 0), 0, Nil{}, False{}}

def R0G(+c0: String, +l: Nat, +L: U32) -> Type:
  &rp: P.RunP -> ({W.task.run0(c0, l, L) == P.mkRun(rp) : NR.Run}
    & ({RD.RunInv(rp) == True{} : Bool}
    & ({P.settle(P.specRun(rp)) == P.settle(SD.rs0(c0, l)) : R.RunSt}
    & {R.RunSt.inbody(P.specRun(rp)) == True{} : Bool})))

def spec_a(+c0: String, +l: Nat, +cl: U32, +ct: AT.Tree<U32>) -> {P.specRun(RPA(c0, l, cl, ct)) == SD.rs0(c0, l) : R.RunSt}:
  {==}

def run0.k2(+c0: String, +l: Nat, +L: U32, +cl: U32, +ct: AT.Tree<U32>,
  +eA: {NR.Run{0n, True{}, "", Some{c0}, NR.of_str(c0), Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, R.Cnt{0n, 0n, 0n, 0n}, BY.empty(0n), 0, Nil{}, False{}} == P.mkRun(RPA(c0, l, cl, ct)) : NR.Run},
  rr: &p2: P.RunP -> ({NR.reserve(P.mkRun(RPA(c0, l, cl, ct)), L) == P.mkRun(p2) : NR.Run}
    & ({PRN.RunInv(p2) == True{} : Bool}
    & ({P.specRun(p2) == P.specRun(RPA(c0, l, cl, ct)) : R.RunSt}
    & {P.RunP.ow(p2) == P.RunP.ow(RPA(c0, l, cl, ct)) : U32})))) ->
  R0G(c0, l, L):
  (+rp, r1) = rr
  (+er, r2) = r1
  (+hi, r3) = r2
  (+es, r4) = r3
  +e0 = {
    %Equal.sym(NR.Run, NR.Run{0n, True{}, "", Some{c0}, NR.of_str(c0), Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, R.Cnt{0n, 0n, 0n, 0n}, BY.empty(0n), 0, Nil{}, False{}}, P.mkRun(RPA(c0, l, cl, ct)), eA) :
      {NR.reserve(_, L) == P.mkRun(rp) : NR.Run}
    er : {W.task.run0(c0, l, L) == P.mkRun(rp) : NR.Run}}
  +es2 = Equal.trans(R.RunSt, P.specRun(rp), P.specRun(RPA(c0, l, cl, ct)), SD.rs0(c0, l), es, spec_a(c0, l, cl, ct))
  (rp, (e0, (hi, (Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), P.specRun(rp), SD.rs0(c0, l), es2),
    Equal.cong(R.RunSt, Bool, z => R.RunSt.inbody(z), P.specRun(rp), SD.rs0(c0, l), es2)))))

def run0.k(+c0: String, +l: Nat, +L: U32,
  os: &cl: U32 -> &ct: AT.Tree<U32> -> &cd: Nat ->
    ({NR.of_str(c0) == C.BT(cl, ct) : D.Bytes}
    & ({D.ok(C.BT(cl, ct), cd) == True{} : Bool}
    & {NR.chars(D.view(C.BT(cl, ct))) == c0 : String}))) ->
  R0G(c0, l, L):
  (+cl, o1) = os
  (+ct, o2) = o1
  (+cd, o3) = o2
  (+eqs, o4) = o3
  (+hok, hch) = o4
  +t0 = G.tnew(0n, 0)
  +k0 = {R.Cnt{0n, 0n, 0n, 0n} : R.Cnt}
  +ok0 = LM.ok_td(0, t0, 0n, C.ok_mk(0, t0, 0n, G.tnew_full(0n, 0), {==}, I.le0(Nat.mul(4n, Nat.pow(2n, 0n)))))
  +okc = LM.ok_td(cl, ct, cd, hok)
  +hs = {
    %Equal.sym(String, NR.chars(D.view(C.BT(cl, ct))), c0, hch) : {String.eq(_, c0) == True{} : Bool}
    CL.str_eq_refl(c0) : {String.eq(NR.chars(D.view(C.BT(cl, ct))), Maybe.default(&2, String, Some{c0}, "")) == True{} : Bool}}
  +hinv = PI.inv_mk(True{}, "", Some{c0}, cl, ct, Nil{}, Nil{}, 0n, 0n, 0, t0, 0, Nil{}, False{}, (ok0, ({==}, (okc, (hs, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))))))
  +eq1 = AB.subst(D.Bytes, z => {NR.Run{0n, True{}, "", Some{c0}, z, Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, k0, C.BT(0, t0), 0, Nil{}, False{}} == P.mkRun(RPA(c0, l, cl, ct)) : NR.Run},
    C.BT(cl, ct), NR.of_str(c0), Equal.sym(D.Bytes, NR.of_str(c0), C.BT(cl, ct), eqs), {==})
  +eq2 = AB.subst(D.Bytes, z => {NR.Run{0n, True{}, "", Some{c0}, NR.of_str(c0), Nil{}, Some{NR.Ck{l, l, 0n, None{}, 0}}, Nil{}, Nil{}, 0n, 0n, k0, z, 0, Nil{}, False{}} == P.mkRun(RPA(c0, l, cl, ct)) : NR.Run},
    C.BT(0, t0), BY.empty(0n), Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), eq1)
  run0.k2(c0, l, L, cl, ct, eq2, PRN.run_reserve(RPA(c0, l, cl, ct), L, hinv))

# NR.of_str of a CHROM of at most 2^28 bytes (proof_b_run.bend's of_str,
# from the 2^28 bound).
def of_str28(+s: String,
  hb: {E.is_bytes(s) == True{} : Bool},
  hn: {Q.len_le(s, 268435456) == True{} : Bool}) ->
  &l: U32 -> &t: AT.Tree<U32> -> &d: Nat ->
  ({NR.of_str(s) == C.BT(l, t) : D.Bytes}
  & ({D.ok(C.BT(l, t), d) == True{} : Bool}
  & {NR.chars(D.view(C.BT(l, t))) == s : String})):
  +L = String.length(s)
  +t0 = G.tnew(0n, 0)
  +hL = NM.lt_c0(L, Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(L, SZ.le28_30(L, SZ.len28(s, hn))))
  +hok0 = AB.subst(D.Bytes, z => {D.ok(z, 0n) == True{} : Bool}, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n), G.empty_ok(0n, {==}))
  +eq = AB.subst(D.Bytes, z => {NR.put_str(z, s) == C.BT(BF.pstl(s, 0), BF.PSR(0, t0, s)) : D.Bytes}, C.BT(0, t0), BY.empty(0n),
    Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), BF.put_str_eq(0, t0, s, G.tnew_full(0n, 0)))
  (BF.pstl(s, 0), (BF.PSR(0, t0, s), (RD.tdepth(BF.PSR(0, t0, s)),
    (eq,
    (BF.put_str_ok(0, t0, 0n, s, hok0, hL),
    BF.put_str_text(0, t0, 0n, s, hok0, hb, hL))))))

# The task's run: a good run picture standing for the phantom state.
def run0_ok(+c0: String, +l: Nat, +L: U32,
  +hb: {E.is_bytes(c0) == True{} : Bool},
  +hn: {Q.len_le(c0, 268435456) == True{} : Bool}) ->
  R0G(c0, l, L):
  run0.k(c0, l, L, of_str28(c0, hb, hn))
