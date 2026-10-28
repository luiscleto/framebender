import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_sdefs.bend as BDs
import ./proof_b_budget_step.bend as BS
import ./proof_b_enc.bend as EN
import ./proof_b_lines_str.bend as LS
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-arrays/proof_base.bend as AB
import ./proof_e_wrap_defs.bend as WD
import ./proof_e_wrap_base.bend as QB
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_api.bend as API
import ./proof_e_bud_step.bend as ST

# Phase E, area E2: the budget of a step with no batch (Q's own step) and of
# the step that starts a batch.

# A piece and its buffer
# ======================

law len_enc:
  for +c: String
  {BY.len(E.enc(c)) == (E.enc(c), U32.from_nat(String.length(c))) : D.Bytes & U32}

def len_enc(c):
  %Equal.sym(D.Bytes, E.enc(c), C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), EN.enc_bt(c)) :
    {BY.len(_) == (_, U32.from_nat(String.length(c))) : D.Bytes & U32}
  {==}

law chars_enc.k:
  for +c: String
  for r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
    & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
    & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
    & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))
  {NR.chars(D.view(E.enc(c))) == c : String}

def chars_enc.k(c, r):
  (hok, r1) = r
  (hv, r2) = r1
  %Equal.sym(D.Bytes, E.enc(c), C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), EN.enc_bt(c)) : {NR.chars(D.view(_)) == c : String}
  %Equal.sym(List<&2, U32>, D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))), E.codes(c), hv) : {NR.chars(_) == c : String}
  LS.chars_codes(c)

# A piece of bytes, at most 2^31 of them, read back from its buffer.
law chars_enc:
  for +c: String
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  {NR.chars(D.view(E.enc(c))) == c : String}

def chars_enc(c, hcb, hcn):
  chars_enc.k(c, EN.enc_ok(c, hcb, hcn))

law nat_enc.k:
  for +c: String
  for r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
    & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
    & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
    & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))
  {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}

def nat_enc.k(c, r):
  (hok, r1) = r
  (hv, r2) = r1
  (hd, hn) = r2
  hn

# The batch takes the piece: it has at least 256 bytes.
law big_of:
  for +c: String
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +h: {U32.is_le(256, U32.from_nat(String.length(c))) == True{} : Bool}
  {BD.big(c) == True{} : Bool}

def big_of(c, hcb, hcn, h):
  +h1 = Equal.trans(Bool, Nat.is_le(U32.to_nat(256), U32.to_nat(U32.from_nat(String.length(c)))), U32.is_le(256, U32.from_nat(String.length(c))), True{},
    Equal.sym(Bool, U32.is_le(256, U32.from_nat(String.length(c))), Nat.is_le(U32.to_nat(256), U32.to_nat(U32.from_nat(String.length(c)))), U.is_le_to_nat(256, U32.from_nat(String.length(c)))), h)
  AB.subst(Nat, z => {Nat.is_le(256n, z) == True{} : Bool}, U32.to_nat(U32.from_nat(String.length(c))), String.length(c), nat_enc.k(c, EN.enc_ok(c, hcb, hcn)), h1)

# Arithmetic
# ==========

law ar_q:
  for +V: Nat
  for +X: Nat
  for +P: Nat
  {Nat.is_le(Nat.add(Nat.add(V, X), Nat.add(0n, 1n)), 1n+Nat.add(V, Nat.add(P, X))) == True{} : Bool}

def ar_q(V, X, P):
  %Equal.sym(Nat, Nat.add(Nat.add(V, X), 1n), 1n+Nat.add(V, X), N.add_one(Nat.add(V, X))) : {Nat.is_le(_, 1n+Nat.add(V, Nat.add(P, X))) == True{} : Bool}
  N.le_add_mono_l(V, X, Nat.add(P, X), N.le_add_l(X, P))

law ar_c:
  for +Vq: Nat
  for +X: Nat
  {Nat.is_le(Nat.add(Nat.add(Nat.add(Vq, 11n), X), Nat.add(0n, 1n)), Nat.add(Vq, Nat.add(12n, X))) == True{} : Bool}

def ar_c(Vq, X):
  +e = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Vq, 11n), X), 1n), 1n+Nat.add(Nat.add(Vq, 11n), X), Nat.add(Vq, Nat.add(12n, X)),
    N.add_one(Nat.add(Nat.add(Vq, 11n), X)),
    Equal.trans(Nat, 1n+Nat.add(Nat.add(Vq, 11n), X), 1n+Nat.add(Vq, Nat.add(11n, X)), Nat.add(Vq, Nat.add(12n, X)),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(Vq, 11n), X), Nat.add(Vq, Nat.add(11n, X)), N.add_assoc(Vq, 11n, X)),
      Equal.sym(Nat, Nat.add(Vq, 1n+Nat.add(11n, X)), 1n+Nat.add(Vq, Nat.add(11n, X)), N.add_succ(Vq, Nat.add(11n, X)))))
  %e : {Nat.is_le(Nat.add(Nat.add(Nat.add(Vq, 11n), X), 1n), _) == True{} : Bool}
  N.le_refl(Nat.add(Nat.add(Nat.add(Vq, 11n), X), 1n))

law ar_e:
  for +Z: Nat
  {Nat.is_le(Nat.add(Nat.add(Z, 0n), 1n), Nat.add(1n+Z, 0n)) == True{} : Bool}

def ar_e(Z):
  %Equal.sym(Nat, Nat.add(Z, 0n), Z, N.add_zero(Z)) : {Nat.is_le(Nat.add(_, 1n), Nat.add(1n+Z, 0n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(1n+Z, 0n), 1n+Z, N.add_zero(1n+Z)) : {Nat.is_le(Nat.add(Z, 1n), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Z, 1n), 1n+Z, N.add_one(Z)) : {Nat.is_le(_, 1n+Z) == True{} : Bool}
  N.le_refl(1n+Z)

# 1 + R more than the reads' share: (Q + X) + (R + 1) <= Q' + X, Q' with W0
# replaced by (1 + R) + W0.
law ar_r:
  for +A: Nat
  for +H: Nat
  for +W0: Nat
  for +R: Nat
  for +X: Nat
  {Nat.is_le(Nat.add(Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H, W0))), X), Nat.add(R, 1n)), Nat.add(Nat.add(A, Nat.add(2n, Nat.add(H, Nat.add(1n+R, W0)))), X)) == True{} : Bool}

def ar_r(A, H, W0, R, X):
  +R1 = Nat.add(R, 1n)
  +Q = Nat.add(A, Nat.add(2n, Nat.add(H, W0)))
  +Q2 = Nat.add(A, Nat.add(2n, Nat.add(H, Nat.add(1n+R, W0))))
  # (Q + X) + R1 = (Q + R1) + X
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Q, X), R1), Nat.add(Q, Nat.add(X, R1)), Nat.add(Nat.add(Q, R1), X),
    N.add_assoc(Q, X, R1),
    Equal.trans(Nat, Nat.add(Q, Nat.add(X, R1)), Nat.add(Q, Nat.add(R1, X)), Nat.add(Nat.add(Q, R1), X),
      Equal.cong(Nat, Nat, z => Nat.add(Q, z), Nat.add(X, R1), Nat.add(R1, X), N.add_comm(X, R1)),
      Equal.sym(Nat, Nat.add(Nat.add(Q, R1), X), Nat.add(Q, Nat.add(R1, X)), N.add_assoc(Q, R1, X))))
  # Q + R1 = Q2
  +eW = Equal.trans(Nat, Nat.add(W0, R1), Nat.add(R1, W0), Nat.add(1n+R, W0), N.add_comm(W0, R1),
    Equal.cong(Nat, Nat, z => Nat.add(z, W0), R1, 1n+R, N.add_one(R)))
  +eH = Equal.trans(Nat, Nat.add(Nat.add(H, W0), R1), Nat.add(H, Nat.add(W0, R1)), Nat.add(H, Nat.add(1n+R, W0)),
    N.add_assoc(H, W0, R1), Equal.cong(Nat, Nat, z => Nat.add(H, z), Nat.add(W0, R1), Nat.add(1n+R, W0), eW))
  +e2n = Equal.trans(Nat, Nat.add(Nat.add(2n, Nat.add(H, W0)), R1), Nat.add(2n, Nat.add(Nat.add(H, W0), R1)), Nat.add(2n, Nat.add(H, Nat.add(1n+R, W0))),
    N.add_assoc(2n, Nat.add(H, W0), R1), Equal.cong(Nat, Nat, z => Nat.add(2n, z), Nat.add(Nat.add(H, W0), R1), Nat.add(H, Nat.add(1n+R, W0)), eH))
  +e2 = Equal.trans(Nat, Nat.add(Q, R1), Nat.add(A, Nat.add(Nat.add(2n, Nat.add(H, W0)), R1)), Q2,
    N.add_assoc(A, Nat.add(2n, Nat.add(H, W0)), R1), Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(Nat.add(2n, Nat.add(H, W0)), R1), Nat.add(2n, Nat.add(H, Nat.add(1n+R, W0))), e2n))
  +e = Equal.trans(Nat, Nat.add(Nat.add(Q, X), R1), Nat.add(Nat.add(Q, R1), X), Nat.add(Q2, X), e1,
    Equal.cong(Nat, Nat, z => Nat.add(z, X), Nat.add(Q, R1), Q2, e2))
  %e : {Nat.is_le(Nat.add(Nat.add(Q, X), R1), _) == True{} : Bool}
  N.le_refl(Nat.add(Nat.add(Q, X), R1))

# The batch's first piece: Q's state handed out as is (out), the piece held.
law wrap_col1:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +W0: Nat
  for s: Norm.Step
  for +hch: {NR.chars(D.view(E.enc(c))) == c : String}
  for h: BDs.BudS(fa, T, c <> cs, O, W0, s)
  ST.BudW(fa, T, cs, False{}, O, Nat.add(Nat.add(ST.VQ(T, c <> cs, False{}, O, W0), Nat.add(BD.kx(1n), 4n)), BD.XK(cs)), W.wrap(s, W.BCol{[E.enc(c)], 1n}))

def wrap_col1(fa, T, c, cs, O, W0, s, hch, h):
  match s:
    case Norm.Step{st, b, +ns, +nx}:
      (hbi, k) = h
      hnf => (%Equal.sym(String, NR.chars(D.view(E.enc(c))), c, hch) : {BN.biS(st, _ <> cs) == True{} : Bool}; hbi,
        +t => hout => hp => +n => en => %en : {Nat.is_le(_, Nat.add(Nat.add(ST.VQ(T, c <> cs, False{}, O, W0), Nat.add(BD.kx(1n), 4n)), BD.XK(cs))) == True{} : Bool};
          %Equal.sym(String, NR.chars(D.view(E.enc(c))), c, hch) :
            {Nat.is_le(Nat.add(Nat.add(BN.needS(fa, T, st, _ <> cs, False{}, nx, String.append(O, t)), Nat.add(BD.kx(1n), 4n)), BD.XK(cs)), Nat.add(Nat.add(ST.VQ(T, c <> cs, False{}, O, W0), Nat.add(BD.kx(1n), 4n)), BD.XK(cs))) == True{} : Bool}
          ST.needs_le2(fa, T, c <> cs, False{}, O, W0, st, nx, String.append(O, t), Nat.add(BD.kx(1n), 4n), BD.XK(cs), k(t, hout, hp), ST.name_was(fa, st, c <> cs)))

# Q's step from a state waiting for more: phase B's budget, with no batch.
# ======================================================================

law none_chunk.if:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  for +q: Bool
  for +hq: {Bool.and(QB.qb(p), U32.is_le(256, U32.from_nat(String.length(c)))) == q : Bool}
  API.KontW(fa, T, W.none.chunk((S.mkSt(fa, p), q), E.enc(c)), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), c <> cs, False{}, Pr.More{}, O), O, N)

def none_chunk.if(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn, q, hq):
  match q:
    case False{}:
      +W0 = BDs.WP(fa, c <> cs, p)
      +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), c <> cs, False{}, Pr.More{}, O)
      ST.kont_of(fa, T, W.wrap(Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}), W.BNone{}), cs, False{}, 0n, n1, Nat.add(ST.VQ(T, cs, False{}, O, W0), BD.XK(cs)), O, N,
        ST.wrap_none(fa, T, cs, False{}, O, W0, Norm.step(S.mkSt(fa, p), Pr.Chunk{E.enc(c)}),
          BS.fed_bud(fa, T, cs, O, N, W0, Norm.feed(S.mkSt(fa, p), E.enc(c)), hb, BS.chunk_fed(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn))),
        ar_q(ST.VQ(T, cs, False{}, O, W0), BD.XK(cs), BN.pick(BD.big(c), 12n)))
    case True{}:
      +W0 = BDs.WP(fa, c <> cs, p)
      +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), c <> cs, False{}, Pr.More{}, O)
      +hbig = big_of(c, hcb, hcn, PB.and_true_r(QB.qb(p), U32.is_le(256, U32.from_nat(String.length(c))), hq))
      +Vq = ST.VQ(T, c <> cs, False{}, O, W0)
      ST.kont_of(fa, T, W.wrap(Norm.out(S.mkSt(fa, p), Pr.More{}), W.BCol{[E.enc(c)], 1n}), cs, False{}, 0n, n1, Nat.add(Nat.add(Vq, Nat.add(BD.kx(1n), 4n)), BD.XK(cs)), O, N,
        wrap_col1(fa, T, c, cs, O, W0, Norm.out(S.mkSt(fa, p), Pr.More{}), chars_enc(c, hcb, hcn),
          BS.out_bud(fa, T, c <> cs, O, p, Pr.More{}, W0, hbi, N.le_refl(W0))),
        %Equal.sym(Bool, BD.big(c), True{}, hbig) : {Nat.is_le(Nat.add(Nat.add(Nat.add(Vq, 11n), BD.XK(cs)), Nat.add(0n, 1n)), Nat.add(Vq, Nat.add(BN.pick(_, 12n), BD.XK(cs)))) == True{} : Bool};
        ar_c(Vq, BD.XK(cs)))

law none_chunk:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +c: String
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, c <> cs, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), c <> cs) == True{} : Bool}
  for +hcb: {E.is_bytes(c) == True{} : Bool}
  for +hcn: {P.le31(String.length(c)) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), Pr.Chunk{E.enc(c)}), cs, False{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), c <> cs, False{}, Pr.More{}, O), O, N)

def none_chunk(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn):
  +n1 = BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), c <> cs, False{}, Pr.More{}, O)
  %QB.quiet_mk(fa, p) : API.KontW(fa, T, W.none.len(_, BY.len(E.enc(c))), cs, False{}, 0n, n1, O, N)
  %Equal.sym(D.Bytes & U32, BY.len(E.enc(c)), (E.enc(c), U32.from_nat(String.length(c))), len_enc(c)) : API.KontW(fa, T, W.none.len((S.mkSt(fa, p), QB.qb(p)), _), cs, False{}, 0n, n1, O, N)
  none_chunk.if(fa, T, c, cs, O, N, p, hb, hm, hr, hg, hbi, hcb, hcn, Bool.and(QB.qb(p), U32.is_le(256, U32.from_nat(String.length(c)))), {==})

law none_eof:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, Nil{}, O, N, p) == T : R.Report}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), Nil{}) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), Pr.Eof{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), Nil{}, False{}, Pr.More{}, O), O, N)

def none_eof(fa, T, O, N, p, hb, hm, hr, hg, hbi):
  +W0 = BDs.WP(fa, Nil{}, p)
  ST.kont_of(fa, T, W.wrap(Norm.step(S.mkSt(fa, p), Pr.Eof{}), W.BNone{}), Nil{}, True{}, 0n, BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), Nil{}, False{}, Pr.More{}, O), Nat.add(ST.VQ(T, Nil{}, True{}, O, W0), 0n), O, N,
    ST.wrap_none(fa, T, Nil{}, True{}, O, W0, Norm.step(S.mkSt(fa, p), Pr.Eof{}),
      BS.fed_bud(fa, T, Nil{}, O, N, W0, Norm.feed_eof(S.mkSt(fa, p)), hb, BS.eof_fed(fa, T, O, N, p, hb, hm, hr, hg, hbi))),
    ar_e(Nat.add(2n, Nat.add(BN.HO(T, O), W0))))

law none_ref:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +p: S.StP
  for +rs: List<&2, Pr.Req>
  for +ef: Bool
  for +hb: {PC.fa_bytes(fa) == True{} : Bool}
  for +hw: {S.WF(fa, p) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, p) == T : R.Report}
  for +ha: {S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}
  for +hq: {E.reqs_ok(rs) == True{} : Bool}
  for +hp: {rs == S.rq(rs) : List<&2, Pr.Req>}
  for +hmr: {S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}
  for +hg: {S.guard(O, N, p) == True{} : Bool}
  for +hbi: {BN.biS(S.mkSt(fa, p), cs) == True{} : Bool}
  API.KontW(fa, T, W.step(WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), Pr.Ref{M.truths(fa, rs)}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), cs, ef, Pr.Ask{rs}, O), O, N)

def none_ref(fa, T, cs, O, N, p, rs, ef, hb, hw, hr, ha, hq, hp, hmr, hg, hbi):
  +W0 = BDs.WP(fa, cs, p)
  ST.kont_of(fa, T, W.wrap(Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}), W.BNone{}), cs, ef, List.length(&2, Pr.Req, rs), BD.needW(fa, T, WD.mkWSt(fa, WD.WPic{p, WD.BNoneP{}}), cs, ef, Pr.Ask{rs}, O), Nat.add(ST.VQ(T, cs, ef, O, W0), BD.XK(cs)), O, N,
    ST.wrap_none(fa, T, cs, ef, O, W0, Norm.step(S.mkSt(fa, p), Pr.Ref{M.truths(fa, rs)}),
      BS.fed_bud(fa, T, cs, O, N, W0, Norm.set_win(S.mkSt(fa, p), M.truths(fa, rs)), hb, BS.ref_fed(fa, T, cs, rs, O, N, p, hb, hw, hr, ha, hq, hp, hmr, hg, hbi))),
    ar_r(Nat.add(List.length(&2, String, cs), BN.pick(Bool.not(ef), 1n)), BN.HO(T, O), W0, List.length(&2, Pr.Req, rs), BD.XK(cs)))
