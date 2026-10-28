import Base
import ./proof_c_tan_lists.bend as TL
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U

# Phase C, area "tan": the index arithmetic of NX.el, on Nat. p: POS, k:
# shifts, o: the window's first contig index, w: the window's length, j: a
# byte of R_k ++ a; s, l: an allele's start and length in a line of b bytes.
# R_k starts at window index ((p - 1) - k) - o.

law le_cancel_l:
  for c: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_le(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}
  {Nat.is_le(x, y) == True{} : Bool}

def le_cancel_l(c, x, y, h):
  match c:
    case 0n:
      h
    case 1n+q:
      le_cancel_l(q, x, y, h)

law lt_cancel_l:
  for c: Nat
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(Nat.add(c, x), Nat.add(c, y)) == True{} : Bool}
  {Nat.is_lt(x, y) == True{} : Bool}

def lt_cancel_l(c, x, y, h):
  match c:
    case 0n:
      h
    case 1n+q:
      lt_cancel_l(q, x, y, h)

law sub_le_self:
  for +x: Nat
  for +y: Nat
  {Nat.is_le(Nat.sub(x, y), x) == True{} : Bool}

def sub_le_self(x, y):
  U.sub_le(x, y)

law one_le:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(1n, p) == True{} : Bool}

def one_le(k, o, p, hk):
  N.le_trans(1n, Nat.add(Nat.add(k, o), 1n), p, N.le_add_l(1n, Nat.add(k, o)), hk)

# Window
# ======

law wk1:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(Nat.add(k, o), Nat.sub(p, 1n)) == True{} : Bool}

def wk1(k, o, p, hk):
  TL.le_sub(1n, Nat.add(k, o), p,
    %N.add_one(Nat.add(k, o)) : {Nat.is_le(_, p) == True{} : Bool}
    hk)

law wk2:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(k, Nat.sub(p, 1n)) == True{} : Bool}

def wk2(k, o, p, hk):
  N.le_trans(k, Nat.add(k, o), Nat.sub(p, 1n), N.le_add_r(k, o), wk1(k, o, p, hk))

law wk3:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(o, Nat.sub(Nat.sub(p, 1n), k)) == True{} : Bool}

def wk3(k, o, p, hk):
  TL.le_sub(k, o, Nat.sub(p, 1n), wk1(k, o, p, hk))

# ((p - 1) - k) + k = p - 1.
law wk_back:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.add(Nat.sub(Nat.sub(p, 1n), k), k) == Nat.sub(p, 1n) : Nat}

def wk_back(k, o, p, hk):
  TL.sub_add_id(Nat.sub(p, 1n), k, wk2(k, o, p, hk))

law wk4:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +j: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  for +hj: {Nat.is_lt(j, k) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.sub(Nat.sub(p, 1n), k), j), p) == True{} : Bool}

def wk4(k, o, p, j, hk, hj):
  +A2 = Nat.sub(Nat.sub(p, 1n), k)
  N.le_trans(Nat.add(A2, j), Nat.add(A2, k), p, N.le_add_mono_l(A2, j, k, N.lt_to_le(j, k, hj)),
    %Equal.sym(Nat, Nat.add(A2, k), Nat.sub(p, 1n), wk_back(k, o, p, hk)) : {Nat.is_le(_, p) == True{} : Bool}
    sub_le_self(p, 1n))

law wk5:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +j: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(o, Nat.add(Nat.sub(Nat.sub(p, 1n), k), j)) == True{} : Bool}

def wk5(k, o, p, j, hk):
  +A2 = Nat.sub(Nat.sub(p, 1n), k)
  N.le_trans(o, A2, Nat.add(A2, j), wk3(k, o, p, hk), N.le_add_r(A2, j))

law wk6:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +j: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.sub(Nat.add(Nat.sub(Nat.sub(p, 1n), k), j), o) == Nat.add(Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o), j) : Nat}

def wk6(k, o, p, j, hk):
  TL.add_sub_r(Nat.sub(Nat.sub(p, 1n), k), o, j, wk3(k, o, p, hk))

# R_k fits in the window.
law wk8:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +w: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(p, 1n), Nat.add(o, w)) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o), k), w) == True{} : Bool}

def wk8(k, o, p, w, hk, ho):
  +A2 = Nat.sub(Nat.sub(p, 1n), k)
  +B0 = Nat.sub(A2, o)
  le_cancel_l(o, Nat.add(B0, k), w,
    %N.add_assoc(o, B0, k) : {Nat.is_le(_, Nat.add(o, w)) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(o, B0), A2, N.le_sub_add(o, A2, wk3(k, o, p, hk))) : {Nat.is_le(Nat.add(_, k), Nat.add(o, w)) == True{} : Bool}
    %Equal.sym(Nat, Nat.add(A2, k), Nat.sub(p, 1n), wk_back(k, o, p, hk)) : {Nat.is_le(_, Nat.add(o, w)) == True{} : Bool}
    ho)

law wk7:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +w: Nat
  for +j: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  for +ho: {Nat.is_le(Nat.sub(p, 1n), Nat.add(o, w)) == True{} : Bool}
  for +hj: {Nat.is_lt(j, k) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o), j), w) == True{} : Bool}

def wk7(k, o, p, w, j, hk, ho, hj):
  +B0 = Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o)
  N.lt_le_trans(Nat.add(B0, j), Nat.add(B0, k), w, N.lt_add_l(B0, j, k, hj), wk8(k, o, p, w, hk, ho))

# Line
# ====

law ln1:
  for +s: Nat
  for +l: Nat
  for +b: Nat
  for +j: Nat
  for +hin: {Nat.is_le(Nat.add(s, l), b) == True{} : Bool}
  for +hj: {Nat.is_lt(j, l) == True{} : Bool}
  {Nat.is_le(Nat.add(s, j), b) == True{} : Bool}

def ln1(s, l, b, j, hin, hj):
  N.le_trans(Nat.add(s, j), Nat.add(s, l), b, N.le_add_mono_l(s, j, l, N.lt_to_le(j, l, hj)), hin)

law ln2:
  for +s: Nat
  for +j: Nat
  for +k: Nat
  for +hkj: {Nat.is_le(k, j) == True{} : Bool}
  {Nat.is_le(k, Nat.add(s, j)) == True{} : Bool}

def ln2(s, j, k, hkj):
  N.le_trans(k, j, Nat.add(s, j), hkj, N.le_add_l(j, s))

law ln3:
  for +s: Nat
  for +j: Nat
  for +k: Nat
  for +hkj: {Nat.is_le(k, j) == True{} : Bool}
  {Nat.sub(Nat.add(s, j), k) == Nat.add(s, Nat.sub(j, k)) : Nat}

def ln3(s, j, k, hkj):
  %N.add_comm(j, s) : {Nat.sub(_, k) == Nat.add(s, Nat.sub(j, k)) : Nat}
  %N.add_comm(Nat.sub(j, k), s) : {Nat.sub(Nat.add(j, s), k) == _ : Nat}
  TL.add_sub_r(j, k, s, hkj)

law ln4:
  for +l: Nat
  for +j: Nat
  for +k: Nat
  for +hj: {Nat.is_lt(j, l) == True{} : Bool}
  {Nat.is_lt(Nat.sub(j, k), l) == True{} : Bool}

def ln4(l, j, k, hj):
  N.le_lt_trans(Nat.sub(j, k), j, l, sub_le_self(j, k), hj)

law ln5:
  for +s: Nat
  for +l: Nat
  for +b: Nat
  for +j: Nat
  for +k: Nat
  for +hin: {Nat.is_le(Nat.add(s, l), b) == True{} : Bool}
  for +hj: {Nat.is_lt(j, l) == True{} : Bool}
  {Nat.is_lt(Nat.sub(Nat.add(s, j), k), b) == True{} : Bool}

def ln5(s, l, b, j, k, hin, hj):
  N.le_lt_trans(Nat.sub(Nat.add(s, j), k), Nat.add(s, j), b, sub_le_self(Nat.add(s, j), k),
    N.lt_le_trans(Nat.add(s, j), Nat.add(s, l), b, N.lt_add_l(s, j, l, hj), hin))

# Shift
# =====

# y - 1 + 1 = y when 1 <= y.
law pred_succ:
  for +y: Nat
  for +h: {Nat.is_le(1n, y) == True{} : Bool}
  {Nat.add(Nat.sub(y, 1n), 1n) == y : Nat}

def pred_succ(y, h):
  TL.sub_add_id(y, 1n, h)

# y - 2 + 1 = y - 1 when 2 <= y.
law pred2_succ:
  for +y: Nat
  for +h: {Nat.is_le(2n, y) == True{} : Bool}
  {Nat.add(Nat.sub(y, 2n), 1n) == Nat.sub(y, 1n) : Nat}

def pred2_succ(y, h):
  %TL.sub_sub(y, 1n, 1n) : {Nat.add(_, 1n) == Nat.sub(y, 1n) : Nat}
  pred_succ(Nat.sub(y, 1n), TL.le_sub(1n, 1n, y, h))

# (p - k) - 1 = (p - 1) - k.
law sub_swap1:
  for +p: Nat
  for +k: Nat
  {Nat.sub(Nat.sub(p, k), 1n) == Nat.sub(Nat.sub(p, 1n), k) : Nat}

def sub_swap1(p, k):
  %Equal.sym(Nat, Nat.sub(Nat.sub(p, k), 1n), Nat.sub(p, Nat.add(k, 1n)), TL.sub_sub(p, k, 1n)) : {_ == Nat.sub(Nat.sub(p, 1n), k) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(p, 1n), k), Nat.sub(p, Nat.add(1n, k)), TL.sub_sub(p, 1n, k)) : {Nat.sub(p, Nat.add(k, 1n)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+k, N.add_one(k)) : {Nat.sub(p, _) == Nat.sub(p, 1n+k) : Nat}
  {==}

# R_{k+1} starts where the shift reads: ((p - 1) - (k + 1)) - o = ((p - k) - 2) - o.
law sh_b0:
  for +p: Nat
  for +k: Nat
  for +o: Nat
  {Nat.sub(Nat.sub(Nat.sub(p, 1n), Nat.add(k, 1n)), o) == Nat.sub(Nat.sub(Nat.sub(p, k), 2n), o) : Nat}

def sh_b0(p, k, o):
  %Equal.sym(Nat, Nat.sub(Nat.sub(p, 1n), Nat.add(k, 1n)), Nat.sub(p, Nat.add(1n, Nat.add(k, 1n))), TL.sub_sub(p, 1n, Nat.add(k, 1n))) :
    {Nat.sub(_, o) == Nat.sub(Nat.sub(Nat.sub(p, k), 2n), o) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(p, k), 2n), Nat.sub(p, Nat.add(k, 2n)), TL.sub_sub(p, k, 2n)) :
    {Nat.sub(Nat.sub(p, Nat.add(1n, Nat.add(k, 1n))), o) == Nat.sub(_, o) : Nat}
  %Equal.sym(Nat, Nat.add(k, 2n), 1n+Nat.add(k, 1n), N.add_succ(k, 1n)) : {Nat.sub(Nat.sub(p, Nat.add(1n, Nat.add(k, 1n))), o) == Nat.sub(Nat.sub(p, _), o) : Nat}
  {==}

# ... and R_k starts one later.
law sh_b1:
  for +p: Nat
  for +k: Nat
  for +o: Nat
  for +h2: {Nat.is_le(2n, Nat.sub(p, k)) == True{} : Bool}
  for +ho: {Nat.is_le(o, Nat.sub(Nat.sub(p, k), 2n)) == True{} : Bool}
  {Nat.add(Nat.sub(Nat.sub(Nat.sub(p, k), 2n), o), 1n) == Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o) : Nat}

def sh_b1(p, k, o, h2, ho):
  +x = Nat.sub(Nat.sub(p, k), 2n)
  %TL.add_sub_r(x, o, 1n, ho) :
    {_ == Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n), Nat.sub(Nat.sub(p, k), 1n), pred2_succ(Nat.sub(p, k), h2)) :
    {Nat.sub(_, o) == Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.sub(p, k), 1n), Nat.sub(Nat.sub(p, 1n), k), sub_swap1(p, k)) :
    {Nat.sub(_, o) == Nat.sub(Nat.sub(Nat.sub(p, 1n), k), o) : Nat}
  {==}

# The letter a shift reads is in the window.
law sh_lt:
  for +p: Nat
  for +k: Nat
  for +o: Nat
  for +w: Nat
  for +h2: {Nat.is_le(2n, Nat.sub(p, k)) == True{} : Bool}
  for +ho: {Nat.is_le(o, Nat.sub(Nat.sub(p, k), 2n)) == True{} : Bool}
  for +hw: {Nat.is_le(Nat.sub(p, 1n), Nat.add(o, w)) == True{} : Bool}
  {Nat.is_lt(Nat.sub(Nat.sub(Nat.sub(p, k), 2n), o), w) == True{} : Bool}

def sh_lt(p, k, o, w, h2, ho, hw):
  +x = Nat.sub(Nat.sub(p, k), 2n)
  +hx = N.le_trans(Nat.add(x, 1n), Nat.sub(p, 1n), Nat.add(o, w),
    %Equal.sym(Nat, Nat.add(x, 1n), Nat.sub(Nat.sub(p, k), 1n), pred2_succ(Nat.sub(p, k), h2)) : {Nat.is_le(_, Nat.sub(p, 1n)) == True{} : Bool}
    %Equal.sym(Nat, Nat.sub(Nat.sub(p, k), 1n), Nat.sub(Nat.sub(p, 1n), k), sub_swap1(p, k)) : {Nat.is_le(_, Nat.sub(p, 1n)) == True{} : Bool}
    sub_le_self(Nat.sub(p, 1n), k), hw)
  lt_cancel_l(o, Nat.sub(x, o), w,
    %Equal.sym(Nat, Nat.add(o, Nat.sub(x, o)), x, N.le_sub_add(o, x, ho)) : {Nat.is_lt(_, Nat.add(o, w)) == True{} : Bool}
    TL.le_succ_lt(x, Nat.add(o, w), hx))

# 1 <= p - k gives k <= p.
law pos_sub_le:
  for p: Nat
  for k: Nat
  for +h: {Nat.is_le(1n, Nat.sub(p, k)) == True{} : Bool}
  {Nat.is_le(k, p) == True{} : Bool}

def pos_sub_le(p, k, h):
  match p k:
    case 0n _:
      Empty.absurd({Nat.is_le(k, 0n) == True{} : Bool}, N.false_ne_true(h))
    case 1n+q 0n:
      {==}
    case 1n+q 1n+r:
      pos_sub_le(q, r, h)

# After a shift, R_{k+1} still lies after the window's start.
law sh_kok:
  for +p: Nat
  for +k: Nat
  for +o: Nat
  for +h2: {Nat.is_le(2n, Nat.sub(p, k)) == True{} : Bool}
  for +ho: {Nat.is_le(o, Nat.sub(Nat.sub(p, k), 2n)) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Nat.add(k, 1n), o), 1n), p) == True{} : Bool}

def sh_kok(p, k, o, h2, ho):
  +x = Nat.sub(p, k)
  +ho2 = N.le_trans(Nat.add(o, 2n), Nat.add(Nat.sub(x, 2n), 2n), x, N.le_add_mono_r(2n, o, Nat.sub(x, 2n), ho),
    %Equal.sym(Nat, Nat.add(Nat.sub(x, 2n), 2n), x, TL.sub_add_id(x, 2n, h2)) : {Nat.is_le(_, x) == True{} : Bool}
    N.le_refl(x))
  %Equal.sym(Nat, Nat.add(Nat.add(k, 1n), o), Nat.add(k, Nat.add(1n, o)), N.add_assoc(k, 1n, o)) :
    {Nat.is_le(Nat.add(_, 1n), p) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(k, Nat.add(1n, o)), 1n), Nat.add(k, Nat.add(Nat.add(1n, o), 1n)), N.add_assoc(k, Nat.add(1n, o), 1n)) :
    {Nat.is_le(_, p) == True{} : Bool}
  %N.add_succ(o, 1n) : {Nat.is_le(Nat.add(k, _), p) == True{} : Bool}
  TL.sub_le_add(k, Nat.add(o, 2n), p, pos_sub_le(p, k, N.le_trans(1n, 2n, x, {==}, h2)), ho2)

law kok_lt:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_lt(k, p) == True{} : Bool}

def kok_lt(k, o, p, hk):
  TL.le_succ_lt(k, p, N.le_trans(Nat.add(k, 1n), Nat.add(Nat.add(k, o), 1n), p, N.le_add_mono_r(1n, k, Nat.add(k, o), N.le_add_r(k, o)), hk))

law kok_le:
  for +k: Nat
  for +o: Nat
  for +p: Nat
  for +hk: {Nat.is_le(Nat.add(Nat.add(k, o), 1n), p) == True{} : Bool}
  {Nat.is_le(k, p) == True{} : Bool}

def kok_le(k, o, p, hk):
  N.lt_to_le(k, p, kok_lt(k, o, p, hk))

# a + c < b gives c < b - a.
law lt_sub:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for +h: {Nat.is_lt(Nat.add(a, c), b) == True{} : Bool}
  {Nat.is_lt(c, Nat.sub(b, a)) == True{} : Bool}

def lt_sub(a, c, b, h):
  TL.le_succ_lt(c, Nat.sub(b, a), TL.le_sub(a, Nat.add(c, 1n), b,
    %N.add_assoc(a, c, 1n) : {Nat.is_le(_, b) == True{} : Bool}
    TL.lt_succ_le(Nat.add(a, c), b, h)))

# A left trim keeps every allele one base or more long.
law kl_step:
  for +t: Nat
  for +d: Nat
  for +l: Nat
  for +h1: {Nat.is_lt(Nat.add(t, d), l) == True{} : Bool}
  for +h2: {Nat.is_le(2n, Nat.sub(Nat.sub(l, t), d)) == True{} : Bool}
  {Nat.is_lt(Nat.add(t, Nat.add(1n, d)), l) == True{} : Bool}

def kl_step(t, d, l, h1, h2):
  +hd = TL.le_sub(t, d, l, N.lt_to_le(Nat.add(t, d), l, h1))
  +h3 = TL.sub_le_add(d, 2n, Nat.sub(l, t), hd, h2)
  +htl = N.le_trans(t, Nat.add(t, d), l, N.le_add_r(t, d), N.lt_to_le(Nat.add(t, d), l, h1))
  +h4 = TL.sub_le_add(t, Nat.add(d, 2n), l, htl, h3)
  TL.le_succ_lt(Nat.add(t, Nat.add(1n, d)), l,
    %Equal.sym(Nat, Nat.add(Nat.add(t, Nat.add(1n, d)), 1n), Nat.add(t, Nat.add(Nat.add(1n, d), 1n)), N.add_assoc(t, Nat.add(1n, d), 1n)) :
      {Nat.is_le(_, l) == True{} : Bool}
    %N.add_succ(d, 1n) : {Nat.is_le(Nat.add(t, _), l) == True{} : Bool}
    h4)

# The long flag of a right trim: 2 <= l - t - d on words.
law u_long:
  for +ln: U32
  for +tr: U32
  for +d: Nat
  for +h: {Nat.is_lt(Nat.add(U32.to_nat(tr), d), U32.to_nat(ln)) == True{} : Bool}
  {U32.is_le(2, ((ln - tr : U32) - U32.from_nat(d) : U32)) == Nat.is_le(2n, Nat.sub(Nat.sub(U32.to_nat(ln), U32.to_nat(tr)), d)) : Bool}

def u_long(ln, tr, d, h):
  +l = U32.to_nat(ln)
  +t = U32.to_nat(tr)
  +lt = (ln - tr : U32)
  +hdl = N.le_lt_trans(d, Nat.add(t, d), l, N.le_add_l(d, t), h)
  +E1 = TL.u_sub(ln, tr, N.le_trans(t, Nat.add(t, d), l, N.le_add_r(t, d), N.lt_to_le(Nat.add(t, d), l, h)))
  +Ed = TL.u_from(d, ln, hdl)
  +E2 = TL.u_sub(lt, U32.from_nat(d),
    %Equal.sym(Nat, U32.to_nat(U32.from_nat(d)), d, Ed) : {Nat.is_le(_, U32.to_nat(lt)) == True{} : Bool}
    %Equal.sym(Nat, U32.to_nat(lt), Nat.sub(l, t), E1) : {Nat.is_le(d, _) == True{} : Bool}
    TL.le_sub(t, d, l, N.lt_to_le(Nat.add(t, d), l, h)))
  %Equal.sym(Bool, U32.is_le(2, (lt - U32.from_nat(d) : U32)), Nat.is_le(2n, U32.to_nat((lt - U32.from_nat(d) : U32))), TL.u_le(2, (lt - U32.from_nat(d) : U32))) : {_ == Nat.is_le(2n, Nat.sub(Nat.sub(l, t), d)) : Bool}
  %Equal.sym(Nat, U32.to_nat((lt - U32.from_nat(d) : U32)), Nat.sub(U32.to_nat(lt), U32.to_nat(U32.from_nat(d))), E2) :
    {Nat.is_le(2n, _) == Nat.is_le(2n, Nat.sub(Nat.sub(l, t), d)) : Bool}
  %Equal.sym(Nat, U32.to_nat(lt), Nat.sub(l, t), E1) :
    {Nat.is_le(2n, Nat.sub(_, U32.to_nat(U32.from_nat(d)))) == Nat.is_le(2n, Nat.sub(Nat.sub(l, t), d)) : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.from_nat(d)), d, Ed) :
    {Nat.is_le(2n, Nat.sub(Nat.sub(l, t), _)) == Nat.is_le(2n, Nat.sub(Nat.sub(l, t), d)) : Bool}
  {==}
