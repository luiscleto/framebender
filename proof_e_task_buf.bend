import Base
import ./protocol.bend as Pr
import ./norm_seq.bend as Q
import ./norm.bend as W
import ./bytes_enc.bend as E
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/fast.bend as F
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_bytes.bend as WB
import ./proof_b_fasteq.bend as FE
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area D (task): the plan's reads of a piece's buffer hand the
# buffer back, whatever the indices, and every text they read is bytes. (The
# plan's last line, POS digits and reads need nothing more.)

# Any byte read is below 256.
def at_lt(+len: U32, +t: AT.Tree<U32>, +i: U32) -> {U32.is_lt(C.AT(len, t, i), 256) == True{} : Bool}:
  +k = (i >> 2n : U32)
  %Equal.sym(Array<U32> & U32, Array.get(U32, AT.fromT(U32, t), k), (AT.fromT(U32, t), C.WD(t, k)), AT.get_pair_t(U32, t, k)) :
    {U32.is_lt(Pair.snd(D.Bytes, U32, BY.at.fin(len, i, _)), 256) == True{} : Bool}
  WB.byte_lt(C.WD(t, k), U32.to_nat((i .&. 3 : U32)))

# Bytes read as a list are bytes.
def tl_bytes(+n: Nat, +len: U32, +t: AT.Tree<U32>, +s: U32) ->
  {D.all_bytes(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.go(n, BY.at(C.BT(len, t), s), s))) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), s), (C.BT(len, t), C.AT(len, t, s)), C.at_pair_t(len, t, s)) :
        {D.all_bytes(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.go(0n, _, s))) == True{} : Bool}
      {==}
    case 1n+m:
      +s1 = (s + 1 : U32)
      +x = C.AT(len, t, s)
      +G = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.go(m, BY.at(C.BT(len, t), s1), s1))
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), s), (C.BT(len, t), x), C.at_pair_t(len, t, s)) :
        {D.all_bytes(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.go(1n+m, _, s))) == True{} : Bool}
      %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list.go(m, BY.at(C.BT(len, t), s1), s1), (C.BT(len, t), G), SM.tl_pair(m, len, t, s1)) :
        {D.all_bytes(Pair.snd(D.Bytes, List<&2, U32>, BY.to_list.cons(x, _))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_lt(x, 256), True{}, at_lt(len, t, s)) : {Bool.and(_, D.all_bytes(G)) == True{} : Bool}
      tl_bytes(m, len, t, s1)

def andl(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def andr(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, N.false_ne_true(h))

# Norm.chars of bytes is bytes.
def chars_bytes(+ys: List<&2, U32>, +h: {D.all_bytes(ys) == True{} : Bool}) -> {E.is_bytes(Q.chars(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(Bool, U32.is_lt(y, 256), True{}, andl(U32.is_lt(y, 256), D.all_bytes(r), h)) : {Bool.and(_, E.is_bytes(Q.chars(r))) == True{} : Bool}
      chars_bytes(r, andr(U32.is_lt(y, 256), D.all_bytes(r), h))

# Q.text hands the buffer back; its text is bytes.
def text_b(+len: U32, +t: AT.Tree<U32>, +s: U32, +n: U32) ->
  &x: String -> ({Q.text(C.BT(len, t), s, n) == (C.BT(len, t), x) : D.Bytes & String} & {E.is_bytes(x) == True{} : Bool}):
  +Y = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(len, t), s, n))
  +e = {
    %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(len, t), s, n), (C.BT(len, t), Y), SM.to_list_pair_t(len, t, s, n)) :
      {Q.text.k(_) == (C.BT(len, t), Q.chars(Y)) : D.Bytes & String}
    {==} : {Q.text(C.BT(len, t), s, n) == (C.BT(len, t), Q.chars(Y)) : D.Bytes & String}}
  (Q.chars(Y), (e, chars_bytes(Y, tl_bytes(U32.to_nat(n), len, t, s))))

# ---------------------------------------------------------------------------
# num, rlf, cp: the buffer comes back
# ---------------------------------------------------------------------------

def dig(+x: U32) -> Bool:
  U32.is_le(48, x) && U32.is_le(x, 57)

# num.step.if's result, field by field.
def NJ(+more: Bool, +j: U32) -> U32:
  match more:
    case True{}:
      (j + 1 : U32)
    case False{}:
      j

def NA(+more: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32, +acc: U32) -> U32:
  match more:
    case True{}:
      Bool.pick(U32, dig(C.AT(len, t, j)), ((acc * 10 : U32) + (C.AT(len, t, j) - 48 : U32) : U32), acc)
    case False{}:
      acc

def NM(+more: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32) -> Bool:
  match more:
    case True{}:
      dig(C.AT(len, t, j))
    case False{}:
      False{}

def nstep.if(+more: Bool, +len: U32, +t: AT.Tree<U32>, +j: U32, +acc: U32) ->
  {W.num.step.if(more, C.BT(len, t), j, acc) == W.Nm{C.BT(len, t), NJ(more, j), NA(more, len, t, j, acc), NM(more, len, t, j)} : W.Nm}:
  match more:
    case True{}:
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), j), (C.BT(len, t), C.AT(len, t, j)), C.at_pair_t(len, t, j)) :
        {W.num.byte(_, j, acc) == W.Nm{C.BT(len, t), NJ(True{}, j), NA(True{}, len, t, j, acc), NM(True{}, len, t, j)} : W.Nm}
      {==}
    case False{}:
      {==}

def NG(+f: Nat, +len: U32, +t: AT.Tree<U32>, +j: U32, +acc: U32, +m: Bool, +e: U32) -> U32:
  Pair.snd(D.Bytes, U32, W.num.go(f, W.Nm{C.BT(len, t), j, acc, m}, e))

def ngo(+f: Nat, +len: U32, +t: AT.Tree<U32>, +j: U32, +acc: U32, +m: Bool, +e: U32) ->
  {W.num.go(f, W.Nm{C.BT(len, t), j, acc, m}, e) == (C.BT(len, t), NG(f, len, t, j, acc, m, e)) : D.Bytes & U32}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match m:
        case False{}:
          {==}
        case True{}:
          +mo = U32.is_lt(j, e)
          %Equal.sym(W.Nm, W.num.step.if(mo, C.BT(len, t), j, acc), W.Nm{C.BT(len, t), NJ(mo, j), NA(mo, len, t, j, acc), NM(mo, len, t, j)}, nstep.if(mo, len, t, j, acc)) :
            {W.num.go(g, _, e) == (C.BT(len, t), Pair.snd(D.Bytes, U32, W.num.go(g, _, e))) : D.Bytes & U32}
          ngo(g, len, t, NJ(mo, j), NA(mo, len, t, j, acc), NM(mo, len, t, j), e)

# num hands the buffer back.
def num_b(+len: U32, +t: AT.Tree<U32>, +j: U32, +e: U32) ->
  {W.num(C.BT(len, t), j, e) == (C.BT(len, t), Pair.snd(D.Bytes, U32, W.num(C.BT(len, t), j, e))) : D.Bytes & U32}:
  +mo = U32.is_lt(j, e)
  %Equal.sym(W.Nm, W.num.step.if(mo, C.BT(len, t), j, 0), W.Nm{C.BT(len, t), NJ(mo, j), NA(mo, len, t, j, 0), NM(mo, len, t, j)}, nstep.if(mo, len, t, j, 0)) :
    {W.num.go(10n, _, e) == (C.BT(len, t), Pair.snd(D.Bytes, U32, W.num.go(10n, _, e))) : D.Bytes & U32}
  ngo(10n, len, t, NJ(mo, j), NA(mo, len, t, j, 0), NM(mo, len, t, j), e)

# rlf.step.if's result, field by field.
def RI(+dn: Bool, +i: U32) -> U32:
  match dn:
    case True{}:
      i
    case False{}:
      (i - 1 : U32)

def RM(+dn: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32) -> Bool:
  match dn:
    case True{}:
      False{}
    case False{}:
      Bool.not(U32.is_eq(C.AT(len, t, (i - 1 : U32)), 10))

def RH(+dn: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32) -> Bool:
  match dn:
    case True{}:
      False{}
    case False{}:
      U32.is_eq(C.AT(len, t, (i - 1 : U32)), 10)

def rstep.if(+dn: Bool, +len: U32, +t: AT.Tree<U32>, +i: U32) ->
  {W.rlf.step.if(dn, C.BT(len, t), i) == W.Rl{C.BT(len, t), RI(dn, i), RM(dn, len, t, i), RH(dn, len, t, i)} : W.Rl}:
  match dn:
    case True{}:
      {==}
    case False{}:
      +i1 = (i - 1 : U32)
      %Equal.sym(D.Bytes & U32, BY.at(C.BT(len, t), i1), (C.BT(len, t), C.AT(len, t, i1)), C.at_pair_t(len, t, i1)) :
        {W.rlf.byte(_, i1) == W.Rl{C.BT(len, t), RI(False{}, i), RM(False{}, len, t, i), RH(False{}, len, t, i)} : W.Rl}
      {==}

def RG(+f: Nat, +len: U32, +t: AT.Tree<U32>, +i: U32, +m: Bool, +h: Bool, +lo: U32) -> U32 & Bool:
  Pair.snd(D.Bytes, U32 & Bool, W.rlf.go(f, W.Rl{C.BT(len, t), i, m, h}, lo))

def rgo(+f: Nat, +len: U32, +t: AT.Tree<U32>, +i: U32, +m: Bool, +h: Bool, +lo: U32) ->
  {W.rlf.go(f, W.Rl{C.BT(len, t), i, m, h}, lo) == (C.BT(len, t), (Pair.fst(U32, Bool, RG(f, len, t, i, m, h, lo)), Pair.snd(U32, Bool, RG(f, len, t, i, m, h, lo)))) : D.Bytes & (U32 & Bool)}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match m:
        case False{}:
          {==}
        case True{}:
          +dn = U32.is_le(i, lo)
          %Equal.sym(W.Rl, W.rlf.step.if(dn, C.BT(len, t), i), W.Rl{C.BT(len, t), RI(dn, i), RM(dn, len, t, i), RH(dn, len, t, i)}, rstep.if(dn, len, t, i)) :
            {W.rlf.go(g, _, lo) == (C.BT(len, t), (Pair.fst(U32, Bool, Pair.snd(D.Bytes, U32 & Bool, W.rlf.go(g, _, lo))), Pair.snd(U32, Bool, Pair.snd(D.Bytes, U32 & Bool, W.rlf.go(g, _, lo))))) : D.Bytes & (U32 & Bool)}
          rgo(g, len, t, RI(dn, i), RM(dn, len, t, i), RH(dn, len, t, i), lo)

def RL(+len: U32, +t: AT.Tree<U32>, +j: U32, +lo: U32) -> U32 & Bool:
  Pair.snd(D.Bytes, U32 & Bool, W.rlf(C.BT(len, t), j, lo))

# rlf hands the buffer back.
def rlf_b(+len: U32, +t: AT.Tree<U32>, +j: U32, +lo: U32) ->
  {W.rlf(C.BT(len, t), j, lo) == (C.BT(len, t), (Pair.fst(U32, Bool, RL(len, t, j, lo)), Pair.snd(U32, Bool, RL(len, t, j, lo)))) : D.Bytes & (U32 & Bool)}:
  +dn = U32.is_le(j, lo)
  +F = Nat.add(U32.to_nat((j - lo : U32)), 2n)
  %Equal.sym(W.Rl, W.rlf.step.if(dn, C.BT(len, t), j), W.Rl{C.BT(len, t), RI(dn, j), RM(dn, len, t, j), RH(dn, len, t, j)}, rstep.if(dn, len, t, j)) :
    {W.rlf.go(F, _, lo) == (C.BT(len, t), (Pair.fst(U32, Bool, Pair.snd(D.Bytes, U32 & Bool, W.rlf.go(F, _, lo))), Pair.snd(U32, Bool, Pair.snd(D.Bytes, U32 & Bool, W.rlf.go(F, _, lo))))) : D.Bytes & (U32 & Bool)}
  rgo(F, len, t, RI(dn, j), RM(dn, len, t, j), RH(dn, len, t, j), lo)

# Q.text, as a pair.
def TY(+len: U32, +t: AT.Tree<U32>, +s: U32, +n: U32) -> List<&2, U32>:
  Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(len, t), s, n))

def text_p(+len: U32, +t: AT.Tree<U32>, +s: U32, +n: U32) ->
  {Q.text(C.BT(len, t), s, n) == (C.BT(len, t), Q.chars(TY(len, t, s, n))) : D.Bytes & String}:
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(len, t), s, n), (C.BT(len, t), TY(len, t, s, n)), SM.to_list_pair_t(len, t, s, n)) :
    {Q.text.k(_) == (C.BT(len, t), Q.chars(TY(len, t, s, n))) : D.Bytes & String}
  {==}

# cp's result, field by field (the tab test passed or not).
def CC(+found: Bool, +len: U32, +t: AT.Tree<U32>, +s: U32, +tb: U32) -> String:
  match found:
    case True{}:
      Q.chars(TY(len, t, s, (tb - s : U32)))
    case False{}:
      ""

def CP(+found: Bool, +len: U32, +t: AT.Tree<U32>, +tb: U32, +e: U32) -> Nat:
  match found:
    case True{}:
      U32.to_nat(Pair.snd(D.Bytes, U32, W.num(C.BT(len, t), (tb + 1 : U32), e)))
    case False{}:
      0n

def cc_bytes(+found: Bool, +len: U32, +t: AT.Tree<U32>, +s: U32, +tb: U32) -> {E.is_bytes(CC(found, len, t, s, tb)) == True{} : Bool}:
  match found:
    case True{}:
      chars_bytes(TY(len, t, s, (tb - s : U32)), tl_bytes(U32.to_nat((tb - s : U32)), len, t, s))
    case False{}:
      {==}

def cp.if(+found: Bool, +len: U32, +t: AT.Tree<U32>, +s: U32, +tb: U32, +e: U32) ->
  {W.cp.tab.if(found, s, tb, e, C.BT(len, t)) == W.Cp{C.BT(len, t), found, CC(found, len, t, s, tb), CP(found, len, t, tb, e)} : W.Cp}:
  match found:
    case True{}:
      +X = Q.chars(TY(len, t, s, (tb - s : U32)))
      %Equal.sym(D.Bytes & String, Q.text(C.BT(len, t), s, (tb - s : U32)), (C.BT(len, t), X), text_p(len, t, s, (tb - s : U32))) :
        {W.cp.text(tb, e, _) == W.Cp{C.BT(len, t), True{}, CC(True{}, len, t, s, tb), CP(True{}, len, t, tb, e)} : W.Cp}
      %Equal.sym(D.Bytes & U32, W.num(C.BT(len, t), (tb + 1 : U32), e), (C.BT(len, t), Pair.snd(D.Bytes, U32, W.num(C.BT(len, t), (tb + 1 : U32), e))), num_b(len, t, (tb + 1 : U32), e)) :
        {W.cp.num(X, _) == W.Cp{C.BT(len, t), True{}, CC(True{}, len, t, s, tb), CP(True{}, len, t, tb, e)} : W.Cp}
      {==}
    case False{}:
      {==}

def CF(+len: U32, +t: AT.Tree<U32>, +s: U32, +e: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), s, e, 9))

# cp hands the buffer back: ok is the tab test, the CHROM is bytes.
def cp_b(+len: U32, +t: AT.Tree<U32>, +s: U32, +e: U32) ->
  {W.cp(C.BT(len, t), s, e) == W.Cp{C.BT(len, t), U32.is_lt(CF(len, t, s, e), e), CC(U32.is_lt(CF(len, t, s, e), e), len, t, s, CF(len, t, s, e)), CP(U32.is_lt(CF(len, t, s, e), e), len, t, CF(len, t, s, e), e)} : W.Cp}:
  +tb = CF(len, t, s, e)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s, e, 9), (C.BT(len, t), tb), FE.find_pair(C.BT(len, t), s, e, 9)) :
    {W.cp.tab(s, e, _) == W.Cp{C.BT(len, t), U32.is_lt(tb, e), CC(U32.is_lt(tb, e), len, t, s, tb), CP(U32.is_lt(tb, e), len, t, tb, e)} : W.Cp}
  cp.if(U32.is_lt(tb, e), len, t, s, tb, e)

# ---------------------------------------------------------------------------
# The reads
# ---------------------------------------------------------------------------

# Copies of proof_e_task.bend's rs_ok and two (that file imports this one;
# it shows them equal).
def rs_ok2(+rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Pr.Req{+c, +a, +b} <> t:
      E.le31(Nat.sub(b, a)) && E.is_bytes(c) && rs_ok2(t)

def two2(+rs: List<&2, Pr.Req>) -> Bool:
  match rs:
    case a <> b <> Nil{}:
      True{}
    case _:
      False{}

def subself(+n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      subself(m)

def le31_0(+e: Nat) -> {E.le31(Nat.sub(e, e)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(e, e), 0n, subself(e)) : {E.le31(_) == True{} : Bool}
  {==}

def WA(+one: Bool, +a: Nat, +e: Nat) -> Nat:
  match one:
    case True{}:
      a
    case False{}:
      e

def win.if(+one: Bool, +c: String, +a: Nat, +e: Nat, +h: {one == Q.le31(Nat.sub(e, a)) : Bool}) ->
  {W.plan.win.if(one, c, a, e) == Pr.Req{c, WA(one, a, e), e} : Pr.Req} & {E.le31(Nat.sub(e, WA(one, a, e))) == True{} : Bool}:
  match one:
    case True{}:
      ({==}, Equal.sym(Bool, True{}, Q.le31(Nat.sub(e, a)), h))
    case False{}:
      ({==}, le31_0(e))

def WB(+c: String, +a: Nat, +e: Nat) -> Nat:
  WA(Q.le31(Nat.sub(e, a)), a, e)

# plan.win: one read within 2^31 letters.
def win_ok(+c: String, +a: Nat, +e: Nat) ->
  {W.plan.win(c, a, e) == Pr.Req{c, WB(c, a, e), e} : Pr.Req} & {E.le31(Nat.sub(e, WB(c, a, e))) == True{} : Bool}:
  win.if(Q.le31(Nat.sub(e, a)), c, a, e, {==})

def win_eq(+c: String, +a: Nat, +e: Nat) -> {W.plan.win(c, a, e) == Pr.Req{c, WB(c, a, e), e} : Pr.Req}:
  Pair.fst({W.plan.win(c, a, e) == Pr.Req{c, WB(c, a, e), e} : Pr.Req}, {E.le31(Nat.sub(e, WB(c, a, e))) == True{} : Bool}, win_ok(c, a, e))

def win_le(+c: String, +a: Nat, +e: Nat) -> {E.le31(Nat.sub(e, WB(c, a, e))) == True{} : Bool}:
  Pair.snd({W.plan.win(c, a, e) == Pr.Req{c, WB(c, a, e), e} : Pr.Req}, {E.le31(Nat.sub(e, WB(c, a, e))) == True{} : Bool}, win_ok(c, a, e))

# Two reads, each built by plan.win: within 2^31 letters, of bytes contigs.
def two_win(+c1: String, +A1: Nat, +E1: Nat, +c2: String, +A2: Nat, +E2: Nat,
  +hb1: {E.is_bytes(c1) == True{} : Bool},
  +hb2: {E.is_bytes(c2) == True{} : Bool}) ->
  {Bool.and(rs_ok2([W.plan.win(c1, A1, E1), W.plan.win(c2, A2, E2)]), two2([W.plan.win(c1, A1, E1), W.plan.win(c2, A2, E2)])) == True{} : Bool}:
  +R1 = {Pr.Req{c1, WB(c1, A1, E1), E1} : Pr.Req}
  +R2 = {Pr.Req{c2, WB(c2, A2, E2), E2} : Pr.Req}
  %Equal.sym(Pr.Req, W.plan.win(c1, A1, E1), R1, win_eq(c1, A1, E1)) :
    {Bool.and(rs_ok2([_, W.plan.win(c2, A2, E2)]), two2([_, W.plan.win(c2, A2, E2)])) == True{} : Bool}
  %Equal.sym(Pr.Req, W.plan.win(c2, A2, E2), R2, win_eq(c2, A2, E2)) :
    {Bool.and(rs_ok2([R1, _]), two2([R1, _])) == True{} : Bool}
  %Equal.sym(Bool, E.le31(Nat.sub(E1, WB(c1, A1, E1))), True{}, win_le(c1, A1, E1)) :
    {Bool.and(Bool.and(Bool.and(_, E.is_bytes(c1)), Bool.and(Bool.and(E.le31(Nat.sub(E2, WB(c2, A2, E2))), E.is_bytes(c2)), True{})), True{}) == True{} : Bool}
  %Equal.sym(Bool, E.le31(Nat.sub(E2, WB(c2, A2, E2))), True{}, win_le(c2, A2, E2)) :
    {Bool.and(Bool.and(Bool.and(True{}, E.is_bytes(c1)), Bool.and(Bool.and(_, E.is_bytes(c2)), True{})), True{}) == True{} : Bool}
  %Equal.sym(Bool, E.is_bytes(c1), True{}, hb1) :
    {Bool.and(Bool.and(Bool.and(True{}, _), Bool.and(Bool.and(True{}, E.is_bytes(c2)), True{})), True{}) == True{} : Bool}
  %Equal.sym(Bool, E.is_bytes(c2), True{}, hb2) :
    {Bool.and(Bool.and(Bool.and(True{}, True{}), Bool.and(Bool.and(True{}, _), True{})), True{}) == True{} : Bool}
  {==}

# plan.two: the span's halves, or the windows on from the first line and back
# from the last.
def two_ok(+halves: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat, +a: Nat, +e: Nat,
  +hb1: {E.is_bytes(c1) == True{} : Bool},
  +hb2: {E.is_bytes(c2) == True{} : Bool}) ->
  {Bool.and(rs_ok2(W.plan.two(halves, c1, p1, c2, p2, a, e)), two2(W.plan.two(halves, c1, p1, c2, p2, a, e))) == True{} : Bool}:
  match halves:
    case True{}:
      +m = Nat.add(a, Nat.div(Nat.sub(e, a), 2n))
      two_win(c1, a, Nat.add(m, Q.margin()), c1, Nat.sub(m, Q.margin()), e, hb1, hb1)
    case False{}:
      two_win(c1, Nat.sub(Nat.sub(p1, 1n), Q.margin()), Nat.add(p1, Q.ahead()), c2, Nat.sub(Nat.sub(p2, 1n), Q.ahead()), Nat.add(p2, Q.margin()), hb1, hb2)

def reqs.if(+one: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat, +a: Nat, +e: Nat,
  +h: {one == Bool.and(Bool.and(String.eq(c1, c2), Q.le31(Nat.sub(e, a))), Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead())) : Bool},
  +hb1: {E.is_bytes(c1) == True{} : Bool},
  +hb2: {E.is_bytes(c2) == True{} : Bool}) ->
  {Bool.and(rs_ok2(W.plan.reqs.if(one, c1, p1, c2, p2, a, e)), two2(W.plan.reqs.if(one, c1, p1, c2, p2, a, e))) == True{} : Bool}:
  match one:
    case True{}:
      +hl = andr(String.eq(c1, c2), Q.le31(Nat.sub(e, a)), andl(Bool.and(String.eq(c1, c2), Q.le31(Nat.sub(e, a))), Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead()), Equal.sym(Bool, True{}, Bool.and(Bool.and(String.eq(c1, c2), Q.le31(Nat.sub(e, a))), Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead())), h)))
      %Equal.sym(Bool, E.le31(Nat.sub(e, a)), True{}, hl) :
        {Bool.and(Bool.and(Bool.and(_, E.is_bytes(c1)), Bool.and(Bool.and(E.le31(Nat.sub(e, e)), E.is_bytes(c1)), True{})), True{}) == True{} : Bool}
      %Equal.sym(Bool, E.le31(Nat.sub(e, e)), True{}, le31_0(e)) :
        {Bool.and(Bool.and(Bool.and(True{}, E.is_bytes(c1)), Bool.and(Bool.and(_, E.is_bytes(c1)), True{})), True{}) == True{} : Bool}
      %Equal.sym(Bool, E.is_bytes(c1), True{}, hb1) :
        {Bool.and(Bool.and(Bool.and(True{}, _), Bool.and(Bool.and(True{}, _), True{})), True{}) == True{} : Bool}
      {==}
    case False{}:
      two_ok(Bool.and(Bool.and(String.eq(c1, c2), Bool.not(Nat.is_le(Nat.sub(Nat.sub(p2, p1), Q.ahead()), Q.ahead()))), Nat.is_le(Nat.sub(Nat.sub(Nat.sub(Nat.sub(e, a), Q.ahead()), Q.ahead()), Q.ahead()), Q.ahead())), c1, p1, c2, p2, a, e, hb1, hb2)

# plan.reqs: two reads, each within 2^31 letters, of bytes contigs.
def reqs_ok(+c1: String, +p1: Nat, +c2: String, +p2: Nat,
  +hb1: {E.is_bytes(c1) == True{} : Bool},
  +hb2: {E.is_bytes(c2) == True{} : Bool}) ->
  {Bool.and(rs_ok2(W.plan.reqs(c1, p1, c2, p2)), two2(W.plan.reqs(c1, p1, c2, p2))) == True{} : Bool}:
  +a = Nat.sub(Nat.sub(Nat.min(p1, p2), 1n), Q.margin())
  +e = Nat.add(Nat.max(p1, p2), Q.margin())
  reqs.if(Bool.and(Bool.and(String.eq(c1, c2), Q.le31(Nat.sub(e, a))), Nat.is_le(Nat.sub(Nat.sub(e, a), Q.margin()), Q.ahead())), c1, p1, c2, p2, a, e, {==}, hb1, hb2)

# ---------------------------------------------------------------------------
# The last line
# ---------------------------------------------------------------------------

def lrs(+ok: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat) -> List<&2, Pr.Req>:
  match ok:
    case True{}:
      W.plan.reqs(c1, p1, c2, p2)
    case False{}:
      W.plan.reqs(c1, p1, c1, p1)

def lrs_ok(+ok: Bool, +c1: String, +p1: Nat, +c2: String, +p2: Nat,
  +hb1: {E.is_bytes(c1) == True{} : Bool},
  +hb2: {E.is_bytes(c2) == True{} : Bool}) ->
  {Bool.and(rs_ok2(lrs(ok, c1, p1, c2, p2)), two2(lrs(ok, c1, p1, c2, p2))) == True{} : Bool}:
  match ok:
    case True{}:
      reqs_ok(c1, p1, c2, p2, hb1, hb2)
    case False{}:
      reqs_ok(c1, p1, c1, p1, hb1, hb1)

def plcp(+ok: Bool, +k: U32, +c1: String, +p1: Nat, +l: Nat, +c2: String, +p2: Nat, +len: U32, +t: AT.Tree<U32>) ->
  {W.plan.last.cp(k, c1, p1, l, W.Cp{C.BT(len, t), ok, c2, p2}) == W.Pl{C.BT(len, t), lrs(ok, c1, p1, c2, p2), True{}, k, c1, l} : W.Pl}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# The last line's search, step by step.
def EL(+len: U32, +t: AT.Tree<U32>, +s1: U32) -> U32:
  Pair.fst(U32, Bool, RL(len, t, len, s1))

def LS(+len: U32, +t: AT.Tree<U32>, +s1: U32) -> U32:
  Bool.pick(U32, Pair.snd(U32, Bool, RL(len, t, EL(len, t, s1), s1)), (Pair.fst(U32, Bool, RL(len, t, EL(len, t, s1), s1)) + 1 : U32), s1)

def LOK(+len: U32, +t: AT.Tree<U32>, +s1: U32) -> Bool:
  U32.is_lt(CF(len, t, LS(len, t, s1), EL(len, t, s1)), EL(len, t, s1))

def LC(+len: U32, +t: AT.Tree<U32>, +s1: U32) -> String:
  CC(LOK(len, t, s1), len, t, LS(len, t, s1), CF(len, t, LS(len, t, s1), EL(len, t, s1)))

def LP(+len: U32, +t: AT.Tree<U32>, +s1: U32) -> Nat:
  CP(LOK(len, t, s1), len, t, CF(len, t, LS(len, t, s1), EL(len, t, s1)), EL(len, t, s1))

def LRS(+len: U32, +t: AT.Tree<U32>, +c1: String, +p1: Nat, +s1: U32) -> List<&2, Pr.Req>:
  lrs(LOK(len, t, s1), c1, p1, LC(len, t, s1), LP(len, t, s1))

# plan.last.k hands the buffer back with the reads LRS.
def last_b(+k: U32, +c1: String, +p1: Nat, +l: Nat, +s1: U32, +len: U32, +t: AT.Tree<U32>) ->
  {W.plan.last.k(k, c1, p1, l, s1, W.rlf(C.BT(len, t), len, s1)) == W.Pl{C.BT(len, t), LRS(len, t, c1, p1, s1), True{}, k, c1, l} : W.Pl}:
  +el = EL(len, t, s1)
  +s = LS(len, t, s1)
  %Equal.sym(D.Bytes & (U32 & Bool), W.rlf(C.BT(len, t), len, s1), (C.BT(len, t), (el, Pair.snd(U32, Bool, RL(len, t, len, s1)))), rlf_b(len, t, len, s1)) :
    {W.plan.last.k(k, c1, p1, l, s1, _) == W.Pl{C.BT(len, t), LRS(len, t, c1, p1, s1), True{}, k, c1, l} : W.Pl}
  %Equal.sym(D.Bytes & (U32 & Bool), W.rlf(C.BT(len, t), el, s1), (C.BT(len, t), (Pair.fst(U32, Bool, RL(len, t, el, s1)), Pair.snd(U32, Bool, RL(len, t, el, s1)))), rlf_b(len, t, el, s1)) :
    {W.plan.last.at(k, c1, p1, l, el, s1, _) == W.Pl{C.BT(len, t), LRS(len, t, c1, p1, s1), True{}, k, c1, l} : W.Pl}
  %Equal.sym(W.Cp, W.cp(C.BT(len, t), s, el), W.Cp{C.BT(len, t), LOK(len, t, s1), LC(len, t, s1), LP(len, t, s1)}, cp_b(len, t, s, el)) :
    {W.plan.last.cp(k, c1, p1, l, _) == W.Pl{C.BT(len, t), LRS(len, t, c1, p1, s1), True{}, k, c1, l} : W.Pl}
  plcp(LOK(len, t, s1), k, c1, p1, l, LC(len, t, s1), LP(len, t, s1), len, t)

# ---------------------------------------------------------------------------
# The phantom (plan.first): the buffer comes back
# ---------------------------------------------------------------------------

# plan.tab's tab.
def TB(+len: U32, +t: AT.Tree<U32>, +e1: U32, +j: U32) -> U32:
  Pair.snd(D.Bytes, U32, F.find(C.BT(len, t), (j + 1 : U32), e1, 9))

def tab_b(+len: U32, +t: AT.Tree<U32>, +e1: U32, +j: U32) ->
  {W.plan.tab(e1, (C.BT(len, t), j)) == (C.BT(len, t), TB(len, t, e1, j)) : D.Bytes & U32}:
  FE.find_pair(C.BT(len, t), (j + 1 : U32), e1, 9)

# The first line's REF (after its tab t3, up to t4) and ALT (after t4, up to
# the next tab t5), and the phantom.
def RF(+len: U32, +t: AT.Tree<U32>, +t3: U32, +t4: U32) -> String:
  Q.chars(TY(len, t, (t3 + 1 : U32), (t4 - t3 - 1 : U32)))

def AF(+len: U32, +t: AT.Tree<U32>, +t4: U32, +t5: U32) -> String:
  Q.chars(TY(len, t, (t4 + 1 : U32), (t5 - t4 - 1 : U32)))

def PHI(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +p1: Nat, +t3: U32, +t4: U32, +t5: U32) -> Nat:
  match ok:
    case True{}:
      Nat.add(p1, W.plan.est(RF(len, t, t3, t4), AF(len, t, t4, t5)))
    case False{}:
      p1

def ph.if(+ok: Bool, +len: U32, +t: AT.Tree<U32>, +k: U32, +c1: String, +p1: Nat, +s1: U32, +t3: U32, +t4: U32, +t5: U32) ->
  {W.plan.ph.if(ok, k, c1, p1, s1, len, t3, t4, t5, C.BT(len, t)) == W.plan.last.k(k, c1, p1, PHI(ok, len, t, p1, t3, t4, t5), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}:
  match ok:
    case True{}:
      +n3 = (t4 - t3 - 1 : U32)
      +n4 = (t5 - t4 - 1 : U32)
      +R = RF(len, t, t3, t4)
      %Equal.sym(D.Bytes & String, Q.text(C.BT(len, t), (t3 + 1 : U32), n3), (C.BT(len, t), R), text_p(len, t, (t3 + 1 : U32), n3)) :
        {W.plan.ph.ref(k, c1, p1, s1, len, t4, t5, _) == W.plan.last.k(k, c1, p1, PHI(True{}, len, t, p1, t3, t4, t5), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
      %Equal.sym(D.Bytes & String, Q.text(C.BT(len, t), (t4 + 1 : U32), n4), (C.BT(len, t), AF(len, t, t4, t5)), text_p(len, t, (t4 + 1 : U32), n4)) :
        {W.plan.ph.alt(k, c1, p1, s1, len, R, _) == W.plan.last.k(k, c1, p1, PHI(True{}, len, t, p1, t3, t4, t5), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
      {==}
    case False{}:
      {==}

# plan.ph.t5's test, with t4 and t5 the tabs after t3.
def OKP(+len: U32, +t: AT.Tree<U32>, +e1: U32, +t3: U32) -> Bool:
  U32.is_lt(t3, TB(len, t, e1, t3)) && U32.is_lt(TB(len, t, e1, t3), e1) && U32.is_le((TB(len, t, e1, TB(len, t, e1, t3)) - t3 : U32), W.plan.big())

def ph_b(+len: U32, +t: AT.Tree<U32>, +k: U32, +c1: String, +p1: Nat, +s1: U32, +e1: U32, +t3: U32) ->
  {W.plan.ph(k, c1, p1, s1, len, e1, (C.BT(len, t), t3)) == W.plan.last.k(k, c1, p1, PHI(OKP(len, t, e1, t3), len, t, p1, t3, TB(len, t, e1, t3), TB(len, t, e1, TB(len, t, e1, t3))), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}:
  +T4 = TB(len, t, e1, t3)
  +T5 = TB(len, t, e1, T4)
  %Equal.sym(D.Bytes & U32, W.plan.tab(e1, (C.BT(len, t), t3)), (C.BT(len, t), T4), tab_b(len, t, e1, t3)) :
    {W.plan.ph.t4(k, c1, p1, s1, len, e1, t3, _) == W.plan.last.k(k, c1, p1, PHI(OKP(len, t, e1, t3), len, t, p1, t3, T4, T5), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
  %Equal.sym(D.Bytes & U32, W.plan.tab(e1, (C.BT(len, t), T4)), (C.BT(len, t), T5), tab_b(len, t, e1, T4)) :
    {W.plan.ph.t5(k, c1, p1, s1, len, e1, t3, T4, _) == W.plan.last.k(k, c1, p1, PHI(OKP(len, t, e1, t3), len, t, p1, t3, T4, T5), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
  ph.if(OKP(len, t, e1, t3), len, t, k, c1, p1, s1, t3, T4, T5)

# The first line's third tab (after ID), and the phantom plan.first takes.
def T3(+len: U32, +t: AT.Tree<U32>, +s1: U32, +e1: U32) -> U32:
  TB(len, t, e1, TB(len, t, e1, CF(len, t, s1, e1)))

def PH(+len: U32, +t: AT.Tree<U32>, +p1: Nat, +s1: U32, +e1: U32) -> Nat:
  PHI(OKP(len, t, e1, T3(len, t, s1, e1)), len, t, p1, T3(len, t, s1, e1), TB(len, t, e1, T3(len, t, s1, e1)), TB(len, t, e1, TB(len, t, e1, T3(len, t, s1, e1))))

# plan.first, on a line with a tab: plan.last.k with the phantom PH.
def first_b(+len: U32, +t: AT.Tree<U32>, +k: U32, +c1: String, +p1: Nat, +s1: U32, +e1: U32) ->
  {W.plan.first(len, k, s1, e1, W.Cp{C.BT(len, t), True{}, c1, p1}) == W.plan.last.k(k, c1, p1, PH(len, t, p1, s1, e1), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}:
  +T1 = CF(len, t, s1, e1)
  +T2 = TB(len, t, e1, T1)
  %Equal.sym(D.Bytes & U32, F.find(C.BT(len, t), s1, e1, 9), (C.BT(len, t), T1), FE.find_pair(C.BT(len, t), s1, e1, 9)) :
    {W.plan.ph(k, c1, p1, s1, len, e1, W.plan.tab(e1, W.plan.tab(e1, _))) == W.plan.last.k(k, c1, p1, PH(len, t, p1, s1, e1), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
  %Equal.sym(D.Bytes & U32, W.plan.tab(e1, (C.BT(len, t), T1)), (C.BT(len, t), T2), tab_b(len, t, e1, T1)) :
    {W.plan.ph(k, c1, p1, s1, len, e1, W.plan.tab(e1, _)) == W.plan.last.k(k, c1, p1, PH(len, t, p1, s1, e1), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
  %Equal.sym(D.Bytes & U32, W.plan.tab(e1, (C.BT(len, t), T2)), (C.BT(len, t), TB(len, t, e1, T2)), tab_b(len, t, e1, T2)) :
    {W.plan.ph(k, c1, p1, s1, len, e1, _) == W.plan.last.k(k, c1, p1, PH(len, t, p1, s1, e1), s1, W.rlf(C.BT(len, t), len, s1)) : W.Pl}
  ph_b(len, t, k, c1, p1, s1, e1, TB(len, t, e1, T2))

def last_ok(+c1: String, +p1: Nat, +s1: U32, +len: U32, +t: AT.Tree<U32>,
  +hb1: {E.is_bytes(c1) == True{} : Bool}) ->
  {Bool.and(rs_ok2(LRS(len, t, c1, p1, s1)), two2(LRS(len, t, c1, p1, s1))) == True{} : Bool}:
  lrs_ok(LOK(len, t, s1), c1, p1, LC(len, t, s1), LP(len, t, s1), hb1,
    cc_bytes(LOK(len, t, s1), len, t, LS(len, t, s1), CF(len, t, LS(len, t, s1), EL(len, t, s1))))

# Good reads followed by good reads.
def rs2_app(+rs: List<&2, Pr.Req>, +R: List<&2, Pr.Req>,
  +h1: {rs_ok2(rs) == True{} : Bool},
  +h2: {E.reqs_ok(R) == True{} : Bool}) ->
  {E.reqs_ok(List.append(&2, Pr.Req, rs, R)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h2
    case Con{Pr.Req{+c, +a, +b}, +t}:
      +hl = andl(E.le31(Nat.sub(b, a)), E.is_bytes(c), andl(Bool.and(E.le31(Nat.sub(b, a)), E.is_bytes(c)), rs_ok2(t), h1))
      %Equal.sym(Bool, E.le31(Nat.sub(b, a)), True{}, hl) : {Bool.and(_, E.reqs_ok(List.append(&2, Pr.Req, t, R))) == True{} : Bool}
      rs2_app(t, R, andr(Bool.and(E.le31(Nat.sub(b, a)), E.is_bytes(c)), rs_ok2(t), h1), h2)
