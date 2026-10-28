import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_b_lines_str.bend as LS
import ./proof_base.bend as PB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_base.bend as WB
import ./proof_e_wrap_ms.bend as WM
import ./proof_e_wrap_spec.bend as SP

# Helpers for proof_e_wrap.bend (area E1): the line across a boundary. Q's
# advances at the edge chain their Moved facts (Ch); the edge's check (Q's
# line count up by exactly one, the run not stopped) makes the chain one line
# long (one_line); then the lines still to come are the piece's after its
# first LF (edge_lines; area E2 uses it too).

# The chain
# =========

# From p1 to pc: in the byte mode both, the lines handled moved into the run
# (as S.Moved); p1 in the String mode: so is pc; else nothing.
def Ch.md(+m1: S.MdP, +mc: S.MdP, +fa: List<&2, B.Contig>, +cs: List<&2, String>, +p1: S.StP, +pc: S.StP) -> Type:
  match m1 mc:
    case S.MSP{s, qs, ql, code} _:
      {WM.is_msp(S.StP.md(pc)) == True{} : Bool}
    case S.MBP{+rp1} S.MBP{+rpc}:
      S.Moved(fa, cs, p1, pc)
    case S.MBP{rp1} S.MSP{s, qs, ql, code}:
      Unit

def Ch(+fa: List<&2, B.Contig>, +cs: List<&2, String>, +p1: S.StP, +pc: S.StP) -> Type:
  Ch.md(S.StP.md(p1), S.StP.md(pc), fa, cs, p1, pc)

law ch_refl:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +p1: S.StP
  Ch(fa, cs, p1, p1)

def ch_refl(fa, cs, p1):
  match p1:
    case S.StP{+o, S.MBP{+rp}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      (Nil{}, ({==}, {==}))
    case S.StP{+o, S.MSP{+s, +qs, +ql, +code}, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      {==}

law moved_comp:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +p1: S.StP
  for +pc: S.StP
  for +p2: S.StP
  for +rp1: P.RunP
  for +rpc: P.RunP
  for +rp2: P.RunP
  for hch: S.Moved.md(S.MBP{rp1}, S.MBP{rpc}, fa, cs, p1, pc)
  for hmv: S.Moved.md(S.MBP{rpc}, S.MBP{rp2}, fa, cs, pc, p2)
  for +eo: {S.StP.o(pc) == S.StP.o(p1) : B.Opts}
  S.Moved.md(S.MBP{rp1}, S.MBP{rp2}, fa, cs, p1, p2)

def moved_comp(fa, cs, p1, pc, p2, rp1, rpc, rp2, hch, hmv, eo):
  (+ls1, h1) = hch
  (+e1, s1) = h1
  (+ls2, h2) = hmv
  (+e2, s2) = h2
  +o1 = S.StP.o(p1)
  +L1 = B.Text.lines(S.intext(p1, cs))
  +Lc = B.Text.lines(S.intext(pc, cs))
  +L2 = B.Text.lines(S.intext(p2, cs))
  (List.append(&2, B.Line, ls1, ls2),
    (Equal.trans(List<&2, B.Line>, L1, List.append(&2, B.Line, ls1, Lc), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), e1,
      Equal.trans(List<&2, B.Line>, List.append(&2, B.Line, ls1, Lc), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2),
        Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => List.append(&2, B.Line, ls1, z), Lc, List.append(&2, B.Line, ls2, L2), e2),
        Equal.sym(List<&2, B.Line>, List.append(&2, B.Line, List.append(&2, B.Line, ls1, ls2), L2), List.append(&2, B.Line, ls1, List.append(&2, B.Line, ls2, L2)), PB.append_assoc(B.Line, ls1, ls2, L2)))),
    Equal.trans(R.RunSt, P.settle(P.specRun(rp2)), P.settle(L.run.go(ls2, fa, S.StP.o(pc), P.specRun(rpc))), P.settle(L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o1, P.specRun(rp1))), s2,
      Equal.trans(R.RunSt, P.settle(L.run.go(ls2, fa, S.StP.o(pc), P.specRun(rpc))), P.settle(L.run.go(ls2, fa, o1, P.specRun(rpc))), P.settle(L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o1, P.specRun(rp1))),
        Equal.cong(B.Opts, R.RunSt, z => P.settle(L.run.go(ls2, fa, z, P.specRun(rpc))), S.StP.o(pc), o1, eo),
        Equal.trans(R.RunSt, P.settle(L.run.go(ls2, fa, o1, P.specRun(rpc))), P.settle(L.run.go(ls2, fa, o1, L.run.go(ls1, fa, o1, P.specRun(rp1)))), P.settle(L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o1, P.specRun(rp1))),
          SP.go_settle(ls2, fa, o1, P.specRun(rpc), L.run.go(ls1, fa, o1, P.specRun(rp1)), s1),
          Equal.cong(R.RunSt, R.RunSt, z => P.settle(z), L.run.go(ls2, fa, o1, L.run.go(ls1, fa, o1, P.specRun(rp1))), L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o1, P.specRun(rp1)),
            Equal.sym(R.RunSt, L.run.go(List.append(&2, B.Line, ls1, ls2), fa, o1, P.specRun(rp1)), L.run.go(ls2, fa, o1, L.run.go(ls1, fa, o1, P.specRun(rp1))), SP.go_app(ls1, ls2, fa, o1, P.specRun(rp1)))))))))

# One more advance (its Moved fact, the options kept, and the String mode
# kept) extends the chain.
law ch_step:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +p1: S.StP
  for +pc: S.StP
  for +p2: S.StP
  for hch: Ch(fa, cs, p1, pc)
  for hmv: S.Moved(fa, cs, pc, p2)
  for +eo: {S.StP.o(pc) == S.StP.o(p1) : B.Opts}
  for +hk: {Bool.or(Bool.not(WM.is_msp(S.StP.md(pc))), WM.is_msp(S.StP.md(p2))) == True{} : Bool}
  Ch(fa, cs, p1, p2)

def ch_step(fa, cs, p1, pc, p2, hch, hmv, eo, hk):
  match p1 pc p2:
    case S.StP{+o1, S.MSP{+s1, +qs1, +ql1, +cd1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MSP{+sc, +qsc, +qlc, +cdc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} +q2:
      hk
    case S.StP{+o1, S.MSP{+s1, +qs1, +ql1, +cd1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MBP{+rpc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} +q2:
      Empty.absurd(Ch(fa, cs, S.StP{o1, S.MSP{s1, qs1, ql1, cd1}, sr1, pd1, ef1, bk1, wp1, as1, fn1}, q2), PB.false_ne_true(hch))
    case S.StP{+o1, S.MBP{+rp1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MBP{+rpc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} S.StP{+o2, S.MBP{+rp2}, +sr2, +pd2, +ef2, +bk2, +wp2, +as2, +fn2}:
      moved_comp(fa, cs, S.StP{o1, S.MBP{rp1}, sr1, pd1, ef1, bk1, wp1, as1, fn1}, S.StP{oc, S.MBP{rpc}, src, pdc, efc, bkc, wpc, asc, fnc}, S.StP{o2, S.MBP{rp2}, sr2, pd2, ef2, bk2, wp2, as2, fn2}, rp1, rpc, rp2, hch, hmv, eo)
    case S.StP{+o1, S.MBP{+rp1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MBP{+rpc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, +sr2, +pd2, +ef2, +bk2, +wp2, +as2, +fn2}:
      Unit{}
    case S.StP{+o1, S.MBP{+rp1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MSP{+sc, +qsc, +qlc, +cdc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} S.StP{+o2, S.MBP{+rp2}, +sr2, +pd2, +ef2, +bk2, +wp2, +as2, +fn2}:
      Empty.absurd(Ch(fa, cs, S.StP{o1, S.MBP{rp1}, sr1, pd1, ef1, bk1, wp1, as1, fn1}, S.StP{o2, S.MBP{rp2}, sr2, pd2, ef2, bk2, wp2, as2, fn2}), PB.false_ne_true(hk))
    case S.StP{+o1, S.MBP{+rp1}, +sr1, +pd1, +ef1, +bk1, +wp1, +as1, +fn1} S.StP{+oc, S.MSP{+sc, +qsc, +qlc, +cdc}, +src, +pdc, +efc, +bkc, +wpc, +asc, +fnc} S.StP{+o2, S.MSP{+s2, +qs2, +ql2, +cd2}, +sr2, +pd2, +ef2, +bk2, +wp2, +as2, +fn2}:
      Unit{}

# The edge's check
# ================

law add_cancel:
  for +a: Nat
  for +b: Nat
  for +h: {Nat.add(a, b) == 1n+a : Nat}
  {b == 1n : Nat}

def add_cancel(a, b, h):
  match a:
    case 0n:
      h
    case 1n+a2:
      add_cancel(a2, b, PB.succ_inj(Nat.add(a2, b), 1n+a2, h))

# The run went from rp1 to rp2 (up to settle) over ls1, its count up by one
# and not stopped: ls1 is one line.
law one_line:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ls1: List<&2, B.Line>
  for +rp1: P.RunP
  for +rp2: P.RunP
  for +hs: {P.settle(P.specRun(rp2)) == P.settle(L.run.go(ls1, fa, o, P.specRun(rp1))) : R.RunSt}
  for +hn: {P.RunP.n(rp2) == 1n+P.RunP.n(rp1) : Nat}
  for +hx: {P.RunP.x(rp2) == False{} : Bool}
  {List.length(&2, B.Line, ls1) == 1n : Nat}

def one_line(fa, o, ls1, rp1, rp2, hs, hn, hx):
  +G = L.run.go(ls1, fa, o, P.specRun(rp1))
  +hg = Equal.trans(Bool, R.RunSt.halt(G), R.RunSt.halt(P.settle(G)), False{}, Equal.sym(Bool, R.RunSt.halt(P.settle(G)), R.RunSt.halt(G), SP.settle_halt(G)),
    Equal.trans(Bool, R.RunSt.halt(P.settle(G)), R.RunSt.halt(P.settle(P.specRun(rp2))), False{},
      Equal.cong(R.RunSt, Bool, z => R.RunSt.halt(z), P.settle(G), P.settle(P.specRun(rp2)), Equal.sym(R.RunSt, P.settle(P.specRun(rp2)), P.settle(G), hs)),
      Equal.trans(Bool, R.RunSt.halt(P.settle(P.specRun(rp2))), R.RunSt.halt(P.specRun(rp2)), False{}, SP.settle_halt(P.specRun(rp2)),
        Equal.trans(Bool, R.RunSt.halt(P.specRun(rp2)), P.RunP.x(rp2), False{}, SP.spec_halt(rp2), hx))))
  +hnG = Equal.trans(Nat, R.RunSt.n(G), R.RunSt.n(P.settle(G)), 1n+P.RunP.n(rp1), Equal.sym(Nat, R.RunSt.n(P.settle(G)), R.RunSt.n(G), SP.settle_n(G)),
    Equal.trans(Nat, R.RunSt.n(P.settle(G)), R.RunSt.n(P.settle(P.specRun(rp2))), 1n+P.RunP.n(rp1),
      Equal.cong(R.RunSt, Nat, z => R.RunSt.n(z), P.settle(G), P.settle(P.specRun(rp2)), Equal.sym(R.RunSt, P.settle(P.specRun(rp2)), P.settle(G), hs)),
      Equal.trans(Nat, R.RunSt.n(P.settle(P.specRun(rp2))), R.RunSt.n(P.specRun(rp2)), 1n+P.RunP.n(rp1), SP.settle_n(P.specRun(rp2)),
        Equal.trans(Nat, R.RunSt.n(P.specRun(rp2)), P.RunP.n(rp2), 1n+P.RunP.n(rp1), SP.spec_n(rp2), hn))))
  +h1 = Equal.trans(Nat, Nat.add(P.RunP.n(rp1), List.length(&2, B.Line, ls1)), Nat.add(R.RunSt.n(P.specRun(rp1)), List.length(&2, B.Line, ls1)), 1n+P.RunP.n(rp1),
    Equal.cong(Nat, Nat, z => Nat.add(z, List.length(&2, B.Line, ls1)), P.RunP.n(rp1), R.RunSt.n(P.specRun(rp1)), Equal.sym(Nat, R.RunSt.n(P.specRun(rp1)), P.RunP.n(rp1), SP.spec_n(rp1))),
    Equal.trans(Nat, Nat.add(R.RunSt.n(P.specRun(rp1)), List.length(&2, B.Line, ls1)), R.RunSt.n(G), 1n+P.RunP.n(rp1),
      Equal.sym(Nat, R.RunSt.n(G), Nat.add(R.RunSt.n(P.specRun(rp1)), List.length(&2, B.Line, ls1)), SP.go_n(ls1, fa, o, P.specRun(rp1), hg)), hnG))
  add_cancel(P.RunP.n(rp1), List.length(&2, B.Line, ls1), h1)

def tail_l(xs: List<&2, B.Line>) -> List<&2, B.Line>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

law one_tail:
  for +ls1: List<&2, B.Line>
  for +L1: B.Line
  for +A: List<&2, B.Line>
  for +B2: List<&2, B.Line>
  for +hone: {List.length(&2, B.Line, ls1) == 1n : Nat}
  for +h: {L1 <> A == List.append(&2, B.Line, ls1, B2) : List<&2, B.Line>}
  {B2 == A : List<&2, B.Line>}

def one_tail(ls1, L1, A, B2, hone, h):
  match ls1:
    case Nil{}:
      Empty.absurd({B2 == A : List<&2, B.Line>}, PB.succ_ne_zero(0n, Equal.sym(Nat, 0n, 1n, hone)))
    case Con{+x, Nil{}}:
      Equal.sym(List<&2, B.Line>, A, B2, Equal.cong(List<&2, B.Line>, List<&2, B.Line>, z => tail_l(z), L1 <> A, x <> B2, h))
    case Con{+x, Con{+y, +t}}:
      Empty.absurd({B2 == A : List<&2, B.Line>}, PB.succ_ne_zero(List.length(&2, B.Line, t), PB.succ_inj(1n+List.length(&2, B.Line, t), 0n, hone)))

# The lines still to come
# =======================

law concat_cons:
  for +c: String
  for +X: List<&2, String>
  {String.concat(c <> X) == String.append(c, String.concat(X)) : String}

def concat_cons(c, X):
  {==}

# The text from a state waiting for more, with the piece c in front: its
# line end, then c (a, its first LF, then what follows it), then the rest.
law split_first:
  for +D: String
  for +c: String
  for +a: String
  for +aft: String
  for +X: List<&2, String>
  for +hc: {c == String.append(a, String.append("\n", aft)) : String}
  {String.append(D, String.concat(c <> X)) == String.append(String.append(D, a), String.append("\n", String.append(aft, String.concat(X)))) : String}

def split_first(D, c, a, aft, X, hc):
  +cX = String.concat(X)
  Equal.trans(String, String.append(D, String.concat(c <> X)), String.append(D, String.append(c, cX)), String.append(String.append(D, a), String.append("\n", String.append(aft, cX))),
    Equal.cong(String, String, z => String.append(D, z), String.concat(c <> X), String.append(c, cX), concat_cons(c, X)),
    Equal.trans(String, String.append(D, String.append(c, cX)), String.append(D, String.append(String.append(a, String.append("\n", aft)), cX)), String.append(String.append(D, a), String.append("\n", String.append(aft, cX))),
      Equal.cong(String, String, z => String.append(D, String.append(z, cX)), c, String.append(a, String.append("\n", aft)), hc),
      Equal.trans(String, String.append(D, String.append(String.append(a, String.append("\n", aft)), cX)), String.append(D, String.append(a, String.append("\n", String.append(aft, cX)))), String.append(String.append(D, a), String.append("\n", String.append(aft, cX))),
        Equal.cong(String, String, z => String.append(D, z), String.append(String.append(a, String.append("\n", aft)), cX), String.append(a, String.append("\n", String.append(aft, cX))), LS.sassoc(a, String.append("\n", aft), cX)),
        Equal.sym(String, String.append(String.append(D, a), String.append("\n", String.append(aft, cX))), String.append(D, String.append(a, String.append("\n", String.append(aft, cX)))), LS.sassoc(D, a, String.append("\n", String.append(aft, cX)))))))

law edge_lines_k:
  for +fa: List<&2, B.Contig>
  for +c: String
  for +k: U32
  for +X: List<&2, String>
  for +o: B.Opts
  for +md: S.MdP
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +fneed: Bool
  for +p3: S.StP
  for +ls1: List<&2, B.Line>
  for +a: String
  for +hw: {S.WF(fa, S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hmv: {B.Text.lines(S.intext(S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed}, c <> X)) == List.append(&2, B.Line, ls1, B.Text.lines(S.intext(p3, X))) : List<&2, B.Line>}
  for +hone: {List.length(&2, B.Line, ls1) == 1n : Nat}
  {B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X))) : List<&2, B.Line>}

def edge_lines_k(fa, c, k, X, o, md, pd, back, wp, fneed, p3, ls1, a, hw, hc, hn, hmv, hone):
  +D = P.pdtext(pd)
  +Y = String.append(PT.after(c, k), String.concat(X))
  +hd = DO.x9_3(S.md_ok(md), S.srcs_ok(Nil{}), P.pd_ok(pd), P.nolf(P.pdtext(pd)), Bool.or(S.src_empty(Nil{}), String.is_empty(P.pdtext(pd))), Bool.or(Bool.not(False{}), Bool.and(String.is_empty(P.pdtext(pd)), S.ends_lf(P.srcstext(Nil{})))), PC.wp_ok(fa, wp), S.mb_win(md, wp), E.all_bytes(S.opts_args(o)), hw)
  +el = Equal.trans(List<&2, B.Line>, B.Text.lines(String.append(D, String.concat(c <> X))), B.Text.lines(String.append(String.append(D, a), String.append("\n", Y))), B.Text.line(String.append(D, a)) <> B.Text.lines(Y),
    Equal.cong(String, List<&2, B.Line>, z => B.Text.lines(z), String.append(D, String.concat(c <> X)), String.append(String.append(D, a), String.append("\n", Y)), split_first(D, c, a, PT.after(c, k), X, hc)),
    LS.lines_cons(String.append(D, a), Y, LS.nolf_app(D, a, hd, hn)))
  one_tail(ls1, B.Text.line(String.append(D, a)), B.Text.lines(Y), B.Text.lines(S.intext(p3, X)), hone,
    Equal.trans(List<&2, B.Line>, B.Text.line(String.append(D, a)) <> B.Text.lines(Y), B.Text.lines(String.append(D, String.concat(c <> X))), List.append(&2, B.Line, ls1, B.Text.lines(S.intext(p3, X))),
      Equal.sym(List<&2, B.Line>, B.Text.lines(String.append(D, String.concat(c <> X))), B.Text.line(String.append(D, a)) <> B.Text.lines(Y), el), hmv))

# The lines still to come at the edge (E2 uses this): from a state p waiting
# for more, given the piece c (a, its first LF, then PT.after(c, k)), if the
# lines from p with c in front are ls1 then p3's, and ls1 is one line, then
# p3's lines are those after c's first LF, then X's.
law edge_lines:
  for +fa: List<&2, B.Contig>
  for +c: String
  for +k: U32
  for +X: List<&2, String>
  for +p: S.StP
  for +p3: S.StP
  for +ls1: List<&2, B.Line>
  for +a: String
  for +hm: {DR.more_ok(fa, p) == True{} : Bool}
  for +hc: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for +hn: {P.nolf(a) == True{} : Bool}
  for +hmv: {B.Text.lines(S.intext(p, c <> X)) == List.append(&2, B.Line, ls1, B.Text.lines(S.intext(p3, X))) : List<&2, B.Line>}
  for +hone: {List.length(&2, B.Line, ls1) == 1n : Nat}
  {B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X))) : List<&2, B.Line>}

def edge_lines(fa, c, k, X, p, p3, ls1, a, hm, hc, hn, hmv, hone):
  match p:
    case S.StP{+o, +md, Con{+x, +r}, +pd, +eof, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Con{x, r}, pd, eof, back, wp, asked, fneed} : S.StP}
      Empty.absurd({B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X))) : List<&2, B.Line>},
        PB.false_ne_true(WB.mo_se(S.WF(fa, q), False{}, Bool.not(eof), Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, True{}, +back, +wp, +asked, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, True{}, back, wp, asked, fneed} : S.StP}
      Empty.absurd({B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X))) : List<&2, B.Line>},
        PB.false_ne_true(WB.mo_ne(S.WF(fa, q), True{}, False{}, Maybe.is_none(&2, List<&2, Pr.Req>, asked), hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, Some{+rs}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, Some{rs}, fneed} : S.StP}
      Empty.absurd({B.Text.lines(S.intext(p3, X)) == B.Text.lines(String.append(PT.after(c, k), String.concat(X))) : List<&2, B.Line>},
        PB.false_ne_true(WB.mo_no(S.WF(fa, q), True{}, True{}, False{}, hm)))
    case S.StP{+o, +md, Nil{}, +pd, False{}, +back, +wp, None{}, +fneed}:
      +q = {S.StP{o, md, Nil{}, pd, False{}, back, wp, None{}, fneed} : S.StP}
      edge_lines_k(fa, c, k, X, o, md, pd, back, wp, fneed, p3, ls1, a, WB.mo_w(S.WF(fa, q), True{}, True{}, True{}, hm), hc, hn, hmv, hone)
