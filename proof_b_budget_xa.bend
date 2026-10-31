import Base
import ./types.bend as B
import ./run.bend as R
import ./protocol.bend as Pr
import ./norm_seq.bend as Norm
import ./proof_b_budget_need.bend as BN
import lawful-words@0.1.0.0/proof_nat.bend as N

# Lemmas on the budget's records and extra allowances (proof_b_budget_need.bend's
# RL, ALL, XA, WAS). Every variable is reusable.

# A state with no sources: no records in front, so WAS is WA and XA over the
# input's own lines.
law was_nil:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for md: Norm.Md
  for pend: Norm.Pd
  for +eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +cs: List<&2, String>
  {BN.WAS(fa, Norm.St{o, md, Nil{}, pend, eof, back, win, asked, fneed, dfs}, cs)
    == Nat.add(BN.WA.ls(fa, BN.fast_left(md, fneed), back, win, asked, BN.lines(Nil{}, pend, eof, cs)), BN.XA(o, fa, BN.lines(Nil{}, pend, eof, cs))) : Nat}

def was_nil(fa, o, md, pend, eof, back, win, asked, fneed, dfs, cs):
  {==}

# The same for bi.
law bi_nil:
  for +o: B.Opts
  for md: Norm.Md
  for pend: Norm.Pd
  for +eof: Bool
  for +back: Nat
  for win: Norm.Win
  for asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +dfs: B.Defs
  for +cs: List<&2, String>
  {BN.biS(Norm.St{o, md, Nil{}, pend, eof, back, win, asked, fneed, dfs}, cs) == BN.bi.ls(back, win, asked, BN.lines(Nil{}, pend, eof, cs)) : Bool}

def bi_nil(o, md, pend, eof, back, win, asked, fneed, dfs, cs):
  {==}

# XA of two lists joined.
law xa_app:
  for +o: B.Opts
  for +fa: List<&2, B.Contig>
  for xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  {BN.XA(o, fa, List.append(&2, B.Line, xs, ys)) == Nat.add(BN.XA(o, fa, xs), BN.XA(o, fa, ys)) : Nat}

def xa_app(o, fa, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +l <> +t:
      +X = BN.xa(o, fa, l)
      Equal.trans(Nat, Nat.add(X, BN.XA(o, fa, List.append(&2, B.Line, t, ys))), Nat.add(X, Nat.add(BN.XA(o, fa, t), BN.XA(o, fa, ys))),
        Nat.add(Nat.add(X, BN.XA(o, fa, t)), BN.XA(o, fa, ys)),
        Equal.cong(Nat, Nat, z => Nat.add(X, z), BN.XA(o, fa, List.append(&2, B.Line, t, ys)), Nat.add(BN.XA(o, fa, t), BN.XA(o, fa, ys)), xa_app(o, fa, t, ys)),
        Equal.sym(Nat, Nat.add(Nat.add(X, BN.XA(o, fa, t)), BN.XA(o, fa, ys)), Nat.add(X, Nat.add(BN.XA(o, fa, t), BN.XA(o, fa, ys))), N.add_assoc(X, BN.XA(o, fa, t), BN.XA(o, fa, ys))))

# Without -m no line is a candidate: XA is 0.
law xa_off_l:
  for +o: B.Opts
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  for +h: {R.Opts.split(o) == False{} : Bool}
  {BN.xa(o, fa, l) == 0n : Nat}

def xa_off_l(o, fa, l, h):
  %Equal.sym(Bool, R.Opts.split(o), False{}, h) :
    {BN.pick(Bool.and(Bool.and(_, Bool.not(B.Rec.malformed(B.Rec.fields(B.Line.body(l))))), Nat.is_le(2n, BN.nalts(l))), Nat.mul(BN.nalts(l), BN.LA(fa, l))) == 0n : Nat}
  {==}

law xa_off:
  for +o: B.Opts
  for +fa: List<&2, B.Contig>
  for ls: List<&2, B.Line>
  for +h: {R.Opts.split(o) == False{} : Bool}
  {BN.XA(o, fa, ls) == 0n : Nat}

def xa_off(o, fa, ls, h):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %Equal.sym(Nat, BN.xa(o, fa, l), 0n, xa_off_l(o, fa, l, h)) : {Nat.add(_, BN.XA(o, fa, t)) == 0n : Nat}
      xa_off(o, fa, t, h)
