import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./bytes_enc.bend as E
import ./proof_b_simdefs.bend as S
import ./proof_base.bend as PB
import ../lawful-arrays/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD

# Phase E, area E2: what the driver reads off a good wrapper state (InvW):
# before More, the file has not ended; before Ask{rs}, the reads are good.

def askrs(nx: Pr.Next) -> List<&2, Pr.Req>:
  match nx:
    case Pr.Ask{rs}:
      rs
    case _:
      Nil{}

# More is not an Ask.
law more_ask:
  for +rs: List<&2, Pr.Req>
  for +e: {Pr.More{} == Pr.Ask{rs} : Pr.Next}
  Empty

def more_ask(rs, e):
  PB.true_ne_false(Equal.cong(Pr.Next, Bool, z => WD.next_is_more(z), Pr.More{}, Pr.Ask{rs}, e))

law inv_more_ef:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +ef: Bool
  for hi: WD.InvW(fa, T, cs, O, N, x, Pr.More{}, ef)
  {ef == False{} : Bool}

def inv_more_ef(fa, T, cs, O, N, x, ef, hi):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, h5) = i3
      h5
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      (h5, j2) = j1
      (h6, j3) = j2
      (h7, h8) = j3
      h7
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      Empty.absurd({ef == False{} : Bool}, more_ask(PT.reqs_of(ps), h4))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      Empty.absurd({ef == False{} : Bool}, more_ask(Nil{}, h4))
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      (h5, j2) = j1
      Empty.absurd({ef == False{} : Bool}, PB.true_ne_false(h5))

law inv_ask_reqs:
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +rs: List<&2, Pr.Req>
  for +ef: Bool
  for hi: WD.InvW(fa, T, cs, O, N, x, Pr.Ask{rs}, ef)
  {E.reqs_ok(rs) == True{} : Bool}

def inv_ask_reqs(fa, T, cs, O, N, x, rs, ef, hi):
  match x:
    case WD.WPic{+p, WD.BNoneP{}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      (h5, j2) = j1
      h5
    case WD.WPic{+p, WD.BColP{+hs, +k}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      Empty.absurd({E.reqs_ok(rs) == True{} : Bool}, more_ask(rs, Equal.sym(Pr.Next, Pr.Ask{rs}, Pr.More{}, h4)))
    case WD.WPic{+p, WD.BAskP{+ps, +e}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      (h5, j2) = j1
      (h6, j3) = j2
      (h7, j4) = j3
      +er = Equal.cong(Pr.Next, List<&2, Pr.Req>, z => askrs(z), Pr.Ask{rs}, Pr.Ask{PT.reqs_of(ps)}, h4)
      AB.subst(List<&2, Pr.Req>, z => {E.reqs_ok(z) == True{} : Bool}, PT.reqs_of(ps), rs, Equal.sym(List<&2, Pr.Req>, rs, PT.reqs_of(ps), er), h7)
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, False{}}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      +er = Equal.cong(Pr.Next, List<&2, Pr.Req>, z => askrs(z), Pr.Ask{rs}, Pr.Ask{Nil{}}, h4)
      AB.subst(List<&2, Pr.Req>, z => {E.reqs_ok(z) == True{} : Bool}, Nil{}, rs, Equal.sym(List<&2, Pr.Req>, rs, Nil{}, er), {==})
    case WD.WPic{+p, WD.BCombP{+ps, +xs, +e, True{}}}:
      (h1, i1) = hi
      (h2, i2) = i1
      (h3, i3) = i2
      (h4, j1) = i3
      (h5, j2) = h4
      (h6, j3) = j2
      h6
