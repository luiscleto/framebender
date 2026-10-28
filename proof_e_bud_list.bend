import Base
import ./types.bend as B
import ./bytes_enc.bend as E
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_lines_str.bend as LS
import ./proof_base.bend as PB
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_base.bend as AB
import ./proof_e_task.bend as PT
import ./proof_e_bud_defs.bend as BD
import ./proof_e_bud_none.bend as BNo

# Phase E, area E2: lists of pieces. The batch's buffers read back as the
# pieces' texts (bytes, at most 2^31 each); reversing.

# Reversing
# =========

law rg:
  for +l: List<&2, String>
  for +acc: List<&2, String>
  {List.reverse.go(&2, String, l, acc) == List.append(&2, String, List.reverse(&2, String, l), acc) : List<&2, String>}

def rg(l, acc):
  match l:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, t, h <> acc), List.append(&2, String, List.reverse(&2, String, t), h <> acc),
        List.append(&2, String, List.reverse.go(&2, String, t, [h]), acc),
        rg(t, h <> acc),
        Equal.trans(List<&2, String>, List.append(&2, String, List.reverse(&2, String, t), h <> acc),
          List.append(&2, String, List.append(&2, String, List.reverse(&2, String, t), [h]), acc),
          List.append(&2, String, List.reverse.go(&2, String, t, [h]), acc),
          Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, List.reverse(&2, String, t), [h]), acc), List.append(&2, String, List.reverse(&2, String, t), h <> acc),
            PB.append_assoc(String, List.reverse(&2, String, t), [h], acc)),
          Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, acc), List.append(&2, String, List.reverse(&2, String, t), [h]), List.reverse.go(&2, String, t, [h]),
            Equal.sym(List<&2, String>, List.reverse.go(&2, String, t, [h]), List.append(&2, String, List.reverse(&2, String, t), [h]), rg(t, [h])))))

# The newest held piece goes last.
law revapp:
  for +a: String
  for +l: List<&2, String>
  for +cs: List<&2, String>
  {List.append(&2, String, List.reverse(&2, String, a <> l), cs) == List.append(&2, String, List.reverse(&2, String, l), a <> cs) : List<&2, String>}

def revapp(a, l, cs):
  Equal.trans(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, l, [a]), cs), List.append(&2, String, List.append(&2, String, List.reverse(&2, String, l), [a]), cs),
    List.append(&2, String, List.reverse(&2, String, l), a <> cs),
    Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, cs), List.reverse.go(&2, String, l, [a]), List.append(&2, String, List.reverse(&2, String, l), [a]), rg(l, [a])),
    PB.append_assoc(String, List.reverse(&2, String, l), [a], cs))

# The accumulator's facts survive reversing onto it.
law suf_ab:
  for +t: List<&2, String>
  for +acc: List<&2, String>
  for +h: {E.all_bytes(List.reverse.go(&2, String, t, acc)) == True{} : Bool}
  {E.all_bytes(acc) == True{} : Bool}

def suf_ab(t, acc, h):
  match t:
    case Nil{}:
      h
    case Con{+y, +r}:
      PB.and_true_r(E.is_bytes(y), E.all_bytes(acc), suf_ab(r, y <> acc, h))

law suf_po:
  for +t: List<&2, String>
  for +acc: List<&2, String>
  for +h: {E.pieces_ok(List.reverse.go(&2, String, t, acc)) == True{} : Bool}
  {E.pieces_ok(acc) == True{} : Bool}

def suf_po(t, acc, h):
  match t:
    case Nil{}:
      h
    case Con{+y, +r}:
      PB.and_true_r(E.le31(String.length(y)), E.pieces_ok(acc), suf_po(r, y <> acc, h))

# The held buffers read back
# ==========================

law bts_go:
  for +hs: List<&2, String>
  for +acc: List<&2, String>
  for +ha: {E.all_bytes(List.reverse.go(&2, String, hs, acc)) == True{} : Bool}
  for +hp: {E.pieces_ok(List.reverse.go(&2, String, hs, acc)) == True{} : Bool}
  {BD.bts(PT.encs(hs)) == hs : List<&2, String>}

def bts_go(hs, acc, ha, hp):
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hb = PB.and_true_l(E.is_bytes(x), E.all_bytes(acc), suf_ab(t, x <> acc, ha))
      +hn = PB.and_true_l(E.le31(String.length(x)), E.pieces_ok(acc), suf_po(t, x <> acc, hp))
      %Equal.sym(String, NR.chars(D.view(E.enc(x))), x, BNo.chars_enc(x, hb, hn)) : {_ <> BD.bts(PT.encs(t)) == x <> t : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, BD.bts(PT.encs(t)), t, bts_go(t, x <> acc, ha, hp))

# While collecting: the held pieces (newest first) are bytes, read back.
law bts_rev:
  for +hs: List<&2, String>
  for +h: {E.all_bytes(List.reverse(&2, String, hs)) && E.pieces_ok(List.reverse(&2, String, hs)) == True{} : Bool}
  {BD.bts(PT.encs(hs)) == hs : List<&2, String>}

def bts_rev(hs, h):
  bts_go(hs, Nil{}, PB.and_true_l(E.all_bytes(List.reverse(&2, String, hs)), E.pieces_ok(List.reverse(&2, String, hs)), h),
    PB.and_true_r(E.all_bytes(List.reverse(&2, String, hs)), E.pieces_ok(List.reverse(&2, String, hs)), h))

# A planned batch: its buffers read back.
law plts_mk:
  for +ps: List<&2, PT.Pc>
  for +ha: {E.all_bytes(PT.texts(ps)) == True{} : Bool}
  for +hp: {E.pieces_ok(PT.texts(ps)) == True{} : Bool}
  {BD.plts(PT.mkPls(ps)) == PT.texts(ps) : List<&2, String>}

def plts_mk(ps, ha, hp):
  match ps:
    case Nil{}:
      {==}
    case Con{PT.Pc{+c, +rs, +ok, +k, +c0, +l}, +t}:
      +hb = PB.and_true_l(E.is_bytes(c), E.all_bytes(PT.texts(t)), ha)
      +hn = PB.and_true_l(E.le31(String.length(c)), E.pieces_ok(PT.texts(t)), hp)
      %Equal.sym(String, NR.chars(D.view(E.enc(c))), c, BNo.chars_enc(c, hb, hn)) : {_ <> BD.plts(PT.mkPls(t)) == c <> PT.texts(t) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => c <> z, BD.plts(PT.mkPls(t)), PT.texts(t),
        plts_mk(t, PB.and_true_r(E.is_bytes(c), E.all_bytes(PT.texts(t)), ha), PB.and_true_r(E.le31(String.length(c)), E.pieces_ok(PT.texts(t)), hp)))

# A batch's results: their buffers read back (TOutOK's view).
law tots_mk:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +dcs: List<&2, String>
  for h: PT.BatchOK(fa, o, ps, xs, dcs)
  {BD.tots(PT.mkTOuts(fa, ps, xs)) == PT.texts(ps) : List<&2, String>}

def tots_mk(fa, o, ps, xs, dcs, h):
  match ps xs:
    case Nil{} Nil{}:
      {==}
    case Con{PT.Pc{+c, +rs, +ok, +k, +c0, +l}, +pt} Con{PT.TOutP{+len, +t, +d, +r}, +xt}:
      (h1, h2) = h
      (a1, h3) = h1
      (a2, h4) = h3
      %Equal.sym(List<&2, U32>, D.view(C.BT(len, t)), E.codes(c), a2) : {NR.chars(_) <> BD.tots(PT.mkTOuts(fa, pt, xt)) == c <> PT.texts(pt) : List<&2, String>}
      %Equal.sym(String, NR.chars(E.codes(c)), c, LS.chars_codes(c)) : {_ <> BD.tots(PT.mkTOuts(fa, pt, xt)) == c <> PT.texts(pt) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => c <> z, BD.tots(PT.mkTOuts(fa, pt, xt)), PT.texts(pt), tots_mk(fa, o, pt, xt, dcs, h2))
    case Nil{} Con{+x, +xt}:
      Empty.absurd({BD.tots(PT.mkTOuts(fa, Nil{}, x <> xt)) == PT.texts(Nil{}) : List<&2, String>}, h)
    case Con{+p, +pt} Nil{}:
      Empty.absurd({BD.tots(PT.mkTOuts(fa, p <> pt, Nil{})) == PT.texts(p <> pt) : List<&2, String>}, h)
