import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_rg.bend as RGH
import ./proof_b_drivedefs.bend as DR
import ./proof_b_run.bend as PR
import ./proof_b_enc.bend as ENC
import ./proof_b_lit.bend as LIT
import ./proof_b_frame.bend as FM
import ./proof_b_frame_fr.bend as FR
import ./proof_b_drive_out.bend as DO
import ./proof_b_drive_fin.bend as DF
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Helpers for proof_b_drive.bend: the end of the run in the String mode
# (Norm.finish of an MS state). The report's output is queued (fin.ms) and
# handed out: at once if it fits (Finish), else over Ask{[]} steps.

# Bytes
# =====

law bytes_app:
  for +a: String
  for +b: String
  for +ha: {E.is_bytes(a) == True{} : Bool}
  for +hb: {E.is_bytes(b) == True{} : Bool}
  {E.is_bytes(String.append(a, b)) == True{} : Bool}

def bytes_app(a, b, ha, hb):
  match a:
    case SNil{}:
      hb
    case SCon{+c, +t}:
      +h1 = PB.and_true_l(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), ha)
      +h2 = PB.and_true_r(U32.is_lt(Char.to_u32(c), 256), E.is_bytes(t), ha)
      %Equal.sym(Bool, U32.is_lt(Char.to_u32(c), 256), True{}, h1) : {Bool.and(_, E.is_bytes(String.append(t, b))) == True{} : Bool}
      %Equal.sym(Bool, E.is_bytes(String.append(t, b)), True{}, bytes_app(t, b, h2, hb)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

def fout(f: R.Flush) -> String:
  match f:
    case R.Flushed{o, l}:
      o
    case R.Broke{o, b, p}:
      o

law fout_pre:
  for +s: String
  for +f: R.Flush
  {fout(R.Flush.pre(s, f)) == String.append(s, fout(f)) : String}

def fout_pre(s, f):
  match f:
    case R.Flushed{+o, +l}:
      {==}
    case R.Broke{+o, +b, +p}:
      {==}

law fl_put:
  for +ok: Bool
  for +it: R.Item
  for +last: Maybe<&2, R.Item>
  for +rest: R.Flush
  for +hx: {E.is_bytes(R.Item.text(it)) == True{} : Bool}
  for +hr: {E.is_bytes(fout(rest)) == True{} : Bool}
  {E.is_bytes(fout(R.flush.put(ok, it, last, rest))) == True{} : Bool}

def fl_put(ok, it, last, rest, hx, hr):
  match ok:
    case True{}:
      %Equal.sym(String, fout(R.Flush.pre(R.Item.text(it), rest)), String.append(R.Item.text(it), fout(rest)), fout_pre(R.Item.text(it), rest)) :
        {E.is_bytes(_) == True{} : Bool}
      bytes_app(R.Item.text(it), fout(rest), hx, hr)
    case False{}:
      {==}

# What flush writes is bytes when the items' texts are.
law fl_bytes:
  for +items: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +h: {P.items_bytes(items) == True{} : Bool}
  {E.is_bytes(fout(R.flush(items, last))) == True{} : Bool}

def fl_bytes(items, last, h):
  match items:
    case Nil{}:
      {==}
    case Con{R.Item{+kk, +pp, +aa, +tt}, +rest}:
      fl_put(R.flush.ok(last, kk), R.Item{kk, pp, aa, tt}, last, R.flush(rest, Some{R.Item{kk, pp, aa, tt}}),
        PB.and_true_l(E.is_bytes(tt), P.items_bytes(rest), h),
        fl_bytes(rest, Some{R.Item{kk, pp, aa, tt}}, PB.and_true_r(E.is_bytes(tt), P.items_bytes(rest), h)))

law ff_out:
  for +f: R.Flush
  for +o: String
  for +ns: List<&2, B.Note>
  for +k: R.Cnt
  {R.Report.out(R.finish.flush(f, o, ns, k)) == String.append(o, fout(f)) : String}

def ff_out(f, o, ns, k):
  match f k:
    case R.Broke{+o2, +bad, +prev} _:
      {==}
    case R.Flushed{+o2, +l2} R.Cnt{+a, +bb, +cc, +dd}:
      {==}

# What run.bend's finish writes is bytes when the run's texts are.
law fin_out_bytes:
  for +st: R.RunSt
  for +hb: {P.st_bytes(st) == True{} : Bool}
  {E.is_bytes(R.Report.out(R.finish(st))) == True{} : Bool}

def fin_out_bytes(st, hb):
  match st:
    case R.RunSt{+n, +i, +h, +c, +e, +l, +b, +k, +o, +ns, True{}}:
      PB.and_true_r(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hb)
    case R.RunSt{+n, False{}, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      {==}
    case R.RunSt{+n, True{}, +h, +c, +e, +l, +b, +k, +o, +ns, False{}}:
      +hx = PB.and_true_l(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hb)
      %Equal.sym(String, R.Report.out(R.finish.flush(R.flush(b, l), o, ns, k)), String.append(o, fout(R.flush(b, l))), ff_out(R.flush(b, l), o, ns, k)) :
        {E.is_bytes(_) == True{} : Bool}
      bytes_app(o, fout(R.flush(b, l)), PB.and_true_r(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o), hb),
        fl_bytes(b, l, PB.and_true_r(E.is_bytes(h), P.items_bytes(b), hx)))

# Before the #CHROM line, with nothing written, finish writes nothing.
law fin_out_empty:
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +eo2: {o2 == "" : String}
  {R.Report.out(R.finish(R.RunSt{n, False{}, h, c, e, l, b, k, o2, ns, x})) == "" : String}

def fin_out_empty(n, h, c, e, l, b, k, o2, ns, x, eo2):
  match x:
    case True{}:
      eo2
    case False{}:
      {==}

# Queues
# ======

law rev_acc:
  for +xs: List<&2, String>
  for +acc: List<&2, String>
  {List.reverse.go(&2, String, xs, acc) == List.append(&2, String, List.reverse.go(&2, String, xs, Nil{}), acc) : List<&2, String>}

def rev_acc(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +Rv = List.reverse.go(&2, String, t, Nil{})
      Equal.trans(List<&2, String>, List.reverse.go(&2, String, t, y <> acc), List.append(&2, String, Rv, y <> acc), List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc),
        rev_acc(t, y <> acc),
        Equal.sym(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, Rv, y <> acc),
          Equal.trans(List<&2, String>, List.append(&2, String, List.reverse.go(&2, String, t, [y]), acc), List.append(&2, String, List.append(&2, String, Rv, [y]), acc), List.append(&2, String, Rv, y <> acc),
            Equal.cong(List<&2, String>, List<&2, String>, z => List.append(&2, String, z, acc), List.reverse.go(&2, String, t, [y]), List.append(&2, String, Rv, [y]), rev_acc(t, [y])),
            PB.append_assoc(String, Rv, [y], acc))))

law catgo_snoc:
  for +t: List<&2, String>
  for +hd: String
  for +a: String
  {Norm.cat.go(List.append(&2, String, t, [a]), hd) == String.append(Norm.cat.go(t, hd), a) : String}

def catgo_snoc(t, hd, a):
  match t:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(String, Norm.cat.go(List.append(&2, String, r, [a]), y), String.append(Norm.cat.go(r, y), a), catgo_snoc(r, y, a)) :
        {String.append(hd, _) == String.append(String.append(hd, Norm.cat.go(r, y)), a) : String}
      Equal.sym(String, String.append(String.append(hd, Norm.cat.go(r, y)), a), String.append(hd, String.append(Norm.cat.go(r, y), a)), PN.str_assoc(hd, Norm.cat.go(r, y), a))

law cat_snoc:
  for +xs: List<&2, String>
  for +a: String
  {Norm.cat(List.append(&2, String, xs, [a])) == String.append(Norm.cat(xs), a) : String}

def cat_snoc(xs, a):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      catgo_snoc(t, y, a)

# The queue with a's text added last.
law cat_rev_cons:
  for +a: String
  for +qs: List<&2, String>
  {Norm.cat(List.reverse(&2, String, a <> qs)) == String.append(Norm.cat(List.reverse(&2, String, qs)), a) : String}

def cat_rev_cons(a, qs):
  Equal.trans(String, Norm.cat(List.reverse.go(&2, String, qs, [a])), Norm.cat(List.append(&2, String, List.reverse.go(&2, String, qs, Nil{}), [a])), String.append(Norm.cat(List.reverse(&2, String, qs)), a),
    Equal.cong(List<&2, String>, String, z => Norm.cat(z), List.reverse.go(&2, String, qs, [a]), List.append(&2, String, List.reverse.go(&2, String, qs, Nil{}), [a]), rev_acc(qs, [a])),
    cat_snoc(List.reverse.go(&2, String, qs, Nil{}), a))

# Reports
# =======

law rep_eta:
  for +r: R.Report
  {R.Report{R.Report.out(r), R.Report.notes(r), R.Report.code(r)} == r : R.Report}

def rep_eta(r):
  match r:
    case R.Report{+o, +n, +c}:
      {==}

law or_and_t:
  for +i: Bool
  for +E1: Bool
  for +h: {Bool.or(i, E1) == True{} : Bool}
  {Bool.or(i, Bool.and(E1, List.is_empty(&2, B.Note, Nil{}))) == True{} : Bool}

def or_and_t(i, E1, h):
  match i:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, E1, True{}, h) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

law pre_with:
  for +Q: String
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +eo2: {o2 == "" : String}
  {S.with_out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Q) == S.pre(Q, Nil{}, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}) : R.RunSt}

def pre_with(Q, n, i, h, c, e, l, b, k, o2, ns, x, eo2):
  %Equal.sym(String, o2, "", eo2) :
    {R.RunSt{n, i, h, c, e, l, b, k, Q, ns, x} == R.RunSt{n, i, h, c, e, l, b, k, String.append(Q, _), List.append(&2, B.Note, Nil{}, ns), x} : R.RunSt}
  %Equal.sym(String, String.append(Q, ""), Q, PN.str_nil(Q)) :
    {R.RunSt{n, i, h, c, e, l, b, k, Q, ns, x} == R.RunSt{n, i, h, c, e, l, b, k, _, List.append(&2, B.Note, Nil{}, ns), x} : R.RunSt}
  {==}

# The String mode's report with no line left, once finish's output is queued.
law rep_none:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +eo2: {o2 == "" : String}
  for +hg: {Bool.or(i, Bool.and(String.is_empty(O), List.is_empty(&2, B.Note, N))) == True{} : Bool}
  for +h5: {Bool.or(i, String.is_empty(Norm.cat(List.reverse(&2, String, qs)))) == True{} : Bool}
  for +hnl: DF.NoLines(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs})
  {R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))} == S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) : R.Report}

def rep_none(dfs,fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, eo2, hg, h5, hnl):
  +X = S.with_out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Norm.cat(List.reverse(&2, String, qs)))
  +eF = Equal.trans(R.Report, R.finish(X), R.finish(S.pre(Norm.cat(List.reverse(&2, String, qs)), Nil{}, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), R.Report{String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))},
    Equal.cong(R.RunSt, R.Report, z => R.finish(z), X, S.pre(Norm.cat(List.reverse(&2, String, qs)), Nil{}, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), pre_with(Norm.cat(List.reverse(&2, String, qs)), n, i, h, c, e, l, b, k, o2, ns, x, eo2)),
    FM.finish_pre(Norm.cat(List.reverse(&2, String, qs)), Nil{}, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, or_and_t(i, String.is_empty(Norm.cat(List.reverse(&2, String, qs))), h5)))
  %Equal.sym(R.Report, S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}), R.finish(S.pre(O, N, X)), hnl) :
    {R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))} == _ : R.Report}
  %Equal.sym(R.Report, R.finish(S.pre(O, N, X)), R.Report{String.append(O, R.Report.out(R.finish(X))), List.append(&2, B.Note, N, R.Report.notes(R.finish(X))), R.Report.code(R.finish(X))}, FM.finish_pre(O, N, X, hg)) :
    {R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))} == _ : R.Report}
  %Equal.sym(R.Report, R.finish(X), R.Report{String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, eF) :
    {R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))} == R.Report{String.append(O, R.Report.out(_)), List.append(&2, B.Note, N, R.Report.notes(_)), R.Report.code(_)} : R.Report}
  {==}


# Handing out a queue that fits one step
# ======================================

law fin_fits.k:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +cc: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824) == True{} : Bool}
  for +hT: {R.Report{String.append(O, Norm.cat(List.reverse(&2, String, qs))), List.append(&2, B.Note, N, ns), cc} == T : R.Report}
  for os: &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> ({NR.of_str(Norm.cat(List.reverse(&2, String, qs))) == C.BT(ol, ot) : D.Bytes}
    & ({D.ok(C.BT(ol, ot), d) == True{} : Bool} & {NR.chars(D.view(C.BT(ol, ot))) == Norm.cat(List.reverse(&2, String, qs)) : String}))
  for +ef: Bool
  DO.StepG2(fa, T, cs, O, N, ef, Norm.out(Norm.St{o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}, Pr.Finish{cc}))

def fin_fits.k(dfs,fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hz, hT, os, ef):
  (+ol, os1) = os
  (+ot, os2) = os1
  (+d, os3) = os2
  (+e1, os4) = os3
  (+eok, ech) = os4
  %Equal.sym(List<&1, Norm.Src> & U32, Norm.left(P.mkSrcs(src)), (P.mkSrcs(src), DO.lsum(src)), DO.left_eq(src)) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.out.left(o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, _, P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Finish{cc}))
  %Equal.sym(Norm.Cut2, Norm.take_w(Norm.cat(List.reverse(&2, String, qs)), 1073741824), Norm.Cut2{Norm.cat(List.reverse(&2, String, qs)), ""}, LIT.take_w_all(Norm.cat(List.reverse(&2, String, qs)), 1073741824, hz)) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.out.k(Norm.ms.take.c(_, R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, ns, Some{cc}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Finish{cc}))
  %Equal.sym(D.Bytes, NR.of_str(Norm.cat(List.reverse(&2, String, qs))), C.BT(ol, ot), e1) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.out.k(((_, ns), Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, Nil{}, x}, [""], String.length(""), Some{cc}}), o, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs, Pr.Finish{cc}))
  +eout = Equal.trans(Maybe<&2, String>, E.out(C.BT(ol, ot)), Some{E.chars(D.view(C.BT(ol, ot)))}, Some{Norm.cat(List.reverse(&2, String, qs))},
    ENC.out_ok(ol, ot, d, eok, C.ok_d(ol, ot, d, eok)),
    Equal.cong(String, Maybe<&2, String>, z => Some{z}, E.chars(D.view(C.BT(ol, ot))), Norm.cat(List.reverse(&2, String, qs)),
      Equal.trans(String, E.chars(D.view(C.BT(ol, ot))), NR.chars(D.view(C.BT(ol, ot))), Norm.cat(List.reverse(&2, String, qs)), DO.chars_nr(D.view(C.BT(ol, ot))), ech)))
  (Norm.cat(List.reverse(&2, String, qs)), (eout, hT))

law fin_fits:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +cc: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824) == True{} : Bool}
  for +hbq: {E.is_bytes(Norm.cat(List.reverse(&2, String, qs))) == True{} : Bool}
  for +hT: {R.Report{String.append(O, Norm.cat(List.reverse(&2, String, qs))), List.append(&2, B.Note, N, ns), cc} == T : R.Report}
  for +ef: Bool
  DO.StepG2(fa, T, cs, O, N, ef, Norm.out(Norm.St{o, Norm.MS{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs}, Pr.Finish{cc}))

def fin_fits(dfs,fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hz, hbq, hT, ef):
  fin_fits.k(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hz, hT, PR.of_str(Norm.cat(List.reverse(&2, String, qs)), hbq, hz), ef)

# The code is set: the queue is handed out
# ========================================

law fms_go:
  for +dfs: B.Defs
  for +z: Bool
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +cc: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824) == z : Bool}
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {eof == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.fin.ms.go(z, o, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, cc, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))

def fms_go(dfs,z, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hz, hw, hr, hg, ha, ef, hef):
  match z:
    case True{}:
      +hmd = DO.wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}, hw)
      fin_fits(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hz, DO.z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), hr, ef)
    case False{}:
      +p = {S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      DO.out_ask(fa, T, cs, O, N, p, Nil{}, Norm.out(S.mkSt(fa, p), Pr.Ask{Nil{}}), DO.out_ok(fa, cs, O, N, p, Pr.Ask{Nil{}}, hw, hg, {==}), hr, {==}, {==},
        DO.mbr_nil(S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}), ha, ef, hef)

law fin_ms_some:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +cc: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +ef: Bool
  for +hef: {eof == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, Some{cc}}, src, pd, eof, back, wp, asked, fneed, dfs})))

def fin_ms_some(dfs,fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha, ef, hef):
  fms_go(dfs, Norm.len_le(Norm.cat(List.reverse(&2, String, qs)), 1073741824), fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, cc, src, pd, eof, back, wp, asked, fneed, {==}, hw, hr, hg, ha, ef, hef)

# No code yet: finish's report is queued first
# ============================================

law c1_q:
  for +ql: Nat
  for +Q: String
  for +a: String
  for +Q3: String
  for +hq: {Q3 == String.append(Q, a) : String}
  for +h1: {Nat.is_eq(ql, String.length(Q)) == True{} : Bool}
  {Nat.is_eq(Nat.add(ql, String.length(a)), String.length(Q3)) == True{} : Bool}

def c1_q(ql, Q, a, Q3, hq, h1):
  %Equal.sym(String, Q3, String.append(Q, a), hq) : {Nat.is_eq(Nat.add(ql, String.length(a)), String.length(_)) == True{} : Bool}
  %Equal.sym(Nat, String.length(String.append(Q, a)), Nat.add(String.length(Q), String.length(a)), PN.str_len_append(Q, a)) :
    {Nat.is_eq(Nat.add(ql, String.length(a)), _) == True{} : Bool}
  %Equal.sym(Nat, ql, String.length(Q), N.eq_sound(ql, String.length(Q), h1)) : {Nat.is_eq(Nat.add(_, String.length(a)), Nat.add(String.length(Q), String.length(a))) == True{} : Bool}
  N.eq_refl(Nat.add(String.length(Q), String.length(a)))

law and_t:
  for +a: Bool
  for +b: Bool
  for +h: {Bool.and(a, b) == True{} : Bool}
  {Bool.and(a, True{}) == True{} : Bool}

def and_t(a, b, h):
  %Equal.sym(Bool, a, True{}, PB.and_true_l(a, b, h)) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

law fmn_go:
  for +dfs: B.Defs
  for +z: Bool
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hz: {Norm.len_le(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), 1073741824) == z : Bool}
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hnl: DF.NoLines(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs})
  for +ef: Bool
  for +hef: {eof == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.fin.ms.go(z, o, R.RunSt{n, i, h, c, e, l, b, k, "", R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), x}, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))

def fmn_go(dfs,z, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, hz, hw, hr, hg, ha, hnl, ef, hef):
  match z i:
    case True{} _:
      +hmd = DO.wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, hw)
      +eo2 = DF.str_empty(o2, DO.z6_4(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))
      +ecat = cat_rev_cons(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), qs)
      +hT = Equal.trans(R.Report, R.Report{String.append(O, Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))},
        R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, T,
        Equal.cong(String, R.Report, zz => R.Report{String.append(O, zz), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), ecat),
        Equal.trans(R.Report, R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}), T,
          rep_none(dfs, fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, eo2, hg, DO.z6_5(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), hnl), hr))
      +hbq = Equal.trans(Bool, E.is_bytes(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs))), E.is_bytes(String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), True{},
        Equal.cong(String, Bool, zz => E.is_bytes(zz), Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), ecat),
        bytes_app(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), DO.z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), fin_out_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, DO.z6_3(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))))
      fin_fits(dfs, fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, "", R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), x, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), src, pd, eof, back, wp, asked, fneed, hz, hbq, hT, ef)
    case False{} True{}:
      +hmd = DO.wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, hw)
      +eo2 = DF.str_empty(o2, DO.z6_4(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))
      +ecat = cat_rev_cons(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), qs)
      +hT = Equal.trans(R.Report, R.Report{String.append(O, Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))},
        R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, T,
        Equal.cong(String, R.Report, zz => R.Report{String.append(O, zz), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), ecat),
        Equal.trans(R.Report, R.Report{String.append(O, String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), List.append(&2, B.Note, N, R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}, S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}), T,
          rep_none(dfs, fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, eo2, hg, DO.z6_5(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), hnl), hr))
      +hbq = Equal.trans(Bool, E.is_bytes(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs))), E.is_bytes(String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), True{},
        Equal.cong(String, Bool, zz => E.is_bytes(zz), Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), ecat),
        bytes_app(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), DO.z6_2(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd), fin_out_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, DO.z6_3(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))))
      +RS3t = {R.RunSt{n, True{}, h, c, e, l, b, k, "", R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), x} : R.RunSt}
      +hmd3 = DO.z6_mk(Nat.is_eq(Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), String.length(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs))), P.st_bytes(RS3t), String.is_empty(""), True{}, True{},
        c1_q(ql, Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), ecat, DO.z6_1(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)), hbq,
        and_t(Bool.and(E.is_bytes(h), P.items_bytes(b)), E.is_bytes(o2), DO.z6_3(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd)), {==}, {==}, {==})
      +p3 = {S.StP{o, S.MSP{RS3t, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), Some{R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}}, src, pd, eof, back, wp, asked, fneed, dfs} : S.StP}
      +wf3 = DO.wf_set_md(dfs, fa, o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, S.MSP{RS3t, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), Some{R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}}, src, pd, eof, back, wp, asked, fneed, hw, hmd3, {==},
        DO.rr_body(List.is_empty(&2, P.SrcP, S.recs(src)), i, Nat.is_le(1n, n), DO.wf_rr(dfs, fa, o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, hw)))
      DO.out_ask(fa, T, cs, O, N, p3, Nil{}, Norm.out(S.mkSt(fa, p3), Pr.Ask{Nil{}}), DO.out_ok(fa, cs, O, N, p3, Pr.Ask{Nil{}}, wf3, {==}, {==}), hT, {==}, {==},
        DO.mbr_nil(S.MSP{RS3t, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), Some{R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))}}), ha, ef, hef)
    case False{} False{}:
      +hmd = DO.wf_md(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, hw)
      +eo2 = DF.str_empty(o2, DO.z6_4(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))
      +eQ = DF.str_empty(Norm.cat(List.reverse(&2, String, qs)), DO.z6_5(Nat.is_eq(ql, String.length(Norm.cat(List.reverse(&2, String, qs)))), E.is_bytes(Norm.cat(List.reverse(&2, String, qs))), P.st_bytes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(P.RunSt.out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), String.is_empty(Norm.cat(List.reverse(&2, String, qs)))), Bool.or(R.RunSt.inbody(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}), List.is_empty(&2, B.Note, P.RunSt.notes(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), hmd))
      +eA = fin_out_empty(n, h, c, e, l, b, k, o2, ns, x, eo2)
      +ecat = cat_rev_cons(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), qs)
      +htr = Equal.trans(Bool, Norm.len_le(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), 1073741824), Norm.len_le(String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), 1073741824), True{},
        Equal.cong(String, Bool, zz => Norm.len_le(zz, 1073741824), Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), ecat),
        Equal.trans(Bool, Norm.len_le(String.append(Norm.cat(List.reverse(&2, String, qs)), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), 1073741824), Norm.len_le(String.append("", R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), 1073741824), True{},
          Equal.cong(String, Bool, zz => Norm.len_le(String.append(zz, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}))), 1073741824), Norm.cat(List.reverse(&2, String, qs)), "", eQ),
          Equal.trans(Bool, Norm.len_le(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), 1073741824), Norm.len_le("", 1073741824), True{},
            Equal.cong(String, Bool, zz => Norm.len_le(zz, 1073741824), R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), "", eA), {==})))
      Empty.absurd(DO.StepG2(fa, T, cs, O, N, ef, Norm.fin.ms.go(False{}, o, R.RunSt{n, i, h, c, e, l, b, k, "", R.Report.notes(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), x}, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs, Nat.add(ql, String.length(R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})))), R.Report.code(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})), P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs)),
        PB.true_ne_false(Equal.trans(Bool, True{}, Norm.len_le(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), 1073741824), False{}, Equal.sym(Bool, Norm.len_le(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), 1073741824), True{}, htr), hz)))

law fin_ms_none:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +hr: {S.report(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == T : R.Report}
  for +hg: {S.guard(O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}) == True{} : Bool}
  for +ha: {asked == None{} : Maybe<&2, List<&2, Pr.Req>>}
  for +hnl: DF.NoLines(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs})
  for +ef: Bool
  for +hef: {eof == ef : Bool}
  DO.StepG2(fa, T, cs, O, N, ef, Norm.finish(S.mkSt(fa, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs})))

def fin_ms_none(dfs,fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, hw, hr, hg, ha, hnl, ef, hef):
  %rep_eta(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) :
    DO.StepG2(fa, T, cs, O, N, ef, Norm.fin.ms(_, o, R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, P.mkSrcs(src), P.mkPd(pd), eof, back, PC.mkWin(fa, wp), asked, fneed, dfs))
  fmn_go(dfs, Norm.len_le(Norm.cat(List.reverse(&2, String, R.Report.out(R.finish(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x})) <> qs)), 1073741824), fa, T, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, {==}, hw, hr, hg, ha, hnl, ef, hef)

# No lines left (String mode, no code yet)
# ========================================

law nl_halt_ms:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +o2: String
  for +ns: List<&2, B.Note>
  for +x: Bool
  for +qs: List<&2, String>
  for +ql: Nat
  for +src: List<&2, P.SrcP>
  for +pd: P.PdP
  for +eof: Bool
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hx: {x == True{} : Bool}
  DF.NoLines(fa, cs, O, N, S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs})

def nl_halt_ms(dfs,fa, cs, O, N, o, n, i, h, c, e, l, b, k, o2, ns, x, qs, ql, src, pd, eof, back, wp, asked, fneed, hx):
  +st = S.pre(O, N, S.with_out(R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, Norm.cat(List.reverse(&2, String, qs))))
  +ls = B.Text.lines(S.intext(S.StP{o, S.MSP{R.RunSt{n, i, h, c, e, l, b, k, o2, ns, x}, qs, ql, None{}}, src, pd, eof, back, wp, asked, fneed, dfs}, cs))
  +DF = L.defs.go(ls, i, dfs)
  %Equal.sym(R.RunSt, S.RG(S.recs(src), fa, DF, o, st), st, RGH.rg_halted(S.recs(src), fa, DF, o, st, hx)) :
    {R.finish(L.run.go(ls, fa, DF, o, _)) == R.finish(st) : R.Report}
  Equal.cong(R.RunSt, R.Report, z => R.finish(z), L.run.go(ls, fa, DF, o, st), st, FM.run_halted(DF, ls, fa, o, st, hx))


law nl_eof_ms:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +o: B.Opts
  for +s: R.RunSt
  for +qs: List<&2, String>
  for +ql: Nat
  for +pd: P.PdP
  for +back: Nat
  for +wp: PC.WP
  for +asked: Maybe<&2, List<&2, Pr.Req>>
  for +fneed: Bool
  for +hw: {S.WF(fa, S.StP{o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, True{}, back, wp, asked, fneed, dfs}) == True{} : Bool}
  DF.NoLines(fa, cs, O, N, S.StP{o, S.MSP{s, qs, ql, None{}}, Nil{}, pd, True{}, back, wp, asked, fneed, dfs})

def nl_eof_ms(dfs,fa, cs, O, N, o, s, qs, ql, pd, back, wp, asked, fneed, hw):
  %Equal.sym(String, P.pdtext(pd), "", DF.pd_eof(dfs, fa, o, S.MSP{s, qs, ql, None{}}, pd, back, wp, asked, fneed, hw)) :
    {R.finish(L.run.go(B.Text.lines(String.append("", String.append(_, ""))), fa, L.defs.go(B.Text.lines(String.append("", String.append(_, ""))), R.RunSt.inbody(S.with_out(s, Norm.cat(List.reverse(&2, String, qs)))), dfs), o, S.pre(O, N, S.with_out(s, Norm.cat(List.reverse(&2, String, qs)))))) == R.finish(S.pre(O, N, S.with_out(s, Norm.cat(List.reverse(&2, String, qs))))) : R.Report}
  {==}

