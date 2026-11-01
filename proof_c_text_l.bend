import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_b_cut.bend as CU
import ./proof_b_alleles_list.bend as AL
import ./proof_b_adv_slow.bend as SLW
import ./proof_b_lines_str.bend as LSS
import ./proof_c_text_s.bend as TS
import ./proof_run_rec.bend as RR
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_same.bend as SM
import lawful-bytes@0.1.1.0/proof_append.bend as PA
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase C: the rewritten line's text, from the line's own bytes: its pieces
# (CHROM and its tab, the tab, ID and the tab after it, the line from ALT's
# tab to its LF) are the String path's fields, so the text the writer builds
# is B.Rec.rebuild's with the line's terminator. Every variable is reusable.

def FLD(+X: List<&2, U32>, +a: Nat, +b: Nat) -> String:
  CU.fld(X, a, b)

law nchars_app:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  {Norm.chars(List.append(&2, U32, xs, ys)) == String.append(Norm.chars(xs), Norm.chars(ys)) : String}

def nchars_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Norm.chars(List.append(&2, U32, t, ys)), String.append(Norm.chars(t), Norm.chars(ys)), nchars_app(t, ys)) :
        {SCon{Chr{x}, _} == String.append(Norm.chars(Con{x, t}), Norm.chars(ys)) : String}
      {==}

law sub_one:
  for +c: Nat
  for +e: Nat
  for +h: {Nat.is_lt(e, c) == True{} : Bool}
  {Nat.sub(c, e) == 1n+Nat.sub(c, Nat.add(e, 1n)) : Nat}

def sub_one(c, e, h):
  match c e:
    case 0n _:
      Empty.absurd({Nat.sub(0n, e) == 1n+Nat.sub(0n, Nat.add(e, 1n)) : Nat}, P.true_ne_false(Equal.trans(Bool, True{}, Nat.is_lt(e, 0n), False{}, Equal.sym(Bool, Nat.is_lt(e, 0n), True{}, h), P.lt_zero(e))))
    case 1n+(+c2) 0n:
      %Equal.sym(Nat, Nat.sub(c2, 0n), c2, P.sub_zero(c2)) : {1n+c2 == 1n+_ : Nat}
      {==}
    case 1n+(+c2) 1n+(+e2):
      sub_one(c2, e2, h)

# A tab at e splits the text of bytes a .. c-1 there.
law st:
  for +X: List<&2, U32>
  for +a: Nat
  for +e: Nat
  for +c: Nat
  for +hae: {Nat.is_le(a, e) == True{} : Bool}
  for +hec: {Nat.is_lt(e, c) == True{} : Bool}
  for +htab: {List.get(&2, U32, X, e) == Some{9} : Maybe<&2, U32>}
  {FLD(X, a, c) == String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))) : String}

def st(X, a, e, c, hae, hec, htab):
  +k = Nat.sub(c, Nat.add(e, 1n))
  %Equal.sym(List<&2, U32>, D.slice(X, a, Nat.sub(c, a)), List.append(&2, U32, D.slice(X, a, Nat.sub(e, a)), D.slice(X, e, Nat.sub(c, e))), AL.slice_app(X, a, e, c, hae, N.lt_to_le(e, c, hec))) :
    {Norm.chars(_) == String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))) : String}
  %Equal.sym(String, Norm.chars(List.append(&2, U32, D.slice(X, a, Nat.sub(e, a)), D.slice(X, e, Nat.sub(c, e)))), String.append(Norm.chars(D.slice(X, a, Nat.sub(e, a))), Norm.chars(D.slice(X, e, Nat.sub(c, e)))), nchars_app(D.slice(X, a, Nat.sub(e, a)), D.slice(X, e, Nat.sub(c, e)))) :
    {_ == String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))) : String}
  %Equal.sym(Nat, Nat.sub(c, e), 1n+k, sub_one(c, e, hec)) :
    {String.append(FLD(X, a, e), Norm.chars(D.slice(X, e, _))) == String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))) : String}
  %Equal.sym(List<&2, U32>, D.slice(X, e, 1n+k), 9 <> D.slice(X, Nat.add(e, 1n), k), SM.slice_cons(X, e, k, 9, htab)) :
    {String.append(FLD(X, a, e), Norm.chars(_)) == String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))) : String}
  {==}

law sub_self:
  for +x: Nat
  {Nat.sub(x, x) == 0n : Nat}

def sub_self(x):
  match x:
    case 0n:
      {==}
    case 1n+(+p):
      sub_self(p)

law fld_empty:
  for +X: List<&2, U32>
  for +a: Nat
  {FLD(X, a, a) == "" : String}

def fld_empty(X, a):
  %Equal.sym(Nat, Nat.sub(a, a), 0n, sub_self(a)) : {Norm.chars(D.slice(X, a, _)) == "" : String}
  %Equal.sym(List<&2, U32>, D.slice(X, a, 0n), Nil{}, PA.slice_zero(X, a)) : {Norm.chars(_) == "" : String}
  {==}

law sapp_nil:
  for +s: String
  {String.append(s, "") == s : String}

def sapp_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(String, String.append(t, ""), t, sapp_nil(t)) : {SCon{h, _} == SCon{h, t} : String}
      {==}

law lt_nx:
  for +e: Nat
  {Nat.is_lt(e, Nat.add(e, 1n)) == True{} : Bool}

def lt_nx(e):
  match e:
    case 0n:
      {==}
    case 1n+(+p):
      lt_nx(p)

law nx_le:
  for +x: Nat
  for +y: Nat
  for +h: {Nat.is_lt(x, y) == True{} : Bool}
  {Nat.is_le(Nat.add(x, 1n), y) == True{} : Bool}

def nx_le(x, y, h):
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, N.add_one(x)) : {Nat.is_le(_, y) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+x, y), Nat.is_lt(x, y), N.le_succ_lt(x, y)) : {_ == True{} : Bool}
  h

# Bytes a .. e, e a tab: the text of a .. e-1 and the tab.
law fld_tab_end:
  for +X: List<&2, U32>
  for +a: Nat
  for +e: Nat
  for +hae: {Nat.is_le(a, e) == True{} : Bool}
  for +htab: {List.get(&2, U32, X, e) == Some{9} : Maybe<&2, U32>}
  {FLD(X, a, Nat.add(e, 1n)) == String.append(FLD(X, a, e), "\t") : String}

def fld_tab_end(X, a, e, hae, htab):
  %Equal.sym(String, FLD(X, a, Nat.add(e, 1n)), String.append(FLD(X, a, e), String.append("\t", FLD(X, Nat.add(e, 1n), Nat.add(e, 1n)))), st(X, a, e, Nat.add(e, 1n), hae, lt_nx(e), htab)) :
    {_ == String.append(FLD(X, a, e), "\t") : String}
  %Equal.sym(String, FLD(X, Nat.add(e, 1n), Nat.add(e, 1n)), "", fld_empty(X, Nat.add(e, 1n))) :
    {String.append(FLD(X, a, e), String.append("\t", _)) == String.append(FLD(X, a, e), "\t") : String}
  {==}

# Bytes e .. c-1, e a tab: the tab and the text of e+1 .. c-1.
law fld_tab_start:
  for +X: List<&2, U32>
  for +e: Nat
  for +c: Nat
  for +hec: {Nat.is_lt(e, c) == True{} : Bool}
  for +htab: {List.get(&2, U32, X, e) == Some{9} : Maybe<&2, U32>}
  {FLD(X, e, c) == String.append("\t", FLD(X, Nat.add(e, 1n), c)) : String}

def fld_tab_start(X, e, c, hec, htab):
  %Equal.sym(String, FLD(X, e, c), String.append(FLD(X, e, e), String.append("\t", FLD(X, Nat.add(e, 1n), c))), st(X, e, e, c, N.le_refl(e), hec, htab)) :
    {_ == String.append("\t", FLD(X, Nat.add(e, 1n), c)) : String}
  %Equal.sym(String, FLD(X, e, e), "", fld_empty(X, e)) :
    {String.append(_, String.append("\t", FLD(X, Nat.add(e, 1n), c))) == String.append("\t", FLD(X, Nat.add(e, 1n), c)) : String}
  {==}

# Bytes a .. c-1 split at e (no tab).
law fld_split:
  for +X: List<&2, U32>
  for +a: Nat
  for +e: Nat
  for +c: Nat
  for +hae: {Nat.is_le(a, e) == True{} : Bool}
  for +hec: {Nat.is_le(e, c) == True{} : Bool}
  {FLD(X, a, c) == String.append(FLD(X, a, e), FLD(X, e, c)) : String}

def fld_split(X, a, e, c, hae, hec):
  %Equal.sym(List<&2, U32>, D.slice(X, a, Nat.sub(c, a)), List.append(&2, U32, D.slice(X, a, Nat.sub(e, a)), D.slice(X, e, Nat.sub(c, e))), AL.slice_app(X, a, e, c, hae, hec)) :
    {Norm.chars(_) == String.append(FLD(X, a, e), FLD(X, e, c)) : String}
  nchars_app(D.slice(X, a, Nat.sub(e, a)), D.slice(X, e, Nat.sub(c, e)))

def nx(+e: Nat) -> Nat:
  Nat.add(e, 1n)

# A line's bytes a .. c-1 with tabs at x0 .. x3: its first five fields
# (TS.TJ), then bytes x4 .. c-1.
law line5:
  for +X: List<&2, U32>
  for +a: Nat
  for +x0: Nat
  for +x1: Nat
  for +x2: Nat
  for +x3: Nat
  for +x4: Nat
  for +c: Nat
  for +h0: {Nat.is_le(a, x0) == True{} : Bool}
  for +h1: {Nat.is_lt(x0, x1) == True{} : Bool}
  for +h2: {Nat.is_lt(x1, x2) == True{} : Bool}
  for +h3: {Nat.is_lt(x2, x3) == True{} : Bool}
  for +h4: {Nat.is_lt(x3, x4) == True{} : Bool}
  for +h5: {Nat.is_le(x4, c) == True{} : Bool}
  for +t0: {List.get(&2, U32, X, x0) == Some{9} : Maybe<&2, U32>}
  for +t1: {List.get(&2, U32, X, x1) == Some{9} : Maybe<&2, U32>}
  for +t2: {List.get(&2, U32, X, x2) == Some{9} : Maybe<&2, U32>}
  for +t3: {List.get(&2, U32, X, x3) == Some{9} : Maybe<&2, U32>}
  {FLD(X, a, c) == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}

def line5(X, a, x0, x1, x2, x3, x4, c, h0, h1, h2, h3, h4, h5, t0, t1, t2, t3):
  +l34 = N.lt_le_trans(x3, x4, c, h4, h5)
  +l23 = N.lt_trans(x2, x3, c, h3, l34)
  +l12 = N.lt_trans(x1, x2, c, h2, l23)
  +l01 = N.lt_trans(x0, x1, c, h1, l12)
  %Equal.sym(String, FLD(X, a, c), String.append(FLD(X, a, x0), String.append("\t", FLD(X, nx(x0), c))), st(X, a, x0, c, h0, l01, t0)) :
    {_ == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}
  %Equal.sym(String, FLD(X, nx(x0), c), String.append(FLD(X, nx(x0), x1), String.append("\t", FLD(X, nx(x1), c))), st(X, nx(x0), x1, c, nx_le(x0, x1, h1), l12, t1)) :
    {String.append(FLD(X, a, x0), String.append("\t", _)) == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}
  %Equal.sym(String, FLD(X, nx(x1), c), String.append(FLD(X, nx(x1), x2), String.append("\t", FLD(X, nx(x2), c))), st(X, nx(x1), x2, c, nx_le(x1, x2, h2), l23, t2)) :
    {String.append(FLD(X, a, x0), String.append("\t", String.append(FLD(X, nx(x0), x1), String.append("\t", _)))) == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}
  %Equal.sym(String, FLD(X, nx(x2), c), String.append(FLD(X, nx(x2), x3), String.append("\t", FLD(X, nx(x3), c))), st(X, nx(x2), x3, c, nx_le(x2, x3, h3), l34, t3)) :
    {String.append(FLD(X, a, x0), String.append("\t", String.append(FLD(X, nx(x0), x1), String.append("\t", String.append(FLD(X, nx(x1), x2), String.append("\t", _)))))) == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}
  %Equal.sym(String, FLD(X, nx(x3), c), String.append(FLD(X, nx(x3), x4), FLD(X, x4, c)), fld_split(X, nx(x3), x4, c, nx_le(x3, x4, h4), h5)) :
    {String.append(FLD(X, a, x0), String.append("\t", String.append(FLD(X, nx(x0), x1), String.append("\t", String.append(FLD(X, nx(x1), x2), String.append("\t", String.append(FLD(X, nx(x2), x3), String.append("\t", _)))))))) == TS.TJ([FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3)], String.append(FLD(X, nx(x3), x4), FLD(X, x4, c))) : String}
  {==}

# The line's text is its body's five fields and the rest, then its
# terminator: so bytes x4 .. c-1 (from ALT's tab) are the tab, the rest of
# the body and the terminator.
law tail_eq:
  for +l: B.Line
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +JG: String
  for +T4: String
  for +hl: {B.Line.text(l) == TS.TJ([f0, f1, f2, f3], String.append(f4, T4)) : String}
  for +hb: {B.Line.body(l) == TS.TJ([f0, f1, f2, f3, f4], JG) : String}
  {T4 == String.append("\t", String.append(JG, B.Line.term(l))) : String}

def tail_eq(l, f0, f1, f2, f3, f4, JG, T4, hl, hb):
  +tm = B.Line.term(l)
  +F = {[f0, f1, f2, f3] : List<&2, String>}
  +e1 = Equal.trans(String, TS.TJ(F, String.append(f4, T4)), B.Line.text(l), String.append(TS.TJ([f0, f1, f2, f3, f4], JG), tm),
    Equal.sym(String, B.Line.text(l), TS.TJ(F, String.append(f4, T4)), hl),
    Equal.trans(String, B.Line.text(l), String.append(B.Line.body(l), tm), String.append(TS.TJ([f0, f1, f2, f3, f4], JG), tm), SLW.lt_split(l),
      Equal.cong(String, String, z => String.append(z, tm), B.Line.body(l), TS.TJ([f0, f1, f2, f3, f4], JG), hb)))
  +e2 = Equal.trans(String, TS.TJ(F, String.append(f4, T4)), String.append(TS.TJ(F, String.append(f4, String.append("\t", JG))), tm), TS.TJ(F, String.append(String.append(f4, String.append("\t", JG)), tm)),
    e1, TS.tj_app(F, String.append(f4, String.append("\t", JG)), tm))
  +e3 = TS.tj_cancel(F, String.append(f4, T4), String.append(String.append(f4, String.append("\t", JG)), tm), e2)
  +e4 = Equal.trans(String, String.append(f4, T4), String.append(String.append(f4, String.append("\t", JG)), tm), String.append(f4, String.append(String.append("\t", JG), tm)),
    e3, TS.sapp_assoc(f4, String.append("\t", JG), tm))
  TS.sapp_cancel(f4, T4, String.append(String.append("\t", JG), tm), e4)

# The writer's pieces put together: the five new fields, the rest of the
# body, the terminator.
law shape:
  for +f0: String
  for +q: String
  for +f2: String
  for +rs: String
  for +as: String
  for +JG: String
  for +tm: String
  {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), as), String.append("\t", String.append(JG, tm)))
    == String.append(TS.TJ([f0, q, f2, rs, as], JG), tm) : String}

def shape(f0, q, f2, rs, as, JG, tm):
  %Equal.sym(String, String.append(TS.TJ([f0, q, f2, rs, as], JG), tm), TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)), TS.tj_app([f0, q, f2, rs, as], JG, tm)) :
    {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), as), String.append("\t", String.append(JG, tm))) == _ : String}
  %Equal.sym(String, String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), as), String.append("\t", String.append(JG, tm))), String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), String.append(as, String.append("\t", String.append(JG, tm)))), TS.sapp_assoc(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), as, String.append("\t", String.append(JG, tm)))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t"), String.append(as, String.append("\t", String.append(JG, tm)))), String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))), TS.sapp_assoc(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), "\t", String.append(as, String.append("\t", String.append(JG, tm))))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs), String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))), String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))), TS.sapp_assoc(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t"))), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))), String.append(String.append(String.append(f0, "\t"), q), String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))), TS.sapp_assoc(String.append(String.append(f0, "\t"), q), String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(String.append(f0, "\t"), q), String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))), String.append(String.append(f0, "\t"), String.append(q, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))))), TS.sapp_assoc(String.append(f0, "\t"), q, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(f0, "\t"), String.append(q, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))))), String.append(f0, String.append("\t", String.append(q, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))))), TS.sapp_assoc(f0, "\t", String.append(q, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))))) :
    {_ == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append("\t", String.append(f2, "\t")), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))), String.append("\t", String.append(String.append(f2, "\t"), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))), TS.sapp_assoc("\t", String.append(f2, "\t"), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))) :
    {String.append(f0, String.append("\t", String.append(q, _))) == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  %Equal.sym(String, String.append(String.append(f2, "\t"), String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm)))))), String.append(f2, String.append("\t", String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))), TS.sapp_assoc(f2, "\t", String.append(rs, String.append("\t", String.append(as, String.append("\t", String.append(JG, tm))))))) :
    {String.append(f0, String.append("\t", String.append(q, String.append("\t", _)))) == TS.TJ([f0, q, f2, rs, as], String.append(JG, tm)) : String}
  {==}

# The writer's text, on the line's bytes, is the record rewritten for
# Var{qn, s, y} (INFO, field 7, has no END entry) with the line's terminator.
law tx_eq:
  for +X: List<&2, U32>
  for +l: B.Line
  for +a: Nat
  for +x0: Nat
  for +x1: Nat
  for +x2: Nat
  for +x3: Nat
  for +x4: Nat
  for +c: Nat
  for +f5: String
  for +R: List<&2, String>
  for +v: B.Var
  for +qn: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +h0: {Nat.is_le(a, x0) == True{} : Bool}
  for +h1: {Nat.is_lt(x0, x1) == True{} : Bool}
  for +h2: {Nat.is_lt(x1, x2) == True{} : Bool}
  for +h3: {Nat.is_lt(x2, x3) == True{} : Bool}
  for +h4: {Nat.is_lt(x3, x4) == True{} : Bool}
  for +h5: {Nat.is_le(x4, c) == True{} : Bool}
  for +t0: {List.get(&2, U32, X, x0) == Some{9} : Maybe<&2, U32>}
  for +t1: {List.get(&2, U32, X, x1) == Some{9} : Maybe<&2, U32>}
  for +t2: {List.get(&2, U32, X, x2) == Some{9} : Maybe<&2, U32>}
  for +t3: {List.get(&2, U32, X, x3) == Some{9} : Maybe<&2, U32>}
  for +hlt: {B.Line.text(l) == FLD(X, a, c) : String}
  for +hfs: {B.Rec.fields(B.Line.body(l)) == TS.L7(FLD(X, a, x0), FLD(X, nx(x0), x1), FLD(X, nx(x1), x2), FLD(X, nx(x2), x3), FLD(X, nx(x3), x4), f5, R) : List<&2, String>}
  for +hin: {B.Info.has(B.Rec.field(R, 1n), "END") == False{} : Bool}
  {String.append(String.append(String.append(String.append(String.append(String.append(FLD(X, a, nx(x0)), Nat.show(qn)), FLD(X, x1, nx(x2))), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), FLD(X, x4, c))
    == String.append(B.Rec.rebuild(B.Rec.fields(B.Line.body(l)), v, B.Var{qn, s, y}), B.Line.term(l)) : String}

def tx_eq(X, l, a, x0, x1, x2, x3, x4, c, f5, R, v, qn, s, y, h0, h1, h2, h3, h4, h5, t0, t1, t2, t3, hlt, hfs, hin):
  +f0 = FLD(X, a, x0)
  +f1 = FLD(X, nx(x0), x1)
  +f2 = FLD(X, nx(x1), x2)
  +f3 = FLD(X, nx(x2), x3)
  +f4 = FLD(X, nx(x3), x4)
  +JG = String.join.go(R, f5, "\t")
  +tm = B.Line.term(l)
  +body = B.Line.body(l)
  +L = TS.L7(f0, f1, f2, f3, f4, f5, R)
  +hbody = Equal.trans(String, body, String.join(B.Rec.fields(body), "\t"), TS.TJ([f0, f1, f2, f3, f4], JG),
    Equal.sym(String, String.join(B.Rec.fields(body), "\t"), body, RR.join_split(body, '\t')),
    Equal.trans(String, String.join(B.Rec.fields(body), "\t"), String.join(L, "\t"), TS.TJ([f0, f1, f2, f3, f4], JG),
      Equal.cong(List<&2, String>, String, z => String.join(z, "\t"), B.Rec.fields(body), L, hfs), TS.join_tj(f0, f1, f2, f3, f4, f5, R)))
  +hl5 = Equal.trans(String, B.Line.text(l), FLD(X, a, c), TS.TJ([f0, f1, f2, f3], String.append(f4, FLD(X, x4, c))), hlt,
    line5(X, a, x0, x1, x2, x3, x4, c, h0, h1, h2, h3, h4, h5, t0, t1, t2, t3))
  +ht = tail_eq(l, f0, f1, f2, f3, f4, JG, FLD(X, x4, c), hl5, hbody)
  +l12 = N.lt_trans(x1, x2, nx(x2), h2, lt_nx(x2))
  +h2f = Equal.trans(String, FLD(X, x1, nx(x2)), String.append("\t", FLD(X, nx(x1), nx(x2))), String.append("\t", String.append(f2, "\t")),
    fld_tab_start(X, x1, nx(x2), l12, t1),
    Equal.cong(String, String, z => String.append("\t", z), FLD(X, nx(x1), nx(x2)), String.append(f2, "\t"), fld_tab_end(X, nx(x1), x2, nx_le(x1, x2, h2), t2)))
  %Equal.sym(String, FLD(X, a, nx(x0)), String.append(f0, "\t"), fld_tab_end(X, a, x0, h0, t0)) :
    {String.append(String.append(String.append(String.append(String.append(String.append(_, Nat.show(qn)), FLD(X, x1, nx(x2))), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), FLD(X, x4, c)) == String.append(B.Rec.rebuild(B.Rec.fields(body), v, B.Var{qn, s, y}), tm) : String}
  %Equal.sym(String, FLD(X, x1, nx(x2)), String.append("\t", String.append(f2, "\t")), h2f) :
    {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), Nat.show(qn)), _), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), FLD(X, x4, c)) == String.append(B.Rec.rebuild(B.Rec.fields(body), v, B.Var{qn, s, y}), tm) : String}
  %Equal.sym(String, FLD(X, x4, c), String.append("\t", String.append(JG, tm)), ht) :
    {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), Nat.show(qn)), String.append("\t", String.append(f2, "\t"))), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), _) == String.append(B.Rec.rebuild(B.Rec.fields(body), v, B.Var{qn, s, y}), tm) : String}
  %Equal.sym(List<&2, String>, B.Rec.fields(body), L, hfs) :
    {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), Nat.show(qn)), String.append("\t", String.append(f2, "\t"))), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), String.append("\t", String.append(JG, tm))) == String.append(B.Rec.rebuild(_, v, B.Var{qn, s, y}), tm) : String}
  %Equal.sym(String, B.Rec.rebuild(L, v, B.Var{qn, s, y}), String.join(TS.L7(f0, Nat.show(qn), f2, B.Allele.show(s), String.join(B.Alleles.show(y), ","), f5, R), "\t"), TS.rebuild_fix(f0, f1, f2, f3, f4, f5, R, v, qn, s, y, hin)) :
    {String.append(String.append(String.append(String.append(String.append(String.append(String.append(f0, "\t"), Nat.show(qn)), String.append("\t", String.append(f2, "\t"))), B.Allele.show(s)), "\t"), String.join(B.Alleles.show(y), ",")), String.append("\t", String.append(JG, tm))) == String.append(_, tm) : String}
  shape(f0, Nat.show(qn), f2, B.Allele.show(s), String.join(B.Alleles.show(y), ","), JG, tm)
