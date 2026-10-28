import Base
import ./types.bend as B
import ./norm_line.bend as J
import ./proof_base.bend as P
import ./proof_fast.bend as PF
import ./proof_run_rec.bend as RR

# Phase C, the rewritten line's text at the String level: Rec.rebuild of a
# record whose INFO has no END entry is the record with POS, REF and ALT
# replaced, every other byte kept. Every variable is reusable.

# ---------------------------------------------------------------------------
# Strings
# ---------------------------------------------------------------------------

law sapp_assoc:
  for +a: String
  for +b: String
  for +c: String
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}

def sapp_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %sapp_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def scon_tail(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

law sapp_cancel:
  for +a: String
  for +x: String
  for +y: String
  for +e: {String.append(a, x) == String.append(a, y) : String}
  {x == y : String}

def sapp_cancel(a, x, y, e):
  match a:
    case SNil{}:
      e
    case SCon{+h, +t}:
      sapp_cancel(t, x, y, Equal.cong(String, String, z => scon_tail(z), SCon{h, String.append(t, x)}, SCon{h, String.append(t, y)}, e))

# Fields joined with tabs, the last part given: x0 \t x1 \t ... \t tail.
def TJ(xs: List<&2, String>, +tail: String) -> String:
  match xs:
    case Nil{}:
      tail
    case x <> t:
      String.append(x, String.append("\t", TJ(t, tail)))

law tj_app:
  for +xs: List<&2, String>
  for +a: String
  for +c: String
  {String.append(TJ(xs, a), c) == TJ(xs, String.append(a, c)) : String}

def tj_app(xs, a, c):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(String, String.append(String.append(x, String.append("\t", TJ(t, a))), c), String.append(x, String.append(String.append("\t", TJ(t, a)), c)), sapp_assoc(x, String.append("\t", TJ(t, a)), c)) : {_ == TJ(x <> t, String.append(a, c)) : String}
      %Equal.sym(String, String.append(String.append("\t", TJ(t, a)), c), String.append("\t", String.append(TJ(t, a), c)), sapp_assoc("\t", TJ(t, a), c)) : {String.append(x, _) == TJ(x <> t, String.append(a, c)) : String}
      %Equal.sym(String, String.append(TJ(t, a), c), TJ(t, String.append(a, c)), tj_app(t, a, c)) : {String.append(x, String.append("\t", _)) == TJ(x <> t, String.append(a, c)) : String}
      {==}

law tj_cancel:
  for +xs: List<&2, String>
  for +a: String
  for +b: String
  for +e: {TJ(xs, a) == TJ(xs, b) : String}
  {a == b : String}

def tj_cancel(xs, a, b, e):
  match xs:
    case Nil{}:
      e
    case +x <> +t:
      tj_cancel(t, a, b, sapp_cancel("\t", TJ(t, a), TJ(t, b), sapp_cancel(x, String.append("\t", TJ(t, a)), String.append("\t", TJ(t, b)), e)))

# ---------------------------------------------------------------------------
# INFO without an END entry
# ---------------------------------------------------------------------------

law or_false_r_inv:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_r_inv(a, b, e):
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.true_ne_false(e))
    case False{}:
      e

law sed_go:
  for +ps: List<&2, String>
  for +e: Nat
  for +h: {B.Info.has.go(ps, "END") == False{} : Bool}
  {B.Info.set_end.go(ps, e) == ps : List<&2, String>}

def sed_go(ps, e, h):
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      +k = String.eq(B.Info.key(p), "END")
      %Equal.sym(Bool, k, False{}, P.or_false_inv(k, B.Info.has.go(t, "END"), h)) : {B.Info.set_end.put(_, p, e) <> B.Info.set_end.go(t, e) == p <> t : List<&2, String>}
      %Equal.sym(List<&2, String>, B.Info.set_end.go(t, e), t, sed_go(t, e, or_false_r_inv(k, B.Info.has.go(t, "END"), h))) : {p <> _ == p <> t : List<&2, String>}
      {==}

# Info.set_end changes nothing when INFO has no END entry.
law set_end_id:
  for +info: String
  for +e: Nat
  for +h: {B.Info.has(info, "END") == False{} : Bool}
  {B.Info.set_end(info, e) == info : String}

def set_end_id(info, e, h):
  %Equal.sym(List<&2, String>, B.Info.set_end.go(String.split(info, ';'), e), String.split(info, ';'), sed_go(String.split(info, ';'), e, h)) : {String.join(_, ";") == info : String}
  RR.join_split(info, ';')

law info_id:
  for +mv: Bool
  for +info: String
  for +w: B.Var
  for +h: {B.Info.has(info, "END") == False{} : Bool}
  {B.Rec.info(mv, info, w) == info : String}

def info_id(mv, info, w, h):
  match mv w:
    case True{} B.Var{+q, +s, +y}:
      set_end_id(info, Nat.sub(Nat.add(q, List.length(&2, B.Base, s)), 1n), h)
    case False{} _:
      {==}

# ---------------------------------------------------------------------------
# Rec.rebuild
# ---------------------------------------------------------------------------

def L7(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +R: List<&2, String>) -> List<&2, String>:
  f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> R

# The record rewritten for w: POS, REF and ALT replaced (INFO, field 7, has
# no END entry, so it is kept).
law rebuild_fix:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +R: List<&2, String>
  for +v: B.Var
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +h7: {B.Info.has(B.Rec.field(R, 1n), "END") == False{} : Bool}
  {B.Rec.rebuild(L7(f0, f1, f2, f3, f4, f5, R), v, B.Var{q, s, y}) == String.join(L7(f0, Nat.show(q), f2, B.Allele.show(s), String.join(B.Alleles.show(y), ","), f5, R), "\t") : String}

def rebuild_fix(f0, f1, f2, f3, f4, f5, R, v, q, s, y, h7):
  +w = {B.Var{q, s, y} : B.Var}
  +I = B.Rec.field(R, 1n)
  +L = L7(f0, Nat.show(q), f2, B.Allele.show(s), String.join(B.Alleles.show(y), ","), f5, R)
  %Equal.sym(String, B.Rec.info(B.Rec.moved(v, w), I, w), I, info_id(B.Rec.moved(v, w), I, w, h7)) :
    {String.join(B.Rec.put(B.Rec.put(B.Rec.put(B.Rec.put(L7(f0, f1, f2, f3, f4, f5, R), 1n, Nat.show(q)), 3n, B.Allele.show(s)), 4n, String.join(B.Alleles.show(y), ",")), 7n, _), "\t") == String.join(L, "\t") : String}
  %Equal.sym(List<&2, String>, B.Rec.put(R, 1n, I), R, RR.put_same(R, 1n, I, {==})) :
    {String.join(f0 <> Nat.show(q) <> f2 <> B.Allele.show(s) <> String.join(B.Alleles.show(y), ",") <> f5 <> _, "\t") == String.join(L, "\t") : String}
  {==}

# ---------------------------------------------------------------------------
# The fields of a line whose first 8 the machine cut
# ---------------------------------------------------------------------------

def FSH(+body: String, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String) -> Type:
  &R: List<&2, String> -> {B.Rec.fields(body) == L7(f0, f1, f2, f3, f4, f5, R) : List<&2, String>}

def fsh.m(+g: J.C7, +body: String, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String,
  +hs: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>},
  +hp: {J.pfs.g(g, body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}) ->
  FSH(body, f0, f1, f2, f3, f4, f5):
  match g:
    case J.Got{+g0, +g1, +g2, +g3, +g4, +g5, +g6, +r}:
      +G = {[g0, g1, g2, g3, g4, g5, g6, J.info.if(J.noend(r), r)] : List<&2, String>}
      +F = {[f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}
      +e0 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 0n), G, F, hp)
      +e1 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 1n), G, F, hp)
      +e2 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 2n), G, F, hp)
      +e3 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 3n), G, F, hp)
      +e4 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 4n), G, F, hp)
      +e5 = Equal.cong(List<&2, String>, String, z => B.Rec.field(z, 5n), G, F, hp)
      +R0 = {g6 <> String.split(r, '\t') : List<&2, String>}
      %e0 : FSH(body, _, f1, f2, f3, f4, f5)
      %e1 : FSH(body, g0, _, f2, f3, f4, f5)
      %e2 : FSH(body, g0, g1, _, f3, f4, f5)
      %e3 : FSH(body, g0, g1, g2, _, f4, f5)
      %e4 : FSH(body, g0, g1, g2, g3, _, f5)
      %e5 : FSH(body, g0, g1, g2, g3, g4, _)
      (R0, Equal.sym(List<&2, String>, L7(g0, g1, g2, g3, g4, g5, R0), B.Rec.fields(body), hs))
    case J.Short{}:
      ([f6, ""], hp)

def fsh.g(+g: J.C7, +body: String, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String,
  +hg: {J.c7(body) == g : J.C7},
  +hpf: {J.pfs(body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}) ->
  FSH(body, f0, f1, f2, f3, f4, f5):
  +hs = {%hg : {PF.gsplit(_, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}; PF.c7_split(body) : {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}}
  +hp = {%hg : {J.pfs.g(_, body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}; hpf : {J.pfs.g(g, body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}}
  fsh.m(g, body, f0, f1, f2, f3, f4, f5, f6, hs, hp)

# The full split of a line whose kept fields are f0 .. f6 (J.pfs) starts
# with f0 .. f5.
def fsh(+body: String, +f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String,
  +hpf: {J.pfs(body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}) ->
  FSH(body, f0, f1, f2, f3, f4, f5):
  fsh.g(J.c7(body), body, f0, f1, f2, f3, f4, f5, f6, {==}, hpf)

# A list of fields joined: TJ of its first five.
law join_tj:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +R: List<&2, String>
  {String.join(L7(f0, f1, f2, f3, f4, f5, R), "\t") == TJ([f0, f1, f2, f3, f4], String.join.go(R, f5, "\t")) : String}

def join_tj(f0, f1, f2, f3, f4, f5, R):
  {==}
