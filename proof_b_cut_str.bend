import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_shift.bend as PSh
import lawful-bytes@0.1.0.0/proof_append.bend as PA
import lawful-bytes@0.1.0.0/proof_seq.bend as PSq
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_find.bend as PF
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Lines and fields as text: Norm.chars of slices of a list of bytes.

def chars_app(+xs: List<&2, U32>, +ys: List<&2, U32>) ->
  {Norm.chars(List.append(&2, U32, xs, ys)) == Norm.chars(xs) ++ Norm.chars(ys) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(String, Norm.chars(List.append(&2, U32, t, ys)), Norm.chars(t) ++ Norm.chars(ys), chars_app(t, ys)) :
        {SCon{Chr{x}, _} == SCon{Chr{x}, Norm.chars(t) ++ Norm.chars(ys)} : String}
      {==}

def chr_eq(+x: U32, +y: U32, +h: {Char.is_eq(Chr{x}, Chr{y}) == True{} : Bool}) -> {Chr{x} == Chr{y} : Char}:
  Equal.cong(U32, Char, z => Chr{z}, x, y, U.is_eq_true(x, y, h))

# A text that ends with CR: its terminator CR LF is the same text as LF
# after the whole text.
def ecr_go(+t: String, +h: Char, +hh: {Norm.ends_cr.go(t, h) == True{} : Bool}) ->
  {String.take(SCon{h, t}, Nat.sub(String.length(SCon{h, t}), 1n)) ++ "\r\n" == SCon{h, t} ++ "\n" : String}:
  match t h:
    case SNil{} Chr{+x}:
      %Equal.sym(Char, Chr{x}, Chr{13}, chr_eq(x, 13, hh)) : {"\r\n" == SCon{_, "\n"} : String}
      {==}
    case SCon{+h2, +t2} _:
      +ih = AB.subst(Nat, z => {String.take(SCon{h2, t2}, z) ++ "\r\n" == SCon{h2, t2} ++ "\n" : String}, Nat.sub(String.length(t2), 0n), String.length(t2),
        N.sub_zero(String.length(t2)), ecr_go(t2, h2, hh))
      %Equal.sym(String, String.take(SCon{h2, t2}, String.length(t2)) ++ "\r\n", SCon{h2, t2} ++ "\n", ih) :
        {SCon{h, _} == SCon{h, SCon{h2, t2} ++ "\n"} : String}
      {==}

def lt_k(+b: Bool, +p: String, +hb: {Norm.ends_cr(p) == b : Bool}) ->
  {B.Line.text(B.Text.line.if(b, p)) == p ++ "\n" : String}:
  match b p:
    case False{} _:
      {==}
    case True{} SNil{}:
      Empty.absurd({B.Line.text(B.Text.line.if(True{}, SNil{})) == SNil{} ++ "\n" : String}, N.false_ne_true(hb))
    case True{} SCon{+h, +t}:
      ecr_go(t, h, hb)

# Norm.line's text with its terminator is the text and an LF.
def ltext_nl(+p: String) -> {B.Line.text(Norm.line(p)) == p ++ "\n" : String}:
  lt_k(Norm.ends_cr(p), p, {==})

def chars_snoc(+ys: List<&2, U32>, +j: Nat, +x: U32, +h: {List.get(&2, U32, ys, j) == Some{x} : Maybe<&2, U32>}) ->
  {Norm.chars(List.take(&2, U32, ys, Nat.add(j, 1n))) == Norm.chars(List.take(&2, U32, ys, j)) ++ SCon{Chr{x}, SNil{}} : String}:
  %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, Nat.add(j, 1n)), List.append(&2, U32, List.take(&2, U32, ys, j), [x]), PSh.take_snoc(ys, j, x, h)) : {Norm.chars(_) == Norm.chars(List.take(&2, U32, ys, j)) ++ SCon{Chr{x}, SNil{}} : String}
  chars_app(List.take(&2, U32, ys, j), [x])

# The text of bytes a .. b, with the LF at b.
def fld_nl(+xs: List<&2, U32>, +a: Nat, +b: Nat, +hlf: {List.get(&2, U32, xs, b) == Some{10} : Maybe<&2, U32>},
  +hab: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Norm.chars(D.slice(xs, a, Nat.sub(Nat.add(b, 1n), a))) == Norm.chars(D.slice(xs, a, Nat.sub(b, a))) ++ "\n" : String}:
  +k = Nat.sub(b, a)
  +ys = List.drop(&2, U32, xs, a)
  +hg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ys, k), List.get(&2, U32, xs, Nat.add(a, k)), Some{10}, PSh.get_drop(xs, a, k),
    AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{10} : Maybe<&2, U32>}, b, Nat.add(a, k), Equal.sym(Nat, Nat.add(a, k), b, N.le_sub_add(a, b, hab)), hlf))
  %Equal.sym(Nat, Nat.sub(Nat.add(b, 1n), a), Nat.add(k, 1n), U.sub_add_comm(b, 1n, a, hab)) : {Norm.chars(List.take(&2, U32, ys, _)) == Norm.chars(List.take(&2, U32, ys, k)) ++ "\n" : String}
  chars_snoc(ys, k, 10, hg)

# ---------------------------------------------------------------------------
# Cutting a field at its first tab
# ---------------------------------------------------------------------------

def fld(+xs: List<&2, U32>, +a: Nat, +b: Nat) -> String:
  Norm.chars(D.slice(xs, a, Nat.sub(b, a)))

def CT(+ys: List<&2, U32>, +r: Nat) -> J.Cut:
  J.Cut{Norm.chars(List.take(&2, U32, ys, r)), Norm.chars(List.drop(&2, U32, ys, Nat.add(r, 1n))), True{}}

def cut_tab(+x: U32, +t: List<&2, U32>, +hx: {U32.is_eq(x, 9) == True{} : Bool}) -> {J.cut(Norm.chars(Con{x, t})) == CT(Con{x, t}, 0n) : J.Cut}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, U32.is_eq(x, 9), True{}, hx) : {J.cut.go(SNil{}, _, Chr{x}) == CT(Con{x, Nil{}}, 0n) : J.Cut}
      {==}
    case Con{+y, +t2}:
      %Equal.sym(Bool, U32.is_eq(x, 9), True{}, hx) : {J.cut.go(Norm.chars(Con{y, t2}), _, Chr{x}) == CT(Con{x, Con{y, t2}}, 0n) : J.Cut}
      {==}

def cut_no(+x: U32, +y: U32, +t: List<&2, U32>, +r: Nat, +hx: {U32.is_eq(x, 9) == False{} : Bool},
  +ih: {J.cut(Norm.chars(Con{y, t})) == CT(Con{y, t}, r) : J.Cut}) -> {J.cut(Norm.chars(Con{x, Con{y, t}})) == CT(Con{x, Con{y, t}}, 1n+r) : J.Cut}:
  %Equal.sym(Bool, U32.is_eq(x, 9), False{}, hx) : {J.cut.go(Norm.chars(Con{y, t}), _, Chr{x}) == CT(Con{x, Con{y, t}}, 1n+r) : J.Cut}
  %Equal.sym(J.Cut, J.cut(Norm.chars(Con{y, t})), CT(Con{y, t}, r), ih) : {J.cut.k(Chr{x}, _) == CT(Con{x, Con{y, t}}, 1n+r) : J.Cut}
  {==}

def cut_rl.k(+x: U32, +b: Bool, +r: Nat, +t: List<&2, U32>, +hb: {U32.is_eq(x, 9) == b : Bool},
  +hr: {D.run_len(Con{x, t}, 9) == r : Nat}, +hh: {D.has(Con{x, t}, r, 9) == True{} : Bool},
  ih: @r2: Nat -> {D.run_len(t, 9) == r2 : Nat} -> {D.has(t, r2, 9) == True{} : Bool} -> {J.cut(Norm.chars(t)) == CT(t, r2) : J.Cut}) ->
  {J.cut(Norm.chars(Con{x, t})) == CT(Con{x, t}, r) : J.Cut}:
  match b r t:
    case True{} 0n _:
      cut_tab(x, t, hb)
    case True{} 1n+q _:
      +h0 = AB.subst(Bool, z => {Bool.pick(Nat, z, 0n, Nat.add(1n, D.run_len(t, 9))) == 1n+q : Nat}, U32.is_eq(x, 9), True{}, hb, hr)
      Empty.absurd({J.cut(Norm.chars(Con{x, t})) == CT(Con{x, t}, 1n+q) : J.Cut}, N.zero_ne_succ(q, h0))
    case False{} 0n _:
      +h0 = AB.subst(Bool, z => {Bool.pick(Nat, z, 0n, Nat.add(1n, D.run_len(t, 9))) == 0n : Nat}, U32.is_eq(x, 9), False{}, hb, hr)
      Empty.absurd({J.cut(Norm.chars(Con{x, t})) == CT(Con{x, t}, 0n) : J.Cut}, N.succ_ne_zero(D.run_len(t, 9), h0))
    case False{} 1n+q Nil{}:
      Empty.absurd({J.cut(Norm.chars(Con{x, Nil{}})) == CT(Con{x, Nil{}}, 1n+q) : J.Cut}, N.false_ne_true(hh))
    case False{} 1n+q Con{+y, +t2}:
      +h0 = AB.subst(Bool, z => {Bool.pick(Nat, z, 0n, Nat.add(1n, D.run_len(Con{y, t2}, 9))) == 1n+q : Nat}, U32.is_eq(x, 9), False{}, hb, hr)
      cut_no(x, y, t2, q, hb, ih(q, N.succ_inj(D.run_len(Con{y, t2}, 9), q, h0), hh))

# A list whose first tab is at r: its text cut at the tab.
def cut_rl(+ys: List<&2, U32>, +r: Nat, +hr: {D.run_len(ys, 9) == r : Nat}, +hh: {D.has(ys, r, 9) == True{} : Bool}) ->
  {J.cut(Norm.chars(ys)) == CT(ys, r) : J.Cut}:
  match ys:
    case Nil{}:
      Empty.absurd({J.cut(Norm.chars(Nil{})) == CT(Nil{}, r) : J.Cut}, N.false_ne_true(hh))
    case Con{+x, +t}:
      cut_rl.k(x, U32.is_eq(x, 9), r, t, {==}, hr, hh, r2 => h1 => h2 => cut_rl(t, r2, h1, h2))

def drop_take(+xs: List<&2, U32>, +m: Nat, +k: Nat) ->
  {List.drop(&2, U32, List.take(&2, U32, xs, m), k) == List.take(&2, U32, List.drop(&2, U32, xs, k), Nat.sub(m, k)) : List<&2, U32>}:
  match xs m k:
    case Nil{} _ _:
      {==}
    case Con{+x, +t} 0n 0n:
      {==}
    case Con{+x, +t} 0n 1n+j:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, t, j), 0n), Nil{}, PSq.take_zero(List.drop(&2, U32, t, j))) : {Nil{} == _ : List<&2, U32>}
      {==}
    case Con{+x, +t} 1n+i 0n:
      {==}
    case Con{+x, +t} 1n+i 1n+j:
      drop_take(t, i, j)

def drop_drop(+xs: List<&2, U32>, +a: Nat, +b: Nat) ->
  {List.drop(&2, U32, List.drop(&2, U32, xs, a), b) == List.drop(&2, U32, xs, Nat.add(a, b)) : List<&2, U32>}:
  match xs a:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n+i:
      drop_drop(t, i, b)

def sub_sub(+m: Nat, +a: Nat, +k: Nat) -> {Nat.sub(Nat.sub(m, a), k) == Nat.sub(m, Nat.add(a, k)) : Nat}:
  match m a:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      sub_sub(p, q, k)

def lt_sub(+a: Nat, +e: Nat, +b: Nat, +hae: {Nat.is_le(a, e) == True{} : Bool}, +heb: {Nat.is_lt(e, b) == True{} : Bool}) ->
  {Nat.is_lt(Nat.sub(e, a), Nat.sub(b, a)) == True{} : Bool}:
  match a e b:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(e, 0n), e, N.sub_zero(e)) : {Nat.is_lt(_, Nat.sub(b, 0n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(b, 0n), b, N.sub_zero(b)) : {Nat.is_lt(e, _) == True{} : Bool}
      heb
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+p), Nat.sub(b, 1n+p)) == True{} : Bool}, N.false_ne_true(hae))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(1n+q, 1n+p), Nat.sub(0n, 1n+p)) == True{} : Bool}, N.false_ne_true(heb))
    case 1n+p 1n+q 1n+c:
      lt_sub(p, q, c, hae, heb)

def ct_eq(+ys: List<&2, U32>, +r: Nat, +l1: List<&2, U32>, +l2: List<&2, U32>,
  +e1: {List.take(&2, U32, ys, r) == l1 : List<&2, U32>}, +e2: {List.drop(&2, U32, ys, Nat.add(r, 1n)) == l2 : List<&2, U32>}) ->
  {CT(ys, r) == J.Cut{Norm.chars(l1), Norm.chars(l2), True{}} : J.Cut}:
  %Equal.sym(List<&2, U32>, List.take(&2, U32, ys, r), l1, e1) : {J.Cut{Norm.chars(_), Norm.chars(List.drop(&2, U32, ys, Nat.add(r, 1n))), True{}} == J.Cut{Norm.chars(l1), Norm.chars(l2), True{}} : J.Cut}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, ys, Nat.add(r, 1n)), l2, e2) : {J.Cut{Norm.chars(l1), Norm.chars(_), True{}} == J.Cut{Norm.chars(l1), Norm.chars(l2), True{}} : J.Cut}
  {==}

# The text of a .. b-1 cut at its first tab, e.
def cut_fld(+xs: List<&2, U32>, +a: Nat, +e: Nat, +b: Nat, +hae: {Nat.is_le(a, e) == True{} : Bool}, +heb: {Nat.is_lt(e, b) == True{} : Bool},
  +hf: {D.first(xs, a, b, 9) == e : Nat}, +htab: {List.get(&2, U32, xs, e) == Some{9} : Maybe<&2, U32>}) ->
  {J.cut(fld(xs, a, b)) == J.Cut{fld(xs, a, e), fld(xs, Nat.add(e, 1n), b), True{}} : J.Cut}:
  +zs = List.drop(&2, U32, xs, a)
  +ys = List.take(&2, U32, zs, Nat.sub(b, a))
  +r = Nat.sub(e, a)
  +R = D.run_len(ys, 9)
  +hr = Equal.trans(Nat, R, Nat.sub(Nat.add(a, R), a), r, Equal.sym(Nat, Nat.sub(Nat.add(a, R), a), R, N.sub_add_l(a, R)),
    Equal.cong(Nat, Nat, z => Nat.sub(z, a), Nat.add(a, R), e, hf))
  +hrb = lt_sub(a, e, b, hae, heb)
  +hae2 = N.le_sub_add(a, e, hae)
  +hg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ys, r), List.get(&2, U32, zs, r), Some{9}, C.take_get(zs, Nat.sub(b, a), r, hrb),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, zs, r), List.get(&2, U32, xs, Nat.add(a, r)), Some{9}, PSh.get_drop(xs, a, r),
      AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{9} : Maybe<&2, U32>}, e, Nat.add(a, r), Equal.sym(Nat, Nat.add(a, r), e, hae2), htab)))
  +hh = AB.subst(Maybe<&2, U32>, m => {D.is_some(m, 9) == True{} : Bool}, Some{9}, List.get(&2, U32, ys, r), Equal.sym(Maybe<&2, U32>, List.get(&2, U32, ys, r), Some{9}, hg), {==})
  +e1 = PSq.take_take(zs, Nat.sub(b, a), r, N.lt_to_le(r, Nat.sub(b, a), hrb))
  +k = Nat.add(r, 1n)
  +hk = Equal.trans(Nat, Nat.add(a, k), Nat.add(Nat.add(a, r), 1n), Nat.add(e, 1n), Equal.sym(Nat, Nat.add(Nat.add(a, r), 1n), Nat.add(a, k), N.add_assoc(a, r, 1n)),
    Equal.cong(Nat, Nat, z => Nat.add(z, 1n), Nat.add(a, r), e, hae2))
  +e2a = Equal.trans(List<&2, U32>, List.drop(&2, U32, ys, k), List.take(&2, U32, List.drop(&2, U32, zs, k), Nat.sub(Nat.sub(b, a), k)),
    List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(a, k)), Nat.sub(b, Nat.add(a, k))), drop_take(zs, Nat.sub(b, a), k),
    %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.drop(&2, U32, xs, a), k), List.drop(&2, U32, xs, Nat.add(a, k)), drop_drop(xs, a, k)) : {List.take(&2, U32, _, Nat.sub(Nat.sub(b, a), k)) == List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(a, k)), Nat.sub(b, Nat.add(a, k))) : List<&2, U32>};
    %Equal.sym(Nat, Nat.sub(Nat.sub(b, a), k), Nat.sub(b, Nat.add(a, k)), sub_sub(b, a, k)) : {List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(a, k)), _) == List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(a, k)), Nat.sub(b, Nat.add(a, k))) : List<&2, U32>};
    {==})
  +e2 = AB.subst(Nat, z => {List.drop(&2, U32, ys, k) == List.take(&2, U32, List.drop(&2, U32, xs, z), Nat.sub(b, z)) : List<&2, U32>}, Nat.add(a, k), Nat.add(e, 1n), hk, e2a)
  Equal.trans(J.Cut, J.cut(Norm.chars(ys)), CT(ys, r), J.Cut{fld(xs, a, e), fld(xs, Nat.add(e, 1n), b), True{}}, cut_rl(ys, r, hr, hh),
    ct_eq(ys, r, List.take(&2, U32, zs, r), List.take(&2, U32, List.drop(&2, U32, xs, Nat.add(e, 1n)), Nat.sub(b, Nat.add(e, 1n))), e1, e2))

# ---------------------------------------------------------------------------
# The body of a line: a final CR is cut off
# ---------------------------------------------------------------------------

def some_eq(+x: U32, +y: U32, +h: {Some{x} == Some{y} : Maybe<&2, U32>}) -> {x == y : U32}:
  Equal.cong(Maybe<&2, U32>, U32, m => Maybe.default(&2, U32, m, 0), Some{x}, Some{y}, h)

def ecr_go3(+t: List<&2, U32>, +y: U32, +x: U32, +h: {List.get(&2, U32, Con{y, t}, List.length(&2, U32, t)) == Some{x} : Maybe<&2, U32>}) ->
  {Norm.ends_cr.go(Norm.chars(t), Chr{y}) == U32.is_eq(x, 13) : Bool}:
  match t:
    case Nil{}:
      %some_eq(y, x, h) : {U32.is_eq(y, 13) == U32.is_eq(_, 13) : Bool}
      {==}
    case Con{+z, +t2}:
      ecr_go3(t2, z, x, h)

def ecr_last(+ys: List<&2, U32>, +x: U32, +hy: {List.get(&2, U32, ys, Nat.sub(List.length(&2, U32, ys), 1n)) == Some{x} : Maybe<&2, U32>}) ->
  {Norm.ends_cr(Norm.chars(ys)) == U32.is_eq(x, 13) : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Norm.ends_cr(Norm.chars(Nil{})) == U32.is_eq(x, 13) : Bool}, PF.none_ne_some(x, hy))
    case Con{+y, +t}:
      ecr_go3(t, y, x, AB.subst(Nat, z => {List.get(&2, U32, Con{y, t}, z) == Some{x} : Maybe<&2, U32>}, Nat.sub(List.length(&2, U32, t), 0n), List.length(&2, U32, t), N.sub_zero(List.length(&2, U32, t)), hy))

def chars_len(+ys: List<&2, U32>) -> {String.length(Norm.chars(ys)) == List.length(&2, U32, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %chars_len(t) : {1n+String.length(Norm.chars(t)) == 1n+_ : Nat}
      {==}

def chars_take(+ys: List<&2, U32>, +m: Nat) -> {String.take(Norm.chars(ys), m) == Norm.chars(List.take(&2, U32, ys, m)) : String}:
  match ys m:
    case Nil{} _:
      {==}
    case Con{+y, +t} 0n:
      {==}
    case Con{+y, +t} 1n+k:
      %chars_take(t, k) : {SCon{Chr{y}, String.take(Norm.chars(t), k)} == SCon{Chr{y}, _} : String}
      {==}

def sub_mono(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      N.le_zero_l(Nat.sub(b, c))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, c), Nat.sub(0n, c)) == True{} : Bool}, N.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      sub_mono(p, q, r, h)

# The slice a .. b-1 has b - a bytes.
def slice_len(+xs: List<&2, U32>, +a: Nat, +b: Nat, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool}) ->
  {List.length(&2, U32, D.slice(xs, a, Nat.sub(b, a))) == Nat.sub(b, a) : Nat}:
  PSq.take_length(List.drop(&2, U32, xs, a), Nat.sub(b, a),
    AB.subst(Nat, z => {Nat.is_le(Nat.sub(b, a), z) == True{} : Bool}, Nat.sub(List.length(&2, U32, xs), a), List.length(&2, U32, List.drop(&2, U32, xs, a)),
      Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, xs, a)), Nat.sub(List.length(&2, U32, xs), a), PSh.drop_length(xs, a)),
      sub_mono(b, List.length(&2, U32, xs), a, hb)))

def lb_k(+c: Bool, +p: String) -> String:
  B.Line.body(B.Text.line.if(c, p))

def BDY(+xs: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, cr: Bool) -> String:
  match cr:
    case True{}:
      fld(xs, a, c)
    case False{}:
      fld(xs, a, b)

def body_k(+xs: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +cr: Bool,
  +ht: {String.take(fld(xs, a, b), Nat.sub(String.length(fld(xs, a, b)), 1n)) == fld(xs, a, c) : String}) ->
  {B.Line.body(B.Text.line.if(cr, fld(xs, a, b))) == BDY(xs, a, b, c, cr) : String}:
  match cr:
    case True{}:
      ht
    case False{}:
      {==}

# The line a .. b-1 whose last byte (at c = b - 1) is x: its body.
def body_eq(+xs: List<&2, U32>, +a: Nat, +b: Nat, +c: Nat, +x: U32, +hc: {Nat.add(c, 1n) == b : Nat},
  +hac: {Nat.is_le(a, c) == True{} : Bool}, +hb: {Nat.is_le(b, List.length(&2, U32, xs)) == True{} : Bool},
  +hx: {List.get(&2, U32, xs, c) == Some{x} : Maybe<&2, U32>}) ->
  {B.Line.body(Norm.line(fld(xs, a, b))) == BDY(xs, a, b, c, U32.is_eq(x, 13)) : String}:
  +zs = List.drop(&2, U32, xs, a)
  +k = Nat.sub(b, a)
  +ys = List.take(&2, U32, zs, k)
  +r = Nat.sub(c, a)
  +hk = Equal.trans(Nat, k, Nat.sub(Nat.add(c, 1n), a), Nat.add(r, 1n), Equal.cong(Nat, Nat, z => Nat.sub(z, a), b, Nat.add(c, 1n), Equal.sym(Nat, Nat.add(c, 1n), b, hc)),
    U.sub_add_comm(c, 1n, a, hac))
  +hk1 = Equal.trans(Nat, Nat.sub(k, 1n), Nat.sub(Nat.add(r, 1n), 1n), r, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), k, Nat.add(r, 1n), hk), N.sub_add(r, 1n))
  +hlen = Equal.trans(Nat, Nat.sub(String.length(Norm.chars(ys)), 1n), Nat.sub(k, 1n), r,
    Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), String.length(Norm.chars(ys)), k,
      Equal.trans(Nat, String.length(Norm.chars(ys)), List.length(&2, U32, ys), k, chars_len(ys), slice_len(xs, a, b, hb))), hk1)
  +hrk = AB.subst(Nat, z => {Nat.is_lt(r, z) == True{} : Bool}, Nat.add(r, 1n), k, Equal.sym(Nat, k, Nat.add(r, 1n), hk), PF.lt_add_succ(r, 0n))
  +hg = Equal.trans(Maybe<&2, U32>, List.get(&2, U32, ys, r), List.get(&2, U32, zs, r), Some{x}, C.take_get(zs, k, r, hrk),
    Equal.trans(Maybe<&2, U32>, List.get(&2, U32, zs, r), List.get(&2, U32, xs, Nat.add(a, r)), Some{x}, PSh.get_drop(xs, a, r),
      AB.subst(Nat, z => {List.get(&2, U32, xs, z) == Some{x} : Maybe<&2, U32>}, c, Nat.add(a, r), Equal.sym(Nat, Nat.add(a, r), c, N.le_sub_add(a, c, hac)), hx)))
  +hlenL = Equal.trans(Nat, Nat.sub(List.length(&2, U32, ys), 1n), Nat.sub(k, 1n), r, Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), List.length(&2, U32, ys), k, slice_len(xs, a, b, hb)), hk1)
  +hcr = ecr_last(ys, x, AB.subst(Nat, z => {List.get(&2, U32, ys, z) == Some{x} : Maybe<&2, U32>}, r, Nat.sub(List.length(&2, U32, ys), 1n), Equal.sym(Nat, Nat.sub(List.length(&2, U32, ys), 1n), r, hlenL), hg))
  +ht = Equal.trans(String, String.take(Norm.chars(ys), Nat.sub(String.length(Norm.chars(ys)), 1n)), String.take(Norm.chars(ys), r), fld(xs, a, c),
    Equal.cong(Nat, String, z => String.take(Norm.chars(ys), z), Nat.sub(String.length(Norm.chars(ys)), 1n), r, hlen),
    Equal.trans(String, String.take(Norm.chars(ys), r), Norm.chars(List.take(&2, U32, ys, r)), fld(xs, a, c), chars_take(ys, r),
      Equal.cong(List<&2, U32>, String, l => Norm.chars(l), List.take(&2, U32, ys, r), List.take(&2, U32, zs, r), PSq.take_take(zs, k, r, N.lt_to_le(r, k, hrk)))))
  %Equal.sym(Bool, Norm.ends_cr(Norm.chars(ys)), U32.is_eq(x, 13), hcr) : {B.Line.body(B.Text.line.if(_, fld(xs, a, b))) == BDY(xs, a, b, c, U32.is_eq(x, 13)) : String}
  body_k(xs, a, b, c, U32.is_eq(x, 13), ht)
