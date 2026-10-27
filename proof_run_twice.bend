import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_text.bend as X
import ./proof_run_line.bend as N
import ./proof_run_two.bend as W
import ./proof_run_gsort.bend as G
import ./proof_run_head.bend as H
import ./proof_run_sorted.bend as PS
import ./proof_run_grouped.bend as PG

# twice_run: run 1's body lines are its items' texts; run 2 reads them back
# as lines whose items have the same key, CHROM and text, grouped and sorted,
# so run 2 succeeds and writes the same body.

# The lines run 1 writes for its items.
def lns(ys: List<&2, R.Item>) -> List<&2, B.Line>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> t:
      N.ln(R.Item.text(y)) <> lns(t)

def q4(+fa: List<&2, B.Contig>, +o: B.Opts, +y: R.Item) -> Bool:
  +l2 = N.ln(R.Item.text(y))
  Bool.and(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), N.go_on(o, L.judge(fa, B.Line.body(l2))))

law qi_q4:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.Item
  for +h: {N.qi(fa, o, y) == True{} : Bool}
  {q4(fa, o, y) == True{} : Bool}

def qi_q4(fa, o, y, h):
  P.and_true_l(q4(fa, o, y), N.simb(L.item(fa, N.ln(R.Item.text(y)), 0n), y), h)

law qi_sim:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.Item
  for +h: {N.qi(fa, o, y) == True{} : Bool}
  {N.simb(L.item(fa, N.ln(R.Item.text(y)), 0n), y) == True{} : Bool}

def qi_sim(fa, o, y, h):
  P.and_true_r(q4(fa, o, y), N.simb(L.item(fa, N.ln(R.Item.text(y)), 0n), y), h)

law qi_good:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.Item
  for +h: {N.qi(fa, o, y) == True{} : Bool}
  {X.goodb(N.ln(R.Item.text(y))) == True{} : Bool}

def qi_good(fa, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  P.and_true_l(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)),
    P.and_true_l(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), N.go_on(o, L.judge(fa, B.Line.body(l2))), qi_q4(fa, o, y, h)))

law qi_text:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.Item
  for +h: {N.qi(fa, o, y) == True{} : Bool}
  {B.Line.text(N.ln(R.Item.text(y))) == R.Item.text(y) : String}

def qi_text(fa, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  Q.str_eq_sound(B.Line.text(l2), R.Item.text(y), P.and_true_r(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y)),
    P.and_true_l(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), N.go_on(o, L.judge(fa, B.Line.body(l2))), qi_q4(fa, o, y, h))))

law qi_go:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +y: R.Item
  for +h: {N.qi(fa, o, y) == True{} : Bool}
  {N.go_on(o, L.judge(fa, B.Line.body(N.ln(R.Item.text(y))))) == True{} : Bool}

def qi_go(fa, o, y, h):
  +l2 = N.ln(R.Item.text(y))
  P.and_true_r(Bool.and(X.goodb(l2), String.eq(B.Line.text(l2), R.Item.text(y))), N.go_on(o, L.judge(fa, B.Line.body(l2))), qi_q4(fa, o, y, h))

law lns_good:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {G.allq(fa, o, ys) == True{} : Bool}
  {X.all_good(lns(ys)) == True{} : Bool}

def lns_good(fa, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      S.and_intro(X.goodb(N.ln(R.Item.text(y))), X.all_good(lns(t)), qi_good(fa, o, y, P.and_true_l(N.qi(fa, o, y), G.allq(fa, o, t), h)),
        lns_good(fa, o, t, P.and_true_r(N.qi(fa, o, y), G.allq(fa, o, t), h)))

law lns_go:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {G.allq(fa, o, ys) == True{} : Bool}
  {W.all_go(fa, o, lns(ys)) == True{} : Bool}

def lns_go(fa, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      S.and_intro(N.go_on(o, L.judge(fa, B.Line.body(N.ln(R.Item.text(y))))), W.all_go(fa, o, lns(t)), qi_go(fa, o, y, P.and_true_l(N.qi(fa, o, y), G.allq(fa, o, t), h)),
        lns_go(fa, o, t, P.and_true_r(N.qi(fa, o, y), G.allq(fa, o, t), h)))

law lns_text:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +h: {G.allq(fa, o, ys) == True{} : Bool}
  {B.Lines.text(lns(ys)) == L.texts(ys) : String}

def lns_text(fa, o, ys, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(String, B.Line.text(N.ln(R.Item.text(y))), R.Item.text(y), qi_text(fa, o, y, P.and_true_l(N.qi(fa, o, y), G.allq(fa, o, t), h))) :
        {_ ++ B.Lines.text(lns(t)) == R.Item.text(y) ++ L.texts(t) : String}
      %Equal.sym(String, B.Lines.text(lns(t)), L.texts(t), lns_text(fa, o, t, P.and_true_r(N.qi(fa, o, y), G.allq(fa, o, t), h))) :
        {R.Item.text(y) ++ _ == R.Item.text(y) ++ L.texts(t) : String}
      {==}

# Same key, CHROM and text, item by item
# ======================================

def allsim(xs: List<&2, R.Item>, ys: List<&2, R.Item>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case x <> t y <> u:
      N.simb(x, y) && allsim(t, u)
    case _ _:
      False{}

law simb_key:
  for +a: R.Item
  for +b: R.Item
  for +h: {N.simb(a, b) == True{} : Bool}
  {R.Item.key(a) == R.Item.key(b) : Nat}

def simb_key(a, b, h):
  match a b:
    case R.Item{+k1, p1, B.At{n1, +c1, q1}, +t1} R.Item{+k2, p2, B.At{n2, +c2, q2}, +t2}:
      P.eq_sound(k1, k2, P.and_true_l(Nat.is_eq(k1, k2), String.eq(c1, c2), P.and_true_l(Bool.and(Nat.is_eq(k1, k2), String.eq(c1, c2)), String.eq(t1, t2), h)))

law simb_chrom:
  for +a: R.Item
  for +b: R.Item
  for +h: {N.simb(a, b) == True{} : Bool}
  {R.Item.chrom(a) == R.Item.chrom(b) : String}

def simb_chrom(a, b, h):
  match a b:
    case R.Item{+k1, p1, B.At{n1, +c1, q1}, +t1} R.Item{+k2, p2, B.At{n2, +c2, q2}, +t2}:
      Q.str_eq_sound(c1, c2, P.and_true_r(Nat.is_eq(k1, k2), String.eq(c1, c2), P.and_true_l(Bool.and(Nat.is_eq(k1, k2), String.eq(c1, c2)), String.eq(t1, t2), h)))

law simb_text:
  for +a: R.Item
  for +b: R.Item
  for +h: {N.simb(a, b) == True{} : Bool}
  {R.Item.text(a) == R.Item.text(b) : String}

def simb_text(a, b, h):
  match a b:
    case R.Item{+k1, p1, B.At{n1, +c1, q1}, +t1} R.Item{+k2, p2, B.At{n2, +c2, q2}, +t2}:
      Q.str_eq_sound(t1, t2, P.and_true_r(Bool.and(Nat.is_eq(k1, k2), String.eq(c1, c2)), String.eq(t1, t2), h))

def sn.go(r: B.Res, l2: B.Line, +f0: String, +f1: String, +p: Nat, +n: Nat, y: R.Item,
  h: {N.simb(L.item_of(r, l2, B.At{0n, f0, f1}, p), y) == True{} : Bool}) ->
  {N.simb(L.item_of(r, l2, B.At{n, f0, f1}, p), y) == True{} : Bool}:
  match r l2 y:
    case B.Res{B.Normalized{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Broken{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Skipped{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.NoContig{}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h
    case B.Res{B.Problem{c}, k, t, st} B.Line{b, tm} R.Item{ky, py, B.At{ny, cy, qy}, ty}:
      h

law nitems_sim:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ys: List<&2, R.Item>
  for +n: Nat
  for +h: {G.allq(fa, o, ys) == True{} : Bool}
  {allsim(T.nitems(lns(ys), fa, n), ys) == True{} : Bool}

def nitems_sim(fa, o, ys, n, h):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +l2 = N.ln(R.Item.text(y))
      +hy = P.and_true_l(N.qi(fa, o, y), G.allq(fa, o, t), h)
      +ht = P.and_true_r(N.qi(fa, o, y), G.allq(fa, o, t), h)
      +fs = B.Rec.fields(B.Line.body(l2))
      %Equal.sym(List<&2, R.Item>, T.nitems(l2 <> lns(t), fa, n), L.item(fa, l2, 1n+n) <> T.nitems(lns(t), fa, 1n+n), T.nitems_cons(l2, lns(t), fa, n)) :
        {allsim(_, y <> t) == True{} : Bool}
      S.and_intro(N.simb(L.item(fa, l2, 1n+n), y), allsim(T.nitems(lns(t), fa, 1n+n), t),
        sn.go(L.judge(fa, B.Line.body(l2)), l2, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n), B.Rec.pos(fs), 1n+n, y, qi_sim(fa, o, y, hy)),
        nitems_sim(fa, o, t, 1n+n, ht))

law texts_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {allsim(xs, ys) == True{} : Bool}
  {L.texts(xs) == L.texts(ys) : String}

def texts_sim(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case +x <> +t +y <> +u:
      +h1 = P.and_true_l(N.simb(x, y), allsim(t, u), h)
      +h2 = P.and_true_r(N.simb(x, y), allsim(t, u), h)
      %simb_text(x, y, h1) : {R.Item.text(x) ++ L.texts(t) == _ ++ L.texts(u) : String}
      %texts_sim(t, u, h2) : {R.Item.text(x) ++ L.texts(t) == R.Item.text(x) ++ _ : String}
      {==}
    case Nil{} y <> u:
      Empty.absurd({L.texts(Nil{}) == L.texts(y <> u) : String}, P.false_ne_true(h))
    case x <> t Nil{}:
      Empty.absurd({L.texts(x <> t) == L.texts(Nil{}) : String}, P.false_ne_true(h))

law mc_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {allsim(xs, ys) == True{} : Bool}
  {G.mc(xs) == G.mc(ys) : List<&2, String>}

def mc_sim(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case +x <> +t +y <> +u:
      +h1 = P.and_true_l(N.simb(x, y), allsim(t, u), h)
      +h2 = P.and_true_r(N.simb(x, y), allsim(t, u), h)
      %simb_chrom(x, y, h1) : {R.Item.chrom(x) <> G.mc(t) == _ <> G.mc(u) : List<&2, String>}
      %mc_sim(t, u, h2) : {R.Item.chrom(x) <> G.mc(t) == R.Item.chrom(x) <> _ : List<&2, String>}
      {==}
    case Nil{} y <> u:
      Empty.absurd({G.mc(Nil{}) == G.mc(y <> u) : List<&2, String>}, P.false_ne_true(h))
    case x <> t Nil{}:
      Empty.absurd({G.mc(x <> t) == G.mc(Nil{}) : List<&2, String>}, P.false_ne_true(h))

law grouped_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {allsim(xs, ys) == True{} : Bool}
  for +hg: {L.grouped(ys) == True{} : Bool}
  {L.grouped(xs) == True{} : Bool}

def grouped_sim(xs, ys, h, hg):
  %Equal.sym(Bool, L.grouped(xs), G.grp(G.mc(xs)), G.grouped_mc(xs)) : {_ == True{} : Bool}
  %Equal.sym(List<&2, String>, G.mc(xs), G.mc(ys), mc_sim(xs, ys, h)) : {G.grp(_) == True{} : Bool}
  %G.grouped_mc(ys) : {_ == True{} : Bool}
  hg

def simm(mp: Maybe<&2, R.Item>, mq: Maybe<&2, R.Item>) -> Bool:
  match mp mq:
    case None{} None{}:
      True{}
    case Some{a} Some{b}:
      N.simb(a, b)
    case _ _:
      False{}

def am_sim.cond(+a: R.Item, +b: R.Item, +x: R.Item, +y: R.Item, +ha: {N.simb(a, b) == True{} : Bool}, +hx: {N.simb(x, y) == True{} : Bool}) ->
  {Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))) ==
    Bool.or(Bool.not(String.eq(R.Item.chrom(b), R.Item.chrom(y))), Nat.is_le(R.Item.key(b), R.Item.key(y))) : Bool}:
  %simb_chrom(a, b, ha) : {Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))) ==
    Bool.or(Bool.not(String.eq(_, R.Item.chrom(y))), Nat.is_le(R.Item.key(b), R.Item.key(y))) : Bool}
  %simb_chrom(x, y, hx) : {Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))) ==
    Bool.or(Bool.not(String.eq(R.Item.chrom(a), _)), Nat.is_le(R.Item.key(b), R.Item.key(y))) : Bool}
  %simb_key(a, b, ha) : {Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))) ==
    Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(_, R.Item.key(y))) : Bool}
  %simb_key(x, y, hx) : {Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))) ==
    Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), _)) : Bool}
  {==}

law am_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +mp: Maybe<&2, R.Item>
  for +mq: Maybe<&2, R.Item>
  for +h: {allsim(xs, ys) == True{} : Bool}
  for +hm: {simm(mp, mq) == True{} : Bool}
  {G.asck_m(xs, mp) == G.asck_m(ys, mq) : Bool}

def am_sim(xs, ys, mp, mq, h, hm):
  match xs ys mp mq:
    case Nil{} Nil{} _ _:
      {==}
    case +x <> +t +y <> +u None{} None{}:
      am_sim(t, u, Some{x}, Some{y}, P.and_true_r(N.simb(x, y), allsim(t, u), h), P.and_true_l(N.simb(x, y), allsim(t, u), h))
    case +x <> +t +y <> +u Some{+a} Some{+b}:
      +hx = P.and_true_l(N.simb(x, y), allsim(t, u), h)
      %am_sim.cond(a, b, x, y, hm, hx) : {Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))), G.asck_m(t, Some{x})) ==
        Bool.and(_, G.asck_m(u, Some{y})) : Bool}
      %am_sim(t, u, Some{x}, Some{y}, P.and_true_r(N.simb(x, y), allsim(t, u), h), hx) :
        {Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))), G.asck_m(t, Some{x})) ==
          Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))), _) : Bool}
      {==}
    case +x <> +t +y <> +u None{} Some{b}:
      Empty.absurd({G.asck_m(x <> t, None{}) == G.asck_m(y <> u, Some{b}) : Bool}, P.false_ne_true(hm))
    case +x <> +t +y <> +u Some{a} None{}:
      Empty.absurd({G.asck_m(x <> t, Some{a}) == G.asck_m(y <> u, None{}) : Bool}, P.false_ne_true(hm))
    case Nil{} y <> u _ _:
      Empty.absurd({G.asck_m(Nil{}, mp) == G.asck_m(y <> u, mq) : Bool}, P.false_ne_true(h))
    case x <> t Nil{} _ _:
      Empty.absurd({G.asck_m(x <> t, mp) == G.asck_m(Nil{}, mq) : Bool}, P.false_ne_true(h))

law asck_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {allsim(xs, ys) == True{} : Bool}
  for +hk: {W.asck(ys) == True{} : Bool}
  {W.asck(xs) == True{} : Bool}

def asck_sim(xs, ys, h, hk):
  %Equal.sym(Bool, W.asck(xs), G.asck_m(xs, None{}), G.asck_eq(xs)) : {_ == True{} : Bool}
  %Equal.sym(Bool, G.asck_m(xs, None{}), G.asck_m(ys, None{}), am_sim(xs, ys, None{}, None{}, h, {==})) : {_ == True{} : Bool}
  %G.asck_eq(ys) : {_ == True{} : Bool}
  hk

law allq_lines:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +hg: {X.all_good(ls) == True{} : Bool}
  for +hgo: {W.all_go(fa, o, ls) == True{} : Bool}
  {G.allq(fa, o, T.nitems(ls, fa, n)) == True{} : Bool}

def allq_lines(ls, fa, o, n, hg, hgo):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      %Equal.sym(List<&2, R.Item>, T.nitems(l <> t, fa, n), L.item(fa, l, 1n+n) <> T.nitems(t, fa, 1n+n), T.nitems_cons(l, t, fa, n)) :
        {G.allq(fa, o, _) == True{} : Bool}
      S.and_intro(N.qi(fa, o, L.item(fa, l, 1n+n)), G.allq(fa, o, T.nitems(t, fa, 1n+n)),
        N.line_qi(fa, o, l, 1n+n, P.and_true_l(X.goodb(l), X.all_good(t), hg), P.and_true_l(N.go_on(o, L.judge(fa, B.Line.body(l))), W.all_go(fa, o, t), hgo)),
        allq_lines(t, fa, o, 1n+n, P.and_true_r(X.goodb(l), X.all_good(t), hg), P.and_true_r(N.go_on(o, L.judge(fa, B.Line.body(l))), W.all_go(fa, o, t), hgo)))

law all_nc_app:
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  for +h1: {H.all_nc(xs) == True{} : Bool}
  for +h2: {H.all_nc(ys) == True{} : Bool}
  {H.all_nc(X.lapp(xs, ys)) == True{} : Bool}

def all_nc_app(xs, ys, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      S.and_intro(Bool.not(H.isc(x)), H.all_nc(X.lapp(t, ys)), (%Equal.sym(Bool, H.isc(x), False{}, H.nc_head(x, t, h1)) : {Bool.not(_) == True{} : Bool}; {==}), all_nc_app(t, ys, H.nc_tail(x, t, h1), h2))

def P2(+ls: List<&2, B.Line>, +o: B.Opts) -> List<&2, B.Line>:
  X.lapp(H.pre_c(ls), [H.al1(B.Line.term(H.cl_c(ls))), H.al2(o, B.Line.term(H.cl_c(ls)))])

law p2_nc:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  {H.all_nc(P2(ls, o)) == True{} : Bool}

def p2_nc(ls, o):
  +tm = B.Line.term(H.cl_c(ls))
  all_nc_app(H.pre_c(ls), [H.al1(tm), H.al2(o, tm)], H.pre_nc(ls),
    (%Equal.sym(Bool, H.isc(H.al1(tm)), False{}, H.isc_al1(tm)) : {Bool.and(Bool.not(_), Bool.and(Bool.not(H.isc(H.al2(o, tm))), True{})) == True{} : Bool};
     %Equal.sym(Bool, H.isc(H.al2(o, tm)), False{}, H.isc_al2(o, tm)) : {Bool.and(True{}, Bool.and(Bool.not(_), True{})) == True{} : Bool}; {==}))

# The header lines then ts, as lines: P2, the #CHROM line, ts.
law hl_split:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  for +ts: List<&2, B.Line>
  {X.lapp(H.Hl(ls, o), ts) == X.lapp(P2(ls, o), H.cl_c(ls) <> ts) : List<&2, B.Line>}

def hl_split(ls, o, ts):
  +pre = H.pre_c(ls)
  +cl = H.cl_c(ls)
  +tm = B.Line.term(cl)
  %Equal.sym(List<&2, B.Line>, X.lapp(X.lapp(pre, [H.al1(tm), H.al2(o, tm), cl]), ts), X.lapp(pre, X.lapp([H.al1(tm), H.al2(o, tm), cl], ts)),
    P.append_assoc(B.Line, pre, [H.al1(tm), H.al2(o, tm), cl], ts)) : {_ == X.lapp(P2(ls, o), cl <> ts) : List<&2, B.Line>}
  Equal.sym(List<&2, B.Line>, X.lapp(X.lapp(pre, [H.al1(tm), H.al2(o, tm)]), cl <> ts), X.lapp(pre, H.al1(tm) <> H.al2(o, tm) <> cl <> ts),
    P.append_assoc(B.Line, pre, [H.al1(tm), H.al2(o, tm)], cl <> ts))

# body() of a header then good lines ts is the text of ts.
law body_hd:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  for +ts: List<&2, B.Line>
  for +hg: {X.all_good(ls) == True{} : Bool}
  for +hc: {H.has_c(ls) == True{} : Bool}
  for +ht: {X.all_good(ts) == True{} : Bool}
  {L.body(B.Lines.text(H.Hl(ls, o)) ++ B.Lines.text(ts)) == B.Lines.text(ts) : String}

def body_hd(ls, o, ts, hg, hc, ht):
  +hl = H.Hl(ls, o)
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(hl) ++ B.Lines.text(ts)), X.lapp(hl, B.Text.lines(B.Lines.text(ts))),
    X.lines_text_app(hl, B.Lines.text(ts), H.hl_good(ls, o, hg, hc))) : {L.body.go(_, False{}, "") == B.Lines.text(ts) : String}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(ts)), ts, X.lines_text(ts, ht)) : {L.body.go(X.lapp(hl, _), False{}, "") == B.Lines.text(ts) : String}
  %Equal.sym(List<&2, B.Line>, X.lapp(hl, ts), X.lapp(P2(ls, o), H.cl_c(ls) <> ts), hl_split(ls, o, ts)) : {L.body.go(_, False{}, "") == B.Lines.text(ts) : String}
  H.bgo1(P2(ls, o), H.cl_c(ls), ts, "", p2_nc(ls, o), H.cl_isc(ls, hc))

# Assembly
# ========

def FA(+fasta: String) -> List<&2, B.Contig>:
  B.Fasta.parse(fasta)

def LS1(+vcf: String) -> List<&2, B.Line>:
  B.Text.lines(vcf)

def K0() -> R.Cnt:
  R.Cnt{0n, 0n, 0n, 0n}

def YS(+fasta: String, +vcf: String) -> List<&2, R.Item>:
  L.gsort(L.items(fasta, vcf))

def TL(+fasta: String, +vcf: String) -> List<&2, B.Line>:
  lns(YS(fasta, vcf))

def O1(+fasta: String, +vcf: String, +o: B.Opts) -> String:
  R.Report.out(L.run(fasta, vcf, o))

def HC(+fasta: String, +vcf: String, +o: B.Opts) -> Type:
  {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}

law r1_has:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {H.has_c(LS1(vcf)) == True{} : Bool}

def r1_has(fasta, vcf, o, h):
  H.hdr_has(LS1(vcf), FA(fasta), o, 0n, "", K0(), "", Nil{}, h)

law r1_go:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {W.all_go(FA(fasta), o, H.post_c(LS1(vcf))) == True{} : Bool}

def r1_go(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +er = H.hdr_run(ls, fa, o, 0n, "", K0(), "", Nil{}, r1_has(fasta, vcf, o, h))
  +h2 = {(%er : {R.Report.code(R.finish(_)) == 0n : Nat}; h) :
    {R.Report.code(R.finish(L.run.go(H.post_c(ls), fa, o, H.bst(H.idx_c(ls, 0n), K0(), L.head.go(ls, o, False{}, ""), Nil{})))) == 0n : Nat}}
  H.body_go(H.post_c(ls), fa, o, H.idx_c(ls, 0n), "", None{}, Nil{}, None{}, Nil{}, K0(), L.head.go(ls, o, False{}, ""), Nil{}, h2)

law post_good:
  for +ls: List<&2, B.Line>
  for +hg: {X.all_good(ls) == True{} : Bool}
  for +hc: {H.has_c(ls) == True{} : Bool}
  {X.all_good(H.post_c(ls)) == True{} : Bool}

def post_good(ls, hg, hc):
  +ps = H.pre_c(ls)
  +cl = H.cl_c(ls)
  +rs = H.post_c(ls)
  P.and_true_r(X.goodb(cl), X.all_good(rs),
    H.all_good_r(ps, cl <> rs, (%H.hs_split(ls, hc) : {X.all_good(_) == True{} : Bool}; hg)))

law r1_allq:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {G.allq(FA(fasta), o, L.items(fasta, vcf)) == True{} : Bool}

def r1_allq(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +hc = r1_has(fasta, vcf, o, h)
  %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, 0n, Nil{}})), T.nitems(H.post_c(ls), fa, H.idx_c(ls, 0n)), H.hdr_items(ls, fa, 0n, hc)) :
    {G.allq(fa, o, _) == True{} : Bool}
  allq_lines(H.post_c(ls), fa, o, H.idx_c(ls, 0n), post_good(ls, X.lines_good(vcf), hc), r1_go(fasta, vcf, o, h))

law ys_allq:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {G.allq(FA(fasta), o, YS(fasta, vcf)) == True{} : Bool}

def ys_allq(fasta, vcf, o, h):
  G.allq_gs(FA(fasta), o, L.items(fasta, vcf), Nil{}, Nil{}, r1_allq(fasta, vcf, o, h), {==}, {==})

law r1_out:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {O1(fasta, vcf, o) == B.Lines.text(H.Hl(LS1(vcf), o)) ++ B.Lines.text(TL(fasta, vcf)) : String}

def r1_out(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +hc = r1_has(fasta, vcf, o, h)
  +ys = YS(fasta, vcf)
  %Equal.sym(String, B.Lines.text(lns(ys)), L.texts(ys), lns_text(fa, o, ys, ys_allq(fasta, vcf, o, h))) :
    {O1(fasta, vcf, o) == B.Lines.text(H.Hl(ls, o)) ++ _ : String}
  %H.hdr_head(ls, o, "", hc) : {O1(fasta, vcf, o) == _ ++ L.texts(ys) : String}
  PS.sorted_head(ls, fa, o, 0n, "", K0(), "", Nil{}, h)

law r1_body:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.body(O1(fasta, vcf, o)) == B.Lines.text(TL(fasta, vcf)) : String}

def r1_body(fasta, vcf, o, h):
  %Equal.sym(String, O1(fasta, vcf, o), B.Lines.text(H.Hl(LS1(vcf), o)) ++ B.Lines.text(TL(fasta, vcf)), r1_out(fasta, vcf, o, h)) :
    {L.body(_) == B.Lines.text(TL(fasta, vcf)) : String}
  body_hd(LS1(vcf), o, TL(fasta, vcf), X.lines_good(vcf), r1_has(fasta, vcf, o, h), lns_good(FA(fasta), o, YS(fasta, vcf), ys_allq(fasta, vcf, o, h)))

def LS2(+fasta: String, +vcf: String, +o: B.Opts) -> List<&2, B.Line>:
  X.lapp(P2(LS1(vcf), o), H.cl_c(LS1(vcf)) <> TL(fasta, vcf))

law r2_lines:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {B.Text.lines(O1(fasta, vcf, o)) == LS2(fasta, vcf, o) : List<&2, B.Line>}

def r2_lines(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +hl = H.Hl(ls, o)
  +tl = TL(fasta, vcf)
  +hc = r1_has(fasta, vcf, o, h)
  %Equal.sym(String, O1(fasta, vcf, o), B.Lines.text(hl) ++ B.Lines.text(tl), r1_out(fasta, vcf, o, h)) : {B.Text.lines(_) == LS2(fasta, vcf, o) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(hl) ++ B.Lines.text(tl)), X.lapp(hl, B.Text.lines(B.Lines.text(tl))),
    X.lines_text_app(hl, B.Lines.text(tl), H.hl_good(ls, o, X.lines_good(vcf), hc))) : {_ == LS2(fasta, vcf, o) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(tl)), tl, X.lines_text(tl, lns_good(FA(fasta), o, YS(fasta, vcf), ys_allq(fasta, vcf, o, h)))) :
    {X.lapp(hl, _) == LS2(fasta, vcf, o) : List<&2, B.Line>}
  hl_split(ls, o, tl)

law r2_has:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {H.has_c(LS2(fasta, vcf, o)) == True{} : Bool}

def r2_has(fasta, vcf, o, h):
  H.dec_has(P2(LS1(vcf), o), H.cl_c(LS1(vcf)), TL(fasta, vcf), p2_nc(LS1(vcf), o), H.cl_isc(LS1(vcf), r1_has(fasta, vcf, o, h)))

def BS2(+fasta: String, +vcf: String, +o: B.Opts) -> R.RunSt:
  +ls2 = LS2(fasta, vcf, o)
  H.bst(H.idx_c(ls2, 0n), K0(), L.head.go(ls2, o, False{}, ""), Nil{})

law r2_run:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.run(fasta, O1(fasta, vcf, o), o) == R.finish(L.run.go(TL(fasta, vcf), FA(fasta), o, BS2(fasta, vcf, o))) : R.Report}

def r2_run(fasta, vcf, o, h):
  +ls2 = LS2(fasta, vcf, o)
  +fa = FA(fasta)
  +h2 = r2_has(fasta, vcf, o, h)
  %Equal.sym(List<&2, B.Line>, B.Text.lines(O1(fasta, vcf, o)), ls2, r2_lines(fasta, vcf, o, h)) :
    {R.finish(L.run.go(_, fa, o, R.start_st())) == R.finish(L.run.go(TL(fasta, vcf), fa, o, BS2(fasta, vcf, o))) : R.Report}
  %Equal.sym(R.RunSt, L.run.go(ls2, fa, o, H.hst(0n, "", K0(), "", Nil{})), L.run.go(H.post_c(ls2), fa, o, BS2(fasta, vcf, o)),
    H.hdr_run(ls2, fa, o, 0n, "", K0(), "", Nil{}, h2)) :
    {R.finish(_) == R.finish(L.run.go(TL(fasta, vcf), fa, o, BS2(fasta, vcf, o))) : R.Report}
  %Equal.sym(List<&2, B.Line>, H.post_c(ls2), TL(fasta, vcf),
    H.dec_post(P2(LS1(vcf), o), H.cl_c(LS1(vcf)), TL(fasta, vcf), p2_nc(LS1(vcf), o), H.cl_isc(LS1(vcf), r1_has(fasta, vcf, o, h)))) :
    {R.finish(L.run.go(_, fa, o, BS2(fasta, vcf, o))) == R.finish(L.run.go(TL(fasta, vcf), fa, o, BS2(fasta, vcf, o))) : R.Report}
  {==}

law r2_cm:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  W.CM(FA(fasta), o, TL(fasta, vcf), L.head.go(LS2(fasta, vcf, o), o, False{}, "") ++ L.texts(T.nitems(TL(fasta, vcf), FA(fasta), H.idx_c(LS2(fasta, vcf, o), 0n))), BS2(fasta, vcf, o))

def r2_cm(fasta, vcf, o, h):
  +fa = FA(fasta)
  +ys = YS(fasta, vcf)
  +tl = TL(fasta, vcf)
  +ls2 = LS2(fasta, vcf, o)
  +n2 = H.idx_c(ls2, 0n)
  +hq = ys_allq(fasta, vcf, o, h)
  +sim = nitems_sim(fa, o, ys, n2, hq)
  +hgr = G.grouped_gs(L.items(fasta, vcf), PG.grouped_head(LS1(vcf), fa, o, 0n, "", K0(), "", Nil{}, h))
  W.two_first(tl, fa, o, n2, "", K0(), L.head.go(ls2, o, False{}, ""), Nil{},
    grouped_sim(T.nitems(tl, fa, n2), ys, sim, hgr), asck_sim(T.nitems(tl, fa, n2), ys, sim, G.asck_gs(L.items(fasta, vcf))), lns_go(fa, o, ys, hq))

def twice.fin(+fasta: String, +vcf: String, +o: B.Opts, +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat},
  cm: W.CM(FA(fasta), o, TL(fasta, vcf), L.head.go(LS2(fasta, vcf, o), o, False{}, "") ++ L.texts(T.nitems(TL(fasta, vcf), FA(fasta), H.idx_c(LS2(fasta, vcf, o), 0n))), BS2(fasta, vcf, o))) ->
  {(Nat.is_eq(R.Report.code(L.run(fasta, O1(fasta, vcf, o), o)), 0n)
    && String.eq(L.body(R.Report.out(L.run(fasta, O1(fasta, vcf, o), o))), L.body(O1(fasta, vcf, o)))) == True{} : Bool}:
  match cm:
    case (+c2, +e2):
      +fa = FA(fasta)
      +ys = YS(fasta, vcf)
      +tl = TL(fasta, vcf)
      +ls2 = LS2(fasta, vcf, o)
      +n2 = H.idx_c(ls2, 0n)
      +hd2 = L.head.go(ls2, o, False{}, "")
      +run2 = L.run(fasta, O1(fasta, vcf, o), o)
      +fin2 = R.finish(L.run.go(tl, fa, o, BS2(fasta, vcf, o)))
      +er = r2_run(fasta, vcf, o, h)
      +hq = ys_allq(fasta, vcf, o, h)
      +h2 = r2_has(fasta, vcf, o, h)
      +ec = Equal.trans(Nat, R.Report.code(run2), R.Report.code(fin2), 0n, Equal.cong(R.Report, Nat, z => R.Report.code(z), run2, fin2, er), c2)
      +eo = {Equal.trans(String, R.Report.out(run2), R.Report.out(fin2), hd2 ++ L.texts(T.nitems(tl, fa, n2)),
          Equal.cong(R.Report, String, z => R.Report.out(z), run2, fin2, er), e2) :
        {R.Report.out(run2) == hd2 ++ L.texts(T.nitems(tl, fa, n2)) : String}}
      +eo2 = {(%H.hdr_head(ls2, o, "", h2) : {R.Report.out(run2) == _ ++ B.Lines.text(tl) : String};
          %Equal.sym(String, B.Lines.text(lns(ys)), L.texts(ys), lns_text(fa, o, ys, hq)) : {R.Report.out(run2) == hd2 ++ _ : String};
          %texts_sim(T.nitems(tl, fa, n2), ys, nitems_sim(fa, o, ys, n2, hq)) : {R.Report.out(run2) == hd2 ++ _ : String};
          eo) : {R.Report.out(run2) == B.Lines.text(H.Hl(ls2, o)) ++ B.Lines.text(tl) : String}}
      +hg2 = {(%r2_lines(fasta, vcf, o, h) : {X.all_good(_) == True{} : Bool}; X.lines_good(O1(fasta, vcf, o))) : {X.all_good(ls2) == True{} : Bool}}
      +eb2 = {(%Equal.sym(String, R.Report.out(run2), B.Lines.text(H.Hl(ls2, o)) ++ B.Lines.text(tl), eo2) : {L.body(_) == B.Lines.text(tl) : String};
          body_hd(ls2, o, tl, hg2, h2, lns_good(fa, o, ys, hq))) : {L.body(R.Report.out(run2)) == B.Lines.text(tl) : String}}
      +eb1 = r1_body(fasta, vcf, o, h)
      %Equal.sym(Nat, R.Report.code(run2), 0n, ec) :
        {Bool.and(Nat.is_eq(_, 0n), String.eq(L.body(R.Report.out(run2)), L.body(O1(fasta, vcf, o)))) == True{} : Bool}
      %Equal.sym(String, L.body(R.Report.out(run2)), B.Lines.text(tl), eb2) :
        {Bool.and(Nat.is_eq(0n, 0n), String.eq(_, L.body(O1(fasta, vcf, o)))) == True{} : Bool}
      %Equal.sym(String, L.body(O1(fasta, vcf, o)), B.Lines.text(tl), eb1) :
        {Bool.and(Nat.is_eq(0n, 0n), String.eq(B.Lines.text(tl), _)) == True{} : Bool}
      Q.str_eq_refl(B.Lines.text(tl))

# Running the tool on its own output succeeds and gives the same body lines.
law twice_main:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {(Nat.is_eq(R.Report.code(L.run(fasta, R.Report.out(L.run(fasta, vcf, o)), o)), 0n)
    && String.eq(L.body(R.Report.out(L.run(fasta, R.Report.out(L.run(fasta, vcf, o)), o))), L.body(R.Report.out(L.run(fasta, vcf, o))))) == True{} : Bool}

def twice_main(fasta, vcf, o, h):
  twice.fin(fasta, vcf, o, h, r2_cm(fasta, vcf, o, h))
