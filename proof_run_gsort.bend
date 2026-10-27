import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_line.bend as N
import ./proof_run_two.bend as W
import ./proof_run_text.bend as X2

# The spec's sort L.gsort for twice_run: it keeps every item (qi holds after),
# keeps the CHROM sequence (so grouped), and sorts keys within each CHROM run.

def iapp(xs: List<&2, R.Item>, ys: List<&2, R.Item>) -> List<&2, R.Item>:
  List.append(&2, R.Item, xs, ys)

def allq(+fa: List<&2, B.Contig>, +o: B.Opts, xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      N.qi(fa, o, x) && allq(fa, o, t)

law allq_app:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h1: {allq(fa, o, xs) == True{} : Bool}
  for +h2: {allq(fa, o, ys) == True{} : Bool}
  {allq(fa, o, iapp(xs, ys)) == True{} : Bool}

def allq_app(fa, o, xs, ys, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      S.and_intro(N.qi(fa, o, x), allq(fa, o, iapp(t, ys)), P.and_true_l(N.qi(fa, o, x), allq(fa, o, t), h1),
        allq_app(fa, o, t, ys, P.and_true_r(N.qi(fa, o, x), allq(fa, o, t), h1), h2))

def allq_ins.go(+fa: List<&2, B.Contig>, +o: B.Opts, +x: R.Item, +y: R.Item, +t: List<&2, R.Item>, b: Bool,
  +hx: {N.qi(fa, o, x) == True{} : Bool}, +hy: {N.qi(fa, o, y) == True{} : Bool}, +ht: {allq(fa, o, t) == True{} : Bool},
  ih: {allq(fa, o, L.ins_first(x, t)) == True{} : Bool}) ->
  {allq(fa, o, L.ins_first.put(b, x, y, t, L.ins_first(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      S.and_intro(N.qi(fa, o, x), allq(fa, o, y <> t), hx, S.and_intro(N.qi(fa, o, y), allq(fa, o, t), hy, ht))
    case False{}:
      S.and_intro(N.qi(fa, o, y), allq(fa, o, L.ins_first(x, t)), hy, ih)

law allq_ins:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +x: R.Item
  for +ys: List<&2, R.Item>
  for +hx: {N.qi(fa, o, x) == True{} : Bool}
  for +hy: {allq(fa, o, ys) == True{} : Bool}
  {allq(fa, o, L.ins_first(x, ys)) == True{} : Bool}

def allq_ins(fa, o, x, ys, hx, hy):
  match ys:
    case Nil{}:
      S.and_intro(N.qi(fa, o, x), True{}, hx, {==})
    case +y <> +t:
      +h1 = P.and_true_l(N.qi(fa, o, y), allq(fa, o, t), hy)
      +h2 = P.and_true_r(N.qi(fa, o, y), allq(fa, o, t), hy)
      allq_ins.go(fa, o, x, y, t, Nat.is_le(R.Item.key(x), R.Item.key(y)), hx, h1, h2, allq_ins(fa, o, x, t, hx, h2))

law allq_isort:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +h: {allq(fa, o, xs) == True{} : Bool}
  {allq(fa, o, L.isort(xs)) == True{} : Bool}

def allq_isort(fa, o, xs, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      allq_ins(fa, o, x, L.isort(t), P.and_true_l(N.qi(fa, o, x), allq(fa, o, t), h),
        allq_isort(fa, o, t, P.and_true_r(N.qi(fa, o, x), allq(fa, o, t), h)))

def allq_gs.go(+fa: List<&2, B.Contig>, +o: B.Opts, +x: R.Item, +t: List<&2, R.Item>, +run: List<&2, R.Item>, +done: List<&2, R.Item>, b: Bool,
  +hx: {N.qi(fa, o, x) == True{} : Bool}, +hr: {allq(fa, o, run) == True{} : Bool}, +hd: {allq(fa, o, done) == True{} : Bool},
  ih: @r2: List<&2, R.Item> -> @d2: List<&2, R.Item> -> {allq(fa, o, r2) == True{} : Bool} -> {allq(fa, o, d2) == True{} : Bool} ->
    {allq(fa, o, L.gsort.go(t, r2, d2)) == True{} : Bool}) ->
  {allq(fa, o, L.gsort.go(t, Bool.pick(List<&2, R.Item>, b, iapp(run, [x]), [x]), Bool.pick(List<&2, R.Item>, b, done, iapp(done, L.isort(run))))) == True{} : Bool}:
  match b:
    case True{}:
      ih(iapp(run, [x]), done, allq_app(fa, o, run, [x], hr, S.and_intro(N.qi(fa, o, x), True{}, hx, {==})), hd)
    case False{}:
      ih([x], iapp(done, L.isort(run)), S.and_intro(N.qi(fa, o, x), True{}, hx, {==}), allq_app(fa, o, done, L.isort(run), hd, allq_isort(fa, o, run, hr)))

law allq_gs:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +xs: List<&2, R.Item>
  for +run: List<&2, R.Item>
  for +done: List<&2, R.Item>
  for +hx: {allq(fa, o, xs) == True{} : Bool}
  for +hr: {allq(fa, o, run) == True{} : Bool}
  for +hd: {allq(fa, o, done) == True{} : Bool}
  {allq(fa, o, L.gsort.go(xs, run, done)) == True{} : Bool}

def allq_gs(fa, o, xs, run, done, hx, hr, hd):
  match xs:
    case Nil{}:
      allq_app(fa, o, done, L.isort(run), hd, allq_isort(fa, o, run, hr))
    case +x <> +t:
      allq_gs.go(fa, o, x, t, run, done, L.same_chrom(run, R.Item.chrom(x)), P.and_true_l(N.qi(fa, o, x), allq(fa, o, t), hx), hr, hd,
        r2 => d2 => h2 => h3 => allq_gs(fa, o, t, r2, d2, P.and_true_r(N.qi(fa, o, x), allq(fa, o, t), hx), h2, h3))

# The CHROM sequence
# ==================

def mc(xs: List<&2, R.Item>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      R.Item.chrom(x) <> mc(t)

def sapp(xs: List<&2, String>, ys: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, xs, ys)

def grp.go(cs: List<&2, String>, +cur: String, +ended: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> t:
      (String.eq(c, cur) || Bool.not(R.has(c, cur <> ended))) && grp.go(t, c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended))

def grp(cs: List<&2, String>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> t:
      grp.go(t, c, Nil{})

law gr_mc:
  for +xs: List<&2, R.Item>
  for +cur: String
  for +ended: List<&2, String>
  {L.grouped.go(xs, cur, ended) == grp.go(mc(xs), cur, ended) : Bool}

def gr_mc(xs, cur, ended):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +c = R.Item.chrom(x)
      %Equal.sym(Bool, L.grouped.go(t, c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended)),
        grp.go(mc(t), c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended)),
        gr_mc(t, c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended))) :
        {Bool.and(Bool.or(String.eq(c, cur), Bool.not(R.has(c, cur <> ended))), _) ==
          Bool.and(Bool.or(String.eq(c, cur), Bool.not(R.has(c, cur <> ended))), grp.go(mc(t), c, Bool.pick(List<&2, String>, String.eq(c, cur), ended, cur <> ended))) : Bool}
      {==}

law grouped_mc:
  for +xs: List<&2, R.Item>
  {L.grouped(xs) == grp(mc(xs)) : Bool}

def grouped_mc(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      gr_mc(t, R.Item.chrom(x), Nil{})

def allc(xs: List<&2, R.Item>, +c: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      String.eq(R.Item.chrom(x), c) && allc(t, c)

def rep(n: Nat, +c: String) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      c <> rep(k, c)

def ilen(xs: List<&2, R.Item>) -> Nat:
  List.length(&2, R.Item, xs)

law mc_rep:
  for +xs: List<&2, R.Item>
  for +c: String
  for +h: {allc(xs, c) == True{} : Bool}
  {mc(xs) == rep(ilen(xs), c) : List<&2, String>}

def mc_rep(xs, c, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +h1 = P.and_true_l(String.eq(R.Item.chrom(x), c), allc(t, c), h)
      %Equal.sym(String, R.Item.chrom(x), c, Q.str_eq_sound(R.Item.chrom(x), c, h1)) : {_ <> mc(t) == c <> rep(ilen(t), c) : List<&2, String>}
      %Equal.sym(List<&2, String>, mc(t), rep(ilen(t), c), mc_rep(t, c, P.and_true_r(String.eq(R.Item.chrom(x), c), allc(t, c), h))) :
        {c <> _ == c <> rep(ilen(t), c) : List<&2, String>}
      {==}

def ins_len.go(+x: R.Item, +y: R.Item, +t: List<&2, R.Item>, b: Bool, ih: {ilen(L.ins_first(x, t)) == 1n+ilen(t) : Nat}) ->
  {ilen(L.ins_first.put(b, x, y, t, L.ins_first(x, t))) == 1n+ilen(y <> t) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, ilen(L.ins_first(x, t)), 1n+ilen(t), ih) : {1n+_ == 1n+ilen(y <> t) : Nat}
      {==}

law ins_len:
  for +x: R.Item
  for +ys: List<&2, R.Item>
  {ilen(L.ins_first(x, ys)) == 1n+ilen(ys) : Nat}

def ins_len(x, ys):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      ins_len.go(x, y, t, Nat.is_le(R.Item.key(x), R.Item.key(y)), ins_len(x, t))

law isort_len:
  for +xs: List<&2, R.Item>
  {ilen(L.isort(xs)) == ilen(xs) : Nat}

def isort_len(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat, ilen(L.ins_first(x, L.isort(t))), 1n+ilen(L.isort(t)), ins_len(x, L.isort(t))) : {_ == 1n+ilen(t) : Nat}
      %Equal.sym(Nat, ilen(L.isort(t)), ilen(t), isort_len(t)) : {1n+_ == 1n+ilen(t) : Nat}
      {==}

def allc_ins.go(+x: R.Item, +y: R.Item, +t: List<&2, R.Item>, +c: String, b: Bool,
  +hx: {String.eq(R.Item.chrom(x), c) == True{} : Bool}, +hy: {String.eq(R.Item.chrom(y), c) == True{} : Bool}, +ht: {allc(t, c) == True{} : Bool},
  ih: {allc(L.ins_first(x, t), c) == True{} : Bool}) ->
  {allc(L.ins_first.put(b, x, y, t, L.ins_first(x, t)), c) == True{} : Bool}:
  match b:
    case True{}:
      S.and_intro(String.eq(R.Item.chrom(x), c), allc(y <> t, c), hx, S.and_intro(String.eq(R.Item.chrom(y), c), allc(t, c), hy, ht))
    case False{}:
      S.and_intro(String.eq(R.Item.chrom(y), c), allc(L.ins_first(x, t), c), hy, ih)

law allc_ins:
  for +x: R.Item
  for +ys: List<&2, R.Item>
  for +c: String
  for +hx: {String.eq(R.Item.chrom(x), c) == True{} : Bool}
  for +hy: {allc(ys, c) == True{} : Bool}
  {allc(L.ins_first(x, ys), c) == True{} : Bool}

def allc_ins(x, ys, c, hx, hy):
  match ys:
    case Nil{}:
      S.and_intro(String.eq(R.Item.chrom(x), c), True{}, hx, {==})
    case +y <> +t:
      +h1 = P.and_true_l(String.eq(R.Item.chrom(y), c), allc(t, c), hy)
      +h2 = P.and_true_r(String.eq(R.Item.chrom(y), c), allc(t, c), hy)
      allc_ins.go(x, y, t, c, Nat.is_le(R.Item.key(x), R.Item.key(y)), hx, h1, h2, allc_ins(x, t, c, hx, h2))

law allc_isort:
  for +xs: List<&2, R.Item>
  for +c: String
  for +h: {allc(xs, c) == True{} : Bool}
  {allc(L.isort(xs), c) == True{} : Bool}

def allc_isort(xs, c, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      allc_ins(x, L.isort(t), c, P.and_true_l(String.eq(R.Item.chrom(x), c), allc(t, c), h),
        allc_isort(t, c, P.and_true_r(String.eq(R.Item.chrom(x), c), allc(t, c), h)))

law mc_isort:
  for +xs: List<&2, R.Item>
  for +c: String
  for +h: {allc(xs, c) == True{} : Bool}
  {mc(L.isort(xs)) == mc(xs) : List<&2, String>}

def mc_isort(xs, c, h):
  %Equal.sym(List<&2, String>, mc(L.isort(xs)), rep(ilen(L.isort(xs)), c), mc_rep(L.isort(xs), c, allc_isort(xs, c, h))) : {_ == mc(xs) : List<&2, String>}
  %Equal.sym(Nat, ilen(L.isort(xs)), ilen(xs), isort_len(xs)) : {rep(_, c) == mc(xs) : List<&2, String>}
  Equal.sym(List<&2, String>, mc(xs), rep(ilen(xs), c), mc_rep(xs, c, h))

law mc_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  {mc(iapp(xs, ys)) == sapp(mc(xs), mc(ys)) : List<&2, String>}

def mc_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %mc_app(t, ys) : {R.Item.chrom(x) <> mc(iapp(t, ys)) == R.Item.chrom(x) <> _ : List<&2, String>}
      {==}

law allc_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +c: String
  for +h1: {allc(xs, c) == True{} : Bool}
  for +h2: {allc(ys, c) == True{} : Bool}
  {allc(iapp(xs, ys), c) == True{} : Bool}

def allc_app(xs, ys, c, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      S.and_intro(String.eq(R.Item.chrom(x), c), allc(iapp(t, ys), c), P.and_true_l(String.eq(R.Item.chrom(x), c), allc(t, c), h1),
        allc_app(t, ys, c, P.and_true_r(String.eq(R.Item.chrom(x), c), allc(t, c), h1), h2))

def chomo(run: List<&2, R.Item>) -> Bool:
  match run:
    case Nil{}:
      True{}
    case +r0 <> rt:
      allc(r0 <> rt, R.Item.chrom(r0))

law mc_isort_ch:
  for +run: List<&2, R.Item>
  for +hr: {chomo(run) == True{} : Bool}
  {mc(L.isort(run)) == mc(run) : List<&2, String>}

def mc_isort_ch(run, hr):
  match run:
    case Nil{}:
      {==}
    case +r0 <> +rt:
      mc_isort(r0 <> rt, R.Item.chrom(r0), hr)

def IHM(xs: List<&2, R.Item>) -> Type:
  @run: List<&2, R.Item> -> @done: List<&2, R.Item> -> {chomo(run) == True{} : Bool} ->
    {mc(L.gsort.go(xs, run, done)) == sapp(mc(done), sapp(mc(run), mc(xs))) : List<&2, String>}

def mg.go(+x: R.Item, +t: List<&2, R.Item>, +r0: R.Item, +rt: List<&2, R.Item>, +done: List<&2, R.Item>, b: Bool,
  +eb: {String.eq(R.Item.chrom(r0), R.Item.chrom(x)) == b : Bool}, +hr: {chomo(r0 <> rt) == True{} : Bool},
  ih: @run: List<&2, R.Item> -> @d2: List<&2, R.Item> -> {chomo(run) == True{} : Bool} ->
    {mc(L.gsort.go(t, run, d2)) == sapp(mc(d2), sapp(mc(run), mc(t))) : List<&2, String>}) ->
  {mc(L.gsort.go(t, Bool.pick(List<&2, R.Item>, b, iapp(r0 <> rt, [x]), [x]), Bool.pick(List<&2, R.Item>, b, done, iapp(done, L.isort(r0 <> rt))))) ==
    sapp(mc(done), sapp(mc(r0 <> rt), R.Item.chrom(x) <> mc(t))) : List<&2, String>}:
  match b:
    case True{}:
      +run = {r0 <> rt : List<&2, R.Item>}
      +cx = R.Item.chrom(x)
      +c = R.Item.chrom(r0)
      +ex = Equal.trans(Bool, String.eq(cx, c), String.eq(c, cx), True{}, Q.str_eq_sym(c, cx), eb)
      +hr2 = allc_app(run, [x], c, hr, S.and_intro(String.eq(cx, c), True{}, ex, {==}))
      %Equal.sym(List<&2, String>, mc(L.gsort.go(t, iapp(run, [x]), done)), sapp(mc(done), sapp(mc(iapp(run, [x])), mc(t))), ih(iapp(run, [x]), done, hr2)) : {_ == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      %Equal.sym(List<&2, String>, mc(iapp(run, [x])), sapp(mc(run), [cx]), mc_app(run, [x])) : {sapp(mc(done), sapp(_, mc(t))) == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      %Equal.sym(List<&2, String>, sapp(sapp(mc(run), [cx]), mc(t)), sapp(mc(run), sapp([cx], mc(t))), P.append_assoc(String, mc(run), [cx], mc(t))) :
        {sapp(mc(done), _) == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      {==}
    case False{}:
      +run = {r0 <> rt : List<&2, R.Item>}
      +cx = R.Item.chrom(x)
      +c = R.Item.chrom(r0)
      %Equal.sym(List<&2, String>, mc(L.gsort.go(t, [x], iapp(done, L.isort(run)))), sapp(mc(iapp(done, L.isort(run))), sapp([cx], mc(t))),
        ih([x], iapp(done, L.isort(run)), S.and_intro(String.eq(cx, cx), True{}, Q.str_eq_refl(cx), {==}))) :
        {_ == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      %Equal.sym(List<&2, String>, mc(iapp(done, L.isort(run))), sapp(mc(done), mc(L.isort(run))), mc_app(done, L.isort(run))) : {sapp(_, cx <> mc(t)) == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      %Equal.sym(List<&2, String>, mc(L.isort(run)), mc(run), mc_isort_ch(run, hr)) : {sapp(sapp(mc(done), _), cx <> mc(t)) == sapp(mc(done), sapp(mc(run), cx <> mc(t))) : List<&2, String>}
      P.append_assoc(String, mc(done), mc(run), cx <> mc(t))

# gsort keeps the CHROM sequence.
law mc_gs:
  for +xs: List<&2, R.Item>
  for +run: List<&2, R.Item>
  for +done: List<&2, R.Item>
  for +hr: {chomo(run) == True{} : Bool}
  {mc(L.gsort.go(xs, run, done)) == sapp(mc(done), sapp(mc(run), mc(xs))) : List<&2, String>}

def mc_gs(xs, run, done, hr):
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, String>, mc(iapp(done, L.isort(run))), sapp(mc(done), mc(L.isort(run))), mc_app(done, L.isort(run))) : {_ == sapp(mc(done), sapp(mc(run), Nil{})) : List<&2, String>}
      %Equal.sym(List<&2, String>, mc(L.isort(run)), mc(run), mc_isort_ch(run, hr)) : {sapp(mc(done), _) == sapp(mc(done), sapp(mc(run), Nil{})) : List<&2, String>}
      %Equal.sym(List<&2, String>, sapp(mc(run), Nil{}), mc(run), P.append_nil(String, mc(run))) : {sapp(mc(done), mc(run)) == sapp(mc(done), _) : List<&2, String>}
      {==}
    case +x <> +t:
      match run:
        case Nil{}:
          mc_gs(t, [x], done, S.and_intro(String.eq(R.Item.chrom(x), R.Item.chrom(x)), True{}, Q.str_eq_refl(R.Item.chrom(x)), {==}))
        case +r0 <> +rt:
          mg.go(x, t, r0, rt, done, String.eq(R.Item.chrom(r0), R.Item.chrom(x)), {==}, hr, r2 => d2 => h2 => mc_gs(t, r2, d2, h2))

law grouped_gs:
  for +xs: List<&2, R.Item>
  for +h: {L.grouped(xs) == True{} : Bool}
  {L.grouped(L.gsort(xs)) == True{} : Bool}

def grouped_gs(xs, h):
  %Equal.sym(Bool, L.grouped(L.gsort(xs)), grp(mc(L.gsort(xs))), grouped_mc(L.gsort(xs))) : {_ == True{} : Bool}
  %Equal.sym(List<&2, String>, mc(L.gsort(xs)), sapp(Nil{}, sapp(Nil{}, mc(xs))), mc_gs(xs, Nil{}, Nil{}, {==})) : {grp(_) == True{} : Bool}
  %grouped_mc(xs) : {_ == True{} : Bool}
  h

# Keys ascend within each CHROM
# =============================

def ins_sorted.go(+x: R.Item, +y: R.Item, +t: List<&2, R.Item>, +k: Nat, b: Bool, +eb: {Nat.is_le(R.Item.key(x), R.Item.key(y)) == b : Bool},
  +hs: {S.sorted_from(y <> t, k) == True{} : Bool}, +hk: {Nat.is_le(k, R.Item.key(x)) == True{} : Bool},
  ih: {Nat.is_le(R.Item.key(y), R.Item.key(x)) == True{} : Bool} -> {S.sorted_from(L.ins_first(x, t), R.Item.key(y)) == True{} : Bool}) ->
  {S.sorted_from(L.ins_first.put(b, x, y, t, L.ins_first(x, t)), k) == True{} : Bool}:
  match b:
    case True{}:
      S.and_intro(Nat.is_le(k, R.Item.key(x)), S.sorted_from(y <> t, R.Item.key(x)), hk,
        S.and_intro(Nat.is_le(R.Item.key(x), R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), eb,
          P.and_true_r(Nat.is_le(k, R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), hs)))
    case False{}:
      S.and_intro(Nat.is_le(k, R.Item.key(y)), S.sorted_from(L.ins_first(x, t), R.Item.key(y)),
        P.and_true_l(Nat.is_le(k, R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), hs), ih(Q.le_flip(R.Item.key(x), R.Item.key(y), eb)))

law ins_sorted:
  for +x: R.Item
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +hs: {S.sorted_from(ys, k) == True{} : Bool}
  for +hk: {Nat.is_le(k, R.Item.key(x)) == True{} : Bool}
  {S.sorted_from(L.ins_first(x, ys), k) == True{} : Bool}

def ins_sorted(x, ys, k, hs, hk):
  match ys:
    case Nil{}:
      S.and_intro(Nat.is_le(k, R.Item.key(x)), True{}, hk, {==})
    case +y <> +t:
      ins_sorted.go(x, y, t, k, Nat.is_le(R.Item.key(x), R.Item.key(y)), {==}, hs, hk,
        h2 => ins_sorted(x, t, R.Item.key(y), P.and_true_r(Nat.is_le(k, R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), hs), h2))

law isort_sorted:
  for +xs: List<&2, R.Item>
  {S.sorted_from(L.isort(xs), 0n) == True{} : Bool}

def isort_sorted(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ins_sorted(x, L.isort(t), 0n, isort_sorted(t), P.le_zero_l(R.Item.key(x)))

def asck_m(xs: List<&2, R.Item>, mp: Maybe<&2, R.Item>) -> Bool:
  match xs mp:
    case Nil{} _:
      True{}
    case +x <> t None{}:
      asck_m(t, Some{x})
    case +x <> t Some{+a}:
      (Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))) || Nat.is_le(R.Item.key(a), R.Item.key(x))) && asck_m(t, Some{x})

law asck_go_m:
  for +xs: List<&2, R.Item>
  for +a: R.Item
  {W.asck.go(xs, a) == asck_m(xs, Some{a}) : Bool}

def asck_go_m(xs, a):
  match xs:
    case Nil{}:
      {==}
    case +b <> +t:
      %asck_go_m(t, b) : {Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))), Nat.is_le(R.Item.key(a), R.Item.key(b))), W.asck.go(t, b)) ==
        Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))), Nat.is_le(R.Item.key(a), R.Item.key(b))), _) : Bool}
      {==}

law asck_eq:
  for +xs: List<&2, R.Item>
  {W.asck(xs) == asck_m(xs, None{}) : Bool}

def asck_eq(xs):
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      asck_go_m(t, a)

def lm(xs: List<&2, R.Item>, mp: Maybe<&2, R.Item>) -> Maybe<&2, R.Item>:
  match xs:
    case Nil{}:
      mp
    case x <> t:
      lm(t, Some{x})

law lm_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +mp: Maybe<&2, R.Item>
  {lm(iapp(xs, ys), mp) == lm(ys, lm(xs, mp)) : Maybe<&2, R.Item>}

def lm_app(xs, ys, mp):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      lm_app(t, ys, Some{x})

def am_app.go(+x: R.Item, +t: List<&2, R.Item>, +ys: List<&2, R.Item>, mp: Maybe<&2, R.Item>,
  +h1: {asck_m(x <> t, mp) == True{} : Bool},
  ih: {asck_m(t, Some{x}) == True{} : Bool} -> {asck_m(iapp(t, ys), Some{x}) == True{} : Bool}) ->
  {asck_m(x <> iapp(t, ys), mp) == True{} : Bool}:
  match mp:
    case None{}:
      ih(h1)
    case Some{+a}:
      +cd = Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x)))
      S.and_intro(cd, asck_m(iapp(t, ys), Some{x}), P.and_true_l(cd, asck_m(t, Some{x}), h1), ih(P.and_true_r(cd, asck_m(t, Some{x}), h1)))

law am_app:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +mp: Maybe<&2, R.Item>
  for +h1: {asck_m(xs, mp) == True{} : Bool}
  for +h2: {asck_m(ys, lm(xs, mp)) == True{} : Bool}
  {asck_m(iapp(xs, ys), mp) == True{} : Bool}

def am_app(xs, ys, mp, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      am_app.go(x, t, ys, mp, h1, h => am_app(t, ys, Some{x}, h, h2))

law sorted_am:
  for +xs: List<&2, R.Item>
  for +a: R.Item
  for +hs: {S.sorted_from(xs, R.Item.key(a)) == True{} : Bool}
  {asck_m(xs, Some{a}) == True{} : Bool}

def sorted_am(xs, a, hs):
  match xs:
    case Nil{}:
      {==}
    case +b <> +t:
      S.and_intro(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))), Nat.is_le(R.Item.key(a), R.Item.key(b))), asck_m(t, Some{b}),
        S.or_true_rr(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))), Nat.is_le(R.Item.key(a), R.Item.key(b)),
          P.and_true_l(Nat.is_le(R.Item.key(a), R.Item.key(b)), S.sorted_from(t, R.Item.key(b)), hs)),
        sorted_am(t, b, P.and_true_r(Nat.is_le(R.Item.key(a), R.Item.key(b)), S.sorted_from(t, R.Item.key(b)), hs)))

def bnd(mp: Maybe<&2, R.Item>, +c: String) -> Bool:
  match mp:
    case None{}:
      True{}
    case Some{d}:
      Bool.not(String.eq(R.Item.chrom(d), c))

def chr_sound(+x: R.Item, +t: List<&2, R.Item>, +c: String, +h: {allc(x <> t, c) == True{} : Bool}) -> {R.Item.chrom(x) == c : String}:
  Q.str_eq_sound(R.Item.chrom(x), c, P.and_true_l(String.eq(R.Item.chrom(x), c), allc(t, c), h))

law am_sorted:
  for +ys: List<&2, R.Item>
  for +mp: Maybe<&2, R.Item>
  for +c: String
  for +hs: {S.sorted_from(ys, 0n) == True{} : Bool}
  for +hc: {allc(ys, c) == True{} : Bool}
  for +hb: {bnd(mp, c) == True{} : Bool}
  {asck_m(ys, mp) == True{} : Bool}

def am_sorted(ys, mp, c, hs, hc, hb):
  match ys mp:
    case Nil{} _:
      {==}
    case +y <> +t None{}:
      sorted_am(t, y, P.and_true_r(Nat.is_le(0n, R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), hs))
    case +y <> +t Some{+d}:
      +ey = chr_sound(y, t, c, hc)
      S.and_intro(Bool.or(Bool.not(String.eq(R.Item.chrom(d), R.Item.chrom(y))), Nat.is_le(R.Item.key(d), R.Item.key(y))), asck_m(t, Some{y}),
        S.or_true_l(Bool.not(String.eq(R.Item.chrom(d), R.Item.chrom(y))), Nat.is_le(R.Item.key(d), R.Item.key(y)),
          (%Equal.sym(String, R.Item.chrom(y), c, ey) : {Bool.not(String.eq(R.Item.chrom(d), _)) == True{} : Bool}; hb)),
        sorted_am(t, y, P.and_true_r(Nat.is_le(0n, R.Item.key(y)), S.sorted_from(t, R.Item.key(y)), hs)))

law lm_ne:
  for +ys: List<&2, R.Item>
  for +mp: Maybe<&2, R.Item>
  for +c: String
  for +c2: String
  for +hc: {allc(ys, c) == True{} : Bool}
  for +hcc: {String.eq(c, c2) == False{} : Bool}
  for ne: {ys == Nil{} : List<&2, R.Item>} -> Empty
  {bnd(lm(ys, mp), c2) == True{} : Bool}

def lm_ne(ys, mp, c, c2, hc, hcc, ne):
  match ys:
    case Nil{}:
      Empty.absurd({bnd(mp, c2) == True{} : Bool}, ne({==}))
    case +y <> Nil{}:
      %Equal.sym(String, R.Item.chrom(y), c, chr_sound(y, Nil{}, c, hc)) : {Bool.not(String.eq(_, c2)) == True{} : Bool}
      %Equal.sym(Bool, String.eq(c, c2), False{}, hcc) : {Bool.not(_) == True{} : Bool}
      {==}
    case +y <> (+z <> +r):
      lm_ne(z <> r, Some{y}, c, c2, P.and_true_r(String.eq(R.Item.chrom(y), c), allc(z <> r, c), hc), hcc, e => X2.cons_ne_nil(R.Item, z, r, e))

law isort_ne:
  for +r0: R.Item
  for +rt: List<&2, R.Item>
  for e: {L.isort(r0 <> rt) == Nil{} : List<&2, R.Item>}
  Empty

def isort_ne(r0, rt, e):
  P.succ_ne_zero(ilen(rt), Equal.trans(Nat, 1n+ilen(rt), ilen(L.isort(r0 <> rt)), 0n,
    Equal.sym(Nat, ilen(L.isort(r0 <> rt)), 1n+ilen(rt), isort_len(r0 <> rt)),
    Equal.cong(List<&2, R.Item>, Nat, z => ilen(z), L.isort(r0 <> rt), Nil{}, e)))

def ag.go(+x: R.Item, +t: List<&2, R.Item>, +r0: R.Item, +rt: List<&2, R.Item>, +done: List<&2, R.Item>, b: Bool,
  +eb: {String.eq(R.Item.chrom(r0), R.Item.chrom(x)) == b : Bool},
  +hd: {asck_m(done, None{}) == True{} : Bool}, +hc: {allc(r0 <> rt, R.Item.chrom(r0)) == True{} : Bool},
  +hb: {bnd(lm(done, None{}), R.Item.chrom(r0)) == True{} : Bool},
  ih: @s0: R.Item -> @st: List<&2, R.Item> -> @d2: List<&2, R.Item> -> {asck_m(d2, None{}) == True{} : Bool} ->
    {allc(s0 <> st, R.Item.chrom(s0)) == True{} : Bool} -> {bnd(lm(d2, None{}), R.Item.chrom(s0)) == True{} : Bool} ->
    {asck_m(L.gsort.go(t, s0 <> st, d2), None{}) == True{} : Bool}) ->
  {asck_m(L.gsort.go(t, Bool.pick(List<&2, R.Item>, b, iapp(r0 <> rt, [x]), [x]), Bool.pick(List<&2, R.Item>, b, done, iapp(done, L.isort(r0 <> rt)))), None{}) == True{} : Bool}:
  match b:
    case True{}:
      +c = R.Item.chrom(r0)
      +cx = R.Item.chrom(x)
      +ex = Equal.trans(Bool, String.eq(cx, c), String.eq(c, cx), True{}, Q.str_eq_sym(c, cx), eb)
      ih(r0, iapp(rt, [x]), done, hd, allc_app(r0 <> rt, [x], c, hc, S.and_intro(String.eq(cx, c), True{}, ex, {==})), hb)
    case False{}:
      +c = R.Item.chrom(r0)
      +cx = R.Item.chrom(x)
      +run = {r0 <> rt : List<&2, R.Item>}
      +srt = L.isort(run)
      +hi = allc_isort(run, c, hc)
      +hd2 = am_app(done, srt, None{}, hd, am_sorted(srt, lm(done, None{}), c, isort_sorted(run), hi, hb))
      +hb2 = {(%Equal.sym(Maybe<&2, R.Item>, lm(iapp(done, srt), None{}), lm(srt, lm(done, None{})), lm_app(done, srt, None{})) : {bnd(_, cx) == True{} : Bool};
          lm_ne(srt, lm(done, None{}), c, cx, hi, eb, e => isort_ne(r0, rt, e))) :
        {bnd(lm(iapp(done, srt), None{}), cx) == True{} : Bool}}
      ih(x, Nil{}, iapp(done, srt), hd2, S.and_intro(String.eq(cx, cx), True{}, Q.str_eq_refl(cx), {==}), hb2)

law ag:
  for +xs: List<&2, R.Item>
  for +r0: R.Item
  for +rt: List<&2, R.Item>
  for +done: List<&2, R.Item>
  for +hd: {asck_m(done, None{}) == True{} : Bool}
  for +hc: {allc(r0 <> rt, R.Item.chrom(r0)) == True{} : Bool}
  for +hb: {bnd(lm(done, None{}), R.Item.chrom(r0)) == True{} : Bool}
  {asck_m(L.gsort.go(xs, r0 <> rt, done), None{}) == True{} : Bool}

def ag(xs, r0, rt, done, hd, hc, hb):
  match xs:
    case Nil{}:
      +run = {r0 <> rt : List<&2, R.Item>}
      am_app(done, L.isort(run), None{}, hd, am_sorted(L.isort(run), lm(done, None{}), R.Item.chrom(r0), isort_sorted(run), allc_isort(run, R.Item.chrom(r0), hc), hb))
    case +x <> +t:
      ag.go(x, t, r0, rt, done, String.eq(R.Item.chrom(r0), R.Item.chrom(x)), {==}, hd, hc, hb,
        s0 => st => d2 => h1 => h2 => h3 => ag(t, s0, st, d2, h1, h2, h3))

# gsort sorts keys within each CHROM.
law asck_gs:
  for +xs: List<&2, R.Item>
  {W.asck(L.gsort(xs)) == True{} : Bool}

def asck_gs.m(xs: List<&2, R.Item>) -> {asck_m(L.gsort(xs), None{}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      ag(t, x, Nil{}, Nil{}, {==}, S.and_intro(String.eq(R.Item.chrom(x), R.Item.chrom(x)), True{}, Q.str_eq_refl(R.Item.chrom(x)), {==}), {==})

def asck_gs(xs):
  %Equal.sym(Bool, W.asck(L.gsort(xs)), asck_m(L.gsort(xs), None{}), asck_eq(L.gsort(xs))) : {_ == True{} : Bool}
  asck_gs.m(xs)
