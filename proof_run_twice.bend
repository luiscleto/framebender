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
import ./proof_run_tail.bend as U
import ./proof_run_qm.bend as QM

# twice_run: run 1's body lines are its items' texts; run 2 reads them back
# as lines whose items have the same key, CHROM and text, grouped and sorted,
# so run 2 succeeds and writes the same body.

# Same key, CHROM and text, item by item
# ======================================

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

law texts_sim:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +h: {QM.allsim(xs, ys) == True{} : Bool}
  {L.texts(xs) == L.texts(ys) : String}

def texts_sim(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case +x <> +t +y <> +u:
      +h1 = P.and_true_l(N.simb(x, y), QM.allsim(t, u), h)
      +h2 = P.and_true_r(N.simb(x, y), QM.allsim(t, u), h)
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
  for +h: {QM.allsim(xs, ys) == True{} : Bool}
  {G.mc(xs) == G.mc(ys) : List<&2, String>}

def mc_sim(xs, ys, h):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case +x <> +t +y <> +u:
      +h1 = P.and_true_l(N.simb(x, y), QM.allsim(t, u), h)
      +h2 = P.and_true_r(N.simb(x, y), QM.allsim(t, u), h)
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
  for +h: {QM.allsim(xs, ys) == True{} : Bool}
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
  for +h: {QM.allsim(xs, ys) == True{} : Bool}
  for +hm: {simm(mp, mq) == True{} : Bool}
  {G.asck_m(xs, mp) == G.asck_m(ys, mq) : Bool}

def am_sim(xs, ys, mp, mq, h, hm):
  match xs ys mp mq:
    case Nil{} Nil{} _ _:
      {==}
    case +x <> +t +y <> +u None{} None{}:
      am_sim(t, u, Some{x}, Some{y}, P.and_true_r(N.simb(x, y), QM.allsim(t, u), h), P.and_true_l(N.simb(x, y), QM.allsim(t, u), h))
    case +x <> +t +y <> +u Some{+a} Some{+b}:
      +hx = P.and_true_l(N.simb(x, y), QM.allsim(t, u), h)
      %am_sim.cond(a, b, x, y, hm, hx) : {Bool.and(Bool.or(Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(x))), Nat.is_le(R.Item.key(a), R.Item.key(x))), G.asck_m(t, Some{x})) ==
        Bool.and(_, G.asck_m(u, Some{y})) : Bool}
      %am_sim(t, u, Some{x}, Some{y}, P.and_true_r(N.simb(x, y), QM.allsim(t, u), h), hx) :
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
  for +h: {QM.allsim(xs, ys) == True{} : Bool}
  for +hk: {W.asck(ys) == True{} : Bool}
  {W.asck(xs) == True{} : Bool}

def asck_sim(xs, ys, h, hk):
  %Equal.sym(Bool, W.asck(xs), G.asck_m(xs, None{}), G.asck_eq(xs)) : {_ == True{} : Bool}
  %Equal.sym(Bool, G.asck_m(xs, None{}), G.asck_m(ys, None{}), am_sim(xs, ys, None{}, None{}, h, {==})) : {_ == True{} : Bool}
  %G.asck_eq(ys) : {_ == True{} : Bool}
  hk

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

def YS(+fasta: String, +vcf: String, +o: B.Opts) -> List<&2, R.Item>:
  L.gsort(L.out_items(fasta, vcf, o))

def TL(+fasta: String, +vcf: String, +o: B.Opts) -> List<&2, B.Line>:
  QM.lns(YS(fasta, vcf, o))

def O1(+fasta: String, +vcf: String, +o: B.Opts) -> String:
  R.Report.out(L.run(fasta, vcf, o))

law r1_has:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {H.has_c(LS1(vcf)) == True{} : Bool}

def r1_has(fasta, vcf, o, h):
  H.hdr_has(LS1(vcf), FA(fasta), L.defs(vcf), o, 0n, "", K0(), "", Nil{}, h)

law r1_go:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {H.all_lgo(H.post_c(LS1(vcf)), FA(fasta), L.defs(vcf), o) == True{} : Bool}

def r1_go(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +defs = L.defs(vcf)
  +er = H.hdr_run(ls, fa, defs, o, 0n, "", K0(), "", Nil{}, r1_has(fasta, vcf, o, h))
  +h2 = {(%er : {R.Report.code(R.finish(_)) == 0n : Nat}; h) :
    {R.Report.code(R.finish(L.run.go(H.post_c(ls), fa, defs, o, H.bst(H.idx_c(ls, 0n), K0(), L.head.go(ls, o, False{}, ""), Nil{})))) == 0n : Nat}}
  H.body_go(H.post_c(ls), fa, defs, o, H.idx_c(ls, 0n), "", None{}, Nil{}, None{}, Nil{}, K0(), L.head.go(ls, o, False{}, ""), Nil{}, h2)

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

law r1_allqm:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {QM.allqm(FA(fasta), L.defs(vcf), o, L.out_items(fasta, vcf, o)) == True{} : Bool}

def r1_allqm(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +defs = L.defs(vcf)
  +hc = r1_has(fasta, vcf, o, h)
  %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, 0n, Nil{}})), U.mitems(H.post_c(ls), fa, defs, o, H.idx_c(ls, 0n)),
    H.hdr_mitems(ls, fa, defs, o, 0n, hc)) : {QM.allqm(fa, defs, o, _) == True{} : Bool}
  QM.allqm_lines(H.post_c(ls), fa, defs, o, H.idx_c(ls, 0n), post_good(ls, X.lines_good(vcf), hc), r1_go(fasta, vcf, o, h))

law ys_allqm:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {QM.allqm(FA(fasta), L.defs(vcf), o, YS(fasta, vcf, o)) == True{} : Bool}

def ys_allqm(fasta, vcf, o, h):
  QM.allqm_gs(FA(fasta), L.defs(vcf), o, L.out_items(fasta, vcf, o), Nil{}, Nil{}, r1_allqm(fasta, vcf, o, h), {==}, {==})

law r1_out:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {O1(fasta, vcf, o) == B.Lines.text(H.Hl(LS1(vcf), o)) ++ B.Lines.text(TL(fasta, vcf, o)) : String}

def r1_out(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +fa = FA(fasta)
  +defs = L.defs(vcf)
  +hc = r1_has(fasta, vcf, o, h)
  +ys = YS(fasta, vcf, o)
  %Equal.sym(String, B.Lines.text(QM.lns(ys)), L.texts(ys), QM.lnsm_text(fa, defs, o, ys, ys_allqm(fasta, vcf, o, h))) :
    {O1(fasta, vcf, o) == B.Lines.text(H.Hl(ls, o)) ++ _ : String}
  %H.hdr_head(ls, o, "", hc) : {O1(fasta, vcf, o) == _ ++ L.texts(ys) : String}
  PS.sorted_head(ls, fa, defs, o, 0n, "", K0(), "", Nil{}, h)

law r1_body:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.body(O1(fasta, vcf, o)) == B.Lines.text(TL(fasta, vcf, o)) : String}

def r1_body(fasta, vcf, o, h):
  %Equal.sym(String, O1(fasta, vcf, o), B.Lines.text(H.Hl(LS1(vcf), o)) ++ B.Lines.text(TL(fasta, vcf, o)), r1_out(fasta, vcf, o, h)) :
    {L.body(_) == B.Lines.text(TL(fasta, vcf, o)) : String}
  body_hd(LS1(vcf), o, TL(fasta, vcf, o), X.lines_good(vcf), r1_has(fasta, vcf, o, h),
    QM.lnsm_good(FA(fasta), L.defs(vcf), o, YS(fasta, vcf, o), ys_allqm(fasta, vcf, o, h)))

def LS2(+fasta: String, +vcf: String, +o: B.Opts) -> List<&2, B.Line>:
  X.lapp(P2(LS1(vcf), o), H.cl_c(LS1(vcf)) <> TL(fasta, vcf, o))

law r2_lines:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {B.Text.lines(O1(fasta, vcf, o)) == LS2(fasta, vcf, o) : List<&2, B.Line>}

def r2_lines(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +hl = H.Hl(ls, o)
  +tl = TL(fasta, vcf, o)
  +hc = r1_has(fasta, vcf, o, h)
  %Equal.sym(String, O1(fasta, vcf, o), B.Lines.text(hl) ++ B.Lines.text(tl), r1_out(fasta, vcf, o, h)) : {B.Text.lines(_) == LS2(fasta, vcf, o) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(hl) ++ B.Lines.text(tl)), X.lapp(hl, B.Text.lines(B.Lines.text(tl))),
    X.lines_text_app(hl, B.Lines.text(tl), H.hl_good(ls, o, X.lines_good(vcf), hc))) : {_ == LS2(fasta, vcf, o) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(tl)), tl,
    X.lines_text(tl, QM.lnsm_good(FA(fasta), L.defs(vcf), o, YS(fasta, vcf, o), ys_allqm(fasta, vcf, o, h)))) :
    {X.lapp(hl, _) == LS2(fasta, vcf, o) : List<&2, B.Line>}
  hl_split(ls, o, tl)

law r2_has:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {H.has_c(LS2(fasta, vcf, o)) == True{} : Bool}

def r2_has(fasta, vcf, o, h):
  H.dec_has(P2(LS1(vcf), o), H.cl_c(LS1(vcf)), TL(fasta, vcf, o), p2_nc(LS1(vcf), o), H.cl_isc(LS1(vcf), r1_has(fasta, vcf, o, h)))

# The header's definitions
# ========================

law dg_done:
  for +ts: List<&2, B.Line>
  for +d: B.Defs
  {L.defs.go(ts, True{}, d) == d : B.Defs}

def dg_done(ts, d):
  match ts:
    case Nil{}:
      {==}
    case +l <> +t:
      dg_done(t, d)

law dg_app:
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  for +d: B.Defs
  for +h: {H.all_nc(xs) == True{} : Bool}
  {L.defs.go(X.lapp(xs, ys), False{}, d) == L.defs.go(ys, False{}, L.defs.go(xs, False{}, d)) : B.Defs}

def dg_app(xs, ys, d, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +ex = Equal.sym(Bool, H.isc(x), False{}, H.nc_head(x, t, h))
      %ex : {L.defs.go(X.lapp(t, ys), _, B.Defs.line(d, B.Line.body(x))) == L.defs.go(ys, False{}, L.defs.go(t, _, B.Defs.line(d, B.Line.body(x)))) : B.Defs}
      dg_app(t, ys, B.Defs.line(d, B.Line.body(x)), H.nc_tail(x, t, h))

# The definitions read from lines up to and including the #CHROM line cl.
law dg_cl:
  for +ps: List<&2, B.Line>
  for +cl: B.Line
  for +ts: List<&2, B.Line>
  for +d: B.Defs
  for +hp: {H.all_nc(ps) == True{} : Bool}
  for +hc: {H.isc(cl) == True{} : Bool}
  {L.defs.go(X.lapp(ps, cl <> ts), False{}, d) == B.Defs.line(L.defs.go(ps, False{}, d), B.Line.body(cl)) : B.Defs}

def dg_cl(ps, cl, ts, d, hp, hc):
  +d1 = L.defs.go(ps, False{}, d)
  %Equal.sym(B.Defs, L.defs.go(X.lapp(ps, cl <> ts), False{}, d), L.defs.go(cl <> ts, False{}, d1), dg_app(ps, cl <> ts, d, hp)) : {_ == B.Defs.line(d1, B.Line.body(cl)) : B.Defs}
  %Equal.sym(Bool, H.isc(cl), True{}, hc) : {L.defs.go(ts, _, B.Defs.line(d1, B.Line.body(cl))) == B.Defs.line(d1, B.Line.body(cl)) : B.Defs}
  dg_done(ts, B.Defs.line(d1, B.Line.body(cl)))

def dg_added(o: B.Opts, +tm: String, +d: B.Defs) -> {L.defs.go([H.al1(tm), H.al2(o, tm)], False{}, d) == d : B.Defs}:
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      {==}

# Run 1's output has the input's header definitions: the added lines define
# nothing.
law defs_out:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.defs(O1(fasta, vcf, o)) == L.defs(vcf) : B.Defs}

def defs_out(fasta, vcf, o, h):
  +ls = LS1(vcf)
  +pre = H.pre_c(ls)
  +cl = H.cl_c(ls)
  +tm = B.Line.term(cl)
  +d0 = {B.Defs{Nil{}, Nil{}} : B.Defs}
  +hc = r1_has(fasta, vcf, o, h)
  +hic = H.cl_isc(ls, hc)
  %Equal.sym(List<&2, B.Line>, B.Text.lines(O1(fasta, vcf, o)), LS2(fasta, vcf, o), r2_lines(fasta, vcf, o, h)) :
    {L.defs.go(_, False{}, d0) == L.defs(vcf) : B.Defs}
  %Equal.sym(B.Defs, L.defs.go(LS2(fasta, vcf, o), False{}, d0), B.Defs.line(L.defs.go(P2(ls, o), False{}, d0), B.Line.body(cl)), dg_cl(P2(ls, o), cl, TL(fasta, vcf, o), d0, p2_nc(ls, o), hic)) : {_ == L.defs(vcf) : B.Defs}
  %Equal.sym(B.Defs, L.defs.go(P2(ls, o), False{}, d0), L.defs.go([H.al1(tm), H.al2(o, tm)], False{}, L.defs.go(pre, False{}, d0)), dg_app(pre, [H.al1(tm), H.al2(o, tm)], d0, H.pre_nc(ls))) : {B.Defs.line(_, B.Line.body(cl)) == L.defs(vcf) : B.Defs}
  %Equal.sym(B.Defs, L.defs.go([H.al1(tm), H.al2(o, tm)], False{}, L.defs.go(pre, False{}, d0)), L.defs.go(pre, False{}, d0), dg_added(o, tm, L.defs.go(pre, False{}, d0))) : {B.Defs.line(_, B.Line.body(cl)) == L.defs(vcf) : B.Defs}
  %Equal.sym(List<&2, B.Line>, ls, X.lapp(pre, cl <> H.post_c(ls)), H.hs_split(ls, hc)) : {B.Defs.line(L.defs.go(pre, False{}, d0), B.Line.body(cl)) == L.defs.go(_, False{}, d0) : B.Defs}
  Equal.sym(B.Defs, L.defs.go(X.lapp(pre, cl <> H.post_c(ls)), False{}, d0), B.Defs.line(L.defs.go(pre, False{}, d0), B.Line.body(cl)),
    dg_cl(pre, cl, H.post_c(ls), d0, H.pre_nc(ls), hic))

# Run 2
# =====

def BS2(+fasta: String, +vcf: String, +o: B.Opts) -> R.RunSt:
  +ls2 = LS2(fasta, vcf, o)
  H.bst(H.idx_c(ls2, 0n), K0(), L.head.go(ls2, o, False{}, ""), Nil{})

law r2_run:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  {L.run(fasta, O1(fasta, vcf, o), o) == R.finish(L.run.go(TL(fasta, vcf, o), FA(fasta), L.defs(vcf), o, BS2(fasta, vcf, o))) : R.Report}

def r2_run(fasta, vcf, o, h):
  +ls2 = LS2(fasta, vcf, o)
  +fa = FA(fasta)
  +d2 = L.defs(O1(fasta, vcf, o))
  +h2 = r2_has(fasta, vcf, o, h)
  +rhs = R.finish(L.run.go(TL(fasta, vcf, o), fa, L.defs(vcf), o, BS2(fasta, vcf, o)))
  %Equal.sym(List<&2, B.Line>, B.Text.lines(O1(fasta, vcf, o)), ls2, r2_lines(fasta, vcf, o, h)) :
    {R.finish(L.run.go(_, fa, d2, o, R.start_st())) == rhs : R.Report}
  %Equal.sym(R.RunSt, L.run.go(ls2, fa, d2, o, H.hst(0n, "", K0(), "", Nil{})), L.run.go(H.post_c(ls2), fa, d2, o, BS2(fasta, vcf, o)),
    H.hdr_run(ls2, fa, d2, o, 0n, "", K0(), "", Nil{}, h2)) :
    {R.finish(_) == rhs : R.Report}
  %Equal.sym(List<&2, B.Line>, H.post_c(ls2), TL(fasta, vcf, o),
    H.dec_post(P2(LS1(vcf), o), H.cl_c(LS1(vcf)), TL(fasta, vcf, o), p2_nc(LS1(vcf), o), H.cl_isc(LS1(vcf), r1_has(fasta, vcf, o, h)))) :
    {R.finish(L.run.go(_, fa, d2, o, BS2(fasta, vcf, o))) == rhs : R.Report}
  %Equal.sym(B.Defs, d2, L.defs(vcf), defs_out(fasta, vcf, o, h)) :
    {R.finish(L.run.go(TL(fasta, vcf, o), fa, _, o, BS2(fasta, vcf, o))) == rhs : R.Report}
  {==}

def N2(+fasta: String, +vcf: String, +o: B.Opts) -> Nat:
  H.idx_c(LS2(fasta, vcf, o), 0n)

def ZS(+fasta: String, +vcf: String, +o: B.Opts) -> List<&2, R.Item>:
  U.mitems(TL(fasta, vcf, o), FA(fasta), L.defs(vcf), o, N2(fasta, vcf, o))

law r2_cm:
  for +fasta: String
  for +vcf: String
  for +o: B.Opts
  for +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat}
  W.CM(FA(fasta), L.defs(vcf), o, TL(fasta, vcf, o), L.head.go(LS2(fasta, vcf, o), o, False{}, "") ++ L.texts(ZS(fasta, vcf, o)), BS2(fasta, vcf, o))

def r2_cm(fasta, vcf, o, h):
  +fa = FA(fasta)
  +defs = L.defs(vcf)
  +ys = YS(fasta, vcf, o)
  +tl = TL(fasta, vcf, o)
  +n2 = N2(fasta, vcf, o)
  +zs = ZS(fasta, vcf, o)
  +hq = ys_allqm(fasta, vcf, o, h)
  +sim = QM.mitems_sim(fa, defs, o, ys, n2, hq)
  +hgr = G.grouped_gs(L.out_items(fasta, vcf, o), PG.grouped_head(LS1(vcf), fa, defs, o, 0n, "", K0(), "", Nil{}, h))
  W.two_first(tl, fa, defs, o, n2, "", K0(), L.head.go(LS2(fasta, vcf, o), o, False{}, ""), Nil{},
    grouped_sim(zs, ys, sim, hgr), asck_sim(zs, ys, sim, G.asck_gs(L.out_items(fasta, vcf, o))), QM.lnsm_m1(fa, defs, o, ys, hq))

def twice.fin(+fasta: String, +vcf: String, +o: B.Opts, +h: {R.Report.code(L.run(fasta, vcf, o)) == 0n : Nat},
  cm: W.CM(FA(fasta), L.defs(vcf), o, TL(fasta, vcf, o), L.head.go(LS2(fasta, vcf, o), o, False{}, "") ++ L.texts(ZS(fasta, vcf, o)), BS2(fasta, vcf, o))) ->
  {(Nat.is_eq(R.Report.code(L.run(fasta, O1(fasta, vcf, o), o)), 0n)
    && String.eq(L.body(R.Report.out(L.run(fasta, O1(fasta, vcf, o), o))), L.body(O1(fasta, vcf, o)))) == True{} : Bool}:
  match cm:
    case (+c2, +e2):
      +fa = FA(fasta)
      +defs = L.defs(vcf)
      +ys = YS(fasta, vcf, o)
      +tl = TL(fasta, vcf, o)
      +ls2 = LS2(fasta, vcf, o)
      +n2 = N2(fasta, vcf, o)
      +zs = ZS(fasta, vcf, o)
      +hd2 = L.head.go(ls2, o, False{}, "")
      +run2 = L.run(fasta, O1(fasta, vcf, o), o)
      +fin2 = R.finish(L.run.go(tl, fa, defs, o, BS2(fasta, vcf, o)))
      +er = r2_run(fasta, vcf, o, h)
      +hq = ys_allqm(fasta, vcf, o, h)
      +h2 = r2_has(fasta, vcf, o, h)
      +ec = Equal.trans(Nat, R.Report.code(run2), R.Report.code(fin2), 0n, Equal.cong(R.Report, Nat, z => R.Report.code(z), run2, fin2, er), c2)
      +eo = {Equal.trans(String, R.Report.out(run2), R.Report.out(fin2), hd2 ++ L.texts(zs),
          Equal.cong(R.Report, String, z => R.Report.out(z), run2, fin2, er), e2) :
        {R.Report.out(run2) == hd2 ++ L.texts(zs) : String}}
      +eo2 = {(%H.hdr_head(ls2, o, "", h2) : {R.Report.out(run2) == _ ++ B.Lines.text(tl) : String};
          %Equal.sym(String, B.Lines.text(QM.lns(ys)), L.texts(ys), QM.lnsm_text(fa, defs, o, ys, hq)) : {R.Report.out(run2) == hd2 ++ _ : String};
          %texts_sim(zs, ys, QM.mitems_sim(fa, defs, o, ys, n2, hq)) : {R.Report.out(run2) == hd2 ++ _ : String};
          eo) : {R.Report.out(run2) == B.Lines.text(H.Hl(ls2, o)) ++ B.Lines.text(tl) : String}}
      +hg2 = {(%r2_lines(fasta, vcf, o, h) : {X.all_good(_) == True{} : Bool}; X.lines_good(O1(fasta, vcf, o))) : {X.all_good(ls2) == True{} : Bool}}
      +eb2 = {(%Equal.sym(String, R.Report.out(run2), B.Lines.text(H.Hl(ls2, o)) ++ B.Lines.text(tl), eo2) : {L.body(_) == B.Lines.text(tl) : String};
          body_hd(ls2, o, tl, hg2, h2, QM.lnsm_good(fa, defs, o, ys, hq))) : {L.body(R.Report.out(run2)) == B.Lines.text(tl) : String}}
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
