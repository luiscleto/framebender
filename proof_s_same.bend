import Base
import ./types.bend as B
import ./proof_s_cr.bend as CR
import ./LAWS.bend as L
import ./proof_s_str.bend as ST
import ./proof_s_site.bend as SI
import ./proof_s_chars.bend as CH
import ./proof_run_base.bend as RB
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# Law split_site: each record keeps the line's CHROM, POS, ID, REF, QUAL,
# FILTER and FORMAT, and its number of fields. Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Gs() -> Data:
  List<&2, B.Got>

def TAB() -> CH.Cls:
  CH.NoC{'\t'}

# The two ways of saying "no c" agree.
law noc_allc:
  for +s: String
  for +c: Char
  {ST.noc(s, c) == CH.ALLC(CH.NoC{c}, s) : Bool}

def noc_allc(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(Bool.not(Char.is_eq(h, c)), z), ST.noc(t, c), CH.ALLC(CH.NoC{c}, t), noc_allc(t, c))

law alls_noc:
  for +xs: Ss()
  for +c: Char
  {ST.allnoc(xs, c) == CH.ALLS(CH.NoC{c}, xs) : Bool}

def alls_noc(xs, c):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, ST.noc(x, c), CH.ALLC(CH.NoC{c}, x), noc_allc(x, c)) : {Bool.and(_, ST.allnoc(t, c)) == CH.ALLS(CH.NoC{c}, Con{x, t}) : Bool}
      %Equal.sym(Bool, ST.allnoc(t, c), CH.ALLS(CH.NoC{c}, t), alls_noc(t, c)) : {Bool.and(CH.ALLC(CH.NoC{c}, x), _) == CH.ALLS(CH.NoC{c}, Con{x, t}) : Bool}
      {==}

# The texts of results.
def TX(gs: Gs()) -> Ss():
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      SI.gtext(g) <> TX(t)

def is_got(g: B.Got) -> Bool:
  match g:
    case B.Got{s}:
      True{}
    case B.Refuse{c}:
      False{}

# A result that is a text is the text of itself.
def got_self(+g: B.Got, +x: String, +h: {g == B.Got{x} : B.Got}) -> {g == B.Got{SI.gtext(g)} : B.Got}:
  match g:
    case B.Got{+y}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Got, Bool, is_got, B.Refuse{c}, B.Got{x}, h)))

def cat_l(+a: B.Got, +b: B.Got, +x: String, +h: {B.Got.cat(a, "\t", b) == B.Got{x} : B.Got}) -> {a == B.Got{SI.gtext(a)} : B.Got}:
  match a:
    case B.Got{+y}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(Equal.cong(B.Got, Bool, is_got, B.Refuse{c}, B.Got{x}, h)))

def cat_x(+y: String, +b: B.Got, +x: String, +h: {B.Got.cat(B.Got{y}, "\t", b) == B.Got{x} : B.Got}) ->
  {x == String.append(y, String.append("\t", SI.gtext(b))) : String}:
  SI.cat_y(y, b, x, h)

def cat_b(+y: String, +b: B.Got, +x: String, +h: {B.Got.cat(B.Got{y}, "\t", b) == B.Got{x} : B.Got}) -> {b == B.Got{SI.gtext(b)} : B.Got}:
  SI.cat_r(y, b, x, h)

def gok_noc(+g: B.Got, +eg: {g == B.Got{SI.gtext(g)} : B.Got}, +hg: {CH.GOK(TAB(), g) == True{} : Bool}) -> {ST.noc(SI.gtext(g), '\t') == True{} : Bool}:
  +h2 = AB.subst(B.Got, z => {CH.GOK(TAB(), z) == True{} : Bool}, g, B.Got{SI.gtext(g)}, eg, hg)
  Equal.trans(Bool, ST.noc(SI.gtext(g), '\t'), CH.ALLC(CH.NoC{'\t'}, SI.gtext(g)), True{}, noc_allc(SI.gtext(g), '\t'), h2)

# Results joined with tabs, none holding a tab: the fields are their texts.
law join_fields:
  for +t: Gs()
  for +g: B.Got
  for +x: String
  for +h: {B.Got.join(Con{g, t}, "\t") == B.Got{x} : B.Got}
  for +hg: {CH.GOKS(TAB(), Con{g, t}) == True{} : Bool}
  {B.Rec.fields(x) == TX(Con{g, t}) : Ss()}

def join_fields(t, g, x, h, hg):
  match t:
    case Nil{}:
      +eg = got_self(g, x, h)
      +ex = Equal.cong(B.Got, String, SI.gtext, g, B.Got{x}, h)
      %ex : {B.Rec.fields(_) == TX(Con{g, Nil{}}) : Ss()}
      ST.split_noc(SI.gtext(g), '\t', gok_noc(g, eg, AB.and_true_l(CH.GOK(TAB(), g), True{}, hg)))
    case Con{+g2, +t2}:
      +J = B.Got.join(Con{g2, t2}, "\t")
      +eg = cat_l(g, J, x, h)
      +h2 = AB.subst(B.Got, z => {B.Got.cat(z, "\t", J) == B.Got{x} : B.Got}, g, B.Got{SI.gtext(g)}, eg, h)
      +ex = cat_x(SI.gtext(g), J, x, h2)
      +eJ = cat_b(SI.gtext(g), J, x, h2)
      %Equal.sym(String, x, String.append(SI.gtext(g), String.append("\t", SI.gtext(J))), ex) : {B.Rec.fields(_) == TX(Con{g, Con{g2, t2}}) : Ss()}
      %Equal.sym(Ss(), String.split(String.append(SI.gtext(g), SCon{'\t', SI.gtext(J)}), '\t'), SI.gtext(g) <> String.split(SI.gtext(J), '\t'),
          ST.split_tab(SI.gtext(g), SI.gtext(J), gok_noc(g, eg, AB.and_true_l(CH.GOK(TAB(), g), CH.GOKS(TAB(), Con{g2, t2}), hg)))) :
        {_ == TX(Con{g, Con{g2, t2}}) : Ss()}
      %Equal.sym(Ss(), B.Rec.fields(SI.gtext(J)), TX(Con{g2, t2}), join_fields(t2, g2, SI.gtext(J), eJ, AB.and_true_r(CH.GOK(TAB(), g), CH.GOKS(TAB(), Con{g2, t2}), hg))) :
        {SI.gtext(g) <> _ == TX(Con{g, Con{g2, t2}}) : Ss()}
      {==}

law len_tx:
  for +gs: Gs()
  {List.length(&2, String, TX(gs)) == List.length(&2, B.Got, gs) : Nat}

def len_tx(gs):
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, String, TX(t)), List.length(&2, B.Got, t), len_tx(t))

law len_go:
  for +fs: Ss()
  for +j: Nat
  for +a: String
  for +defs: B.Defs
  for +ks: Ss()
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  {List.length(&2, B.Got, B.Rec.piece.go(fs, j, a, defs, ks, over0, n, i)) == List.length(&2, String, fs) : Nat}

def len_go(fs, j, a, defs, ks, over0, n, i):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, B.Got, B.Rec.piece.go(t, 1n+j, a, defs, ks, over0, n, i)), List.length(&2, String, t), len_go(t, 1n+j, a, defs, ks, over0, n, i))

def and_tt(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def EQ(+x: String) -> Bool:
  String.eq(x, x)

# The seven fields kept, equal to themselves.
def sf7(+f0: String, +f1: String, +f2: String, +f3: String, +f5: String, +f6: String, +f8: String) ->
  {Bool.and(EQ(f0), Bool.and(EQ(f1), Bool.and(EQ(f2), Bool.and(EQ(f3), Bool.and(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{}))))))) == True{} : Bool}:
  and_tt(EQ(f0), Bool.and(EQ(f1), Bool.and(EQ(f2), Bool.and(EQ(f3), Bool.and(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{})))))), RB.str_eq_refl(f0),
  and_tt(EQ(f1), Bool.and(EQ(f2), Bool.and(EQ(f3), Bool.and(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{}))))), RB.str_eq_refl(f1),
  and_tt(EQ(f2), Bool.and(EQ(f3), Bool.and(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{})))), RB.str_eq_refl(f2),
  and_tt(EQ(f3), Bool.and(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{}))), RB.str_eq_refl(f3),
  and_tt(EQ(f5), Bool.and(EQ(f6), Bool.and(EQ(f8), True{})), RB.str_eq_refl(f5),
  and_tt(EQ(f6), Bool.and(EQ(f8), True{}), RB.str_eq_refl(f6),
  and_tt(EQ(f8), True{}, RB.str_eq_refl(f8), {==})))))))

def F8(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String, +r: Ss()) -> Ss():
  Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}}}

def SAMEG(+fs: Ss(), +gs: Ss()) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, String, fs), List.length(&2, String, gs)), L.same_fields(fs, gs, [0n, 1n, 2n, 3n, 5n, 6n, 8n]))

def ps.k(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String, r: Ss(),
  +a: String, +defs: B.Defs, +ks: Ss(), +over0: Bool, +n: Nat, +i: Nat) ->
  {SAMEG(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), TX(B.Rec.piece.go(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), 0n, a, defs, ks, over0, n, i))) == True{} : Bool}:
  match r:
    case Nil{}:
      and_tt(Nat.is_eq(8n, 8n), L.same_fields(F8(f0, f1, f2, f3, f4, f5, f6, f7, Nil{}), TX(B.Rec.piece.go(F8(f0, f1, f2, f3, f4, f5, f6, f7, Nil{}), 0n, a, defs, ks, over0, n, i)), [0n, 1n, 2n, 3n, 5n, 6n, 8n]), {==},
        sf7(f0, f1, f2, f3, f5, f6, ""))
    case Con{+f8, +r2}:
      +G9 = B.Rec.piece.go(r2, 9n, a, defs, ks, over0, n, i)
      +eL = Equal.trans(Nat, List.length(&2, String, TX(G9)), List.length(&2, B.Got, G9), List.length(&2, String, r2), len_tx(G9), len_go(r2, 9n, a, defs, ks, over0, n, i))
      +FS9 = F8(f0, f1, f2, f3, f4, f5, f6, f7, Con{f8, r2})
      +GS9 = TX(B.Rec.piece.go(FS9, 0n, a, defs, ks, over0, n, i))
      and_tt(Nat.is_eq(List.length(&2, String, FS9), List.length(&2, String, GS9)), L.same_fields(FS9, GS9, [0n, 1n, 2n, 3n, 5n, 6n, 8n]),
        {%Equal.sym(Nat, List.length(&2, String, TX(G9)), List.length(&2, String, r2), eL) : {Nat.is_eq(1n+1n+1n+1n+1n+1n+1n+1n+1n+List.length(&2, String, r2), 1n+1n+1n+1n+1n+1n+1n+1n+1n+_) == True{} : Bool};
         N.eq_refl(1n+1n+1n+1n+1n+1n+1n+1n+1n+List.length(&2, String, r2)) : {Nat.is_eq(List.length(&2, String, FS9), List.length(&2, String, GS9)) == True{} : Bool}},
        sf7(f0, f1, f2, f3, f5, f6, f8))

# One record keeps the site and the number of fields.
law piece_same:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +f7: String
  for +r: Ss()
  for +a: String
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +i: Nat
  for +x: String
  for +hj: {B.Rec.piece(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), a, defs, over0, n, i) == B.Got{x} : B.Got}
  for +hf: {CH.ALLS(TAB(), F8(f0, f1, f2, f3, f4, f5, f6, f7, r)) == True{} : Bool}
  for +ha: {CH.ALLC(TAB(), a) == True{} : Bool}
  {L.same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), x) == True{} : Bool}

def piece_same(f0, f1, f2, f3, f4, f5, f6, f7, r, a, defs, over0, n, i, x, hj, hf, ha):
  +ks = String.split(B.Rec.field(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), 8n), ':')
  +g = B.Rec.piece.field(0n, f0, a, defs, ks, over0, n, i)
  +t = B.Rec.piece.go(Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}}, 1n, a, defs, ks, over0, n, i)
  +E = join_fields(t, g, x, hj, CH.pgo(TAB(), F8(f0, f1, f2, f3, f4, f5, f6, f7, r), 0n, a, defs, ks, over0, n, i, hf, ha, {==}))
  %Equal.sym(Ss(), B.Rec.fields(x), TX(Con{g, t}), E) :
    {Bool.and(Nat.is_eq(List.length(&2, String, F8(f0, f1, f2, f3, f4, f5, f6, f7, r)), List.length(&2, String, _)), L.same_fields(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), _, [0n, 1n, 2n, 3n, 5n, 6n, 8n])) == True{} : Bool}
  ps.k(f0, f1, f2, f3, f4, f5, f6, f7, r, a, defs, ks, over0, n, i)

law pieces_same:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +f7: String
  for +r: Ss()
  for +defs: B.Defs
  for +over0: Bool
  for +n: Nat
  for +alts: Ss()
  for +i: Nat
  for +ps: Ss()
  for +h: {B.Parts.of(B.Rec.pieces.go(alts, F8(f0, f1, f2, f3, f4, f5, f6, f7, r), defs, over0, n, i)) == B.Pieces{ps} : B.Parts}
  for +hf: {CH.ALLS(TAB(), F8(f0, f1, f2, f3, f4, f5, f6, f7, r)) == True{} : Bool}
  for +hat: {CH.ALLS(TAB(), alts) == True{} : Bool}
  {L.all_same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), ps) == True{} : Bool}

def pieces_same(f0, f1, f2, f3, f4, f5, f6, f7, r, defs, over0, n, alts, i, ps, h, hf, hat):
  match alts:
    case Nil{}:
      %Equal.sym(Ss(), ps, Nil{}, Equal.sym(Ss(), Nil{}, ps, Equal.cong(B.Parts, Ss(), SI.pieces_of, B.Pieces{Nil{}}, B.Pieces{ps}, h))) : {L.all_same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), _) == True{} : Bool}
      {==}
    case Con{+a, +t}:
      +g = B.Rec.piece(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), a, defs, over0, n, i)
      +rr = B.Parts.of(B.Rec.pieces.go(t, F8(f0, f1, f2, f3, f4, f5, f6, f7, r), defs, over0, n, 1n+i))
      +eg = SI.pc_g(g, rr, ps, h)
      +h2g = {%eg : {B.Parts.cons(_, rr) == B.Pieces{ps} : B.Parts}; h : {B.Parts.cons(B.Got{SI.gtext(g)}, rr) == B.Pieces{ps} : B.Parts}}
      %Equal.sym(Ss(), ps, SI.gtext(g) <> SI.pieces_of(rr), SI.pc_ps(SI.gtext(g), rr, ps, h2g)) : {L.all_same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), _) == True{} : Bool}
      and_tt(L.same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), SI.gtext(g)), L.all_same_site(F8(f0, f1, f2, f3, f4, f5, f6, f7, r), SI.pieces_of(rr)),
        piece_same(f0, f1, f2, f3, f4, f5, f6, f7, r, a, defs, over0, n, i, SI.gtext(g), eg, hf, AB.and_true_l(CH.ALLC(TAB(), a), CH.ALLS(TAB(), t), hat)),
        pieces_same(f0, f1, f2, f3, f4, f5, f6, f7, r, defs, over0, n, t, 1n+i, SI.pieces_of(rr), SI.pc_r(SI.gtext(g), rr, ps, h2g), hf, AB.and_true_r(CH.ALLC(TAB(), a), CH.ALLS(TAB(), t), hat)))

def or_false_l(+a: Bool, +b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, e)))

def not_true(+b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(h))
    case False{}:
      {==}

def ss_fs(fs: Ss(), +defs: B.Defs, +o0: Bool, +ps: Ss(),
  +h: {B.Parts.of(B.Rec.pieces.go(B.Rec.alts(fs), fs, defs, o0, List.length(&2, String, B.Rec.alts(fs)), 1n)) == B.Pieces{ps} : B.Parts},
  +hf: {CH.ALLS(TAB(), fs) == True{} : Bool},
  +hl: {Nat.is_lt(List.length(&2, String, fs), 8n) == False{} : Bool}) -> {L.all_same_site(fs, ps) == True{} : Bool}:
  match fs:
    case Nil{}:
      Empty.absurd({L.all_same_site(Nil{}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Nil{}}:
      Empty.absurd({L.all_same_site(Con{f0, Nil{}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Nil{}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Con{f2, Nil{}}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Con{f2, Con{f3, Nil{}}}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Nil{}}}}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Nil{}}}}}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({L.all_same_site(Con{f0, Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Nil{}}}}}}}}, ps) == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hl)))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +r}}}}}}}}:
      +FS = F8(f0, f1, f2, f3, f4, f5, f6, f7, r)
      +a1 = AB.and_true_r(CH.ALLC(TAB(), f0), CH.ALLS(TAB(), Con{f1, Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}}), hf)
      +a2 = AB.and_true_r(CH.ALLC(TAB(), f1), CH.ALLS(TAB(), Con{f2, Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}}), a1)
      +a3 = AB.and_true_r(CH.ALLC(TAB(), f2), CH.ALLS(TAB(), Con{f3, Con{f4, Con{f5, Con{f6, Con{f7, r}}}}}), a2)
      +a4 = AB.and_true_r(CH.ALLC(TAB(), f3), CH.ALLS(TAB(), Con{f4, Con{f5, Con{f6, Con{f7, r}}}}), a3)
      +h4 = AB.and_true_l(CH.ALLC(TAB(), f4), CH.ALLS(TAB(), Con{f5, Con{f6, Con{f7, r}}}), a4)
      pieces_same(f0, f1, f2, f3, f4, f5, f6, f7, r, defs, o0, List.length(&2, String, String.split(f4, ',')), String.split(f4, ','), 1n, ps, h, hf,
        CH.split_all(TAB(), f4, ',', h4))

def ss_split(+d: Bool, +defs: B.Defs, +o0: Bool, +body: String, +ps: Ss(),
  +ed: {B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))) == d : Bool},
  +h: {B.Rec.parts.split(B.Alts.distinct(B.Rec.alts(B.Rec.fields(body))), B.Rec.alts(B.Rec.fields(body)), B.Rec.fields(body), defs, o0) == B.Pieces{ps} : B.Parts},
  +hl: {Nat.is_lt(List.length(&2, String, B.Rec.fields(body)), 8n) == False{} : Bool}) ->
  {L.all_same_site(B.Rec.fields(body), ps) == True{} : Bool}:
  match d:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(False{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.all_same_site(fs, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Unsplit{B.DupAlts{}}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +h2 = {%ed : {B.Rec.parts.split(_, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.split(True{}, B.Rec.alts(fs), fs, defs, o0) == B.Pieces{ps} : B.Parts}}
      ss_fs(fs, defs, o0, ps, h2, Equal.trans(Bool, CH.ALLS(TAB(), fs), ST.allnoc(fs, '\t'), True{}, Equal.sym(Bool, ST.allnoc(fs, '\t'), CH.ALLS(TAB(), fs), alls_noc(fs, '\t')), ST.split_all(body, '\t')), hl)

def ss_if(+c: Bool, +defs: B.Defs, +o0: Bool, +sp: Bool, +body: String, +ps: Ss(),
  +e: {SI.COND(sp, B.Rec.fields(body)) == c : Bool},
  +h: {B.Rec.parts.if(SI.COND(sp, B.Rec.fields(body)), False{}, defs, o0, B.Rec.fields(body)) == B.Pieces{ps} : B.Parts}) ->
  {L.all_same_site(B.Rec.fields(body), ps) == True{} : Bool}:
  match c:
    case False{}:
      +fs = B.Rec.fields(body)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(False{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      Empty.absurd({L.all_same_site(fs, ps) == True{} : Bool}, AB.false_ne_true(Equal.cong(B.Parts, Bool, SI.is_pieces, B.Whole{}, B.Pieces{ps}, h2)))
    case True{}:
      +fs = B.Rec.fields(body)
      +al = B.Rec.alts(fs)
      +h2 = {%e : {B.Rec.parts.if(_, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}; h : {B.Rec.parts.if(True{}, False{}, defs, o0, fs) == B.Pieces{ps} : B.Parts}}
      +M = B.Rec.malformed(fs)
      +hnm = not_true(M, AB.and_true_r(sp, Bool.not(M), AB.and_true_l(Bool.and(sp, Bool.not(M)), Nat.is_le(2n, List.length(&2, String, al)), e)))
      +L8 = Nat.is_lt(List.length(&2, String, fs), 8n)
      +B0 = String.is_empty(B.Rec.field(fs, 0n))
      +B1 = Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))
      +B3 = Bool.not(B.Text.is_letters(B.Rec.field(fs, 3n)))
      +B4 = B.Text.any_empty(B.Rec.alts(fs))
      +hl = or_false_l(L8, B0, or_false_l(Bool.or(L8, B0), B1, or_false_l(Bool.or(Bool.or(L8, B0), B1), B3, or_false_l(Bool.or(Bool.or(Bool.or(L8, B0), B1), B3), B4, hnm))))
      ss_split(B.Alts.distinct(al), defs, o0, body, ps, {==}, h2, hl)

# Law split_site: each record keeps the input's CHROM, POS, ID, REF, QUAL,
# FILTER and FORMAT, and its number of fields.
law split_site:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  {L.all_same_site(B.Rec.fields(body), ps) == True{} : Bool}

def split_site(defs, o, body, ps, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      ss_if(SI.COND(sp, B.Rec.fields(body)), defs, o0, sp, body, ps, {==}, CR.cr_h(SI.COND(sp, B.Rec.fields(body)), B.Text.has_cr(body), defs, o0, B.Rec.fields(body), ps, CR.cr_none(defs, B.Opts{st, w, sp, o0, args}, body, ps, h), h))
