import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_site.bend as SI
import ./proof_s_str.bend as ST
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_col.bend as CO
import ./proof_run_base.bend as RB
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Laws split_gt and split_phase: a genotype in the record for ALT i+1 names,
# token by token, B.Gt.rule's allele for the input's ('.', 0 or 1), with the
# input's separators. Tokens are split at either separator (TKS); the laws'
# gt_tokens (split at '/', then each piece at '|') gives the same. Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def sep(+c: Char) -> Bool:
  B.Gt.is_sep(c)

def tks.put(b: Bool, +h: Char, r: Ss()) -> Ss():
  match b:
    case True{}:
      Con{"", r}
    case False{}:
      String.split.push(h, r)

# A genotype's tokens, split at either separator.
def TKS(s: String) -> Ss():
  match s:
    case SNil{}:
      [""]
    case SCon{+h, t}:
      tks.put(sep(h), h, TKS(t))

# No separator in the text.
def NS(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.not(sep(h)) && NS(t)

# Characters put in front of the first token.
def pushs(a: String, xs: Ss()) -> Ss():
  match a:
    case SNil{}:
      xs
    case SCon{h, t}:
      String.split.push(h, pushs(t, xs))

law pushs_cons:
  for +a: String
  for +x: String
  for +xs: Ss()
  {pushs(a, Con{x, xs}) == Con{String.append(a, x), xs} : Ss()}

def pushs_cons(a, x, xs):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Ss(), pushs(t, Con{x, xs}), Con{String.append(t, x), xs}, pushs_cons(t, x, xs)) :
        {String.split.push(h, _) == Con{String.append(SCon{h, t}, x), xs} : Ss()}
      {==}

def nf(+a: Bool, +b: Bool, +h: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AB.false_ne_true(h))
    case False{}:
      {==}

def nt(+a: Bool, +b: Bool, +h: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, AB.false_ne_true(h))
    case False{}:
      h

# A text without separators in front: its characters join the first token.
law tks_app:
  for +a: String
  for +r: String
  for +hn: {NS(a) == True{} : Bool}
  {TKS(String.append(a, r)) == pushs(a, TKS(r)) : Ss()}

def tks_app(a, r, hn):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, sep(h), False{}, nf(sep(h), NS(t), hn)) : {tks.put(_, h, TKS(String.append(t, r))) == pushs(SCon{h, t}, TKS(r)) : Ss()}
      %Equal.sym(Ss(), TKS(String.append(t, r)), pushs(t, TKS(r)), tks_app(t, r, nt(sep(h), NS(t), hn))) : {String.split.push(h, _) == pushs(SCon{h, t}, TKS(r)) : Ss()}
      {==}

law seps_app:
  for +a: String
  for +r: String
  for +hn: {NS(a) == True{} : Bool}
  {L.gt_seps(String.append(a, r)) == L.gt_seps(r) : String}

def seps_app(a, r, hn):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, sep(h), False{}, nf(sep(h), NS(t), hn)) : {L.gt_seps.put(_, h, L.gt_seps(String.append(t, r))) == L.gt_seps(r) : String}
      seps_app(t, r, nt(sep(h), NS(t), hn))

law push_app:
  for +h: Char
  for +xs: Ss()
  for +ys: Ss()
  for +hc: {ST.is_cons(xs) == True{} : Bool}
  {List.append(&2, String, String.split.push(h, xs), ys) == String.split.push(h, List.append(&2, String, xs, ys)) : Ss()}

def push_app(h, xs, ys, hc):
  match xs:
    case Nil{}:
      Empty.absurd({List.append(&2, String, String.split.push(h, Nil{}), ys) == String.split.push(h, List.append(&2, String, Nil{}, ys)) : Ss()}, AB.false_ne_true(hc))
    case Con{+x, +t}:
      {==}

def GC(+ss: Ss()) -> Ss():
  L.gt_cut(ss)

def te.c(+b2: Bool, +x: U32, +t: String, +s0: String, +rest: Ss(),
  +e2: {U32.is_eq(x, 124) == b2 : Bool},
  +ih: {GC(Con{s0, rest}) == TKS(t) : Ss()}) ->
  {GC(Con{SCon{Chr{x}, s0}, rest}) == tks.put(Bool.or(False{}, b2), Chr{x}, TKS(t)) : Ss()}:
  match b2:
    case True{}:
      +S0 = String.split(s0, '|')
      +GR = GC(rest)
      %Equal.sym(Bool, U32.is_eq(x, 124), True{}, e2) : {List.append(&2, String, String.split.fin(Chr{x}, S0, _), GR) == Con{"", TKS(t)} : Ss()}
      Equal.cong(Ss(), Ss(), z => Con{"", z}, GC(Con{s0, rest}), TKS(t), ih)
    case False{}:
      +S0 = String.split(s0, '|')
      +GR = GC(rest)
      %Equal.sym(Bool, U32.is_eq(x, 124), False{}, e2) : {List.append(&2, String, String.split.fin(Chr{x}, S0, _), GR) == String.split.push(Chr{x}, TKS(t)) : Ss()}
      Equal.trans(Ss(), List.append(&2, String, String.split.push(Chr{x}, S0), GR), String.split.push(Chr{x}, GC(Con{s0, rest})), String.split.push(Chr{x}, TKS(t)),
        push_app(Chr{x}, S0, GR, ST.split_cons(s0, '|')),
        Equal.cong(Ss(), Ss(), z => String.split.push(Chr{x}, z), GC(Con{s0, rest}), TKS(t), ih))

def te.b(ss: Ss(), +b2: Bool, +x: U32, +t: String,
  +es: {String.split(t, '/') == ss : Ss()},
  +e2: {U32.is_eq(x, 124) == b2 : Bool},
  +ih: {GC(String.split(t, '/')) == TKS(t) : Ss()}) ->
  {GC(String.split.push(Chr{x}, ss)) == tks.put(Bool.or(False{}, b2), Chr{x}, TKS(t)) : Ss()}:
  match ss:
    case Nil{}:
      +hc = {%es : {ST.is_cons(_) == True{} : Bool}; ST.split_cons(t, '/') : {ST.is_cons(Nil{}) == True{} : Bool}}
      Empty.absurd({GC(String.split.push(Chr{x}, Nil{})) == tks.put(Bool.or(False{}, b2), Chr{x}, TKS(t)) : Ss()}, AB.false_ne_true(hc))
    case Con{+s0, +rest}:
      te.c(b2, x, t, s0, rest, e2, {%es : {GC(_) == TKS(t) : Ss()}; ih : {GC(Con{s0, rest}) == TKS(t) : Ss()}})

def te.a(+b1: Bool, +b2: Bool, +x: U32, +t: String,
  +e1: {U32.is_eq(x, 47) == b1 : Bool},
  +e2: {U32.is_eq(x, 124) == b2 : Bool},
  +ih: {GC(String.split(t, '/')) == TKS(t) : Ss()}) ->
  {GC(String.split.fin(Chr{x}, String.split(t, '/'), b1)) == tks.put(Bool.or(b1, b2), Chr{x}, TKS(t)) : Ss()}:
  match b1:
    case True{}:
      Equal.cong(Ss(), Ss(), z => Con{"", z}, GC(String.split(t, '/')), TKS(t), ih)
    case False{}:
      te.b(String.split(t, '/'), b2, x, t, {==}, e2, ih)

# The laws' tokens (split at '/', then at '|') are TKS.
law tk_eq:
  for +g: String
  {L.gt_tokens(g) == TKS(g) : Ss()}

def tk_eq(g):
  match g:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      match h:
        case Chr{+x}:
          te.a(U32.is_eq(x, 47), U32.is_eq(x, 124), x, t, {==}, {==}, tk_eq(t))

# ---------------------------------------------------------------------------
# One token
# ---------------------------------------------------------------------------

def AL(+o0: Bool, +n: Nat, +i: Nat, +t: String) -> B.Got:
  B.Gt.allele(o0, n, i, t)

def OUT(+o0: Bool, +n: Nat, +i: Nat, +t: String) -> String:
  SI.gtext(AL(o0, n, i, t))

def gok(+x: String) -> Bool:
  String.eq(x, ".") || B.Gt.canon(x)

def RL(+r: Maybe<&2, Nat>) -> Type:
  {L.gt_read(B.Gt.show(r)) == r : Maybe<&2, Nat>} & ({gok(B.Gt.show(r)) == True{} : Bool} & {NS(B.Gt.show(r)) == True{} : Bool})

def PK(+b1: Bool, +b2: Bool, +b3: Bool) -> Maybe<&2, Nat>:
  Bool.pick(Maybe<&2, Nat>, b1, Some{0n}, Bool.pick(Maybe<&2, Nat>, b2, Some{1n}, Bool.pick(Maybe<&2, Nat>, b3, Some{0n}, None{})))

# The rule's alleles: 0, 1 or missing; written "0", "1", ".".
def gl(+b1: Bool, +b2: Bool, +b3: Bool) -> RL(PK(b1, b2, b3)):
  match b1 b2 b3:
    case True{} _ _:
      ({==}, ({==}, {==}))
    case False{} True{} _:
      ({==}, ({==}, {==}))
    case False{} False{} True{}:
      ({==}, ({==}, {==}))
    case False{} False{} False{}:
      ({==}, ({==}, {==}))

def TOK(+o0: Bool, +n: Nat, +i: Nat, +t: String) -> Type:
  {L.gt_read(OUT(o0, n, i, t)) == B.Gt.rule(o0, i, L.gt_read(t)) : Maybe<&2, Nat>}
  & ({gok(OUT(o0, n, i, t)) == True{} : Bool} & {NS(OUT(o0, n, i, t)) == True{} : Bool})

def ALN(+o0: Bool, +n: Nat, +i: Nat, +b: Bool, +a: Nat) -> B.Got:
  Bool.pick(B.Got, b, B.Got{B.Gt.show(B.Gt.rule(o0, i, Some{a}))}, B.Refuse{B.BadGt{}})

def ALK(+o0: Bool, +n: Nat, +i: Nat, +c1: Bool, +c2: Bool, +m: Maybe<&2, Nat>) -> B.Got:
  Bool.pick(B.Got, c1, B.Got{"."}, Bool.pick(B.Got, c2, B.Gt.num(m, o0, n, i), B.Refuse{B.BadGt{}}))

def TOKK(+o0: Bool, +n: Nat, +i: Nat, +c1: Bool, +c2: Bool, +m: Maybe<&2, Nat>) -> Type:
  {L.gt_read(SI.gtext(ALK(o0, n, i, c1, c2, m))) == B.Gt.rule(o0, i, Bool.pick(Maybe<&2, Nat>, c1, None{}, m)) : Maybe<&2, Nat>}
  & ({gok(SI.gtext(ALK(o0, n, i, c1, c2, m))) == True{} : Bool} & {NS(SI.gtext(ALK(o0, n, i, c1, c2, m))) == True{} : Bool})

def tok.s(+o0: Bool, +n: Nat, +i: Nat, +b: Bool, +a: Nat,
  +hg: {ALN(o0, n, i, b, a) == B.Got{SI.gtext(ALN(o0, n, i, b, a))} : B.Got}) ->
  {L.gt_read(SI.gtext(ALN(o0, n, i, b, a))) == B.Gt.rule(o0, i, Some{a}) : Maybe<&2, Nat>}
  & ({gok(SI.gtext(ALN(o0, n, i, b, a))) == True{} : Bool} & {NS(SI.gtext(ALN(o0, n, i, b, a))) == True{} : Bool}):
  match b:
    case True{}:
      gl(Nat.is_eq(a, 0n), Nat.is_eq(a, i), o0)
    case False{}:
      Empty.absurd({L.gt_read("") == B.Gt.rule(o0, i, Some{a}) : Maybe<&2, Nat>} & ({gok("") == True{} : Bool} & {NS("") == True{} : Bool}), CO.ref_ne(B.BadGt{}, "", hg))

def tok.m(+o0: Bool, +n: Nat, +i: Nat, +m: Maybe<&2, Nat>,
  +hg: {B.Gt.num(m, o0, n, i) == B.Got{SI.gtext(B.Gt.num(m, o0, n, i))} : B.Got}) -> TOKK(o0, n, i, False{}, True{}, m):
  match m:
    case None{}:
      Empty.absurd(TOKK(o0, n, i, False{}, True{}, None{}), CO.ref_ne(B.BadGt{}, "", hg))
    case Some{+a}:
      tok.s(o0, n, i, Nat.is_le(a, n), a, hg)

def tok.k(+o0: Bool, +n: Nat, +i: Nat, +c1: Bool, +c2: Bool, +m: Maybe<&2, Nat>,
  +hg: {ALK(o0, n, i, c1, c2, m) == B.Got{SI.gtext(ALK(o0, n, i, c1, c2, m))} : B.Got}) -> TOKK(o0, n, i, c1, c2, m):
  match c1 c2:
    case True{} _:
      ({==}, ({==}, {==}))
    case False{} True{}:
      tok.m(o0, n, i, m, hg)
    case False{} False{}:
      Empty.absurd(TOKK(o0, n, i, False{}, False{}, m), CO.ref_ne(B.BadGt{}, "", hg))

# One token of a genotype, accepted: its allele read back is the rule's, it
# is well written ('.', 0 or 1), and holds no separator.
def tok(+o0: Bool, +n: Nat, +i: Nat, +t: String,
  +hg: {AL(o0, n, i, t) == B.Got{OUT(o0, n, i, t)} : B.Got}) -> TOK(o0, n, i, t):
  tok.k(o0, n, i, String.eq(t, "."), B.Gt.canon(t), B.Pos.read(t), hg)

# ---------------------------------------------------------------------------
# A genotype, read from the right (B.Gt.go)
# ---------------------------------------------------------------------------

def tl(xs: Ss()) -> Ss():
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def TL(+g: String) -> Ss():
  tl(TKS(g))

def MO(+o0: Bool, +n: Nat, +i: Nat, ts: Ss()) -> Ss():
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, r}:
      OUT(o0, n, i, t) <> MO(o0, n, i, r)

def AG(+o0: Bool, +n: Nat, +i: Nat, ts: Ss()) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{+t, r}:
      SM.is_got(AL(o0, n, i, t)) && AG(o0, n, i, r)

# What B.Gt.go gives for g: the first token (no separator), and, when the
# rest is a text, that rest's tokens are an empty one then the later
# tokens' alleles; its separators are g's; those alleles are texts.
def GQT(+o0: Bool, +n: Nat, +i: Nat, +tks: Ss(), +sps: String, +tk: String, +rs: B.Got) -> Type:
  {rs == B.Got{SI.gtext(rs)} : B.Got} ->
    ({tks == Con{tk, tl(tks)} : Ss()}
    & ({TKS(SI.gtext(rs)) == Con{"", MO(o0, n, i, tl(tks))} : Ss()}
    & ({L.gt_seps(SI.gtext(rs)) == sps : String}
    & ({NS(tk) == True{} : Bool} & {AG(o0, n, i, tl(tks)) == True{} : Bool}))))

def GQ(+o0: Bool, +n: Nat, +i: Nat, +g: String, r: B.Gp) -> Type:
  match r:
    case B.Gp{+tk, +rs}:
      GQT(o0, n, i, TKS(g), L.gt_seps(g), tk, rs)

def QR(+o0: Bool, +n: Nat, +i: Nat, +tks: Ss(), +sps: String, +tk: String, +rs: B.Got) -> Type:
  {tks == Con{tk, tl(tks)} : Ss()}
  & ({TKS(SI.gtext(rs)) == Con{"", MO(o0, n, i, tl(tks))} : Ss()}
  & ({L.gt_seps(SI.gtext(rs)) == sps : String}
  & ({NS(tk) == True{} : Bool} & {AG(o0, n, i, tl(tks)) == True{} : Bool})))

# A character not a separator: it joins the first token.
def gq.f(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got,
  +eb: {sep(c) == False{} : Bool},
  q: QR(o0, n, i, TKS(t), L.gt_seps(t), tk, rs)) -> QR(o0, n, i, String.split.push(c, TKS(t)), L.gt_seps(t), SCon{c, tk}, rs):
  match q:
    case (e1, q1):
      match q1:
        case (e2, q2):
          match q2:
            case (e3, q3):
              match q3:
                case (e4, e5):
                  +T0 = TKS(t)
                  +TT = tl(TKS(t))
                  +sy = Equal.sym(Ss(), T0, Con{tk, TT}, e1)
                  ({%sy : {String.split.push(c, _) == Con{SCon{c, tk}, tl(String.split.push(c, _))} : Ss()}; {==} : {String.split.push(c, T0) == Con{SCon{c, tk}, tl(String.split.push(c, T0))} : Ss()}},
                   ({%sy : {TKS(SI.gtext(rs)) == Con{"", MO(o0, n, i, tl(String.split.push(c, _)))} : Ss()}; e2 : {TKS(SI.gtext(rs)) == Con{"", MO(o0, n, i, tl(String.split.push(c, T0)))} : Ss()}},
                    (e3,
                     ({%Equal.sym(Bool, sep(c), False{}, eb) : {Bool.and(Bool.not(_), NS(tk)) == True{} : Bool}; e4 : {NS(SCon{c, tk}) == True{} : Bool}},
                      {%sy : {AG(o0, n, i, tl(String.split.push(c, _))) == True{} : Bool}; e5 : {AG(o0, n, i, tl(String.split.push(c, T0))) == True{} : Bool}}))))

def RSP(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +tk: String, +rs: B.Got) -> B.Got:
  B.Got.cat(B.Got.cat(B.Got{SCon{c, SNil{}}}, "", AL(o0, n, i, tk)), "", rs)

def tok_ns(+o0: Bool, +n: Nat, +i: Nat, +tk: String, w: TOK(o0, n, i, tk)) -> {NS(OUT(o0, n, i, tk)) == True{} : Bool}:
  match w:
    case (r1, ww):
      match ww:
        case (r2, r3):
          r3

def gq.t3(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got,
  +eb: {sep(c) == True{} : Bool},
  +eA: {AL(o0, n, i, tk) == B.Got{OUT(o0, n, i, tk)} : B.Got},
  +eRS: {SI.gtext(RSP(o0, n, i, c, tk, rs)) == SCon{c, String.append(OUT(o0, n, i, tk), SI.gtext(rs))} : String},
  q: QR(o0, n, i, TKS(t), L.gt_seps(t), tk, rs), +r3: {NS(OUT(o0, n, i, tk)) == True{} : Bool}) ->
  QR(o0, n, i, Con{"", TKS(t)}, SCon{c, L.gt_seps(t)}, "", RSP(o0, n, i, c, tk, rs)):
  match q:
    case (e1, q1):
      match q1:
        case (e2, q2):
          match q2:
            case (e3, q3):
              match q3:
                case (e4, e5):
                          +O = OUT(o0, n, i, tk)
                          +Rt = SI.gtext(rs)
                          +TT = tl(TKS(t))
                          +M = MO(o0, n, i, TT)
                          +X = String.append(O, Rt)
                          +e1s = e1
                          +t2 = Equal.trans(Ss(), TKS(SI.gtext(RSP(o0, n, i, c, tk, rs))), TKS(SCon{c, X}), Con{"", Con{O, M}},
                            Equal.cong(String, Ss(), z => TKS(z), SI.gtext(RSP(o0, n, i, c, tk, rs)), SCon{c, X}, eRS),
                            Equal.trans(Ss(), TKS(SCon{c, X}), Con{"", TKS(X)}, Con{"", Con{O, M}},
                              Equal.cong(Bool, Ss(), z => tks.put(z, c, TKS(X)), sep(c), True{}, eb),
                              Equal.trans(Ss(), Con{"", TKS(X)}, Con{"", pushs(O, TKS(Rt))}, Con{"", Con{O, M}},
                                Equal.cong(Ss(), Ss(), z => Con{"", z}, TKS(X), pushs(O, TKS(Rt)), tks_app(O, Rt, r3)),
                                Equal.trans(Ss(), Con{"", pushs(O, TKS(Rt))}, Con{"", pushs(O, Con{"", M})}, Con{"", Con{O, M}},
                                  Equal.cong(Ss(), Ss(), z => Con{"", pushs(O, z)}, TKS(Rt), Con{"", M}, e2),
                                  Equal.trans(Ss(), Con{"", pushs(O, Con{"", M})}, Con{"", Con{String.append(O, ""), M}}, Con{"", Con{O, M}},
                                    Equal.cong(Ss(), Ss(), z => Con{"", z}, pushs(O, Con{"", M}), Con{String.append(O, ""), M}, pushs_cons(O, "", M)),
                                    Equal.cong(String, Ss(), z => Con{"", Con{z, M}}, String.append(O, ""), O, ST.sapp_nil(O)))))))
                          +t7 = Equal.cong(Ss(), Ss(), z => Con{"", MO(o0, n, i, z)}, TKS(t), Con{tk, TT}, e1s)
                          +s3 = Equal.trans(String, L.gt_seps(SI.gtext(RSP(o0, n, i, c, tk, rs))), L.gt_seps(SCon{c, X}), SCon{c, L.gt_seps(t)},
                            Equal.cong(String, String, z => L.gt_seps(z), SI.gtext(RSP(o0, n, i, c, tk, rs)), SCon{c, X}, eRS),
                            Equal.trans(String, L.gt_seps(SCon{c, X}), SCon{c, L.gt_seps(X)}, SCon{c, L.gt_seps(t)},
                              Equal.cong(Bool, String, z => L.gt_seps.put(z, c, L.gt_seps(X)), sep(c), True{}, eb),
                              Equal.cong(String, String, z => SCon{c, z}, L.gt_seps(X), L.gt_seps(t), Equal.trans(String, L.gt_seps(X), L.gt_seps(Rt), L.gt_seps(t), seps_app(O, Rt, r3), e3))))
                          ({==},
                           (Equal.trans(Ss(), TKS(SI.gtext(RSP(o0, n, i, c, tk, rs))), Con{"", Con{O, M}}, Con{"", MO(o0, n, i, TKS(t))}, t2, Equal.sym(Ss(), Con{"", MO(o0, n, i, TKS(t))}, Con{"", Con{O, M}}, t7)),
                            (s3,
                             ({==},
                              {%Equal.sym(Ss(), TKS(t), Con{tk, TT}, e1s) : {AG(o0, n, i, _) == True{} : Bool};
                               SM.and_tt(SM.is_got(AL(o0, n, i, tk)), AG(o0, n, i, TT), Equal.cong(B.Got, Bool, SM.is_got, AL(o0, n, i, tk), B.Got{O}, eA), e5) :
                               {AG(o0, n, i, tl(Con{"", TKS(t)})) == True{} : Bool}}))))

def gq.t2(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got,
  +eb: {sep(c) == True{} : Bool},
  +h: {RSP(o0, n, i, c, tk, rs) == B.Got{SI.gtext(RSP(o0, n, i, c, tk, rs))} : B.Got},
  ih: GQT(o0, n, i, TKS(t), L.gt_seps(t), tk, rs)) -> QR(o0, n, i, Con{"", TKS(t)}, SCon{c, L.gt_seps(t)}, "", RSP(o0, n, i, c, tk, rs)):
  +W = SI.gtext(RSP(o0, n, i, c, tk, rs))
  +A = AL(o0, n, i, tk)
  +X = B.Got.cat(B.Got{SCon{c, SNil{}}}, "", A)
  +eX = AT.cat_l(X, "", rs, W, h)
  +h2 = AB.subst(B.Got, z => {B.Got.cat(z, "", rs) == B.Got{W} : B.Got}, X, B.Got{SI.gtext(X)}, eX, h)
  +ers = AT.cat_r(SI.gtext(X), "", rs, W, h2)
  +ey = AT.cat_y(SI.gtext(X), "", rs, W, h2)
  +eA = AT.cat_r(SCon{c, SNil{}}, "", A, SI.gtext(X), eX)
  +eyX = AT.cat_y(SCon{c, SNil{}}, "", A, SI.gtext(X), eX)
  +eRS = Equal.trans(String, W, String.append(SI.gtext(X), SI.gtext(rs)), SCon{c, String.append(OUT(o0, n, i, tk), SI.gtext(rs))}, ey,
    Equal.cong(String, String, z => String.append(z, SI.gtext(rs)), SI.gtext(X), SCon{c, OUT(o0, n, i, tk)}, eyX))
  gq.t3(o0, n, i, c, t, tk, rs, eb, eA, eRS, ih(ers), tok_ns(o0, n, i, tk, tok(o0, n, i, tk, eA)))

def gq.t(+o0: Bool, +n: Nat, +i: Nat, +c: Char, +t: String, +tk: String, +rs: B.Got,
  +eb: {sep(c) == True{} : Bool},
  ih: GQT(o0, n, i, TKS(t), L.gt_seps(t), tk, rs)) -> GQT(o0, n, i, Con{"", TKS(t)}, SCon{c, L.gt_seps(t)}, "", RSP(o0, n, i, c, tk, rs)):
  h => gq.t2(o0, n, i, c, t, tk, rs, eb, h, ih)

def gq.k(+o0: Bool, +n: Nat, +i: Nat, +b: Bool, +c: Char, +t: String, r: B.Gp,
  +eb: {sep(c) == b : Bool},
  ih: GQ(o0, n, i, t, r)) -> GQ(o0, n, i, SCon{c, t}, B.Gt.go.put(b, c, r, o0, n, i)):
  match b r:
    case True{} B.Gp{+tk, +rs}:
      %Equal.sym(Bool, sep(c), True{}, eb) : GQT(o0, n, i, tks.put(_, c, TKS(t)), L.gt_seps.put(_, c, L.gt_seps(t)), "", RSP(o0, n, i, c, tk, rs))
      gq.t(o0, n, i, c, t, tk, rs, eb, ih)
    case False{} B.Gp{+tk, +rs}:
      %Equal.sym(Bool, sep(c), False{}, eb) : GQT(o0, n, i, tks.put(_, c, TKS(t)), L.gt_seps.put(_, c, L.gt_seps(t)), SCon{c, tk}, rs)
      hr => gq.f(o0, n, i, c, t, tk, rs, eb, ih(hr))

# B.Gt.go's invariant (QR, when the rest is a text).
law gq:
  for +g: String
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  GQ(o0, n, i, g, B.Gt.go(g, o0, n, i))

def gq(g, o0, n, i):
  match g:
    case SNil{}:
      hr => ({==}, ({==}, ({==}, ({==}, {==}))))
    case SCon{+c, +t}:
      gq.k(o0, n, i, sep(c), c, t, B.Gt.go(t, o0, n, i), {==}, gq(t, o0, n, i))

# ---------------------------------------------------------------------------
# A genotype split for one ALT
# ---------------------------------------------------------------------------

def got_is(+g: B.Got, +h: {SM.is_got(g) == True{} : Bool}) -> {g == B.Got{SI.gtext(g)} : B.Got}:
  match g:
    case B.Got{+x}:
      {==}
    case B.Refuse{+c}:
      Empty.absurd({B.Refuse{c} == B.Got{""} : B.Got}, AB.false_ne_true(h))

def GSP(+o0: Bool, +n: Nat, +i: Nat, +g: String) -> B.Got:
  B.Gt.split(o0, n, i, g)

def GWT(+o0: Bool, +n: Nat, +i: Nat, +g: String, +w: String) -> Type:
  {TKS(w) == MO(o0, n, i, TKS(g)) : Ss()} & ({AG(o0, n, i, TKS(g)) == True{} : Bool} & {L.gt_seps(w) == L.gt_seps(g) : String})

def gw.q(+o0: Bool, +n: Nat, +i: Nat, +g: String, +tk: String, +rs: B.Got,
  +eA: {AL(o0, n, i, tk) == B.Got{OUT(o0, n, i, tk)} : B.Got},
  +hn: {NS(OUT(o0, n, i, tk)) == True{} : Bool},
  q: QR(o0, n, i, TKS(g), L.gt_seps(g), tk, rs)) -> GWT(o0, n, i, g, String.append(OUT(o0, n, i, tk), SI.gtext(rs))):
  match q:
    case (e1, q1):
      match q1:
        case (e2, q2):
          match q2:
            case (e3, q3):
              match q3:
                case (e4, e5):
                  +O = OUT(o0, n, i, tk)
                  +Rt = SI.gtext(rs)
                  +TT = tl(TKS(g))
                  +M = MO(o0, n, i, TT)
                  +e1s = e1
                  (Equal.trans(Ss(), TKS(String.append(O, Rt)), pushs(O, TKS(Rt)), MO(o0, n, i, TKS(g)), tks_app(O, Rt, hn),
                     Equal.trans(Ss(), pushs(O, TKS(Rt)), pushs(O, Con{"", M}), MO(o0, n, i, TKS(g)), Equal.cong(Ss(), Ss(), z => pushs(O, z), TKS(Rt), Con{"", M}, e2),
                       Equal.trans(Ss(), pushs(O, Con{"", M}), Con{String.append(O, ""), M}, MO(o0, n, i, TKS(g)), pushs_cons(O, "", M),
                         Equal.trans(Ss(), Con{String.append(O, ""), M}, Con{O, M}, MO(o0, n, i, TKS(g)), Equal.cong(String, Ss(), z => Con{z, M}, String.append(O, ""), O, ST.sapp_nil(O)),
                           Equal.sym(Ss(), MO(o0, n, i, TKS(g)), Con{O, M}, Equal.cong(Ss(), Ss(), z => MO(o0, n, i, z), TKS(g), Con{tk, TT}, e1s)))))),
                   ({%Equal.sym(Ss(), TKS(g), Con{tk, TT}, e1s) : {AG(o0, n, i, _) == True{} : Bool};
                     SM.and_tt(SM.is_got(AL(o0, n, i, tk)), AG(o0, n, i, TT), Equal.cong(B.Got, Bool, SM.is_got, AL(o0, n, i, tk), B.Got{O}, eA), e5) : {AG(o0, n, i, TKS(g)) == True{} : Bool}},
                    Equal.trans(String, L.gt_seps(String.append(O, Rt)), L.gt_seps(Rt), L.gt_seps(g), seps_app(O, Rt, hn), e3)))

def gw.k(+o0: Bool, +n: Nat, +i: Nat, +g: String, r: B.Gp,
  +h: {B.Gt.split.of(r, o0, n, i) == B.Got{SI.gtext(B.Gt.split.of(r, o0, n, i))} : B.Got},
  q: GQ(o0, n, i, g, r)) -> GWT(o0, n, i, g, SI.gtext(B.Gt.split.of(r, o0, n, i))):
  match r:
    case B.Gp{+tk, +rs}:
      +A = AL(o0, n, i, tk)
      +W = SI.gtext(B.Got.cat(A, "", rs))
      +eA = AT.cat_l(A, "", rs, W, h)
      +h2 = AB.subst(B.Got, z => {B.Got.cat(z, "", rs) == B.Got{W} : B.Got}, A, B.Got{SI.gtext(A)}, eA, h)
      +ers = AT.cat_r(SI.gtext(A), "", rs, W, h2)
      +ey = AT.cat_y(SI.gtext(A), "", rs, W, h2)
      {%Equal.sym(String, W, String.append(SI.gtext(A), SI.gtext(rs)), ey) : GWT(o0, n, i, g, _);
       gw.q(o0, n, i, g, tk, rs, eA, tok_ns(o0, n, i, tk, tok(o0, n, i, tk, eA)), q(ers)) : GWT(o0, n, i, g, W)}

# A genotype split for ALT i: its tokens are the alleles of g's tokens (all
# texts), and its separators are g's.
law gw:
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +g: String
  for +h: {GSP(o0, n, i, g) == B.Got{SI.gtext(GSP(o0, n, i, g))} : B.Got}
  GWT(o0, n, i, g, SI.gtext(GSP(o0, n, i, g)))

def gw(o0, n, i, g, h):
  gw.k(o0, n, i, g, B.Gt.go(g, o0, n, i), h, gq(g, o0, n, i))

def tok_r1(+o0: Bool, +n: Nat, +i: Nat, +t: String, w: TOK(o0, n, i, t)) -> {L.gt_read(OUT(o0, n, i, t)) == B.Gt.rule(o0, i, L.gt_read(t)) : Maybe<&2, Nat>}:
  match w:
    case (r1, ww):
      r1

def tok_r2(+o0: Bool, +n: Nat, +i: Nat, +t: String, w: TOK(o0, n, i, t)) -> {gok(OUT(o0, n, i, t)) == True{} : Bool}:
  match w:
    case (r1, ww):
      match ww:
        case (r2, r3):
          r2

law am:
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +ts: Ss()
  for +hag: {AG(o0, n, i, ts) == True{} : Bool}
  {L.gt_alleles.go(MO(o0, n, i, ts)) == L.gt_rule_all(o0, i, L.gt_alleles.go(ts)) : List<&2, Maybe<&2, Nat>>}

def am(o0, n, i, ts, hag):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      +eA = got_is(AL(o0, n, i, t), AB.and_true_l(SM.is_got(AL(o0, n, i, t)), AG(o0, n, i, r), hag))
      +e1 = tok_r1(o0, n, i, t, tok(o0, n, i, t, eA))
      %Equal.sym(Maybe<&2, Nat>, L.gt_read(OUT(o0, n, i, t)), B.Gt.rule(o0, i, L.gt_read(t)), e1) : {_ <> L.gt_alleles.go(MO(o0, n, i, r)) == B.Gt.rule(o0, i, L.gt_read(t)) <> L.gt_rule_all(o0, i, L.gt_alleles.go(r)) : List<&2, Maybe<&2, Nat>>}
      Equal.cong(List<&2, Maybe<&2, Nat>>, List<&2, Maybe<&2, Nat>>, z => B.Gt.rule(o0, i, L.gt_read(t)) <> z, L.gt_alleles.go(MO(o0, n, i, r)), L.gt_rule_all(o0, i, L.gt_alleles.go(r)),
        am(o0, n, i, r, AB.and_true_r(SM.is_got(AL(o0, n, i, t)), AG(o0, n, i, r), hag)))

law wm:
  for +o0: Bool
  for +n: Nat
  for +i: Nat
  for +ts: Ss()
  for +hag: {AG(o0, n, i, ts) == True{} : Bool}
  {L.gt_well.go(MO(o0, n, i, ts)) == True{} : Bool}

def wm(o0, n, i, ts, hag):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      +eA = got_is(AL(o0, n, i, t), AB.and_true_l(SM.is_got(AL(o0, n, i, t)), AG(o0, n, i, r), hag))
      SM.and_tt(gok(OUT(o0, n, i, t)), L.gt_well.go(MO(o0, n, i, r)), tok_r2(o0, n, i, t, tok(o0, n, i, t, eA)),
        wm(o0, n, i, r, AB.and_true_r(SM.is_got(AL(o0, n, i, t)), AG(o0, n, i, r), hag)))

def gt_k(+o0: Bool, +n: Nat, +i: Nat, +g: String, +w: String, q: GWT(o0, n, i, g, w)) ->
  {L.gt_view(Some{w}) == Some{L.gt_rule_all(o0, i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}:
  match q:
    case (eT, q1):
      match q1:
        case (eG, eS):
          +eG2 = eG
          +eT2 = eT
          +tw = Equal.trans(Ss(), L.gt_tokens(w), TKS(w), MO(o0, n, i, TKS(g)), tk_eq(w), eT2)
          +hw = {%Equal.sym(Ss(), L.gt_tokens(w), MO(o0, n, i, TKS(g)), tw) : {L.gt_well.go(_) == True{} : Bool}; wm(o0, n, i, TKS(g), eG2) : {L.gt_well(w) == True{} : Bool}}
          {%Equal.sym(Bool, L.gt_well(w), True{}, hw) : {L.gt_view.if(_, w) == Some{L.gt_rule_all(o0, i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>};
           %Equal.sym(Ss(), L.gt_tokens(w), MO(o0, n, i, TKS(g)), tw) : {Some{L.gt_alleles.go(_)} == Some{L.gt_rule_all(o0, i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>};
           %Equal.sym(Ss(), L.gt_tokens(g), TKS(g), tk_eq(g)) : {Some{L.gt_alleles.go(MO(o0, n, i, TKS(g)))} == Some{L.gt_rule_all(o0, i, L.gt_alleles.go(_))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>};
           Equal.cong(List<&2, Maybe<&2, Nat>>, Maybe<&2, List<&2, Maybe<&2, Nat>>>, z => Some{z}, L.gt_alleles.go(MO(o0, n, i, TKS(g))), L.gt_rule_all(o0, i, L.gt_alleles.go(TKS(g))), am(o0, n, i, TKS(g), eG2)) :
           {L.gt_view(Some{w}) == Some{L.gt_rule_all(o0, i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}}

def gt_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +g: String,
  r: CO.VA(defs, o0, body, i, p, s, j, "GT", g)) ->
  {L.gt_view(L.sample_at(p, s, j)) == Some{L.gt_rule_all(o0, 1n+i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}:
  match r:
    case (+col, q):
      match q:
        case (em, q2):
          match q2:
            case (eO, ea):
              +w = SI.gtext(CO.ONE(defs, o0, body, i, col, "GT", g))
              {%Equal.sym(Maybe<&2, String>, L.sample_at(p, s, j), Some{w}, ea) : {L.gt_view(_) == Some{L.gt_rule_all(o0, 1n+i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>};
               gt_k(o0, L.n_alts(body), 1n+i, g, w, gw(o0, L.n_alts(body), 1n+i, g, eO)) :
               {L.gt_view(L.sample_at(p, s, j)) == Some{L.gt_rule_all(o0, 1n+i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}}

# Law split_gt: in the record for ALT i+1, every GT value of every sample is
# well written and names, copy by copy, B.Gt.rule's allele for the input's.
law split_gt:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +j: Nat
  for +hk: {List.get(&2, String, L.format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
  for +g: String
  for +hg: {L.sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
  {L.gt_view(L.sample_at(p, s, j)) == Some{L.gt_rule_all(R.Opts.over0(o), 1n+i, L.gt_alleles(g))} : Maybe<&2, List<&2, Maybe<&2, Nat>>>}

def split_gt(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg):
  gt_at(defs, R.Opts.over0(o), body, i, p, s, j, g, CO.val_at(defs, o, body, ps, h, i, p, hp, s, j, "GT", hk, g, hg))

def ph_k(+o0: Bool, +n: Nat, +i: Nat, +g: String, +w: String, q: GWT(o0, n, i, g, w)) -> {L.seps_of(Some{w}) == Some{L.gt_seps(g)} : Maybe<&2, String>}:
  match q:
    case (eT, q1):
      match q1:
        case (eG, eS):
          Equal.cong(String, Maybe<&2, String>, z => Some{z}, L.gt_seps(w), L.gt_seps(g), eS)

def ph_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +g: String,
  r: CO.VA(defs, o0, body, i, p, s, j, "GT", g)) -> {L.seps_of(L.sample_at(p, s, j)) == Some{L.gt_seps(g)} : Maybe<&2, String>}:
  match r:
    case (+col, q):
      match q:
        case (em, q2):
          match q2:
            case (eO, ea):
              +w = SI.gtext(CO.ONE(defs, o0, body, i, col, "GT", g))
              {%Equal.sym(Maybe<&2, String>, L.sample_at(p, s, j), Some{w}, ea) : {L.seps_of(_) == Some{L.gt_seps(g)} : Maybe<&2, String>};
               ph_k(o0, L.n_alts(body), 1n+i, g, w, gw(o0, L.n_alts(body), 1n+i, g, eO)) : {L.seps_of(L.sample_at(p, s, j)) == Some{L.gt_seps(g)} : Maybe<&2, String>}}

# Law split_phase: ... and keeps the input's separators, so its phasing and
# ploidy.
law split_phase:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +j: Nat
  for +hk: {List.get(&2, String, L.format_keys(body), j) == Some{"GT"} : Maybe<&2, String>}
  for +g: String
  for +hg: {L.sample_at(body, s, j) == Some{g} : Maybe<&2, String>}
  {L.seps_of(L.sample_at(p, s, j)) == Some{L.gt_seps(g)} : Maybe<&2, String>}

def split_phase(defs, o, body, ps, h, i, p, hp, s, j, hk, g, hg):
  ph_at(defs, R.Opts.over0(o), body, i, p, s, j, g, CO.val_at(defs, o, body, ps, h, i, p, hp, s, j, "GT", hk, g, hg))
