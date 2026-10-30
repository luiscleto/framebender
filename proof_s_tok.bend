import Base
import ./types.bend as B
import ./norm_split.bend as NS
import ./norm_run.bend as NR
import ./proof_base.bend as P
import ./proof_machine_nat.bend as MN
import ./proof_s_gtspec.bend as G
import ./proof_s_read.bend as RD
import lawful-fields@0.1.0.0/defs.bend as FD
import lawful-fields@0.1.0.0/proof_num.bend as LN
import lawful-fields@0.1.0.0/proof_digits.bend as LDG
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# One allele of a genotype: what norm_split.bend writes for it (rule) is
# what B.Gt.allele gives, as text. Every variable is reusable.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def L32() -> Data:
  List<&2, U32>

# ---------------------------------------------------------------------------
# The allele written
# ---------------------------------------------------------------------------

def rs.k(+b1: Bool, +b2: Bool, +o: Bool) ->
  {NR.chars([Bool.pick(U32, b1, 48, Bool.pick(U32, b2, 49, Bool.pick(U32, o, 48, 46)))]) ==
    B.Gt.show(Bool.pick(Maybe<&2, Nat>, b1, Some{0n}, Bool.pick(Maybe<&2, Nat>, b2, Some{1n}, Bool.pick(Maybe<&2, Nat>, o, Some{0n}, None{})))) : String}:
  match b1 b2 o:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

law rule_show:
  for +o: Bool
  for +i: Nat
  for +v: U32
  {NR.chars([NS.rule(o, i, v)]) == B.Gt.show(B.Gt.rule(o, i, Some{n(v)})) : String}

def rule_show(o, i, v):
  %Equal.sym(Bool, U32.is_zero(v), Nat.is_eq(n(v), 0n), U.is_zero_to_nat(v)) : {NR.chars([Bool.pick(U32, _, 48, Bool.pick(U32, Nat.is_eq(n(v), i), 49, Bool.pick(U32, o, 48, 46)))]) == B.Gt.show(B.Gt.rule(o, i, Some{n(v)})) : String}
  rs.k(Nat.is_eq(n(v), 0n), Nat.is_eq(n(v), i), o)

# ---------------------------------------------------------------------------
# Numbers: Pos.read on text is lawful-fields' dec
# ---------------------------------------------------------------------------

def dig.k(+x: U32, +b: Bool, +hb: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == b : Bool}) -> {B.Pos.digit.if(x, b) == FD.digit.if(x, b) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, U32.to_nat(U32.sub(x, 48)), Nat.sub(n(x), 48n), LN.ed48(x, N.and_true_l(U32.is_ge(x, 48), U32.is_le(x, 57), hb))) : {Some{_} == Some{Nat.sub(n(x), 48n)} : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

def push_eq(+acc: Maybe<&2, Nat>, +d: Maybe<&2, Nat>) -> {B.Pos.read.push(acc, d) == FD.dec.push(acc, d) : Maybe<&2, Nat>}:
  match acc d:
    case Some{+a} Some{+k}:
      {==}
    case Some{+a} None{}:
      {==}
    case None{} _:
      {==}

def dig_eq(+x: U32) -> {B.Pos.digit(Chr{x}) == FD.digit(x) : Maybe<&2, Nat>}:
  dig.k(x, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), {==})

law pr_dec:
  for +xs: L32()
  for +acc: Maybe<&2, Nat>
  {B.Pos.read.go(NR.chars(xs), acc) == FD.dec.go(xs, acc) : Maybe<&2, Nat>}

def pr_dec(xs, acc):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Maybe<&2, Nat>, B.Pos.digit(Chr{x}), FD.digit(x), dig_eq(x)) :
        {B.Pos.read.go(NR.chars(r), B.Pos.read.push(acc, _)) == FD.dec.go(r, FD.dec.push(acc, FD.digit(x))) : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, B.Pos.read.push(acc, FD.digit(x)), FD.dec.push(acc, FD.digit(x)), push_eq(acc, FD.digit(x))) :
        {B.Pos.read.go(NR.chars(r), _) == FD.dec.go(r, FD.dec.push(acc, FD.digit(x))) : Maybe<&2, Nat>}
      pr_dec(r, FD.dec.push(acc, FD.digit(x)))

law read_dec:
  for +xs: L32()
  {B.Pos.read(NR.chars(xs)) == FD.dec(xs) : Maybe<&2, Nat>}

def read_dec(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      pr_dec(Con{x, r}, Some{0n})

law alld_txt:
  for +xs: L32()
  {B.Text.all_digits(NR.chars(xs)) == LDG.alld(xs) : Bool}

def alld_txt(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Bool, B.Text.all_digits(NR.chars(r)), LDG.alld(r), alld_txt(r)) : {Bool.and(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), _) == Bool.and(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), LDG.alld(r)) : Bool}
      {==}

# ---------------------------------------------------------------------------
# B.Gt.allele for the alleles the code takes
# ---------------------------------------------------------------------------

def NUMG(+o: Bool, +nn: Nat, +i: Nat, +k: Nat) -> B.Got:
  B.Gt.num(Some{k}, o, nn, i)

# Not '.', canonical, read as k: the number k.
def allele_num(+o: Bool, +nn: Nat, +i: Nat, +s: String, +k: Nat,
  +hne: {String.eq(s, ".") == False{} : Bool}, +hc: {B.Gt.canon(s) == True{} : Bool},
  +hr: {B.Pos.read(s) == Some{k} : Maybe<&2, Nat>}) -> {G.ALLELE(o, nn, i, s) == NUMG(o, nn, i, k) : B.Got}:
  %Equal.sym(Bool, String.eq(s, "."), False{}, hne) : {Bool.pick(B.Got, _, B.Got{"."}, Bool.pick(B.Got, B.Gt.canon(s), B.Gt.num(B.Pos.read(s), o, nn, i), B.Refuse{B.BadGt{}})) == NUMG(o, nn, i, k) : B.Got}
  %Equal.sym(Bool, B.Gt.canon(s), True{}, hc) : {Bool.pick(B.Got, _, B.Gt.num(B.Pos.read(s), o, nn, i), B.Refuse{B.BadGt{}}) == NUMG(o, nn, i, k) : B.Got}
  %Equal.sym(Maybe<&2, Nat>, B.Pos.read(s), Some{k}, hr) : {B.Gt.num(_, o, nn, i) == NUMG(o, nn, i, k) : B.Got}
  {==}

# canon from its three parts.
def canon_of(+s: String, +hE: {String.is_empty(s) == False{} : Bool}, +hA: {B.Text.all_digits(s) == True{} : Bool},
  +hZ: {(String.eq(s, "0") || Bool.not(String.starts_with(s, "0"))) == True{} : Bool}) -> {B.Gt.canon(s) == True{} : Bool}:
  %Equal.sym(Bool, String.is_empty(s), False{}, hE) : {(Bool.not(_) && B.Text.all_digits(s) && (String.eq(s, "0") || Bool.not(String.starts_with(s, "0")))) == True{} : Bool}
  %Equal.sym(Bool, B.Text.all_digits(s), True{}, hA) : {(Bool.not(False{}) && _ && (String.eq(s, "0") || Bool.not(String.starts_with(s, "0")))) == True{} : Bool}
  %Equal.sym(Bool, (String.eq(s, "0") || Bool.not(String.starts_with(s, "0"))), True{}, hZ) : {(Bool.not(False{}) && True{} && _) == True{} : Bool}
  {==}

def hz1.k(+b: Bool) -> {Bool.or(Bool.and(b, String.eq(SNil{}, SNil{})), Bool.not(String.starts_with.go.if(SNil{}, SNil{}, b))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# One digit x: canonical, read as x - 48.
def canon1(+x: U32, +hd: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == True{} : Bool}) -> {B.Gt.canon(SCon{Chr{x}, SNil{}}) == True{} : Bool}:
  +s = {SCon{Chr{x}, SNil{}} : String}
  +hA = {%Equal.sym(Bool, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), True{}, hd) : {Bool.and(_, True{}) == True{} : Bool}; {==} : {B.Text.all_digits(s) == True{} : Bool}}
  +hZ = {%Equal.sym(Bool, String.eq(s, "0"), Bool.and(U32.is_eq(x, 48), String.eq(SNil{}, SNil{})), RD.sc(x, 48, SNil{}, SNil{})) : {Bool.or(_, Bool.not(String.starts_with(s, "0"))) == True{} : Bool};
    hz1.k(U32.is_eq(x, 48)) : {(String.eq(s, "0") || Bool.not(String.starts_with(s, "0"))) == True{} : Bool}}
  canon_of(s, {==}, hA, hZ)

def read1(+x: U32, +hd: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == True{} : Bool}) -> {B.Pos.read(SCon{Chr{x}, SNil{}}) == Some{n((x - 48 : U32))} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), True{}, hd) : {B.Pos.read.push(Some{0n}, B.Pos.digit.if(x, _)) == Some{n((x - 48 : U32))} : Maybe<&2, Nat>}
  {==}

def alle1(+o: Bool, +nn: Nat, +i: Nat, +x: U32, +h46: {U32.is_eq(x, 46) == False{} : Bool},
  +hd: {Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)) == True{} : Bool}) ->
  {G.ALLELE(o, nn, i, SCon{Chr{x}, SNil{}}) == NUMG(o, nn, i, n((x - 48 : U32))) : B.Got}:
  +hne = {%Equal.sym(Bool, String.eq(SCon{Chr{x}, SNil{}}, SCon{Chr{46}, SNil{}}), Bool.and(U32.is_eq(x, 46), String.eq(SNil{}, SNil{})), RD.sc(x, 46, SNil{}, SNil{})) : {_ == False{} : Bool}; %Equal.sym(Bool, U32.is_eq(x, 46), False{}, h46) : {Bool.and(_, String.eq(SNil{}, SNil{})) == False{} : Bool}; {==} : {String.eq(SCon{Chr{x}, SNil{}}, ".") == False{} : Bool}}
  allele_num(o, nn, i, SCon{Chr{x}, SNil{}}, n((x - 48 : U32)), hne, canon1(x, hd), read1(x, hd))

# Two or more bytes, the first not '0', a number k.
def allem(+o: Bool, +nn: Nat, +i: Nat, +x: U32, +y: U32, +r: L32(), +k: Nat,
  +h48: {U32.is_eq(x, 48) == False{} : Bool},
  +hk: {FD.dec(Con{x, Con{y, r}}) == Some{k} : Maybe<&2, Nat>}) ->
  {G.ALLELE(o, nn, i, NR.chars(Con{x, Con{y, r}})) == NUMG(o, nn, i, k) : B.Got}:
  +xs = {Con{x, Con{y, r}} : L32()}
  +s = NR.chars(xs)
  +hne = {%Equal.sym(Bool, String.eq(s, SCon{Chr{46}, SNil{}}), Bool.and(U32.is_eq(x, 46), String.eq(NR.chars(Con{y, r}), SNil{})), RD.sc(x, 46, NR.chars(Con{y, r}), SNil{})) : {_ == False{} : Bool}; N.and_false_r(U32.is_eq(x, 46)) : {String.eq(s, ".") == False{} : Bool}}
  +hsome = {%Equal.sym(Maybe<&2, Nat>, FD.dec(xs), Some{k}, hk) : {Maybe.is_some(&2, Nat, _) == True{} : Bool}; {==} : {Maybe.is_some(&2, Nat, FD.dec.go(xs, Some{0n})) == True{} : Bool}}
  +hA = {%Equal.sym(Bool, B.Text.all_digits(s), LDG.alld(xs), alld_txt(xs)) : {_ == True{} : Bool}; %LDG.go_some(xs, Some{0n}) : {_ == True{} : Bool}; hsome : {B.Text.all_digits(s) == True{} : Bool}}
  +hZ = {%Equal.sym(Bool, String.eq(s, "0"), Bool.and(U32.is_eq(x, 48), String.eq(NR.chars(Con{y, r}), SNil{})), RD.sc(x, 48, NR.chars(Con{y, r}), SNil{})) : {Bool.or(_, Bool.not(String.starts_with(s, "0"))) == True{} : Bool};
    %Equal.sym(Bool, U32.is_eq(x, 48), False{}, h48) : {Bool.or(Bool.and(_, String.eq(NR.chars(Con{y, r}), SNil{})), Bool.not(String.starts_with.go.if(SNil{}, NR.chars(Con{y, r}), _))) == True{} : Bool};
    {==} : {(String.eq(s, "0") || Bool.not(String.starts_with(s, "0"))) == True{} : Bool}}
  +hr = Equal.trans(Maybe<&2, Nat>, B.Pos.read(s), FD.dec(xs), Some{k}, read_dec(xs), hk)
  allele_num(o, nn, i, s, k, hne, canon_of(s, {==}, hA, hZ), hr)

# ---------------------------------------------------------------------------
# Byte facts for tok
# ---------------------------------------------------------------------------

def rl.k(+b1: Bool, +b2: Bool, +o: Bool) -> {U32.is_lt(Bool.pick(U32, b1, 48, Bool.pick(U32, b2, 49, Bool.pick(U32, o, 48, 46))), 256) == True{} : Bool}:
  match b1 b2 o:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def issm(+m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{+x}:
      True{}
    case None{}:
      False{}

def none_some(-A: Type, +k: Nat, +h: {None{} == Some{k} : Maybe<&2, Nat>}) -> A:
  Empty.absurd(A, P.false_ne_true(Equal.cong(Maybe<&2, Nat>, Bool, m => issm(m), None{}, Some{k}, h)))

def dbif(+j: Nat, +k: Nat, +b: Bool, +h: {FD.decb.if(j, b) == Some{k} : Maybe<&2, Nat>}) -> {Some{j} == Some{k} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      h
    case False{}:
      none_some({Some{j} == Some{k} : Maybe<&2, Nat>}, k, h)

def dbof(+m: Maybe<&2, Nat>, +k: Nat, +bd: Nat, +h: {FD.decb.of(m, bd) == Some{k} : Maybe<&2, Nat>}) -> {m == Some{k} : Maybe<&2, Nat>}:
  match m:
    case Some{+j}:
      dbif(j, k, Nat.is_lt(j, bd), h)
    case None{}:
      none_some({None{} == Some{k} : Maybe<&2, Nat>}, k, h)

def rule_lt(+o: Bool, +i: Nat, +v: U32) -> {U32.is_lt(NS.rule(o, i, v), 256) == True{} : Bool}:
  rl.k(U32.is_zero(v), Nat.is_eq(n(v), i), o)

law decb_some:
  for +xs: L32()
  for +k: Nat
  for +bd: Nat
  for +h: {FD.decb(xs, bd) == Some{k} : Maybe<&2, Nat>}
  {FD.dec(xs) == Some{k} : Maybe<&2, Nat>}

def decb_some(xs, k, bd, h):
  dbof(FD.dec(xs), k, bd, h)
