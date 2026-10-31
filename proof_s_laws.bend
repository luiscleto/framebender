import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-words@0.1.0.0/proof_nat.bend as N

# The split laws of LAWS.bend (-m), restated with every variable reusable:
# which lines stay whole. Every variable is reusable.

def COND(+sp: Bool, +fs: List<&2, String>) -> Bool:
  Bool.and(Bool.and(sp, Bool.not(B.Rec.malformed(fs))), Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs))))

def lnl.k(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}, +c: Bool, +e: {Nat.is_le(b, a) == c : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(a, b), True{}, Equal.sym(Bool, Nat.is_lt(a, b), False{}, N.le_not_lt(b, a, e)), h)))
    case False{}:
      {==}

# a < b: not b <= a.
def lt_not_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  lnl.k(a, b, h, Nat.is_le(b, a), {==})

# The test false: whole.
def whole_if(+defs: B.Defs, +st: Bool, +w: Nat, +sp: Bool, +o0: Bool, +args: List<&2, String>, +body: String,
  +h: {COND(sp, B.Rec.fields(body)) == False{} : Bool}) -> {B.Rec.parts(defs, B.Opts{st, w, sp, o0, args}, body) == B.Whole{} : B.Parts}:
  %Equal.sym(Bool, COND(sp, B.Rec.fields(body)), False{}, h) : {B.Rec.parts.if(_, B.Text.has_cr(body), defs, o0, B.Rec.fields(body)) == B.Whole{} : B.Parts}
  {==}

# Without -m, every line is one record.
law whole_without_m:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +h: {R.Opts.split(o) == False{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

def whole_without_m(defs, o, body, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      whole_if(defs, st, w, sp, o0, args, body,
        {%Equal.sym(Bool, sp, False{}, h) : {COND(_, B.Rec.fields(body)) == False{} : Bool}; {==} : {COND(sp, B.Rec.fields(body)) == False{} : Bool}})

# With -m, a record with one ALT is handled as without -m.
law whole_biallelic:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +h: {Nat.is_lt(L.n_alts(body), 2n) == True{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

def whole_biallelic(defs, o, body, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(body)
      +A = Bool.and(sp, Bool.not(B.Rec.malformed(fs)))
      +n = List.length(&2, String, B.Rec.alts(fs))
      +h2 = lt_not_le(n, 2n, h)
      whole_if(defs, st, w, sp, o0, args, body,
        {%Equal.sym(Bool, Nat.is_le(2n, n), False{}, h2) : {Bool.and(A, _) == False{} : Bool}; N.and_false_r(A) : {COND(sp, fs) == False{} : Bool}})

# A MALFORMED line is handled as without -m.
law whole_malformed:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +h: {B.Rec.malformed(B.Rec.fields(body)) == True{} : Bool}
  {B.Rec.parts(defs, o, body) == B.Whole{} : B.Parts}

def whole_malformed(defs, o, body, h):
  match o:
    case B.Opts{+st, +w, +sp, +o0, +args}:
      +fs = B.Rec.fields(body)
      +n2 = Nat.is_le(2n, List.length(&2, String, B.Rec.alts(fs)))
      whole_if(defs, st, w, sp, o0, args, body,
        {%Equal.sym(Bool, B.Rec.malformed(fs), True{}, h) : {Bool.and(Bool.and(sp, Bool.not(_)), n2) == False{} : Bool};
         %Equal.sym(Bool, Bool.and(sp, False{}), False{}, N.and_false_r(sp)) : {Bool.and(_, n2) == False{} : Bool};
         {==} : {COND(sp, fs) == False{} : Bool}})
