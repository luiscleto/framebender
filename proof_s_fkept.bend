import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_site.bend as SI
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_col.bend as CO
import ./proof_run_base.bend as RB
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Law split_format_kept: a FORMAT value (not GT) that is '.' or whose tag has
# Number Other is copied byte for byte into every record. Every variable is
# reusable.

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  CO.ref_ne(c, y, h)

def NUM(+m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat) -> B.Got:
  B.Fmt.split.num(m, k, v, n, cp, i)

# A per-allele value '.': '.' again.
def kp.dot(+num: B.Num, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat, +d: Bool,
  +ed: {String.eq(v, ".") == d : Bool}, +hd: {d == True{} : Bool},
  +hg: {B.Got.of(B.Vals.split(num, n, cp, i, v), B.BadCount{}) == B.Got{SI.gtext(B.Got.of(B.Vals.split(num, n, cp, i, v), B.BadCount{}))} : B.Got}) ->
  {SI.gtext(B.Got.of(B.Vals.split(num, n, cp, i, v), B.BadCount{})) == v : String}:
  +ev = RB.str_eq_sound(v, ".", Equal.trans(Bool, String.eq(v, "."), d, True{}, ed, hd))
  {%Equal.sym(Bool, String.eq(v, "."), True{}, Equal.trans(Bool, String.eq(v, "."), d, True{}, ed, hd)) : {SI.gtext(B.Got.of(B.Vals.split.if(_, num, n, cp, i, v), B.BadCount{})) == v : String};
   Equal.sym(String, v, ".", ev) : {SI.gtext(B.Got.of(B.Vals.split(num, n, cp, i, v), B.BadCount{})) == v : String}}

def kp.or(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, +hb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hb), h)

def kp.num(+num: B.Num, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +hc: {Bool.or(String.eq(v, "."), L.is_other(Some{num})) == True{} : Bool},
  +hg: {NUM(Some{num}, k, v, n, cp, i) == B.Got{SI.gtext(NUM(Some{num}, k, v, n, cp, i))} : B.Got}) ->
  {SI.gtext(NUM(Some{num}, k, v, n, cp, i)) == v : String}:
  match num:
    case B.NumUnknown{}:
      Empty.absurd({SI.gtext(NUM(Some{B.NumUnknown{}}, k, v, n, cp, i)) == v : String}, ref_ne(B.UndefinedTag{"FORMAT/" ++ k}, "", hg))
    case B.NumOther{}:
      {==}
    case B.NumA{}:
      kp.dot(B.NumA{}, v, n, cp, i, String.eq(v, "."), {==}, kp.or(String.eq(v, "."), False{}, hc, {==}), hg)
    case B.NumR{}:
      kp.dot(B.NumR{}, v, n, cp, i, String.eq(v, "."), {==}, kp.or(String.eq(v, "."), False{}, hc, {==}), hg)
    case B.NumG{}:
      kp.dot(B.NumG{}, v, n, cp, i, String.eq(v, "."), {==}, kp.or(String.eq(v, "."), False{}, hc, {==}), hg)

# A copied value: the record has it as it was.
def kp(+m: Maybe<&2, B.Num>, +k: String, +v: String, +n: Nat, +cp: Maybe<&2, Nat>, +i: Nat,
  +hc: {Bool.or(String.eq(v, "."), L.is_other(m)) == True{} : Bool},
  +hg: {NUM(m, k, v, n, cp, i) == B.Got{SI.gtext(NUM(m, k, v, n, cp, i))} : B.Got}) ->
  {SI.gtext(NUM(m, k, v, n, cp, i)) == v : String}:
  match m:
    case None{}:
      Empty.absurd({SI.gtext(NUM(None{}, k, v, n, cp, i)) == v : String}, ref_ne(B.UndefinedTag{"FORMAT/" ++ k}, "", hg))
    case Some{+num}:
      kp.num(num, k, v, n, cp, i, hc, hg)

def fk_at(+defs: B.Defs, +o0: Bool, +body: String, +i: Nat, +p: String, +s: Nat, +j: Nat, +k: String, +v: String,
  +hgt: {String.eq(k, "GT") == False{} : Bool},
  +hc: {L.format_copied(B.Defs.fmt(defs), k, v) == True{} : Bool},
  r: CO.VA(defs, o0, body, i, p, s, j, k, v)) -> {L.sample_at(p, s, j) == Some{v} : Maybe<&2, String>}:
  match r:
    case (+col, q):
      match q:
        case (em, q2):
          match q2:
            case (eO, ea):
              +O = CO.ONE(defs, o0, body, i, col, k, v)
              +m = B.Tags.find(B.Defs.fmt(defs), k)
              +n = L.n_alts(body)
              +cp = CO.CP(body, col)
              +eO2 = {%hgt : {Bool.pick(B.Got, _, B.Gt.split(o0, n, 1n+i, v), NUM(m, k, v, n, cp, 1n+i)) == B.Got{SI.gtext(Bool.pick(B.Got, _, B.Gt.split(o0, n, 1n+i, v), NUM(m, k, v, n, cp, 1n+i)))} : B.Got};
                eO : {NUM(m, k, v, n, cp, 1n+i) == B.Got{SI.gtext(NUM(m, k, v, n, cp, 1n+i))} : B.Got}}
              +ev = {%Equal.sym(Bool, String.eq(k, "GT"), False{}, hgt) : {SI.gtext(Bool.pick(B.Got, _, B.Gt.split(o0, n, 1n+i, v), NUM(m, k, v, n, cp, 1n+i))) == v : String};
                kp(m, k, v, n, cp, 1n+i, hc, eO2) : {SI.gtext(O) == v : String}}
              Equal.trans(Maybe<&2, String>, L.sample_at(p, s, j), Some{SI.gtext(O)}, Some{v}, ea, Equal.cong(String, Maybe<&2, String>, z => Some{z}, SI.gtext(O), v, ev))

# Law split_format_kept: every other FORMAT value (not GT) is copied byte for
# byte: a value '.', a tag of Number Other.
law split_format_kept:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: List<&2, String>
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +s: Nat
  for +j: Nat
  for +k: String
  for +hk: {List.get(&2, String, L.format_keys(body), j) == Some{k} : Maybe<&2, String>}
  for +hgt: {String.eq(k, "GT") == False{} : Bool}
  for +v: String
  for +hv: {L.sample_at(body, s, j) == Some{v} : Maybe<&2, String>}
  for +hc: {L.format_copied(B.Defs.fmt(defs), k, v) == True{} : Bool}
  {L.sample_at(p, s, j) == Some{v} : Maybe<&2, String>}

def split_format_kept(defs, o, body, ps, h, i, p, hp, s, j, k, hk, hgt, v, hv, hc):
  fk_at(defs, R.Opts.over0(o), body, i, p, s, j, k, v, hgt, hc, CO.val_at(defs, o, body, ps, h, i, p, hp, s, j, k, hk, v, hv))
