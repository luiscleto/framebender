import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./run.bend as R
import ./proof_s_site.bend as SI
import ./proof_s_same.bend as SM
import ./proof_s_at.bend as AT
import ./proof_s_ikeys.bend as IK
import ./proof_s_col.bend as CO
import ./proof_s_fvals.bend as FV
import ./proof_s_ient.bend as IE
import ./proof_run_base.bend as RB
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# Laws split_info_kept and split_info_values: an INFO entry with no value,
# the value '.', or a tag of Number Other is copied byte for byte; a
# per-allele entry gives the values of the record's alleles (lifted). Every
# variable is reusable.

def Ss() -> Data:
  List<&2, String>

def ref_ne(+c: B.Code, +y: String, +h: {B.Refuse{c} == B.Got{y} : B.Got}) -> Empty:
  CO.ref_ne(c, y, h)

def EQ(+m: Maybe<&2, B.Num>, +x: String, +n: Nat, +i: Nat) -> B.Got:
  B.Info.split.eq(m, B.Info.key(x), x, n, i)

def or_mid(+a: Bool, +b: Bool, +c: Bool, +h: {Bool.or(Bool.or(a, b), c) == True{} : Bool}, +ha: {a == False{} : Bool}, +hc: {c == False{} : Bool}) -> {b == True{} : Bool}:
  match a b c:
    case True{} _ _:
      Empty.absurd({b == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, ha)))
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hc)))
    case False{} False{} False{}:
      h

# ---------------------------------------------------------------------------
# Kept
# ---------------------------------------------------------------------------

# A per-allele entry with the value '.': written again as it was.
def kp.dot(+num: B.Num, +x: String, +n: Nat, +i: Nat,
  +hne: {String.eq(B.Info.key(x), x) == False{} : Bool},
  +hd: {String.eq(L.value_text(x), ".") == True{} : Bool}) ->
  {SI.gtext(B.Got.cat(B.Got{B.Info.key(x)}, "=", B.Got.of(B.Vals.split(num, n, Some{2n}, i, L.value_text(x)), B.BadCount{}))) == x : String}:
  +K = B.Info.key(x)
  +ev = RB.str_eq_sound(L.value_text(x), ".", hd)
  +ex = IE.kvx(x, hne)
  %Equal.sym(Bool, String.eq(L.value_text(x), "."), True{}, hd) :
    {SI.gtext(B.Got.cat(B.Got{K}, "=", B.Got.of(B.Vals.split.if(_, num, n, Some{2n}, i, L.value_text(x)), B.BadCount{}))) == x : String}
  Equal.trans(String, String.append(K, String.append("=", ".")), String.append(K, String.append("=", L.value_text(x))), x,
    Equal.cong(String, String, z => String.append(K, String.append("=", z)), ".", L.value_text(x), Equal.sym(String, L.value_text(x), ".", ev)),
    Equal.sym(String, x, IE.KV(x), ex))

def nhv(+x: String, +hne: {String.eq(B.Info.key(x), x) == False{} : Bool}) -> {Bool.not(L.has_value(x)) == False{} : Bool}:
  Equal.cong(Bool, Bool, z => Bool.not(z), L.has_value(x), True{}, IE.ne_hv(x, hne))

def kp.m(+m: Maybe<&2, B.Num>, +x: String, +n: Nat, +i: Nat,
  +hne: {String.eq(B.Info.key(x), x) == False{} : Bool},
  +hc: {Bool.or(Bool.or(Bool.not(L.has_value(x)), String.eq(L.value_text(x), ".")), L.is_other(m)) == True{} : Bool},
  +hg: {EQ(m, x, n, i) == B.Got{SI.gtext(EQ(m, x, n, i))} : B.Got}) ->
  {SI.gtext(EQ(m, x, n, i)) == x : String}:
  match m:
    case None{}:
      Empty.absurd({SI.gtext(EQ(None{}, x, n, i)) == x : String}, ref_ne(B.UndefinedTag{"INFO/" ++ B.Info.key(x)}, "", hg))
    case Some{+num}:
      match num:
        case B.NumUnknown{}:
          Empty.absurd({SI.gtext(EQ(Some{B.NumUnknown{}}, x, n, i)) == x : String}, ref_ne(B.UndefinedTag{"INFO/" ++ B.Info.key(x)}, "", hg))
        case B.NumOther{}:
          {==}
        case B.NumA{}:
          kp.dot(B.NumA{}, x, n, i, hne, or_mid(Bool.not(L.has_value(x)), String.eq(L.value_text(x), "."), False{}, hc, nhv(x, hne), {==}))
        case B.NumR{}:
          kp.dot(B.NumR{}, x, n, i, hne, or_mid(Bool.not(L.has_value(x)), String.eq(L.value_text(x), "."), False{}, hc, nhv(x, hne), {==}))
        case B.NumG{}:
          kp.dot(B.NumG{}, x, n, i, hne, or_mid(Bool.not(L.has_value(x)), String.eq(L.value_text(x), "."), False{}, hc, nhv(x, hne), {==}))

def kflag(+pa: Bool, +x: String, +h: {Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{x}) == B.Got{SI.gtext(Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{x}))} : B.Got}) ->
  {SI.gtext(Bool.pick(B.Got, pa, B.Refuse{B.BadCount{}}, B.Got{x})) == x : String}:
  match pa:
    case True{}:
      Empty.absurd({SI.gtext(B.Refuse{B.BadCount{}}) == x : String}, ref_ne(B.BadCount{}, "", h))
    case False{}:
      {==}

def NUM(+m: Maybe<&2, B.Num>, +x: String, +n: Nat, +i: Nat) -> B.Got:
  B.Info.split.num(m, x, n, i)

def kn.c(+c: Bool, +m: Maybe<&2, B.Num>, +x: String, +n: Nat, +i: Nat,
  +ec: {String.eq(B.Info.key(x), x) == c : Bool},
  +hc: {Bool.or(Bool.or(Bool.not(L.has_value(x)), String.eq(L.value_text(x), ".")), L.is_other(m)) == True{} : Bool},
  +hg: {NUM(m, x, n, i) == B.Got{SI.gtext(NUM(m, x, n, i))} : B.Got}) -> {SI.gtext(NUM(m, x, n, i)) == x : String}:
  match c:
    case True{}:
      +P = Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{x})
      +hg2 = {%ec : {Bool.pick(B.Got, _, P, EQ(m, x, n, i)) == B.Got{SI.gtext(Bool.pick(B.Got, _, P, EQ(m, x, n, i)))} : B.Got}; hg : {P == B.Got{SI.gtext(P)} : B.Got}}
      {%Equal.sym(Bool, String.eq(B.Info.key(x), x), True{}, ec) : {SI.gtext(Bool.pick(B.Got, _, P, EQ(m, x, n, i))) == x : String};
       kflag(B.Num.per_allele(m), x, hg2) : {SI.gtext(NUM(m, x, n, i)) == x : String}}
    case False{}:
      +P = Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{x})
      +hg2 = {%ec : {Bool.pick(B.Got, _, P, EQ(m, x, n, i)) == B.Got{SI.gtext(Bool.pick(B.Got, _, P, EQ(m, x, n, i)))} : B.Got}; hg : {EQ(m, x, n, i) == B.Got{SI.gtext(EQ(m, x, n, i))} : B.Got}}
      {%Equal.sym(Bool, String.eq(B.Info.key(x), x), False{}, ec) : {SI.gtext(Bool.pick(B.Got, _, P, EQ(m, x, n, i))) == x : String};
       kp.m(m, x, n, i, ec, hc, hg2) : {SI.gtext(NUM(m, x, n, i)) == x : String}}

def ik_at(+defs: B.Defs, +body: String, +i: Nat, +p: String, +e: Nat, +x: String,
  +hc: {L.info_copied(B.Defs.info(defs), x) == True{} : Bool},
  r: IE.EA(defs, body, i, p, e, x)) -> {List.get(&2, String, L.info_entries(p), e) == Some{x} : Maybe<&2, String>}:
  match r:
    case (eN, eg):
      +N1 = IE.NUMI(defs, body, i, x)
      Equal.trans(Maybe<&2, String>, List.get(&2, String, L.info_entries(p), e), Some{SI.gtext(N1)}, Some{x}, eg,
        Equal.cong(String, Maybe<&2, String>, z => Some{z}, SI.gtext(N1), x,
          kn.c(String.eq(B.Info.key(x), x), B.Tags.find(B.Defs.info(defs), B.Info.key(x)), x, L.n_alts(body), 1n+i, {==}, hc, eN)))

# Law split_info_kept: every other INFO entry is copied by the split, byte
# for byte: a flag, an empty entry, a value '.', a tag of Number Other.
law split_info_kept:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +e: Nat
  for +x: String
  for +hx: {List.get(&2, String, L.info_entries(body), e) == Some{x} : Maybe<&2, String>}
  for +hc: {L.info_copied(B.Defs.info(defs), x) == True{} : Bool}
  {List.get(&2, String, L.info_entries(p), e) == Some{x} : Maybe<&2, String>}

def split_info_kept(defs, o, body, ps, h, i, p, hp, e, x, hx, hc):
  ik_at(defs, body, i, p, e, x, hc, IE.ent_at(defs, o, body, ps, h, i, p, hp, e, x, hx))

# ---------------------------------------------------------------------------
# Values
# ---------------------------------------------------------------------------

def VT(+x: String) -> String:
  L.value_text(x)

def KV2(+num: B.Num, +x: String, +n: Nat, +i: Nat) -> B.Got:
  FV.KEEP(num, n, 2n, 1n+i, FV.VS(VT(x)))

def CAT(+num: B.Num, +x: String, +n: Nat, +i: Nat) -> B.Got:
  B.Got.cat(B.Got{B.Info.key(x)}, "=", KV2(num, x, n, i))

def iv.n(+num: B.Num, +x: String, +n: Nat, +i: Nat,
  +ha: {L.per_allele_num(num) == True{} : Bool},
  +hm: {String.eq(VT(x), ".") == False{} : Bool}) ->
  {EQ(Some{num}, x, n, 1n+i) == CAT(num, x, n, i) : B.Got}:
  match num:
    case B.NumA{}:
      %Equal.sym(Bool, String.eq(VT(x), "."), False{}, hm) : {B.Got.cat(B.Got{B.Info.key(x)}, "=", B.Got.of(B.Vals.split.if(_, B.NumA{}, n, Some{2n}, 1n+i, VT(x)), B.BadCount{})) == CAT(B.NumA{}, x, n, i) : B.Got}
      {==}
    case B.NumR{}:
      %Equal.sym(Bool, String.eq(VT(x), "."), False{}, hm) : {B.Got.cat(B.Got{B.Info.key(x)}, "=", B.Got.of(B.Vals.split.if(_, B.NumR{}, n, Some{2n}, 1n+i, VT(x)), B.BadCount{})) == CAT(B.NumR{}, x, n, i) : B.Got}
      {==}
    case B.NumG{}:
      %Equal.sym(Bool, String.eq(VT(x), "."), False{}, hm) : {B.Got.cat(B.Got{B.Info.key(x)}, "=", B.Got.of(B.Vals.split.if(_, B.NumG{}, n, Some{2n}, 1n+i, VT(x)), B.BadCount{})) == CAT(B.NumG{}, x, n, i) : B.Got}
      {==}
    case B.NumOther{}:
      Empty.absurd({EQ(Some{B.NumOther{}}, x, n, 1n+i) == CAT(B.NumOther{}, x, n, i) : B.Got}, AB.false_ne_true(ha))
    case B.NumUnknown{}:
      Empty.absurd({EQ(Some{B.NumUnknown{}}, x, n, 1n+i) == CAT(B.NumUnknown{}, x, n, i) : B.Got}, AB.false_ne_true(ha))

def iv_at(+defs: B.Defs, +body: String, +i: Nat, +p: String, +e: Nat, +x: String, +num: B.Num,
  +hv: {L.has_value(x) == True{} : Bool},
  +hk: {B.Tags.find(B.Defs.info(defs), B.Info.key(x)) == Some{num} : Maybe<&2, B.Num>},
  +ha: {L.per_allele_num(num) == True{} : Bool},
  +hm: {String.eq(VT(x), ".") == False{} : Bool},
  r: IE.EA(defs, body, i, p, e, x)) ->
  {L.entry_values(List.get(&2, String, L.info_entries(p), e)) == L.lifted(num, 2n, 1n+i, L.values(VT(x))) : Maybe<&2, Ss()>}:
  match r:
    case (eN, eg):
      +n = L.n_alts(body)
      +K = B.Info.key(x)
      +m = B.Tags.find(B.Defs.info(defs), K)
      +N1 = IE.NUMI(defs, body, i, x)
      +KP = KV2(num, x, n, i)
      +P = Bool.pick(B.Got, B.Num.per_allele(m), B.Refuse{B.BadCount{}}, B.Got{x})
      +e1 = Equal.cong(Bool, B.Got, z => Bool.pick(B.Got, z, P, EQ(m, x, n, 1n+i)), String.eq(K, x), False{}, IE.hv_ne(x, hv))
      +e2 = Equal.cong(Maybe<&2, B.Num>, B.Got, z => EQ(z, x, n, 1n+i), m, Some{num}, hk)
      +eC = Equal.trans(B.Got, N1, EQ(m, x, n, 1n+i), CAT(num, x, n, i), e1, Equal.trans(B.Got, EQ(m, x, n, 1n+i), EQ(Some{num}, x, n, 1n+i), CAT(num, x, n, i), e2, iv.n(num, x, n, i, ha, hm)))
      +hC = Equal.trans(B.Got, CAT(num, x, n, i), N1, B.Got{SI.gtext(N1)}, Equal.sym(B.Got, N1, CAT(num, x, n, i), eC), eN)
      +eK = AT.cat_r(K, "=", KP, SI.gtext(N1), hC)
      +ey = AT.cat_y(K, "=", KP, SI.gtext(N1), hC)
      +evt = Equal.trans(String, L.value_text(SI.gtext(N1)), L.value_text(String.append(K, String.append("=", SI.gtext(KP)))), SI.gtext(KP),
        Equal.cong(String, String, z => L.value_text(z), SI.gtext(N1), String.append(K, String.append("=", SI.gtext(KP))), ey),
        IE.vtx(K, SI.gtext(KP), IK.key_nc(x)))
      Equal.trans(Maybe<&2, Ss()>, L.entry_values(List.get(&2, String, L.info_entries(p), e)), L.entry_values(Some{SI.gtext(N1)}), L.lifted(num, 2n, 1n+i, L.values(VT(x))),
        Equal.cong(Maybe<&2, String>, Maybe<&2, Ss()>, z => L.entry_values(z), List.get(&2, String, L.info_entries(p), e), Some{SI.gtext(N1)}, eg),
        Equal.trans(Maybe<&2, Ss()>, L.entry_values(Some{SI.gtext(N1)}), L.values_of(Some{SI.gtext(KP)}), L.lifted(num, 2n, 1n+i, L.values(VT(x))),
          Equal.cong(String, Maybe<&2, Ss()>, z => Some{L.values(z)}, L.value_text(SI.gtext(N1)), SI.gtext(KP), evt),
          FV.fv.lift(num, n, 2n, i, FV.VS(VT(x)), ha, FV.comma_all(VT(x)), eK)))

# Law split_info_values: every INFO entry whose tag is A, R or G and whose
# value is not '.' gives, in the record for ALT i+1, exactly the values of
# that record's alleles (lifted).
law split_info_values:
  for +defs: B.Defs
  for +o: B.Opts
  for +body: String
  for +ps: Ss()
  for +h: {B.Rec.parts(defs, o, body) == B.Pieces{ps} : B.Parts}
  for +i: Nat
  for +p: String
  for +hp: {List.get(&2, String, ps, i) == Some{p} : Maybe<&2, String>}
  for +e: Nat
  for +x: String
  for +hx: {List.get(&2, String, L.info_entries(body), e) == Some{x} : Maybe<&2, String>}
  for +num: B.Num
  for +hk: {B.Tags.find(B.Defs.info(defs), B.Info.key(x)) == Some{num} : Maybe<&2, B.Num>}
  for +ha: {L.per_allele_num(num) == True{} : Bool}
  for +hv: {L.has_value(x) == True{} : Bool}
  for +hm: {String.eq(L.value_text(x), ".") == False{} : Bool}
  {L.entry_values(List.get(&2, String, L.info_entries(p), e)) == L.lifted(num, 2n, 1n+i, L.values(L.value_text(x))) : Maybe<&2, Ss()>}

def split_info_values(defs, o, body, ps, h, i, p, hp, e, x, hx, num, hk, ha, hv, hm):
  iv_at(defs, body, i, p, e, x, num, hv, hk, ha, hm, IE.ent_at(defs, o, body, ps, h, i, p, hp, e, x, hx))
