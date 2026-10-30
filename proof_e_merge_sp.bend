import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as W
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_e_defs.bend as SD
import ./proof_e_merge_lem.bend as ML
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase E, area "merge": a run's items as run.bend's (NR.spec.items, the
# picture's buffer) against norm_par.bend's tests on the byte items: keys,
# input POS, line numbers and the order are kept.

law sp_sorted_go:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +k: Nat
  {SD.sorted.go(NR.spec.items(cs, ch, t), k) == W.sorted.go(cs, k) : Bool}

def sp_sorted_go(cs, ch, t, k):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          %Equal.sym(Bool, SD.sorted.go(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))), kk), W.sorted.go(rest, kk), sp_sorted_go(rest, ch, String.drop(t, U32.to_nat(n)), kk)) : {Bool.and(Nat.is_le(k, kk), _) == Bool.and(Nat.is_le(k, kk), W.sorted.go(rest, kk)) : Bool}
          {==}

law sp_sorted:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  {SD.sorted(NR.spec.items(cs, ch, t)) == W.sorted(cs) : Bool}

def sp_sorted(cs, ch, t):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          sp_sorted_go(rest, ch, String.drop(t, U32.to_nat(n)), kk)

law sp_keys_ge:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +l: Nat
  {SD.keys_ge(NR.spec.items(cs, ch, t), l) == W.keys_ge(cs, l) : Bool}

def sp_keys_ge(cs, ch, t, l):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          %Equal.sym(Bool, SD.keys_ge(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))), l), W.keys_ge(rest, l), sp_keys_ge(rest, ch, String.drop(t, U32.to_nat(n)), l)) : {Bool.and(Nat.is_le(l, kk), _) == Bool.and(Nat.is_le(l, kk), W.keys_ge(rest, l)) : Bool}
          {==}

law sp_max_inpos:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +m: Nat
  {SD.max_inpos(NR.spec.items(cs, ch, t), m) == W.max_inpos(cs, m) : Nat}

def sp_max_inpos(cs, ch, t, m):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          sp_max_inpos(rest, ch, String.drop(t, U32.to_nat(n)), Nat.max(m, ip))

law sp_key_first:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  for +d: Nat
  {SD.key_or(SD.first_item(NR.spec.items(cs, ch, t)), d) == W.key_or(W.first_ck(cs), d) : Nat}

def sp_key_first(cs, ch, t, d):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          {==}

law sp_is_empty:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  {List.is_empty(&2, R.Item, NR.spec.items(cs, ch, t)) == RD.is_nil(cs) : Bool}

def sp_is_empty(cs, ch, t):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      {==}

law sp_last_le:
  for +m: Maybe<&2, NR.Ck>
  for +ch: String
  for +k: Nat
  {SD.last_le(NR.spec.last(m, ch), k) == NR.last_le(m, k) : Bool}

def sp_last_le(m, ch, k):
  match m:
    case None{}:
      {==}
    case Some{+c}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          {==}

law sp_key_last:
  for +m: Maybe<&2, NR.Ck>
  for +ch: String
  for +d: Nat
  {SD.key_or(NR.spec.last(m, ch), d) == W.key_or(m, d) : Nat}

def sp_key_last(m, ch, d):
  match m:
    case None{}:
      {==}
    case Some{+c}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          {==}

law sp_real_inpos:
  for +m: Maybe<&2, NR.Ck>
  for +ch: String
  {SD.real_inpos(NR.spec.last(m, ch)) == W.real_inpos(m) : Nat}

def sp_real_inpos(m, ch):
  match m:
    case None{}:
      {==}
    case Some{+c}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          match ln:
            case 0n:
              {==}
            case 1n+q:
              {==}

# T's items, their line numbers moved on.
law sp_shift:
  for +cs: List<&2, NR.Ck>
  for +d: Nat
  for +ch: String
  for +t: String
  {NR.spec.items(W.cks_shift(d, cs), ch, t) == SD.items_shift(d, NR.spec.items(cs, ch, t)) : List<&2, R.Item>}

def sp_shift(cs, d, ch, t):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          %sp_shift(rest, d, ch, String.drop(t, U32.to_nat(n))) : {Con{R.Item{kk, ip, B.At{Nat.add(ln, d), ch, NR.pos_text(p, kk)}, String.take(t, U32.to_nat(n))}, NR.spec.items(W.cks_shift(d, rest), ch, String.drop(t, U32.to_nat(n)))} == Con{R.Item{kk, ip, B.At{Nat.add(ln, d), ch, NR.pos_text(p, kk)}, String.take(t, U32.to_nat(n))}, _} : List<&2, R.Item>}
          {==}

# The items' texts are the text they were cut from, up to their lengths.
law texts_take:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  {SD.texts(NR.spec.items(cs, ch, t)) == String.take(t, RD.lens(cs)) : String}

def texts_take(cs, ch, t):
  match cs:
    case Nil{}:
      Equal.sym(String, String.take(t, 0n), "", ML.take0(t))
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          Equal.trans(String, String.append(String.take(t, U32.to_nat(n)), SD.texts(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))))), String.append(String.take(t, U32.to_nat(n)), String.take(String.drop(t, U32.to_nat(n)), RD.lens(rest))), String.take(t, Nat.add(U32.to_nat(n), RD.lens(rest))),
            Equal.cong(String, String, z => String.append(String.take(t, U32.to_nat(n)), z), SD.texts(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n)))), String.take(String.drop(t, U32.to_nat(n)), RD.lens(rest)), texts_take(rest, ch, String.drop(t, U32.to_nat(n)))),
            Equal.sym(String, String.take(t, Nat.add(U32.to_nat(n), RD.lens(rest))), String.append(String.take(t, U32.to_nat(n)), String.take(String.drop(t, U32.to_nat(n)), RD.lens(rest))), ML.take_add(t, U32.to_nat(n), RD.lens(rest))))

# Blanked last items
# ==================

law bl_or:
  for +a: Maybe<&2, R.Item>
  for +b: Maybe<&2, R.Item>
  {P.blank(Maybe.or(&2, R.Item, a, b)) == Maybe.or(&2, R.Item, P.blank(a), P.blank(b)) : Maybe<&2, R.Item>}

def bl_or(a, b):
  match a:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case R.Item{+k, +p, +at, +tx}:
          {==}

law sp_last_or:
  for +a: Maybe<&2, NR.Ck>
  for +b: Maybe<&2, NR.Ck>
  for +ch: String
  {NR.spec.last(Maybe.or(&2, NR.Ck, a, b), ch) == Maybe.or(&2, R.Item, NR.spec.last(a, ch), NR.spec.last(b, ch)) : Maybe<&2, R.Item>}

def sp_last_or(a, b, ch):
  match a:
    case None{}:
      {==}
    case Some{+c}:
      {==}

law bl_sp:
  for +m: Maybe<&2, NR.Ck>
  for +ch: String
  {P.blank(NR.spec.last(m, ch)) == NR.spec.last(m, ch) : Maybe<&2, R.Item>}

def bl_sp(m, ch):
  match m:
    case None{}:
      {==}
    case Some{+c}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          {==}

# The last of the items, blanked, is the last item's picture.
law bl_li:
  for +cs: List<&2, NR.Ck>
  for +ch: String
  for +t: String
  {P.blank(SD.last_item(NR.spec.items(cs, ch, t))) == NR.spec.last(W.last_ck(cs), ch) : Maybe<&2, R.Item>}

def bl_li(cs, ch, t):
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match c:
        case NR.Ck{+kk, +ip, +ln, +p, +n}:
          Equal.trans(Maybe<&2, R.Item>, P.blank(Maybe.or(&2, R.Item, SD.last_item(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n)))), Some{R.Item{kk, ip, B.At{ln, ch, NR.pos_text(p, kk)}, String.take(t, U32.to_nat(n))}})), Maybe.or(&2, R.Item, P.blank(SD.last_item(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))))), Some{R.Item{kk, ip, B.At{ln, ch, NR.pos_text(p, kk)}, ""}}), NR.spec.last(Maybe.or(&2, NR.Ck, W.last_ck(rest), Some{NR.Ck{kk, ip, ln, p, n}}), ch),
            bl_or(SD.last_item(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n)))), Some{R.Item{kk, ip, B.At{ln, ch, NR.pos_text(p, kk)}, String.take(t, U32.to_nat(n))}}),
            Equal.trans(Maybe<&2, R.Item>, Maybe.or(&2, R.Item, P.blank(SD.last_item(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))))), Some{R.Item{kk, ip, B.At{ln, ch, NR.pos_text(p, kk)}, ""}}), Maybe.or(&2, R.Item, NR.spec.last(W.last_ck(rest), ch), NR.spec.last(Some{NR.Ck{kk, ip, ln, p, n}}, ch)), NR.spec.last(Maybe.or(&2, NR.Ck, W.last_ck(rest), Some{NR.Ck{kk, ip, ln, p, n}}), ch),
              Equal.cong(Maybe<&2, R.Item>, Maybe<&2, R.Item>, z => Maybe.or(&2, R.Item, z, Some{R.Item{kk, ip, B.At{ln, ch, NR.pos_text(p, kk)}, ""}}), P.blank(SD.last_item(NR.spec.items(rest, ch, String.drop(t, U32.to_nat(n))))), NR.spec.last(W.last_ck(rest), ch), bl_li(rest, ch, String.drop(t, U32.to_nat(n)))),
              Equal.sym(Maybe<&2, R.Item>, NR.spec.last(Maybe.or(&2, NR.Ck, W.last_ck(rest), Some{NR.Ck{kk, ip, ln, p, n}}), ch), Maybe.or(&2, R.Item, NR.spec.last(W.last_ck(rest), ch), NR.spec.last(Some{NR.Ck{kk, ip, ln, p, n}}, ch)), sp_last_or(W.last_ck(rest), Some{NR.Ck{kk, ip, ln, p, n}}, ch))))

# With S's CHROM the same as T's: the merged run's last (S's buffer's last,
# else S's last) is shiftS's, up to the text.
law last_same:
  for +sf: List<&2, NR.Ck>
  for +sb: List<&2, NR.Ck>
  for +sl: Maybe<&2, NR.Ck>
  for +ch: String
  for +u: String
  {P.blank(NR.spec.last(Maybe.or(&2, NR.Ck, W.buf_last(sf, sb), sl), ch)) == P.blank(Maybe.or(&2, R.Item, SD.last_item(NR.spec.items(NR.append_ck(sf, NR.rev_ck(sb, Nil{})), ch, u)), NR.spec.last(sl, ch))) : Maybe<&2, R.Item>}

def last_same(sf, sb, sl, ch, u):
  +its = NR.append_ck(sf, NR.rev_ck(sb, Nil{}))
  +li = SD.last_item(NR.spec.items(its, ch, u))
  +r0 = P.blank(Maybe.or(&2, R.Item, li, NR.spec.last(sl, ch)))
  +r1 = Maybe.or(&2, R.Item, P.blank(li), P.blank(NR.spec.last(sl, ch)))
  +r2 = Maybe.or(&2, R.Item, NR.spec.last(W.last_ck(its), ch), NR.spec.last(sl, ch))
  +r3 = Maybe.or(&2, R.Item, NR.spec.last(W.buf_last(sf, sb), ch), NR.spec.last(sl, ch))
  +r4 = NR.spec.last(Maybe.or(&2, NR.Ck, W.buf_last(sf, sb), sl), ch)
  +e01 = bl_or(li, NR.spec.last(sl, ch))
  +e12 = Equal.trans(Maybe<&2, R.Item>, r1, Maybe.or(&2, R.Item, NR.spec.last(W.last_ck(its), ch), P.blank(NR.spec.last(sl, ch))), r2,
    Equal.cong(Maybe<&2, R.Item>, Maybe<&2, R.Item>, z => Maybe.or(&2, R.Item, z, P.blank(NR.spec.last(sl, ch))), P.blank(li), NR.spec.last(W.last_ck(its), ch), bl_li(its, ch, u)),
    Equal.cong(Maybe<&2, R.Item>, Maybe<&2, R.Item>, z => Maybe.or(&2, R.Item, NR.spec.last(W.last_ck(its), ch), z), P.blank(NR.spec.last(sl, ch)), NR.spec.last(sl, ch), bl_sp(sl, ch)))
  +e23 = Equal.cong(Maybe<&2, NR.Ck>, Maybe<&2, R.Item>, z => Maybe.or(&2, R.Item, NR.spec.last(z, ch), NR.spec.last(sl, ch)), W.last_ck(its), W.buf_last(sf, sb), ML.last_items(sf, sb))
  +e34 = Equal.sym(Maybe<&2, R.Item>, r4, r3, sp_last_or(W.buf_last(sf, sb), sl, ch))
  +e45 = Equal.sym(Maybe<&2, R.Item>, P.blank(r4), r4, bl_sp(Maybe.or(&2, NR.Ck, W.buf_last(sf, sb), sl), ch))
  Equal.sym(Maybe<&2, R.Item>, r0, P.blank(r4),
    Equal.trans(Maybe<&2, R.Item>, r0, r1, P.blank(r4), e01,
      Equal.trans(Maybe<&2, R.Item>, r1, r2, P.blank(r4), e12,
        Equal.trans(Maybe<&2, R.Item>, r2, r3, P.blank(r4), e23,
          Equal.trans(Maybe<&2, R.Item>, r3, r4, P.blank(r4), e34, e45)))))
