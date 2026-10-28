import Base
import ./types.bend as B
import ./LAWS.bend as L
import ./tan.bend as Tan
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_lines_str.bend as LS
import ./proof_b_lines_pd.bend as LP
import ./proof_b_fa_bytes.bend as FB
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# The judge's text is bytes for a body of bytes (judge_bytes,
# proof_b_adv_slow.bend). Every outcome keeps the body as its text, except
# a normalized record: B.Rec.rebuild puts back the body's fields with POS in
# decimal, REF and ALT as the letters A, C, G, T, N, and INFO's END entry as
# "END=" and decimal digits. The reference's letters never reach the text
# (they are read as bases), so fa_bytes is not needed.

# Decimal digits
# ==============

def dig(+r: Nat, +h: {Nat.is_lt(r, 10n) == True{} : Bool}) ->
  {U32.is_lt(Char.to_u32(Chr{U32.from_nat(Nat.add(48n, r))}), 256) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+r1:
        match r1:
          case 0n:
            {==}
          case 1n+r2:
              match r2:
                case 0n:
                  {==}
                case 1n+r3:
                    match r3:
                      case 0n:
                        {==}
                      case 1n+r4:
                          match r4:
                            case 0n:
                              {==}
                            case 1n+r5:
                                match r5:
                                  case 0n:
                                    {==}
                                  case 1n+r6:
                                      match r6:
                                        case 0n:
                                          {==}
                                        case 1n+r7:
                                            match r7:
                                              case 0n:
                                                {==}
                                              case 1n+r8:
                                                  match r8:
                                                    case 0n:
                                                      {==}
                                                    case 1n+r9:
                                                        match r9:
                                                          case 0n:
                                                            {==}
                                                          case 1n+r10:
                                                              match r10:
                                                                case 0n:
                                                                  Empty.absurd({U32.is_lt(Char.to_u32(Chr{U32.from_nat(Nat.add(48n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+0n))}), 256) == True{} : Bool}, AB.false_ne_true(h))
                                                                case 1n+r11:
                                                                  Empty.absurd({U32.is_lt(Char.to_u32(Chr{U32.from_nat(Nat.add(48n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+r11))}), 256) == True{} : Bool}, AB.false_ne_true(h))
def pair_eta(p: Nat & Nat) -> {p == (Pair.fst(Nat, Nat, p), Pair.snd(Nat, Nat, p)) : Nat & Nat}:
  match p:
    case (+a, +b):
      {==}

def put_eq(+n: Nat) ->
  {Nat.show.put(Nat.divmod(n, 10n)) == (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n))) : Char & Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod(n, 10n), (Pair.fst(Nat, Nat, Nat.divmod(n, 10n)), Pair.snd(Nat, Nat, Nat.divmod(n, 10n))), pair_eta(Nat.divmod(n, 10n))) :
    {Nat.show.put(_) == (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n))) : Char & Nat}
  {==}

def dig_n(+n: Nat) -> {U32.is_lt(Char.to_u32(Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}), 256) == True{} : Bool}:
  dig(Nat.mod(n, 10n), N.mod_lt(n, 10n, {==}))

def show_fin(+g: Nat, +acc: String, +d: Char, +q: Nat,
  +hd: {U32.is_lt(Char.to_u32(d), 256) == True{} : Bool},
  +ha: {E.is_bytes(acc) == True{} : Bool},
  ih: @m: Nat -> @a: String -> @ha2: {E.is_bytes(a) == True{} : Bool} -> {E.is_bytes(Nat.show.go(g, m, a)) == True{} : Bool}) ->
  {E.is_bytes(Nat.show.fin(g, acc, (d, q))) == True{} : Bool}:
  match q:
    case 0n:
      LP.and_tt(U32.is_lt(Char.to_u32(d), 256), E.is_bytes(acc), hd, ha)
    case 1n+p:
      ih(1n+p, SCon{d, acc}, LP.and_tt(U32.is_lt(Char.to_u32(d), 256), E.is_bytes(acc), hd, ha))

def show_go(+f: Nat, +n: Nat, +acc: String, +ha: {E.is_bytes(acc) == True{} : Bool}) ->
  {E.is_bytes(Nat.show.go(f, n, acc)) == True{} : Bool}:
  match f:
    case 0n:
      ha
    case 1n+g:
      %Equal.sym(Char & Nat, Nat.show.put(Nat.divmod(n, 10n)), (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n))), put_eq(n)) :
        {E.is_bytes(Nat.show.fin(g, acc, _)) == True{} : Bool}
      show_fin(g, acc, Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n)), dig_n(n), ha,
        m => a => ha2 => show_go(g, m, a, ha2))

def show_bytes(+n: Nat) -> {E.is_bytes(Nat.show(n)) == True{} : Bool}:
  %Equal.sym(Char & Nat, Nat.show.put(Nat.divmod(n, 10n)), (Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n))), put_eq(n)) :
    {E.is_bytes(Nat.show.fin(n, SNil{}, _)) == True{} : Bool}
  show_fin(n, SNil{}, Chr{U32.from_nat(Nat.add(48n, Nat.mod(n, 10n)))}, Pair.fst(Nat, Nat, Nat.divmod(n, 10n)), dig_n(n), {==},
    m => a => ha2 => show_go(n, m, a, ha2))

# Fields
# ======

def split_sep(+s: String, +sep: Char, +hb: {E.is_bytes(s) == True{} : Bool}) ->
  {E.all_bytes(String.split(s, sep)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      FB.fin_bytes(h, String.split(t, sep), Char.is_eq(h, sep),
        AB.and_true_l(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb),
        split_sep(t, sep, AB.and_true_r(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb)))

def field_bytes(+fs: List<&2, String>, +i: Nat, +h: {E.all_bytes(fs) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.field(fs, i)) == True{} : Bool}:
  match fs i:
    case Nil{} _:
      {==}
    case +f <> +t 0n:
      AB.and_true_l(E.is_bytes(f), E.all_bytes(t), h)
    case +f <> +t 1n+j:
      field_bytes(t, j, AB.and_true_r(E.is_bytes(f), E.all_bytes(t), h))

def put_bytes(+fs: List<&2, String>, +i: Nat, +s: String, +h: {E.all_bytes(fs) == True{} : Bool}, +hs: {E.is_bytes(s) == True{} : Bool}) ->
  {E.all_bytes(B.Rec.put(fs, i, s)) == True{} : Bool}:
  match fs i:
    case Nil{} _:
      {==}
    case +f <> +t 0n:
      LP.and_tt(E.is_bytes(s), E.all_bytes(t), hs, AB.and_true_r(E.is_bytes(f), E.all_bytes(t), h))
    case +f <> +t 1n+j:
      LP.and_tt(E.is_bytes(f), E.all_bytes(B.Rec.put(t, j, s)), AB.and_true_l(E.is_bytes(f), E.all_bytes(t), h),
        put_bytes(t, j, s, AB.and_true_r(E.is_bytes(f), E.all_bytes(t), h), hs))

def join_go(+xs: List<&2, String>, +h: String, +sep: String, +hx: {E.all_bytes(xs) == True{} : Bool},
  +hh: {E.is_bytes(h) == True{} : Bool}, +hs: {E.is_bytes(sep) == True{} : Bool}) ->
  {E.is_bytes(String.join.go(xs, h, sep)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hh
    case +h2 <> +t:
      LS.bytes_app(h, String.append(sep, String.join.go(t, h2, sep)), hh,
        LS.bytes_app(sep, String.join.go(t, h2, sep), hs,
          join_go(t, h2, sep, AB.and_true_r(E.is_bytes(h2), E.all_bytes(t), hx), AB.and_true_l(E.is_bytes(h2), E.all_bytes(t), hx), hs)))

def join_bytes(+xs: List<&2, String>, +sep: String, +hx: {E.all_bytes(xs) == True{} : Bool}, +hs: {E.is_bytes(sep) == True{} : Bool}) ->
  {E.is_bytes(String.join(xs, sep)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      join_go(t, h, sep, AB.and_true_r(E.is_bytes(h), E.all_bytes(t), hx), AB.and_true_l(E.is_bytes(h), E.all_bytes(t), hx), hs)

# Alleles and INFO
# ================

def letter_bytes(+x: B.Base) -> {U32.is_lt(Char.to_u32(B.Base.letter(x)), 256) == True{} : Bool}:
  match x:
    case B.A{}:
      {==}
    case B.C{}:
      {==}
    case B.G{}:
      {==}
    case B.T{}:
      {==}
    case B.N{}:
      {==}

def allele_bytes(+xs: List<&2, B.Base>) -> {E.is_bytes(B.Allele.show(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      LP.and_tt(U32.is_lt(Char.to_u32(B.Base.letter(x)), 256), E.is_bytes(B.Allele.show(t)), letter_bytes(x), allele_bytes(t))

def alleles_bytes(+ys: List<&2, List<&2, B.Base>>) -> {E.all_bytes(B.Alleles.show(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      LP.and_tt(E.is_bytes(B.Allele.show(y)), E.all_bytes(B.Alleles.show(t)), allele_bytes(y), alleles_bytes(t))

def set_put(+b: Bool, +p: String, +e: Nat, +hp: {E.is_bytes(p) == True{} : Bool}) ->
  {E.is_bytes(B.Info.set_end.put(b, p, e)) == True{} : Bool}:
  match b:
    case True{}:
      LS.bytes_app("END=", Nat.show(e), {==}, show_bytes(e))
    case False{}:
      hp

def set_go(+ps: List<&2, String>, +e: Nat, +h: {E.all_bytes(ps) == True{} : Bool}) ->
  {E.all_bytes(B.Info.set_end.go(ps, e)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      LP.and_tt(E.is_bytes(B.Info.set_end.put(String.eq(B.Info.key(p), "END"), p, e)), E.all_bytes(B.Info.set_end.go(t, e)),
        set_put(String.eq(B.Info.key(p), "END"), p, e, AB.and_true_l(E.is_bytes(p), E.all_bytes(t), h)),
        set_go(t, e, AB.and_true_r(E.is_bytes(p), E.all_bytes(t), h)))

def info_bytes(+mv: Bool, +info: String, +w: B.Var, +hi: {E.is_bytes(info) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.info(mv, info, w)) == True{} : Bool}:
  match mv w:
    case True{} B.Var{+q, +s, +y}:
      join_bytes(B.Info.set_end.go(String.split(info, ';'), Nat.sub(Nat.add(q, List.length(&2, B.Base, s)), 1n)), ";",
        set_go(String.split(info, ';'), Nat.sub(Nat.add(q, List.length(&2, B.Base, s)), 1n), split_sep(info, ';', hi)), {==})
    case False{} _:
      hi

# The rebuilt record
# ==================

def rebuild_bytes(+fs: List<&2, String>, +v: B.Var, +w: B.Var, +h: {E.all_bytes(fs) == True{} : Bool}) ->
  {E.is_bytes(B.Rec.rebuild(fs, v, w)) == True{} : Bool}:
  match w:
    case B.Var{+q, +s, +y}:
      +info = B.Rec.info(B.Rec.moved(v, B.Var{q, s, y}), B.Rec.field(fs, 7n), B.Var{q, s, y})
      +f1 = B.Rec.put(fs, 1n, Nat.show(q))
      +f3 = B.Rec.put(f1, 3n, B.Allele.show(s))
      +f4 = B.Rec.put(f3, 4n, String.join(B.Alleles.show(y), ","))
      +h1 = put_bytes(fs, 1n, Nat.show(q), h, show_bytes(q))
      +h3 = put_bytes(f1, 3n, B.Allele.show(s), h1, allele_bytes(s))
      +h4 = put_bytes(f3, 4n, String.join(B.Alleles.show(y), ","), h3, join_bytes(B.Alleles.show(y), ",", alleles_bytes(y), {==}))
      +h7 = put_bytes(f4, 7n, info, h4, info_bytes(B.Rec.moved(v, B.Var{q, s, y}), B.Rec.field(fs, 7n), B.Var{q, s, y}, field_bytes(fs, 7n, h)))
      join_bytes(B.Rec.put(f4, 7n, info), "\t", h7, {==})

# The judge
# =========

def jt_problem(+c: Maybe<&2, B.Code>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var,
  +hfs: {E.all_bytes(fs) == True{} : Bool}, +hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.problem(c, fs, body, seq, v))) == True{} : Bool}:
  match c:
    case Some{+k}:
      hbd
    case None{}:
      rebuild_bytes(fs, v, Tan.normal(seq, v), hfs)

def jt_bases(+eo: Bool, +r: Maybe<&2, List<&2, B.Base>>, +a: Maybe<&2, List<&2, List<&2, B.Base>>>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>,
  +hfs: {E.all_bytes(fs) == True{} : Bool}, +hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge.bases(eo, r, a, fs, body, seq))) == True{} : Bool}:
  match r a:
    case Some{+ref} Some{+alts}:
      jt_problem(L.checks(eo, seq, B.Var{B.Rec.pos(fs), ref, alts}), fs, body, seq, B.Var{B.Rec.pos(fs), ref, alts}, hfs, hbd)
    case Some{+ref} None{}:
      hbd
    case None{} _:
      hbd

def jt_contig(+m: Maybe<&2, String>, +fs: List<&2, String>, +body: String,
  +hfs: {E.all_bytes(fs) == True{} : Bool}, +hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge.contig(m, fs, body))) == True{} : Bool}:
  match m:
    case None{}:
      hbd
    case Some{+raw}:
      jt_bases(B.Info.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(B.Rec.pos(fs), String.length(B.Rec.field(fs, 3n))), 1n)),
        B.Allele.read(B.Rec.field(fs, 3n)), B.Alleles.read(B.Rec.alts(fs)), fs, body, B.Bases.of_fasta(raw), hfs, hbd)

def jt_shape(+bad: Bool, +skip: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String,
  +hfs: {E.all_bytes(fs) == True{} : Bool}, +hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge.shape(bad, skip, fa, fs, body))) == True{} : Bool}:
  match bad skip:
    case True{} _:
      hbd
    case False{} True{}:
      hbd
    case False{} False{}:
      jt_contig(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body, hfs, hbd)

# judge_bytes, as proof_b_adv_slow.bend states it (fa_bytes unused).
def judge_bytes(+fa: List<&2, B.Contig>, +body: String,
  +hb: {PC.fa_bytes(fa) == True{} : Bool},
  +hbd: {E.is_bytes(body) == True{} : Bool}) ->
  {E.is_bytes(P.res_text(L.judge(fa, body))) == True{} : Bool}:
  +fs = B.Rec.fields(body)
  jt_shape(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, fs, body, split_sep(body, '\t', hbd), hbd)
