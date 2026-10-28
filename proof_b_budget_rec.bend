import Base
import ./types.bend as B
import ./tan.bend as V
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_rec.bend as C
import ./proof_run_text.bend as X
import ./proof_run_line.bend as RL
import ./proof_b_budget_tan.bend as T
import ./proof_b_budget_dig.bend as G
import ../lawful-words/proof_nat.bend as N
import ../lawful-arrays/proof_base.bend as AB

# A rewritten record is at most 10 (|body| + 1) + 10 bytes long
# (notes/bytes_proofs_budget.md, the output-length bound).

# ---------------------------------------------------------------------------
# Field lists: SN(xs) = sum of (1 + |x|)
# ---------------------------------------------------------------------------

def SN(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      1n+Nat.add(String.length(x), SN(t))

def SL(+s: String) -> Nat:
  String.length(s)

def sf(+h: Char, cut: Bool, ps: List<&2, String>, +t: String, +ih: {SN(ps) == 1n+SL(t) : Nat},
  ne: {ps == Nil{} : List<&2, String>} -> Empty) -> {SN(String.split.fin(h, ps, cut)) == 1n+(1n+SL(t)) : Nat}:
  match cut:
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, SN(ps), 1n+SL(t), ih)
    case False{}:
      match ps:
        case Nil{}:
          Empty.absurd({SN(String.split.push(h, Nil{})) == 1n+(1n+SL(t)) : Nat}, ne({==}))
        case p <> r:
          Equal.cong(Nat, Nat, z => 1n+z, SN(p <> r), 1n+SL(t), ih)

# The pieces of s cut at c: their lengths plus one per piece make |s| + 1.
def split_sn(+s: String, +c: Char) -> {SN(String.split(s, c)) == 1n+SL(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      sf(h, Char.is_eq(h, c), String.split(t, c), t, split_sn(t, c), e => X.split_nn(t, c, e))

def field_le(xs: List<&2, String>, +i: Nat) -> {Nat.is_le(SL(B.Rec.field(xs, i)), SN(xs)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{+x, +t} 0n:
      N.le_trans(SL(x), Nat.add(SL(x), SN(t)), 1n+Nat.add(SL(x), SN(t)), N.le_add_r(SL(x), SN(t)), N.le_add_l(Nat.add(SL(x), SN(t)), 1n))
    case Con{+x, +t} 1n+j:
      N.le_trans(SL(B.Rec.field(t, j)), SN(t), 1n+Nat.add(SL(x), SN(t)), field_le(t, j),
        N.le_trans(SN(t), Nat.add(SL(x), SN(t)), 1n+Nat.add(SL(x), SN(t)), N.le_add_l(SN(t), SL(x)), N.le_add_l(Nat.add(SL(x), SN(t)), 1n)))

def put_le(xs: List<&2, String>, +i: Nat, +s: String) -> {Nat.is_le(SN(B.Rec.put(xs, i, s)), Nat.add(SN(xs), SL(s))) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      N.le_zero_l(SL(s))
    case Con{+f, +t} 0n:
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.add(SL(f), SN(t)), SL(s))) == True{} : Bool}, Nat.add(SN(t), SL(s)), Nat.add(SL(s), SN(t)),
        N.add_comm(SN(t), SL(s)), N.le_add_mono_r(SL(s), SN(t), Nat.add(SL(f), SN(t)), N.le_add_l(SN(t), SL(f))))
    case Con{+f, +t} 1n+j:
      AB.subst(Nat, z => {Nat.is_le(Nat.add(SL(f), SN(B.Rec.put(t, j, s))), z) == True{} : Bool}, Nat.add(SL(f), Nat.add(SN(t), SL(s))), Nat.add(Nat.add(SL(f), SN(t)), SL(s)),
        Equal.sym(Nat, Nat.add(Nat.add(SL(f), SN(t)), SL(s)), Nat.add(SL(f), Nat.add(SN(t), SL(s))), N.add_assoc(SL(f), SN(t), SL(s))),
        N.le_add_mono_l(SL(f), SN(B.Rec.put(t, j, s)), Nat.add(SN(t), SL(s)), put_le(t, j, s)))

def jg(t: List<&2, String>, +h: String, +sep: String, +hs: {SL(sep) == 1n : Nat}) -> {Nat.is_le(SL(String.join.go(t, h, sep)), Nat.add(SL(h), SN(t))) == True{} : Bool}:
  match t:
    case Nil{}:
      AB.subst(Nat, z => {Nat.is_le(SL(h), z) == True{} : Bool}, SL(h), Nat.add(SL(h), 0n), Equal.sym(Nat, Nat.add(SL(h), 0n), SL(h), N.add_zero(SL(h))), N.le_refl(SL(h)))
    case +x <> +r:
      +J = String.join.go(r, x, sep)
      +e1 = Equal.trans(Nat, SL(h ++ (sep ++ J)), Nat.add(SL(h), SL(sep ++ J)), Nat.add(SL(h), Nat.add(SL(sep), SL(J))),
        G.slen_app(h, sep ++ J), Equal.cong(Nat, Nat, z => Nat.add(SL(h), z), SL(sep ++ J), Nat.add(SL(sep), SL(J)), G.slen_app(sep, J)))
      +e2 = Equal.trans(Nat, SL(h ++ (sep ++ J)), Nat.add(SL(h), Nat.add(SL(sep), SL(J))), Nat.add(SL(h), 1n+SL(J)), e1,
        Equal.cong(Nat, Nat, z => Nat.add(SL(h), Nat.add(z, SL(J))), SL(sep), 1n, hs))
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(SL(h), 1n+Nat.add(SL(x), SN(r)))) == True{} : Bool}, Nat.add(SL(h), 1n+SL(J)), SL(h ++ (sep ++ J)),
        Equal.sym(Nat, SL(h ++ (sep ++ J)), Nat.add(SL(h), 1n+SL(J)), e2),
        N.le_add_mono_l(SL(h), 1n+SL(J), 1n+Nat.add(SL(x), SN(r)), jg(r, x, sep, hs)))

# Joining with a one-character separator: at most SN(xs) characters.
def join_le(xs: List<&2, String>, +sep: String, +hs: {SL(sep) == 1n : Nat}) -> {Nat.is_le(SL(String.join(xs, sep)), SN(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      N.le_trans(SL(String.join.go(t, h, sep)), Nat.add(SL(h), SN(t)), 1n+Nat.add(SL(h), SN(t)), jg(t, h, sep, hs), N.le_add_l(Nat.add(SL(h), SN(t)), 1n))

# ---------------------------------------------------------------------------
# Alleles: ASN(ys) = sum of (1 + len y)
# ---------------------------------------------------------------------------

def ASN(ys: List<&2, List<&2, B.Base>>) -> Nat:
  match ys:
    case Nil{}:
      0n
    case y <> t:
      1n+Nat.add(T.lenb(y), ASN(t))

def shows_sn(ys: List<&2, List<&2, B.Base>>) -> {SN(B.Alleles.show(ys)) == ASN(ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(SL(B.Allele.show(y)), SN(B.Alleles.show(t))), Nat.add(T.lenb(y), ASN(t)),
        Equal.trans(Nat, Nat.add(SL(B.Allele.show(y)), SN(B.Alleles.show(t))), Nat.add(T.lenb(y), SN(B.Alleles.show(t))), Nat.add(T.lenb(y), ASN(t)),
          Equal.cong(Nat, Nat, z => Nat.add(z, SN(B.Alleles.show(t))), SL(B.Allele.show(y)), T.lenb(y), C.show_len(y)),
          Equal.cong(Nat, Nat, z => Nat.add(T.lenb(y), z), SN(B.Alleles.show(t)), ASN(t), shows_sn(t))))

def asn_tot(ys: List<&2, List<&2, B.Base>>) -> {ASN(ys) == Nat.add(V.total(ys), T.nals(ys)) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +a = T.lenb(y)
      +b = V.total(t)
      +c = T.nals(t)
      Equal.trans(Nat, 1n+Nat.add(a, ASN(t)), 1n+Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), 1n+c),
        Equal.cong(Nat, Nat, z => 1n+Nat.add(a, z), ASN(t), Nat.add(b, c), asn_tot(t)),
        Equal.trans(Nat, 1n+Nat.add(a, Nat.add(b, c)), 1n+Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, b), 1n+c),
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), N.add_assoc(a, b, c))),
          Equal.sym(Nat, Nat.add(Nat.add(a, b), 1n+c), 1n+Nat.add(Nat.add(a, b), c), N.add_succ(Nat.add(a, b), c))))

def asm(m: Maybe<&2, List<&2, List<&2, B.Base>>>, +n: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{ys}:
      Nat.is_eq(ASN(ys), n)

def rs.k(+x: String, a: Maybe<&2, List<&2, B.Base>>, +ea: {B.Allele.read(x) == a : Maybe<&2, List<&2, B.Base>>},
  r: Maybe<&2, List<&2, List<&2, B.Base>>>, +n: Nat, +ih: {asm(r, n) == True{} : Bool}) ->
  {asm(B.Alleles.read.cons(a, r), 1n+Nat.add(SL(x), n)) == True{} : Bool}:
  match a r:
    case Some{+bs} Some{+ys}:
      +e0 = P.eq_sound(ASN(ys), n, ih)
      +e1 = Equal.trans(Nat, 1n+Nat.add(T.lenb(bs), ASN(ys)), 1n+Nat.add(SL(x), ASN(ys)), 1n+Nat.add(SL(x), n),
        Equal.cong(Nat, Nat, z => 1n+Nat.add(z, ASN(ys)), T.lenb(bs), SL(x), Equal.sym(Nat, SL(x), T.lenb(bs), C.read_len(x, bs, ea))),
        Equal.cong(Nat, Nat, z => 1n+Nat.add(SL(x), z), ASN(ys), n, e0))
      AB.subst(Nat, z => {Nat.is_eq(z, 1n+Nat.add(SL(x), n)) == True{} : Bool}, 1n+Nat.add(SL(x), n), 1n+Nat.add(T.lenb(bs), ASN(ys)),
        Equal.sym(Nat, 1n+Nat.add(T.lenb(bs), ASN(ys)), 1n+Nat.add(SL(x), n), e1), N.eq_refl(1n+Nat.add(SL(x), n)))
    case None{} _:
      {==}
    case Some{bs} None{}:
      {==}

def read_asm(xs: List<&2, String>) -> {asm(B.Alleles.read(xs), SN(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      rs.k(x, B.Allele.read(x), {==}, B.Alleles.read(t), SN(t), read_asm(t))

# Alleles read from pieces: ASN of the alleles is SN of the pieces.
def read_sn(+xs: List<&2, String>, +ys: List<&2, List<&2, B.Base>>, +e: {B.Alleles.read(xs) == Some{ys} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {ASN(ys) == SN(xs) : Nat}:
  P.eq_sound(ASN(ys), SN(xs), AB.subst(Maybe<&2, List<&2, List<&2, B.Base>>>, z => {asm(z, SN(xs)) == True{} : Bool}, B.Alleles.read(xs), Some{ys}, e, read_asm(xs)))

# ---------------------------------------------------------------------------
# INFO: with at most one END entry, setting END adds at most 5 + digits
# ---------------------------------------------------------------------------

def RP(ms: List<&2, Maybe<&2, Nat>>, +k: Nat) -> Nat:
  match ms:
    case Nil{}:
      0n
    case m <> t:
      Nat.add(k, RP(t, k))

def XE(+e: Nat) -> Nat:
  4n+SL(Nat.show(e))

def se.k(b: Bool, +p: String, +t: List<&2, String>, +e: Nat,
  +ih: {Nat.is_le(SN(B.Info.set_end.go(t, e)), Nat.add(SN(t), RP(B.Info.ends.go(t), XE(e)))) == True{} : Bool}) ->
  {Nat.is_le(SN(B.Info.set_end.put(b, p, e) <> B.Info.set_end.go(t, e)), Nat.add(SN(p <> t), RP(B.Info.ends.put(b, p, B.Info.ends.go(t)), XE(e)))) == True{} : Bool}:
  match b:
    case False{}:
      +S2 = SN(B.Info.set_end.go(t, e))
      +R = RP(B.Info.ends.go(t), XE(e))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(SL(p), S2), z) == True{} : Bool}, Nat.add(SL(p), Nat.add(SN(t), R)), Nat.add(Nat.add(SL(p), SN(t)), R),
        Equal.sym(Nat, Nat.add(Nat.add(SL(p), SN(t)), R), Nat.add(SL(p), Nat.add(SN(t), R)), N.add_assoc(SL(p), SN(t), R)),
        N.le_add_mono_l(SL(p), S2, Nat.add(SN(t), R), ih))
    case True{}:
      +S2 = SN(B.Info.set_end.go(t, e))
      +R = RP(B.Info.ends.go(t), XE(e))
      +X = XE(e)
      +Y = Nat.add(SN(t), R)
      +h1 = N.le_trans(Nat.add(X, S2), Nat.add(X, Y), Nat.add(SL(p), Nat.add(X, Y)), N.le_add_mono_l(X, S2, Y, ih), N.le_add_l(Nat.add(X, Y), SL(p)))
      +e1 = Equal.trans(Nat, Nat.add(SL(p), Nat.add(X, Y)), Nat.add(SL(p), Nat.add(SN(t), Nat.add(X, R))), Nat.add(Nat.add(SL(p), SN(t)), Nat.add(X, R)),
        Equal.cong(Nat, Nat, z => Nat.add(SL(p), z), Nat.add(X, Y), Nat.add(SN(t), Nat.add(X, R)), N.add_left_comm(X, SN(t), R)),
        Equal.sym(Nat, Nat.add(Nat.add(SL(p), SN(t)), Nat.add(X, R)), Nat.add(SL(p), Nat.add(SN(t), Nat.add(X, R))), N.add_assoc(SL(p), SN(t), Nat.add(X, R))))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(X, S2), z) == True{} : Bool}, Nat.add(SL(p), Nat.add(X, Y)), Nat.add(Nat.add(SL(p), SN(t)), Nat.add(X, R)), e1, h1)

def se_le(ps: List<&2, String>, +e: Nat) -> {Nat.is_le(SN(B.Info.set_end.go(ps, e)), Nat.add(SN(ps), RP(B.Info.ends.go(ps), XE(e)))) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      se.k(String.eq(B.Info.key(p), "END"), p, t, e, se_le(t, e))

def one.k(m: Maybe<&2, Nat>, t: List<&2, Maybe<&2, Nat>>, +e0: Nat, +k: Nat, +h: {B.Info.end_ok.go(m <> t, e0) == True{} : Bool}) ->
  {Nat.is_le(RP(m <> t, k), k) == True{} : Bool}:
  match m t:
    case Some{v} Nil{}:
      AB.subst(Nat, z => {Nat.is_le(z, k) == True{} : Bool}, k, Nat.add(k, 0n), Equal.sym(Nat, Nat.add(k, 0n), k, N.add_zero(k)), N.le_refl(k))
    case Some{v} Con{u, r}:
      Empty.absurd({Nat.is_le(RP(Some{v} <> (u <> r), k), k) == True{} : Bool}, N.false_ne_true(h))
    case None{} _:
      Empty.absurd({Nat.is_le(RP(None{} <> t, k), k) == True{} : Bool}, N.false_ne_true(h))

def end_one(ms: List<&2, Maybe<&2, Nat>>, +e0: Nat, +k: Nat, +h: {B.Info.end_ok.go(ms, e0) == True{} : Bool}) -> {Nat.is_le(RP(ms, k), k) == True{} : Bool}:
  match ms:
    case Nil{}:
      N.le_zero_l(k)
    case m <> t:
      one.k(m, t, e0, k, h)

# Setting END in an INFO whose END test passed adds at most 5 + digits(e) bytes.
def info_le(+info: String, +e: Nat, +e0: Nat, +h: {B.Info.end_ok(info, e0) == True{} : Bool}) ->
  {Nat.is_le(SL(B.Info.set_end(info, e)), Nat.add(1n+SL(info), XE(e))) == True{} : Bool}:
  +ps = String.split(info, ';')
  +S2 = B.Info.set_end.go(ps, e)
  +h1 = N.le_trans(SL(String.join(S2, ";")), SN(S2), Nat.add(SN(ps), RP(B.Info.ends.go(ps), XE(e))), join_le(S2, ";", {==}), se_le(ps, e))
  +h2 = N.le_trans(SL(String.join(S2, ";")), Nat.add(SN(ps), RP(B.Info.ends.go(ps), XE(e))), Nat.add(SN(ps), XE(e)), h1,
    N.le_add_mono_l(SN(ps), RP(B.Info.ends.go(ps), XE(e)), XE(e), end_one(B.Info.ends.go(ps), e0, XE(e), h)))
  AB.subst(Nat, z => {Nat.is_le(SL(String.join(S2, ";")), Nat.add(z, XE(e))) == True{} : Bool}, SN(ps), 1n+SL(info), split_sn(info, ';'), h2)

def rinfo(mv: Bool, +info: String, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>, +e0: Nat, +h: {B.Info.end_ok(info, e0) == True{} : Bool}) ->
  {Nat.is_le(SL(B.Rec.info(mv, info, B.Var{q, s, y})), Nat.add(1n+SL(info), XE(Nat.sub(Nat.add(q, T.lenb(s)), 1n)))) == True{} : Bool}:
  match mv:
    case True{}:
      info_le(info, Nat.sub(Nat.add(q, T.lenb(s)), 1n), e0, h)
    case False{}:
      N.le_trans(SL(info), 1n+SL(info), Nat.add(1n+SL(info), XE(Nat.sub(Nat.add(q, T.lenb(s)), 1n))), N.le_add_l(SL(info), 1n),
        N.le_add_r(1n+SL(info), XE(Nat.sub(Nat.add(q, T.lenb(s)), 1n))))

# ---------------------------------------------------------------------------
# The rewritten record
# ---------------------------------------------------------------------------

def bnd_e(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>, h: T.BND(p1, a1, p2, a2)) ->
  {Nat.is_le(Nat.add(p2, T.hd(a2)), Nat.add(p1, T.hd(a1))) == True{} : Bool}:
  match h:
    case (e, r):
      e

def bnd_t(+p1: Nat, +a1: List<&2, List<&2, B.Base>>, +p2: Nat, +a2: List<&2, List<&2, B.Base>>, h: T.BND(p1, a1, p2, a2)) ->
  {Nat.is_le(V.total(a2), V.total(a1)) == True{} : Bool}:
  match h:
    case (e, r):
      match r:
        case (t, q):
          t

def lin_v1(+a: Nat, +x: Nat, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(1n+a, G.LIN(1n, 1n, x)) == True{} : Bool}:
  AB.subst(Nat, z => {Nat.is_le(z, Nat.add(x, 1n)) == True{} : Bool}, Nat.add(a, 1n), 1n+a, N.add_one(a), N.le_add_mono_r(1n, a, x, h))

def ASNv(+ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, +f4: String,
  +ea: {B.Alleles.read(String.split(f4, ',')) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}) -> {ASN(ref <> alts) == 1n+Nat.add(T.lenb(ref), 1n+SL(f4)) : Nat}:
  Equal.cong(Nat, Nat, z => 1n+Nat.add(T.lenb(ref), z), ASN(alts), 1n+SL(f4),
    Equal.trans(Nat, ASN(alts), SN(String.split(f4, ',')), 1n+SL(f4), read_sn(String.split(f4, ','), alts, ea), split_sn(f4, ',')))

# The record rewritten for w (end, letters and allele count bounded by v's)
# has at most LIN(10, 10, SN(fs)) bytes.
def rb.k(+fs: List<&2, String>, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>,
  +he1: {Nat.is_le(Nat.add(q, T.lenb(s)), Nat.add(B.Rec.pos(fs), T.lenb(ref))) == True{} : Bool},
  +ht: {Nat.is_le(V.total(s <> y), V.total(ref <> alts)) == True{} : Bool},
  +hn: {T.nals(s <> y) == T.nals(ref <> alts) : Nat},
  +e0: Nat, +he: {B.Info.end_ok(B.Rec.field(fs, 7n), e0) == True{} : Bool},
  +er: {B.Allele.read(B.Rec.field(fs, 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(fs)) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {Nat.is_le(SL(B.Rec.rebuild(fs, B.Var{B.Rec.pos(fs), ref, alts}, B.Var{q, s, y})), G.LIN(10n, 10n, SN(fs))) == True{} : Bool}:
  +p = B.Rec.pos(fs)
  +B1 = SN(fs)
  +f1 = B.Rec.field(fs, 1n)
  +f3 = B.Rec.field(fs, 3n)
  +f4 = B.Rec.field(fs, 4n)
  +f7 = B.Rec.field(fs, 7n)
  +R = T.lenb(ref)
  +hR = AB.subst(Nat, z => {Nat.is_le(z, B1) == True{} : Bool}, SL(f3), R, C.read_len(f3, ref, er), field_le(fs, 3n))
  +hf1 = field_le(fs, 1n)
  +hf4 = field_le(fs, 4n)
  +hf7 = field_le(fs, 7n)
  +hpr = N.le_trans(Nat.add(q, T.lenb(s)), Nat.add(p, R), Nat.add(p, R), he1, N.le_refl(Nat.add(p, R)))
  +hq = N.le_trans(q, Nat.add(q, T.lenb(s)), Nat.add(p, R), N.le_add_r(q, T.lenb(s)), hpr)
  +L2 = G.lin_add(R, SL(f1), 1n, 0n, 1n, 0n, B1, G.lin_v(R, B1, hR), G.lin_v(SL(f1), B1, hf1))
  +Q = SL(Nat.show(q))
  +LQ = G.lin_add(1n, Nat.add(R, SL(f1)), 0n, 1n, 2n, 0n, B1, {==}, L2)
  +hQ = N.le_trans(Q, 1n+Nat.add(R, SL(f1)), G.LIN(2n, 1n, B1), G.qdig(p, R, SL(f1), q, G.pos_lt(f1), hq), LQ)
  +AV = ASNv(ref, alts, f4, ea)
  +hAV = AB.subst(Nat, z => {Nat.is_le(Nat.add(V.total(s <> y), T.nals(s <> y)), z) == True{} : Bool}, Nat.add(V.total(ref <> alts), T.nals(ref <> alts)), ASN(ref <> alts),
    Equal.sym(Nat, ASN(ref <> alts), Nat.add(V.total(ref <> alts), T.nals(ref <> alts)), asn_tot(ref <> alts)),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(V.total(s <> y), T.nals(s <> y)), Nat.add(V.total(ref <> alts), z)) == True{} : Bool}, T.nals(s <> y), T.nals(ref <> alts), hn,
      N.le_add_mono_r(T.nals(s <> y), V.total(s <> y), V.total(ref <> alts), ht)))
  +hW = AB.subst(Nat, z => {Nat.is_le(z, ASN(ref <> alts)) == True{} : Bool}, Nat.add(V.total(s <> y), T.nals(s <> y)), ASN(s <> y),
    Equal.sym(Nat, ASN(s <> y), Nat.add(V.total(s <> y), T.nals(s <> y)), asn_tot(s <> y)), hAV)
  +L4 = G.lin_add(R, 1n+SL(f4), 1n, 0n, 1n, 1n, B1, G.lin_v(R, B1, hR), lin_v1(SL(f4), B1, hf4))
  +LV = G.lin_add(1n, Nat.add(R, 1n+SL(f4)), 0n, 1n, 2n, 1n, B1, {==}, L4)
  +hV = AB.subst(Nat, z => {Nat.is_le(z, G.LIN(2n, 2n, B1)) == True{} : Bool}, 1n+Nat.add(R, 1n+SL(f4)), ASN(ref <> alts), Equal.sym(Nat, ASN(ref <> alts), 1n+Nat.add(R, 1n+SL(f4)), AV), LV)
  +hY = N.le_trans(ASN(y), Nat.add(T.lenb(s), ASN(y)), ASN(s <> y), N.le_add_l(ASN(y), T.lenb(s)), N.le_add_l(Nat.add(T.lenb(s), ASN(y)), 1n))
  +Jy = String.join(B.Alleles.show(y), ",")
  +hJ0 = AB.subst(Nat, z => {Nat.is_le(SL(Jy), z) == True{} : Bool}, SN(B.Alleles.show(y)), ASN(y), shows_sn(y), join_le(B.Alleles.show(y), ",", {==}))
  +hJ = N.le_trans(SL(Jy), ASN(y), G.LIN(2n, 2n, B1), hJ0, N.le_trans(ASN(y), ASN(s <> y), G.LIN(2n, 2n, B1), hY, N.le_trans(ASN(s <> y), ASN(ref <> alts), G.LIN(2n, 2n, B1), hW, hV)))
  +hS0 = N.le_trans(T.lenb(s), Nat.add(T.lenb(s), V.total(y)), V.total(ref <> alts), N.le_add_r(T.lenb(s), V.total(y)), ht)
  +hTa = N.le_trans(V.total(alts), Nat.add(V.total(alts), T.nals(alts)), 1n+SL(f4), N.le_add_r(V.total(alts), T.nals(alts)),
    AB.subst(Nat, z => {Nat.is_le(z, 1n+SL(f4)) == True{} : Bool}, ASN(alts), Nat.add(V.total(alts), T.nals(alts)), asn_tot(alts),
      AB.subst(Nat, z => {Nat.is_le(ASN(alts), z) == True{} : Bool}, SN(String.split(f4, ',')), 1n+SL(f4), split_sn(f4, ','),
        AB.subst(Nat, z => {Nat.is_le(ASN(alts), z) == True{} : Bool}, ASN(alts), SN(String.split(f4, ',')), read_sn(String.split(f4, ','), alts, ea), N.le_refl(ASN(alts))))))
  +hS1 = N.le_trans(T.lenb(s), V.total(ref <> alts), Nat.add(R, 1n+SL(f4)), hS0, N.le_add_mono_l(R, V.total(alts), 1n+SL(f4), hTa))
  +hS = AB.subst(Nat, z => {Nat.is_le(z, G.LIN(2n, 1n, B1)) == True{} : Bool}, T.lenb(s), SL(B.Allele.show(s)), Equal.sym(Nat, SL(B.Allele.show(s)), T.lenb(s), C.show_len(s)),
    N.le_trans(T.lenb(s), Nat.add(R, 1n+SL(f4)), G.LIN(2n, 1n, B1), hS1, L4))
  +e2 = Nat.sub(Nat.add(q, T.lenb(s)), 1n)
  +he2 = N.le_trans(e2, Nat.add(q, T.lenb(s)), Nat.add(p, R), T.sub_le(Nat.add(q, T.lenb(s)), 1n), hpr)
  +hD = N.le_trans(SL(Nat.show(e2)), 1n+Nat.add(R, SL(f1)), G.LIN(2n, 1n, B1), G.qdig(p, R, SL(f1), e2, G.pos_lt(f1), he2), LQ)
  +hX = G.lin_add(4n, SL(Nat.show(e2)), 0n, 4n, 2n, 1n, B1, {==}, hD)
  +LI = G.lin_add(1n+SL(f7), XE(e2), 1n, 1n, 2n, 5n, B1, lin_v1(SL(f7), B1, hf7), hX)
  +W = {B.Var{q, s, y} : B.Var}
  +mv = B.Rec.moved(B.Var{p, ref, alts}, W)
  +I2 = B.Rec.info(mv, f7, W)
  +hI = N.le_trans(SL(I2), Nat.add(1n+SL(f7), XE(e2)), G.LIN(3n, 6n, B1), rinfo(mv, f7, q, s, y, e0, he), LI)
  +F1 = B.Rec.put(fs, 1n, Nat.show(q))
  +F2 = B.Rec.put(F1, 3n, B.Allele.show(s))
  +F3 = B.Rec.put(F2, 4n, Jy)
  +F4 = B.Rec.put(F3, 7n, I2)
  +h1 = N.le_trans(SN(F1), Nat.add(B1, Q), G.LIN(3n, 1n, B1), put_le(fs, 1n, Nat.show(q)), G.lin_add(B1, Q, 1n, 0n, 2n, 1n, B1, G.lin_v(B1, B1, N.le_refl(B1)), hQ))
  +h2 = N.le_trans(SN(F2), Nat.add(SN(F1), SL(B.Allele.show(s))), G.LIN(5n, 2n, B1), put_le(F1, 3n, B.Allele.show(s)),
    G.lin_add(SN(F1), SL(B.Allele.show(s)), 3n, 1n, 2n, 1n, B1, h1, hS))
  +h3 = N.le_trans(SN(F3), Nat.add(SN(F2), SL(Jy)), G.LIN(7n, 4n, B1), put_le(F2, 4n, Jy), G.lin_add(SN(F2), SL(Jy), 5n, 2n, 2n, 2n, B1, h2, hJ))
  +h4 = N.le_trans(SN(F4), Nat.add(SN(F3), SL(I2)), G.LIN(10n, 10n, B1), put_le(F3, 7n, I2), G.lin_add(SN(F3), SL(I2), 7n, 4n, 3n, 6n, B1, h3, hI))
  N.le_trans(SL(String.join(F4, "\t")), SN(F4), G.LIN(10n, 10n, B1), join_le(F4, "\t", {==}), h4)

def rb_bound(+fs: List<&2, String>, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, w: B.Var,
  h1: T.VB(B.Rec.pos(fs), ref <> alts, w), h2: T.VB(B.Rec.pos(fs), ref <> alts, w), h3: T.VB(B.Rec.pos(fs), ref <> alts, w),
  +e0: Nat, +he: {B.Info.end_ok(B.Rec.field(fs, 7n), e0) == True{} : Bool},
  +er: {B.Allele.read(B.Rec.field(fs, 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(fs)) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  {Nat.is_le(SL(B.Rec.rebuild(fs, B.Var{B.Rec.pos(fs), ref, alts}, w)), G.LIN(10n, 10n, SN(fs))) == True{} : Bool}:
  match w:
    case B.Var{+q, +s, +y}:
      +p = B.Rec.pos(fs)
      rb.k(fs, ref, alts, q, s, y, bnd_e(p, ref <> alts, q, s <> y, h1), bnd_t(p, ref <> alts, q, s <> y, h2), T.bnd_n(p, ref <> alts, q, s <> y, h3), e0, he, er, ea)

def ane_nz(xs: List<&2, List<&2, B.Base>>, +h: {L.all_nonempty(xs) == True{} : Bool}) -> {T.nz(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      T.and_tt(Nat.is_le(1n, T.lenb(x)), T.nz(t), N.and_true_l(Nat.is_le(1n, T.lenb(x)), L.all_nonempty(t), h),
        ane_nz(t, N.and_true_r(Nat.is_le(1n, T.lenb(x)), L.all_nonempty(t), h)))

# A valid variant has no empty allele.
def valid_nz(+seq: List<&2, B.Base>, +p: Nat, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +h: {L.valid(seq, B.Var{p, ref, alts}) == True{} : Bool}) -> {T.nz(ref <> alts) == True{} : Bool}:
  +c1 = Bool.and(Nat.is_le(1n, p), Nat.is_le(1n, L.len(ref)))
  +c3 = Bool.and(c1, Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)))
  +c4 = Bool.and(c3, L.all_nonempty(alts))
  +c5 = Bool.and(c4, B.Alleles.distinct(ref <> alts))
  +c6 = B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)
  +h5 = N.and_true_l(c5, c6, h)
  +h4 = N.and_true_l(c4, B.Alleles.distinct(ref <> alts), h5)
  +h3 = N.and_true_l(c3, L.all_nonempty(alts), h4)
  +ha = N.and_true_r(c3, L.all_nonempty(alts), h4)
  +h1 = N.and_true_l(c1, Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)), h3)
  +hr = N.and_true_r(Nat.is_le(1n, p), Nat.is_le(1n, L.len(ref)), h1)
  T.and_tt(Nat.is_le(1n, T.lenb(ref)), T.nz(alts), hr, ane_nz(alts, ha))

# What judge writes for a line: a normalized record has at most
# LIN(10, 10, |body| + 1) bytes (other outcomes keep the line's text).
def JB(+body: String, r: B.Res) -> Type:
  match r:
    case B.Res{B.Normalized{}, k, t, s}:
      {Nat.is_le(SL(t), G.LIN(10n, 10n, 1n+SL(body))) == True{} : Bool}
    case _:
      Unit

def jb.norm(+body: String, +raw: String, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>,
  +em: {B.Rec.malformed(RL.FS(body)) == False{} : Bool},
  +er: {B.Allele.read(B.Rec.field(RL.FS(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(RL.FS(body))) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(RL.FS(body), 7n), RL.E1(body)), B.Bases.of_fasta(raw), RL.VV(body, ref, alts)) == None{} : Maybe<&2, B.Code>}) ->
  JB(body, L.problem(None{}, RL.FS(body), body, B.Bases.of_fasta(raw), RL.VV(body, ref, alts))):
  +fs = RL.FS(body)
  +seq = B.Bases.of_fasta(raw)
  +p = B.Rec.pos(fs)
  +end1 = B.Info.end_ok(B.Rec.field(fs, 7n), RL.E1(body))
  +n1 = RL.first_b(Bool.not(end1), B.BadEnd{}, L.first(Nat.is_eq(p, 0n), B.BadPos{},
    L.first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}))), ec)
  +he = P.not_false(end1, n1)
  +hz = valid_nz(seq, p, ref, alts, RL.nz_valid(fs, seq, ref, alts, end1, em, er, ea, ec))
  +w = V.normal(seq, B.Var{p, ref, alts})
  +hb = rb_bound(fs, ref, alts, w, T.normal_bnd(seq, p, ref, alts, hz), T.normal_bnd(seq, p, ref, alts, hz), T.normal_bnd(seq, p, ref, alts, hz),
    RL.E1(body), he, er, ea)
  AB.subst(Nat, z => {Nat.is_le(SL(B.Rec.rebuild(fs, B.Var{p, ref, alts}, w)), G.LIN(10n, 10n, z)) == True{} : Bool}, SN(fs), 1n+SL(body), split_sn(body, '\t'), hb)

def jb.problem(+body: String, +raw: String, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, c: Maybe<&2, B.Code>,
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(RL.FS(body), 7n), RL.E1(body)), B.Bases.of_fasta(raw), RL.VV(body, ref, alts)) == c : Maybe<&2, B.Code>},
  +em: {B.Rec.malformed(RL.FS(body)) == False{} : Bool},
  +er: {B.Allele.read(B.Rec.field(RL.FS(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(RL.FS(body))) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}) ->
  JB(body, L.problem(c, RL.FS(body), body, B.Bases.of_fasta(raw), RL.VV(body, ref, alts))):
  match c:
    case Some{k}:
      Unit{}
    case None{}:
      jb.norm(body, raw, ref, alts, em, er, ea, ec)

def jb.bases(+body: String, +raw: String,
  r: Maybe<&2, List<&2, B.Base>>, +er: {B.Allele.read(B.Rec.field(RL.FS(body), 3n)) == r : Maybe<&2, List<&2, B.Base>>},
  a: Maybe<&2, List<&2, List<&2, B.Base>>>, +ea: {B.Alleles.read(B.Rec.alts(RL.FS(body))) == a : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +em: {B.Rec.malformed(RL.FS(body)) == False{} : Bool}) ->
  JB(body, L.judge.bases(B.Info.end_ok(B.Rec.field(RL.FS(body), 7n), RL.E1(body)), r, a, RL.FS(body), body, B.Bases.of_fasta(raw))):
  match r a:
    case Some{+ref} Some{+alts}:
      jb.problem(body, raw, ref, alts, L.checks(B.Info.end_ok(B.Rec.field(RL.FS(body), 7n), RL.E1(body)), B.Bases.of_fasta(raw), RL.VV(body, ref, alts)), {==}, em, er, ea)
    case None{} _:
      Unit{}
    case Some{ref} None{}:
      Unit{}

def jb.contig(+fa: List<&2, B.Contig>, +body: String, m: Maybe<&2, String>, +em: {B.Rec.malformed(RL.FS(body)) == False{} : Bool}) ->
  JB(body, L.judge.contig(m, RL.FS(body), body)):
  match m:
    case None{}:
      Unit{}
    case Some{+raw}:
      jb.bases(body, raw, B.Allele.read(B.Rec.field(RL.FS(body), 3n)), {==}, B.Alleles.read(B.Rec.alts(RL.FS(body))), {==}, em)

def jb.shape(+fa: List<&2, B.Contig>, +body: String, bad: Bool, +eb: {B.Rec.malformed(RL.FS(body)) == bad : Bool}, skip: Bool) ->
  JB(body, L.judge.shape(bad, skip, fa, RL.FS(body), body)):
  match bad skip:
    case True{} _:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      jb.contig(fa, body, B.Fasta.find(fa, B.Rec.field(RL.FS(body), 0n)), eb)

# judge's normalized records are at most LIN(10, 10, |body| + 1) bytes.
def judge_len(+fa: List<&2, B.Contig>, +body: String) -> JB(body, L.judge(fa, body)):
  jb.shape(fa, body, B.Rec.malformed(RL.FS(body)), {==}, B.Rec.out_of_scope(RL.FS(body)))
