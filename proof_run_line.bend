import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_text.bend as X
import ./proof_run_dec.bend as D
import ./proof_run_rec.bend as C
import ./proof_run_rejudge.bend as J
import ./proof_var.bend as PV

# Each body line that does not stop run 1 is written as a line that run 2
# reads back and judges to an item with the same key, CHROM and text.

# The line of a text (its first line).
def hd_line(ls: List<&2, B.Line>) -> B.Line:
  match ls:
    case Nil{}:
      B.Line{"", ""}
    case l <> t:
      l

def ln(s: String) -> B.Line:
  hd_line(B.Text.lines(s))

law ln_good:
  for +l: B.Line
  for +h: {X.goodb(l) == True{} : Bool}
  {ln(B.Line.text(l)) == l : B.Line}

def ln_good(l, h):
  %Q.s_append_nil(B.Line.text(l)) : {hd_line(B.Text.lines(_)) == l : B.Line}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Line.text(l) ++ ""), l <> B.Text.lines(""), X.good_line(l, "", h)) : {hd_line(_) == l : B.Line}
  {==}

# A line's outcome lets the run go on.
def go_on(o: B.Opts, r: B.Res) -> Bool:
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      False{}
    case B.Res{B.NoContig{}, k, t, s}:
      False{}
    case B.Res{B.Problem{c}, k, t, s}:
      Bool.not(R.Opts.strict(o))
    case B.Res{B.Skipped{}, k, t, s}:
      True{}
    case B.Res{B.Normalized{}, k, t, s}:
      True{}

# Same key, CHROM and text.
def simb(a: R.Item, b: R.Item) -> Bool:
  match a b:
    case R.Item{k1, p1, B.At{n1, c1, q1}, t1} R.Item{k2, p2, B.At{n2, c2, q2}, t2}:
      Nat.is_eq(k1, k2) && String.eq(c1, c2) && String.eq(t1, t2)

# An item run 1 writes: its text is a good line, which run 2 judges so that it
# goes on, as an item with the same key, CHROM and text.
def qi(+fa: List<&2, B.Contig>, +o: B.Opts, +x: R.Item) -> Bool:
  +l2 = ln(R.Item.text(x))
  X.goodb(l2) && String.eq(B.Line.text(l2), R.Item.text(x)) && go_on(o, L.judge(fa, B.Line.body(l2))) && simb(L.item(fa, l2, 0n), x)

law simb_refl:
  for +k: Nat
  for +p1: Nat
  for +p2: Nat
  for +n1: Nat
  for +n2: Nat
  for +c: String
  for +q1: String
  for +q2: String
  for +t: String
  {simb(R.Item{k, p1, B.At{n1, c, q1}, t}, R.Item{k, p2, B.At{n2, c, q2}, t}) == True{} : Bool}

def simb_refl(k, p1, p2, n1, n2, c, q1, q2, t):
  S.and_intro(Bool.and(Nat.is_eq(k, k), String.eq(c, c)), String.eq(t, t),
    S.and_intro(Nat.is_eq(k, k), String.eq(c, c), P.eq_refl(k), Q.str_eq_refl(c)), Q.str_eq_refl(t))

def QI4(+fa: List<&2, B.Contig>, +o: B.Opts, +l2: B.Line, +x: R.Item) -> Bool:
  X.goodb(l2) && String.eq(B.Line.text(l2), R.Item.text(x)) && go_on(o, L.judge(fa, B.Line.body(l2))) && simb(L.item(fa, l2, 0n), x)

law qi_of:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +l2: B.Line
  for +x: R.Item
  for +hg: {X.goodb(l2) == True{} : Bool}
  for +ht: {B.Line.text(l2) == R.Item.text(x) : String}
  for +h4: {QI4(fa, o, l2, x) == True{} : Bool}
  {qi(fa, o, x) == True{} : Bool}

def qi_of(fa, o, l2, x, hg, ht, h4):
  %Equal.sym(B.Line, ln(R.Item.text(x)), l2, (%ht : {ln(_) == l2 : B.Line}; ln_good(l2, hg))) :
    {Bool.and(Bool.and(Bool.and(X.goodb(_), String.eq(B.Line.text(_), R.Item.text(x))), go_on(o, L.judge(fa, B.Line.body(_)))), simb(L.item(fa, _, 0n), x)) == True{} : Bool}
  h4

def is_norm(r: B.Res) -> Bool:
  match r:
    case B.Res{B.Normalized{}, k, t, s}:
      True{}
    case _:
      False{}

def nn.fin(+fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line, +n: Nat, +r: B.Res,
  +er: {L.judge(fa, B.Line.body(l)) == r : B.Res}, +hg: {X.goodb(l) == True{} : Bool},
  +hn: {go_on(o, r) == True{} : Bool},
  +hi: {L.item_of(r, l, B.At{0n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l)))) ==
    R.Item{B.Rec.pos(B.Rec.fields(B.Line.body(l))), B.Rec.pos(B.Rec.fields(B.Line.body(l))), B.At{0n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Line.text(l)} : R.Item}) ->
  {qi(fa, o, R.Item{B.Rec.pos(B.Rec.fields(B.Line.body(l))), B.Rec.pos(B.Rec.fields(B.Line.body(l))), B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Line.text(l)}) == True{} : Bool}:
  +fs = B.Rec.fields(B.Line.body(l))
  +f0 = B.Rec.field(fs, 0n)
  +f1 = B.Rec.field(fs, 1n)
  +p = B.Rec.pos(fs)
  +x = {R.Item{p, p, B.At{n, f0, f1}, B.Line.text(l)} : R.Item}
  +hgo = {(%Equal.sym(B.Res, L.judge(fa, B.Line.body(l)), r, er) : {go_on(o, _) == True{} : Bool}; hn) : {go_on(o, L.judge(fa, B.Line.body(l))) == True{} : Bool}}
  +hs = {(%Equal.sym(B.Res, L.judge(fa, B.Line.body(l)), r, er) : {simb(L.item_of(_, l, B.At{0n, f0, f1}, p), x) == True{} : Bool};
      %Equal.sym(R.Item, L.item_of(r, l, B.At{0n, f0, f1}, p), R.Item{p, p, B.At{0n, f0, f1}, B.Line.text(l)}, hi) : {simb(_, x) == True{} : Bool};
      simb_refl(p, p, p, 0n, n, f0, f1, f1, B.Line.text(l))) :
    {simb(L.item(fa, l, 0n), x) == True{} : Bool}}
  qi_of(fa, o, l, x, hg, {==},
    S.and_intro(Bool.and(Bool.and(X.goodb(l), String.eq(B.Line.text(l), B.Line.text(l))), go_on(o, L.judge(fa, B.Line.body(l)))), simb(L.item(fa, l, 0n), x),
      S.and_intro(Bool.and(X.goodb(l), String.eq(B.Line.text(l), B.Line.text(l))), go_on(o, L.judge(fa, B.Line.body(l))),
        S.and_intro(X.goodb(l), String.eq(B.Line.text(l), B.Line.text(l)), hg, Q.str_eq_refl(B.Line.text(l))), hgo), hs))

# Facts about the run-1 record
# ============================

law first_b:
  for +b: Bool
  for +c: B.Code
  for +rest: Maybe<&2, B.Code>
  for +e: {L.first(b, c, rest) == None{} : Maybe<&2, B.Code>}
  {b == False{} : Bool}

def first_b(b, c, rest, e):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, C.some_ne_none_c(c, e))
    case False{}:
      {==}

law first_r:
  for +b: Bool
  for +c: B.Code
  for +rest: Maybe<&2, B.Code>
  for +e: {L.first(b, c, rest) == None{} : Maybe<&2, B.Code>}
  {rest == None{} : Maybe<&2, B.Code>}

def first_r(b, c, rest, e):
  match b:
    case True{}:
      Empty.absurd({rest == None{} : Maybe<&2, B.Code>}, C.some_ne_none_c(c, e))
    case False{}:
      e

law ne0_le:
  for +p: Nat
  for +h: {Nat.is_eq(p, 0n) == False{} : Bool}
  {Nat.is_le(1n, p) == True{} : Bool}

def ne0_le(p, h):
  match p:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.true_ne_false(h))
    case 1n+k:
      P.le_zero_l(k)

law letters_len:
  for +s: String
  for +h: {B.Text.is_letters(s) == True{} : Bool}
  {Nat.is_le(1n, String.length(s)) == True{} : Bool}

def letters_len(s, h):
  match s:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, P.false_ne_true(h))
    case SCon{+c, +t}:
      P.le_zero_l(String.length(t))

def split_len1.go(ps: List<&2, String>, ne: {ps == Nil{} : List<&2, String>} -> Empty) -> {Nat.is_le(1n, J.slen(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ne({==}))
    case +p <> +t:
      P.le_zero_l(J.slen(t))

law split_len1:
  for +s: String
  for +c: Char
  {Nat.is_le(1n, J.slen(String.split(s, c))) == True{} : Bool}

def split_len1(s, c):
  split_len1.go(String.split(s, c), e => X.split_nn(s, c, e))

def info2(mv: Bool, +info: String, +q: Nat, +s: List<&2, B.Base>, +y: List<&2, List<&2, B.Base>>) -> String:
  B.Rec.info(mv, info, B.Var{q, s, y})

law inf_noc:
  for +mv: Bool
  for +info: String
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +c: Char
  for +h: {X.no_c(info, c) == True{} : Bool}
  for +hend: {X.no_c(C.endp(Nat.sub(Nat.add(q, L.len(s)), 1n)), c) == True{} : Bool}
  for +hs: {X.no_c(";", c) == True{} : Bool}
  {X.no_c(info2(mv, info, q, s, y), c) == True{} : Bool}

def inf_noc(mv, info, q, s, y, c, h, hend, hs):
  match mv:
    case True{}:
      C.set_end_noc(info, Nat.sub(Nat.add(q, L.len(s)), 1n), c, h, hend, hs)
    case False{}:
      h

law inf_ecr:
  for +mv: Bool
  for +info: String
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for h: {C.ecr(info2(mv, info, q, s, y)) == True{} : Bool}
  {C.ecr(info) == True{} : Bool}

def inf_ecr(mv, info, q, s, y, h):
  match mv:
    case True{}:
      C.ecr_set(info, Nat.sub(Nat.add(q, L.len(s)), 1n), h)
    case False{}:
      h

law inf_end:
  for +mv: Bool
  for +p: Nat
  for +r: List<&2, B.Base>
  for +x: List<&2, List<&2, B.Base>>
  for +q: Nat
  for +s: List<&2, B.Base>
  for +y: List<&2, List<&2, B.Base>>
  for +emv: {B.Rec.moved(B.Var{p, r, x}, B.Var{q, s, y}) == mv : Bool}
  for +info: String
  for +he1: {B.Info.end_ok(info, Nat.sub(Nat.add(p, L.len(r)), 1n)) == True{} : Bool}
  {B.Info.end_ok(info2(mv, info, q, s, y), Nat.sub(Nat.add(q, L.len(s)), 1n)) == True{} : Bool}

def inf_end(mv, p, r, x, q, s, y, emv, info, he1):
  match mv:
    case True{}:
      C.end_set_ok(info, Nat.sub(Nat.add(q, L.len(s)), 1n), Nat.sub(Nat.add(p, L.len(r)), 1n), he1)
    case False{}:
      +ha = P.not_false(Bool.and(Nat.is_eq(p, q), Nat.is_eq(L.len(r), L.len(s))), emv)
      +epq = P.eq_sound(p, q, P.and_true_l(Nat.is_eq(p, q), Nat.is_eq(L.len(r), L.len(s)), ha))
      +ers = P.eq_sound(L.len(r), L.len(s), P.and_true_r(Nat.is_eq(p, q), Nat.is_eq(L.len(r), L.len(s)), ha))
      %epq : {B.Info.end_ok(info, Nat.sub(Nat.add(_, L.len(s)), 1n)) == True{} : Bool}
      %ers : {B.Info.end_ok(info, Nat.sub(Nat.add(p, _), 1n)) == True{} : Bool}
      he1

# The variant of a normalized run-1 line is valid.
def nz_valid(+fs: List<&2, String>, +seq: List<&2, B.Base>, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, +end1: Bool,
  +em: {B.Rec.malformed(fs) == False{} : Bool},
  +er: {B.Allele.read(B.Rec.field(fs, 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(fs)) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +ec: {L.checks(end1, seq, B.Var{B.Rec.pos(fs), ref, alts}) == None{} : Maybe<&2, B.Code>}) ->
  {L.valid(seq, B.Var{B.Rec.pos(fs), ref, alts}) == True{} : Bool}:
  +p = B.Rec.pos(fs)
  +f3 = B.Rec.field(fs, 3n)
  +R3 = L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{})
  +R2 = L.first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, R3)
  +R1 = L.first(Nat.is_eq(p, 0n), B.BadPos{}, R2)
  +r1 = first_r(Bool.not(end1), B.BadEnd{}, R1, ec)
  +n2 = first_b(Nat.is_eq(p, 0n), B.BadPos{}, R2, r1)
  +r2 = first_r(Nat.is_eq(p, 0n), B.BadPos{}, R2, r1)
  +n3 = first_b(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, R3, r2)
  +r3 = first_r(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, R3, r2)
  +n4 = first_b(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}, r3)
  +m1to4 = P.or_false_inv(Bool.or(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
    Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3))), B.Text.any_empty(B.Rec.alts(fs)), em)
  +m5 = C.or_inv_r(Bool.or(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
    Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3))), B.Text.any_empty(B.Rec.alts(fs)), em)
  +m4 = C.or_inv_r(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
    Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3)), m1to4)
  +c1 = ne0_le(p, n2)
  +c2 = {(%C.read_len(f3, ref, er) : {Nat.is_le(1n, _) == True{} : Bool}; letters_len(f3, P.not_false(B.Text.is_letters(f3), m4))) :
    {Nat.is_le(1n, L.len(ref)) == True{} : Bool}}
  +al = {(%ea : {C.alm(_, J.slen(B.Rec.alts(fs))) == True{} : Bool}; C.alleles_len(B.Rec.alts(fs))) :
    {Nat.is_eq(List.length(&2, List<&2, B.Base>, alts), J.slen(B.Rec.alts(fs))) == True{} : Bool}}
  +c3 = {(%Equal.sym(Nat, List.length(&2, List<&2, B.Base>, alts), J.slen(B.Rec.alts(fs)), P.eq_sound(List.length(&2, List<&2, B.Base>, alts), J.slen(B.Rec.alts(fs)), al)) :
      {Nat.is_le(1n, _) == True{} : Bool}; split_len1(B.Rec.field(fs, 4n), ',')) :
    {Nat.is_le(1n, List.length(&2, List<&2, B.Base>, alts)) == True{} : Bool}}
  +c4 = {(%ea : {C.ane(_) == True{} : Bool}; C.alleles_ne(B.Rec.alts(fs), m5)) : {L.all_nonempty(alts) == True{} : Bool}}
  +c5 = P.not_false(B.Alleles.distinct(ref <> alts), n3)
  +c6 = P.not_false(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref), n4)
  S.and_intro(Bool.and(Bool.and(Bool.and(Bool.and(C.c1(p), C.c2(ref)), C.c3(alts)), L.all_nonempty(alts)), C.c5(ref, alts)), C.c6(seq, p, ref),
    S.and_intro(Bool.and(Bool.and(Bool.and(C.c1(p), C.c2(ref)), C.c3(alts)), L.all_nonempty(alts)), C.c5(ref, alts),
      S.and_intro(Bool.and(Bool.and(C.c1(p), C.c2(ref)), C.c3(alts)), L.all_nonempty(alts),
        S.and_intro(Bool.and(C.c1(p), C.c2(ref)), C.c3(alts), S.and_intro(C.c1(p), C.c2(ref), c1, c2), c3), c4), c5), c6)

def FS(+body: String) -> List<&2, String>:
  String.split(body, '\t')

def VV(+body: String, +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>) -> B.Var:
  B.Var{B.Rec.pos(FS(body)), ref, alts}

def E1(+body: String) -> Nat:
  Nat.sub(Nat.add(B.Rec.pos(FS(body)), String.length(B.Rec.field(FS(body), 3n))), 1n)

def AT(+n: Nat, +body: String) -> B.At:
  B.At{n, B.Rec.field(FS(body), 0n), B.Rec.field(FS(body), 1n)}

# A normalized line.
def nz.go(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat, +raw: String,
  +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, w: B.Var,
  +ew: {Norm.var(B.Bases.of_fasta(raw), VV(body, ref, alts)) == w : B.Var},
  +em: {B.Rec.malformed(FS(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(FS(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(FS(body))) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), B.Bases.of_fasta(raw), VV(body, ref, alts)) == None{} : Maybe<&2, B.Code>},
  +hg: {X.goodb(B.Line{body, term}) == True{} : Bool}) ->
  {qi(fa, o, L.item_of(B.Res{B.Normalized{}, L.pos_of(w), B.Rec.rebuild(FS(body), VV(body, ref, alts), w), B.Rec.stale(FS(body), VV(body, ref, alts), w)},
    B.Line{body, term}, AT(n, body), B.Rec.pos(FS(body)))) == True{} : Bool}:
  match w:
    case B.Var{+q, +s, +y}:
      +fs = FS(body)
      +seq = B.Bases.of_fasta(raw)
      +v = VV(body, ref, alts)
      +p = B.Rec.pos(fs)
      +W = {B.Var{q, s, y} : B.Var}
      +info = B.Rec.field(fs, 7n)
      +f3 = B.Rec.field(fs, 3n)
      +mv = B.Rec.moved(v, W)
      +i2 = info2(mv, info, q, s, y)
      +e2 = Nat.sub(Nat.add(q, L.len(s)), 1n)
      +end1 = B.Info.end_ok(info, E1(body))
      +or4 = Bool.or(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))),
        Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))), Bool.not(B.Text.is_letters(f3)))
      +or2F = P.or_false_inv(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n))),
        P.or_false_inv(Bool.or(Bool.or(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n))), Maybe.is_none(&2, Nat, B.Pos.read(B.Rec.field(fs, 1n)))),
          Bool.not(B.Text.is_letters(f3)), P.or_false_inv(or4, B.Text.any_empty(B.Rec.alts(fs)), em)))
      +m1 = P.or_false_inv(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n)), or2F)
      +m2 = C.or_inv_r(Nat.is_lt(J.slen(fs), 8n), String.is_empty(B.Rec.field(fs, 0n)), or2F)
      +k = Nat.sub(J.slen(fs), 8n)
      +hl = J.ge8(J.slen(fs), m1)
      +hvv = nz_valid(fs, seq, ref, alts, end1, em, er, ea, ec)
      +htw = {(%ew : {Norm.var(seq, _) == _ : B.Var}; PV.twice(seq, v, hvv)) : {Norm.var(seq, W) == W : B.Var}}
      +hv = {(%ew : {L.valid(seq, _) == True{} : Bool}; PV.stays_valid(seq, v, hvv)) : {L.valid(seq, W) == True{} : Bool}}
      +htab = X.pieces_noc(body, '\t')
      +hi2 = inf_noc(mv, info, q, s, y, '\t', C.field_noc(fs, 7n, '\t', htab), C.digits_noc(Nat.show(e2), '\t', D.show_digits(e2), {==}), {==})
      +n1 = first_b(Bool.not(end1), B.BadEnd{}, L.first(Nat.is_eq(p, 0n), B.BadPos{},
        L.first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(p, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}))), ec)
      +he1 = {(%C.read_len(f3, ref, er) : {B.Info.end_ok(info, Nat.sub(Nat.add(p, _), 1n)) == True{} : Bool}; P.not_false(end1, n1)) :
        {B.Info.end_ok(info, Nat.sub(Nat.add(p, L.len(ref)), 1n)) == True{} : Bool}}
      +hend = inf_end(mv, p, ref, alts, q, s, y, {==}, info, he1)
      +hnlfs = C.pieces_sub_noc(body, '\t', '\n', P.and_true_l(X.no_c(body, '\n'),
        Bool.or(String.eq(term, "\r\n"), Bool.and(String.eq(term, "\n"), Bool.not(String.ends_with(body, "\r")))), hg))
      +hnl = J.fa_noc(fs, q, s, y, i2, '\n', hnlfs, C.digits_noc(Nat.show(q), '\n', D.show_digits(q), {==}), C.show_noc(s, '\n', {==}),
        C.join_noc2(B.Alleles.show(y), ",", '\n', C.shows_noc(y, '\n', {==}), {==}),
        inf_noc(mv, info, q, s, y, '\n', C.field_noc(fs, 7n, '\n', hnlfs), C.digits_noc(Nat.show(e2), '\n', D.show_digits(e2), {==}), {==}))
      +g2 = J.good_re(body, term, fs, q, s, y, i2, k, {==}, hl, hg, hnl, h => inf_ecr(mv, info, q, s, y, h))
      +F = J.fsA(fs, q, s, y, i2)
      +b2 = String.join(F, "\t")
      +l2 = {B.Line{b2, term} : B.Line}
      +x = {R.Item{q, p, AT(n, body), b2 ++ term} : R.Item}
      +rj = J.rejudge(fa, fs, raw, q, s, y, i2, k, hl, m2, ef, htab, hi2, hend, hv, htw)
      +rf = J.rb_fields(fs, q, s, y, i2, k, hl, htab, hi2)
      +go = {(%Equal.sym(B.Res, L.judge(fa, b2), J.RES(q, s, y, F), rj) : {go_on(o, _) == True{} : Bool}; {==}) :
        {go_on(o, L.judge(fa, b2)) == True{} : Bool}}
      +sm = {(%Equal.sym(B.Res, L.judge(fa, b2), J.RES(q, s, y, F), rj) :
          {simb(L.item_of(_, l2, B.At{0n, B.Rec.field(String.split(b2, '\t'), 0n), B.Rec.field(String.split(b2, '\t'), 1n)}, B.Rec.pos(String.split(b2, '\t'))), x) == True{} : Bool};
        %Equal.sym(List<&2, String>, String.split(b2, '\t'), F, rf) :
          {simb(R.Item{q, B.Rec.pos(_), B.At{0n, B.Rec.field(_, 0n), B.Rec.field(_, 1n)}, b2 ++ term}, x) == True{} : Bool};
        %Equal.sym(String, B.Rec.field(F, 0n), B.Rec.field(fs, 0n), J.fa_f0(fs, q, s, y, i2)) :
          {simb(R.Item{q, B.Rec.pos(F), B.At{0n, _, B.Rec.field(F, 1n)}, b2 ++ term}, x) == True{} : Bool};
        simb_refl(q, B.Rec.pos(F), p, 0n, n, B.Rec.field(fs, 0n), B.Rec.field(F, 1n), B.Rec.field(fs, 1n), b2 ++ term)) :
        {simb(L.item(fa, l2, 0n), x) == True{} : Bool}}
      qi_of(fa, o, l2, x, g2, {==},
        S.and_intro(Bool.and(Bool.and(X.goodb(l2), String.eq(b2 ++ term, b2 ++ term)), go_on(o, L.judge(fa, b2))), simb(L.item(fa, l2, 0n), x),
          S.and_intro(Bool.and(X.goodb(l2), String.eq(b2 ++ term, b2 ++ term)), go_on(o, L.judge(fa, b2)),
            S.and_intro(X.goodb(l2), String.eq(b2 ++ term, b2 ++ term), g2, Q.str_eq_refl(b2 ++ term)), go), sm))

def QG(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat, r: B.Res) -> Type:
  {qi(fa, o, L.item_of(r, B.Line{body, term}, AT(n, body), B.Rec.pos(FS(body)))) == True{} : Bool}

def pl.pass(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat, +r: B.Res,
  +ej: {L.judge(fa, body) == r : B.Res}, +hg: {X.goodb(B.Line{body, term}) == True{} : Bool}, +hgo: {go_on(o, r) == True{} : Bool},
  +hi: {L.item_of(r, B.Line{body, term}, AT(0n, body), B.Rec.pos(FS(body))) == R.Item{B.Rec.pos(FS(body)), B.Rec.pos(FS(body)), AT(0n, body), body ++ term} : R.Item},
  +hx: {L.item_of(r, B.Line{body, term}, AT(n, body), B.Rec.pos(FS(body))) == R.Item{B.Rec.pos(FS(body)), B.Rec.pos(FS(body)), AT(n, body), body ++ term} : R.Item}) ->
  QG(fa, o, body, term, n, r):
  %Equal.sym(R.Item, L.item_of(r, B.Line{body, term}, AT(n, body), B.Rec.pos(FS(body))),
    R.Item{B.Rec.pos(FS(body)), B.Rec.pos(FS(body)), AT(n, body), body ++ term}, hx) : {qi(fa, o, _) == True{} : Bool}
  nn.fin(fa, o, B.Line{body, term}, n, r, ej, hg, hgo, hi)

def pl.problem(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat, +raw: String,
  +ref: List<&2, B.Base>, +alts: List<&2, List<&2, B.Base>>, c: Maybe<&2, B.Code>,
  +ec: {L.checks(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), B.Bases.of_fasta(raw), VV(body, ref, alts)) == c : Maybe<&2, B.Code>},
  +ej: {L.judge(fa, body) == L.problem(c, FS(body), body, B.Bases.of_fasta(raw), VV(body, ref, alts)) : B.Res},
  +em: {B.Rec.malformed(FS(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +er: {B.Allele.read(B.Rec.field(FS(body), 3n)) == Some{ref} : Maybe<&2, List<&2, B.Base>>},
  +ea: {B.Alleles.read(B.Rec.alts(FS(body))) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +hg: {X.goodb(B.Line{body, term}) == True{} : Bool},
  +hgo: {go_on(o, L.problem(c, FS(body), body, B.Bases.of_fasta(raw), VV(body, ref, alts))) == True{} : Bool}) ->
  QG(fa, o, body, term, n, L.problem(c, FS(body), body, B.Bases.of_fasta(raw), VV(body, ref, alts))):
  match c:
    case Some{+k}:
      pl.pass(fa, o, body, term, n, L.res(B.Problem{k}, FS(body), body), ej, hg, hgo, {==}, {==})
    case None{}:
      nz.go(fa, o, body, term, n, raw, ref, alts, Norm.var(B.Bases.of_fasta(raw), VV(body, ref, alts)), {==}, em, ef, er, ea, ec, hg)

def pl.bases(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat, +raw: String,
  r: Maybe<&2, List<&2, B.Base>>, +er: {B.Allele.read(B.Rec.field(FS(body), 3n)) == r : Maybe<&2, List<&2, B.Base>>},
  a: Maybe<&2, List<&2, List<&2, B.Base>>>, +ea: {B.Alleles.read(B.Rec.alts(FS(body))) == a : Maybe<&2, List<&2, List<&2, B.Base>>>},
  +ej: {L.judge(fa, body) == L.judge.bases(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), r, a, FS(body), body, B.Bases.of_fasta(raw)) : B.Res},
  +em: {B.Rec.malformed(FS(body)) == False{} : Bool},
  +ef: {B.Fasta.find(fa, B.Rec.field(FS(body), 0n)) == Some{raw} : Maybe<&2, String>},
  +hg: {X.goodb(B.Line{body, term}) == True{} : Bool},
  +hgo: {go_on(o, L.judge.bases(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), r, a, FS(body), body, B.Bases.of_fasta(raw))) == True{} : Bool}) ->
  QG(fa, o, body, term, n, L.judge.bases(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), r, a, FS(body), body, B.Bases.of_fasta(raw))):
  match r a:
    case Some{+ref} Some{+alts}:
      pl.problem(fa, o, body, term, n, raw, ref, alts, L.checks(B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), B.Bases.of_fasta(raw), VV(body, ref, alts)), {==}, ej, em, ef, er, ea, hg, hgo)
    case None{} _:
      pl.pass(fa, o, body, term, n, L.res(B.Problem{Bool.pick(B.Code, B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), B.NonAcgtn{}, B.BadEnd{})}, FS(body), body), ej, hg, hgo, {==}, {==})
    case Some{ref} None{}:
      pl.pass(fa, o, body, term, n, L.res(B.Problem{Bool.pick(B.Code, B.Info.end_ok(B.Rec.field(FS(body), 7n), E1(body)), B.NonAcgtn{}, B.BadEnd{})}, FS(body), body), ej, hg, hgo, {==}, {==})

def pl.contig(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat,
  m: Maybe<&2, String>, +ef: {B.Fasta.find(fa, B.Rec.field(FS(body), 0n)) == m : Maybe<&2, String>},
  +ej: {L.judge(fa, body) == L.judge.contig(m, FS(body), body) : B.Res},
  +em: {B.Rec.malformed(FS(body)) == False{} : Bool},
  +hg: {X.goodb(B.Line{body, term}) == True{} : Bool},
  +hgo: {go_on(o, L.judge.contig(m, FS(body), body)) == True{} : Bool}) ->
  QG(fa, o, body, term, n, L.judge.contig(m, FS(body), body)):
  match m:
    case None{}:
      Empty.absurd(QG(fa, o, body, term, n, L.judge.contig(None{}, FS(body), body)), P.false_ne_true(hgo))
    case Some{+raw}:
      pl.bases(fa, o, body, term, n, raw, B.Allele.read(B.Rec.field(FS(body), 3n)), {==}, B.Alleles.read(B.Rec.alts(FS(body))), {==}, ej, em, ef, hg, hgo)

def pl.shape(+fa: List<&2, B.Contig>, +o: B.Opts, +body: String, +term: String, +n: Nat,
  bad: Bool, +eb: {B.Rec.malformed(FS(body)) == bad : Bool}, skip: Bool,
  +ej: {L.judge(fa, body) == L.judge.shape(bad, skip, fa, FS(body), body) : B.Res},
  +hg: {X.goodb(B.Line{body, term}) == True{} : Bool},
  +hgo: {go_on(o, L.judge.shape(bad, skip, fa, FS(body), body)) == True{} : Bool}) ->
  QG(fa, o, body, term, n, L.judge.shape(bad, skip, fa, FS(body), body)):
  match bad skip:
    case True{} _:
      Empty.absurd(QG(fa, o, body, term, n, L.judge.shape(True{}, skip, fa, FS(body), body)), P.false_ne_true(hgo))
    case False{} True{}:
      pl.pass(fa, o, body, term, n, L.res(B.Skipped{}, FS(body), body), ej, hg, hgo, {==}, {==})
    case False{} False{}:
      pl.contig(fa, o, body, term, n, B.Fasta.find(fa, B.Rec.field(FS(body), 0n)), {==}, ej, eb, hg, hgo)

# Every body line that lets run 1 go on gives an item run 2 reads back.
law line_qi:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +l: B.Line
  for +n: Nat
  for +hg: {X.goodb(l) == True{} : Bool}
  for +hgo: {go_on(o, L.judge(fa, B.Line.body(l))) == True{} : Bool}
  {qi(fa, o, L.item(fa, l, n)) == True{} : Bool}

def line_qi(fa, o, l, n, hg, hgo):
  match l:
    case B.Line{+body, +term}:
      pl.shape(fa, o, body, term, n, B.Rec.malformed(FS(body)), {==}, B.Rec.out_of_scope(FS(body)), {==}, hg, hgo)
