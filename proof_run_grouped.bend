import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_sorted.bend as PS
import ./proof_run_tail.bend as U
import ./proof_s_same.bend as SM

# The law `grouped_in`: a run that succeeds had each CHROM in one run. The
# machine's current CHROM and ended CHROMs are grouped.go's cur and ended.

# The rest of a run that succeeds makes g true.
def GM(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +g: Bool, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(U.TT(t, fa, defs, o, st))) == 0n : Nat} -> {g == True{} : Bool}

def halted_gm(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +g: Bool,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  GM(fa, defs, o, t, g, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  hc => Empty.absurd({g == True{} : Bool},
    PS.code_10(R.Report.code(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), hc,
      U.tt_code(t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)))

# same_run keeps the CHROM bookkeeping (or stops).
def gm_same(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +g: Bool,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>,
  +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item,
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    GM(fa, defs, o, t, g, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  GM(fa, defs, o, t, g, R.same_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, it)):
  T.SR(st2 => GM(fa, defs, o, t, g, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
    +o3 => +bad => +prev => ef => halted_gm(fa, defs, o, t, g, n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
      List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
    +o2 => +l2 => ef => ih(l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), out ++ o2))

def IHR(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    GM(fa, defs, o, t, L.grouped.go(rest, gc2, ge2), R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k, out2, ns, False{}})

def grouped.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, b: Bool,
  +eb: {String.eq(gc, R.Item.chrom(it)) == b : Bool}, ih: IHR(fa, defs, o, t, rest, n, h, k, ns)) ->
  GM(fa, defs, o, t, L.grouped.go(it <> rest, gc, ge),
    R.keyed.go(b, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      +c = R.Item.chrom(it)
      +es = Equal.trans(Bool, String.eq(c, gc), String.eq(gc, c), True{}, Q.str_eq_sym(gc, c), eb)
      %Equal.sym(Bool, String.eq(c, gc), True{}, es) :
        GM(fa, defs, o, t, Bool.and(Bool.or(_, Bool.not(R.has(c, gc <> ge))), L.grouped.go(rest, c, Bool.pick(List<&2, String>, _, ge, gc <> ge))),
          R.same_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, it))
      %Q.str_eq_sound(gc, c, eb) : GM(fa, defs, o, t, L.grouped.go(rest, _, ge),
          R.same_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, it))
      gm_same(fa, defs, o, t, L.grouped.go(rest, gc, ge), n, h, Some{gc}, ge, last, buf, k, out, ns, w, it,
        last2 => buf2 => out2 => ih(gc, ge, last2, buf2, out2))
    case False{}:
      +c = R.Item.chrom(it)
      +es = Equal.trans(Bool, String.eq(c, gc), String.eq(gc, c), False{}, Q.str_eq_sym(gc, c), eb)
      %Equal.sym(Bool, String.eq(c, gc), False{}, es) :
        GM(fa, defs, o, t, Bool.and(Bool.or(_, Bool.not(Bool.or(_, R.has(c, ge)))), L.grouped.go(rest, c, Bool.pick(List<&2, String>, _, ge, gc <> ge))),
          R.new_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, c, it))
      +g = Bool.and(Bool.not(R.has(c, ge)), L.grouped.go(rest, c, gc <> ge))
      T.NR(st2 => GM(fa, defs, o, t, g, st2), n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}, w, c, it,
        +o3 => +bad => +prev => ef => halted_gm(fa, defs, o, t, g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => ef => eh => halted_gm(fa, defs, o, t, g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o2,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
        +o2 => +l2 => ef => eh =>
          %Equal.sym(Bool, R.has(c, ge), False{}, eh) :
            GM(fa, defs, o, t, Bool.and(Bool.not(_), L.grouped.go(rest, c, gc <> ge)),
              R.same_run(R.RunSt{n, True{}, h, Some{c}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, False{}}, w, it));
          gm_same(fa, defs, o, t, L.grouped.go(rest, c, gc <> ge), n, h, Some{c}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, w, it,
            last2 => buf2 => out2 => ih(c, gc <> ge, last2, buf2, out2)))

# The place of a line (or of its records) with fields fs and number n.
def AT(+fs: List<&2, String>, +n: Nat) -> B.At:
  B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}

# After a line's records, within a CHROM run: the lines t.
def KR(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @k2: R.Cnt -> @out2: String -> @ns2: List<&2, B.Note> ->
    GM(fa, defs, o, U.TLs(t), L.grouped.go(rest, gc2, ge2), R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k2, out2, ns2, False{}})

# After a line with no record, before the first CHROM run: the lines t.
def KF(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @k2: R.Cnt -> @out2: String -> @ns2: List<&2, B.Note> ->
    GM(fa, defs, o, U.TLs(t), L.grouped(rest), R.RunSt{n, True{}, h, None{}, Nil{}, last2, buf2, k2, out2, ns2, False{}})

# A split line's records, within a CHROM run.
def grouped_ps(ps: List<&2, String>, +fs: List<&2, String>, +term: String, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +rest: List<&2, R.Item>, +hs: {L.all_same_site(fs, ps) == True{} : Bool}, kl: KR(fa, defs, o, t, rest, n, h)) ->
  GM(fa, defs, o, U.Tl{ps, term, AT(fs, n), B.Rec.pos(fs), t}, L.grouped.go(S.app(L.items.pieces(ps, fa, term, n), rest), gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kl(gc, ge, last, buf, k, out, ns)
    case Con{+p, +pt}:
      +at = AT(fs, n)
      +inpos = B.Rec.pos(fs)
      +LN = {B.Line{p, term} : B.Line}
      +it = L.item_of(L.judge(fa, p), LN, at, inpos)
      +rest2 = S.app(L.items.pieces(pt, fa, term, n), rest)
      +hs1 = P.and_true_l(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +hs2 = P.and_true_r(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      +g = L.grouped.go(it <> rest2, gc, ge)
      %Equal.sym(R.Item, L.item(fa, LN, n), it, U.item_site(fs, p, term, n, fa, hs1)) :
        GM(fa, defs, o, U.Tl{Con{p, pt}, term, at, inpos, t}, L.grouped.go(_ <> rest2, gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})
      T.BL(st2 => GM(fa, defs, o, tl, g, st2), L.judge(fa, p), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => u => halted_gm(fa, defs, o, tl, g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped.key(fa, defs, o, tl, rest2, n, h, gc, ge, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, String.eq(gc, R.Item.chrom(it)), {==},
          gc2 => ge2 => last2 => buf2 => out2 => grouped_ps(pt, fs, term, t, fa, defs, o, n, h, gc2, ge2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), rest, hs2, kl)))

# A body line within a CHROM run, by what -m does with it.
def grouped_line(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +rest: List<&2, R.Item>, +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, kl: KR(fa, defs, o, t, rest, n, h)) ->
  GM(fa, defs, o, U.TLs(t), L.grouped.go(S.app(L.items.line(pt, fa, l, n), rest), gc, ge),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, l, AT(B.Rec.fields(B.Line.body(l)), n), B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = AT(fs, n)
      +it = L.item(fa, l, n)
      +g = L.grouped.go(it <> rest, gc, ge)
      T.BL(st2 => GM(fa, defs, o, U.TLs(t), g, st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_gm(fa, defs, o, U.TLs(t), g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped.key(fa, defs, o, U.TLs(t), rest, n, h, gc, ge, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, String.eq(gc, R.Item.chrom(it)), {==},
          gc2 => ge2 => last2 => buf2 => out2 => kl(gc2, ge2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))
    case B.Pieces{+ps}:
      grouped_ps(ps, B.Rec.fields(B.Line.body(l)), B.Line.term(l), t, fa, defs, o, n, h, gc, ge, last, buf, k, out, ns, rest,
        SM.split_site(defs, o, B.Line.body(l), ps, hpt), kl)
    case B.Unsplit{+c}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = AT(fs, n)
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      +g = L.grouped.go(it <> rest, gc, ge)
      U.UL(st2 => GM(fa, defs, o, U.TLs(t), g, st2), L.judge(fa, B.Line.body(l)), c, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), c, hpt),
        +cd => u => halted_gm(fa, defs, o, U.TLs(t), g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped.key(fa, defs, o, U.TLs(t), rest, n, h, gc, ge, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, String.eq(gc, R.Item.chrom(it)), {==},
          gc2 => ge2 => last2 => buf2 => out2 => kl(gc2, ge2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))

# Within the body, with a current CHROM run.
law grouped_run:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +gc: String
  for +ge: List<&2, String>
  for +last: Maybe<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  GM(fa, defs, o, U.TLs(ls), L.grouped.go(U.mitems(ls, fa, defs, o, n), gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})

def grouped_run(ls, fa, defs, o, n, h, gc, ge, last, buf, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      +rest = U.mitems(t, fa, defs, o, 1n+n)
      %Equal.sym(List<&2, R.Item>, U.mitems(l <> t, fa, defs, o, n), S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), rest), U.mitems_cons(l, t, fa, defs, o, n)) :
        GM(fa, defs, o, U.TLs(l <> t), L.grouped.go(_, gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})
      grouped_line(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, gc, ge, last, buf, k, out, ns, rest, {==},
        gc2 => ge2 => last2 => buf2 => k2 => out2 => ns2 => grouped_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2))

# The first record of the body starts the first CHROM run.
def grouped_fk(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +tl: U.Tl, +rest: List<&2, R.Item>, +n: Nat, +h: String, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>,
  +k2: R.Cnt, +out: String, +ns2: List<&2, B.Note>, +it: R.Item,
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    GM(fa, defs, o, tl, L.grouped.go(rest, R.Item.chrom(it), Nil{}), R.RunSt{n, True{}, h, Some{R.Item.chrom(it)}, Nil{}, last2, buf2, k2, out2, ns2, False{}})) ->
  GM(fa, defs, o, tl, L.grouped(it <> rest), R.new_run(R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k2, out, ns2, False{}}, R.Opts.w(o), R.Item.chrom(it), it)):
  +c = R.Item.chrom(it)
  +g = L.grouped.go(rest, c, Nil{})
  T.NR(st2 => GM(fa, defs, o, tl, g, st2), n, True{}, h, None{}, Nil{}, last, buf, k2, out, ns2, False{}, R.Opts.w(o), c, it,
    +o3 => +bad => +prev => ef => halted_gm(fa, defs, o, tl, g, n, True{}, h, None{}, Nil{}, last, buf, k2, out ++ o3,
      List.append(&2, B.Note, ns2, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
    +o2 => +l2 => ef => eh => halted_gm(fa, defs, o, tl, g, n, True{}, h, None{}, Nil{}, last, buf, k2, out ++ o2,
      List.append(&2, B.Note, ns2, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
    +o2 => +l2 => ef => eh =>
      gm_same(fa, defs, o, tl, g, n, h, Some{c}, Nil{}, None{}, Nil{}, k2, out ++ o2, ns2, R.Opts.w(o), it,
        last2 => buf2 => out2 => ih(last2, buf2, out2)))

# A split line's records, before the first CHROM run.
def grouped_fps(ps: List<&2, String>, +fs: List<&2, String>, +term: String, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +rest: List<&2, R.Item>, +hs: {L.all_same_site(fs, ps) == True{} : Bool}, kf: KF(fa, defs, o, t, rest, n, h), kr: KR(fa, defs, o, t, rest, n, h)) ->
  GM(fa, defs, o, U.Tl{ps, term, AT(fs, n), B.Rec.pos(fs), t}, L.grouped(S.app(L.items.pieces(ps, fa, term, n), rest)), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kf(last, buf, k, out, ns)
    case Con{+p, +pt}:
      +at = AT(fs, n)
      +inpos = B.Rec.pos(fs)
      +LN = {B.Line{p, term} : B.Line}
      +it = L.item_of(L.judge(fa, p), LN, at, inpos)
      +rest2 = S.app(L.items.pieces(pt, fa, term, n), rest)
      +hs1 = P.and_true_l(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +hs2 = P.and_true_r(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      +g = L.grouped(it <> rest2)
      %Equal.sym(R.Item, L.item(fa, LN, n), it, U.item_site(fs, p, term, n, fa, hs1)) :
        GM(fa, defs, o, U.Tl{Con{p, pt}, term, at, inpos, t}, L.grouped(_ <> rest2), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}})
      T.BL(st2 => GM(fa, defs, o, tl, g, st2), L.judge(fa, p), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => u => halted_gm(fa, defs, o, tl, g, n, True{}, h, None{}, Nil{}, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped_fk(fa, defs, o, tl, rest2, n, h, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it,
          last2 => buf2 => out2 => grouped_ps(pt, fs, term, t, fa, defs, o, n, h, R.Item.chrom(it), Nil{}, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), rest, hs2, kr)))

# A body line before the first CHROM run, by what -m does with it.
def grouped_fline(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +rest: List<&2, R.Item>, +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, kf: KF(fa, defs, o, t, rest, n, h), kr: KR(fa, defs, o, t, rest, n, h)) ->
  GM(fa, defs, o, U.TLs(t), L.grouped(S.app(L.items.line(pt, fa, l, n), rest)),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}}, l, AT(B.Rec.fields(B.Line.body(l)), n), B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = AT(fs, n)
      +it = L.item(fa, l, n)
      +g = L.grouped(it <> rest)
      T.BL(st2 => GM(fa, defs, o, U.TLs(t), g, st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}}, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_gm(fa, defs, o, U.TLs(t), g, n, True{}, h, None{}, Nil{}, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped_fk(fa, defs, o, U.TLs(t), rest, n, h, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it,
          last2 => buf2 => out2 => kr(R.Item.chrom(it), Nil{}, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))
    case B.Pieces{+ps}:
      grouped_fps(ps, B.Rec.fields(B.Line.body(l)), B.Line.term(l), t, fa, defs, o, n, h, last, buf, k, out, ns, rest,
        SM.split_site(defs, o, B.Line.body(l), ps, hpt), kf, kr)
    case B.Unsplit{+c}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = AT(fs, n)
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      +g = L.grouped(it <> rest)
      U.UL(st2 => GM(fa, defs, o, U.TLs(t), g, st2), L.judge(fa, B.Line.body(l)), c, R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), c, hpt),
        +cd => u => halted_gm(fa, defs, o, U.TLs(t), g, n, True{}, h, None{}, Nil{}, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped_fk(fa, defs, o, U.TLs(t), rest, n, h, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it,
          last2 => buf2 => out2 => kr(R.Item.chrom(it), Nil{}, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))

# The first body line starts the first CHROM run.
law grouped_first:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +last: Maybe<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  GM(fa, defs, o, U.TLs(ls), L.grouped(U.mitems(ls, fa, defs, o, n)), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}})

def grouped_first(ls, fa, defs, o, n, h, last, buf, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      +rest = U.mitems(t, fa, defs, o, 1n+n)
      %Equal.sym(List<&2, R.Item>, U.mitems(l <> t, fa, defs, o, n), S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), rest), U.mitems_cons(l, t, fa, defs, o, n)) :
        GM(fa, defs, o, U.TLs(l <> t), L.grouped(_), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}})
      grouped_fline(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, last, buf, k, out, ns, rest, {==},
        last2 => buf2 => k2 => out2 => ns2 => grouped_first(t, fa, defs, o, 1n+n, h, last2, buf2, k2, out2, ns2),
        gc2 => ge2 => last2 => buf2 => k2 => out2 => ns2 => grouped_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2))

def grouped_head.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, b: Bool, +l: B.Line,
  ih: @h2: String -> GM(fa, defs, o, U.TLs(t), L.grouped(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{False{}, 1n+n, Nil{}}))),
    R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  GM(fa, defs, o, U.TLs(t), L.grouped(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}}))),
    R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)):
  match b:
    case False{}:
      ih(h ++ B.Line.text(l))
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          grouped_first(t, fa, defs, o, 1n+n, "", None{}, Nil{}, k, h ++ R.added(o, term) ++ bd ++ term, ns)

law grouped_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  GM(fa, defs, o, U.TLs(ls), L.grouped(L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}}))),
    R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def grouped_head(ls, fa, defs, o, n, h, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      grouped_head.go(fa, defs, o, t, n, h, k, out, ns, R.is_chrom_line(B.Line.body(l)), l,
        h2 => grouped_head(t, fa, defs, o, 1n+n, h2, k, out, ns))
