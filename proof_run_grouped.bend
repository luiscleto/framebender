import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_sorted.bend as PS

# The law `grouped_in`: a run that succeeds had each CHROM in one run. The
# machine's current CHROM and ended CHROMs are grouped.go's cur and ended.

# The rest of a run that succeeds makes g true.
def GM(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>, +g: Bool, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, o, st))) == 0n : Nat} -> {g == True{} : Bool}

def halted_gm(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +g: Bool,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  GM(fa, o, t, g, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  hc => Empty.absurd({g == True{} : Bool},
    PS.code_10(R.Report.code(R.finish(L.run.go(t, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), hc,
      T.halted_code(t, fa, o, n, i, h, c, e, l, b, k, out, ns)))

# same_run keeps the CHROM bookkeeping (or stops).
def gm_same(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +g: Bool,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>,
  +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item,
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    GM(fa, o, t, g, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  GM(fa, o, t, g, R.same_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, it)):
  T.SR(st2 => GM(fa, o, t, g, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
    +o3 => +bad => +prev => ef => halted_gm(fa, o, t, g, n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
      List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
    +o2 => +l2 => ef => ih(l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), out ++ o2))

def IHR(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    GM(fa, o, t, L.grouped.go(rest, gc2, ge2), R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k, out2, ns, False{}})

def grouped.key(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, b: Bool,
  +eb: {String.eq(gc, R.Item.chrom(it)) == b : Bool}, ih: IHR(fa, o, t, rest, n, h, k, ns)) ->
  GM(fa, o, t, L.grouped.go(it <> rest, gc, ge),
    R.keyed.go(b, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      +c = R.Item.chrom(it)
      +es = Equal.trans(Bool, String.eq(c, gc), String.eq(gc, c), True{}, Q.str_eq_sym(gc, c), eb)
      %Equal.sym(Bool, String.eq(c, gc), True{}, es) :
        GM(fa, o, t, Bool.and(Bool.or(_, Bool.not(R.has(c, gc <> ge))), L.grouped.go(rest, c, Bool.pick(List<&2, String>, _, ge, gc <> ge))),
          R.same_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, it))
      %Q.str_eq_sound(gc, c, eb) : GM(fa, o, t, L.grouped.go(rest, _, ge),
          R.same_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, it))
      gm_same(fa, o, t, L.grouped.go(rest, gc, ge), n, h, Some{gc}, ge, last, buf, k, out, ns, w, it,
        last2 => buf2 => out2 => ih(gc, ge, last2, buf2, out2))
    case False{}:
      +c = R.Item.chrom(it)
      +es = Equal.trans(Bool, String.eq(c, gc), String.eq(gc, c), False{}, Q.str_eq_sym(gc, c), eb)
      %Equal.sym(Bool, String.eq(c, gc), False{}, es) :
        GM(fa, o, t, Bool.and(Bool.or(_, Bool.not(Bool.or(_, R.has(c, ge)))), L.grouped.go(rest, c, Bool.pick(List<&2, String>, _, ge, gc <> ge))),
          R.new_run(R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, w, c, it))
      +g = Bool.and(Bool.not(R.has(c, ge)), L.grouped.go(rest, c, gc <> ge))
      T.NR(st2 => GM(fa, o, t, g, st2), n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}, w, c, it,
        +o3 => +bad => +prev => ef => halted_gm(fa, o, t, g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => ef => eh => halted_gm(fa, o, t, g, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o2,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
        +o2 => +l2 => ef => eh =>
          %Equal.sym(Bool, R.has(c, ge), False{}, eh) :
            GM(fa, o, t, Bool.and(Bool.not(_), L.grouped.go(rest, c, gc <> ge)),
              R.same_run(R.RunSt{n, True{}, h, Some{c}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, False{}}, w, it));
          gm_same(fa, o, t, L.grouped.go(rest, c, gc <> ge), n, h, Some{c}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, w, it,
            last2 => buf2 => out2 => ih(c, gc <> ge, last2, buf2, out2)))

# Within the body, with a current CHROM run.
law grouped_run:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
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
  GM(fa, o, ls, L.grouped.go(T.nitems(ls, fa, n), gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})

def grouped_run(ls, fa, o, n, h, gc, ge, last, buf, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      +st1 = {R.RunSt{1n+n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, 1n+n)
      +rest = T.nitems(t, fa, 1n+n)
      +g = L.grouped.go(it <> rest, gc, ge)
      %Equal.sym(List<&2, R.Item>, T.nitems(l <> t, fa, n), it <> rest, T.nitems_cons(l, t, fa, n)) :
        GM(fa, o, l <> t, L.grouped.go(_, gc, ge), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})
      T.BL(st2 => GM(fa, o, t, g, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_gm(fa, o, t, g, 1n+n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => grouped.key(fa, o, t, rest, 1n+n, h, gc, ge, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, String.eq(gc, R.Item.chrom(it)), {==},
          gc2 => ge2 => last2 => buf2 => out2 => grouped_run(t, fa, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))

# The first body line starts the first CHROM run.
law grouped_first:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +last: Maybe<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  GM(fa, o, ls, L.grouped(T.nitems(ls, fa, n)), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}})

def grouped_first(ls, fa, o, n, h, last, buf, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      +st1 = {R.RunSt{1n+n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, 1n+n)
      +rest = T.nitems(t, fa, 1n+n)
      +c = R.Item.chrom(it)
      +g = L.grouped.go(rest, c, Nil{})
      %Equal.sym(List<&2, R.Item>, T.nitems(l <> t, fa, n), it <> rest, T.nitems_cons(l, t, fa, n)) :
        GM(fa, o, l <> t, L.grouped(_), R.RunSt{n, True{}, h, None{}, Nil{}, last, buf, k, out, ns, False{}})
      T.BL(st2 => GM(fa, o, t, g, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_gm(fa, o, t, g, 1n+n, True{}, h, None{}, Nil{}, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          T.NR(st2 => GM(fa, o, t, g, st2), 1n+n, True{}, h, None{}, Nil{}, last, buf, k2, out, ns2, False{}, R.Opts.w(o), c, it,
            +o3 => +bad => +prev => ef => halted_gm(fa, o, t, g, 1n+n, True{}, h, None{}, Nil{}, last, buf, k2, out ++ o3,
              List.append(&2, B.Note, ns2, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
            +o2 => +l2 => ef => eh => halted_gm(fa, o, t, g, 1n+n, True{}, h, None{}, Nil{}, last, buf, k2, out ++ o2,
              List.append(&2, B.Note, ns2, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
            +o2 => +l2 => ef => eh =>
              gm_same(fa, o, t, g, 1n+n, h, Some{c}, Nil{}, None{}, Nil{}, k2, out ++ o2, ns2, R.Opts.w(o), it,
                last2 => buf2 => out2 => grouped_run(t, fa, o, 1n+n, h, c, Nil{}, last2, buf2, k2, out2, ns2))))

def grouped_head.go(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, b: Bool, +l: B.Line,
  ih: @h2: String -> GM(fa, o, t, L.grouped(L.ItSt.acc(L.items.go(t, fa, L.ItSt{False{}, 1n+n, Nil{}}))),
    R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  GM(fa, o, t, L.grouped(L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}}))),
    R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)):
  match b:
    case False{}:
      ih(h ++ B.Line.text(l))
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          grouped_first(t, fa, o, 1n+n, "", None{}, Nil{}, k, h ++ R.added(o, term) ++ bd ++ term, ns)

law grouped_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  GM(fa, o, ls, L.grouped(L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}}))),
    R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def grouped_head(ls, fa, o, n, h, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      grouped_head.go(fa, o, t, n, h, k, out, ns, R.is_chrom_line(B.Line.body(l)), l,
        h2 => grouped_head(t, fa, o, 1n+n, h2, k, out, ns))
