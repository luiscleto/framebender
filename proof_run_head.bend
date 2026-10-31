import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_text.bend as X
import ./proof_run_rec.bend as C
import ./proof_run_sorted.bend as PS
import ./proof_run_grouped.bend as PG
import ./proof_run_line.bend as N
import ./proof_run_tail.bend as U

# The header of a VCF text for twice_run: the lines before the first #CHROM
# line, that line, and the rest; how a run, its items, its header and body()
# see that split.

def isc(+l: B.Line) -> Bool:
  R.is_chrom_line(B.Line.body(l))

def pre_c.go(b: Bool, l: B.Line, r: List<&2, B.Line>) -> List<&2, B.Line>:
  match b:
    case True{}:
      Nil{}
    case False{}:
      l <> r

# The lines before the first #CHROM line.
def pre_c(ls: List<&2, B.Line>) -> List<&2, B.Line>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> t:
      pre_c.go(isc(l), l, pre_c(t))

def post_c.go(b: Bool, t: List<&2, B.Line>, r: List<&2, B.Line>) -> List<&2, B.Line>:
  match b:
    case True{}:
      t
    case False{}:
      r

# The lines after the first #CHROM line.
def post_c(ls: List<&2, B.Line>) -> List<&2, B.Line>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +t:
      post_c.go(isc(l), t, post_c(t))

def cl_c.go(b: Bool, l: B.Line, r: B.Line) -> B.Line:
  match b:
    case True{}:
      l
    case False{}:
      r

# The first #CHROM line.
def cl_c(ls: List<&2, B.Line>) -> B.Line:
  match ls:
    case Nil{}:
      B.Line{"", ""}
    case +l <> t:
      cl_c.go(isc(l), l, cl_c(t))

def has_c(ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> t:
      isc(l) || has_c(t)

def idx_c.go(b: Bool, +n: Nat, r: Nat) -> Nat:
  match b:
    case True{}:
      n
    case False{}:
      r

# The line count after the first #CHROM line.
def idx_c(ls: List<&2, B.Line>, +n: Nat) -> Nat:
  match ls:
    case Nil{}:
      n
    case +l <> t:
      idx_c.go(isc(l), 1n+n, idx_c(t, 1n+n))

def hst(+n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) -> R.RunSt:
  R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}

def bst(+n: Nat, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) -> R.RunSt:
  R.RunSt{n, True{}, "", None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}

def hr.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, b: Bool, +l: B.Line, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +eb: {isc(l) == b : Bool}, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: @h2: String -> {has_c(t) == True{} : Bool} ->
    {L.run.go(t, fa, defs, o, hst(1n+n, h2, k, out, ns)) == L.run.go(post_c(t), fa, defs, o, bst(idx_c(t, 1n+n), k, L.head.go(t, o, False{}, h2), ns)) : R.RunSt}) ->
  {L.run.go(t, fa, defs, o, R.head_line(b, hst(1n+n, h, k, out, ns), o, l)) ==
    L.run.go(post_c.go(b, t, post_c(t)), fa, defs, o, bst(idx_c.go(b, 1n+n, idx_c(t, 1n+n)), k,
      L.head.go(t, o, b, Bool.pick(String, b, h ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l), h ++ B.Line.text(l))), ns)) : R.RunSt}:
  match b:
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          +hd = h ++ R.added(o, term) ++ bd ++ term
          %PS.head_done(t, o, hd) : {L.run.go(t, fa, defs, o, bst(1n+n, k, _, ns)) == L.run.go(t, fa, defs, o, bst(1n+n, k, L.head.go(t, o, True{}, hd), ns)) : R.RunSt}
          {==}
    case False{}:
      ih(h ++ B.Line.text(l), hc)

# The run over the header, up to the first #CHROM line.
law hdr_run:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hc: {has_c(ls) == True{} : Bool}
  {L.run.go(ls, fa, defs, o, hst(n, h, k, out, ns)) == L.run.go(post_c(ls), fa, defs, o, bst(idx_c(ls, n), k, L.head.go(ls, o, False{}, h), ns)) : R.RunSt}

def hdr_run(ls, fa, defs, o, n, h, k, out, ns, hc):
  match ls:
    case Nil{}:
      Empty.absurd({L.run.go(Nil{}, fa, defs, o, hst(n, h, k, out, ns)) == L.run.go(Nil{}, fa, defs, o, bst(n, k, h, ns)) : R.RunSt}, P.false_ne_true(hc))
    case +l <> +t:
      hr.go(fa, defs, o, isc(l), l, t, n, h, k, out, ns, {==}, hc, h2 => hc2 => hdr_run(t, fa, defs, o, 1n+n, h2, k, out, ns, hc2))

def hi.go(+fa: List<&2, B.Contig>, b: Bool, +t: List<&2, B.Line>, +n: Nat, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: {has_c(t) == True{} : Bool} -> {L.ItSt.acc(L.items.go(t, fa, L.ItSt{False{}, 1n+n, Nil{}})) == T.nitems(post_c(t), fa, idx_c(t, 1n+n)) : List<&2, R.Item>}) ->
  {L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}})) == T.nitems(post_c.go(b, t, post_c(t)), fa, idx_c.go(b, 1n+n, idx_c(t, 1n+n))) : List<&2, R.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(hc)

# The items of a text with a #CHROM line are those of the lines after it.
law hdr_items:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +n: Nat
  for +hc: {has_c(ls) == True{} : Bool}
  {L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}})) == T.nitems(post_c(ls), fa, idx_c(ls, n)) : List<&2, R.Item>}

def hdr_items(ls, fa, n, hc):
  match ls:
    case Nil{}:
      Empty.absurd({Nil{} == T.nitems(Nil{}, fa, n) : List<&2, R.Item>}, P.false_ne_true(hc))
    case +l <> +t:
      hi.go(fa, isc(l), t, n, hc, h2 => hdr_items(t, fa, 1n+n, h2))

def hm.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, b: Bool, +t: List<&2, B.Line>, +n: Nat, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: {has_c(t) == True{} : Bool} -> {L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{False{}, 1n+n, Nil{}})) == U.mitems(post_c(t), fa, defs, o, idx_c(t, 1n+n)) : List<&2, R.Item>}) ->
  {L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}})) == U.mitems(post_c.go(b, t, post_c(t)), fa, defs, o, idx_c.go(b, 1n+n, idx_c(t, 1n+n))) : List<&2, R.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(hc)

# The records a run writes, for a text with a #CHROM line: those of the lines
# after it.
law hdr_mitems:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +hc: {has_c(ls) == True{} : Bool}
  {L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}})) == U.mitems(post_c(ls), fa, defs, o, idx_c(ls, n)) : List<&2, R.Item>}

def hdr_mitems(ls, fa, defs, o, n, hc):
  match ls:
    case Nil{}:
      Empty.absurd({Nil{} == U.mitems(Nil{}, fa, defs, o, n) : List<&2, R.Item>}, P.false_ne_true(hc))
    case +l <> +t:
      hm.go(fa, defs, o, isc(l), t, n, hc, h2 => hdr_mitems(t, fa, defs, o, 1n+n, h2))

def al1(+t: String) -> B.Line:
  B.Line{"##framebender_normVersion=" ++ R.version(), t}

def al2(o: B.Opts, +t: String) -> B.Line:
  match o:
    case B.Opts{s, w, om_m, om_z, args}:
      B.Line{"##framebender_normCommand=norm" ++ R.args_text(args), t}

law added_eq:
  for +o: B.Opts
  for +t: String
  {R.added(o, t) == B.Line.text(al1(t)) ++ B.Line.text(al2(o, t)) : String}

def added_eq(o, t):
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      {==}

# The header lines as written: those before #CHROM, the two added lines, #CHROM.
def Hl(+ls: List<&2, B.Line>, +o: B.Opts) -> List<&2, B.Line>:
  +cl = cl_c(ls)
  X.lapp(pre_c(ls), [al1(B.Line.term(cl)), al2(o, B.Line.term(cl)), cl])

def hh.go(+o: B.Opts, b: Bool, +l: B.Line, +t: List<&2, B.Line>, +h: String, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: @h2: String -> {has_c(t) == True{} : Bool} -> {L.head.go(t, o, False{}, h2) == h2 ++ B.Lines.text(Hl(t, o)) : String}) ->
  {L.head.go(t, o, b, Bool.pick(String, b, h ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l), h ++ B.Line.text(l))) ==
    h ++ B.Lines.text(X.lapp(pre_c.go(b, l, pre_c(t)), [al1(B.Line.term(cl_c.go(b, l, cl_c(t)))), al2(o, B.Line.term(cl_c.go(b, l, cl_c(t)))), cl_c.go(b, l, cl_c(t))])) : String}:
  match b:
    case True{}:
      +tm = B.Line.term(l)
      +A1 = B.Line.text(al1(tm))
      +A2 = B.Line.text(al2(o, tm))
      +tl = B.Line.text(l)
      %Equal.sym(String, L.head.go(t, o, True{}, h ++ R.added(o, tm) ++ tl), h ++ R.added(o, tm) ++ tl, PS.head_done(t, o, h ++ R.added(o, tm) ++ tl)) : {_ == h ++ (A1 ++ (A2 ++ (tl ++ ""))) : String}
      %Equal.sym(String, tl ++ "", tl, Q.s_append_nil(tl)) : {h ++ R.added(o, tm) ++ tl == h ++ (A1 ++ (A2 ++ _)) : String}
      %Q.s_append_assoc(A1, A2, tl) : {h ++ R.added(o, tm) ++ tl == h ++ _ : String}
      %Equal.sym(String, R.added(o, tm), A1 ++ A2, added_eq(o, tm)) : {h ++ _ ++ tl == h ++ ((A1 ++ A2) ++ tl) : String}
      {==}
    case False{}:
      +tl = B.Line.text(l)
      %Equal.sym(String, L.head.go(t, o, False{}, h ++ tl), (h ++ tl) ++ B.Lines.text(Hl(t, o)), ih(h ++ tl, hc)) : {_ == h ++ B.Lines.text(l <> Hl(t, o)) : String}
      Q.s_append_assoc(h, tl, B.Lines.text(Hl(t, o)))

# The header string is the text of the header lines.
law hdr_head:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  for +h: String
  for +hc: {has_c(ls) == True{} : Bool}
  {L.head.go(ls, o, False{}, h) == h ++ B.Lines.text(Hl(ls, o)) : String}

def hdr_head(ls, o, h, hc):
  match ls:
    case Nil{}:
      Empty.absurd({h == h ++ B.Lines.text(Hl(Nil{}, o)) : String}, P.false_ne_true(hc))
    case +l <> +t:
      hh.go(o, isc(l), l, t, h, hc, h2 => hc2 => hdr_head(t, o, h2, hc2))

# A body line: stops, or goes on (and then go_on holds).
def BLK(-M: R.RunSt -> Type, r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hstop: @cd: B.Code -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: {N.go_on(o, r) == True{} : Bool} -> @nts: List<&2, B.Note> -> @k2: R.Cnt -> M(R.keyed(st, R.Opts.w(o), L.item_of(r, l, at, inpos), nts, k2))) ->
  M(R.body_line(r, st, o, l, at, inpos)):
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      hstop(B.Malformed{})
    case B.Res{B.NoContig{}, k, t, s}:
      hstop(B.UnknownChrom{})
    case B.Res{B.Problem{+c}, k, t, s}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              hstop(c)
            case False{}:
              hkey({==}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))
    case B.Res{B.Skipped{}, k, t, s}:
      hkey({==}, Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +k, +t, +s}:
      match l:
        case B.Line{+bd, +term}:
          hkey({==}, R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, bd)), False{}, False{}))

# What a body line needs for the run to go on, by what -m does with it: its
# outcome (Whole), each record's (Pieces), or, unsplit, its outcome and -c w.
def pgo(ps: List<&2, String>, +fa: List<&2, B.Contig>, +o: B.Opts) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +p <> t:
      N.go_on(o, L.judge(fa, p)) && pgo(t, fa, o)

def lgo.go(pt: B.Parts, +fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line) -> Bool:
  match pt:
    case B.Whole{}:
      N.go_on(o, L.judge(fa, B.Line.body(l)))
    case B.Pieces{ps}:
      pgo(ps, fa, o)
    case B.Unsplit{c}:
      N.go_on(o, L.judge(fa, B.Line.body(l))) && Bool.not(R.Opts.strict(o))

def lgo(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +l: B.Line) -> Bool:
  lgo.go(B.Rec.parts(defs, o, B.Line.body(l)), fa, o, l)

def all_lgo(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      lgo(fa, defs, o, l) && all_lgo(t, fa, defs, o)

# An outcome goes on exactly when it does not stop the run.
law go_stop:
  for +o: B.Opts
  for +r: B.Res
  {Bool.not(L.stops(r, R.Opts.strict(o))) == N.go_on(o, r) : Bool}

def go_stop(o, r):
  match r:
    case B.Res{B.Broken{}, +k, +t, +s}:
      {==}
    case B.Res{B.NoContig{}, +k, +t, +s}:
      {==}
    case B.Res{B.Problem{+c}, +k, +t, +s}:
      {==}
    case B.Res{B.Skipped{}, +k, +t, +s}:
      {==}
    case B.Res{B.Normalized{}, +k, +t, +s}:
      {==}

def ug.s(-M: R.RunSt -> Type, s: Bool, +r: B.Res, +c: B.Code, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +hs: {L.stops(r, R.Opts.strict(o)) == s : Bool},
  hstop: @cd: B.Code -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: {Bool.and(N.go_on(o, r), Bool.not(R.Opts.strict(o))) == True{} : Bool} -> @nts: List<&2, B.Note> -> @k2: R.Cnt ->
    M(R.keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, nts, k2))) ->
  M(Bool.pick(R.RunSt, s, R.body_line(r, st, o, l, at, inpos), R.problem_line(R.Opts.strict(o), st, R.Opts.w(o), c, l, at, inpos))):
  match s:
    case True{}:
      BLK(M, r, st, o, l, at, inpos, hstop,
        hg => +nts => +k2 => Empty.absurd(M(R.keyed(st, R.Opts.w(o), L.item_of(r, l, at, inpos), nts, k2)),
          P.false_ne_true(Equal.trans(Bool, False{}, N.go_on(o, r), True{},
            {(%hs : {Bool.not(_) == N.go_on(o, r) : Bool}; go_stop(o, r)) : {False{} == N.go_on(o, r) : Bool}}, hg))))
    case False{}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              hstop(c)
            case False{}:
              +o2 = {B.Opts{False{}, w, om_m, om_z, a} : B.Opts}
              +hg = {(%go_stop(o2, r) : {_ == True{} : Bool}; %Equal.sym(Bool, L.stops(r, False{}), False{}, hs) : {Bool.not(_) == True{} : Bool}; {==}) :
                {N.go_on(o2, r) == True{} : Bool}}
              hkey({(%Equal.sym(Bool, N.go_on(o2, r), True{}, hg) : {Bool.and(_, True{}) == True{} : Bool}; {==}) : {Bool.and(N.go_on(o2, r), True{}) == True{} : Bool}}, [B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

# A line -m cannot split (code c): it stops the run, or goes on (then its
# outcome goes on and the run is under -c w) as the line as it came.
def UG(-M: R.RunSt -> Type, +r: B.Res, +c: B.Code, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hstop: @cd: B.Code -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: {Bool.and(N.go_on(o, r), Bool.not(R.Opts.strict(o))) == True{} : Bool} -> @nts: List<&2, B.Note> -> @k2: R.Cnt ->
    M(R.keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, nts, k2))) ->
  M(L.unsplit_in(r, c, o, st, l, at, inpos)):
  ug.s(M, L.stops(r, R.Opts.strict(o)), r, c, st, o, l, at, inpos, {==}, hstop, hkey)

def IHB(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +tl: U.Tl, +g: Bool, +n: Nat, +h: String, +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @c2: Maybe<&2, String> -> @e2: List<&2, String> -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    PG.GM(fa, defs, o, tl, g, R.RunSt{n, True{}, h, c2, e2, last2, buf2, k, out2, ns, False{}})

def bg.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +tl: U.Tl, +g: Bool, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +it: R.Item, b: Bool,
  ih: IHB(fa, defs, o, tl, g, n, h, k, ns)) ->
  PG.GM(fa, defs, o, tl, g, R.keyed.go(b, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, R.Opts.w(o), R.Item.chrom(it), it)):
  match b:
    case True{}:
      +w = R.Opts.w(o)
      PG.gm_same(fa, defs, o, tl, g, n, h, c, e, last, buf, k, out, ns, w, it, last2 => buf2 => out2 => ih(c, e, last2, buf2, out2))
    case False{}:
      +w = R.Opts.w(o)
      +ch = R.Item.chrom(it)
      T.NR(st2 => PG.GM(fa, defs, o, tl, g, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, ch, it,
        +o3 => +bad => +prev => ef => PG.halted_gm(fa, defs, o, tl, g, n, True{}, h, c, e, last, buf, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => ef => eh => PG.halted_gm(fa, defs, o, tl, g, n, True{}, h, c, e, last, buf, k, out ++ o2,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
        +o2 => +l2 => ef => eh =>
          PG.gm_same(fa, defs, o, tl, g, n, h, Some{ch}, R.push_cur(c, e), None{}, Nil{}, k, out ++ o2, ns, w, it,
            last2 => buf2 => out2 => ih(Some{ch}, R.push_cur(c, e), last2, buf2, out2)))

# The rest of the lines from any state in the body (the run's line number n).
def KB(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String) -> Type:
  @c: Maybe<&2, String> -> @e: List<&2, String> -> @last: Maybe<&2, R.Item> -> @buf: List<&2, R.Item> -> @k: R.Cnt -> @out: String -> @ns: List<&2, B.Note> ->
    PG.GM(fa, defs, o, U.TLs(t), all_lgo(t, fa, defs, o), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}})

# The records of a split line, then the rest of the lines.
def bg.ps(ps: List<&2, String>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +term: String, +at: B.At, +inpos: Nat, +t: List<&2, B.Line>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String,
  +ns: List<&2, B.Note>, kb: KB(fa, defs, o, t, n, h)) ->
  PG.GM(fa, defs, o, U.Tl{ps, term, at, inpos, t}, Bool.and(pgo(ps, fa, o), all_lgo(t, fa, defs, o)), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kb(c, e, last, buf, k, out, ns)
    case Con{+p, +pt}:
      +st = {R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}} : R.RunSt}
      +LN = {B.Line{p, term} : B.Line}
      +r = L.judge(fa, p)
      +g = Bool.and(pgo(pt, fa, o), all_lgo(t, fa, defs, o))
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      BLK(st2 => PG.GM(fa, defs, o, tl, Bool.and(Bool.and(N.go_on(o, r), pgo(pt, fa, o)), all_lgo(t, fa, defs, o)), st2), r, st, o, LN, at, inpos,
        +cd => PG.halted_gm(fa, defs, o, tl, Bool.and(Bool.and(N.go_on(o, r), pgo(pt, fa, o)), all_lgo(t, fa, defs, o)), n, True{}, h, c, e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        hg => +nts => +k2 =>
          +it = L.item_of(r, LN, at, inpos)
          %Equal.sym(Bool, N.go_on(o, r), True{}, hg) :
            PG.GM(fa, defs, o, tl, Bool.and(Bool.and(_, pgo(pt, fa, o)), all_lgo(t, fa, defs, o)), R.keyed(st, R.Opts.w(o), it, nts, k2))
          bg.key(fa, defs, o, tl, g, n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it, R.is_cur(c, R.Item.chrom(it)),
            c2 => e2 => last2 => buf2 => out2 => bg.ps(pt, fa, defs, o, term, at, inpos, t, n, h, c2, e2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), kb)))

# One body line, by what -m does with it.
def bg.line(pt: B.Parts, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +l: B.Line, +t: List<&2, B.Line>, +at: B.At, +inpos: Nat,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String,
  +ns: List<&2, B.Note>, kb: KB(fa, defs, o, t, n, h)) ->
  PG.GM(fa, defs, o, U.TLs(t), Bool.and(lgo.go(pt, fa, o, l), all_lgo(t, fa, defs, o)),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, l, at, inpos)):
  match pt:
    case B.Whole{}:
      +st = {R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}} : R.RunSt}
      +G = all_lgo(t, fa, defs, o)
      +r = L.judge(fa, B.Line.body(l))
      BLK(st2 => PG.GM(fa, defs, o, U.TLs(t), Bool.and(N.go_on(o, r), G), st2), r, st, o, l, at, inpos,
        +cd => PG.halted_gm(fa, defs, o, U.TLs(t), Bool.and(N.go_on(o, r), G), n, True{}, h, c, e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        hg => +nts => +k2 =>
          +it = L.item_of(r, l, at, inpos)
          %Equal.sym(Bool, N.go_on(o, r), True{}, hg) :
            PG.GM(fa, defs, o, U.TLs(t), Bool.and(_, G), R.keyed(st, R.Opts.w(o), it, nts, k2))
          bg.key(fa, defs, o, U.TLs(t), G, n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it, R.is_cur(c, R.Item.chrom(it)),
            c2 => e2 => last2 => buf2 => out2 => kb(c2, e2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))
    case B.Pieces{+ps}:
      bg.ps(ps, fa, defs, o, B.Line.term(l), at, inpos, t, n, h, c, e, last, buf, k, out, ns, kb)
    case B.Unsplit{+cu}:
      +st = {R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}} : R.RunSt}
      +G = all_lgo(t, fa, defs, o)
      +r = L.judge(fa, B.Line.body(l))
      +q = Bool.and(N.go_on(o, r), Bool.not(R.Opts.strict(o)))
      UG(st2 => PG.GM(fa, defs, o, U.TLs(t), Bool.and(q, G), st2), r, cu, st, o, l, at, inpos,
        +cd => PG.halted_gm(fa, defs, o, U.TLs(t), Bool.and(q, G), n, True{}, h, c, e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        hq => +nts => +k2 =>
          +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
          %Equal.sym(Bool, q, True{}, hq) :
            PG.GM(fa, defs, o, U.TLs(t), Bool.and(_, G), R.keyed(st, R.Opts.w(o), it, nts, k2))
          bg.key(fa, defs, o, U.TLs(t), G, n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), it, R.is_cur(c, R.Item.chrom(it)),
            c2 => e2 => last2 => buf2 => out2 => kb(c2, e2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts))))

# A run that succeeds lets every body line go on.
law body_go:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +last: Maybe<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  PG.GM(fa, defs, o, U.TLs(ls), all_lgo(ls, fa, defs, o), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}})

def body_go(ls, fa, defs, o, n, h, c, e, last, buf, k, out, ns):
  match ls:
    case Nil{}:
      hc => {==}
    case +l <> +t:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      bg.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, defs, o, l, t, at, B.Rec.pos(fs), 1n+n, h, c, e, last, buf, k, out, ns,
        c2 => e2 => last2 => buf2 => k2 => out2 => ns2 => body_go(t, fa, defs, o, 1n+n, h, c2, e2, last2, buf2, k2, out2, ns2))

def hh_has.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, b: Bool, +l: B.Line, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  ih: @h2: String -> PG.GM(fa, defs, o, U.TLs(t), has_c(t), hst(1n+n, h2, k, out, ns))) ->
  PG.GM(fa, defs, o, U.TLs(t), Bool.or(b, has_c(t)), R.head_line(b, hst(1n+n, h, k, out, ns), o, l)):
  match b:
    case True{}:
      hc => {==}
    case False{}:
      ih(h ++ B.Line.text(l))

# A run that succeeds has a #CHROM line.
law hdr_has:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  PG.GM(fa, defs, o, U.TLs(ls), has_c(ls), hst(n, h, k, out, ns))

def hdr_has(ls, fa, defs, o, n, h, k, out, ns):
  match ls:
    case Nil{}:
      hc => Empty.absurd({False{} == True{} : Bool}, PS.code_10(1n, hc, {==}))
    case +l <> +t:
      hh_has.go(fa, defs, o, isc(l), l, t, n, h, k, out, ns, h2 => hdr_has(t, fa, defs, o, 1n+n, h2, k, out, ns))

# Splitting at the first #CHROM line
# ==================================

def all_nc(ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      Bool.not(isc(l)) && all_nc(t)

def BB(ls: List<&2, B.Line>) -> Type:
  {has_c(ls) == True{} : Bool}

def sp.go(b: Bool, +l: B.Line, +t: List<&2, B.Line>, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: {has_c(t) == True{} : Bool} -> {t == X.lapp(pre_c(t), cl_c(t) <> post_c(t)) : List<&2, B.Line>}) ->
  {l <> t == X.lapp(pre_c.go(b, l, pre_c(t)), cl_c.go(b, l, cl_c(t)) <> post_c.go(b, t, post_c(t))) : List<&2, B.Line>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %ih(hc) : {l <> t == l <> _ : List<&2, B.Line>}
      {==}

law hs_split:
  for +ls: List<&2, B.Line>
  for +hc: {has_c(ls) == True{} : Bool}
  {ls == X.lapp(pre_c(ls), cl_c(ls) <> post_c(ls)) : List<&2, B.Line>}

def hs_split(ls, hc):
  match ls:
    case Nil{}:
      Empty.absurd({Nil{} == X.lapp(Nil{}, B.Line{"", ""} <> Nil{}) : List<&2, B.Line>}, P.false_ne_true(hc))
    case +l <> +t:
      sp.go(isc(l), l, t, hc, h2 => hs_split(t, h2))

def pnc.go(b: Bool, +l: B.Line, +t: List<&2, B.Line>, +eb: {isc(l) == b : Bool}, +ih: {all_nc(pre_c(t)) == True{} : Bool}) ->
  {all_nc(pre_c.go(b, l, pre_c(t))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, isc(l), False{}, eb) : {Bool.and(Bool.not(_), all_nc(pre_c(t))) == True{} : Bool}
      ih

law pre_nc:
  for +ls: List<&2, B.Line>
  {all_nc(pre_c(ls)) == True{} : Bool}

def pre_nc(ls):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      pnc.go(isc(l), l, t, {==}, pre_nc(t))

def cli.go(b: Bool, +l: B.Line, +t: List<&2, B.Line>, +eb: {isc(l) == b : Bool}, hc: {Bool.or(b, has_c(t)) == True{} : Bool},
  ih: {has_c(t) == True{} : Bool} -> {isc(cl_c(t)) == True{} : Bool}) -> {isc(cl_c.go(b, l, cl_c(t))) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      ih(hc)

law cl_isc:
  for +ls: List<&2, B.Line>
  for +hc: {has_c(ls) == True{} : Bool}
  {isc(cl_c(ls)) == True{} : Bool}

def cl_isc(ls, hc):
  match ls:
    case Nil{}:
      Empty.absurd({isc(B.Line{"", ""}) == True{} : Bool}, P.false_ne_true(hc))
    case +l <> +t:
      cli.go(isc(l), l, t, {==}, hc, h2 => cl_isc(t, h2))

law all_good_app:
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  for +h1: {X.all_good(xs) == True{} : Bool}
  for +h2: {X.all_good(ys) == True{} : Bool}
  {X.all_good(X.lapp(xs, ys)) == True{} : Bool}

def all_good_app(xs, ys, h1, h2):
  match xs:
    case Nil{}:
      h2
    case +x <> +t:
      S.and_intro(X.goodb(x), X.all_good(X.lapp(t, ys)), P.and_true_l(X.goodb(x), X.all_good(t), h1),
        all_good_app(t, ys, P.and_true_r(X.goodb(x), X.all_good(t), h1), h2))

law all_good_l:
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  for +h: {X.all_good(X.lapp(xs, ys)) == True{} : Bool}
  {X.all_good(xs) == True{} : Bool}

def all_good_l(xs, ys, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      S.and_intro(X.goodb(x), X.all_good(t), P.and_true_l(X.goodb(x), X.all_good(X.lapp(t, ys)), h),
        all_good_l(t, ys, P.and_true_r(X.goodb(x), X.all_good(X.lapp(t, ys)), h)))

law all_good_r:
  for +xs: List<&2, B.Line>
  for +ys: List<&2, B.Line>
  for +h: {X.all_good(X.lapp(xs, ys)) == True{} : Bool}
  {X.all_good(ys) == True{} : Bool}

def all_good_r(xs, ys, h):
  match xs:
    case Nil{}:
      h
    case +x <> +t:
      all_good_r(t, ys, P.and_true_r(X.goodb(x), X.all_good(X.lapp(t, ys)), h))

law nc_head:
  for +p: B.Line
  for +t: List<&2, B.Line>
  for +h: {all_nc(p <> t) == True{} : Bool}
  {isc(p) == False{} : Bool}

def nc_head(p, t, h):
  P.not_true(isc(p), P.and_true_l(Bool.not(isc(p)), all_nc(t), h))

law nc_tail:
  for +p: B.Line
  for +t: List<&2, B.Line>
  for +h: {all_nc(p <> t) == True{} : Bool}
  {all_nc(t) == True{} : Bool}

def nc_tail(p, t, h):
  P.and_true_r(Bool.not(isc(p)), all_nc(t), h)

# Splitting a text with no #CHROM line before c, a #CHROM line.
law dec_pre:
  for +ps: List<&2, B.Line>
  for +c: B.Line
  for +rs: List<&2, B.Line>
  for +hp: {all_nc(ps) == True{} : Bool}
  for +hc: {isc(c) == True{} : Bool}
  {pre_c(X.lapp(ps, c <> rs)) == ps : List<&2, B.Line>}

def dec_pre(ps, c, rs, hp, hc):
  match ps:
    case Nil{}:
      %Equal.sym(Bool, isc(c), True{}, hc) : {pre_c.go(_, c, pre_c(rs)) == Nil{} : List<&2, B.Line>}
      {==}
    case +p <> +t:
      %Equal.sym(Bool, isc(p), False{}, nc_head(p, t, hp)) : {pre_c.go(_, p, pre_c(X.lapp(t, c <> rs))) == p <> t : List<&2, B.Line>}
      %Equal.sym(List<&2, B.Line>, pre_c(X.lapp(t, c <> rs)), t, dec_pre(t, c, rs, nc_tail(p, t, hp), hc)) : {p <> _ == p <> t : List<&2, B.Line>}
      {==}

law dec_cl:
  for +ps: List<&2, B.Line>
  for +c: B.Line
  for +rs: List<&2, B.Line>
  for +hp: {all_nc(ps) == True{} : Bool}
  for +hc: {isc(c) == True{} : Bool}
  {cl_c(X.lapp(ps, c <> rs)) == c : B.Line}

def dec_cl(ps, c, rs, hp, hc):
  match ps:
    case Nil{}:
      %Equal.sym(Bool, isc(c), True{}, hc) : {cl_c.go(_, c, cl_c(rs)) == c : B.Line}
      {==}
    case +p <> +t:
      %Equal.sym(Bool, isc(p), False{}, nc_head(p, t, hp)) : {cl_c.go(_, p, cl_c(X.lapp(t, c <> rs))) == c : B.Line}
      dec_cl(t, c, rs, nc_tail(p, t, hp), hc)

law dec_post:
  for +ps: List<&2, B.Line>
  for +c: B.Line
  for +rs: List<&2, B.Line>
  for +hp: {all_nc(ps) == True{} : Bool}
  for +hc: {isc(c) == True{} : Bool}
  {post_c(X.lapp(ps, c <> rs)) == rs : List<&2, B.Line>}

def dec_post(ps, c, rs, hp, hc):
  match ps:
    case Nil{}:
      %Equal.sym(Bool, isc(c), True{}, hc) : {post_c.go(_, rs, post_c(rs)) == rs : List<&2, B.Line>}
      {==}
    case +p <> +t:
      %Equal.sym(Bool, isc(p), False{}, nc_head(p, t, hp)) : {post_c.go(_, X.lapp(t, c <> rs), post_c(X.lapp(t, c <> rs))) == rs : List<&2, B.Line>}
      dec_post(t, c, rs, nc_tail(p, t, hp), hc)

law dec_has:
  for +ps: List<&2, B.Line>
  for +c: B.Line
  for +rs: List<&2, B.Line>
  for +hp: {all_nc(ps) == True{} : Bool}
  for +hc: {isc(c) == True{} : Bool}
  {has_c(X.lapp(ps, c <> rs)) == True{} : Bool}

def dec_has(ps, c, rs, hp, hc):
  match ps:
    case Nil{}:
      S.or_true_l(isc(c), has_c(rs), hc)
    case +p <> +t:
      S.or_true_rr(isc(p), has_c(X.lapp(t, c <> rs)), dec_has(t, c, rs, nc_tail(p, t, hp), hc))

# body() of a split text
# ======================

law bgo2:
  for +rs: List<&2, B.Line>
  for +acc: String
  {L.body.go(rs, True{}, acc) == acc ++ B.Lines.text(rs) : String}

def bgo2(rs, acc):
  match rs:
    case Nil{}:
      Equal.sym(String, acc ++ "", acc, Q.s_append_nil(acc))
    case +l <> +t:
      %Equal.sym(String, L.body.go(t, True{}, acc ++ B.Line.text(l)), (acc ++ B.Line.text(l)) ++ B.Lines.text(t), bgo2(t, acc ++ B.Line.text(l))) :
        {_ == acc ++ (B.Line.text(l) ++ B.Lines.text(t)) : String}
      Q.s_append_assoc(acc, B.Line.text(l), B.Lines.text(t))

law bgo1:
  for +ps: List<&2, B.Line>
  for +c: B.Line
  for +rs: List<&2, B.Line>
  for +acc: String
  for +hp: {all_nc(ps) == True{} : Bool}
  for +hc: {isc(c) == True{} : Bool}
  {L.body.go(X.lapp(ps, c <> rs), False{}, acc) == acc ++ B.Lines.text(rs) : String}

def bgo1(ps, c, rs, acc, hp, hc):
  match ps:
    case Nil{}:
      %Equal.sym(Bool, isc(c), True{}, hc) : {L.body.go(rs, _, acc) == acc ++ B.Lines.text(rs) : String}
      bgo2(rs, acc)
    case +p <> +t:
      %Equal.sym(Bool, isc(p), False{}, nc_head(p, t, hp)) : {L.body.go(X.lapp(t, c <> rs), _, acc) == acc ++ B.Lines.text(rs) : String}
      bgo1(t, c, rs, acc, nc_tail(p, t, hp), hc)

# The two added lines
# ===================

def cc.y(+x: U32, +c: Char, y: Bool, +ey: {Char.is_eq(Chr{x}, c) == y : Bool},
  +eb: {Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)) == False{} : Bool},
  +hcl: {U32.is_lt(B.Char.code(c), 32) == True{} : Bool}) -> {Bool.not(y) == True{} : Bool}:
  match y:
    case False{}:
      {==}
    case True{}:
      +ex = Equal.cong(Char, U32, z => B.Char.code(z), Chr{x}, c, X.char_eq_sound(Chr{x}, c, ey))
      +e2 = {(%ex : {Bool.or(U32.is_lt(_, 32), U32.is_eq(_, 127)) == False{} : Bool}; eb) :
        {Bool.or(U32.is_lt(B.Char.code(c), 32), U32.is_eq(B.Char.code(c), 127)) == False{} : Bool}}
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
        P.true_ne_false(Equal.trans(Bool, True{}, Bool.or(U32.is_lt(B.Char.code(c), 32), U32.is_eq(B.Char.code(c), 127)), False{},
          (%Equal.sym(Bool, U32.is_lt(B.Char.code(c), 32), True{}, hcl) : {True{} == Bool.or(_, U32.is_eq(B.Char.code(c), 127)) : Bool}; {==}), e2)))

def cc.go(+x: U32, +c: Char, b: Bool, +eb: {Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)) == b : Bool},
  +hsp: {Char.is_eq(' ', c) == False{} : Bool}, +hcl: {U32.is_lt(B.Char.code(c), 32) == True{} : Bool}) ->
  {Bool.not(Char.is_eq(Bool.pick(Char, b, ' ', Chr{x}), c)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Char.is_eq(' ', c), False{}, hsp) : {Bool.not(_) == True{} : Bool}
      {==}
    case False{}:
      cc.y(x, c, Char.is_eq(Chr{x}, c), {==}, eb, hcl)

law clean_noc:
  for +s: String
  for +c: Char
  for +hsp: {Char.is_eq(' ', c) == False{} : Bool}
  for +hcl: {U32.is_lt(B.Char.code(c), 32) == True{} : Bool}
  {X.no_c(R.clean(s), c) == True{} : Bool}

def clean_noc(s, c, hsp, hcl):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      S.and_intro(Bool.not(Char.is_eq(R.clean.char(Chr{x}), c)), X.no_c(R.clean(t), c),
        cc.go(x, c, Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)), {==}, hsp, hcl), clean_noc(t, c, hsp, hcl))

law args_noc:
  for +xs: List<&2, String>
  for +c: Char
  for +hsp: {Char.is_eq(' ', c) == False{} : Bool}
  for +hcl: {U32.is_lt(B.Char.code(c), 32) == True{} : Bool}
  {X.no_c(R.args_text(xs), c) == True{} : Bool}

def args_noc(xs, c, hsp, hcl):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      X.no_c_app(" ", R.clean(x) ++ R.args_text(t), c, S.and_intro(Bool.not(Char.is_eq(' ', c)), True{}, (%Equal.sym(Bool, Char.is_eq(' ', c), False{}, hsp) : {Bool.not(_) == True{} : Bool}; {==}), {==}),
        X.no_c_app(R.clean(x), R.args_text(t), c, clean_noc(x, c, hsp, hcl), args_noc(t, c, hsp, hcl)))

def term_ok.go(+bd: String, +t: String, x: Bool, +ex: {String.eq(t, "\r\n") == x : Bool},
  +h: {Bool.or(x, Bool.and(String.eq(t, "\n"), Bool.not(String.ends_with(bd, "\r")))) == True{} : Bool}) ->
  {Bool.or(x, Bool.and(String.eq(t, "\n"), True{})) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      S.and_intro(String.eq(t, "\n"), True{}, P.and_true_l(String.eq(t, "\n"), Bool.not(String.ends_with(bd, "\r")), h), {==})

# The terminator of a good line is LF or CR LF.
law term_ok:
  for +bd: String
  for +t: String
  for +h: {X.goodb(B.Line{bd, t}) == True{} : Bool}
  {Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), True{})) == True{} : Bool}

def term_ok(bd, t, h):
  term_ok.go(bd, t, String.eq(t, "\r\n"), {==},
    P.and_true_r(X.no_c(bd, '\n'), Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), Bool.not(String.ends_with(bd, "\r")))), h))

law al1_good:
  for +bd: String
  for +t: String
  for +h: {X.goodb(B.Line{bd, t}) == True{} : Bool}
  {X.goodb(al1(t)) == True{} : Bool}

def al1_good(bd, t, h):
  term_ok(bd, t, h)

law al2_good:
  for +o: B.Opts
  for +bd: String
  for +t: String
  for +h: {X.goodb(B.Line{bd, t}) == True{} : Bool}
  {X.goodb(al2(o, t)) == True{} : Bool}

def al2_good(o, bd, t, h):
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      +b = "##framebender_normCommand=norm" ++ R.args_text(args)
      +ncr = {args_noc(args, '\r', {==}, {==}) : {X.no_c(b, '\r') == True{} : Bool}}
      %Equal.sym(Bool, C.ecr(b), False{}, C.noc_ecr(b, ncr)) :
        {Bool.and(X.no_c(b, '\n'), Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), Bool.not(_)))) == True{} : Bool}
      S.and_intro(X.no_c(b, '\n'), Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), True{})),
        args_noc(args, '\n', {==}, {==}), term_ok(bd, t, h))

law field0_push:
  for +c: Char
  for +ps: List<&2, String>
  {B.Rec.field(String.split.push(c, ps), 0n) == SCon{c, B.Rec.field(ps, 0n)} : String}

def field0_push(c, ps):
  match ps:
    case Nil{}:
      {==}
    case +h <> +t:
      {==}

law order_lt:
  for +a: String
  for +b: String
  {String.order.go(a, b, LT{}) == LT{} : Cmp}

def order_lt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{U32{x}}, t}:
      {==}
    case SCon{Chr{U32{x}}, t} SNil{}:
      {==}
    case SCon{Chr{U32{x}}, t1} SCon{Chr{U32{y}}, t2}:
      {==}

# A line starting with "##" is no #CHROM line.
law isc_hash2:
  for +x: String
  for +t: String
  {isc(B.Line{SCon{'#', SCon{'#', x}}, t}) == False{} : Bool}

def isc_hash2(x, t):
  +p1 = String.split.push('#', String.split(x, '\t'))
  %Equal.sym(String, B.Rec.field(String.split.push('#', p1), 0n), SCon{'#', B.Rec.field(p1, 0n)}, field0_push('#', p1)) :
    {String.eq(_, "#CHROM") == False{} : Bool}
  %Equal.sym(String, B.Rec.field(p1, 0n), SCon{'#', B.Rec.field(String.split(x, '\t'), 0n)}, field0_push('#', String.split(x, '\t'))) :
    {String.eq(SCon{'#', _}, "#CHROM") == False{} : Bool}
  %Equal.sym(Cmp, String.order.go(B.Rec.field(String.split(x, '\t'), 0n), "HROM", LT{}), LT{}, order_lt(B.Rec.field(String.split(x, '\t'), 0n), "HROM")) :
    {Cmp.is_eq(_) == False{} : Bool}
  {==}

law isc_al1:
  for +t: String
  {isc(al1(t)) == False{} : Bool}

def isc_al1(t):
  isc_hash2("framebender_normVersion=" ++ R.version(), t)

law isc_al2:
  for +o: B.Opts
  for +t: String
  {isc(al2(o, t)) == False{} : Bool}

def isc_al2(o, t):
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      isc_hash2("framebender_normCommand=norm" ++ R.args_text(args), t)

law hl_good:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  for +hg: {X.all_good(ls) == True{} : Bool}
  for +hc: {has_c(ls) == True{} : Bool}
  {X.all_good(Hl(ls, o)) == True{} : Bool}

def hl_good.cl(cl: B.Line, +o: B.Opts, +h: {X.goodb(cl) == True{} : Bool}) ->
  {X.all_good([al1(B.Line.term(cl)), al2(o, B.Line.term(cl)), cl]) == True{} : Bool}:
  match cl:
    case B.Line{+bd, +t}:
      S.and_intro(X.goodb(al1(t)), X.all_good([al2(o, t), B.Line{bd, t}]), al1_good(bd, t, h),
        S.and_intro(X.goodb(al2(o, t)), X.all_good([B.Line{bd, t}]), al2_good(o, bd, t, h), S.and_intro(X.goodb(B.Line{bd, t}), True{}, h, {==})))

def hl_good(ls, o, hg, hc):
  +ps = pre_c(ls)
  +cl = cl_c(ls)
  +rs = post_c(ls)
  +hg2 = {(%hs_split(ls, hc) : {X.all_good(_) == True{} : Bool}; hg) : {X.all_good(X.lapp(ps, cl <> rs)) == True{} : Bool}}
  +hcl = P.and_true_l(X.goodb(cl), X.all_good(rs), all_good_r(ps, cl <> rs, hg2))
  all_good_app(ps, [al1(B.Line.term(cl)), al2(o, B.Line.term(cl)), cl], all_good_l(ps, cl <> rs, hg2), hl_good.cl(cl, o, hcl))
