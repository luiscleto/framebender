import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S

# One body line of L.run, case by case (eliminators over a motive on the next
# state), and the facts every run law needs: a stopped run stays stopped, the
# items of the body lines, judge never answers UNSORTED.

# judge never answers UNSORTED
# ============================

def code_ok(c: B.Code) -> Bool:
  match c:
    case B.Unsorted{}:
      False{}
    case _:
      True{}

def mcode_ok(m: Maybe<&2, B.Code>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      code_ok(c)

def res_ok(r: B.Res) -> Bool:
  match r:
    case B.Res{B.Problem{c}, k, t, s}:
      code_ok(c)
    case _:
      True{}

def first_ok(+b: Bool, +c: B.Code, +rest: Maybe<&2, B.Code>, hc: {code_ok(c) == True{} : Bool},
  hr: {mcode_ok(rest) == True{} : Bool}) -> {mcode_ok(L.first(b, c, rest)) == True{} : Bool}:
  match b:
    case True{}:
      hc
    case False{}:
      hr

law checks_ok:
  for +end_ok: Bool
  for +seq: List<&2, B.Base>
  for +v: B.Var
  {mcode_ok(L.checks(end_ok, seq, v)) == True{} : Bool}

def checks_ok(end_ok, seq, v):
  match v:
    case B.Var{+pos, +ref, +alts}:
      first_ok(Bool.not(end_ok), B.BadEnd{}, L.first(Nat.is_eq(pos, 0n), B.BadPos{}, L.first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}))), {==},
      first_ok(Nat.is_eq(pos, 0n), B.BadPos{}, L.first(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{})), {==},
      first_ok(Bool.not(B.Alleles.distinct(ref <> alts)), B.AltDup{}, L.first(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}), {==},
      first_ok(Bool.not(B.Bases.eq(L.slice(seq, Nat.sub(pos, 1n), L.len(ref)), ref)), B.RefMismatch{}, None{}, {==}, {==}))))

def problem_ok(m: Maybe<&2, B.Code>, +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>, +v: B.Var,
  hm: {mcode_ok(m) == True{} : Bool}) -> {res_ok(L.problem(m, fs, body, seq, v)) == True{} : Bool}:
  match m:
    case Some{k}:
      hm
    case None{}:
      {==}

def pick_ok(+b: Bool) -> {code_ok(Bool.pick(B.Code, b, B.NonAcgtn{}, B.BadEnd{})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bases_ok(+end_ok: Bool, r: Maybe<&2, List<&2, B.Base>>, a: Maybe<&2, List<&2, List<&2, B.Base>>>,
  +fs: List<&2, String>, +body: String, +seq: List<&2, B.Base>) ->
  {res_ok(L.judge.bases(end_ok, r, a, fs, body, seq)) == True{} : Bool}:
  match r a:
    case Some{+ref} Some{+alts}:
      problem_ok(L.checks(end_ok, seq, B.Var{B.Rec.pos(fs), ref, alts}), fs, body, seq, B.Var{B.Rec.pos(fs), ref, alts},
        checks_ok(end_ok, seq, B.Var{B.Rec.pos(fs), ref, alts}))
    case None{} _:
      pick_ok(end_ok)
    case Some{ref} None{}:
      pick_ok(end_ok)

def contig_ok(m: Maybe<&2, String>, +fs: List<&2, String>, +body: String) ->
  {res_ok(L.judge.contig(m, fs, body)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+raw}:
      +ref = B.Rec.field(fs, 3n)
      bases_ok(B.Info.end_ok(B.Rec.field(fs, 7n), Nat.sub(Nat.add(B.Rec.pos(fs), String.length(ref)), 1n)),
        B.Allele.read(ref), B.Alleles.read(B.Rec.alts(fs)), fs, body, B.Bases.of_fasta(raw))

def shape_ok(bad: Bool, skip: Bool, +fa: List<&2, B.Contig>, +fs: List<&2, String>, +body: String) ->
  {res_ok(L.judge.shape(bad, skip, fa, fs, body)) == True{} : Bool}:
  match bad skip:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      contig_ok(B.Fasta.find(fa, B.Rec.field(fs, 0n)), fs, body)

# No line is judged UNSORTED.
law judge_ok:
  for +fa: List<&2, B.Contig>
  for +body: String
  {res_ok(L.judge(fa, body)) == True{} : Bool}

def judge_ok(fa, body):
  +fs = B.Rec.fields(body)
  shape_ok(B.Rec.malformed(fs), B.Rec.out_of_scope(fs), fa, fs, body)

law stop_ok:
  for +c: B.Code
  for -a: Maybe<&2, B.At>
  for -p: Maybe<&2, B.At>
  for h: {code_ok(c) == True{} : Bool}
  {L.is_unsorted(B.Stop{c, a, p}) == False{} : Bool}

def stop_ok(c, a, p, h):
  match c:
    case B.Unsorted{}:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(h))
    case B.Malformed{}:
      {==}
    case B.UnknownChrom{}:
      {==}
    case B.BadEnd{}:
      {==}
    case B.NonAcgtn{}:
      {==}
    case B.BadPos{}:
      {==}
    case B.AltDup{}:
      {==}
    case B.RefMismatch{}:
      {==}
    case B.NoHeader{}:
      {==}
    case B.Stale{}:
      {==}
    case B.UndefinedTag{tag}:
      {==}
    case B.BadCount{}:
      {==}
    case B.BadGt{}:
      {==}
    case B.DupAlts{}:
      {==}
    case B.BadCr{}:
      {==}

def stale_ok(+s: Bool, +at: B.At) -> {L.any_unsorted(R.stale_note(s, at)) == False{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      {==}

# body_line
# =========

# A body line either stops the run (not with UNSORTED) or goes on as its item.
def BL(-M: R.RunSt -> Type, r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  hr: {res_ok(r) == True{} : Bool},
  hstop: @cd: B.Code -> {L.is_unsorted(B.Stop{cd, Some{at}, None{}}) == False{} : Bool} -> M(R.stop(st, "", B.Stop{cd, Some{at}, None{}})),
  hkey: @nts: List<&2, B.Note> -> @k2: R.Cnt -> {L.any_unsorted(nts) == False{} : Bool} ->
    M(R.keyed(st, R.Opts.w(o), L.item_of(r, l, at, inpos), nts, k2))) ->
  M(R.body_line(r, st, o, l, at, inpos)):
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      hstop(B.Malformed{}, {==})
    case B.Res{B.NoContig{}, k, t, s}:
      hstop(B.UnknownChrom{}, {==})
    case B.Res{B.Problem{+c}, k, t, s}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              hstop(c, stop_ok(c, Some{at}, None{}, hr))
            case False{}:
              hkey([B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}), {==})
    case B.Res{B.Skipped{}, k, t, s}:
      hkey(Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}), {==})
    case B.Res{B.Normalized{}, +k, +t, +s}:
      match l:
        case B.Line{+bd, +term}:
          hkey(R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, bd)), False{}, False{}), stale_ok(s, at))

# same_run and new_run
# ====================

def SR.go(-M: R.RunSt -> Type, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat,
  +key: Nat, +inpos: Nat, +at: B.At, +text: String, f: R.Flush,
  ef: {R.flush(R.take_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), l) == f : R.Flush},
  hbroke: @o3: String -> @bad: B.At -> @prev: Maybe<&2, B.At> ->
    {R.flush(R.take_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), l) == R.Broke{o3, bad, prev} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l, Nil{}, k, o ++ o3, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
  hflush: @o2: String -> @l2: Maybe<&2, R.Item> ->
    {R.flush(R.take_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), l) == R.Flushed{o2, l2} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l2, R.drop_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), k, o ++ o2, ns, x})) ->
  M(R.emit.ready(f, R.RunSt{n, i, h, c, e, l, Nil{}, k, o, ns, x}, R.drop_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), at)):
  match f:
    case R.Broke{o3, bad, prev}:
      hbroke(o3, bad, prev, ef)
    case R.Flushed{o2, l2}:
      hflush(o2, l2, ef)

# A line in the current CHROM run: the ready items are written, or the run
# stops with UNSORTED.
def SR(-M: R.RunSt -> Type, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat, it: R.Item,
  hbroke: @o3: String -> @bad: B.At -> @prev: Maybe<&2, B.At> ->
    {R.flush(R.take_ready(w, R.Item.inpos(it), R.insert(it, b)), l) == R.Broke{o3, bad, prev} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l, Nil{}, k, o ++ o3, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
  hflush: @o2: String -> @l2: Maybe<&2, R.Item> ->
    {R.flush(R.take_ready(w, R.Item.inpos(it), R.insert(it, b)), l) == R.Flushed{o2, l2} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, b)), k, o ++ o2, ns, x})) ->
  M(R.same_run(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, it)):
  match it:
    case R.Item{+key, +inpos, +at, +text}:
      SR.go(M, n, i, h, c, e, l, b, k, o, ns, x, w, key, inpos, at, text,
        R.flush(R.take_ready(w, inpos, R.insert(R.Item{key, inpos, at, text}, b)), l), {==}, hbroke, hflush)

def NR.go(-M: R.RunSt -> Type, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat,
  +chrom: String, +it: R.Item, f: R.Flush, g: Bool,
  ef: {R.flush(b, l) == f : R.Flush}, eg: {R.has(chrom, e) == g : Bool},
  hbroke: @o3: String -> @bad: B.At -> @prev: Maybe<&2, B.At> -> {R.flush(b, l) == R.Broke{o3, bad, prev} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l, b, k, o ++ o3, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
  hagain: @o2: String -> @l2: Maybe<&2, R.Item> -> {R.flush(b, l) == R.Flushed{o2, l2} : R.Flush} -> {R.has(chrom, e) == True{} : Bool} ->
    M(R.RunSt{n, i, h, c, e, l, b, k, o ++ o2, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}]), True{}}),
  hnew: @o2: String -> @l2: Maybe<&2, R.Item> -> {R.flush(b, l) == R.Flushed{o2, l2} : R.Flush} -> {R.has(chrom, e) == False{} : Bool} ->
    M(R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, x}, w, it))) ->
  M(R.new_run.go(f, g, R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)):
  match f g:
    case R.Broke{o3, bad, prev} _:
      hbroke(o3, bad, prev, ef)
    case R.Flushed{o2, l2} True{}:
      hagain(o2, l2, ef, eg)
    case R.Flushed{o2, l2} False{}:
      hnew(o2, l2, ef, eg)

# A line that starts a CHROM run: the buffer is written, the run stops with
# UNSORTED if the CHROM came back, or the line goes into the new run.
def NR(-M: R.RunSt -> Type, +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +o: String, +ns: List<&2, B.Note>, +x: Bool, +w: Nat,
  +chrom: String, +it: R.Item,
  hbroke: @o3: String -> @bad: B.At -> @prev: Maybe<&2, B.At> -> {R.flush(b, l) == R.Broke{o3, bad, prev} : R.Flush} ->
    M(R.RunSt{n, i, h, c, e, l, b, k, o ++ o3, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
  hagain: @o2: String -> @l2: Maybe<&2, R.Item> -> {R.flush(b, l) == R.Flushed{o2, l2} : R.Flush} -> {R.has(chrom, e) == True{} : Bool} ->
    M(R.RunSt{n, i, h, c, e, l, b, k, o ++ o2, List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}]), True{}}),
  hnew: @o2: String -> @l2: Maybe<&2, R.Item> -> {R.flush(b, l) == R.Flushed{o2, l2} : R.Flush} -> {R.has(chrom, e) == False{} : Bool} ->
    M(R.same_run(R.RunSt{n, i, h, Some{chrom}, R.push_cur(c, e), None{}, Nil{}, k, o ++ o2, ns, x}, w, it))) ->
  M(R.new_run(R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}, w, chrom, it)):
  NR.go(M, n, i, h, c, e, l, b, k, o, ns, x, w, chrom, it, R.flush(b, l), R.has(chrom, e), {==}, {==}, hbroke, hagain, hnew)

# A stopped run
# =============

law halted_go:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}) == R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}} : R.RunSt}

def halted_go(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  match ls:
    case Nil{}:
      {==}
    case x <> t:
      halted_go(t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)

# A stopped run ends with exit code 1 and the messages so far.
law halted:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.finish(L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})) == R.Report{out, ns, 1n} : R.Report}

def halted.fin(+n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +l: Maybe<&2, R.Item>, +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  {R.finish(R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}) == R.Report{out, ns, 1n} : R.Report}:
  match i:
    case True{}:
      {==}
    case False{}:
      {==}

def halted(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.RunSt, L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}), R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}},
    halted_go(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {R.finish(_) == R.Report{out, ns, 1n} : R.Report}
  halted.fin(n, i, h, c, e, l, b, k, out, ns)

# The items
# =========

def nitems(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, n: Nat) -> List<&2, R.Item>:
  L.ItSt.acc(L.items.go(ls, fa, L.ItSt{True{}, n, Nil{}}))

law acc_split:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +i: Bool
  for +n: Nat
  for +a: List<&2, R.Item>
  {L.ItSt.acc(L.items.go(ls, fa, L.ItSt{i, n, a})) == S.app(a, L.ItSt.acc(L.items.go(ls, fa, L.ItSt{i, n, Nil{}}))) : List<&2, R.Item>}

def acc_split(ls, fa, i, n, a):
  match ls:
    case Nil{}:
      Equal.sym(List<&2, R.Item>, S.app(a, Nil{}), a, P.append_nil(R.Item, a))
    case +l <> +t:
      match i:
        case False{}:
          acc_split(t, fa, R.is_chrom_line(B.Line.body(l)), 1n+n, a)
        case True{}:
          +x = L.item(fa, l, 1n+n)
          +rest = L.ItSt.acc(L.items.go(t, fa, L.ItSt{True{}, 1n+n, Nil{}}))
          %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.items.go(t, fa, L.ItSt{True{}, 1n+n, S.app(a, [x])})), S.app(S.app(a, [x]), rest),
            acc_split(t, fa, True{}, 1n+n, S.app(a, [x]))) : {_ == S.app(a, L.ItSt.acc(L.items.go(t, fa, L.ItSt{True{}, 1n+n, [x]}))) : List<&2, R.Item>}
          %Equal.sym(List<&2, R.Item>, L.ItSt.acc(L.items.go(t, fa, L.ItSt{True{}, 1n+n, [x]})), S.app([x], rest),
            acc_split(t, fa, True{}, 1n+n, [x])) : {S.app(S.app(a, [x]), rest) == S.app(a, _) : List<&2, R.Item>}
          P.append_assoc(R.Item, a, [x], rest)

law nitems_cons:
  for +l: B.Line
  for +t: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +n: Nat
  {nitems(l <> t, fa, n) == L.item(fa, l, 1n+n) <> nitems(t, fa, 1n+n) : List<&2, R.Item>}

def nitems_cons(l, t, fa, n):
  acc_split(t, fa, True{}, 1n+n, [L.item(fa, l, 1n+n)])

law halted_code:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.Report.code(R.finish(L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == 1n : Nat}

def halted_code(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.Report, R.finish(L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})), R.Report{out, ns, 1n},
    halted(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {R.Report.code(_) == 1n : Nat}
  {==}

law halted_notes:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +i: Bool
  for +h: String
  for +c: Maybe<&2, String>
  for +e: List<&2, String>
  for +l: Maybe<&2, R.Item>
  for +b: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  {R.Report.notes(R.finish(L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == ns : List<&2, B.Note>}

def halted_notes(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns):
  %Equal.sym(R.Report, R.finish(L.run.go(ls, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}})), R.Report{out, ns, 1n},
    halted(ls, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {R.Report.notes(_) == ns : List<&2, B.Note>}
  {==}
