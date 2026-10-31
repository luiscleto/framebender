import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_tail.bend as U
import ./proof_s_same.bend as SSm

# The law `sorted`: a run that succeeds writes the header, then the items
# grouped by CHROM run and sorted within each run (L.gsort).

# A doomed run
# ============

# The exit code of the rest of the run.
def DM(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +ls: U.Tl, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(U.TT(ls, fa, defs, o, st))) == 1n : Nat}

# After a flush that does not break, an item below the last key is still
# waiting.
def doomed.next(+w: Nat, +it: R.Item, +buf: List<&2, R.Item>, +last: Maybe<&2, R.Item>, -o2: String, +l2: Maybe<&2, R.Item>,
  d: {S.any_below(R.insert(it, buf), S.lkey(last)) == True{} : Bool},
  +ef: {R.flush(R.take_ready(w, R.Item.inpos(it), R.insert(it, buf)), last) == R.Flushed{o2, l2} : R.Flush}) ->
  {S.any_below(R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), S.lkey(l2)) == True{} : Bool}:
  +p = R.Item.inpos(it)
  +ins = R.insert(it, buf)
  +tk = R.take_ready(w, p, ins)
  +dr = R.drop_ready(w, p, ins)
  +k = S.lkey(last)
  +s = S.flush_ok_sorted(tk, last, o2, l2, ef)
  +d2 = {(%Equal.sym(List<&2, R.Item>, S.app(tk, dr), ins, S.take_drop(w, p, ins)) : {S.any_below(_, k) == True{} : Bool}; d) : {S.any_below(S.app(tk, dr), k) == True{} : Bool}}
  +d3 = S.below_app_r(tk, dr, k, k, P.le_refl(k), s, d2)
  %Equal.sym(Maybe<&2, R.Item>, l2, S.flast(tk, last), S.flushed_last(tk, last, o2, l2, s, ef)) : {S.any_below(dr, S.lkey(_)) == True{} : Bool}
  S.below_mono(dr, k, S.lkey(S.flast(tk, last)), d3, S.lkey_mono(tk, last, s))

def doomed.nobreak(+buf: List<&2, R.Item>, +last: Maybe<&2, R.Item>, -o2: String, -l2: Maybe<&2, R.Item>,
  d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}, ef: {R.flush(buf, last) == R.Flushed{o2, l2} : R.Flush}) -> Empty:
  +k = S.lkey(last)
  P.true_ne_false(Equal.trans(Bool, True{}, S.any_below(buf, k), False{}, Equal.sym(Bool, S.any_below(buf, k), True{}, d),
    S.sorted_not_below(buf, k, k, P.le_refl(k), S.flush_ok_sorted(buf, last, o2, l2, ef))))

def doomed.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +n: Nat, +h: String, +c: Maybe<&2, String>,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +w: Nat, +it: R.Item, b: Bool, +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool},
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {S.any_below(buf2, S.lkey(last2)) == True{} : Bool} -> DM(fa, defs, o, t, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  DM(fa, defs, o, t, R.keyed.go(b, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      T.SR(st2 => DM(fa, defs, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
        o3 => bad => prev => ef => U.tt_code(t, fa, defs, o, n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => ef => ih(l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), out ++ o2, doomed.next(w, it, buf, last, o2, l2, S.below_keep(it, buf, S.lkey(last), d), ef)))
    case False{}:
      T.NR(st2 => DM(fa, defs, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, R.Item.chrom(it), it,
        o3 => bad => prev => ef => U.tt_code(t, fa, defs, o, n, True{}, h, c, e, last, buf, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        o2 => l2 => ef => eh => U.tt_code(t, fa, defs, o, n, True{}, h, c, e, last, buf, k, out ++ o2,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
        o2 => l2 => ef => eh => Empty.absurd(DM(fa, defs, o, t, R.same_run(R.RunSt{n, True{}, h, Some{R.Item.chrom(it)}, R.push_cur(c, e), None{}, Nil{}, k, out ++ o2, ns, False{}}, w, it)),
          doomed.nobreak(buf, last, o2, l2, d, ef)))

def doomed.fin(+buf: List<&2, R.Item>, +last: Maybe<&2, R.Item>, +out: String, +ns: List<&2, B.Note>, +k: R.Cnt,
  f: R.Flush, ef: {R.flush(buf, last) == f : R.Flush}, d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}) ->
  {R.Report.code(R.finish.flush(f, out, ns, k)) == 1n : Nat}:
  match f:
    case R.Broke{o2, bad, prev}:
      {==}
    case R.Flushed{o2, l2}:
      Empty.absurd({R.Report.code(R.finish.flush(R.Flushed{o2, l2}, out, ns, k)) == 1n : Nat}, doomed.nobreak(buf, last, o2, l2, d, ef))

# After a line's records, in a doomed run: the lines t.
def KD(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>) -> Type:
  @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @k2: R.Cnt -> @out2: String -> @ns2: List<&2, B.Note> ->
    {S.any_below(buf2, S.lkey(last2)) == True{} : Bool} -> DM(fa, defs, o, U.TLs(t), R.RunSt{n, True{}, h, c, e, last2, buf2, k2, out2, ns2, False{}})

# A body line's records (any), in a doomed run.
def doomed_ps(ps: List<&2, String>, +term: String, +at: B.At, +inpos: Nat, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}, kd: KD(fa, defs, o, t, n, h, c, e)) ->
  DM(fa, defs, o, U.Tl{ps, term, at, inpos, t}, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kd(last, buf, k, out, ns, d)
    case Con{+p, +pt}:
      +LN = {B.Line{p, term} : B.Line}
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      T.BL(st2 => DM(fa, defs, o, tl, st2), L.judge(fa, p), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => u => U.tt_code(tl, fa, defs, o, n, True{}, h, c, e, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => doomed.key(fa, defs, o, tl, n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          L.item_of(L.judge(fa, p), LN, at, inpos), R.is_cur(c, R.Item.chrom(L.item_of(L.judge(fa, p), LN, at, inpos))), d,
          last2 => buf2 => out2 => d2 => doomed_ps(pt, term, at, inpos, t, fa, defs, o, n, h, c, e, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), d2, kd)))

# A body line, by what -m does with it, in a doomed run.
def doomed_line(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool},
  +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, kd: KD(fa, defs, o, t, n, h, c, e)) ->
  DM(fa, defs, o, U.TLs(t), L.body_in(pt, fa, o, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, l, B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      T.BL(st2 => DM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        +cd => u => U.tt_code(U.TLs(t), fa, defs, o, n, True{}, h, c, e, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => doomed.key(fa, defs, o, U.TLs(t), n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          L.item(fa, l, n), R.is_cur(c, R.Item.chrom(L.item(fa, l, n))), d,
          last2 => buf2 => out2 => d2 => kd(last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), d2)))
    case B.Pieces{+ps}:
      +fs = B.Rec.fields(B.Line.body(l))
      doomed_ps(ps, B.Line.term(l), B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs), t, fa, defs, o, n, h, c, e, last, buf, k, out, ns, d, kd)
    case B.Unsplit{+cc}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      U.UL(st2 => DM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), cc, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), cc, hpt),
        +cd => u => U.tt_code(U.TLs(t), fa, defs, o, n, True{}, h, c, e, last, buf, k, out ++ "", List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => doomed.key(fa, defs, o, U.TLs(t), n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, R.is_cur(c, R.Item.chrom(it)), d,
          last2 => buf2 => out2 => d2 => kd(last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), d2)))

# A run with an item below the last key in its buffer ends with exit code 1.
law doomed:
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
  for +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}
  DM(fa, defs, o, U.TLs(ls), R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}})

def doomed(ls, fa, defs, o, n, h, c, e, last, buf, k, out, ns, d):
  match ls:
    case Nil{}:
      doomed.fin(buf, last, out, ns, k, R.flush(buf, last), {==}, d)
    case +l <> +t:
      doomed_line(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, c, e, last, buf, k, out, ns, d, {==},
        last2 => buf2 => k2 => out2 => ns2 => d2 => doomed(t, fa, defs, o, 1n+n, h, c, e, last2, buf2, k2, out2, ns2, d2))

# The same, from inside a split line.
def doomed_tl(tl: U.Tl, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>,
  +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}) -> DM(fa, defs, o, tl, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}):
  match tl:
    case U.Tl{+ps, +term, +at, +inpos, +t}:
      doomed_ps(ps, term, at, inpos, t, fa, defs, o, n, h, c, e, last, buf, k, out, ns, d,
        last2 => buf2 => k2 => out2 => ns2 => d2 => doomed(t, fa, defs, o, n, h, c, e, last2, buf2, k2, out2, ns2, d2))

# The sorted run
# ==============

def cur_of(gr: List<&2, R.Item>) -> Maybe<&2, String>:
  match gr:
    case Nil{}:
      None{}
    case x <> t:
      Some{R.Item.chrom(x)}

# The output of the rest of a run that succeeds.
def SM(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +ls: U.Tl, +hd: String, +target: List<&2, R.Item>, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(U.TT(ls, fa, defs, o, st))) == 0n : Nat} ->
  {R.Report.out(R.finish(U.TT(ls, fa, defs, o, st))) == hd ++ L.texts(target) : String}

law code_10:
  for -x: Nat
  for h0: {x == 0n : Nat}
  for h1: {x == 1n : Nat}
  Empty

def code_10(x, h0, h1):
  P.succ_ne_zero(0n, Equal.trans(Nat, 1n, x, 0n, Equal.sym(Nat, x, 1n, h1), h0))

def halted_sm(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +target: List<&2, R.Item>,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  SM(fa, defs, o, t, hd, target, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  hc => Empty.absurd({R.Report.out(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == hd ++ L.texts(target) : String},
    code_10(R.Report.code(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), hc,
      U.tt_code(t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)))

def doomed_sm(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +target: List<&2, R.Item>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +d: {S.any_below(b, S.lkey(l)) == True{} : Bool}) ->
  SM(fa, defs, o, t, hd, target, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}):
  hc => Empty.absurd({R.Report.out(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}))) == hd ++ L.texts(target) : String},
    code_10(R.Report.code(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}))), hc,
      doomed_tl(t, fa, defs, o, n, h, c, e, l, b, k, out, ns, d)))

# Writing more items after W.
law out_more:
  for +out: String
  for +hd: String
  for +gd: List<&2, R.Item>
  for +W: List<&2, R.Item>
  for +xs: List<&2, R.Item>
  for +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String}
  {out ++ L.texts(xs) == hd ++ (L.texts(gd) ++ L.texts(S.app(W, xs))) : String}

def out_more(out, hd, gd, W, xs, i2):
  +tg = L.texts(gd)
  +tw = L.texts(W)
  +tx = L.texts(xs)
  %Equal.sym(String, L.texts(S.app(W, xs)), tw ++ tx, S.texts_app(W, xs)) : {out ++ tx == hd ++ (tg ++ _) : String}
  %Equal.sym(String, out, hd ++ (tg ++ tw), i2) : {_ ++ tx == hd ++ (tg ++ (tw ++ tx)) : String}
  %Equal.sym(String, (hd ++ (tg ++ tw)) ++ tx, hd ++ ((tg ++ tw) ++ tx), Q.s_append_assoc(hd, tg ++ tw, tx)) : {_ == hd ++ (tg ++ (tw ++ tx)) : String}
  %Equal.sym(String, (tg ++ tw) ++ tx, tg ++ (tw ++ tx), Q.s_append_assoc(tg, tw, tx)) : {hd ++ _ == hd ++ (tg ++ (tw ++ tx)) : String}
  {==}

# Writing the whole buffer ends the current run.
law out_flush:
  for +out: String
  for +hd: String
  for +gd: List<&2, R.Item>
  for +W: List<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +gr: List<&2, R.Item>
  for +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>}
  for +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String}
  {out ++ L.texts(buf) == hd ++ L.texts(S.app(gd, L.isort(gr))) : String}

def out_flush(out, hd, gd, W, buf, gr, i1, i2):
  %Equal.sym(String, L.texts(S.app(gd, L.isort(gr))), L.texts(gd) ++ L.texts(L.isort(gr)), S.texts_app(gd, L.isort(gr))) :
    {out ++ L.texts(buf) == hd ++ _ : String}
  %Equal.sym(List<&2, R.Item>, L.isort(gr), S.app(W, buf), i1) : {out ++ L.texts(buf) == hd ++ (L.texts(gd) ++ L.texts(_)) : String}
  out_more(out, hd, gd, W, buf, i2)

def IHS(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +e: List<&2, String>, +k: R.Cnt, +ns: List<&2, B.Note>, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>) -> Type:
  @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String -> @W2: List<&2, R.Item> ->
  {L.isort(gr) == S.app(W2, buf2) : List<&2, R.Item>} ->
  {out2 == hd ++ (L.texts(gd) ++ L.texts(W2)) : String} ->
  {S.all_le(W2, S.lkey(last2)) == True{} : Bool} ->
  {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last2, buf2, k, out2, ns, False{}})

# One more item in the current run, not below the last key written.
def sorted.step(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hle: {Nat.is_le(S.lkey(last), R.Item.key(it)) == True{} : Bool},
  +o2: String, +l2: Maybe<&2, R.Item>,
  +ef: {R.flush(R.take_ready(w, R.Item.inpos(it), R.insert(it, buf)), last) == R.Flushed{o2, l2} : R.Flush},
  ih: IHS(fa, defs, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
    R.RunSt{n, True{}, h, cur_of(S.app(gr, [it])), e, l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), k, out ++ o2, ns, False{}}):
  +K = S.lkey(last)
  +ins = R.insert(it, buf)
  +p = R.Item.inpos(it)
  +tk = R.take_ready(w, p, ins)
  +dr = R.drop_ready(w, p, ins)
  +sI = S.insert_sorted(it, buf, K, i4, hle)
  +sTD = {(%Equal.sym(List<&2, R.Item>, S.app(tk, dr), ins, S.take_drop(w, p, ins)) : {S.sorted_from(_, K) == True{} : Bool}; sI) : {S.sorted_from(S.app(tk, dr), K) == True{} : Bool}}
  +sT = S.sorted_prefix(tk, dr, K, sTD)
  +KF = S.lkey(S.flast(tk, last))
  +el2 = {Equal.sym(Maybe<&2, R.Item>, l2, S.flast(tk, last), S.flushed_last(tk, last, o2, l2, sT, ef)) : {S.flast(tk, last) == l2 : Maybe<&2, R.Item>}}
  +eo2 = {Equal.sym(String, o2, L.texts(tk), S.flushed_text(tk, last, o2, l2, sT, ef)) : {L.texts(tk) == o2 : String}}
  +j4 = {(%el2 : {S.sorted_from(dr, S.lkey(_)) == True{} : Bool}; S.sorted_rest(tk, dr, last, sTD)) : {S.sorted_from(dr, S.lkey(l2)) == True{} : Bool}}
  +j3 = {(%el2 : {S.all_le(S.app(W, tk), S.lkey(_)) == True{} : Bool};
    S.all_le_app(W, tk, KF, S.all_le_mono(W, K, KF, i3, S.lkey_mono(tk, last, sT)), S.all_le_flast(tk, last, sT))) :
    {S.all_le(S.app(W, tk), S.lkey(l2)) == True{} : Bool}}
  +j2 = {(%eo2 : {out ++ _ == hd ++ (L.texts(gd) ++ L.texts(S.app(W, tk))) : String}; out_more(out, hd, gd, W, tk, i2)) :
    {out ++ o2 == hd ++ (L.texts(gd) ++ L.texts(S.app(W, tk))) : String}}
  +hw = S.all_le_mono(W, K, R.Item.key(it), i3, hle)
  +j1 = {(%Equal.sym(List<&2, R.Item>, L.isort(S.app(gr, [it])), R.insert(it, L.isort(gr)), S.isort_snoc(gr, it)) :
      {_ == S.app(S.app(W, tk), dr) : List<&2, R.Item>};
    %Equal.sym(List<&2, R.Item>, L.isort(gr), S.app(W, buf), i1) : {R.insert(it, _) == S.app(S.app(W, tk), dr) : List<&2, R.Item>};
    %Equal.sym(List<&2, R.Item>, R.insert(it, S.app(W, buf)), S.app(W, ins), S.insert_app(it, W, buf, hw)) :
      {_ == S.app(S.app(W, tk), dr) : List<&2, R.Item>};
    %Equal.sym(List<&2, R.Item>, S.app(S.app(W, tk), dr), S.app(W, S.app(tk, dr)), P.append_assoc(R.Item, W, tk, dr)) :
      {S.app(W, ins) == _ : List<&2, R.Item>};
    %Equal.sym(List<&2, R.Item>, S.app(tk, dr), ins, S.take_drop(w, p, ins)) : {S.app(W, ins) == S.app(W, _) : List<&2, R.Item>};
    {==}) : {L.isort(S.app(gr, [it])) == S.app(S.app(W, tk), dr) : List<&2, R.Item>}}
  ih(l2, dr, out ++ o2, S.app(W, tk), j1, j2, j3, j4)

def sorted.same.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +c: Bool, +ec: {Nat.is_le(S.lkey(last), R.Item.key(it)) == c : Bool},
  ih: IHS(fa, defs, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
    R.same_run(R.RunSt{n, True{}, h, cur_of(S.app(gr, [it])), e, last, buf, k, out, ns, False{}}, w, it)):
  match c:
    case True{}:
      +target = L.gsort.go(rest, S.app(gr, [it]), gd)
      +cur = cur_of(S.app(gr, [it]))
      T.SR(st2 => SM(fa, defs, o, t, hd, target, st2), n, True{}, h, cur, e, last, buf, k, out, ns, False{}, w, it,
        +o3 => +bad => +prev => ef => halted_sm(fa, defs, o, t, hd, target, n, True{}, h, cur, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => +ef => sorted.step(fa, defs, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, gr, gd, W, i1, i2, i3, i4, ec, o2, l2, ef, ih))
    case False{}:
      +target = L.gsort.go(rest, S.app(gr, [it]), gd)
      +cur = cur_of(S.app(gr, [it]))
      T.SR(st2 => SM(fa, defs, o, t, hd, target, st2), n, True{}, h, cur, e, last, buf, k, out, ns, False{}, w, it,
        +o3 => +bad => +prev => ef => halted_sm(fa, defs, o, t, hd, target, n, True{}, h, cur, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => +ef => doomed_sm(fa, defs, o, t, hd, target, n, h, cur, e, l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), k, out ++ o2, ns,
          doomed.next(w, it, buf, last, o2, l2, S.below_insert(it, buf, S.lkey(last), Q.le_flip_s(S.lkey(last), R.Item.key(it), ec)), ef)))

# A line in the current run.
def sorted.same(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ih: IHS(fa, defs, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
    R.same_run(R.RunSt{n, True{}, h, cur_of(S.app(gr, [it])), e, last, buf, k, out, ns, False{}}, w, it)):
  sorted.same.go(fa, defs, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, gr, gd, W, i1, i2, i3, i4,
    Nat.is_le(S.lkey(last), R.Item.key(it)), {==}, ih)

# A line that starts a new run (the current run, gr, is written out).
def sorted.newrun(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ih: IHS(fa, defs, o, t, hd, rest, n, h, R.push_cur(c, e), k, ns, S.app(Nil{}, [it]), S.app(gd, L.isort(gr)))) ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, [it], S.app(gd, L.isort(gr))),
    R.new_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  +target = L.gsort.go(rest, [it], S.app(gd, L.isort(gr)))
  +fl = S.flush_sorted(buf, last, i4)
  T.NR(st2 => SM(fa, defs, o, t, hd, target, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, R.Item.chrom(it), it,
    +o3 => +bad => +prev => ef => Empty.absurd(SM(fa, defs, o, t, hd, target, R.RunSt{n, True{}, h, c, e, last, buf, k, out ++ o3,
        List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
      S.broke_ne_flushed(o3, bad, prev, L.texts(buf), S.flast(buf, last),
        Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)},
          Equal.sym(R.Flush, R.flush(buf, last), R.Broke{o3, bad, prev}, ef), fl))),
    +o2 => +l2 => ef => eh => halted_sm(fa, defs, o, t, hd, target, n, True{}, h, c, e, last, buf, k, out ++ o2,
      List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
    +o2 => +l2 => +ef => eh =>
      +eo2 = {Equal.sym(String, o2, L.texts(buf), S.flushed_text(buf, last, o2, l2, i4, ef)) : {L.texts(buf) == o2 : String}}
      +j2 = {(%eo2 : {out ++ _ == hd ++ (L.texts(S.app(gd, L.isort(gr))) ++ L.texts(Nil{})) : String};
        %Equal.sym(String, L.texts(S.app(gd, L.isort(gr))) ++ "", L.texts(S.app(gd, L.isort(gr))), Q.s_append_nil(L.texts(S.app(gd, L.isort(gr))))) : {out ++ L.texts(buf) == hd ++ _ : String};
        out_flush(out, hd, gd, W, buf, gr, i1, i2)) :
        {out ++ o2 == hd ++ (L.texts(S.app(gd, L.isort(gr))) ++ L.texts(Nil{})) : String}}
      sorted.same(fa, defs, o, t, hd, rest, n, h, R.push_cur(c, e), None{}, Nil{}, k, out ++ o2, ns, w, it, Nil{}, S.app(gd, L.isort(gr)), Nil{},
        {==}, j2, {==}, {==}, ih))

def IHG(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @e2: List<&2, String> -> @gr2: List<&2, R.Item> -> @gd2: List<&2, R.Item> -> IHS(fa, defs, o, t, hd, rest, n, h, e2, k, ns, gr2, gd2)

def sorted.key2(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +g0: R.Item, +gs: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(g0 <> gs) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  b: Bool, ihg: IHG(fa, defs, o, t, hd, rest, n, h, k, ns)) ->
  SM(fa, defs, o, t, hd, L.gsort.go(rest, Bool.pick(List<&2, R.Item>, b, S.app(g0 <> gs, [it]), [it]),
      Bool.pick(List<&2, R.Item>, b, gd, S.app(gd, L.isort(g0 <> gs)))),
    R.keyed.go(b, R.RunSt{n, True{}, h, Some{R.Item.chrom(g0)}, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      sorted.same(fa, defs, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, g0 <> gs, gd, W, i1, i2, i3, i4,
        ihg(e, S.app(g0 <> gs, [it]), gd))
    case False{}:
      sorted.newrun(fa, defs, o, t, hd, rest, n, h, Some{R.Item.chrom(g0)}, e, last, buf, k, out, ns, w, it, g0 <> gs, gd, W, i1, i2, i4,
        ihg(R.push_cur(Some{R.Item.chrom(g0)}, e), S.app(Nil{}, [it]), S.app(gd, L.isort(g0 <> gs))))

# A line that goes on (keyed), by the current run.
def sorted.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ihg: IHG(fa, defs, o, t, hd, rest, n, h, k, ns)) ->
  SM(fa, defs, o, t, hd, L.gsort.go(it <> rest, gr, gd),
    R.keyed.go(R.is_cur(cur_of(gr), R.Item.chrom(it)), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match gr:
    case Nil{}:
      %P.append_nil(R.Item, gd) : SM(fa, defs, o, t, hd, L.gsort.go(rest, [it], _),
        R.new_run(R.RunSt{n, True{}, h, None{}, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it))
      sorted.newrun(fa, defs, o, t, hd, rest, n, h, None{}, e, last, buf, k, out, ns, w, it, Nil{}, gd, W, i1, i2, i4,
        ihg(e, S.app(Nil{}, [it]), S.app(gd, L.isort(Nil{}))))
    case +g0 <> +gs:
      sorted.key2(fa, defs, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, g0, gs, gd, W, i1, i2, i3, i4,
        String.eq(R.Item.chrom(g0), R.Item.chrom(it)), ihg)

def sorted.fin(+out: String, +ns: List<&2, B.Note>, +tb: String, +fl: Maybe<&2, R.Item>, k: R.Cnt) ->
  {R.Report.out(R.finish.flush(R.Flushed{tb, fl}, out, ns, k)) == out ++ tb : String}:
  match k:
    case R.Cnt{a, b, c, d}:
      {==}

# After a line's records: the lines t.
def KS(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @e2: List<&2, String> -> @gr2: List<&2, R.Item> -> @gd2: List<&2, R.Item> -> @k2: R.Cnt -> @ns2: List<&2, B.Note> ->
  @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String -> @W2: List<&2, R.Item> ->
  {L.isort(gr2) == S.app(W2, buf2) : List<&2, R.Item>} ->
  {out2 == hd ++ (L.texts(gd2) ++ L.texts(W2)) : String} ->
  {S.all_le(W2, S.lkey(last2)) == True{} : Bool} ->
  {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
  SM(fa, defs, o, U.TLs(t), hd, L.gsort.go(rest, gr2, gd2), R.RunSt{n, True{}, h, cur_of(gr2), e2, last2, buf2, k2, out2, ns2, False{}})

# A split line's records, in a run that succeeds.
def sorted_ps(ps: List<&2, String>, +fs: List<&2, String>, +term: String, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +hd: String, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +rest: List<&2, R.Item>, +hs: {L.all_same_site(fs, ps) == True{} : Bool}, ks: KS(fa, defs, o, t, hd, rest, n, h)) ->
  SM(fa, defs, o, U.Tl{ps, term, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs), t}, hd, L.gsort.go(S.app(L.items.pieces(ps, fa, term, n), rest), gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      ks(e, gr, gd, k, ns, last, buf, out, W, i1, i2, i3, i4)
    case Con{+p, +pt}:
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +LN = {B.Line{p, term} : B.Line}
      +it = L.item_of(L.judge(fa, p), LN, at, inpos)
      +rest2 = S.app(L.items.pieces(pt, fa, term, n), rest)
      +hs1 = P.and_true_l(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +hs2 = P.and_true_r(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      +target = L.gsort.go(it <> rest2, gr, gd)
      %Equal.sym(R.Item, L.item(fa, LN, n), it, U.item_site(fs, p, term, n, fa, hs1)) :
        SM(fa, defs, o, U.Tl{Con{p, pt}, term, at, inpos, t}, hd, L.gsort.go(_ <> rest2, gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}})
      T.BL(st2 => SM(fa, defs, o, tl, hd, target, st2), L.judge(fa, p), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => u => halted_sm(fa, defs, o, tl, hd, target, n, True{}, h, cur_of(gr), e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => sorted.key(fa, defs, o, tl, hd, rest2, n, h, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, gr, gd, W, i1, i2, i3, i4,
          e2 => gr2 => gd2 => last2 => buf2 => out2 => W2 => j1 => j2 => j3 => j4 =>
            sorted_ps(pt, fs, term, t, fa, defs, o, n, h, e2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), hd, gr2, gd2, W2, j1, j2, j3, j4, rest, hs2, ks)))

# A body line, by what -m does with it, in a run that succeeds.
def sorted_line(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +hd: String, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +rest: List<&2, R.Item>, +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, ks: KS(fa, defs, o, t, hd, rest, n, h)) ->
  SM(fa, defs, o, U.TLs(t), hd, L.gsort.go(S.app(L.items.line(pt, fa, l, n), rest), gr, gd),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, l, B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +it = L.item(fa, l, n)
      +target = L.gsort.go(it <> rest, gr, gd)
      T.BL(st2 => SM(fa, defs, o, U.TLs(t), hd, target, st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_sm(fa, defs, o, U.TLs(t), hd, target, n, True{}, h, cur_of(gr), e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => sorted.key(fa, defs, o, U.TLs(t), hd, rest, n, h, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, gr, gd, W, i1, i2, i3, i4,
          e2 => gr2 => gd2 => last2 => buf2 => out2 => W2 => j1 => j2 => j3 => j4 =>
            ks(e2, gr2, gd2, k2, List.append(&2, B.Note, ns, nts), last2, buf2, out2, W2, j1, j2, j3, j4)))
    case B.Pieces{+ps}:
      sorted_ps(ps, B.Rec.fields(B.Line.body(l)), B.Line.term(l), t, fa, defs, o, n, h, e, last, buf, k, out, ns, hd, gr, gd, W, i1, i2, i3, i4, rest,
        SSm.split_site(defs, o, B.Line.body(l), ps, hpt), ks)
    case B.Unsplit{+cc}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      +target = L.gsort.go(it <> rest, gr, gd)
      U.UL(st2 => SM(fa, defs, o, U.TLs(t), hd, target, st2), L.judge(fa, B.Line.body(l)), cc, R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), cc, hpt),
        +cd => u => halted_sm(fa, defs, o, U.TLs(t), hd, target, n, True{}, h, cur_of(gr), e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => sorted.key(fa, defs, o, U.TLs(t), hd, rest, n, h, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, gr, gd, W, i1, i2, i3, i4,
          e2 => gr2 => gd2 => last2 => buf2 => out2 => W2 => j1 => j2 => j3 => j4 =>
            ks(e2, gr2, gd2, k2, List.append(&2, B.Note, ns, nts), last2, buf2, out2, W2, j1, j2, j3, j4)))

# The body of a run that succeeds, from a state where the current run gr is
# W written and buf waiting.
law sorted_body:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +e: List<&2, String>
  for +last: Maybe<&2, R.Item>
  for +buf: List<&2, R.Item>
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hd: String
  for +gr: List<&2, R.Item>
  for +gd: List<&2, R.Item>
  for +W: List<&2, R.Item>
  for +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>}
  for +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String}
  for +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool}
  for +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool}
  SM(fa, defs, o, U.TLs(ls), hd, L.gsort.go(U.mitems(ls, fa, defs, o, n), gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}})

def sorted_body(ls, fa, defs, o, n, h, e, last, buf, k, out, ns, hd, gr, gd, W, i1, i2, i3, i4):
  match ls:
    case Nil{}:
      hc =>
        %Equal.sym(R.Flush, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)}, S.flush_sorted(buf, last, i4)) :
          {R.Report.out(R.finish.flush(_, out, ns, k)) == hd ++ L.texts(S.app(gd, L.isort(gr))) : String}
        Equal.trans(String, R.Report.out(R.finish.flush(R.Flushed{L.texts(buf), S.flast(buf, last)}, out, ns, k)), out ++ L.texts(buf),
          hd ++ L.texts(S.app(gd, L.isort(gr))), sorted.fin(out, ns, L.texts(buf), S.flast(buf, last), k),
          out_flush(out, hd, gd, W, buf, gr, i1, i2))
    case +l <> +t:
      +rest = U.mitems(t, fa, defs, o, 1n+n)
      %Equal.sym(List<&2, R.Item>, U.mitems(l <> t, fa, defs, o, n), S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), rest), U.mitems_cons(l, t, fa, defs, o, n)) :
        SM(fa, defs, o, U.TLs(l <> t), hd, L.gsort.go(_, gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}})
      sorted_line(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, e, last, buf, k, out, ns, hd, gr, gd, W, i1, i2, i3, i4, rest, {==},
        e2 => gr2 => gd2 => k2 => ns2 => last2 => buf2 => out2 => W2 => j1 => j2 => j3 => j4 =>
          sorted_body(t, fa, defs, o, 1n+n, h, e2, last2, buf2, k2, out2, ns2, hd, gr2, gd2, W2, j1, j2, j3, j4))


# The header
# ==========

law head_done:
  for +ls: List<&2, B.Line>
  for +o: B.Opts
  for +acc: String
  {L.head.go(ls, o, True{}, acc) == acc : String}

def head_done(ls, o, acc):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      head_done(t, o, acc)

def SH(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +ls: List<&2, B.Line>, +n: Nat, +h: String, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, defs, o, st))) == 0n : Nat} ->
  {R.Report.out(R.finish(L.run.go(ls, fa, defs, o, st))) ==
    L.head.go(ls, o, False{}, h) ++ L.texts(L.gsort(L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}})))) : String}

def sorted_head.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, b: Bool, +l: B.Line,
  ih: @h2: String -> SH(fa, defs, o, t, 1n+n, h2, R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  {R.Report.code(R.finish(L.run.go(t, fa, defs, o, R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)))) == 0n : Nat} ->
  {R.Report.out(R.finish(L.run.go(t, fa, defs, o, R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)))) ==
    L.head.go(t, o, b, Bool.pick(String, b, h ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l), h ++ B.Line.text(l))) ++
      L.texts(L.gsort(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}})))) : String}:
  match b:
    case False{}:
      ih(h ++ B.Line.text(l))
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          +hd = h ++ R.added(o, term) ++ bd ++ term
          +st = {R.RunSt{1n+n, True{}, "", None{}, Nil{}, None{}, Nil{}, k, hd, ns, False{}} : R.RunSt}
          +X = R.Report.out(R.finish(L.run.go(t, fa, defs, o, st)))
          +tx = L.texts(L.gsort(U.mitems(t, fa, defs, o, 1n+n)))
          hc =>
            %Equal.sym(String, L.head.go(t, o, True{}, hd), hd, head_done(t, o, hd)) : {X == _ ++ tx : String}
            sorted_body(t, fa, defs, o, 1n+n, "", Nil{}, None{}, Nil{}, k, hd, ns, hd, Nil{}, Nil{}, Nil{}, {==},
              Equal.sym(String, hd ++ "", hd, Q.s_append_nil(hd)), {==}, {==}, hc)

# The header of a run that succeeds, then its body.
law sorted_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  SH(fa, defs, o, ls, n, h, R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def sorted_head(ls, fa, defs, o, n, h, k, out, ns):
  match ls:
    case Nil{}:
      hc => Empty.absurd({"" == h ++ L.texts(L.gsort(Nil{})) : String}, code_10(1n, hc, {==}))
    case +l <> +t:
      sorted_head.go(fa, defs, o, t, n, h, k, out, ns, R.is_chrom_line(B.Line.body(l)), l,
        h2 => sorted_head(t, fa, defs, o, 1n+n, h2, k, out, ns))
