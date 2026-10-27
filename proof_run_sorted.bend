import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T

# The law `sorted`: a run that succeeds writes the header, then the items
# grouped by CHROM run and sorted within each run (L.gsort).

# A doomed run
# ============

# The exit code of the rest of the run.
def DM(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, o, st))) == 1n : Nat}

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

def doomed.key(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +c: Maybe<&2, String>,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +w: Nat, +it: R.Item, b: Bool, +d: {S.any_below(buf, S.lkey(last)) == True{} : Bool},
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {S.any_below(buf2, S.lkey(last2)) == True{} : Bool} -> DM(fa, o, t, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  DM(fa, o, t, R.keyed.go(b, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      T.SR(st2 => DM(fa, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
        o3 => bad => prev => ef => T.halted_code(t, fa, o, n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => ef => ih(l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), out ++ o2, doomed.next(w, it, buf, last, o2, l2, S.below_keep(it, buf, S.lkey(last), d), ef)))
    case False{}:
      T.NR(st2 => DM(fa, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, R.Item.chrom(it), it,
        o3 => bad => prev => ef => T.halted_code(t, fa, o, n, True{}, h, c, e, last, buf, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        o2 => l2 => ef => eh => T.halted_code(t, fa, o, n, True{}, h, c, e, last, buf, k, out ++ o2,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
        o2 => l2 => ef => eh => Empty.absurd(DM(fa, o, t, R.same_run(R.RunSt{n, True{}, h, Some{R.Item.chrom(it)}, R.push_cur(c, e), None{}, Nil{}, k, out ++ o2, ns, False{}}, w, it)),
          doomed.nobreak(buf, last, o2, l2, d, ef)))

def doomed.fin(+buf: List<&2, R.Item>, +last: Maybe<&2, R.Item>, +out: String, +ns: List<&2, B.Note>, +k: R.Cnt,
  f: R.Flush, ef: {R.flush(buf, last) == f : R.Flush}, d: {S.any_below(buf, S.lkey(last)) == True{} : Bool}) ->
  {R.Report.code(R.finish.flush(f, out, ns, k)) == 1n : Nat}:
  match f:
    case R.Broke{o2, bad, prev}:
      {==}
    case R.Flushed{o2, l2}:
      Empty.absurd({R.Report.code(R.finish.flush(R.Flushed{o2, l2}, out, ns, k)) == 1n : Nat}, doomed.nobreak(buf, last, o2, l2, d, ef))

# A run with an item below the last key in its buffer ends with exit code 1.
law doomed:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
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
  DM(fa, o, ls, R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}})

def doomed(ls, fa, o, n, h, c, e, last, buf, k, out, ns, d):
  match ls:
    case Nil{}:
      doomed.fin(buf, last, out, ns, k, R.flush(buf, last), {==}, d)
    case +l <> +t:
      +st1 = {R.RunSt{1n+n, True{}, h, c, e, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      T.BL(st2 => DM(fa, o, t, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        cd => u => T.halted_code(t, fa, o, 1n+n, True{}, h, c, e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => doomed.key(fa, o, t, 1n+n, h, c, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          L.item_of(L.judge(fa, B.Line.body(l)), l, at, B.Rec.pos(fs)), R.is_cur(c, R.Item.chrom(L.item_of(L.judge(fa, B.Line.body(l)), l, at, B.Rec.pos(fs)))), d,
          last2 => buf2 => out2 => d2 => doomed(t, fa, o, 1n+n, h, c, e, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), d2)))

# The sorted run
# ==============

def cur_of(gr: List<&2, R.Item>) -> Maybe<&2, String>:
  match gr:
    case Nil{}:
      None{}
    case x <> t:
      Some{R.Item.chrom(x)}

# The output of the rest of a run that succeeds.
def SM(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>, +hd: String, +target: List<&2, R.Item>, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, o, st))) == 0n : Nat} ->
  {R.Report.out(R.finish(L.run.go(ls, fa, o, st))) == hd ++ L.texts(target) : String}

law code_10:
  for -x: Nat
  for h0: {x == 0n : Nat}
  for h1: {x == 1n : Nat}
  Empty

def code_10(x, h0, h1):
  P.succ_ne_zero(0n, Equal.trans(Nat, 1n, x, 0n, Equal.sym(Nat, x, 1n, h1), h0))

def halted_sm(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +target: List<&2, R.Item>,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>) ->
  SM(fa, o, t, hd, target, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  hc => Empty.absurd({R.Report.out(R.finish(L.run.go(t, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))) == hd ++ L.texts(target) : String},
    code_10(R.Report.code(R.finish(L.run.go(t, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), hc,
      T.halted_code(t, fa, o, n, i, h, c, e, l, b, k, out, ns)))

def doomed_sm(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +target: List<&2, R.Item>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +d: {S.any_below(b, S.lkey(l)) == True{} : Bool}) ->
  SM(fa, o, t, hd, target, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}):
  hc => Empty.absurd({R.Report.out(R.finish(L.run.go(t, fa, o, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}))) == hd ++ L.texts(target) : String},
    code_10(R.Report.code(R.finish(L.run.go(t, fa, o, R.RunSt{n, True{}, h, c, e, l, b, k, out, ns, False{}}))), hc,
      doomed(t, fa, o, n, h, c, e, l, b, k, out, ns, d)))

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

def IHS(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +e: List<&2, String>, +k: R.Cnt, +ns: List<&2, B.Note>, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>) -> Type:
  @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String -> @W2: List<&2, R.Item> ->
  {L.isort(gr) == S.app(W2, buf2) : List<&2, R.Item>} ->
  {out2 == hd ++ (L.texts(gd) ++ L.texts(W2)) : String} ->
  {S.all_le(W2, S.lkey(last2)) == True{} : Bool} ->
  {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
  SM(fa, o, t, hd, L.gsort.go(rest, gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last2, buf2, k, out2, ns, False{}})

# One more item in the current run, not below the last key written.
def sorted.step(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hle: {Nat.is_le(S.lkey(last), R.Item.key(it)) == True{} : Bool},
  +o2: String, +l2: Maybe<&2, R.Item>,
  +ef: {R.flush(R.take_ready(w, R.Item.inpos(it), R.insert(it, buf)), last) == R.Flushed{o2, l2} : R.Flush},
  ih: IHS(fa, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
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

def sorted.same.go(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +c: Bool, +ec: {Nat.is_le(S.lkey(last), R.Item.key(it)) == c : Bool},
  ih: IHS(fa, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
    R.same_run(R.RunSt{n, True{}, h, cur_of(S.app(gr, [it])), e, last, buf, k, out, ns, False{}}, w, it)):
  match c:
    case True{}:
      +target = L.gsort.go(rest, S.app(gr, [it]), gd)
      +cur = cur_of(S.app(gr, [it]))
      T.SR(st2 => SM(fa, o, t, hd, target, st2), n, True{}, h, cur, e, last, buf, k, out, ns, False{}, w, it,
        +o3 => +bad => +prev => ef => halted_sm(fa, o, t, hd, target, n, True{}, h, cur, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => +ef => sorted.step(fa, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, gr, gd, W, i1, i2, i3, i4, ec, o2, l2, ef, ih))
    case False{}:
      +target = L.gsort.go(rest, S.app(gr, [it]), gd)
      +cur = cur_of(S.app(gr, [it]))
      T.SR(st2 => SM(fa, o, t, hd, target, st2), n, True{}, h, cur, e, last, buf, k, out, ns, False{}, w, it,
        +o3 => +bad => +prev => ef => halted_sm(fa, o, t, hd, target, n, True{}, h, cur, e, last, Nil{}, k, out ++ o3,
          List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}])),
        +o2 => +l2 => +ef => doomed_sm(fa, o, t, hd, target, n, h, cur, e, l2, R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf)), k, out ++ o2, ns,
          doomed.next(w, it, buf, last, o2, l2, S.below_insert(it, buf, S.lkey(last), Q.le_flip_s(S.lkey(last), R.Item.key(it), ec)), ef)))

# A line in the current run.
def sorted.same(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ih: IHS(fa, o, t, hd, rest, n, h, e, k, ns, S.app(gr, [it]), gd)) ->
  SM(fa, o, t, hd, L.gsort.go(rest, S.app(gr, [it]), gd),
    R.same_run(R.RunSt{n, True{}, h, cur_of(S.app(gr, [it])), e, last, buf, k, out, ns, False{}}, w, it)):
  sorted.same.go(fa, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, gr, gd, W, i1, i2, i3, i4,
    Nat.is_le(S.lkey(last), R.Item.key(it)), {==}, ih)

# A line that starts a new run (the current run, gr, is written out).
def sorted.newrun(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ih: IHS(fa, o, t, hd, rest, n, h, R.push_cur(c, e), k, ns, S.app(Nil{}, [it]), S.app(gd, L.isort(gr)))) ->
  SM(fa, o, t, hd, L.gsort.go(rest, [it], S.app(gd, L.isort(gr))),
    R.new_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  +target = L.gsort.go(rest, [it], S.app(gd, L.isort(gr)))
  +fl = S.flush_sorted(buf, last, i4)
  T.NR(st2 => SM(fa, o, t, hd, target, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, R.Item.chrom(it), it,
    +o3 => +bad => +prev => ef => Empty.absurd(SM(fa, o, t, hd, target, R.RunSt{n, True{}, h, c, e, last, buf, k, out ++ o3,
        List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
      S.broke_ne_flushed(o3, bad, prev, L.texts(buf), S.flast(buf, last),
        Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)},
          Equal.sym(R.Flush, R.flush(buf, last), R.Broke{o3, bad, prev}, ef), fl))),
    +o2 => +l2 => ef => eh => halted_sm(fa, o, t, hd, target, n, True{}, h, c, e, last, buf, k, out ++ o2,
      List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(it)}, None{}}])),
    +o2 => +l2 => +ef => eh =>
      +eo2 = {Equal.sym(String, o2, L.texts(buf), S.flushed_text(buf, last, o2, l2, i4, ef)) : {L.texts(buf) == o2 : String}}
      +j2 = {(%eo2 : {out ++ _ == hd ++ (L.texts(S.app(gd, L.isort(gr))) ++ L.texts(Nil{})) : String};
        %Equal.sym(String, L.texts(S.app(gd, L.isort(gr))) ++ "", L.texts(S.app(gd, L.isort(gr))), Q.s_append_nil(L.texts(S.app(gd, L.isort(gr))))) : {out ++ L.texts(buf) == hd ++ _ : String};
        out_flush(out, hd, gd, W, buf, gr, i1, i2)) :
        {out ++ o2 == hd ++ (L.texts(S.app(gd, L.isort(gr))) ++ L.texts(Nil{})) : String}}
      sorted.same(fa, o, t, hd, rest, n, h, R.push_cur(c, e), None{}, Nil{}, k, out ++ o2, ns, w, it, Nil{}, S.app(gd, L.isort(gr)), Nil{},
        {==}, j2, {==}, {==}, ih))

def IHG(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @e2: List<&2, String> -> @gr2: List<&2, R.Item> -> @gd2: List<&2, R.Item> -> IHS(fa, o, t, hd, rest, n, h, e2, k, ns, gr2, gd2)

def sorted.key2(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, +g0: R.Item, +gs: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(g0 <> gs) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  b: Bool, ihg: IHG(fa, o, t, hd, rest, n, h, k, ns)) ->
  SM(fa, o, t, hd, L.gsort.go(rest, Bool.pick(List<&2, R.Item>, b, S.app(g0 <> gs, [it]), [it]),
      Bool.pick(List<&2, R.Item>, b, gd, S.app(gd, L.isort(g0 <> gs)))),
    R.keyed.go(b, R.RunSt{n, True{}, h, Some{R.Item.chrom(g0)}, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match b:
    case True{}:
      sorted.same(fa, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, g0 <> gs, gd, W, i1, i2, i3, i4,
        ihg(e, S.app(g0 <> gs, [it]), gd))
    case False{}:
      sorted.newrun(fa, o, t, hd, rest, n, h, Some{R.Item.chrom(g0)}, e, last, buf, k, out, ns, w, it, g0 <> gs, gd, W, i1, i2, i4,
        ihg(R.push_cur(Some{R.Item.chrom(g0)}, e), S.app(Nil{}, [it]), S.app(gd, L.isort(g0 <> gs))))

# A line that goes on (keyed), by the current run.
def sorted.key(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +hd: String, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +w: Nat, +it: R.Item, gr: List<&2, R.Item>, +gd: List<&2, R.Item>, +W: List<&2, R.Item>,
  +i1: {L.isort(gr) == S.app(W, buf) : List<&2, R.Item>},
  +i2: {out == hd ++ (L.texts(gd) ++ L.texts(W)) : String},
  +i3: {S.all_le(W, S.lkey(last)) == True{} : Bool},
  +i4: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  ihg: IHG(fa, o, t, hd, rest, n, h, k, ns)) ->
  SM(fa, o, t, hd, L.gsort.go(it <> rest, gr, gd),
    R.keyed.go(R.is_cur(cur_of(gr), R.Item.chrom(it)), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it)):
  match gr:
    case Nil{}:
      %P.append_nil(R.Item, gd) : SM(fa, o, t, hd, L.gsort.go(rest, [it], _),
        R.new_run(R.RunSt{n, True{}, h, None{}, e, last, buf, k, out, ns, False{}}, w, R.Item.chrom(it), it))
      sorted.newrun(fa, o, t, hd, rest, n, h, None{}, e, last, buf, k, out, ns, w, it, Nil{}, gd, W, i1, i2, i4,
        ihg(e, S.app(Nil{}, [it]), S.app(gd, L.isort(Nil{}))))
    case +g0 <> +gs:
      sorted.key2(fa, o, t, hd, rest, n, h, e, last, buf, k, out, ns, w, it, g0, gs, gd, W, i1, i2, i3, i4,
        String.eq(R.Item.chrom(g0), R.Item.chrom(it)), ihg)

def sorted.fin(+out: String, +ns: List<&2, B.Note>, +tb: String, +fl: Maybe<&2, R.Item>, k: R.Cnt) ->
  {R.Report.out(R.finish.flush(R.Flushed{tb, fl}, out, ns, k)) == out ++ tb : String}:
  match k:
    case R.Cnt{a, b, c, d}:
      {==}

# The body of a run that succeeds, from a state where the current run gr is
# W written and buf waiting.
law sorted_body:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
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
  SM(fa, o, ls, hd, L.gsort.go(T.nitems(ls, fa, n), gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}})

def sorted_body(ls, fa, o, n, h, e, last, buf, k, out, ns, hd, gr, gd, W, i1, i2, i3, i4):
  match ls:
    case Nil{}:
      hc =>
        %Equal.sym(R.Flush, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)}, S.flush_sorted(buf, last, i4)) :
          {R.Report.out(R.finish.flush(_, out, ns, k)) == hd ++ L.texts(S.app(gd, L.isort(gr))) : String}
        Equal.trans(String, R.Report.out(R.finish.flush(R.Flushed{L.texts(buf), S.flast(buf, last)}, out, ns, k)), out ++ L.texts(buf),
          hd ++ L.texts(S.app(gd, L.isort(gr))), sorted.fin(out, ns, L.texts(buf), S.flast(buf, last), k),
          out_flush(out, hd, gd, W, buf, gr, i1, i2))
    case +l <> +t:
      +st1 = {R.RunSt{1n+n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +r = L.judge(fa, B.Line.body(l))
      +it = L.item(fa, l, 1n+n)
      +rest = T.nitems(t, fa, 1n+n)
      +target = L.gsort.go(it <> rest, gr, gd)
      %Equal.sym(List<&2, R.Item>, T.nitems(l <> t, fa, n), it <> rest, T.nitems_cons(l, t, fa, n)) :
        SM(fa, o, l <> t, hd, L.gsort.go(_, gr, gd), R.RunSt{n, True{}, h, cur_of(gr), e, last, buf, k, out, ns, False{}})
      T.BL(st2 => SM(fa, o, t, hd, target, st2), r, st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => u => halted_sm(fa, o, t, hd, target, 1n+n, True{}, h, cur_of(gr), e, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}])),
        +nts => +k2 => u => sorted.key(fa, o, t, hd, rest, 1n+n, h, e, last, buf, k2, out, List.append(&2, B.Note, ns, nts), R.Opts.w(o),
          it, gr, gd, W, i1, i2, i3, i4,
          e2 => gr2 => gd2 => last2 => buf2 => out2 => W2 => j1 => j2 => j3 => j4 =>
            sorted_body(t, fa, o, 1n+n, h, e2, last2, buf2, k2, out2, List.append(&2, B.Note, ns, nts), hd, gr2, gd2, W2, j1, j2, j3, j4)))

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

def SH(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>, +n: Nat, +h: String, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, o, st))) == 0n : Nat} ->
  {R.Report.out(R.finish(L.run.go(ls, fa, o, st))) ==
    L.head.go(ls, o, False{}, h) ++ L.texts(L.gsort(L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}})))) : String}

def sorted_head.go(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, b: Bool, +l: B.Line,
  ih: @h2: String -> SH(fa, o, t, 1n+n, h2, R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  {R.Report.code(R.finish(L.run.go(t, fa, o, R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)))) == 0n : Nat} ->
  {R.Report.out(R.finish(L.run.go(t, fa, o, R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)))) ==
    L.head.go(t, o, b, Bool.pick(String, b, h ++ R.added(o, B.Line.term(l)) ++ B.Line.text(l), h ++ B.Line.text(l))) ++
      L.texts(L.gsort(L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}})))) : String}:
  match b:
    case False{}:
      ih(h ++ B.Line.text(l))
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          +hd = h ++ R.added(o, term) ++ bd ++ term
          +st = {R.RunSt{1n+n, True{}, "", None{}, Nil{}, None{}, Nil{}, k, hd, ns, False{}} : R.RunSt}
          +X = R.Report.out(R.finish(L.run.go(t, fa, o, st)))
          +tx = L.texts(L.gsort(T.nitems(t, fa, 1n+n)))
          hc =>
            %Equal.sym(String, L.head.go(t, o, True{}, hd), hd, head_done(t, o, hd)) : {X == _ ++ tx : String}
            sorted_body(t, fa, o, 1n+n, "", Nil{}, None{}, Nil{}, k, hd, ns, hd, Nil{}, Nil{}, Nil{}, {==},
              Equal.sym(String, hd ++ "", hd, Q.s_append_nil(hd)), {==}, {==}, hc)

# The header of a run that succeeds, then its body.
law sorted_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  SH(fa, o, ls, n, h, R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def sorted_head(ls, fa, o, n, h, k, out, ns):
  match ls:
    case Nil{}:
      hc => Empty.absurd({"" == h ++ L.texts(L.gsort(Nil{})) : String}, code_10(1n, hc, {==}))
    case +l <> +t:
      sorted_head.go(fa, o, t, n, h, k, out, ns, R.is_chrom_line(B.Line.body(l)), l,
        h2 => sorted_head(t, fa, o, 1n+n, h2, k, out, ns))
