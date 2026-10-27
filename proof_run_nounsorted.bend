import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T

# The law `no_unsorted`: on grouped, ascending input with small moves, every
# flush writes keys in order (the last key written plus w is at most the input
# POS of the line before, and a later line's key is above it), and no CHROM
# comes back, so no UNSORTED message.

# The messages of the rest of the run have no UNSORTED.
def UM(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>, st: R.RunSt) -> Type:
  {L.any_unsorted(R.Report.notes(R.finish(L.run.go(ls, fa, o, st)))) == False{} : Bool}

law or_false_inv_r:
  for +a: Bool
  for +b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_inv_r(a, b, e):
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, P.true_ne_false(e))

law unsorted_app:
  for +ns: List<&2, B.Note>
  for +ms: List<&2, B.Note>
  for +h1: {L.any_unsorted(ns) == False{} : Bool}
  for +h2: {L.any_unsorted(ms) == False{} : Bool}
  {L.any_unsorted(List.append(&2, B.Note, ns, ms)) == False{} : Bool}

def unsorted_app(ns, ms, h1, h2):
  match ns:
    case Nil{}:
      h2
    case +x <> +t:
      S.or_false_intro(L.is_unsorted(x), L.any_unsorted(List.append(&2, B.Note, t, ms)),
        P.or_false_inv(L.is_unsorted(x), L.any_unsorted(t), h1),
        unsorted_app(t, ms, or_false_inv_r(L.is_unsorted(x), L.any_unsorted(t), h1), h2))

law unsorted_one:
  for +x: B.Note
  for +hx: {L.is_unsorted(x) == False{} : Bool}
  {L.any_unsorted([x]) == False{} : Bool}

def unsorted_one(x, hx):
  %Equal.sym(Bool, L.is_unsorted(x), False{}, hx) : {Bool.or(_, False{}) == False{} : Bool}
  {==}

def halted_um(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +hn: {L.any_unsorted(ns) == False{} : Bool}) ->
  UM(fa, o, t, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  %Equal.sym(List<&2, B.Note>, R.Report.notes(R.finish(L.run.go(t, fa, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), ns,
    T.halted_notes(t, fa, o, n, i, h, c, e, l, b, k, out, ns)) : {L.any_unsorted(_) == False{} : Bool}
  hn

# The buffer after inserting an item no lower than the last key, as written
# then waiting.
def sr_sorted(+w: Nat, +it: R.Item, +buf: List<&2, R.Item>, +last: Maybe<&2, R.Item>,
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hk: {Nat.is_le(S.lkey(last), R.Item.key(it)) == True{} : Bool}) ->
  {S.sorted_from(S.app(R.take_ready(w, R.Item.inpos(it), R.insert(it, buf)), R.drop_ready(w, R.Item.inpos(it), R.insert(it, buf))), S.lkey(last)) == True{} : Bool}:
  +ins = R.insert(it, buf)
  +p = R.Item.inpos(it)
  %Equal.sym(List<&2, R.Item>, S.app(R.take_ready(w, p, ins), R.drop_ready(w, p, ins)), ins, S.take_drop(w, p, ins)) :
    {S.sorted_from(_, S.lkey(last)) == True{} : Bool}
  S.insert_sorted(it, buf, S.lkey(last), hb, hk)

# A line in the current run, no lower than the last key: written in order.
def nu.same(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +c: Maybe<&2, String>,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +it: R.Item,
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(it)) == True{} : Bool},
  +hk: {Nat.is_le(S.lkey(last), R.Item.key(it)) == True{} : Bool},
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} -> {S.lbound(last2, R.Opts.w(o), R.Item.inpos(it)) == True{} : Bool} ->
    UM(fa, o, t, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  UM(fa, o, t, R.same_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, R.Opts.w(o), it)):
  +w = R.Opts.w(o)
  +p = R.Item.inpos(it)
  +ins = R.insert(it, buf)
  +tk = R.take_ready(w, p, ins)
  +dr = R.drop_ready(w, p, ins)
  +K = S.lkey(last)
  +sTD = sr_sorted(w, it, buf, last, hb, hk)
  +sT = S.sorted_prefix(tk, dr, K, sTD)
  +fs = S.flush_sorted(tk, last, sT)
  T.SR(st2 => UM(fa, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
    +o3 => +bad => +prev => ef => Empty.absurd(UM(fa, o, t, R.RunSt{n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
        List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
      S.broke_ne_flushed(o3, bad, prev, L.texts(tk), S.flast(tk, last),
        Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(tk, last), R.Flushed{L.texts(tk), S.flast(tk, last)},
          Equal.sym(R.Flush, R.flush(tk, last), R.Broke{o3, bad, prev}, ef), fs))),
    +o2 => +l2 => +ef =>
      +el2 = {Equal.sym(Maybe<&2, R.Item>, l2, S.flast(tk, last), S.flushed_last(tk, last, o2, l2, sT, ef)) : {S.flast(tk, last) == l2 : Maybe<&2, R.Item>}}
      +j4 = {(%el2 : {S.sorted_from(dr, S.lkey(_)) == True{} : Bool}; S.sorted_rest(tk, dr, last, sTD)) : {S.sorted_from(dr, S.lkey(l2)) == True{} : Bool}}
      +jl = {(%el2 : {S.lbound(_, w, p) == True{} : Bool}; S.flast_bound(tk, last, w, p, hl, S.take_ready_ready(w, p, ins))) :
        {S.lbound(l2, w, p) == True{} : Bool}}
      ih(l2, dr, out ++ o2, j4, jl))

def IHN(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @a2: R.Item -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {R.Item.chrom(a2) == gc2 : String} ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
    {S.lbound(last2, R.Opts.w(o), R.Item.inpos(a2)) == True{} : Bool} ->
    {L.grouped.go(rest, gc2, ge2) == True{} : Bool} ->
    {L.ascending.go(rest, a2) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), rest) == True{} : Bool} ->
    UM(fa, o, t, R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k, out2, ns, False{}})

def nu.key(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +a: R.Item, +z: R.Item,
  +ea: {R.Item.chrom(a) == gc : String},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool},
  +hg: {L.grouped.go(z <> rest, gc, ge) == True{} : Bool},
  +ha: {L.ascending.go(z <> rest, a) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), z <> rest) == True{} : Bool},
  b: Bool, +eb: {String.eq(gc, R.Item.chrom(z)) == b : Bool}, ih: IHN(fa, o, t, rest, n, h, k, ns)) ->
  UM(fa, o, t, R.keyed.go(b, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, R.Opts.w(o), R.Item.chrom(z), z)):
  match b:
    case True{}:
      +w = R.Opts.w(o)
      +cz = R.Item.chrom(z)
      +pa = R.Item.inpos(a)
      +pz = R.Item.inpos(z)
      +es = Equal.trans(Bool, String.eq(cz, gc), String.eq(gc, cz), True{}, Q.str_eq_sym(gc, cz), eb)
      +egc = Equal.sym(String, gc, cz, Q.str_eq_sound(gc, cz, eb))
      +hz = P.and_true_l(Nat.is_lt(pz, Nat.add(R.Item.key(z), w)), L.small_moves(w, rest), hm)
      +hmr = P.and_true_r(Nat.is_lt(pz, Nat.add(R.Item.key(z), w)), L.small_moves(w, rest), hm)
      +h1 = P.and_true_l(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(pa, pz)), L.ascending.go(rest, z), ha)
      +har = P.and_true_r(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(pa, pz)), L.ascending.go(rest, z), ha)
      +h2 = {(%ea : {Bool.or(Bool.not(String.eq(_, cz)), Nat.is_le(pa, pz)) == True{} : Bool}; h1) :
        {Bool.or(Bool.not(String.eq(gc, cz)), Nat.is_le(pa, pz)) == True{} : Bool}}
      +haz = {(%eb : {Bool.or(Bool.not(_), Nat.is_le(pa, pz)) == True{} : Bool}; h2) : {Nat.is_le(pa, pz) == True{} : Bool}}
      +hg1 = {(%es : {Bool.and(Bool.or(_, Bool.not(R.has(cz, gc <> ge))), L.grouped.go(rest, cz, Bool.pick(List<&2, String>, _, ge, gc <> ge))) == True{} : Bool}; hg) :
        {L.grouped.go(rest, cz, ge) == True{} : Bool}}
      +hg2 = {(%egc : {L.grouped.go(rest, _, ge) == True{} : Bool}; hg1) : {L.grouped.go(rest, gc, ge) == True{} : Bool}}
      nu.same(fa, o, t, n, h, Some{gc}, ge, last, buf, k, out, ns, z, hb, S.lbound_mono(last, w, pa, pz, hl, haz),
        S.key_ok(last, w, pa, pz, R.Item.key(z), hl, haz, hz),
        last2 => buf2 => out2 => j4 => jl => ih(gc, ge, z, last2, buf2, out2, egc, j4, jl, hg2, har, hmr))
    case False{}:
      +w = R.Opts.w(o)
      +cz = R.Item.chrom(z)
      +es = Equal.trans(Bool, String.eq(cz, gc), String.eq(gc, cz), False{}, Q.str_eq_sym(gc, cz), eb)
      +hz = P.and_true_l(Nat.is_lt(R.Item.inpos(z), Nat.add(R.Item.key(z), w)), L.small_moves(w, rest), hm)
      +hmr = P.and_true_r(Nat.is_lt(R.Item.inpos(z), Nat.add(R.Item.key(z), w)), L.small_moves(w, rest), hm)
      +har = P.and_true_r(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(R.Item.inpos(a), R.Item.inpos(z))), L.ascending.go(rest, z), ha)
      +hg1 = {(%es : {Bool.and(Bool.or(_, Bool.not(Bool.or(_, R.has(cz, ge)))), L.grouped.go(rest, cz, Bool.pick(List<&2, String>, _, ge, gc <> ge))) == True{} : Bool}; hg) :
        {Bool.and(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge)) == True{} : Bool}}
      +hh = P.not_true(R.has(cz, ge), P.and_true_l(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge), hg1))
      +hg2 = P.and_true_r(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge), hg1)
      +fs = S.flush_sorted(buf, last, hb)
      T.NR(st2 => UM(fa, o, t, st2), n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}, w, cz, z,
        +o3 => +bad => +prev => ef => Empty.absurd(UM(fa, o, t, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o3,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
          S.broke_ne_flushed(o3, bad, prev, L.texts(buf), S.flast(buf, last),
            Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)},
              Equal.sym(R.Flush, R.flush(buf, last), R.Broke{o3, bad, prev}, ef), fs))),
        +o2 => +l2 => ef => eh => Empty.absurd(UM(fa, o, t, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o2,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(z)}, None{}}]), True{}}),
          P.true_ne_false(Equal.trans(Bool, True{}, R.has(cz, ge), False{}, Equal.sym(Bool, R.has(cz, ge), True{}, eh), hh))),
        +o2 => +l2 => ef => eh =>
          nu.same(fa, o, t, n, h, Some{cz}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, z, {==}, {==}, P.le_zero_l(R.Item.key(z)),
            last2 => buf2 => out2 => j4 => jl => ih(cz, gc <> ge, z, last2, buf2, out2, {==}, j4, jl, hg2, har, hmr)))

def nu.fin(+out: String, +ns: List<&2, B.Note>, +tb: String, +fl: Maybe<&2, R.Item>, k: R.Cnt,
  +hn: {L.any_unsorted(ns) == False{} : Bool}) ->
  {L.any_unsorted(R.Report.notes(R.finish.flush(R.Flushed{tb, fl}, out, ns, k))) == False{} : Bool}:
  match k:
    case R.Cnt{+a, +b, +c, +d}:
      unsorted_app(ns, [B.Summary{a, b, c, d}], hn, {==})

# Within the body, with a current CHROM run whose last line was a.
law nu_run:
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
  for +a: R.Item
  for +ea: {R.Item.chrom(a) == gc : String}
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool}
  for +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool}
  for +hg: {L.grouped.go(T.nitems(ls, fa, n), gc, ge) == True{} : Bool}
  for +ha: {L.ascending.go(T.nitems(ls, fa, n), a) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), T.nitems(ls, fa, n)) == True{} : Bool}
  UM(fa, o, ls, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})

def nu_run(ls, fa, o, n, h, gc, ge, last, buf, k, out, ns, a, ea, hn, hb, hl, hg, ha, hm):
  match ls:
    case Nil{}:
      %Equal.sym(R.Flush, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)}, S.flush_sorted(buf, last, hb)) :
        {L.any_unsorted(R.Report.notes(R.finish.flush(_, out, ns, k))) == False{} : Bool}
      nu.fin(out, ns, L.texts(buf), S.flast(buf, last), k, hn)
    case +l <> +t:
      +w = R.Opts.w(o)
      +st1 = {R.RunSt{1n+n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, 1n+n)
      +rest = T.nitems(t, fa, 1n+n)
      +ec = T.nitems_cons(l, t, fa, n)
      +hg2 = {(%ec : {L.grouped.go(_, gc, ge) == True{} : Bool}; hg) : {L.grouped.go(it <> rest, gc, ge) == True{} : Bool}}
      +ha2 = {(%ec : {L.ascending.go(_, a) == True{} : Bool}; ha) : {L.ascending.go(it <> rest, a) == True{} : Bool}}
      +hm2 = {(%ec : {L.small_moves(w, _) == True{} : Bool}; hm) : {L.small_moves(w, it <> rest) == True{} : Bool}}
      T.BL(st2 => UM(fa, o, t, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => +hx => halted_um(fa, o, t, 1n+n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.key(fa, o, t, rest, 1n+n, h, gc, ge, last, buf, k2, out, ns2, a, it, ea, hb, hl, hg2, ha2, hm2,
            String.eq(gc, R.Item.chrom(it)), {==},
            gc2 => ge2 => a2 => last2 => buf2 => out2 => j1 => j2 => j3 => j4 => j5 => j6 =>
              nu_run(t, fa, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, j1, hn2, j2, j3, j4, j5, j6)))

# The first body line.
law nu_first:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hg: {L.grouped(T.nitems(ls, fa, n)) == True{} : Bool}
  for +ha: {L.ascending(T.nitems(ls, fa, n)) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), T.nitems(ls, fa, n)) == True{} : Bool}
  UM(fa, o, ls, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def nu_first(ls, fa, o, n, h, k, out, ns, hn, hg, ha, hm):
  match ls:
    case Nil{}:
      nu.fin(out, ns, "", None{}, k, hn)
    case +l <> +t:
      +w = R.Opts.w(o)
      +st1 = {R.RunSt{1n+n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{1n+n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, 1n+n)
      +cz = R.Item.chrom(it)
      +rest = T.nitems(t, fa, 1n+n)
      +ec = T.nitems_cons(l, t, fa, n)
      +hg2 = {(%ec : {L.grouped(_) == True{} : Bool}; hg) : {L.grouped.go(rest, cz, Nil{}) == True{} : Bool}}
      +ha2 = {(%ec : {L.ascending(_) == True{} : Bool}; ha) : {L.ascending.go(rest, it) == True{} : Bool}}
      +hm2 = {(%ec : {L.small_moves(w, _) == True{} : Bool}; hm) : {L.small_moves(w, it <> rest) == True{} : Bool}}
      +hmr = P.and_true_r(Nat.is_lt(R.Item.inpos(it), Nat.add(R.Item.key(it), w)), L.small_moves(w, rest), hm2)
      T.BL(st2 => UM(fa, o, t, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => +hx => halted_um(fa, o, t, 1n+n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.same(fa, o, t, 1n+n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            last2 => buf2 => out2 => j4 => jl => nu_run(t, fa, o, 1n+n, h, cz, Nil{}, last2, buf2, k2, out2, ns2, it, {==}, hn2, j4, jl, hg2, ha2, hmr)))

def nu_head.go(+fa: List<&2, B.Contig>, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +hn: {L.any_unsorted(ns) == False{} : Bool}, b: Bool, +l: B.Line,
  +hg: {L.grouped(L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  +ha: {L.ascending(L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.items.go(t, fa, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  ih: @h2: String ->
    {L.grouped(L.ItSt.acc(L.items.go(t, fa, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    {L.ascending(L.ItSt.acc(L.items.go(t, fa, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.items.go(t, fa, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    UM(fa, o, t, R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  UM(fa, o, t, R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)):
  match b:
    case False{}:
      ih(h ++ B.Line.text(l), hg, ha, hm)
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          nu_first(t, fa, o, 1n+n, "", k, h ++ R.added(o, term) ++ bd ++ term, ns, hn, hg, ha, hm)

law nu_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hg: {L.grouped(L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  for +ha: {L.ascending(L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.items.go(ls, fa, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  UM(fa, o, ls, R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def nu_head(ls, fa, o, n, h, k, out, ns, hn, hg, ha, hm):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      nu_head.go(fa, o, t, n, h, k, out, ns, hn, R.is_chrom_line(B.Line.body(l)), l, hg, ha, hm,
        h2 => g2 => a2 => m2 => nu_head(t, fa, o, 1n+n, h2, k, out, ns, hn, g2, a2, m2))
