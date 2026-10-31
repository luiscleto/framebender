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

# The law `no_unsorted`: on grouped, ascending input with small moves, every
# flush writes keys in order (the last key written plus w is at most the input
# POS of the line before, and a later line's key is above it), and no CHROM
# comes back, so no UNSORTED message.

# The messages of the rest of the run have no UNSORTED.
def UM(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +ls: U.Tl, st: R.RunSt) -> Type:
  {L.any_unsorted(R.Report.notes(R.finish(U.TT(ls, fa, defs, o, st)))) == False{} : Bool}

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

def halted_um(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl,
  +n: Nat, +i: Bool, +h: String, +c: Maybe<&2, String>, +e: List<&2, String>, +l: Maybe<&2, R.Item>,
  +b: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +hn: {L.any_unsorted(ns) == False{} : Bool}) ->
  UM(fa, defs, o, t, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}):
  %Equal.sym(List<&2, B.Note>, R.Report.notes(R.finish(U.TT(t, fa, defs, o, R.RunSt{n, i, h, c, e, l, b, k, out, ns, True{}}))), ns,
    U.tt_notes(t, fa, defs, o, n, i, h, c, e, l, b, k, out, ns)) : {L.any_unsorted(_) == False{} : Bool}
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
def nu.same(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +n: Nat, +h: String, +c: Maybe<&2, String>,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +it: R.Item,
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(it)) == True{} : Bool},
  +hk: {Nat.is_le(S.lkey(last), R.Item.key(it)) == True{} : Bool},
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} -> {S.lbound(last2, R.Opts.w(o), R.Item.inpos(it)) == True{} : Bool} ->
    UM(fa, defs, o, t, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  UM(fa, defs, o, t, R.same_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, R.Opts.w(o), it)):
  +w = R.Opts.w(o)
  +p = R.Item.inpos(it)
  +ins = R.insert(it, buf)
  +tk = R.take_ready(w, p, ins)
  +dr = R.drop_ready(w, p, ins)
  +K = S.lkey(last)
  +sTD = sr_sorted(w, it, buf, last, hb, hk)
  +sT = S.sorted_prefix(tk, dr, K, sTD)
  +fs = S.flush_sorted(tk, last, sT)
  T.SR(st2 => UM(fa, defs, o, t, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, it,
    +o3 => +bad => +prev => ef => Empty.absurd(UM(fa, defs, o, t, R.RunSt{n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
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

def IHN(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @a2: R.Item -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {R.Item.chrom(a2) == gc2 : String} ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
    {S.lbound(last2, R.Opts.w(o), R.Item.inpos(a2)) == True{} : Bool} ->
    {L.grouped.go(rest, gc2, ge2) == True{} : Bool} ->
    {L.ascending.go(rest, a2) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), rest) == True{} : Bool} ->
    UM(fa, defs, o, t, R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k, out2, ns, False{}})

def nu.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: U.Tl, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +a: R.Item, +z: R.Item,
  +ea: {R.Item.chrom(a) == gc : String},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool},
  +hg: {L.grouped.go(z <> rest, gc, ge) == True{} : Bool},
  +ha: {L.ascending.go(z <> rest, a) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), z <> rest) == True{} : Bool},
  b: Bool, +eb: {String.eq(gc, R.Item.chrom(z)) == b : Bool}, ih: IHN(fa, defs, o, t, rest, n, h, k, ns)) ->
  UM(fa, defs, o, t, R.keyed.go(b, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, R.Opts.w(o), R.Item.chrom(z), z)):
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
      nu.same(fa, defs, o, t, n, h, Some{gc}, ge, last, buf, k, out, ns, z, hb, S.lbound_mono(last, w, pa, pz, hl, haz),
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
      T.NR(st2 => UM(fa, defs, o, t, st2), n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}, w, cz, z,
        +o3 => +bad => +prev => ef => Empty.absurd(UM(fa, defs, o, t, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o3,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
          S.broke_ne_flushed(o3, bad, prev, L.texts(buf), S.flast(buf, last),
            Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)},
              Equal.sym(R.Flush, R.flush(buf, last), R.Broke{o3, bad, prev}, ef), fs))),
        +o2 => +l2 => ef => eh => Empty.absurd(UM(fa, defs, o, t, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o2,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(z)}, None{}}]), True{}}),
          P.true_ne_false(Equal.trans(Bool, True{}, R.has(cz, ge), False{}, Equal.sym(Bool, R.has(cz, ge), True{}, eh), hh))),
        +o2 => +l2 => ef => eh =>
          nu.same(fa, defs, o, t, n, h, Some{cz}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, z, {==}, {==}, P.le_zero_l(R.Item.key(z)),
            last2 => buf2 => out2 => j4 => jl => ih(cz, gc <> ge, z, last2, buf2, out2, {==}, j4, jl, hg2, har, hmr)))

def nu.fin(+out: String, +ns: List<&2, B.Note>, +tb: String, +fl: Maybe<&2, R.Item>, k: R.Cnt,
  +hn: {L.any_unsorted(ns) == False{} : Bool}) ->
  {L.any_unsorted(R.Report.notes(R.finish.flush(R.Flushed{tb, fl}, out, ns, k))) == False{} : Bool}:
  match k:
    case R.Cnt{+a, +b, +c, +d}:
      unsorted_app(ns, [B.Summary{a, b, c, d}], hn, {==})

# After a line's records, within a CHROM run whose last item was a2: the
# lines t.
def KN(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @a2: R.Item -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @k2: R.Cnt -> @out2: String -> @ns2: List<&2, B.Note> ->
    {R.Item.chrom(a2) == gc2 : String} ->
    {L.any_unsorted(ns2) == False{} : Bool} ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
    {S.lbound(last2, R.Opts.w(o), R.Item.inpos(a2)) == True{} : Bool} ->
    {L.grouped.go(rest, gc2, ge2) == True{} : Bool} ->
    {L.ascending.go(rest, a2) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), rest) == True{} : Bool} ->
    UM(fa, defs, o, U.TLs(t), R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k2, out2, ns2, False{}})

# After a line with no record, before the first CHROM run: the lines t.
def KNF(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @k2: R.Cnt -> @out2: String -> @ns2: List<&2, B.Note> ->
    {L.any_unsorted(ns2) == False{} : Bool} ->
    {L.grouped(rest) == True{} : Bool} ->
    {L.ascending(rest) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), rest) == True{} : Bool} ->
    UM(fa, defs, o, U.TLs(t), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k2, out2, ns2, False{}})

# A split line's records, within a CHROM run whose last item was a.
def nu_ps(ps: List<&2, String>, +fs: List<&2, String>, +term: String, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +a: R.Item, +ea: {R.Item.chrom(a) == gc : String},
  +hn: {L.any_unsorted(ns) == False{} : Bool},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool},
  +rest: List<&2, R.Item>,
  +hg: {L.grouped.go(S.app(L.items.pieces(ps, fa, term, n), rest), gc, ge) == True{} : Bool},
  +ha: {L.ascending.go(S.app(L.items.pieces(ps, fa, term, n), rest), a) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), S.app(L.items.pieces(ps, fa, term, n), rest)) == True{} : Bool},
  +hs: {L.all_same_site(fs, ps) == True{} : Bool}, kn: KN(fa, defs, o, t, rest, n, h)) ->
  UM(fa, defs, o, U.Tl{ps, term, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs), t}, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kn(gc, ge, a, last, buf, k, out, ns, ea, hn, hb, hl, hg, ha, hm)
    case Con{+p, +pt}:
      +w = R.Opts.w(o)
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +LN = {B.Line{p, term} : B.Line}
      +it = L.item_of(L.judge(fa, p), LN, at, inpos)
      +rest2 = S.app(L.items.pieces(pt, fa, term, n), rest)
      +hs1 = P.and_true_l(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +hs2 = P.and_true_r(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +ei = U.item_site(fs, p, term, n, fa, hs1)
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      +hg2 = {(%ei : {L.grouped.go(_ <> rest2, gc, ge) == True{} : Bool}; hg) : {L.grouped.go(it <> rest2, gc, ge) == True{} : Bool}}
      +ha2 = {(%ei : {L.ascending.go(_ <> rest2, a) == True{} : Bool}; ha) : {L.ascending.go(it <> rest2, a) == True{} : Bool}}
      +hm2 = {(%ei : {L.small_moves(w, _ <> rest2) == True{} : Bool}; hm) : {L.small_moves(w, it <> rest2) == True{} : Bool}}
      T.BL(st2 => UM(fa, defs, o, tl, st2), L.judge(fa, p), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => +hx => halted_um(fa, defs, o, tl, n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.key(fa, defs, o, tl, rest2, n, h, gc, ge, last, buf, k2, out, ns2, a, it, ea, hb, hl, hg2, ha2, hm2,
            String.eq(gc, R.Item.chrom(it)), {==},
            gc2 => ge2 => a2 => last2 => buf2 => out2 => j1 => j2 => j3 => j4 => j5 => j6 =>
              nu_ps(pt, fs, term, t, fa, defs, o, n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, j1, hn2, j2, j3, rest, j4, j5, j6, hs2, kn)))

# A body line within a CHROM run, by what -m does with it.
def nu_line(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +a: R.Item, +ea: {R.Item.chrom(a) == gc : String},
  +hn: {L.any_unsorted(ns) == False{} : Bool},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool},
  +rest: List<&2, R.Item>,
  +hg: {L.grouped.go(S.app(L.items.line(pt, fa, l, n), rest), gc, ge) == True{} : Bool},
  +ha: {L.ascending.go(S.app(L.items.line(pt, fa, l, n), rest), a) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, kn: KN(fa, defs, o, t, rest, n, h)) ->
  UM(fa, defs, o, U.TLs(t), L.body_in(pt, fa, o, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, l, B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, n)
      T.BL(st2 => UM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => +hx => halted_um(fa, defs, o, U.TLs(t), n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.key(fa, defs, o, U.TLs(t), rest, n, h, gc, ge, last, buf, k2, out, ns2, a, it, ea, hb, hl, hg, ha, hm,
            String.eq(gc, R.Item.chrom(it)), {==},
            gc2 => ge2 => a2 => last2 => buf2 => out2 => j1 => j2 => j3 => j4 => j5 => j6 =>
              kn(gc2, ge2, a2, last2, buf2, k2, out2, ns2, j1, hn2, j2, j3, j4, j5, j6)))
    case B.Pieces{+ps}:
      nu_ps(ps, B.Rec.fields(B.Line.body(l)), B.Line.term(l), t, fa, defs, o, n, h, gc, ge, last, buf, k, out, ns, a, ea, hn, hb, hl, rest, hg, ha, hm,
        SSm.split_site(defs, o, B.Line.body(l), ps, hpt), kn)
    case B.Unsplit{+cc}:
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      U.UL(st2 => UM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), cc, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), cc, hpt),
        +cd => +hx => halted_um(fa, defs, o, U.TLs(t), n, True{}, h, Some{gc}, ge, last, buf, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.key(fa, defs, o, U.TLs(t), rest, n, h, gc, ge, last, buf, k2, out, ns2, a, it, ea, hb, hl, hg, ha, hm,
            String.eq(gc, R.Item.chrom(it)), {==},
            gc2 => ge2 => a2 => last2 => buf2 => out2 => j1 => j2 => j3 => j4 => j5 => j6 =>
              kn(gc2, ge2, a2, last2, buf2, k2, out2, ns2, j1, hn2, j2, j3, j4, j5, j6)))

# Within the body, with a current CHROM run whose last line was a.
law nu_run:
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
  for +a: R.Item
  for +ea: {R.Item.chrom(a) == gc : String}
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool}
  for +hl: {S.lbound(last, R.Opts.w(o), R.Item.inpos(a)) == True{} : Bool}
  for +hg: {L.grouped.go(U.mitems(ls, fa, defs, o, n), gc, ge) == True{} : Bool}
  for +ha: {L.ascending.go(U.mitems(ls, fa, defs, o, n), a) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), U.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  UM(fa, defs, o, U.TLs(ls), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})

def nu_run(ls, fa, defs, o, n, h, gc, ge, last, buf, k, out, ns, a, ea, hn, hb, hl, hg, ha, hm):
  match ls:
    case Nil{}:
      %Equal.sym(R.Flush, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)}, S.flush_sorted(buf, last, hb)) :
        {L.any_unsorted(R.Report.notes(R.finish.flush(_, out, ns, k))) == False{} : Bool}
      nu.fin(out, ns, L.texts(buf), S.flast(buf, last), k, hn)
    case +l <> +t:
      +w = R.Opts.w(o)
      +rest = U.mitems(t, fa, defs, o, 1n+n)
      +xs = S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), rest)
      +ec = U.mitems_cons(l, t, fa, defs, o, n)
      +hg2 = {(%ec : {L.grouped.go(_, gc, ge) == True{} : Bool}; hg) : {L.grouped.go(xs, gc, ge) == True{} : Bool}}
      +ha2 = {(%ec : {L.ascending.go(_, a) == True{} : Bool}; ha) : {L.ascending.go(xs, a) == True{} : Bool}}
      +hm2 = {(%ec : {L.small_moves(w, _) == True{} : Bool}; hm) : {L.small_moves(w, xs) == True{} : Bool}}
      nu_line(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, gc, ge, last, buf, k, out, ns, a, ea, hn, hb, hl, rest, hg2, ha2, hm2, {==},
        gc2 => ge2 => a2 => last2 => buf2 => k2 => out2 => ns2 => j1 => hn2 => j2 => j3 => j4 => j5 => j6 =>
          nu_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, j1, hn2, j2, j3, j4, j5, j6))

# A split line's records, before the first CHROM run.
def nu_fps(ps: List<&2, String>, +fs: List<&2, String>, +term: String, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +hn: {L.any_unsorted(ns) == False{} : Bool},
  +rest: List<&2, R.Item>,
  +hg: {L.grouped(S.app(L.items.pieces(ps, fa, term, n), rest)) == True{} : Bool},
  +ha: {L.ascending(S.app(L.items.pieces(ps, fa, term, n), rest)) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), S.app(L.items.pieces(ps, fa, term, n), rest)) == True{} : Bool},
  +hs: {L.all_same_site(fs, ps) == True{} : Bool}, kf: KNF(fa, defs, o, t, rest, n, h), kn: KN(fa, defs, o, t, rest, n, h)) ->
  UM(fa, defs, o, U.Tl{ps, term, B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Rec.pos(fs), t}, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}):
  match ps:
    case Nil{}:
      kf(k, out, ns, hn, hg, ha, hm)
    case Con{+p, +pt}:
      +w = R.Opts.w(o)
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +LN = {B.Line{p, term} : B.Line}
      +it = L.item_of(L.judge(fa, p), LN, at, inpos)
      +cz = R.Item.chrom(it)
      +rest2 = S.app(L.items.pieces(pt, fa, term, n), rest)
      +hs1 = P.and_true_l(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +hs2 = P.and_true_r(L.same_site(fs, p), L.all_same_site(fs, pt), hs)
      +ei = U.item_site(fs, p, term, n, fa, hs1)
      +tl = {U.Tl{pt, term, at, inpos, t} : U.Tl}
      +hg2 = {(%ei : {L.grouped(_ <> rest2) == True{} : Bool}; hg) : {L.grouped.go(rest2, cz, Nil{}) == True{} : Bool}}
      +ha2 = {(%ei : {L.ascending(_ <> rest2) == True{} : Bool}; ha) : {L.ascending.go(rest2, it) == True{} : Bool}}
      +hm2 = {(%ei : {L.small_moves(w, _ <> rest2) == True{} : Bool}; hm) : {L.small_moves(w, it <> rest2) == True{} : Bool}}
      +hmr = P.and_true_r(Nat.is_lt(R.Item.inpos(it), Nat.add(R.Item.key(it), w)), L.small_moves(w, rest2), hm2)
      T.BL(st2 => UM(fa, defs, o, tl, st2), L.judge(fa, p), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, LN, at, inpos, T.judge_ok(fa, p),
        +cd => +hx => halted_um(fa, defs, o, tl, n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.same(fa, defs, o, tl, n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            last2 => buf2 => out2 => j4 => jl => nu_ps(pt, fs, term, t, fa, defs, o, n, h, cz, Nil{}, last2, buf2, k2, out2, ns2, it, {==}, hn2, j4, jl,
              rest, hg2, ha2, hmr, hs2, kn)))

# A body line before the first CHROM run, by what -m does with it.
def nu_fline(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +hn: {L.any_unsorted(ns) == False{} : Bool},
  +rest: List<&2, R.Item>,
  +hg: {L.grouped(S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +ha: {L.ascending(S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +hpt: {B.Rec.parts(defs, o, B.Line.body(l)) == pt : B.Parts}, kf: KNF(fa, defs, o, t, rest, n, h), kn: KN(fa, defs, o, t, rest, n, h)) ->
  UM(fa, defs, o, U.TLs(t), L.body_in(pt, fa, o, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, l, B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +w = R.Opts.w(o)
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, n)
      +cz = R.Item.chrom(it)
      +hmr = P.and_true_r(Nat.is_lt(R.Item.inpos(it), Nat.add(R.Item.key(it), w)), L.small_moves(w, rest), hm)
      T.BL(st2 => UM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l, at, B.Rec.pos(fs), T.judge_ok(fa, B.Line.body(l)),
        +cd => +hx => halted_um(fa, defs, o, U.TLs(t), n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.same(fa, defs, o, U.TLs(t), n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            last2 => buf2 => out2 => j4 => jl => kn(cz, Nil{}, it, last2, buf2, k2, out2, ns2, {==}, hn2, j4, jl, hg, ha, hmr)))
    case B.Pieces{+ps}:
      nu_fps(ps, B.Rec.fields(B.Line.body(l)), B.Line.term(l), t, fa, defs, o, n, h, k, out, ns, hn, rest, hg, ha, hm,
        SSm.split_site(defs, o, B.Line.body(l), ps, hpt), kf, kn)
    case B.Unsplit{+cc}:
      +w = R.Opts.w(o)
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +inpos = B.Rec.pos(fs)
      +it = {R.Item{inpos, inpos, at, B.Line.text(l)} : R.Item}
      +cz = R.Item.chrom(it)
      +hmr = P.and_true_r(Nat.is_lt(R.Item.inpos(it), Nat.add(R.Item.key(it), w)), L.small_moves(w, rest), hm)
      U.UL(st2 => UM(fa, defs, o, U.TLs(t), st2), L.judge(fa, B.Line.body(l)), cc, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l, at, inpos, T.judge_ok(fa, B.Line.body(l)),
        U.unsplit_ok(defs, o, B.Line.body(l), cc, hpt),
        +cd => +hx => halted_um(fa, defs, o, U.TLs(t), n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out ++ "",
          List.append(&2, B.Note, ns, [B.Stop{cd, Some{at}, None{}}]),
          unsorted_app(ns, [B.Stop{cd, Some{at}, None{}}], hn, unsorted_one(B.Stop{cd, Some{at}, None{}}, hx))),
        +nts => +k2 => +hnts =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          +hn2 = unsorted_app(ns, nts, hn, hnts)
          nu.same(fa, defs, o, U.TLs(t), n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            last2 => buf2 => out2 => j4 => jl => kn(cz, Nil{}, it, last2, buf2, k2, out2, ns2, {==}, hn2, j4, jl, hg, ha, hmr)))

# The first body line.
law nu_first:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hg: {L.grouped(U.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  for +ha: {L.ascending(U.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), U.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  UM(fa, defs, o, U.TLs(ls), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def nu_first(ls, fa, defs, o, n, h, k, out, ns, hn, hg, ha, hm):
  match ls:
    case Nil{}:
      nu.fin(out, ns, "", None{}, k, hn)
    case +l <> +t:
      +w = R.Opts.w(o)
      +rest = U.mitems(t, fa, defs, o, 1n+n)
      +xs = S.app(L.items.line(B.Rec.parts(defs, o, B.Line.body(l)), fa, l, 1n+n), rest)
      +ec = U.mitems_cons(l, t, fa, defs, o, n)
      +hg2 = {(%ec : {L.grouped(_) == True{} : Bool}; hg) : {L.grouped(xs) == True{} : Bool}}
      +ha2 = {(%ec : {L.ascending(_) == True{} : Bool}; ha) : {L.ascending(xs) == True{} : Bool}}
      +hm2 = {(%ec : {L.small_moves(w, _) == True{} : Bool}; hm) : {L.small_moves(w, xs) == True{} : Bool}}
      nu_fline(B.Rec.parts(defs, o, B.Line.body(l)), l, t, fa, defs, o, 1n+n, h, k, out, ns, hn, rest, hg2, ha2, hm2, {==},
        k2 => out2 => ns2 => hn2 => g2 => a2 => m2 => nu_first(t, fa, defs, o, 1n+n, h, k2, out2, ns2, hn2, g2, a2, m2),
        gc2 => ge2 => a2 => last2 => buf2 => k2 => out2 => ns2 => j1 => hn2 => j2 => j3 => j4 => j5 => j6 =>
          nu_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, j1, hn2, j2, j3, j4, j5, j6))

def nu_head.go(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +n: Nat, +h: String, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +hn: {L.any_unsorted(ns) == False{} : Bool}, b: Bool, +l: B.Line,
  +hg: {L.grouped(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  +ha: {L.ascending(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  +hm: {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{b, 1n+n, Nil{}}))) == True{} : Bool},
  ih: @h2: String ->
    {L.grouped(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    {L.ascending(L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.out_items.go(t, fa, defs, o, L.ItSt{False{}, 1n+n, Nil{}}))) == True{} : Bool} ->
    UM(fa, defs, o, U.TLs(t), R.RunSt{1n+n, False{}, h2, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})) ->
  UM(fa, defs, o, U.TLs(t), R.head_line(b, R.RunSt{1n+n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, o, l)):
  match b:
    case False{}:
      ih(h ++ B.Line.text(l), hg, ha, hm)
    case True{}:
      match l:
        case B.Line{+bd, +term}:
          nu_first(t, fa, defs, o, 1n+n, "", k, h ++ R.added(o, term) ++ bd ++ term, ns, hn, hg, ha, hm)

law nu_head:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hn: {L.any_unsorted(ns) == False{} : Bool}
  for +hg: {L.grouped(L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  for +ha: {L.ascending(L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  for +hm: {L.small_moves(R.Opts.w(o), L.ItSt.acc(L.out_items.go(ls, fa, defs, o, L.ItSt{False{}, n, Nil{}}))) == True{} : Bool}
  UM(fa, defs, o, U.TLs(ls), R.RunSt{n, False{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def nu_head(ls, fa, defs, o, n, h, k, out, ns, hn, hg, ha, hm):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      nu_head.go(fa, defs, o, t, n, h, k, out, ns, hn, R.is_chrom_line(B.Line.body(l)), l, hg, ha, hm,
        h2 => g2 => a2 => m2 => nu_head(t, fa, defs, o, 1n+n, h2, k, out, ns, hn, g2, a2, m2))
