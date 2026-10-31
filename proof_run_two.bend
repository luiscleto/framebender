import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_run_steps.bend as T
import ./proof_run_line.bend as N
import ./proof_run_nounsorted.bend as U
import ./proof_run_tail.bend as UT
import ./proof_run_head.bend as H

# Run 2 of twice_run: lines that all go on, each as one item (with -m, each
# is whole or refused under -c w), whose items are grouped by CHROM and sorted
# by key within each CHROM, run to the end (exit 0) and are written in input
# order.

# A body line run 2 takes as one item and goes on with: whole, with an outcome
# that goes on; or refused by -m, with an outcome that goes on, under -c w.
def m1.go(pt: B.Parts, +fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line) -> Bool:
  match pt:
    case B.Whole{}:
      N.go_on(o, L.judge(fa, B.Line.body(l)))
    case B.Pieces{ps}:
      False{}
    case B.Unsplit{c}:
      N.go_on(o, L.judge(fa, B.Line.body(l))) && Bool.not(R.Opts.strict(o))

def m1(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +l: B.Line) -> Bool:
  m1.go(B.Rec.parts(defs, o, B.Line.body(l)), fa, o, l)

def all_m1(ls: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      m1(fa, defs, o, l) && all_m1(t, fa, defs, o)

# Such a line's item.
def it1(pt: B.Parts, +fa: List<&2, B.Contig>, +l: B.Line, +n: Nat) -> R.Item:
  match pt:
    case B.Whole{}:
      L.item(fa, l, n)
    case B.Pieces{ps}:
      L.item(fa, l, n)
    case B.Unsplit{c}:
      +fs = B.Rec.fields(B.Line.body(l))
      R.Item{B.Rec.pos(fs), B.Rec.pos(fs), B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)}, B.Line.text(l)}

def all_go(+fa: List<&2, B.Contig>, +o: B.Opts, ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case +l <> t:
      N.go_on(o, L.judge(fa, B.Line.body(l))) && all_go(fa, o, t)

def asck.go(xs: List<&2, R.Item>, +a: R.Item) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +b <> t:
      (Bool.not(String.eq(R.Item.chrom(a), R.Item.chrom(b))) || Nat.is_le(R.Item.key(a), R.Item.key(b))) && asck.go(t, b)

# Within each CHROM, keys never go down.
def asck(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +a <> t:
      asck.go(t, a)

# A body line that goes on, case by case.
def BLG(-M: R.RunSt -> Type, r: B.Res, +st: R.RunSt, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +hgo: {N.go_on(o, r) == True{} : Bool},
  hkey: @nts: List<&2, B.Note> -> @k2: R.Cnt -> M(R.keyed(st, R.Opts.w(o), L.item_of(r, l, at, inpos), nts, k2))) ->
  M(R.body_line(r, st, o, l, at, inpos)):
  match r:
    case B.Res{B.Broken{}, k, t, s}:
      Empty.absurd(M(R.body_line(B.Res{B.Broken{}, k, t, s}, st, o, l, at, inpos)), P.false_ne_true(hgo))
    case B.Res{B.NoContig{}, k, t, s}:
      Empty.absurd(M(R.body_line(B.Res{B.NoContig{}, k, t, s}, st, o, l, at, inpos)), P.false_ne_true(hgo))
    case B.Res{B.Problem{+c}, k, t, s}:
      match o:
        case B.Opts{+sx, +w, +om_m, +om_z, +a}:
          match sx:
            case True{}:
              Empty.absurd(M(R.body_line(B.Res{B.Problem{c}, k, t, s}, st, B.Opts{True{}, w, om_m, om_z, a}, l, at, inpos)), P.false_ne_true(hgo))
            case False{}:
              hkey([B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))
    case B.Res{B.Skipped{}, k, t, s}:
      hkey(Nil{}, R.bump(R.RunSt.cnt(st), False{}, True{}, False{}))
    case B.Res{B.Normalized{}, +k, +t, +s}:
      match l:
        case B.Line{+bd, +term}:
          hkey(R.stale_note(s, at), R.bump(R.RunSt.cnt(st), Bool.not(String.eq(t, bd)), False{}, False{}))

def not_true(x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, P.false_ne_true(h))
    case False{}:
      {==}

# A refused line whose outcome goes on, under -c w: it goes on as it came.
def UK(-M: R.RunSt -> Type, +r: B.Res, +c: B.Code, +st: R.RunSt, o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +hq: {Bool.and(N.go_on(o, r), Bool.not(R.Opts.strict(o))) == True{} : Bool},
  hkey: @nts: List<&2, B.Note> -> @k2: R.Cnt -> M(R.keyed(st, R.Opts.w(o), R.Item{inpos, inpos, at, B.Line.text(l)}, nts, k2))) ->
  M(L.unsplit_in(r, c, o, st, l, at, inpos)):
  match o:
    case B.Opts{+sx, +w, +om_m, +om_z, +a}:
      match sx:
        case True{}:
          Empty.absurd(M(L.unsplit_in(r, c, B.Opts{True{}, w, om_m, om_z, a}, st, l, at, inpos)),
            P.false_ne_true(Equal.trans(Bool, False{}, Bool.and(N.go_on(B.Opts{True{}, w, om_m, om_z, a}, r), False{}), True{},
              Equal.sym(Bool, Bool.and(N.go_on(B.Opts{True{}, w, om_m, om_z, a}, r), False{}), False{}, P.and_false_r(N.go_on(B.Opts{True{}, w, om_m, om_z, a}, r))), hq)))
        case False{}:
          +o2 = {B.Opts{False{}, w, om_m, om_z, a} : B.Opts}
          +hg = P.and_true_l(N.go_on(o2, r), True{}, hq)
          +hn = {(%Equal.sym(Bool, Bool.not(L.stops(r, False{})), N.go_on(o2, r), H.go_stop(o2, r)) : {_ == True{} : Bool}; hg) : {Bool.not(L.stops(r, False{})) == True{} : Bool}}
          %Equal.sym(Bool, L.stops(r, False{}), False{}, not_true(L.stops(r, False{}), hn)) :
            M(Bool.pick(R.RunSt, _, R.body_line(r, st, o2, l, at, inpos), R.problem_line(False{}, st, w, c, l, at, inpos)))
          hkey([B.Warning{c, at}], R.bump(R.RunSt.cnt(st), False{}, False{}, True{}))

# Exit code 0, and the output is tgt.
def CM(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +ls: List<&2, B.Line>, +tgt: String, st: R.RunSt) -> Type:
  {R.Report.code(R.finish(L.run.go(ls, fa, defs, o, st))) == 0n : Nat} & {R.Report.out(R.finish(L.run.go(ls, fa, defs, o, st))) == tgt : String}

law all_le_suffix:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +h: {S.all_le(S.app(xs, ys), k) == True{} : Bool}
  {S.all_le(ys, k) == True{} : Bool}

def all_le_suffix(xs, ys, k, h):
  match xs:
    case Nil{}:
      h
    case +x <> +t:
      all_le_suffix(t, ys, k, P.and_true_r(Nat.is_le(R.Item.key(x), k), S.all_le(S.app(t, ys), k), h))

law all_le_prefix:
  for +xs: List<&2, R.Item>
  for +ys: List<&2, R.Item>
  for +k: Nat
  for +h: {S.all_le(S.app(xs, ys), k) == True{} : Bool}
  {S.all_le(xs, k) == True{} : Bool}

def all_le_prefix(xs, ys, k, h):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      S.and_intro(Nat.is_le(R.Item.key(x), k), S.all_le(t, k), P.and_true_l(Nat.is_le(R.Item.key(x), k), S.all_le(S.app(t, ys), k), h),
        all_le_prefix(t, ys, k, P.and_true_r(Nat.is_le(R.Item.key(x), k), S.all_le(S.app(t, ys), k), h)))

law flast_le:
  for +xs: List<&2, R.Item>
  for +last: Maybe<&2, R.Item>
  for +k: Nat
  for +h1: {Nat.is_le(S.lkey(last), k) == True{} : Bool}
  for +h2: {S.all_le(xs, k) == True{} : Bool}
  {Nat.is_le(S.lkey(S.flast(xs, last)), k) == True{} : Bool}

def flast_le(xs, last, k, h1, h2):
  match xs:
    case Nil{}:
      h1
    case +x <> +t:
      flast_le(t, Some{x}, k, P.and_true_l(Nat.is_le(R.Item.key(x), k), S.all_le(t, k), h2), P.and_true_r(Nat.is_le(R.Item.key(x), k), S.all_le(t, k), h2))

def texts1(+z: R.Item) -> String:
  L.texts([z])

# One more item of the current run, no lower than every key so far.
def two.same(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +tgt: String, +n: Nat, +h: String, +c: Maybe<&2, String>,
  +e: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +z: R.Item, +pre: String,
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hz: {S.all_le(buf, R.Item.key(z)) == True{} : Bool},
  +hlz: {Nat.is_le(S.lkey(last), R.Item.key(z)) == True{} : Bool},
  +hp: {out ++ L.texts(buf) == pre : String},
  ih: @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} -> {S.all_le(buf2, R.Item.key(z)) == True{} : Bool} ->
    {Nat.is_le(S.lkey(last2), R.Item.key(z)) == True{} : Bool} -> {out2 ++ L.texts(buf2) == pre ++ texts1(z) : String} ->
    CM(fa, defs, o, t, tgt, R.RunSt{n, True{}, h, c, e, last2, buf2, k, out2, ns, False{}})) ->
  CM(fa, defs, o, t, tgt, R.same_run(R.RunSt{n, True{}, h, c, e, last, buf, k, out, ns, False{}}, R.Opts.w(o), z)):
  +w = R.Opts.w(o)
  +p = R.Item.inpos(z)
  +ins = R.insert(z, buf)
  +tk = R.take_ready(w, p, ins)
  +dr = R.drop_ready(w, p, ins)
  +K = S.lkey(last)
  +kz = R.Item.key(z)
  +eins = {(%P.append_nil(R.Item, buf) : {R.insert(z, _) == S.app(buf, [z]) : List<&2, R.Item>}; S.insert_app(z, buf, Nil{}, hz)) :
    {ins == S.app(buf, [z]) : List<&2, R.Item>}}
  +sTD = U.sr_sorted(w, z, buf, last, hb, hlz)
  +sT = S.sorted_prefix(tk, dr, K, sTD)
  +fs = S.flush_sorted(tk, last, sT)
  +etd = Equal.sym(List<&2, R.Item>, S.app(tk, dr), ins, S.take_drop(w, p, ins))
  T.SR(st2 => CM(fa, defs, o, t, tgt, st2), n, True{}, h, c, e, last, buf, k, out, ns, False{}, w, z,
    +o3 => +bad => +prev => ef => Empty.absurd(CM(fa, defs, o, t, tgt, R.RunSt{n, True{}, h, c, e, last, Nil{}, k, out ++ o3,
        List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
      S.broke_ne_flushed(o3, bad, prev, L.texts(tk), S.flast(tk, last),
        Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(tk, last), R.Flushed{L.texts(tk), S.flast(tk, last)},
          Equal.sym(R.Flush, R.flush(tk, last), R.Broke{o3, bad, prev}, ef), fs))),
    +o2 => +l2 => +ef =>
      +el2 = {Equal.sym(Maybe<&2, R.Item>, l2, S.flast(tk, last), S.flushed_last(tk, last, o2, l2, sT, ef)) : {S.flast(tk, last) == l2 : Maybe<&2, R.Item>}}
      +eo2 = {Equal.sym(String, o2, L.texts(tk), S.flushed_text(tk, last, o2, l2, sT, ef)) : {L.texts(tk) == o2 : String}}
      +j4 = {(%el2 : {S.sorted_from(dr, S.lkey(_)) == True{} : Bool}; S.sorted_rest(tk, dr, last, sTD)) : {S.sorted_from(dr, S.lkey(l2)) == True{} : Bool}}
      +allz = {(%etd : {S.all_le(_, kz) == True{} : Bool};
          %Equal.sym(List<&2, R.Item>, ins, S.app(buf, [z]), eins) : {S.all_le(_, kz) == True{} : Bool};
          S.all_le_app(buf, [z], kz, hz, S.and_intro(Nat.is_le(kz, kz), True{}, P.le_refl(kz), {==}))) :
        {S.all_le(S.app(tk, dr), kz) == True{} : Bool}}
      +jz = all_le_suffix(tk, dr, kz, allz)
      +jl = {(%el2 : {Nat.is_le(S.lkey(_), kz) == True{} : Bool}; flast_le(tk, last, kz, hlz, all_le_prefix(tk, dr, kz, allz))) :
        {Nat.is_le(S.lkey(l2), kz) == True{} : Bool}}
      +jp = {(%eo2 : {(out ++ _) ++ L.texts(dr) == pre ++ texts1(z) : String};
          %Equal.sym(String, (out ++ L.texts(tk)) ++ L.texts(dr), out ++ (L.texts(tk) ++ L.texts(dr)), Q.s_append_assoc(out, L.texts(tk), L.texts(dr))) :
            {_ == pre ++ texts1(z) : String};
          %S.texts_app(tk, dr) : {out ++ _ == pre ++ texts1(z) : String};
          %etd : {out ++ L.texts(_) == pre ++ texts1(z) : String};
          %Equal.sym(List<&2, R.Item>, ins, S.app(buf, [z]), eins) : {out ++ L.texts(_) == pre ++ texts1(z) : String};
          %Equal.sym(String, L.texts(S.app(buf, [z])), L.texts(buf) ++ texts1(z), S.texts_app(buf, [z])) : {out ++ _ == pre ++ texts1(z) : String};
          %Q.s_append_assoc(out, L.texts(buf), texts1(z)) : {_ == pre ++ texts1(z) : String};
          %Equal.sym(String, out ++ L.texts(buf), pre, hp) : {_ ++ texts1(z) == pre ++ texts1(z) : String};
          {==}) : {(out ++ o2) ++ L.texts(dr) == pre ++ texts1(z) : String}}
      ih(l2, dr, out ++ o2, j4, jz, jl, jp))

def IHT(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String,
  +k: R.Cnt, +ns: List<&2, B.Note>) -> Type:
  @gc2: String -> @ge2: List<&2, String> -> @a2: R.Item -> @last2: Maybe<&2, R.Item> -> @buf2: List<&2, R.Item> -> @out2: String -> @pre2: String ->
    {R.Item.chrom(a2) == gc2 : String} ->
    {S.sorted_from(buf2, S.lkey(last2)) == True{} : Bool} ->
    {S.all_le(buf2, R.Item.key(a2)) == True{} : Bool} ->
    {Nat.is_le(S.lkey(last2), R.Item.key(a2)) == True{} : Bool} ->
    {out2 ++ L.texts(buf2) == pre2 : String} ->
    {L.grouped.go(rest, gc2, ge2) == True{} : Bool} ->
    {asck.go(rest, a2) == True{} : Bool} ->
    CM(fa, defs, o, t, pre2 ++ L.texts(rest), R.RunSt{n, True{}, h, Some{gc2}, ge2, last2, buf2, k, out2, ns, False{}})

law cm_conv:
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +t: List<&2, B.Line>
  for +t1: String
  for +t2: String
  for +st: R.RunSt
  for +e: {t1 == t2 : String}
  for c: CM(fa, defs, o, t, t1, st)
  CM(fa, defs, o, t, t2, st)

def cm_conv(fa, defs, o, t, t1, t2, st, e, c):
  %e : CM(fa, defs, o, t, _, st)
  c

law tgt_eq:
  for +pre: String
  for +z: R.Item
  for +rest: List<&2, R.Item>
  {(pre ++ texts1(z)) ++ L.texts(rest) == pre ++ L.texts(z <> rest) : String}

def tgt_eq(pre, z, rest):
  %Equal.sym(String, L.texts(z <> rest), texts1(z) ++ L.texts(rest), S.texts_app([z], rest)) : {(pre ++ texts1(z)) ++ L.texts(rest) == pre ++ _ : String}
  Q.s_append_assoc(pre, texts1(z), L.texts(rest))

def two.key(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>,
  +n: Nat, +h: String, +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt,
  +out: String, +ns: List<&2, B.Note>, +a: R.Item, +z: R.Item, +pre: String,
  +ea: {R.Item.chrom(a) == gc : String},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hab: {S.all_le(buf, R.Item.key(a)) == True{} : Bool},
  +hla: {Nat.is_le(S.lkey(last), R.Item.key(a)) == True{} : Bool},
  +hp: {out ++ L.texts(buf) == pre : String},
  +hg: {L.grouped.go(z <> rest, gc, ge) == True{} : Bool},
  +hk: {asck.go(z <> rest, a) == True{} : Bool},
  b: Bool, +eb: {String.eq(gc, R.Item.chrom(z)) == b : Bool}, ih: IHT(fa, defs, o, t, rest, n, h, k, ns)) ->
  CM(fa, defs, o, t, pre ++ L.texts(z <> rest), R.keyed.go(b, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, R.Opts.w(o), R.Item.chrom(z), z)):
  match b:
    case True{}:
      +cz = R.Item.chrom(z)
      +ka = R.Item.key(a)
      +kz = R.Item.key(z)
      +es = Equal.trans(Bool, String.eq(cz, gc), String.eq(gc, cz), True{}, Q.str_eq_sym(gc, cz), eb)
      +egc = Equal.sym(String, gc, cz, Q.str_eq_sound(gc, cz, eb))
      +h1 = P.and_true_l(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(ka, kz)), asck.go(rest, z), hk)
      +har = P.and_true_r(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(ka, kz)), asck.go(rest, z), hk)
      +h2 = {(%ea : {Bool.or(Bool.not(String.eq(_, cz)), Nat.is_le(ka, kz)) == True{} : Bool}; h1) :
        {Bool.or(Bool.not(String.eq(gc, cz)), Nat.is_le(ka, kz)) == True{} : Bool}}
      +le = {(%eb : {Bool.or(Bool.not(_), Nat.is_le(ka, kz)) == True{} : Bool}; h2) : {Nat.is_le(ka, kz) == True{} : Bool}}
      +hg1 = {(%es : {Bool.and(Bool.or(_, Bool.not(R.has(cz, gc <> ge))), L.grouped.go(rest, cz, Bool.pick(List<&2, String>, _, ge, gc <> ge))) == True{} : Bool}; hg) :
        {L.grouped.go(rest, cz, ge) == True{} : Bool}}
      +hg2 = {(%egc : {L.grouped.go(rest, _, ge) == True{} : Bool}; hg1) : {L.grouped.go(rest, gc, ge) == True{} : Bool}}
      two.same(fa, defs, o, t, pre ++ L.texts(z <> rest), n, h, Some{gc}, ge, last, buf, k, out, ns, z, pre, hb,
        S.all_le_mono(buf, ka, kz, hab, le), Q.le_trans(S.lkey(last), ka, kz, hla, le), hp,
        +last2 => +buf2 => +out2 => j4 => jz => jl => jp =>
          cm_conv(fa, defs, o, t, (pre ++ texts1(z)) ++ L.texts(rest), pre ++ L.texts(z <> rest),
            R.RunSt{n, True{}, h, Some{gc}, ge, last2, buf2, k, out2, ns, False{}}, tgt_eq(pre, z, rest),
            ih(gc, ge, z, last2, buf2, out2, pre ++ texts1(z), egc, j4, jz, jl, jp, hg2, har)))
    case False{}:
      +cz = R.Item.chrom(z)
      +w = R.Opts.w(o)
      +es = Equal.trans(Bool, String.eq(cz, gc), String.eq(gc, cz), False{}, Q.str_eq_sym(gc, cz), eb)
      +har = P.and_true_r(Bool.or(Bool.not(String.eq(R.Item.chrom(a), cz)), Nat.is_le(R.Item.key(a), R.Item.key(z))), asck.go(rest, z), hk)
      +hg1 = {(%es : {Bool.and(Bool.or(_, Bool.not(Bool.or(_, R.has(cz, ge)))), L.grouped.go(rest, cz, Bool.pick(List<&2, String>, _, ge, gc <> ge))) == True{} : Bool}; hg) :
        {Bool.and(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge)) == True{} : Bool}}
      +hh = P.not_true(R.has(cz, ge), P.and_true_l(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge), hg1))
      +hg2 = P.and_true_r(Bool.not(R.has(cz, ge)), L.grouped.go(rest, cz, gc <> ge), hg1)
      +fs = S.flush_sorted(buf, last, hb)
      +tgt = pre ++ L.texts(z <> rest)
      T.NR(st2 => CM(fa, defs, o, t, tgt, st2), n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}, w, cz, z,
        +o3 => +bad => +prev => ef => Empty.absurd(CM(fa, defs, o, t, tgt, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o3,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{bad}, prev}]), True{}}),
          S.broke_ne_flushed(o3, bad, prev, L.texts(buf), S.flast(buf, last),
            Equal.trans(R.Flush, R.Broke{o3, bad, prev}, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)},
              Equal.sym(R.Flush, R.flush(buf, last), R.Broke{o3, bad, prev}, ef), fs))),
        +o2 => +l2 => ef => eh => Empty.absurd(CM(fa, defs, o, t, tgt, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out ++ o2,
            List.append(&2, B.Note, ns, [B.Stop{B.Unsorted{}, Some{R.Item.at(z)}, None{}}]), True{}}),
          P.true_ne_false(Equal.trans(Bool, True{}, R.has(cz, ge), False{}, Equal.sym(Bool, R.has(cz, ge), True{}, eh), hh))),
        +o2 => +l2 => +ef => eh =>
          +eo2 = {Equal.sym(String, o2, L.texts(buf), S.flushed_text(buf, last, o2, l2, hb, ef)) : {L.texts(buf) == o2 : String}}
          +hp2 = {(%eo2 : {(out ++ _) ++ "" == pre : String}; %Equal.sym(String, (out ++ L.texts(buf)) ++ "", out ++ L.texts(buf), Q.s_append_nil(out ++ L.texts(buf))) : {_ == pre : String}; hp) :
            {(out ++ o2) ++ L.texts(Nil{}) == pre : String}}
          two.same(fa, defs, o, t, tgt, n, h, Some{cz}, gc <> ge, None{}, Nil{}, k, out ++ o2, ns, z, pre, {==}, {==}, P.le_zero_l(R.Item.key(z)), hp2,
            +last2 => +buf2 => +out2 => j4 => jz => jl => jp =>
              cm_conv(fa, defs, o, t, (pre ++ texts1(z)) ++ L.texts(rest), tgt,
                R.RunSt{n, True{}, h, Some{cz}, gc <> ge, last2, buf2, k, out2, ns, False{}}, tgt_eq(pre, z, rest),
                ih(cz, gc <> ge, z, last2, buf2, out2, pre ++ texts1(z), {==}, j4, jz, jl, jp, hg2, har))))

def two.fin(+out: String, +ns: List<&2, B.Note>, +tb: String, +fl: Maybe<&2, R.Item>, k: R.Cnt, +tgt: String,
  +e: {out ++ tb == tgt : String}) ->
  {R.Report.code(R.finish.flush(R.Flushed{tb, fl}, out, ns, k)) == 0n : Nat} & {R.Report.out(R.finish.flush(R.Flushed{tb, fl}, out, ns, k)) == tgt : String}:
  match k:
    case R.Cnt{a, b, c, d}:
      ({==}, e)

# The rest of run 2 after a line, whatever the counts and notes.
def KT(+fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +t: List<&2, B.Line>, +rest: List<&2, R.Item>, +n: Nat, +h: String) -> Type:
  @k2: R.Cnt -> @ns2: List<&2, B.Note> -> IHT(fa, defs, o, t, rest, n, h, k2, ns2)

# One line of run 2 within a CHROM run whose last line was a, by what -m does
# with it.
def two.line(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +gc: String, +ge: List<&2, String>, +last: Maybe<&2, R.Item>, +buf: List<&2, R.Item>, +k: R.Cnt, +out: String, +ns: List<&2, B.Note>,
  +a: R.Item, +pre: String, +rest: List<&2, R.Item>,
  +ea: {R.Item.chrom(a) == gc : String},
  +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool},
  +hab: {S.all_le(buf, R.Item.key(a)) == True{} : Bool},
  +hla: {Nat.is_le(S.lkey(last), R.Item.key(a)) == True{} : Bool},
  +hp: {out ++ L.texts(buf) == pre : String},
  +hg: {L.grouped.go(S.app(L.items.line(pt, fa, l, n), rest), gc, ge) == True{} : Bool},
  +hk: {asck.go(S.app(L.items.line(pt, fa, l, n), rest), a) == True{} : Bool},
  +hm: {m1.go(pt, fa, o, l) == True{} : Bool},
  kt: KT(fa, defs, o, t, rest, n, h)) ->
  CM(fa, defs, o, t, pre ++ L.texts(S.app(L.items.line(pt, fa, l, n), rest)),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, l,
      B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +st1 = {R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, n)
      +tgt = pre ++ L.texts(it <> rest)
      BLG(st2 => CM(fa, defs, o, t, tgt, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), hm,
        +nts => +k2 =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          two.key(fa, defs, o, t, rest, n, h, gc, ge, last, buf, k2, out, ns2, a, it, pre, ea, hb, hab, hla, hp, hg, hk,
            String.eq(gc, R.Item.chrom(it)), {==}, kt(k2, ns2)))
    case B.Pieces{+ps}:
      Empty.absurd(CM(fa, defs, o, t, pre ++ L.texts(S.app(L.items.line(B.Pieces{ps}, fa, l, n), rest)),
        L.body_in(B.Pieces{ps}, fa, o, R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}}, l,
          B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))),
        P.false_ne_true(hm))
    case B.Unsplit{+c}:
      +st1 = {R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = {R.Item{B.Rec.pos(fs), B.Rec.pos(fs), at, B.Line.text(l)} : R.Item}
      +tgt = pre ++ L.texts(it <> rest)
      UK(st2 => CM(fa, defs, o, t, tgt, st2), L.judge(fa, B.Line.body(l)), c, st1, o, l, at, B.Rec.pos(fs), hm,
        +nts => +k2 =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          two.key(fa, defs, o, t, rest, n, h, gc, ge, last, buf, k2, out, ns2, a, it, pre, ea, hb, hab, hla, hp, hg, hk,
            String.eq(gc, R.Item.chrom(it)), {==}, kt(k2, ns2)))

# Run 2 within a CHROM run whose last line was a.
law two_run:
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
  for +pre: String
  for +ea: {R.Item.chrom(a) == gc : String}
  for +hb: {S.sorted_from(buf, S.lkey(last)) == True{} : Bool}
  for +hab: {S.all_le(buf, R.Item.key(a)) == True{} : Bool}
  for +hla: {Nat.is_le(S.lkey(last), R.Item.key(a)) == True{} : Bool}
  for +hp: {out ++ L.texts(buf) == pre : String}
  for +hg: {L.grouped.go(UT.mitems(ls, fa, defs, o, n), gc, ge) == True{} : Bool}
  for +hk: {asck.go(UT.mitems(ls, fa, defs, o, n), a) == True{} : Bool}
  for +hgo: {all_m1(ls, fa, defs, o) == True{} : Bool}
  CM(fa, defs, o, ls, pre ++ L.texts(UT.mitems(ls, fa, defs, o, n)), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})

def two_run(ls, fa, defs, o, n, h, gc, ge, last, buf, k, out, ns, a, pre, ea, hb, hab, hla, hp, hg, hk, hgo):
  match ls:
    case Nil{}:
      %Equal.sym(R.Flush, R.flush(buf, last), R.Flushed{L.texts(buf), S.flast(buf, last)}, S.flush_sorted(buf, last, hb)) :
        {R.Report.code(R.finish.flush(_, out, ns, k)) == 0n : Nat} & {R.Report.out(R.finish.flush(_, out, ns, k)) == pre ++ "" : String}
      two.fin(out, ns, L.texts(buf), S.flast(buf, last), k, pre ++ "",
        Equal.trans(String, out ++ L.texts(buf), pre, pre ++ "", hp, Equal.sym(String, pre ++ "", pre, Q.s_append_nil(pre))))
    case +l <> +t:
      +pt = B.Rec.parts(defs, o, B.Line.body(l))
      +rest = UT.mitems(t, fa, defs, o, 1n+n)
      +ec = UT.mitems_cons(l, t, fa, defs, o, n)
      +xs = S.app(L.items.line(pt, fa, l, 1n+n), rest)
      +hg2 = {(%ec : {L.grouped.go(_, gc, ge) == True{} : Bool}; hg) : {L.grouped.go(xs, gc, ge) == True{} : Bool}}
      +hk2 = {(%ec : {asck.go(_, a) == True{} : Bool}; hk) : {asck.go(xs, a) == True{} : Bool}}
      +hgl = P.and_true_l(m1(fa, defs, o, l), all_m1(t, fa, defs, o), hgo)
      +hgt = P.and_true_r(m1(fa, defs, o, l), all_m1(t, fa, defs, o), hgo)
      %Equal.sym(List<&2, R.Item>, UT.mitems(l <> t, fa, defs, o, n), xs, ec) :
        CM(fa, defs, o, l <> t, pre ++ L.texts(_), R.RunSt{n, True{}, h, Some{gc}, ge, last, buf, k, out, ns, False{}})
      two.line(pt, l, t, fa, defs, o, 1n+n, h, gc, ge, last, buf, k, out, ns, a, pre, rest, ea, hb, hab, hla, hp, hg2, hk2, hgl,
        k2 => ns2 => gc2 => ge2 => a2 => last2 => buf2 => out2 => pre2 => j1 => j2 => j3 => j4 => j5 => j6 => j7 =>
          two_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, pre2, j1, j2, j3, j4, j5, j6, j7, hgt))

# The first line of run 2's body, by what -m does with it.
def two.fline(pt: B.Parts, +l: B.Line, +t: List<&2, B.Line>, +fa: List<&2, B.Contig>, +defs: B.Defs, +o: B.Opts, +n: Nat, +h: String,
  +k: R.Cnt, +out: String, +ns: List<&2, B.Note>, +rest: List<&2, R.Item>,
  +hg: {L.grouped(S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +hk: {asck(S.app(L.items.line(pt, fa, l, n), rest)) == True{} : Bool},
  +hm: {m1.go(pt, fa, o, l) == True{} : Bool},
  kt: KT(fa, defs, o, t, rest, n, h)) ->
  CM(fa, defs, o, t, out ++ L.texts(S.app(L.items.line(pt, fa, l, n), rest)),
    L.body_in(pt, fa, o, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, l,
      B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))):
  match pt:
    case B.Whole{}:
      +st1 = {R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = L.item(fa, l, n)
      +cz = R.Item.chrom(it)
      +tgt = out ++ L.texts(it <> rest)
      BLG(st2 => CM(fa, defs, o, t, tgt, st2), L.judge(fa, B.Line.body(l)), st1, o, l, at, B.Rec.pos(fs), hm,
        +nts => +k2 =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          two.same(fa, defs, o, t, tgt, n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, out, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            Equal.trans(String, (out ++ "") ++ "", out ++ "", out, Q.s_append_nil(out ++ ""), Q.s_append_nil(out)),
            +last2 => +buf2 => +out2 => j4 => jz => jl => jp =>
              cm_conv(fa, defs, o, t, (out ++ texts1(it)) ++ L.texts(rest), tgt,
                R.RunSt{n, True{}, h, Some{cz}, Nil{}, last2, buf2, k2, out2, ns2, False{}}, tgt_eq(out, it, rest),
                kt(k2, ns2, cz, Nil{}, it, last2, buf2, out2, out ++ texts1(it), {==}, j4, jz, jl, jp, hg, hk))))
    case B.Pieces{+ps}:
      Empty.absurd(CM(fa, defs, o, t, out ++ L.texts(S.app(L.items.line(B.Pieces{ps}, fa, l, n), rest)),
        L.body_in(B.Pieces{ps}, fa, o, R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}}, l,
          B.At{n, B.Rec.field(B.Rec.fields(B.Line.body(l)), 0n), B.Rec.field(B.Rec.fields(B.Line.body(l)), 1n)}, B.Rec.pos(B.Rec.fields(B.Line.body(l))))),
        P.false_ne_true(hm))
    case B.Unsplit{+c}:
      +st1 = {R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}} : R.RunSt}
      +fs = B.Rec.fields(B.Line.body(l))
      +at = {B.At{n, B.Rec.field(fs, 0n), B.Rec.field(fs, 1n)} : B.At}
      +it = {R.Item{B.Rec.pos(fs), B.Rec.pos(fs), at, B.Line.text(l)} : R.Item}
      +cz = R.Item.chrom(it)
      +tgt = out ++ L.texts(it <> rest)
      UK(st2 => CM(fa, defs, o, t, tgt, st2), L.judge(fa, B.Line.body(l)), c, st1, o, l, at, B.Rec.pos(fs), hm,
        +nts => +k2 =>
          +ns2 = List.append(&2, B.Note, ns, nts)
          two.same(fa, defs, o, t, tgt, n, h, Some{cz}, Nil{}, None{}, Nil{}, k2, out ++ "", ns2, it, out, {==}, {==}, P.le_zero_l(R.Item.key(it)),
            Equal.trans(String, (out ++ "") ++ "", out ++ "", out, Q.s_append_nil(out ++ ""), Q.s_append_nil(out)),
            +last2 => +buf2 => +out2 => j4 => jz => jl => jp =>
              cm_conv(fa, defs, o, t, (out ++ texts1(it)) ++ L.texts(rest), tgt,
                R.RunSt{n, True{}, h, Some{cz}, Nil{}, last2, buf2, k2, out2, ns2, False{}}, tgt_eq(out, it, rest),
                kt(k2, ns2, cz, Nil{}, it, last2, buf2, out2, out ++ texts1(it), {==}, j4, jz, jl, jp, hg, hk))))

# Run 2 from the start of the body.
law two_first:
  for +ls: List<&2, B.Line>
  for +fa: List<&2, B.Contig>
  for +defs: B.Defs
  for +o: B.Opts
  for +n: Nat
  for +h: String
  for +k: R.Cnt
  for +out: String
  for +ns: List<&2, B.Note>
  for +hg: {L.grouped(UT.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  for +hk: {asck(UT.mitems(ls, fa, defs, o, n)) == True{} : Bool}
  for +hgo: {all_m1(ls, fa, defs, o) == True{} : Bool}
  CM(fa, defs, o, ls, out ++ L.texts(UT.mitems(ls, fa, defs, o, n)), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})

def two_first(ls, fa, defs, o, n, h, k, out, ns, hg, hk, hgo):
  match ls:
    case Nil{}:
      two.fin(out, ns, "", None{}, k, out ++ "", {==})
    case +l <> +t:
      +pt = B.Rec.parts(defs, o, B.Line.body(l))
      +rest = UT.mitems(t, fa, defs, o, 1n+n)
      +ec = UT.mitems_cons(l, t, fa, defs, o, n)
      +xs = S.app(L.items.line(pt, fa, l, 1n+n), rest)
      +hg2 = {(%ec : {L.grouped(_) == True{} : Bool}; hg) : {L.grouped(xs) == True{} : Bool}}
      +hk2 = {(%ec : {asck(_) == True{} : Bool}; hk) : {asck(xs) == True{} : Bool}}
      +hgl = P.and_true_l(m1(fa, defs, o, l), all_m1(t, fa, defs, o), hgo)
      +hgt = P.and_true_r(m1(fa, defs, o, l), all_m1(t, fa, defs, o), hgo)
      %Equal.sym(List<&2, R.Item>, UT.mitems(l <> t, fa, defs, o, n), xs, ec) :
        CM(fa, defs, o, l <> t, out ++ L.texts(_), R.RunSt{n, True{}, h, None{}, Nil{}, None{}, Nil{}, k, out, ns, False{}})
      two.fline(pt, l, t, fa, defs, o, 1n+n, h, k, out, ns, rest, hg2, hk2, hgl,
        k2 => ns2 => gc2 => ge2 => a2 => last2 => buf2 => out2 => pre2 => j1 => j2 => j3 => j4 => j5 => j6 => j7 =>
          two_run(t, fa, defs, o, 1n+n, h, gc2, ge2, last2, buf2, k2, out2, ns2, a2, pre2, j1, j2, j3, j4, j5, j6, j7, hgt))
