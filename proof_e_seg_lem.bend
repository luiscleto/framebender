import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S
import ./proof_e_defs.bend as SD
import ./proof_e_seg_defs.bend as G

# Phase E, area "seg": items moved on by d keep their keys, so the buffer
# rules commute with the move; and the small facts about real items.

law texts_eq:
  for +xs: List<&2, R.Item>
  {SD.texts(xs) == L.texts(xs) : String}

def texts_eq(xs):
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %texts_eq(t) : {R.Item.text(x) ++ SD.texts(t) == R.Item.text(x) ++ _ : String}
      {==}

law key_sh:
  for +d: Nat
  for +x: R.Item
  {R.Item.key(SD.item_shift(d, x)) == R.Item.key(x) : Nat}

def key_sh(d, x):
  match x:
    case R.Item{k, p, B.At{ln, c, s}, t}:
      {==}

law ready_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +x: R.Item
  {R.ready(w, p, SD.item_shift(d, x)) == R.ready(w, p, x) : Bool}

def ready_sh(w, p, d, x):
  match x:
    case R.Item{k, ip, B.At{ln, c, s}, t}:
      {==}

law hr_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +b: List<&2, R.Item>
  {R.head_ready(w, p, SD.items_shift(d, b)) == R.head_ready(w, p, b) : Bool}

def hr_sh(w, p, d, b):
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      ready_sh(w, p, d, x)

law trg_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +b: List<&2, R.Item>
  for +ok: Bool
  {R.take_ready.go(SD.items_shift(d, b), ok, w, p) == SD.items_shift(d, R.take_ready.go(b, ok, w, p)) : List<&2, R.Item>}

def trg_sh(w, p, d, b, ok):
  match b ok:
    case Nil{} _:
      {==}
    case +x <> +t True{}:
      %Equal.sym(Bool, R.head_ready(w, p, SD.items_shift(d, t)), R.head_ready(w, p, t), hr_sh(w, p, d, t)) :
        {SD.item_shift(d, x) <> R.take_ready.go(SD.items_shift(d, t), _, w, p) == SD.items_shift(d, R.take_ready.go(x <> t, True{}, w, p)) : List<&2, R.Item>}
      %trg_sh(w, p, d, t, R.head_ready(w, p, t)) :
        {SD.item_shift(d, x) <> R.take_ready.go(SD.items_shift(d, t), R.head_ready(w, p, t), w, p) == SD.item_shift(d, x) <> _ : List<&2, R.Item>}
      {==}
    case +x <> +t False{}:
      {==}

law drg_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +b: List<&2, R.Item>
  for +ok: Bool
  {R.drop_ready.go(SD.items_shift(d, b), ok, w, p) == SD.items_shift(d, R.drop_ready.go(b, ok, w, p)) : List<&2, R.Item>}

def drg_sh(w, p, d, b, ok):
  match b ok:
    case Nil{} _:
      {==}
    case +x <> +t True{}:
      %Equal.sym(Bool, R.head_ready(w, p, SD.items_shift(d, t)), R.head_ready(w, p, t), hr_sh(w, p, d, t)) :
        {R.drop_ready.go(SD.items_shift(d, t), _, w, p) == SD.items_shift(d, R.drop_ready.go(x <> t, True{}, w, p)) : List<&2, R.Item>}
      drg_sh(w, p, d, t, R.head_ready(w, p, t))
    case +x <> +t False{}:
      {==}

law tr_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +b: List<&2, R.Item>
  {R.take_ready(w, p, SD.items_shift(d, b)) == SD.items_shift(d, R.take_ready(w, p, b)) : List<&2, R.Item>}

def tr_sh(w, p, d, b):
  %Equal.sym(Bool, R.head_ready(w, p, SD.items_shift(d, b)), R.head_ready(w, p, b), hr_sh(w, p, d, b)) :
    {R.take_ready.go(SD.items_shift(d, b), _, w, p) == SD.items_shift(d, R.take_ready(w, p, b)) : List<&2, R.Item>}
  trg_sh(w, p, d, b, R.head_ready(w, p, b))

law dr_sh:
  for +w: Nat
  for +p: Nat
  for +d: Nat
  for +b: List<&2, R.Item>
  {R.drop_ready(w, p, SD.items_shift(d, b)) == SD.items_shift(d, R.drop_ready(w, p, b)) : List<&2, R.Item>}

def dr_sh(w, p, d, b):
  %Equal.sym(Bool, R.head_ready(w, p, SD.items_shift(d, b)), R.head_ready(w, p, b), hr_sh(w, p, d, b)) :
    {R.drop_ready.go(SD.items_shift(d, b), _, w, p) == SD.items_shift(d, R.drop_ready(w, p, b)) : List<&2, R.Item>}
  drg_sh(w, p, d, b, R.head_ready(w, p, b))

def ins_sh.go(+d: Nat, +e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +g: Bool,
  ih: {R.insert(SD.item_shift(d, e), SD.items_shift(d, t)) == SD.items_shift(d, R.insert(e, t)) : List<&2, R.Item>}) ->
  {R.insert.put(g, SD.item_shift(d, x), SD.item_shift(d, e), SD.items_shift(d, t), R.insert(SD.item_shift(d, e), SD.items_shift(d, t)))
    == SD.items_shift(d, R.insert.put(g, x, e, t, R.insert(e, t))) : List<&2, R.Item>}:
  match g:
    case True{}:
      %Equal.sym(List<&2, R.Item>, R.insert(SD.item_shift(d, e), SD.items_shift(d, t)), SD.items_shift(d, R.insert(e, t)), ih) :
        {SD.item_shift(d, x) <> _ == SD.items_shift(d, x <> R.insert(e, t)) : List<&2, R.Item>}
      {==}
    case False{}:
      {==}

law ins_sh:
  for +d: Nat
  for +e: R.Item
  for +b: List<&2, R.Item>
  {R.insert(SD.item_shift(d, e), SD.items_shift(d, b)) == SD.items_shift(d, R.insert(e, b)) : List<&2, R.Item>}

def ins_sh(d, e, b):
  match b:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat, R.Item.key(SD.item_shift(d, x)), R.Item.key(x), key_sh(d, x)) :
        {R.insert.put(Nat.is_le(_, R.Item.key(SD.item_shift(d, e))), SD.item_shift(d, x), SD.item_shift(d, e), SD.items_shift(d, t), R.insert(SD.item_shift(d, e), SD.items_shift(d, t)))
          == SD.items_shift(d, R.insert(e, x <> t)) : List<&2, R.Item>}
      %Equal.sym(Nat, R.Item.key(SD.item_shift(d, e)), R.Item.key(e), key_sh(d, e)) :
        {R.insert.put(Nat.is_le(R.Item.key(x), _), SD.item_shift(d, x), SD.item_shift(d, e), SD.items_shift(d, t), R.insert(SD.item_shift(d, e), SD.items_shift(d, t)))
          == SD.items_shift(d, R.insert(e, x <> t)) : List<&2, R.Item>}
      ins_sh.go(d, e, x, t, Nat.is_le(R.Item.key(x), R.Item.key(e)), ins_sh(d, e, t))

law text_sh:
  for +d: Nat
  for +x: R.Item
  {R.Item.text(SD.item_shift(d, x)) == R.Item.text(x) : String}

def text_sh(d, x):
  match x:
    case R.Item{k, p, B.At{ln, c, s}, t}:
      {==}

law notph:
  for +x: R.Item
  for e: {SD.is_phantom(x) == False{} : Bool}
  {Bool.not(SD.is_phantom(x)) == True{} : Bool}

def notph(x, e):
  %Equal.sym(Bool, SD.is_phantom(x), False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

law real_hd:
  for +x: R.Item
  for +t: List<&2, R.Item>
  for e: {G.allreal(x <> t) == True{} : Bool}
  {SD.is_phantom(x) == False{} : Bool}

def real_hd(x, t, e):
  P.not_true(SD.is_phantom(x), P.and_true_l(Bool.not(SD.is_phantom(x)), G.allreal(t), e))

law real_tl:
  for +x: R.Item
  for +t: List<&2, R.Item>
  for e: {G.allreal(x <> t) == True{} : Bool}
  {G.allreal(t) == True{} : Bool}

def real_tl(x, t, e):
  P.and_true_r(Bool.not(SD.is_phantom(x)), G.allreal(t), e)

law qok_real:
  for +q: Maybe<&2, R.Item>
  for +y: R.Item
  for e: {SD.is_phantom(y) == False{} : Bool}
  {G.qok(q, Some{y}) == True{} : Bool}

def qok_real(q, y, e):
  %Equal.sym(Bool, SD.is_phantom(y), False{}, e) : {G.qok.k(_, q, y) == True{} : Bool}
  {==}

law img_real:
  for +q: Maybe<&2, R.Item>
  for +y: R.Item
  for +d: Nat
  for e: {SD.is_phantom(y) == False{} : Bool}
  {G.img(q, Some{y}, d) == Some{SD.item_shift(d, y)} : Maybe<&2, R.Item>}

def img_real(q, y, d, e):
  %Equal.sym(Bool, SD.is_phantom(y), False{}, e) : {G.img.k(_, q, y, d) == Some{SD.item_shift(d, y)} : Maybe<&2, R.Item>}
  {==}

law fmap_pre:
  for +q: Maybe<&2, R.Item>
  for +d: Nat
  for +s: String
  for +f: R.Flush
  {G.fmap(q, d, R.Flush.pre(s, f)) == R.Flush.pre(s, G.fmap(q, d, f)) : R.Flush}

def fmap_pre(q, d, s, f):
  match f:
    case R.Flushed{o, l}:
      {==}
    case R.Broke{o, b, p}:
      {==}

law pre_flushed:
  for +s: String
  for +f: R.Flush
  {G.is_flushed(R.Flush.pre(s, f)) == G.is_flushed(f) : Bool}

def pre_flushed(s, f):
  match f:
    case R.Flushed{o, l}:
      {==}
    case R.Broke{o, b, p}:
      {==}

def fok2.k(+ph: Bool, +q: Maybe<&2, R.Item>, +x: R.Item, +d: Nat, +y: R.Item,
  hq: {G.qok.k(ph, q, x) == True{} : Bool}, hy: {Nat.is_le(R.Item.key(x), R.Item.key(y)) == True{} : Bool}) ->
  {R.flush.ok(G.img.k(ph, q, x, d), R.Item.key(y)) == True{} : Bool}:
  match ph:
    case True{}:
      %Equal.sym(Bool, R.flush.ok(q, R.Item.key(y)), Nat.is_le(S.lkey(q), R.Item.key(y)), S.ok_lkey(q, R.Item.key(y))) : {_ == True{} : Bool}
      Q.le_trans(S.lkey(q), R.Item.key(x), R.Item.key(y), hq, hy)
    case False{}:
      %Equal.sym(Nat, R.Item.key(SD.item_shift(d, x)), R.Item.key(x), key_sh(d, x)) : {Nat.is_le(_, R.Item.key(y)) == True{} : Bool}
      hy

# X's check passes where Y's does: the phantom stands for an item no higher.
law fok2:
  for +q: Maybe<&2, R.Item>
  for +ly: Maybe<&2, R.Item>
  for +d: Nat
  for +y: R.Item
  for hq: {G.qok(q, ly) == True{} : Bool}
  for hy: {R.flush.ok(ly, R.Item.key(y)) == True{} : Bool}
  {R.flush.ok(G.img(q, ly, d), R.Item.key(SD.item_shift(d, y))) == True{} : Bool}

def fok2(q, ly, d, y, hq, hy):
  match ly:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Nat, R.Item.key(SD.item_shift(d, y)), R.Item.key(y), key_sh(d, y)) : {R.flush.ok(G.img(q, Some{x}, d), _) == True{} : Bool}
      fok2.k(SD.is_phantom(x), q, x, d, y, hq, hy)

def fl2.go(+ys: List<&2, R.Item>, +y: R.Item, +t: List<&2, R.Item>, +ly: Maybe<&2, R.Item>, +q: Maybe<&2, R.Item>, +d: Nat, +g: Bool,
  eg: {R.flush.ok(ly, R.Item.key(y)) == g : Bool},
  hq: {G.qok(q, ly) == True{} : Bool},
  hr: {SD.is_phantom(y) == False{} : Bool},
  hf: {G.is_flushed(R.flush.put(g, y, ly, R.flush(t, Some{y}))) == True{} : Bool},
  ih: {G.is_flushed(R.flush(t, Some{y})) == True{} : Bool} -> {R.flush(SD.items_shift(d, t), G.img(q, Some{y}, d)) == G.fmap(q, d, R.flush(t, Some{y})) : R.Flush}) ->
  {R.flush.put(R.flush.ok(G.img(q, ly, d), R.Item.key(SD.item_shift(d, y))), SD.item_shift(d, y), G.img(q, ly, d), R.flush(SD.items_shift(d, t), Some{SD.item_shift(d, y)}))
    == G.fmap(q, d, R.flush.put(g, y, ly, R.flush(t, Some{y}))) : R.Flush}:
  match g:
    case False{}:
      Empty.absurd({R.flush.put(R.flush.ok(G.img(q, ly, d), R.Item.key(SD.item_shift(d, y))), SD.item_shift(d, y), G.img(q, ly, d), R.flush(SD.items_shift(d, t), Some{SD.item_shift(d, y)}))
        == G.fmap(q, d, R.flush.put(False{}, y, ly, R.flush(t, Some{y}))) : R.Flush}, P.false_ne_true(hf))
    case True{}:
      +ok = fok2(q, ly, d, y, hq, eg)
      %Equal.sym(Bool, R.flush.ok(G.img(q, ly, d), R.Item.key(SD.item_shift(d, y))), True{}, ok) :
        {R.flush.put(_, SD.item_shift(d, y), G.img(q, ly, d), R.flush(SD.items_shift(d, t), Some{SD.item_shift(d, y)}))
          == G.fmap(q, d, R.flush.put(True{}, y, ly, R.flush(t, Some{y}))) : R.Flush}
      %Equal.sym(R.Flush, G.fmap(q, d, R.Flush.pre(R.Item.text(y), R.flush(t, Some{y}))), R.Flush.pre(R.Item.text(y), G.fmap(q, d, R.flush(t, Some{y}))), fmap_pre(q, d, R.Item.text(y), R.flush(t, Some{y}))) :
        {R.Flush.pre(R.Item.text(SD.item_shift(d, y)), R.flush(SD.items_shift(d, t), Some{SD.item_shift(d, y)})) == _ : R.Flush}
      +hf2 = Equal.trans(Bool, G.is_flushed(R.flush(t, Some{y})), G.is_flushed(R.Flush.pre(R.Item.text(y), R.flush(t, Some{y}))), True{},
        Equal.sym(Bool, G.is_flushed(R.Flush.pre(R.Item.text(y), R.flush(t, Some{y}))), G.is_flushed(R.flush(t, Some{y})), pre_flushed(R.Item.text(y), R.flush(t, Some{y}))), hf)
      %ih(hf2) :
        {R.Flush.pre(R.Item.text(SD.item_shift(d, y)), R.flush(SD.items_shift(d, t), Some{SD.item_shift(d, y)})) == R.Flush.pre(R.Item.text(y), _) : R.Flush}
      %img_real(q, y, d, hr) :
        {R.Flush.pre(R.Item.text(SD.item_shift(d, y)), R.flush(SD.items_shift(d, t), _)) == R.Flush.pre(R.Item.text(y), R.flush(SD.items_shift(d, t), G.img(q, Some{y}, d))) : R.Flush}
      %text_sh(d, y) :
        {R.Flush.pre(R.Item.text(SD.item_shift(d, y)), R.flush(SD.items_shift(d, t), G.img(q, Some{y}, d))) == R.Flush.pre(_, R.flush(SD.items_shift(d, t), G.img(q, Some{y}, d))) : R.Flush}
      {==}

# Y's flush passes, so X's does, with the same output and the image of its last.
law fl2:
  for +ys: List<&2, R.Item>
  for +ly: Maybe<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +d: Nat
  for +ha: {G.allreal(ys) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  for +hf: {G.is_flushed(R.flush(ys, ly)) == True{} : Bool}
  {R.flush(SD.items_shift(d, ys), G.img(q, ly, d)) == G.fmap(q, d, R.flush(ys, ly)) : R.Flush}

def fl2(ys, ly, q, d, ha, hq, hf):
  match ys:
    case Nil{}:
      {==}
    case +y <> +t:
      +hr = real_hd(y, t, ha)
      +ht = real_tl(y, t, ha)
      fl2.go(y <> t, y, t, ly, q, d, R.flush.ok(ly, R.Item.key(y)), {==}, hq, hr, hf,
        hf2 => fl2(t, Some{y}, q, d, ht, qok_real(q, y, hr), hf2))

law qok_flast:
  for +ys: List<&2, R.Item>
  for +ly: Maybe<&2, R.Item>
  for +q: Maybe<&2, R.Item>
  for +ha: {G.allreal(ys) == True{} : Bool}
  for +hq: {G.qok(q, ly) == True{} : Bool}
  {G.qok(q, S.flast(ys, ly)) == True{} : Bool}

def qok_flast(ys, ly, q, ha, hq):
  match ys:
    case Nil{}:
      hq
    case +y <> +t:
      qok_flast(t, Some{y}, q, real_tl(y, t, ha), qok_real(q, y, real_hd(y, t, ha)))

# allreal
# =======

law allreal_l:
  for +a: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +h: {G.allreal(S.app(a, b)) == True{} : Bool}
  {G.allreal(a) == True{} : Bool}

def allreal_l(a, b, h):
  match a:
    case Nil{}:
      {==}
    case +x <> +t:
      S.and_intro(Bool.not(SD.is_phantom(x)), G.allreal(t), P.and_true_l(Bool.not(SD.is_phantom(x)), G.allreal(S.app(t, b)), h),
        allreal_l(t, b, P.and_true_r(Bool.not(SD.is_phantom(x)), G.allreal(S.app(t, b)), h)))

law allreal_r:
  for +a: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +h: {G.allreal(S.app(a, b)) == True{} : Bool}
  {G.allreal(b) == True{} : Bool}

def allreal_r(a, b, h):
  match a:
    case Nil{}:
      h
    case +x <> +t:
      allreal_r(t, b, P.and_true_r(Bool.not(SD.is_phantom(x)), G.allreal(S.app(t, b)), h))

def allreal_ins.go(+e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +g: Bool,
  he: {SD.is_phantom(e) == False{} : Bool}, hb: {G.allreal(x <> t) == True{} : Bool},
  ih: {G.allreal(R.insert(e, t)) == True{} : Bool}) ->
  {G.allreal(R.insert.put(g, x, e, t, R.insert(e, t))) == True{} : Bool}:
  match g:
    case True{}:
      S.and_intro(Bool.not(SD.is_phantom(x)), G.allreal(R.insert(e, t)), notph(x, real_hd(x, t, hb)), ih)
    case False{}:
      S.and_intro(Bool.not(SD.is_phantom(e)), G.allreal(x <> t), notph(e, he), hb)

law allreal_ins:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +he: {SD.is_phantom(e) == False{} : Bool}
  for +hb: {G.allreal(b) == True{} : Bool}
  {G.allreal(R.insert(e, b)) == True{} : Bool}

def allreal_ins(e, b, he, hb):
  match b:
    case Nil{}:
      S.and_intro(Bool.not(SD.is_phantom(e)), True{}, notph(e, he), {==})
    case +x <> +t:
      allreal_ins.go(e, x, t, Nat.is_le(R.Item.key(x), R.Item.key(e)), he, hb, allreal_ins(e, t, he, real_tl(x, t, hb)))

law allreal_td:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for +hb: {G.allreal(b) == True{} : Bool}
  {G.allreal(S.app(R.take_ready(w, p, b), R.drop_ready(w, p, b))) == True{} : Bool}

def allreal_td(w, p, b, hb):
  %Equal.sym(List<&2, R.Item>, S.app(R.take_ready(w, p, b), R.drop_ready(w, p, b)), b, S.take_drop(w, p, b)) : {G.allreal(_) == True{} : Bool}
  hb

law allreal_tr:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for +hb: {G.allreal(b) == True{} : Bool}
  {G.allreal(R.take_ready(w, p, b)) == True{} : Bool}

def allreal_tr(w, p, b, hb):
  allreal_l(R.take_ready(w, p, b), R.drop_ready(w, p, b), allreal_td(w, p, b, hb))

law allreal_dr:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for +hb: {G.allreal(b) == True{} : Bool}
  {G.allreal(R.drop_ready(w, p, b)) == True{} : Bool}

def allreal_dr(w, p, b, hb):
  allreal_r(R.take_ready(w, p, b), R.drop_ready(w, p, b), allreal_td(w, p, b, hb))

# keys_ge
# =======

law kge_l:
  for +a: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +l: Nat
  for +h: {SD.keys_ge(S.app(a, b), l) == True{} : Bool}
  {SD.keys_ge(a, l) == True{} : Bool}

def kge_l(a, b, l, h):
  match a:
    case Nil{}:
      {==}
    case +x <> +t:
      S.and_intro(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(t, l), P.and_true_l(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(S.app(t, b), l), h),
        kge_l(t, b, l, P.and_true_r(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(S.app(t, b), l), h)))

law kge_r:
  for +a: List<&2, R.Item>
  for +b: List<&2, R.Item>
  for +l: Nat
  for +h: {SD.keys_ge(S.app(a, b), l) == True{} : Bool}
  {SD.keys_ge(b, l) == True{} : Bool}

def kge_r(a, b, l, h):
  match a:
    case Nil{}:
      h
    case +x <> +t:
      kge_r(t, b, l, P.and_true_r(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(S.app(t, b), l), h))

def kge_ins.go(+e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +l: Nat, +g: Bool,
  he: {Nat.is_le(l, R.Item.key(e)) == True{} : Bool}, hb: {SD.keys_ge(x <> t, l) == True{} : Bool},
  ih: {SD.keys_ge(R.insert(e, t), l) == True{} : Bool}) ->
  {SD.keys_ge(R.insert.put(g, x, e, t, R.insert(e, t)), l) == True{} : Bool}:
  match g:
    case True{}:
      S.and_intro(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(R.insert(e, t), l), P.and_true_l(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(t, l), hb), ih)
    case False{}:
      S.and_intro(Nat.is_le(l, R.Item.key(e)), SD.keys_ge(x <> t, l), he, hb)

law kge_ins:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +l: Nat
  for +he: {Nat.is_le(l, R.Item.key(e)) == True{} : Bool}
  for +hb: {SD.keys_ge(b, l) == True{} : Bool}
  {SD.keys_ge(R.insert(e, b), l) == True{} : Bool}

def kge_ins(e, b, l, he, hb):
  match b:
    case Nil{}:
      S.and_intro(Nat.is_le(l, R.Item.key(e)), True{}, he, {==})
    case +x <> +t:
      kge_ins.go(e, x, t, l, Nat.is_le(R.Item.key(x), R.Item.key(e)), he, hb,
        kge_ins(e, t, l, he, P.and_true_r(Nat.is_le(l, R.Item.key(x)), SD.keys_ge(t, l), hb)))

law kge_dr:
  for +w: Nat
  for +p: Nat
  for +b: List<&2, R.Item>
  for +l: Nat
  for +hb: {SD.keys_ge(b, l) == True{} : Bool}
  {SD.keys_ge(R.drop_ready(w, p, b), l) == True{} : Bool}

def kge_dr(w, p, b, l, hb):
  +h2 = Equal.trans(Bool, SD.keys_ge(S.app(R.take_ready(w, p, b), R.drop_ready(w, p, b)), l), SD.keys_ge(b, l), True{},
    Equal.cong(List<&2, R.Item>, Bool, xs => SD.keys_ge(xs, l), S.app(R.take_ready(w, p, b), R.drop_ready(w, p, b)), b, S.take_drop(w, p, b)), hb)
  kge_r(R.take_ready(w, p, b), R.drop_ready(w, p, b), l, h2)

# all_lt
# ======

def alt_ins.go(+e: R.Item, +x: R.Item, +t: List<&2, R.Item>, +m: Nat, +g: Bool,
  he: {Nat.is_lt(R.Item.inpos(e), m) == True{} : Bool}, hb: {G.all_lt(x <> t, m) == True{} : Bool},
  ih: {G.all_lt(R.insert(e, t), m) == True{} : Bool}) ->
  {G.all_lt(R.insert.put(g, x, e, t, R.insert(e, t)), m) == True{} : Bool}:
  match g:
    case True{}:
      S.and_intro(Nat.is_lt(R.Item.inpos(x), m), G.all_lt(R.insert(e, t), m), P.and_true_l(Nat.is_lt(R.Item.inpos(x), m), G.all_lt(t, m), hb), ih)
    case False{}:
      S.and_intro(Nat.is_lt(R.Item.inpos(e), m), G.all_lt(x <> t, m), he, hb)

law alt_ins:
  for +e: R.Item
  for +b: List<&2, R.Item>
  for +m: Nat
  for +he: {Nat.is_lt(R.Item.inpos(e), m) == True{} : Bool}
  for +hb: {G.all_lt(b, m) == True{} : Bool}
  {G.all_lt(R.insert(e, b), m) == True{} : Bool}

def alt_ins(e, b, m, he, hb):
  match b:
    case Nil{}:
      S.and_intro(Nat.is_lt(R.Item.inpos(e), m), True{}, he, {==})
    case +x <> +t:
      alt_ins.go(e, x, t, m, Nat.is_le(R.Item.key(x), R.Item.key(e)), he, hb,
        alt_ins(e, t, m, he, P.and_true_r(Nat.is_lt(R.Item.inpos(x), m), G.all_lt(t, m), hb)))

# counts
# ======

law cnt_bump:
  for +sk: R.Cnt
  for +k: R.Cnt
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {SD.cnt_add(sk, R.bump(k, a, b, c)) == R.bump(SD.cnt_add(sk, k), a, b, c) : R.Cnt}

def cnt_bump(sk, k, a, b, c):
  match sk k:
    case R.Cnt{+s1, +s2, +s3, +s4} R.Cnt{+k1, +k2, +k3, +k4}:
      +x2 = Bool.pick(Nat, a, 1n, 0n)
      +x3 = Bool.pick(Nat, b, 1n, 0n)
      +x4 = Bool.pick(Nat, c, 1n, 0n)
      %P.add_succ(s1, k1) : {R.Cnt{Nat.add(s1, 1n+k1), Nat.add(s2, Nat.add(k2, x2)), Nat.add(s3, Nat.add(k3, x3)), Nat.add(s4, Nat.add(k4, x4))}
        == R.Cnt{_, Nat.add(Nat.add(s2, k2), x2), Nat.add(Nat.add(s3, k3), x3), Nat.add(Nat.add(s4, k4), x4)} : R.Cnt}
      %P.add_assoc(s2, k2, x2) : {R.Cnt{Nat.add(s1, 1n+k1), _, Nat.add(s3, Nat.add(k3, x3)), Nat.add(s4, Nat.add(k4, x4))}
        == R.Cnt{Nat.add(s1, 1n+k1), Nat.add(Nat.add(s2, k2), x2), Nat.add(Nat.add(s3, k3), x3), Nat.add(Nat.add(s4, k4), x4)} : R.Cnt}
      %P.add_assoc(s3, k3, x3) : {R.Cnt{Nat.add(s1, 1n+k1), Nat.add(Nat.add(s2, k2), x2), _, Nat.add(s4, Nat.add(k4, x4))}
        == R.Cnt{Nat.add(s1, 1n+k1), Nat.add(Nat.add(s2, k2), x2), Nat.add(Nat.add(s3, k3), x3), Nat.add(Nat.add(s4, k4), x4)} : R.Cnt}
      %P.add_assoc(s4, k4, x4) : {R.Cnt{Nat.add(s1, 1n+k1), Nat.add(Nat.add(s2, k2), x2), Nat.add(Nat.add(s3, k3), x3), _}
        == R.Cnt{Nat.add(s1, 1n+k1), Nat.add(Nat.add(s2, k2), x2), Nat.add(Nat.add(s3, k3), x3), Nat.add(Nat.add(s4, k4), x4)} : R.Cnt}
      {==}

law cnt_zero:
  for +sk: R.Cnt
  {SD.cnt_add(sk, R.Cnt{0n, 0n, 0n, 0n}) == sk : R.Cnt}

def cnt_zero(sk):
  match sk:
    case R.Cnt{+s1, +s2, +s3, +s4}:
      %P.add_zero(s1) : {R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), Nat.add(s3, 0n), Nat.add(s4, 0n)} == R.Cnt{_, s2, s3, s4} : R.Cnt}
      %P.add_zero(s2) : {R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), Nat.add(s3, 0n), Nat.add(s4, 0n)} == R.Cnt{Nat.add(s1, 0n), _, s3, s4} : R.Cnt}
      %P.add_zero(s3) : {R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), Nat.add(s3, 0n), Nat.add(s4, 0n)} == R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), _, s4} : R.Cnt}
      %P.add_zero(s4) : {R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), Nat.add(s3, 0n), Nat.add(s4, 0n)} == R.Cnt{Nat.add(s1, 0n), Nat.add(s2, 0n), Nat.add(s3, 0n), _} : R.Cnt}
      {==}
