import Base
import ./run.bend as R
import ./norm_run.bend as NR
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-bytes/proof_core.bend as C
import ./proof_b_rundefs.bend as RD

# norm_run.bend's insert against run.bend's R.insert, on the spec items
# (NR.spec.items), independent of RunInv. ins.start(xs, k) splits xs into
# pre (the items whose keys are at most k, from the front) and rest, with
# plen the bytes of pre; the item goes between them (NR.mid), or at the end
# of the buffer when every key is at most its own (NR.at_end). R.insert puts
# it after every item whose key is at most its own: the same place.

# The bytes of a list of items, as Nat (the head's last, as ins.cons adds).
def nlen(xs: List<&2, NR.Ck>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +c <> t:
      Nat.add(nlen(t), U32.to_nat(NR.Ck.len(c)))

def ipre(i: NR.Ins) -> List<&2, NR.Ck>:
  match i:
    case NR.Ins{p, n, r}:
      p

def iplen(i: NR.Ins) -> U32:
  match i:
    case NR.Ins{p, n, r}:
      n

def irest(i: NR.Ins) -> List<&2, NR.Ck>:
  match i:
    case NR.Ins{p, n, r}:
      r

# Every key at most k.
def allle(xs: List<&2, NR.Ck>, +k: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +c <> t:
      Nat.is_le(NR.Ck.key(c), k) && allle(t, k)

# Strings
# =======

def s_take0(+s: String) -> {String.take(s, 0n) == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def s_drop0(+s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def s_take_app(+a: String, +b: String, +n: Nat, +h: {Nat.is_le(n, String.length(a)) == True{} : Bool}) ->
  {String.take(String.append(a, b), n) == String.take(a, n) : String}:
  match a n:
    case SNil{} 0n:
      s_take0(b)
    case SNil{} 1n+p:
      Empty.absurd({String.take(b, 1n+p) == "" : String}, AB.false_ne_true(h))
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      %s_take_app(t, b, p, h) : {SCon{c, String.take(String.append(t, b), p)} == SCon{c, _} : String}
      {==}

def s_drop_app(+a: String, +b: String, +n: Nat, +h: {Nat.is_le(n, String.length(a)) == True{} : Bool}) ->
  {String.drop(String.append(a, b), n) == String.append(String.drop(a, n), b) : String}:
  match a n:
    case SNil{} 0n:
      s_drop0(b)
    case SNil{} 1n+p:
      Empty.absurd({String.drop(b, 1n+p) == b : String}, AB.false_ne_true(h))
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      s_drop_app(t, b, p, h)

def s_take_len(+s: String) -> {String.take(s, String.length(s)) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %s_take_len(t) : {SCon{c, String.take(t, String.length(t))} == SCon{c, _} : String}
      {==}

def s_drop_len(+s: String) -> {String.drop(s, String.length(s)) == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      s_drop_len(t)

def s_len_take(+s: String, +n: Nat, +h: {Nat.is_le(n, String.length(s)) == True{} : Bool}) ->
  {String.length(String.take(s, n)) == n : Nat}:
  match s n:
    case SNil{} 0n:
      {==}
    case SNil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, AB.false_ne_true(h))
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      %s_len_take(t, p, h) : {1n+String.length(String.take(t, p)) == 1n+_ : Nat}
      {==}

def s_take_idem(+s: String, +a: Nat) -> {String.take(String.take(s, a), a) == String.take(s, a) : String}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      %s_take_idem(t, p) : {SCon{c, String.take(String.take(t, p), p)} == SCon{c, _} : String}
      {==}

def s_take_take(+s: String, +a: Nat, +b: Nat) ->
  {String.take(String.take(s, Nat.add(a, b)), a) == String.take(s, a) : String}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      s_take0(String.take(SCon{c, t}, b))
    case SCon{+c, +t} 1n+p:
      %s_take_take(t, p, b) : {SCon{c, String.take(String.take(t, Nat.add(p, b)), p)} == SCon{c, _} : String}
      {==}

def s_drop_take(+s: String, +a: Nat, +b: Nat) ->
  {String.drop(String.take(s, Nat.add(a, b)), a) == String.take(String.drop(s, a), b) : String}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      s_drop0(String.take(SCon{c, t}, b))
    case SCon{+c, +t} 1n+p:
      s_drop_take(t, p, b)

def s_drop_drop(+s: String, +a: Nat, +b: Nat) ->
  {String.drop(s, Nat.add(a, b)) == String.drop(String.drop(s, a), b) : String}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      s_drop_drop(t, p, b)

def s_len_drop(+s: String, +n: Nat) -> {String.length(String.drop(s, n)) == Nat.sub(String.length(s), n) : Nat}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{+c, +t} 0n:
      {==}
    case SCon{+c, +t} 1n+p:
      s_len_drop(t, p)

# The split (lists and sizes)
# ===========================

def cons_eta(+y: NR.Ck, +i: NR.Ins) ->
  {NR.ins.cons(y, i) == NR.Ins{y <> ipre(i), (iplen(i) + NR.Ck.len(y) : U32), irest(i)} : NR.Ins}:
  match i:
    case NR.Ins{+p, +n, +r}:
      {==}

def append_cons(+y: NR.Ck, +xs: List<&2, NR.Ck>, +ys: List<&2, NR.Ck>) ->
  {NR.append_ck(y <> xs, ys) == y <> NR.append_ck(xs, ys) : List<&2, NR.Ck>}:
  {==}

# pre then rest is the list.
def go_cat(+t: List<&2, NR.Ck>, +z: Bool, +y: NR.Ck, +k: Nat) ->
  {NR.append_ck(ipre(NR.ins.go(t, z, y, k)), irest(NR.ins.go(t, z, y, k))) == y <> t : List<&2, NR.Ck>}:
  match t z:
    case _ False{}:
      {==}
    case Nil{} True{}:
      {==}
    case +w <> +t2 True{}:
      +G = NR.ins.go(t2, Nat.is_le(NR.Ck.key(w), k), w, k)
      %Equal.sym(NR.Ins, NR.ins.cons(y, G), NR.Ins{y <> ipre(G), (iplen(G) + NR.Ck.len(y) : U32), irest(G)}, cons_eta(y, G)) :
        {NR.append_ck(ipre(_), irest(_)) == y <> w <> t2 : List<&2, NR.Ck>}
      %go_cat(t2, Nat.is_le(NR.Ck.key(w), k), w, k) : {y <> NR.append_ck(ipre(G), irest(G)) == y <> _ : List<&2, NR.Ck>}
      {==}

# pre's bytes are at most the list's.
def go_le(+t: List<&2, NR.Ck>, +z: Bool, +y: NR.Ck, +k: Nat) ->
  {Nat.is_le(nlen(ipre(NR.ins.go(t, z, y, k))), nlen(y <> t)) == True{} : Bool}:
  match t z:
    case _ False{}:
      N.le_zero_l(nlen(y <> t))
    case Nil{} True{}:
      N.le_refl(nlen([y]))
    case +w <> +t2 True{}:
      +G = NR.ins.go(t2, Nat.is_le(NR.Ck.key(w), k), w, k)
      %Equal.sym(NR.Ins, NR.ins.cons(y, G), NR.Ins{y <> ipre(G), (iplen(G) + NR.Ck.len(y) : U32), irest(G)}, cons_eta(y, G)) :
        {Nat.is_le(nlen(ipre(_)), nlen(y <> w <> t2)) == True{} : Bool}
      N.le_add_mono_r(U32.to_nat(NR.Ck.len(y)), nlen(ipre(G)), nlen(w <> t2), go_le(t2, Nat.is_le(NR.Ck.key(w), k), w, k))

def nlen_cons(+y: NR.Ck, +t: List<&2, NR.Ck>) -> {nlen(y <> t) == Nat.add(nlen(t), U32.to_nat(NR.Ck.len(y))) : Nat}:
  {==}

# plen is pre's bytes, when the list's bytes are below 2^32.
def go_len(+t: List<&2, NR.Ck>, +z: Bool, +y: NR.Ck, +k: Nat,
  +hw: {Nat.is_lt(nlen(y <> t), Nat.pow(2n, 32n)) == True{} : Bool}) ->
  {U32.to_nat(iplen(NR.ins.go(t, z, y, k))) == nlen(ipre(NR.ins.go(t, z, y, k))) : Nat}:
  match t z:
    case _ False{}:
      {==}
    case Nil{} True{}:
      {==}
    case +w <> +t2 True{}:
      +G = NR.ins.go(t2, Nat.is_le(NR.Ck.key(w), k), w, k)
      +ly = U32.to_nat(NR.Ck.len(y))
      +hw1 = AB.subst(Nat, v => {Nat.is_lt(v, Nat.pow(2n, 32n)) == True{} : Bool}, nlen(y <> w <> t2), Nat.add(nlen(w <> t2), ly), nlen_cons(y, w <> t2), hw)
      +hw2 = N.le_lt_trans(nlen(w <> t2), Nat.add(nlen(w <> t2), ly), Nat.pow(2n, 32n), N.le_add_r(nlen(w <> t2), ly), hw1)
      +ih = go_len(t2, Nat.is_le(NR.Ck.key(w), k), w, k, hw2)
      +hs = N.le_lt_trans(Nat.add(nlen(ipre(G)), ly), Nat.add(nlen(w <> t2), ly), Nat.pow(2n, 32n),
        N.le_add_mono_r(ly, nlen(ipre(G)), nlen(w <> t2), go_le(t2, Nat.is_le(NR.Ck.key(w), k), w, k)), hw1)
      +hs2 = AB.subst(Nat, v => {Nat.is_lt(Nat.add(v, ly), Nat.pow(2n, 32n)) == True{} : Bool}, nlen(ipre(G)), U32.to_nat(iplen(G)), Equal.sym(Nat, U32.to_nat(iplen(G)), nlen(ipre(G)), ih), hs)
      %Equal.sym(NR.Ins, NR.ins.cons(y, G), NR.Ins{y <> ipre(G), (iplen(G) + NR.Ck.len(y) : U32), irest(G)}, cons_eta(y, G)) :
        {U32.to_nat(iplen(_)) == nlen(ipre(_)) : Nat}
      %Equal.sym(Nat, U32.to_nat((iplen(G) + NR.Ck.len(y) : U32)), Nat.add(U32.to_nat(iplen(G)), ly), U.to_nat_add_fits_p(iplen(G), NR.Ck.len(y), hs2)) :
        {_ == Nat.add(nlen(ipre(G)), ly) : Nat}
      %Equal.sym(Nat, U32.to_nat(iplen(G)), nlen(ipre(G)), ih) : {Nat.add(_, ly) == Nat.add(nlen(ipre(G)), ly) : Nat}
      {==}

# The same from ins.start.
def st_cat(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {NR.append_ck(ipre(NR.ins.start(xs, k)), irest(NR.ins.start(xs, k))) == xs : List<&2, NR.Ck>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      go_cat(t, Nat.is_le(NR.Ck.key(y), k), y, k)

def st_le(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {Nat.is_le(nlen(ipre(NR.ins.start(xs, k))), nlen(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      go_le(t, Nat.is_le(NR.Ck.key(y), k), y, k)

def st_len(+xs: List<&2, NR.Ck>, +k: Nat,
  +hw: {Nat.is_lt(nlen(xs), Nat.pow(2n, 32n)) == True{} : Bool}) ->
  {U32.to_nat(iplen(NR.ins.start(xs, k))) == nlen(ipre(NR.ins.start(xs, k))) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      go_len(t, Nat.is_le(NR.Ck.key(y), k), y, k, hw)

# The split (spec items)
# ======================

def key_item(+x: NR.Ck, +chrom: String, +s: String) ->
  {R.Item.key(NR.spec.item(x, chrom, s)) == NR.Ck.key(x) : Nat}:
  match x:
    case NR.Ck{+k, +ip, +l, +p, +n}:
      {==}

# One step of R.insert on the spec items.
def ins_head(+y: NR.Ck, +rest: List<&2, NR.Ck>, +e: R.Item, +chrom: String, +T: String, +b: Bool,
  +eb: {Nat.is_le(NR.Ck.key(y), R.Item.key(e)) == b : Bool}) ->
  {R.insert(e, NR.spec.items(y <> rest, chrom, T))
    == R.insert.put(b, NR.spec.item(y, chrom, String.take(T, U32.to_nat(NR.Ck.len(y)))), e, NR.spec.items(rest, chrom, String.drop(T, U32.to_nat(NR.Ck.len(y)))), R.insert(e, NR.spec.items(rest, chrom, String.drop(T, U32.to_nat(NR.Ck.len(y)))))) : List<&2, R.Item>}:
  match y:
    case NR.Ck{+yk, +ip, +l, +p, +n}:
      +ITY = NR.spec.item(NR.Ck{yk, ip, l, p, n}, chrom, String.take(T, U32.to_nat(n)))
      +ITS = NR.spec.items(rest, chrom, String.drop(T, U32.to_nat(n)))
      %Equal.sym(Bool, Nat.is_le(yk, R.Item.key(e)), b, eb) :
        {R.insert.put(_, ITY, e, ITS, R.insert(e, ITS)) == R.insert.put(b, ITY, e, ITS, R.insert(e, ITS)) : List<&2, R.Item>}
      {==}

# R.insert puts e between pre and rest of ins.go's split.
def go_items(+t: List<&2, NR.Ck>, +z: Bool, +y: NR.Ck, +k: Nat,
  +ez: {Nat.is_le(NR.Ck.key(y), k) == z : Bool},
  +e: R.Item, +ke: {R.Item.key(e) == k : Nat}, +chrom: String, +T: String) ->
  {R.insert(e, NR.spec.items(y <> t, chrom, T))
    == List.append(&2, R.Item, NR.spec.items(ipre(NR.ins.go(t, z, y, k)), chrom, String.take(T, nlen(ipre(NR.ins.go(t, z, y, k))))),
      e <> NR.spec.items(irest(NR.ins.go(t, z, y, k)), chrom, String.drop(T, nlen(ipre(NR.ins.go(t, z, y, k)))))) : List<&2, R.Item>}:
  match t z:
    case _ False{}:
      +eb = AB.subst(Nat, v => {Nat.is_le(NR.Ck.key(y), v) == False{} : Bool}, k, R.Item.key(e), Equal.sym(Nat, R.Item.key(e), k, ke), ez)
      +ly = U32.to_nat(NR.Ck.len(y))
      +ITY = NR.spec.item(y, chrom, String.take(T, ly))
      +D = String.drop(T, ly)
      %Equal.sym(List<&2, R.Item>, R.insert(e, NR.spec.items(y <> t, chrom, T)), R.insert.put(False{}, ITY, e, NR.spec.items(t, chrom, D), R.insert(e, NR.spec.items(t, chrom, D))), ins_head(y, t, e, chrom, T, False{}, eb)) :
        {_ == e <> NR.spec.items(y <> t, chrom, String.drop(T, 0n)) : List<&2, R.Item>}
      %Equal.sym(String, String.drop(T, 0n), T, s_drop0(T)) :
        {e <> ITY <> NR.spec.items(t, chrom, D) == e <> NR.spec.items(y <> t, chrom, _) : List<&2, R.Item>}
      {==}
    case Nil{} True{}:
      +eb = AB.subst(Nat, v => {Nat.is_le(NR.Ck.key(y), v) == True{} : Bool}, k, R.Item.key(e), Equal.sym(Nat, R.Item.key(e), k, ke), ez)
      +ly = U32.to_nat(NR.Ck.len(y))
      +ITY = NR.spec.item(y, chrom, String.take(T, ly))
      +D = String.drop(T, ly)
      %Equal.sym(List<&2, R.Item>, R.insert(e, NR.spec.items([y], chrom, T)), R.insert.put(True{}, ITY, e, NR.spec.items(Nil{}, chrom, D), R.insert(e, NR.spec.items(Nil{}, chrom, D))), ins_head(y, Nil{}, e, chrom, T, True{}, eb)) :
        {_ == [NR.spec.item(y, chrom, String.take(String.take(T, ly), ly)), e] : List<&2, R.Item>}
      %Equal.sym(String, String.take(String.take(T, ly), ly), String.take(T, ly), s_take_idem(T, ly)) :
        {[ITY, e] == [NR.spec.item(y, chrom, _), e] : List<&2, R.Item>}
      {==}
    case +w <> +t2 True{}:
      +eb = AB.subst(Nat, v => {Nat.is_le(NR.Ck.key(y), v) == True{} : Bool}, k, R.Item.key(e), Equal.sym(Nat, R.Item.key(e), k, ke), ez)
      +ly = U32.to_nat(NR.Ck.len(y))
      +ITY = NR.spec.item(y, chrom, String.take(T, ly))
      +D = String.drop(T, ly)
      +G2 = NR.ins.go(t2, Nat.is_le(NR.Ck.key(w), k), w, k)
      +P = ipre(G2)
      +Q = irest(G2)
      +m = nlen(P)
      +ITS = NR.spec.items(w <> t2, chrom, D)
      +LHS = R.insert(e, NR.spec.items(y <> w <> t2, chrom, T))
      +APP = List.append(&2, R.Item, NR.spec.items(P, chrom, String.take(D, m)), e <> NR.spec.items(Q, chrom, String.drop(D, m)))
      %Equal.sym(NR.Ins, NR.ins.cons(y, G2), NR.Ins{y <> P, (iplen(G2) + NR.Ck.len(y) : U32), Q}, cons_eta(y, G2)) :
        {LHS == List.append(&2, R.Item, NR.spec.items(ipre(_), chrom, String.take(T, nlen(ipre(_)))), e <> NR.spec.items(irest(_), chrom, String.drop(T, nlen(ipre(_))))) : List<&2, R.Item>}
      %N.add_comm(ly, m) :
        {LHS == List.append(&2, R.Item, NR.spec.items(y <> P, chrom, String.take(T, _)), e <> NR.spec.items(Q, chrom, String.drop(T, _))) : List<&2, R.Item>}
      %Equal.sym(String, String.take(String.take(T, Nat.add(ly, m)), ly), String.take(T, ly), s_take_take(T, ly, m)) :
        {LHS == List.append(&2, R.Item, NR.spec.item(y, chrom, _) <> NR.spec.items(P, chrom, String.drop(String.take(T, Nat.add(ly, m)), ly)), e <> NR.spec.items(Q, chrom, String.drop(T, Nat.add(ly, m)))) : List<&2, R.Item>}
      %Equal.sym(String, String.drop(String.take(T, Nat.add(ly, m)), ly), String.take(D, m), s_drop_take(T, ly, m)) :
        {LHS == List.append(&2, R.Item, ITY <> NR.spec.items(P, chrom, _), e <> NR.spec.items(Q, chrom, String.drop(T, Nat.add(ly, m)))) : List<&2, R.Item>}
      %Equal.sym(String, String.drop(T, Nat.add(ly, m)), String.drop(D, m), s_drop_drop(T, ly, m)) :
        {LHS == List.append(&2, R.Item, ITY <> NR.spec.items(P, chrom, String.take(D, m)), e <> NR.spec.items(Q, chrom, _)) : List<&2, R.Item>}
      %Equal.sym(List<&2, R.Item>, LHS, R.insert.put(True{}, ITY, e, ITS, R.insert(e, ITS)), ins_head(y, w <> t2, e, chrom, T, True{}, eb)) :
        {_ == ITY <> APP : List<&2, R.Item>}
      %Equal.sym(List<&2, R.Item>, R.insert(e, ITS), APP, go_items(t2, Nat.is_le(NR.Ck.key(w), k), w, k, {==}, e, ke, chrom, D)) :
        {R.insert.put(True{}, ITY, e, ITS, _) == ITY <> APP : List<&2, R.Item>}
      {==}

def st_items(+xs: List<&2, NR.Ck>, +k: Nat, +e: R.Item, +ke: {R.Item.key(e) == k : Nat}, +chrom: String, +T: String) ->
  {R.insert(e, NR.spec.items(xs, chrom, T))
    == List.append(&2, R.Item, NR.spec.items(ipre(NR.ins.start(xs, k)), chrom, String.take(T, nlen(ipre(NR.ins.start(xs, k))))),
      e <> NR.spec.items(irest(NR.ins.start(xs, k)), chrom, String.drop(T, nlen(ipre(NR.ins.start(xs, k)))))) : List<&2, R.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      go_items(t, Nat.is_le(NR.Ck.key(y), k), y, k, {==}, e, ke, chrom, T)

# Spec items of a concatenation
# =============================

# Items of P then Q over a text A then B, when A holds exactly P's bytes.
def items_app(+P: List<&2, NR.Ck>, +Q: List<&2, NR.Ck>, +chrom: String, +A: String, +B: String,
  +h: {nlen(P) == String.length(A) : Nat}) ->
  {NR.spec.items(NR.append_ck(P, Q), chrom, String.append(A, B)) == List.append(&2, R.Item, NR.spec.items(P, chrom, A), NR.spec.items(Q, chrom, B)) : List<&2, R.Item>}:
  match P A:
    case Nil{} SNil{}:
      {==}
    case Nil{} SCon{+a, +at}:
      Empty.absurd({NR.spec.items(Q, chrom, String.append(SCon{a, at}, B)) == NR.spec.items(Q, chrom, B) : List<&2, R.Item>},
        AB.succ_ne_zero(String.length(at), Equal.sym(Nat, 0n, 1n+String.length(at), h)))
    case +c <> +P2 _:
      +nc = U32.to_nat(NR.Ck.len(c))
      +hle = AB.subst(Nat, v => {Nat.is_le(nc, v) == True{} : Bool}, Nat.add(nlen(P2), nc), String.length(A), h, N.le_add_l(nc, nlen(P2)))
      +hd = Equal.trans(Nat, nlen(P2), Nat.sub(Nat.add(nlen(P2), nc), nc), String.length(String.drop(A, nc)),
        Equal.sym(Nat, Nat.sub(Nat.add(nlen(P2), nc), nc), nlen(P2), N.sub_add(nlen(P2), nc)),
        Equal.trans(Nat, Nat.sub(Nat.add(nlen(P2), nc), nc), Nat.sub(String.length(A), nc), String.length(String.drop(A, nc)),
          Equal.cong(Nat, Nat, v => Nat.sub(v, nc), Nat.add(nlen(P2), nc), String.length(A), h),
          Equal.sym(Nat, String.length(String.drop(A, nc)), Nat.sub(String.length(A), nc), s_len_drop(A, nc))))
      +RHS = List.append(&2, R.Item, NR.spec.items(c <> P2, chrom, A), NR.spec.items(Q, chrom, B))
      %Equal.sym(String, String.take(String.append(A, B), nc), String.take(A, nc), s_take_app(A, B, nc, hle)) :
        {NR.spec.item(c, chrom, _) <> NR.spec.items(NR.append_ck(P2, Q), chrom, String.drop(String.append(A, B), nc)) == RHS : List<&2, R.Item>}
      %Equal.sym(String, String.drop(String.append(A, B), nc), String.append(String.drop(A, nc), B), s_drop_app(A, B, nc, hle)) :
        {NR.spec.item(c, chrom, String.take(A, nc)) <> NR.spec.items(NR.append_ck(P2, Q), chrom, _) == RHS : List<&2, R.Item>}
      %Equal.sym(List<&2, R.Item>, NR.spec.items(NR.append_ck(P2, Q), chrom, String.append(String.drop(A, nc), B)),
        List.append(&2, R.Item, NR.spec.items(P2, chrom, String.drop(A, nc)), NR.spec.items(Q, chrom, B)), items_app(P2, Q, chrom, String.drop(A, nc), B, hd)) :
        {NR.spec.item(c, chrom, String.take(A, nc)) <> _ == RHS : List<&2, R.Item>}
      {==}

# The item's own text, then the rest's.
def tail_x(+x: NR.Ck, +rs: List<&2, NR.Ck>, +chrom: String, +xt: String, +D: String,
  +hx: {String.length(xt) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {NR.spec.items(x <> rs, chrom, String.append(xt, D)) == NR.spec.item(x, chrom, xt) <> NR.spec.items(rs, chrom, D) : List<&2, R.Item>}:
  +nx = U32.to_nat(NR.Ck.len(x))
  +hle = AB.subst(Nat, v => {Nat.is_le(v, String.length(xt)) == True{} : Bool}, String.length(xt), nx, hx, N.le_refl(String.length(xt)))
  +ex = Equal.cong(Nat, String, v => String.take(xt, v), nx, String.length(xt), Equal.sym(Nat, String.length(xt), nx, hx))
  +E1 = Equal.trans(String, String.take(String.append(xt, D), nx), String.take(xt, nx), xt, s_take_app(xt, D, nx, hle),
    Equal.trans(String, String.take(xt, nx), String.take(xt, String.length(xt)), xt, ex, s_take_len(xt)))
  +ed = Equal.cong(Nat, String, v => String.drop(xt, v), nx, String.length(xt), Equal.sym(Nat, String.length(xt), nx, hx))
  +E2 = Equal.trans(String, String.drop(String.append(xt, D), nx), String.append(String.drop(xt, nx), D), D, s_drop_app(xt, D, nx, hle),
    Equal.cong(String, String, v => String.append(v, D), String.drop(xt, nx), "", Equal.trans(String, String.drop(xt, nx), String.drop(xt, String.length(xt)), "", ed, s_drop_len(xt))))
  %Equal.sym(String, String.take(String.append(xt, D), nx), xt, E1) :
    {NR.spec.item(x, chrom, _) <> NR.spec.items(rs, chrom, String.drop(String.append(xt, D), nx)) == NR.spec.item(x, chrom, xt) <> NR.spec.items(rs, chrom, D) : List<&2, R.Item>}
  %Equal.sym(String, String.drop(String.append(xt, D), nx), D, E2) :
    {NR.spec.item(x, chrom, xt) <> NR.spec.items(rs, chrom, _) == NR.spec.item(x, chrom, xt) <> NR.spec.items(rs, chrom, D) : List<&2, R.Item>}
  {==}

# The results
# ===========

# NR.mid on the texts: item x (key k, text xt) put between ins.start's pre
# and rest, its text put after pre's bytes in the buffer's text T, is
# R.insert of its item (T holds at least the buffer's bytes).
def mid_core(+xs: List<&2, NR.Ck>, +k: Nat, +x: NR.Ck, +chrom: String, +T: String, +xt: String,
  +hk: {NR.Ck.key(x) == k : Nat},
  +hx: {String.length(xt) == U32.to_nat(NR.Ck.len(x)) : Nat},
  +hT: {Nat.is_le(nlen(xs), String.length(T)) == True{} : Bool}) ->
  {NR.spec.items(NR.append_ck(ipre(NR.ins.start(xs, k)), x <> irest(NR.ins.start(xs, k))), chrom,
      String.append(String.take(T, nlen(ipre(NR.ins.start(xs, k)))), String.append(xt, String.drop(T, nlen(ipre(NR.ins.start(xs, k)))))))
    == R.insert(NR.spec.item(x, chrom, xt), NR.spec.items(xs, chrom, T)) : List<&2, R.Item>}:
  +I = NR.ins.start(xs, k)
  +m = nlen(ipre(I))
  +e = NR.spec.item(x, chrom, xt)
  +hmT = N.le_trans(m, nlen(xs), String.length(T), st_le(xs, k), hT)
  +hA = Equal.sym(Nat, String.length(String.take(T, m)), m, s_len_take(T, m, hmT))
  +ke = Equal.trans(Nat, R.Item.key(e), NR.Ck.key(x), k, key_item(x, chrom, xt), hk)
  +RHS = R.insert(e, NR.spec.items(xs, chrom, T))
  %Equal.sym(List<&2, R.Item>, NR.spec.items(NR.append_ck(ipre(I), x <> irest(I)), chrom, String.append(String.take(T, m), String.append(xt, String.drop(T, m)))),
    List.append(&2, R.Item, NR.spec.items(ipre(I), chrom, String.take(T, m)), NR.spec.items(x <> irest(I), chrom, String.append(xt, String.drop(T, m)))),
    items_app(ipre(I), x <> irest(I), chrom, String.take(T, m), String.append(xt, String.drop(T, m)), hA)) :
    {_ == RHS : List<&2, R.Item>}
  %Equal.sym(List<&2, R.Item>, NR.spec.items(x <> irest(I), chrom, String.append(xt, String.drop(T, m))), e <> NR.spec.items(irest(I), chrom, String.drop(T, m)),
    tail_x(x, irest(I), chrom, xt, String.drop(T, m), hx)) :
    {List.append(&2, R.Item, NR.spec.items(ipre(I), chrom, String.take(T, m)), _) == RHS : List<&2, R.Item>}
  Equal.sym(List<&2, R.Item>, RHS, List.append(&2, R.Item, NR.spec.items(ipre(I), chrom, String.take(T, m)), e <> NR.spec.items(irest(I), chrom, String.drop(T, m))),
    st_items(xs, k, e, ke, chrom, T))

# R.insert of an item whose key is at least every key appends it.
def ins_last(+xs: List<&2, NR.Ck>, +chrom: String, +T: String, +e: R.Item,
  +h: {allle(xs, R.Item.key(e)) == True{} : Bool}) ->
  {R.insert(e, NR.spec.items(xs, chrom, T)) == List.append(&2, R.Item, NR.spec.items(xs, chrom, T), [e]) : List<&2, R.Item>}:
  match xs:
    case Nil{}:
      {==}
    case +c <> +t:
      +nc = U32.to_nat(NR.Ck.len(c))
      +D = String.drop(T, nc)
      +ITC = NR.spec.item(c, chrom, String.take(T, nc))
      +hc = AB.and_true_l(Nat.is_le(NR.Ck.key(c), R.Item.key(e)), allle(t, R.Item.key(e)), h)
      +ht = AB.and_true_r(Nat.is_le(NR.Ck.key(c), R.Item.key(e)), allle(t, R.Item.key(e)), h)
      %Equal.sym(List<&2, R.Item>, R.insert(e, NR.spec.items(c <> t, chrom, T)), R.insert.put(True{}, ITC, e, NR.spec.items(t, chrom, D), R.insert(e, NR.spec.items(t, chrom, D))), ins_head(c, t, e, chrom, T, True{}, hc)) :
        {_ == ITC <> List.append(&2, R.Item, NR.spec.items(t, chrom, D), [e]) : List<&2, R.Item>}
      %Equal.sym(List<&2, R.Item>, R.insert(e, NR.spec.items(t, chrom, D)), List.append(&2, R.Item, NR.spec.items(t, chrom, D), [e]), ins_last(t, chrom, D, e, ht)) :
        {ITC <> _ == ITC <> List.append(&2, R.Item, NR.spec.items(t, chrom, D), [e]) : List<&2, R.Item>}
      {==}

def sapp_nil(+s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %sapp_nil(t) : {SCon{c, String.append(t, "")} == SCon{c, _} : String}
      {==}

# NR.at_end: item x put after the buffer, its text after the buffer's text T
# (T holds exactly the buffer's bytes), when every key is at most x's.
def end_items(+xs: List<&2, NR.Ck>, +x: NR.Ck, +chrom: String, +T: String, +xt: String,
  +hall: {allle(xs, NR.Ck.key(x)) == True{} : Bool},
  +hT: {nlen(xs) == String.length(T) : Nat},
  +hx: {String.length(xt) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {NR.spec.items(NR.append_ck(xs, [x]), chrom, String.append(T, xt)) == R.insert(NR.spec.item(x, chrom, xt), NR.spec.items(xs, chrom, T)) : List<&2, R.Item>}:
  +e = NR.spec.item(x, chrom, xt)
  +he = AB.subst(Nat, v => {allle(xs, v) == True{} : Bool}, NR.Ck.key(x), R.Item.key(e), Equal.sym(Nat, R.Item.key(e), NR.Ck.key(x), key_item(x, chrom, xt)), hall)
  +RHS = R.insert(e, NR.spec.items(xs, chrom, T))
  %Equal.sym(List<&2, R.Item>, NR.spec.items(NR.append_ck(xs, [x]), chrom, String.append(T, xt)), List.append(&2, R.Item, NR.spec.items(xs, chrom, T), NR.spec.items([x], chrom, xt)),
    items_app(xs, [x], chrom, T, xt, hT)) :
    {_ == RHS : List<&2, R.Item>}
  %sapp_nil(xt) :
    {List.append(&2, R.Item, NR.spec.items(xs, chrom, T), NR.spec.items([x], chrom, _)) == RHS : List<&2, R.Item>}
  %Equal.sym(List<&2, R.Item>, NR.spec.items([x], chrom, String.append(xt, "")), [e], tail_x(x, Nil{}, chrom, xt, "", hx)) :
    {List.append(&2, R.Item, NR.spec.items(xs, chrom, T), _) == RHS : List<&2, R.Item>}
  Equal.sym(List<&2, R.Item>, RHS, List.append(&2, R.Item, NR.spec.items(xs, chrom, T), [e]), ins_last(xs, chrom, T, e, he))

# The buffer's order (front, then back reversed) with x pushed on the back.
def ck_assoc(+a: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +c: List<&2, NR.Ck>) ->
  {NR.append_ck(NR.append_ck(a, b), c) == NR.append_ck(a, NR.append_ck(b, c)) : List<&2, NR.Ck>}:
  match a:
    case Nil{}:
      {==}
    case +y <> +t:
      %ck_assoc(t, b, c) : {y <> NR.append_ck(NR.append_ck(t, b), c) == y <> _ : List<&2, NR.Ck>}
      {==}

def rev_app(+b: List<&2, NR.Ck>, +acc: List<&2, NR.Ck>) ->
  {NR.rev_ck(b, acc) == NR.append_ck(NR.rev_ck(b, Nil{}), acc) : List<&2, NR.Ck>}:
  match b:
    case Nil{}:
      {==}
    case +y <> +t:
      %Equal.sym(List<&2, NR.Ck>, NR.rev_ck(t, y <> acc), NR.append_ck(NR.rev_ck(t, Nil{}), y <> acc), rev_app(t, y <> acc)) :
        {_ == NR.append_ck(NR.rev_ck(t, [y]), acc) : List<&2, NR.Ck>}
      %Equal.sym(List<&2, NR.Ck>, NR.rev_ck(t, [y]), NR.append_ck(NR.rev_ck(t, Nil{}), [y]), rev_app(t, [y])) :
        {NR.append_ck(NR.rev_ck(t, Nil{}), y <> acc) == NR.append_ck(_, acc) : List<&2, NR.Ck>}
      Equal.sym(List<&2, NR.Ck>, NR.append_ck(NR.append_ck(NR.rev_ck(t, Nil{}), [y]), acc), NR.append_ck(NR.rev_ck(t, Nil{}), y <> acc), ck_assoc(NR.rev_ck(t, Nil{}), [y], acc))

def end_buf(+f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +x: NR.Ck) ->
  {NR.append_ck(f, NR.rev_ck(x <> b, Nil{})) == NR.append_ck(NR.append_ck(f, NR.rev_ck(b, Nil{})), [x]) : List<&2, NR.Ck>}:
  %Equal.sym(List<&2, NR.Ck>, NR.rev_ck(b, [x]), NR.append_ck(NR.rev_ck(b, Nil{}), [x]), rev_app(b, [x])) : {NR.append_ck(f, _) == NR.append_ck(NR.append_ck(f, NR.rev_ck(b, Nil{})), [x]) : List<&2, NR.Ck>}
  Equal.sym(List<&2, NR.Ck>, NR.append_ck(NR.append_ck(f, NR.rev_ck(b, Nil{})), [x]), NR.append_ck(f, NR.append_ck(NR.rev_ck(b, Nil{}), [x])), ck_assoc(f, NR.rev_ck(b, Nil{}), [x]))

# ---------------------------------------------------------------------------
# The statements the run area asked for (notes/bytes_proofs_run.md, "Wanted
# from pb-lines"), through RD.lens and RD.keys_le
# ---------------------------------------------------------------------------

def lens_nlen(+xs: List<&2, NR.Ck>) -> {RD.lens(xs) == nlen(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %lens_nlen(t) : {Nat.add(U32.to_nat(NR.Ck.len(c)), RD.lens(t)) == Nat.add(_, U32.to_nat(NR.Ck.len(c))) : Nat}
      N.add_comm(U32.to_nat(NR.Ck.len(c)), RD.lens(t))

def keys_allle(+xs: List<&2, NR.Ck>, +k: Nat) -> {RD.keys_le(xs, k) == allle(xs, k) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %keys_allle(t, k) : {Bool.and(Nat.is_le(NR.Ck.key(c), k), RD.keys_le(t, k)) == Bool.and(Nat.is_le(NR.Ck.key(c), k), _) : Bool}
      {==}

def eta_ins(+i: NR.Ins) -> {i == NR.Ins{ipre(i), iplen(i), irest(i)} : NR.Ins}:
  match i:
    case NR.Ins{+p, +n, +r}:
      {==}

def ins_eta(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {NR.ins.start(xs, k) == NR.Ins{ipre(NR.ins.start(xs, k)), iplen(NR.ins.start(xs, k)), irest(NR.ins.start(xs, k))} : NR.Ins}:
  eta_ins(NR.ins.start(xs, k))

def ins_split(+xs: List<&2, NR.Ck>, +k: Nat) ->
  {NR.append_ck(ipre(NR.ins.start(xs, k)), irest(NR.ins.start(xs, k))) == xs : List<&2, NR.Ck>}:
  st_cat(xs, k)

# The prefix's text length, as the word mid adds up (no wrap while xs's
# lengths fit).
def ins_plen(+xs: List<&2, NR.Ck>, +k: Nat,
  +h: {Nat.is_le(RD.lens(xs), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}) ->
  {U32.to_nat(iplen(NR.ins.start(xs, k))) == RD.lens(ipre(NR.ins.start(xs, k))) : Nat}:
  +hw = AB.subst(Nat, v => {Nat.is_lt(v, Nat.pow(2n, 32n)) == True{} : Bool}, RD.lens(xs), nlen(xs), lens_nlen(xs), C.fits_e(RD.lens(xs), 29n, 32n, {==}, h))
  Equal.trans(Nat, U32.to_nat(iplen(NR.ins.start(xs, k))), nlen(ipre(NR.ins.start(xs, k))), RD.lens(ipre(NR.ins.start(xs, k))),
    st_len(xs, k, hw), Equal.sym(Nat, RD.lens(ipre(NR.ins.start(xs, k))), nlen(ipre(NR.ins.start(xs, k))), lens_nlen(ipre(NR.ins.start(xs, k)))))

# R.insert of x's item into the items of xs is x put at the split, its text
# tx put at the prefix's text length (t holds exactly the texts of xs).
def ins_mid(+xs: List<&2, NR.Ck>, +x: NR.Ck, +chrom: String, +t: String, +tx: String,
  +ht: {String.length(t) == RD.lens(xs) : Nat},
  +hx: {String.length(tx) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t))
    == NR.spec.items(NR.append_ck(ipre(NR.ins.start(xs, NR.Ck.key(x))), x <> irest(NR.ins.start(xs, NR.Ck.key(x)))), chrom,
         String.append(String.take(t, RD.lens(ipre(NR.ins.start(xs, NR.Ck.key(x))))),
           String.append(tx, String.drop(t, RD.lens(ipre(NR.ins.start(xs, NR.Ck.key(x)))))))) : List<&2, R.Item>}:
  +k = NR.Ck.key(x)
  +P = ipre(NR.ins.start(xs, k))
  +hn = Equal.trans(Nat, nlen(xs), RD.lens(xs), String.length(t), Equal.sym(Nat, RD.lens(xs), nlen(xs), lens_nlen(xs)), Equal.sym(Nat, String.length(t), RD.lens(xs), ht))
  +hT = AB.subst(Nat, v => {Nat.is_le(nlen(xs), v) == True{} : Bool}, nlen(xs), String.length(t), hn, N.le_refl(nlen(xs)))
  %Equal.sym(Nat, RD.lens(P), nlen(P), lens_nlen(P)) :
    {R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t))
      == NR.spec.items(NR.append_ck(P, x <> irest(NR.ins.start(xs, k))), chrom, String.append(String.take(t, _), String.append(tx, String.drop(t, _)))) : List<&2, R.Item>}
  Equal.sym(List<&2, R.Item>,
    NR.spec.items(NR.append_ck(P, x <> irest(NR.ins.start(xs, k))), chrom, String.append(String.take(t, nlen(P)), String.append(tx, String.drop(t, nlen(P))))),
    R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t)),
    mid_core(xs, k, x, chrom, t, tx, {==}, hx, hT))

# At the end: every key of xs is at most x's.
def ins_end(+xs: List<&2, NR.Ck>, +x: NR.Ck, +chrom: String, +t: String, +tx: String,
  +hk: {RD.keys_le(xs, NR.Ck.key(x)) == True{} : Bool},
  +ht: {String.length(t) == RD.lens(xs) : Nat},
  +hx: {String.length(tx) == U32.to_nat(NR.Ck.len(x)) : Nat}) ->
  {R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t))
    == NR.spec.items(NR.append_ck(xs, [x]), chrom, String.append(t, tx)) : List<&2, R.Item>}:
  +hall = Equal.trans(Bool, allle(xs, NR.Ck.key(x)), RD.keys_le(xs, NR.Ck.key(x)), True{}, Equal.sym(Bool, RD.keys_le(xs, NR.Ck.key(x)), allle(xs, NR.Ck.key(x)), keys_allle(xs, NR.Ck.key(x))), hk)
  +hT = Equal.trans(Nat, nlen(xs), RD.lens(xs), String.length(t), Equal.sym(Nat, RD.lens(xs), nlen(xs), lens_nlen(xs)), Equal.sym(Nat, String.length(t), RD.lens(xs), ht))
  Equal.sym(List<&2, R.Item>, NR.spec.items(NR.append_ck(xs, [x]), chrom, String.append(t, tx)), R.insert(NR.spec.item(x, chrom, tx), NR.spec.items(xs, chrom, t)),
    end_items(xs, x, chrom, t, tx, hall, hT, hx))
