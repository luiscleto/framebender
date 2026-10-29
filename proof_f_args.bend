import Base
import ./types.bend as B
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./proof_base.bend as PB
import ../lawful-words/proof_nat.bend as N

# Phases F and H: the command-line parser (types.bend's Args) with --threads
# and the output options. The parser records the arguments it keeps (keep)
# and reads the driver's options (drv: the thread count, -o and -O). This file
# proves:
# - kl_go, ab_go: the recorded arguments are no longer, in args_len, than the
#   arguments read, and are bytes when those are (for the budget and the
#   driver's start, proof_b_bud_start.bend and proof_b_drive_start.bend);
# - parse_thr: --threads N where no option waits for its value changes nothing
#   Args.parse returns (for law threads, proof_f_threads.bend);
# - threads_parsed, threads_range: Args.threads gives Some{n} only for a line
#   Args.parse accepts, and then 1 <= n <= Args.max_threads().
# Note: && associates to the left (a && b && c is (a && b) && c).

def keep(st: B.ArgSt) -> List<&2, String>:
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      k

def kl(st: B.ArgSt) -> Nat:
  M.args_len(keep(st))

def kx(k: List<&2, String>, x: String) -> List<&2, String>:
  List.append(&2, String, k, [x])

# The state with no driver options (no thread count, no output options).
def unthr(st: B.ArgSt) -> B.ArgSt:
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      B.ArgSt{p, s, w, B.Drv.none(), r, v, ok, k}

# Args.word's branches, from the last one up (Args.word(x, st) unfolds to w1).
def w8(+x: String, s: Bool, w: Maybe<&2, Nat>, t: B.Drv, r: Maybe<&2, String>, +v: Maybe<&2, String>, ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  B.ArgSt{B.PNone{}, s, w, t, r, Some{x}, ok && Bool.not(String.starts_with(x, "-") && Nat.is_lt(1n, String.length(x))) && Maybe.is_none(&2, String, v), kx(k, x)}

def w7(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}), w8(x, s, w, t, r, v, ok, k))

def w6(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, w7(x, s, w, t, r, v, ok, k))

def w5(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, w6(x, s, w, t, r, v, ok, k))

def w4(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, w5(x, s, w, t, r, v, ok, k))

def w3(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)}, w4(x, s, w, t, r, v, ok, k))

def w2(+x: String, +s: Bool, +w: Maybe<&2, Nat>, +t: B.Drv, +r: Maybe<&2, String>, +v: Maybe<&2, String>, +ok: Bool, +k: List<&2, String>) -> B.ArgSt:
  Bool.pick(B.ArgSt, String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, kx(k, x)}, w3(x, s, w, t, r, v, ok, k))

# ---------------------------------------------------------------------------
# Lists and Bools
# ---------------------------------------------------------------------------

law al_snoc:
  for +k: List<&2, String>
  for +x: String
  {M.args_len(kx(k, x)) == Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)) : Nat}

def al_snoc(k, x):
  match k:
    case Nil{}:
      N.add_zero(Nat.add(String.length(x), 1n))
    case h <> t:
      %Equal.sym(Nat, M.args_len(kx(t, x)), Nat.add(M.args_len(t), Nat.add(String.length(x), 1n)), al_snoc(t, x)) :
        {Nat.add(Nat.add(String.length(h), 1n), _) == Nat.add(Nat.add(Nat.add(String.length(h), 1n), M.args_len(t)), Nat.add(String.length(x), 1n)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Nat.add(String.length(h), 1n), M.args_len(t)), Nat.add(String.length(x), 1n)),
        Nat.add(Nat.add(String.length(h), 1n), Nat.add(M.args_len(t), Nat.add(String.length(x), 1n))),
        N.add_assoc(Nat.add(String.length(h), 1n), M.args_len(t), Nat.add(String.length(x), 1n)))

law snoc_le:
  for +k: List<&2, String>
  for +x: String
  {Nat.is_le(M.args_len(kx(k, x)), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n))) == True{} : Bool}

def snoc_le(k, x):
  %Equal.sym(Nat, M.args_len(kx(k, x)), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), al_snoc(k, x)) :
    {Nat.is_le(_, Nat.add(M.args_len(k), Nat.add(String.length(x), 1n))) == True{} : Bool}
  N.le_refl(Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)))

law ab_snoc:
  for +k: List<&2, String>
  for +x: String
  for +hk: {E.all_bytes(k) == True{} : Bool}
  for +hx: {E.is_bytes(x) == True{} : Bool}
  {E.all_bytes(kx(k, x)) == True{} : Bool}

def ab_snoc(k, x, hk, hx):
  match k:
    case Nil{}:
      %Equal.sym(Bool, E.is_bytes(x), True{}, hx) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case h <> t:
      +hh = PB.and_true_l(E.is_bytes(h), E.all_bytes(t), hk)
      +ht = PB.and_true_r(E.is_bytes(h), E.all_bytes(t), hk)
      %Equal.sym(Bool, E.is_bytes(h), True{}, hh) : {Bool.and(_, E.all_bytes(kx(t, x))) == True{} : Bool}
      ab_snoc(t, x, ht, hx)

# Removing a false ok, or making ok smaller.
def tin(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+n}:
      Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())

# ok, then the thread count is in range.
def inv(st: B.ArgSt) -> Bool:
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      Bool.not(ok) || tin(B.Drv.thr(t))

law tok_and:
  for +ok: Bool
  for +c: Bool
  for +t: Maybe<&2, Nat>
  for +h: {(Bool.not(ok) || tin(t)) == True{} : Bool}
  {(Bool.not(ok && c) || tin(t)) == True{} : Bool}

def tok_and(ok, c, t, h):
  match ok:
    case True{}:
      match c:
        case True{}:
          h
        case False{}:
          {==}
    case False{}:
      {==}

law tok_thr:
  for +ok: Bool
  for +a: Bool
  for +b: Bool
  {(Bool.not(ok && a && b) || (a && b)) == True{} : Bool}

def tok_thr(ok, a, b):
  match ok:
    case True{}:
      match a:
        case True{}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          {==}
    case False{}:
      {==}

def mdisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{n}:
      Empty

law none_ne_some:
  for -n: Nat
  for e: {None{} == Some{n} : Maybe<&2, Nat>}
  Empty

def none_ne_some(n, e):
  %e : mdisc(_)
  Unit{}

# ---------------------------------------------------------------------------
# Picks (Bool.pick over states, as Args.word makes them)
# ---------------------------------------------------------------------------

law pick_kl:
  for +b: Bool
  for +a: B.ArgSt
  for +c: B.ArgSt
  for +m: Nat
  for +ha: {Nat.is_le(kl(a), m) == True{} : Bool}
  for +hc: {Nat.is_le(kl(c), m) == True{} : Bool}
  {Nat.is_le(kl(Bool.pick(B.ArgSt, b, a, c)), m) == True{} : Bool}

def pick_kl(b, a, c, m, ha, hc):
  match b:
    case True{}:
      ha
    case False{}:
      hc

law pick_ab:
  for +b: Bool
  for +a: B.ArgSt
  for +c: B.ArgSt
  for +ha: {E.all_bytes(keep(a)) == True{} : Bool}
  for +hc: {E.all_bytes(keep(c)) == True{} : Bool}
  {E.all_bytes(keep(Bool.pick(B.ArgSt, b, a, c))) == True{} : Bool}

def pick_ab(b, a, c, ha, hc):
  match b:
    case True{}:
      ha
    case False{}:
      hc

law pick_inv:
  for +b: Bool
  for +a: B.ArgSt
  for +c: B.ArgSt
  for +ha: {inv(a) == True{} : Bool}
  for +hc: {inv(c) == True{} : Bool}
  {inv(Bool.pick(B.ArgSt, b, a, c)) == True{} : Bool}

def pick_inv(b, a, c, ha, hc):
  match b:
    case True{}:
      ha
    case False{}:
      hc

law pick_un:
  for +b: Bool
  for +a1: B.ArgSt
  for +a2: B.ArgSt
  for +c1: B.ArgSt
  for +c2: B.ArgSt
  for +ha: {unthr(a1) == unthr(a2) : B.ArgSt}
  for +hc: {unthr(c1) == unthr(c2) : B.ArgSt}
  {unthr(Bool.pick(B.ArgSt, b, a1, c1)) == unthr(Bool.pick(B.ArgSt, b, a2, c2)) : B.ArgSt}

def pick_un(b, a1, a2, c1, c2, ha, hc):
  match b:
    case True{}:
      ha
    case False{}:
      hc

# ---------------------------------------------------------------------------
# One step
# ---------------------------------------------------------------------------

law win_keep:
  for +m: Maybe<&2, Nat>
  for +st: B.ArgSt
  {keep(B.Args.win(m, st)) == keep(st) : List<&2, String>}

def win_keep(m, st):
  match m st:
    case Some{n} B.ArgSt{p, s, w, t, r, v, ok, k}:
      {==}
    case None{} B.ArgSt{p, s, w, t, r, v, ok, k}:
      {==}

law thr_keep:
  for +m: Maybe<&2, Nat>
  for +st: B.ArgSt
  {keep(B.Args.thr(m, st)) == keep(st) : List<&2, String>}

def thr_keep(m, st):
  match m st:
    case Some{n} B.ArgSt{p, s, w, t, r, v, ok, k}:
      {==}
    case None{} B.ArgSt{p, s, w, t, r, v, ok, k}:
      {==}

# -o and -O keep the recorded arguments, keep the invariant, and do not look
# at the driver options (except to set them).
law typ_kl:
  for +m: Maybe<&2, B.OType>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +n: Nat
  {Nat.is_le(kl(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})), Nat.add(M.args_len(k), n)) == True{} : Bool}

def typ_kl(m, s, w, t, r, v, ok, k, n):
  match m:
    case Some{y}:
      N.le_add_r(M.args_len(k), n)
    case None{}:
      N.le_add_r(M.args_len(k), n)

law typ_ab:
  for +m: Maybe<&2, B.OType>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +hk: {E.all_bytes(k) == True{} : Bool}
  {E.all_bytes(keep(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}))) == True{} : Bool}

def typ_ab(m, s, w, t, r, v, ok, k, hk):
  match m:
    case Some{y}:
      hk
    case None{}:
      hk

law typ_inv:
  for +m: Maybe<&2, B.OType>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +h: {(Bool.not(ok) || tin(B.Drv.thr(t))) == True{} : Bool}
  {inv(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == True{} : Bool}

def typ_inv(m, s, w, t, r, v, ok, k, h):
  match m:
    case Some{y}:
      match y t:
        case B.OType{z1, l1} B.Drv{t0, o0, z0, l0}:
          h
    case None{}:
      {==}

law out_inv:
  for +x: String
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +h: {(Bool.not(ok) || tin(B.Drv.thr(t))) == True{} : Bool}
  {inv(B.ArgSt{B.PNone{}, s, w, B.Drv.set_out(x, t), r, v, ok && Bool.not(B.Args.bcf(x)), k}) == True{} : Bool}

def out_inv(x, s, w, t, r, v, ok, k, h):
  match t:
    case B.Drv{t0, o0, z0, l0}:
      tok_and(ok, Bool.not(B.Args.bcf(x)), t0, h)

law typ_un:
  for +m: Maybe<&2, B.OType>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unthr(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == unthr(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, B.Drv.none(), r, v, ok, k})) : B.ArgSt}

def typ_un(m, s, w, t, r, v, ok, k):
  match m:
    case Some{y}:
      {==}
    case None{}:
      {==}

law kl_step:
  for +st: B.ArgSt
  for +x: String
  {Nat.is_le(kl(B.Args.step(st, x)), Nat.add(kl(st), Nat.add(String.length(x), 1n))) == True{} : Bool}

def kl_step(st, x):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          pick_kl(String.eq(x, "-f"), B.ArgSt{B.PRef{}, s, w, t, r, v, ok, kx(k, x)}, w2(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), snoc_le(k, x),
          pick_kl(String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, kx(k, x)}, w3(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), snoc_le(k, x),
          pick_kl(String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)}, w4(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), snoc_le(k, x),
          pick_kl(String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, w5(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), N.le_add_r(M.args_len(k), Nat.add(String.length(x), 1n)),
          pick_kl(String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, w6(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), N.le_add_r(M.args_len(k), Nat.add(String.length(x), 1n)),
          pick_kl(String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, w7(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), N.le_add_r(M.args_len(k), Nat.add(String.length(x), 1n)),
          pick_kl(String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}), w8(x, s, w, t, r, v, ok, k), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n)), typ_kl(B.Args.otype(String.drop(x, 2n)), s, w, t, r, v, ok, k, Nat.add(String.length(x), 1n)),
          snoc_le(k, x))))))))
        case B.PRef{}:
          snoc_le(k, x)
        case B.PCheck{}:
          snoc_le(k, x)
        case B.PWin{}:
          %Equal.sym(List<&2, String>, keep(B.Args.win(B.Pos.read(x), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)})), kx(k, x), win_keep(B.Pos.read(x), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)})) :
            {Nat.is_le(M.args_len(_), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n))) == True{} : Bool}
          snoc_le(k, x)
        case B.PThr{}:
          %Equal.sym(List<&2, String>, keep(B.Args.thr(B.Pos.read(x), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})), k, thr_keep(B.Pos.read(x), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) :
            {Nat.is_le(M.args_len(_), Nat.add(M.args_len(k), Nat.add(String.length(x), 1n))) == True{} : Bool}
          N.le_add_r(M.args_len(k), Nat.add(String.length(x), 1n))
        case B.POut{}:
          N.le_add_r(M.args_len(k), Nat.add(String.length(x), 1n))
        case B.PType{}:
          typ_kl(B.Args.otype(x), s, w, t, r, v, ok, k, Nat.add(String.length(x), 1n))

law ab_step:
  for +st: B.ArgSt
  for +x: String
  for +hk: {E.all_bytes(keep(st)) == True{} : Bool}
  for +hx: {E.is_bytes(x) == True{} : Bool}
  {E.all_bytes(keep(B.Args.step(st, x))) == True{} : Bool}

def ab_step(st, x, hk, hx):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          pick_ab(String.eq(x, "-f"), B.ArgSt{B.PRef{}, s, w, t, r, v, ok, kx(k, x)}, w2(x, s, w, t, r, v, ok, k), ab_snoc(k, x, hk, hx),
          pick_ab(String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, kx(k, x)}, w3(x, s, w, t, r, v, ok, k), ab_snoc(k, x, hk, hx),
          pick_ab(String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)}, w4(x, s, w, t, r, v, ok, k), ab_snoc(k, x, hk, hx),
          pick_ab(String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, w5(x, s, w, t, r, v, ok, k), hk,
          pick_ab(String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, w6(x, s, w, t, r, v, ok, k), hk,
          pick_ab(String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, w7(x, s, w, t, r, v, ok, k), hk,
          pick_ab(String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}), w8(x, s, w, t, r, v, ok, k), typ_ab(B.Args.otype(String.drop(x, 2n)), s, w, t, r, v, ok, k, hk),
          ab_snoc(k, x, hk, hx))))))))
        case B.PRef{}:
          ab_snoc(k, x, hk, hx)
        case B.PCheck{}:
          ab_snoc(k, x, hk, hx)
        case B.PWin{}:
          %Equal.sym(List<&2, String>, keep(B.Args.win(B.Pos.read(x), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)})), kx(k, x), win_keep(B.Pos.read(x), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)})) :
            {E.all_bytes(_) == True{} : Bool}
          ab_snoc(k, x, hk, hx)
        case B.PThr{}:
          %Equal.sym(List<&2, String>, keep(B.Args.thr(B.Pos.read(x), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})), k, thr_keep(B.Pos.read(x), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) :
            {E.all_bytes(_) == True{} : Bool}
          hk
        case B.POut{}:
          hk
        case B.PType{}:
          typ_ab(B.Args.otype(x), s, w, t, r, v, ok, k, hk)

law win_inv:
  for +m: Maybe<&2, Nat>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +h: {(Bool.not(ok) || tin(B.Drv.thr(t))) == True{} : Bool}
  {inv(B.Args.win(m, B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k})) == True{} : Bool}

def win_inv(m, s, w, t, r, v, ok, k, h):
  match m:
    case Some{n}:
      tok_and(ok, Nat.is_le(1n, n), B.Drv.thr(t), h)
    case None{}:
      {==}

law thr_inv:
  for +m: Maybe<&2, Nat>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {inv(B.Args.thr(m, B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) == True{} : Bool}

def thr_inv(m, s, w, t, r, v, ok, k):
  match m:
    case Some{n}:
      match t:
        case B.Drv{t0, o0, z0, l0}:
          tok_thr(ok, Nat.is_le(1n, n), Nat.is_le(n, B.Args.max_threads()))
    case None{}:
      {==}

law inv_step:
  for +st: B.ArgSt
  for +x: String
  for +h: {inv(st) == True{} : Bool}
  {inv(B.Args.step(st, x)) == True{} : Bool}

def inv_step(st, x, h):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          pick_inv(String.eq(x, "-f"), B.ArgSt{B.PRef{}, s, w, t, r, v, ok, kx(k, x)}, w2(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, kx(k, x)}, w3(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)}, w4(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, w5(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, w6(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, w7(x, s, w, t, r, v, ok, k), h,
          pick_inv(String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}), w8(x, s, w, t, r, v, ok, k), typ_inv(B.Args.otype(String.drop(x, 2n)), s, w, t, r, v, ok, k, h),
          tok_and(ok && Bool.not(String.starts_with(x, "-") && Nat.is_lt(1n, String.length(x))), Maybe.is_none(&2, String, v), B.Drv.thr(t),
            tok_and(ok, Bool.not(String.starts_with(x, "-") && Nat.is_lt(1n, String.length(x))), B.Drv.thr(t), h)))))))))
        case B.PRef{}:
          tok_and(ok, Maybe.is_none(&2, String, r), B.Drv.thr(t), h)
        case B.PCheck{}:
          tok_and(ok, String.eq(x, "e") || String.eq(x, "w"), B.Drv.thr(t), h)
        case B.PWin{}:
          win_inv(B.Pos.read(x), s, w, t, r, v, ok, kx(k, x), h)
        case B.PThr{}:
          thr_inv(B.Pos.read(x), s, w, t, r, v, ok, k)
        case B.POut{}:
          out_inv(x, s, w, t, r, v, ok, k, h)
        case B.PType{}:
          typ_inv(B.Args.otype(x), s, w, t, r, v, ok, k, h)

law win_un:
  for +m: Maybe<&2, Nat>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unthr(B.Args.win(m, B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k})) == unthr(B.Args.win(m, B.ArgSt{B.PWin{}, s, w, B.Drv.none(), r, v, ok, k})) : B.ArgSt}

def win_un(m, s, w, t, r, v, ok, k):
  match m:
    case Some{n}:
      {==}
    case None{}:
      {==}

law thr_un:
  for +m: Maybe<&2, Nat>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unthr(B.Args.thr(m, B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) == unthr(B.Args.thr(m, B.ArgSt{B.PThr{}, s, w, B.Drv.none(), r, v, ok, k})) : B.ArgSt}

def thr_un(m, s, w, t, r, v, ok, k):
  match m:
    case Some{n}:
      {==}
    case None{}:
      {==}

# A step does not look at the driver options (except to set them).
law un_step:
  for +st: B.ArgSt
  for +x: String
  {unthr(B.Args.step(st, x)) == unthr(B.Args.step(unthr(st), x)) : B.ArgSt}

def un_step(st, x):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          pick_un(String.eq(x, "-f"), B.ArgSt{B.PRef{}, s, w, t, r, v, ok, kx(k, x)}, B.ArgSt{B.PRef{}, s, w, B.Drv.none(), r, v, ok, kx(k, x)}, w2(x, s, w, t, r, v, ok, k), w2(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, kx(k, x)}, B.ArgSt{B.PCheck{}, s, w, B.Drv.none(), r, v, ok, kx(k, x)}, w3(x, s, w, t, r, v, ok, k), w3(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, t, r, v, ok, kx(k, x)}, B.ArgSt{B.PWin{}, s, w, B.Drv.none(), r, v, ok, kx(k, x)}, w4(x, s, w, t, r, v, ok, k), w4(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, B.ArgSt{B.PThr{}, s, w, B.Drv.none(), r, v, ok, k}, w5(x, s, w, t, r, v, ok, k), w5(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, B.ArgSt{B.POut{}, s, w, B.Drv.none(), r, v, ok, k}, w6(x, s, w, t, r, v, ok, k), w6(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, B.ArgSt{B.PType{}, s, w, B.Drv.none(), r, v, ok, k}, w7(x, s, w, t, r, v, ok, k), w7(x, s, w, B.Drv.none(), r, v, ok, k), {==},
          pick_un(String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, B.Drv.none(), r, v, ok, k}), w8(x, s, w, t, r, v, ok, k), w8(x, s, w, B.Drv.none(), r, v, ok, k), typ_un(B.Args.otype(String.drop(x, 2n)), s, w, t, r, v, ok, k), {==})))))))
        case B.PRef{}:
          {==}
        case B.PCheck{}:
          {==}
        case B.PWin{}:
          win_un(B.Pos.read(x), s, w, t, r, v, ok, kx(k, x))
        case B.PThr{}:
          thr_un(B.Pos.read(x), s, w, t, r, v, ok, k)
        case B.POut{}:
          {==}
        case B.PType{}:
          typ_un(B.Args.otype(x), s, w, t, r, v, ok, k)


# ---------------------------------------------------------------------------
# Many steps
# ---------------------------------------------------------------------------

law mono_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +h: {Nat.is_le(a, Nat.add(b, c)) == True{} : Bool}
  {Nat.is_le(Nat.add(a, d), Nat.add(b, Nat.add(c, d))) == True{} : Bool}

def mono_assoc(a, b, c, d, h):
  %N.add_assoc(b, c, d) : {Nat.is_le(Nat.add(a, d), _) == True{} : Bool}
  N.le_add_mono_r(d, a, Nat.add(b, c), h)

law kl_go:
  for +xs: List<&2, String>
  for +st: B.ArgSt
  {Nat.is_le(kl(B.Args.go(xs, st)), Nat.add(kl(st), M.args_len(xs))) == True{} : Bool}

def kl_go(xs, st):
  match xs:
    case Nil{}:
      N.le_add_r(kl(st), 0n)
    case x <> t:
      +s1 = B.Args.step(st, x)
      N.le_trans(kl(B.Args.go(t, s1)), Nat.add(kl(s1), M.args_len(t)), Nat.add(kl(st), Nat.add(Nat.add(String.length(x), 1n), M.args_len(t))),
        kl_go(t, s1),
        mono_assoc(kl(s1), kl(st), Nat.add(String.length(x), 1n), M.args_len(t), kl_step(st, x)))

law ab_go:
  for +xs: List<&2, String>
  for +st: B.ArgSt
  for +hk: {E.all_bytes(keep(st)) == True{} : Bool}
  for +hx: {E.all_bytes(xs) == True{} : Bool}
  {E.all_bytes(keep(B.Args.go(xs, st))) == True{} : Bool}

def ab_go(xs, st, hk, hx):
  match xs:
    case Nil{}:
      hk
    case x <> t:
      ab_go(t, B.Args.step(st, x), ab_step(st, x, hk, PB.and_true_l(E.is_bytes(x), E.all_bytes(t), hx)), PB.and_true_r(E.is_bytes(x), E.all_bytes(t), hx))

law inv_go:
  for +xs: List<&2, String>
  for +st: B.ArgSt
  for +h: {inv(st) == True{} : Bool}
  {inv(B.Args.go(xs, st)) == True{} : Bool}

def inv_go(xs, st, h):
  match xs:
    case Nil{}:
      h
    case x <> t:
      inv_go(t, B.Args.step(st, x), inv_step(st, x, h))

law un_un:
  for +st: B.ArgSt
  {unthr(st) == unthr(unthr(st)) : B.ArgSt}

def un_un(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      {==}

law un_go:
  for +xs: List<&2, String>
  for +st: B.ArgSt
  {unthr(B.Args.go(xs, st)) == unthr(B.Args.go(xs, unthr(st))) : B.ArgSt}

def un_go(xs, st):
  match xs:
    case Nil{}:
      un_un(st)
    case x <> t:
      +s1 = B.Args.step(st, x)
      +s2 = B.Args.step(unthr(st), x)
      Equal.trans(B.ArgSt, unthr(B.Args.go(t, s1)), unthr(B.Args.go(t, unthr(s1))), unthr(B.Args.go(t, s2)),
        un_go(t, s1),
        Equal.trans(B.ArgSt, unthr(B.Args.go(t, unthr(s1))), unthr(B.Args.go(t, unthr(s2))), unthr(B.Args.go(t, s2)),
          Equal.cong(B.ArgSt, B.ArgSt, z => unthr(B.Args.go(t, z)), unthr(s1), unthr(s2), un_step(st, x)),
          Equal.sym(B.ArgSt, unthr(B.Args.go(t, s2)), unthr(B.Args.go(t, unthr(s2))), un_go(t, s2))))

law go_append:
  for +pre: List<&2, String>
  for +ys: List<&2, String>
  for +st: B.ArgSt
  {B.Args.go(List.append(&2, String, pre, ys), st) == B.Args.go(ys, B.Args.go(pre, st)) : B.ArgSt}

def go_append(pre, ys, st):
  match pre:
    case Nil{}:
      {==}
    case h <> t:
      go_append(t, ys, B.Args.step(st, h))

# Args.done does not look at the thread count.
law done_un:
  for +st: B.ArgSt
  {B.Args.done(st) == B.Args.done(unthr(st)) : Maybe<&2, B.Cfg>}

def done_un(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match r:
            case None{}:
              {==}
            case Some{r1}:
              match v:
                case None{}:
                  {==}
                case Some{v1}:
                  match ok:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case B.PRef{}:
          {==}
        case B.PCheck{}:
          {==}
        case B.PWin{}:
          {==}
        case B.PThr{}:
          {==}
        case B.POut{}:
          {==}
        case B.PType{}:
          {==}

law done_same:
  for +post: List<&2, String>
  for +s1: B.ArgSt
  for +s2: B.ArgSt
  for +h: {unthr(s1) == unthr(s2) : B.ArgSt}
  {B.Args.done(B.Args.go(post, s1)) == B.Args.done(B.Args.go(post, s2)) : Maybe<&2, B.Cfg>}

def done_same(post, s1, s2, h):
  +g1 = B.Args.go(post, s1)
  +g2 = B.Args.go(post, s2)
  Equal.trans(Maybe<&2, B.Cfg>, B.Args.done(g1), B.Args.done(unthr(g1)), B.Args.done(g2),
    done_un(g1),
    Equal.trans(Maybe<&2, B.Cfg>, B.Args.done(unthr(g1)), B.Args.done(unthr(g2)), B.Args.done(g2),
      Equal.cong(B.ArgSt, Maybe<&2, B.Cfg>, z => B.Args.done(z), unthr(g1), unthr(g2),
        Equal.trans(B.ArgSt, unthr(g1), unthr(B.Args.go(post, unthr(s1))), unthr(g2),
          un_go(post, s1),
          Equal.trans(B.ArgSt, unthr(B.Args.go(post, unthr(s1))), unthr(B.Args.go(post, unthr(s2))), unthr(g2),
            Equal.cong(B.ArgSt, B.ArgSt, z => unthr(B.Args.go(post, z)), unthr(s1), unthr(s2), h),
            Equal.sym(B.ArgSt, unthr(g2), unthr(B.Args.go(post, unthr(s2))), un_go(post, s2))))),
      Equal.sym(Maybe<&2, B.Cfg>, B.Args.done(g2), B.Args.done(unthr(g2)), done_un(g2))))

# ---------------------------------------------------------------------------
# --threads N where no option waits for its value
# ---------------------------------------------------------------------------

# The two words --threads and x change only the thread count.
law two_words:
  for +st: B.ArgSt
  for +x: String
  for +n: Nat
  for +he: {B.Args.expecting.of(st) == True{} : Bool}
  for +hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
  for +hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
  {unthr(B.Args.step(B.Args.step(st, "--threads"), x)) == unthr(st) : B.ArgSt}

def two_words(st, x, n, he, hx, hn):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          +h1 = PB.and_true_l(Nat.is_le(1n, n), Nat.is_le(n, B.Args.max_threads()), hn)
          +h2 = PB.and_true_r(Nat.is_le(1n, n), Nat.is_le(n, B.Args.max_threads()), hn)
          %Equal.sym(Maybe<&2, Nat>, B.Pos.read(x), Some{n}, hx) :
            {unthr(B.Args.thr(_, B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
          %Equal.sym(Bool, Nat.is_le(1n, n), True{}, h1) :
            {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok && _ && Nat.is_le(n, B.Args.max_threads()), k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
          %Equal.sym(Bool, Nat.is_le(n, B.Args.max_threads()), True{}, h2) :
            {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok && True{} && _, k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
          %Equal.sym(Bool, ok && True{} && True{}, ok && True{}, N.and_true_r_id(ok && True{})) :
            {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, _, k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
          %Equal.sym(Bool, ok && True{}, ok, N.and_true_r_id(ok)) :
            {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, _, k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
          {==}
        case B.PRef{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PCheck{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PWin{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PThr{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POut{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PType{}:
          Empty.absurd({unthr(B.Args.step(B.Args.step(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, "--threads"), x)) == unthr(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))

# The parser fact behind law threads.
law parse_thr:
  for +pre: List<&2, String>
  for +x: String
  for +n: Nat
  for +post: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
  for +hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
  {B.Args.parse(M.command(pre, "--threads" <> x <> post)) == B.Args.parse(M.command(pre, post)) : Maybe<&2, B.Cfg>}

def parse_thr(pre, x, n, post, he, hx, hn):
  +st = B.Args.go(pre, B.Args.init())
  +tl = {"--threads" <> x <> post : List<&2, String>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, tl), B.Args.init()), B.Args.go(tl, st), go_append(pre, tl, B.Args.init())) :
    {B.Args.done(_) == B.Args.done(B.Args.go(List.append(&2, String, pre, post), B.Args.init())) : Maybe<&2, B.Cfg>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, post), B.Args.init()), B.Args.go(post, st), go_append(pre, post, B.Args.init())) :
    {B.Args.done(B.Args.go(tl, st)) == B.Args.done(_) : Maybe<&2, B.Cfg>}
  done_same(post, B.Args.step(B.Args.step(st, "--threads"), x), st, two_words(st, x, n, he, hx, hn))

# ---------------------------------------------------------------------------
# Args.threads
# ---------------------------------------------------------------------------

law done_some:
  for +st: B.ArgSt
  for +n: Nat
  for +h: {B.Args.thr.done(st) == Some{n} : Maybe<&2, Nat>}
  {Maybe.is_none(&2, B.Cfg, B.Args.done(st)) == False{} : Bool}

def done_some(st, n, h):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match r:
            case None{}:
              Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PNone{}, s, w, t, None{}, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
            case Some{r1}:
              match v:
                case None{}:
                  Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PNone{}, s, w, t, Some{r1}, None{}, ok, k})) == False{} : Bool}, none_ne_some(n, h))
                case Some{v1}:
                  match ok:
                    case True{}:
                      {==}
                    case False{}:
                      Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PNone{}, s, w, t, Some{r1}, Some{v1}, False{}, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.PRef{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.PCheck{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.PWin{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.PThr{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.POut{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))
        case B.PType{}:
          Empty.absurd({Maybe.is_none(&2, B.Cfg, B.Args.done(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == False{} : Bool}, none_ne_some(n, h))

law done_range:
  for +st: B.ArgSt
  for +n: Nat
  for +hi: {inv(st) == True{} : Bool}
  for +h: {B.Args.thr.done(st) == Some{n} : Maybe<&2, Nat>}
  {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}

def done_range(st, n, hi, h):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match r:
            case None{}:
              Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
            case Some{r1}:
              match v:
                case None{}:
                  Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
                case Some{v1}:
                  match ok:
                    case True{}:
                      %h : {tin(_) == True{} : Bool}
                      hi
                    case False{}:
                      Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.PRef{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.PCheck{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.PWin{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.PThr{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.POut{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))
        case B.PType{}:
          Empty.absurd({(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}, none_ne_some(n, h))

law threads_if:
  for +c: Bool
  for +rest: List<&2, String>
  for +n: Nat
  for +h: {B.Args.threads.if(c, rest) == Some{n} : Maybe<&2, Nat>}
  {(Bool.not(Maybe.is_none(&2, B.Cfg, B.Args.done.if(c, rest))) && (Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads()))) == True{} : Bool}

def threads_if(c, rest, n, h):
  match c:
    case True{}:
      +st = B.Args.go(rest, B.Args.init())
      %Equal.sym(Bool, Maybe.is_none(&2, B.Cfg, B.Args.done(st)), False{}, done_some(st, n, h)) :
        {(Bool.not(_) && (Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads()))) == True{} : Bool}
      done_range(st, n, inv_go(rest, B.Args.init(), {==}), h)
    case False{}:
      Empty.absurd({(Bool.not(Maybe.is_none(&2, B.Cfg, B.Args.done.if(False{}, rest))) && (Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads()))) == True{} : Bool}, none_ne_some(n, h))

# Args.threads gives a count only for a command line Args.parse accepts, and
# then a count from 1 to Args.max_threads() (the driver sizes its tables by it).
law threads_ok:
  for +argv: List<&2, String>
  for +n: Nat
  for +h: {B.Args.threads(argv) == Some{n} : Maybe<&2, Nat>}
  {(Bool.not(Maybe.is_none(&2, B.Cfg, B.Args.parse(argv))) && (Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads()))) == True{} : Bool}

def threads_ok(argv, n, h):
  match argv:
    case Nil{}:
      Empty.absurd({(Bool.not(Maybe.is_none(&2, B.Cfg, B.Args.parse(Nil{}))) && (Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads()))) == True{} : Bool}, none_ne_some(n, h))
    case cmd <> rest:
      threads_if(String.eq(cmd, "norm"), rest, n, h)
