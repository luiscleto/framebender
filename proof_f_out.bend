import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm.bend as W
import ./proof_base.bend as PB
import ./proof_run_base.bend as Q
import ./proof_run_text.bend as T
import ./proof_f_args.bend as A
import ./proof_f_threads.bend as FT
import lawful-words@0.1.0.0/proof_nat.bend as N

# Phase H: law output (MACHINE.bend). Where no option waits for its value,
# the words of one output option (-o PATH, -O T, -OT; B.Args.out_opt) change
# only the parser's driver options (out_words), so Args.parse gives the same
# result with or without them (parse_out); then law usage or law machine gives
# both command lines the same launch (FT.same_parse). Also output_ok:
# Args.output answers Some exactly when Args.parse does.
# Note: && associates to the left (a && b && c is (a && b) && c).

# ---------------------------------------------------------------------------
# Bools and words
# ---------------------------------------------------------------------------

law or_left:
  for +x: Bool
  for +y: Bool
  for +m: Bool
  for +h: {(x || (y && m)) == True{} : Bool}
  for +hy: {y == False{} : Bool}
  {x == True{} : Bool}

def or_left(x, y, m, h, hy):
  match x:
    case True{}:
      {==}
    case False{}:
      match y:
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, PB.false_ne_true(Equal.sym(Bool, True{}, False{}, hy)))
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, PB.false_ne_true(h))

law sw_head:
  for +pt: String
  for +t: String
  for +b: Bool
  for +h: {String.starts_with.go.if(pt, t, b) == True{} : Bool}
  {b == True{} : Bool}

def sw_head(pt, t, b, h):
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PB.false_ne_true(h))

law sw_tail:
  for +pt: String
  for +t: String
  for +b: Bool
  for +h: {String.starts_with.go.if(pt, t, b) == True{} : Bool}
  {String.starts_with.go(pt, t) == True{} : Bool}

def sw_tail(pt, t, b, h):
  match b:
    case True{}:
      h
    case False{}:
      Empty.absurd({String.starts_with.go(pt, t) == True{} : Bool}, PB.false_ne_true(h))

law drop_zero:
  for +t: String
  {String.drop(t, 0n) == t : String}

def drop_zero(t):
  match t:
    case SNil{}:
      {==}
    case SCon{h, u}:
      {==}

# A word that starts with -O is -O followed by the rest.
law pre_O:
  for +a: String
  for +h: {String.starts_with(a, "-O") == True{} : Bool}
  {"-O" ++ String.drop(a, 2n) == a : String}

def pre_O(a, h):
  match a:
    case SNil{}:
      Empty.absurd({"-O" ++ String.drop(SNil{}, 2n) == SNil{} : String}, PB.false_ne_true(h))
    case SCon{c1, t1}:
      match t1:
        case SNil{}:
          Empty.absurd({"-O" ++ String.drop(SCon{c1, SNil{}}, 2n) == SCon{c1, SNil{}} : String}, PB.false_ne_true(sw_tail("O", SNil{}, Char.is_eq(c1, '-'), h)))
        case SCon{c2, t2}:
          +e1 = sw_head("O", SCon{c2, t2}, Char.is_eq(c1, '-'), h)
          +h1 = sw_tail("O", SCon{c2, t2}, Char.is_eq(c1, '-'), h)
          +e2 = sw_head("", t2, Char.is_eq(c2, 'O'), h1)
          %Equal.sym(String, String.drop(t2, 0n), t2, drop_zero(t2)) : {SCon{'-', SCon{'O', _}} == SCon{c1, SCon{c2, t2}} : String}
          %Equal.sym(Char, c1, '-', T.char_eq_sound(c1, '-', e1)) : {SCon{'-', SCon{'O', t2}} == SCon{_, SCon{c2, t2}} : String}
          %Equal.sym(Char, c2, 'O', T.char_eq_sound(c2, 'O', e2)) : {SCon{'-', SCon{'O', t2}} == SCon{'-', SCon{_, t2}} : String}
          {==}

# ---------------------------------------------------------------------------
# One output option where no option waits for its value
# ---------------------------------------------------------------------------

# The value of -O, accepted: only the driver options change.
law typ_some:
  for +m: Maybe<&2, B.OType>
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +hm: {Maybe.is_some(&2, B.OType, m) == True{} : Bool}
  {A.unthr(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def typ_some(m, s, w, t, r, v, ok, k, hm):
  match m:
    case Some{y}:
      {==}
    case None{}:
      Empty.absurd({A.unthr(B.Args.typ(None{}, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}, PB.false_ne_true(hm))

# The glued -OT, T accepted.
law glued:
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +d: String
  for +hd: {Maybe.is_some(&2, B.OType, B.Args.otype(d)) == True{} : Bool}
  {A.unthr(B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, "-O" ++ d)) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def glued(s, w, t, r, v, ok, k, d, hd):
  match d:
    case SNil{}:
      Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, "-O" ++ SNil{})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}, PB.false_ne_true(hd))
    case SCon{c, e}:
      match c:
        case Chr{x}:
          typ_some(B.Args.otype(SCon{Chr{x}, e}), s, w, t, r, v, ok, k, hd)

law glued_any:
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +a: String
  for +h: {(String.starts_with(a, "-O") && Maybe.is_some(&2, B.OType, B.Args.otype(String.drop(a, 2n)))) == True{} : Bool}
  {A.unthr(B.Args.go([a], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def glued_any(s, w, t, r, v, ok, k, a, h):
  +h1 = PB.and_true_l(String.starts_with(a, "-O"), Maybe.is_some(&2, B.OType, B.Args.otype(String.drop(a, 2n))), h)
  +h2 = PB.and_true_r(String.starts_with(a, "-O"), Maybe.is_some(&2, B.OType, B.Args.otype(String.drop(a, 2n))), h)
  %pre_O(a, h1) : {A.unthr(B.Args.go([_], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
  glued(s, w, t, r, v, ok, k, String.drop(a, 2n), h2)

# -o PATH, PATH not a .bcf.
law two_o:
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +b: String
  for +hb: {Bool.not(B.Args.bcf(b)) == True{} : Bool}
  {A.unthr(B.Args.go(["-o", b], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def two_o(s, w, t, r, v, ok, k, b, hb):
  %Equal.sym(Bool, Bool.not(B.Args.bcf(b)), True{}, hb) :
    {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok && _, k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
  %Equal.sym(Bool, ok && True{}, ok, N.and_true_r_id(ok)) :
    {B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, _, k} == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
  {==}

# -O T, T accepted.
law two_O:
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +b: String
  for +hb: {Maybe.is_some(&2, B.OType, B.Args.otype(b)) == True{} : Bool}
  {A.unthr(B.Args.go(["-O", b], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def two_O(s, w, t, r, v, ok, k, b, hb):
  typ_some(B.Args.otype(b), s, w, t, r, v, ok, k, hb)

law neq_O:
  for +a: String
  for +ea: {a == "-o" : String}
  {String.eq(a, "-O") == False{} : Bool}

def neq_O(a, ea):
  %Equal.sym(String, a, "-o", ea) : {String.eq(_, "-O") == False{} : Bool}
  {==}

# The two words a b of Args.out_opt.two, split on whether a is -o (c).
law two_k:
  for +s: Bool
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +a: String
  for +b: String
  for +c: Bool
  for +hc: {String.eq(a, "-o") == c : Bool}
  for +h: {((c && Bool.not(B.Args.bcf(b))) || (String.eq(a, "-O") && Maybe.is_some(&2, B.OType, B.Args.otype(b)))) == True{} : Bool}
  {A.unthr(B.Args.go([a, b], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}

def two_k(s, w, t, r, v, ok, k, a, b, c, hc, h):
  match c:
    case True{}:
      +ea = Q.str_eq_sound(a, "-o", hc)
      +hb = or_left(Bool.not(B.Args.bcf(b)), String.eq(a, "-O"), Maybe.is_some(&2, B.OType, B.Args.otype(b)), h, neq_O(a, ea))
      %Equal.sym(String, a, "-o", ea) : {A.unthr(B.Args.go([_, b], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
      two_o(s, w, t, r, v, ok, k, b, hb)
    case False{}:
      +ha = PB.and_true_l(String.eq(a, "-O"), Maybe.is_some(&2, B.OType, B.Args.otype(b)), h)
      +hs = PB.and_true_r(String.eq(a, "-O"), Maybe.is_some(&2, B.OType, B.Args.otype(b)), h)
      %Equal.sym(String, a, "-O", Q.str_eq_sound(a, "-O", ha)) : {A.unthr(B.Args.go([_, b], B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == B.ArgSt{B.PNone{}, s, w, B.Drv.none(), r, v, ok, k} : B.ArgSt}
      two_O(s, w, t, r, v, ok, k, b, hs)

# The words of one output option change only the driver options.
law out_words:
  for +st: B.ArgSt
  for +o: List<&2, String>
  for +he: {B.Args.expecting.of(st) == True{} : Bool}
  for +ho: {B.Args.out_opt(o) == True{} : Bool}
  {A.unthr(B.Args.go(o, st)) == A.unthr(st) : B.ArgSt}

def out_words(st, o, he, ho):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match o:
            case Nil{}:
              Empty.absurd({A.unthr(B.Args.go(Nil{}, B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(ho))
            case a <> t1:
              match t1:
                case Nil{}:
                  glued_any(s, w, t, r, v, ok, k, a, ho)
                case b <> t2:
                  match t2:
                    case Nil{}:
                      two_k(s, w, t, r, v, ok, k, a, b, String.eq(a, "-o"), {==}, ho)
                    case c <> t3:
                      Empty.absurd({A.unthr(B.Args.go(a <> b <> c <> t3, B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(ho))
        case B.PRef{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PCheck{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PWin{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PThr{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POut{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.POut{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PType{}:
          Empty.absurd({A.unthr(B.Args.go(o, B.ArgSt{B.PType{}, s, w, t, r, v, ok, k})) == A.unthr(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))

# The parser fact behind law output.
law parse_out:
  for +pre: List<&2, String>
  for +o: List<&2, String>
  for +post: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +ho: {B.Args.out_opt(o) == True{} : Bool}
  {B.Args.parse(M.command(pre, List.append(&2, String, o, post))) == B.Args.parse(M.command(pre, post)) : Maybe<&2, B.Cfg>}

def parse_out(pre, o, post, he, ho):
  +st = B.Args.go(pre, B.Args.init())
  +tl = List.append(&2, String, o, post)
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, tl), B.Args.init()), B.Args.go(tl, st), A.go_append(pre, tl, B.Args.init())) :
    {B.Args.done(_) == B.Args.done(B.Args.go(List.append(&2, String, pre, post), B.Args.init())) : Maybe<&2, B.Cfg>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, post), B.Args.init()), B.Args.go(post, st), A.go_append(pre, post, B.Args.init())) :
    {B.Args.done(B.Args.go(tl, st)) == B.Args.done(_) : Maybe<&2, B.Cfg>}
  %Equal.sym(B.ArgSt, B.Args.go(tl, st), B.Args.go(post, B.Args.go(o, st)), A.go_append(o, post, st)) :
    {B.Args.done(_) == B.Args.done(B.Args.go(post, st)) : Maybe<&2, B.Cfg>}
  A.done_same(post, B.Args.go(o, st), st, out_words(st, o, he, ho))

# ---------------------------------------------------------------------------
# Law output
# ---------------------------------------------------------------------------

# Dropping the words o, the rest of the command line is still bytes.
law ab_tail:
  for +o: List<&2, String>
  for +post: List<&2, String>
  for +h: {E.all_bytes(List.append(&2, String, o, post)) == True{} : Bool}
  {E.all_bytes(post) == True{} : Bool}

def ab_tail(o, post, h):
  match o:
    case Nil{}:
      h
    case x <> t:
      ab_tail(t, post, PB.and_true_r(E.is_bytes(x), E.all_bytes(List.append(&2, String, t, post)), h))

law ab_drop:
  for +pre: List<&2, String>
  for +o: List<&2, String>
  for +post: List<&2, String>
  for +h: {E.all_bytes(List.append(&2, String, pre, List.append(&2, String, o, post))) == True{} : Bool}
  {E.all_bytes(List.append(&2, String, pre, post)) == True{} : Bool}

def ab_drop(pre, o, post, h):
  match pre:
    case Nil{}:
      ab_tail(o, post, h)
    case p <> t:
      +hp = PB.and_true_l(E.is_bytes(p), E.all_bytes(List.append(&2, String, t, List.append(&2, String, o, post))), h)
      +ht = PB.and_true_r(E.is_bytes(p), E.all_bytes(List.append(&2, String, t, List.append(&2, String, o, post))), h)
      %Equal.sym(Bool, E.is_bytes(p), True{}, hp) : {Bool.and(_, E.all_bytes(List.append(&2, String, t, post))) == True{} : Bool}
      ab_drop(t, o, post, ht)

law texts_drop:
  for +pre: List<&2, String>
  for +o: List<&2, String>
  for +post: List<&2, String>
  for +fasta: String
  for +cs: List<&2, String>
  for +h: {E.texts_ok(M.command(pre, List.append(&2, String, o, post)), fasta, cs) == True{} : Bool}
  {E.texts_ok(M.command(pre, post), fasta, cs) == True{} : Bool}

def texts_drop(pre, o, post, fasta, cs, h):
  +ha = PB.and_true_l(E.all_bytes(List.append(&2, String, pre, List.append(&2, String, o, post))), E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs)), h)
  +hr = PB.and_true_r(E.all_bytes(List.append(&2, String, pre, List.append(&2, String, o, post))), E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs)), h)
  %Equal.sym(Bool, E.all_bytes(List.append(&2, String, pre, post)), True{}, ab_drop(pre, o, post, ha)) :
    {Bool.and(_, E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs))) == True{} : Bool}
  hr

law output:
  for +pre: List<&2, String>
  for +o: List<&2, String>
  for +post: List<&2, String>
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +ho: {B.Args.out_opt(o) == True{} : Bool}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(M.command(pre, List.append(&2, String, o, post)), fasta, cs) == True{} : Bool}
  {M.launch(W.start(M.command(pre, List.append(&2, String, o, post))), M.command(pre, List.append(&2, String, o, post)), fasta, vcf, cs)
    == M.launch(W.start(M.command(pre, post)), M.command(pre, post), fasta, vcf, cs) : Maybe<&2, M.Launch>}

def output(pre, o, post, fasta, vcf, cs, he, ho, hf, h, hb):
  +tl = List.append(&2, String, o, post)
  FT.same_parse(B.Args.parse(M.command(pre, post)), M.command(pre, tl), M.command(pre, post), fasta, vcf, cs,
    {==}, parse_out(pre, o, post, he, ho), hf, h, hb, texts_drop(pre, o, post, fasta, cs, hb))

# ---------------------------------------------------------------------------
# Args.output answers exactly when Args.parse does
# ---------------------------------------------------------------------------

law sink_done_ok:
  for +st: B.ArgSt
  {Maybe.is_some(&2, B.Sink, B.Args.sink.done(st)) == Maybe.is_some(&2, B.Cfg, B.Args.done(st)) : Bool}

def sink_done_ok(st):
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

law output_if:
  for +c: Bool
  for +rest: List<&2, String>
  {Maybe.is_some(&2, B.Sink, B.Args.output.if(c, rest)) == Maybe.is_some(&2, B.Cfg, B.Args.done.if(c, rest)) : Bool}

def output_if(c, rest):
  match c:
    case True{}:
      sink_done_ok(B.Args.go(rest, B.Args.init()))
    case False{}:
      {==}

# Args.output gives a Sink exactly for the command lines Args.parse accepts
# (the driver treats a None after Norm.start began as an internal error).
law output_ok:
  for +argv: List<&2, String>
  {Maybe.is_some(&2, B.Sink, B.Args.output(argv)) == Maybe.is_some(&2, B.Cfg, B.Args.parse(argv)) : Bool}

def output_ok(argv):
  match argv:
    case Nil{}:
      {==}
    case cmd <> rest:
      output_if(String.eq(cmd, "norm"), rest)
