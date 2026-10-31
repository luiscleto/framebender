import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm.bend as W
import ./proof_base.bend as PB
import ./proof_run_base.bend as Q
import ./proof_f_args.bend as A
import ./proof_f_threads.bend as FT
import ./proof_f_out.bend as FO

# Phase J: laws index and index_sink (MACHINE.bend). Where no option waits
# for its value, an index option x (B.Args.idx_opt: one of eight words) is one
# step of the parser that changes only the index format it keeps (idx_step:
# the state's Drv gets Drv.set_idx(B.Args.wfmt(x), t)). So:
# - law index: Args.parse gives the same result with or without x
#   (parse_idx, through A.unthr and A.done_same), and law usage or law machine
#   gives both command lines the same launch (FT.same_parse);
# - law index_sink: the same walk with unidx, which forgets only the index
#   format, gives the same Args.sink.done and Args.thr.done, so the same
#   Args.output and Args.threads (M.route);
# - index_ok: Args.index answers Some exactly when Args.parse does.
# Note: && and || associate to the left (a || b || c is (a || b) || c).

# ---------------------------------------------------------------------------
# The eight words
# ---------------------------------------------------------------------------

# A word that is none of the eight is not an index option.
law wfmt_none:
  for +x: String
  for +h1: {String.eq(x, "-W") == False{} : Bool}
  for +h2: {String.eq(x, "--write-index") == False{} : Bool}
  for +h3: {String.eq(x, "-Wcsi") == False{} : Bool}
  for +h4: {String.eq(x, "-W=csi") == False{} : Bool}
  for +h5: {String.eq(x, "--write-index=csi") == False{} : Bool}
  for +h6: {String.eq(x, "-Wtbi") == False{} : Bool}
  for +h7: {String.eq(x, "-W=tbi") == False{} : Bool}
  for +h8: {String.eq(x, "--write-index=tbi") == False{} : Bool}
  {Maybe.is_some(&2, B.IFmt, B.Args.wfmt(x)) == False{} : Bool}

def wfmt_none(x, h1, h2, h3, h4, h5, h6, h7, h8):
  %Equal.sym(Bool, String.eq(x, "-W"), False{}, h1) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "--write-index") || String.eq(x, "-Wcsi") || String.eq(x, "-W=csi") || String.eq(x, "--write-index=csi"), Some{B.Csi{}}, Bool.pick(Maybe<&2, B.IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "--write-index"), False{}, h2) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "-Wcsi") || String.eq(x, "-W=csi") || String.eq(x, "--write-index=csi"), Some{B.Csi{}}, Bool.pick(Maybe<&2, B.IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "-Wcsi"), False{}, h3) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "-W=csi") || String.eq(x, "--write-index=csi"), Some{B.Csi{}}, Bool.pick(Maybe<&2, B.IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "-W=csi"), False{}, h4) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "--write-index=csi"), Some{B.Csi{}}, Bool.pick(Maybe<&2, B.IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "--write-index=csi"), False{}, h5) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _, Some{B.Csi{}}, Bool.pick(Maybe<&2, B.IFmt>, String.eq(x, "-Wtbi") || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{}))) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "-Wtbi"), False{}, h6) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "-W=tbi") || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "-W=tbi"), False{}, h7) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _ || String.eq(x, "--write-index=tbi"), Some{B.Tbi{}}, None{})) == False{} : Bool}
  %Equal.sym(Bool, String.eq(x, "--write-index=tbi"), False{}, h8) :
    {Maybe.is_some(&2, B.IFmt, Bool.pick(Maybe<&2, B.IFmt>, _, Some{B.Tbi{}}, None{})) == False{} : Bool}
  {==}

# One index option where no option waits for its value: the step only sets
# the index format (b1 ... b8: whether x is each of the eight words).
law idx_step:
  for +s: B.Sci
  for +w: Maybe<&2, Nat>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  for +x: String
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  for +b7: Bool
  for +b8: Bool
  for +h1: {String.eq(x, "-W") == b1 : Bool}
  for +h2: {String.eq(x, "--write-index") == b2 : Bool}
  for +h3: {String.eq(x, "-Wcsi") == b3 : Bool}
  for +h4: {String.eq(x, "-W=csi") == b4 : Bool}
  for +h5: {String.eq(x, "--write-index=csi") == b5 : Bool}
  for +h6: {String.eq(x, "-Wtbi") == b6 : Bool}
  for +h7: {String.eq(x, "-W=tbi") == b7 : Bool}
  for +h8: {String.eq(x, "--write-index=tbi") == b8 : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, x) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), t), r, v, ok, k} : B.ArgSt}

def idx_step(s, w, t, r, v, ok, k, x, b1, b2, b3, b4, b5, b6, b7, b8, h1, h2, h3, h4, h5, h6, h7, h8, hx):
  match b1:
    case True{}:
      %Equal.sym(String, x, "-W", Q.str_eq_sound(x, "-W", h1)) :
        {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
      {==}
    case False{}:
      match b2:
        case True{}:
          %Equal.sym(String, x, "--write-index", Q.str_eq_sound(x, "--write-index", h2)) :
            {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
          {==}
        case False{}:
          match b3:
            case True{}:
              %Equal.sym(String, x, "-Wcsi", Q.str_eq_sound(x, "-Wcsi", h3)) :
                {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
              {==}
            case False{}:
              match b4:
                case True{}:
                  %Equal.sym(String, x, "-W=csi", Q.str_eq_sound(x, "-W=csi", h4)) :
                    {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
                  {==}
                case False{}:
                  match b5:
                    case True{}:
                      %Equal.sym(String, x, "--write-index=csi", Q.str_eq_sound(x, "--write-index=csi", h5)) :
                        {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
                      {==}
                    case False{}:
                      match b6:
                        case True{}:
                          %Equal.sym(String, x, "-Wtbi", Q.str_eq_sound(x, "-Wtbi", h6)) :
                            {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
                          {==}
                        case False{}:
                          match b7:
                            case True{}:
                              %Equal.sym(String, x, "-W=tbi", Q.str_eq_sound(x, "-W=tbi", h7)) :
                                {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
                              {==}
                            case False{}:
                              match b8:
                                case True{}:
                                  %Equal.sym(String, x, "--write-index=tbi", Q.str_eq_sound(x, "--write-index=tbi", h8)) :
                                    {B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, _) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(_), t), r, v, ok, k} : B.ArgSt}
                                  {==}
                                case False{}:
                                  Empty.absurd({B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, x) == B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), t), r, v, ok, k} : B.ArgSt}, PB.false_ne_true(Equal.trans(Bool, False{}, Maybe.is_some(&2, B.IFmt, B.Args.wfmt(x)), True{},
                                    Equal.sym(Bool, Maybe.is_some(&2, B.IFmt, B.Args.wfmt(x)), False{}, wfmt_none(x, h1, h2, h3, h4, h5, h6, h7, h8)), hx)))

# Where no option waits for its value, an index option leaves the state as
# it was but for the driver options.
law idx_un:
  for +st: B.ArgSt
  for +x: String
  for +he: {B.Args.expecting.of(st) == True{} : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  {A.unthr(B.Args.step(st, x)) == A.unthr(st) : B.ArgSt}

def idx_un(st, x, he, hx):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          %Equal.sym(B.ArgSt, B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, x), B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), t), r, v, ok, k}, idx_step(s, w, t, r, v, ok, k, x, String.eq(x, "-W"), String.eq(x, "--write-index"), String.eq(x, "-Wcsi"), String.eq(x, "-W=csi"), String.eq(x, "--write-index=csi"), String.eq(x, "-Wtbi"), String.eq(x, "-W=tbi"), String.eq(x, "--write-index=tbi"), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, hx)) :
            {A.unthr(_) == A.unthr(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}) : B.ArgSt}
          {==}
        case B.PRef{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PCheck{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PWin{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PThr{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POut{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PType{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PMulti{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.PMulti{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.PMulti{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POver{}:
          Empty.absurd({A.unthr(B.Args.step(B.ArgSt{B.POver{}, s, w, t, r, v, ok, k}, x)) == A.unthr(B.ArgSt{B.POver{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))

# The parser fact behind law index.
law parse_idx:
  for +pre: List<&2, String>
  for +x: String
  for +post: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  {B.Args.parse(M.command(pre, x <> post)) == B.Args.parse(M.command(pre, post)) : Maybe<&2, B.Cfg>}

def parse_idx(pre, x, post, he, hx):
  +st = B.Args.go(pre, B.Args.init())
  +tl = {x <> post : List<&2, String>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, tl), B.Args.init()), B.Args.go(tl, st), A.go_append(pre, tl, B.Args.init())) :
    {B.Args.done(_) == B.Args.done(B.Args.go(List.append(&2, String, pre, post), B.Args.init())) : Maybe<&2, B.Cfg>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, post), B.Args.init()), B.Args.go(post, st), A.go_append(pre, post, B.Args.init())) :
    {B.Args.done(B.Args.go(tl, st)) == B.Args.done(_) : Maybe<&2, B.Cfg>}
  A.done_same(post, B.Args.step(st, x), st, idx_un(st, x, he, hx))

# ---------------------------------------------------------------------------
# Law index
# ---------------------------------------------------------------------------

law index:
  for +pre: List<&2, String>
  for +x: String
  for +post: List<&2, String>
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(M.command(pre, x <> post), fasta, cs) == True{} : Bool}
  {M.launch(W.start(M.command(pre, x <> post)), M.command(pre, x <> post), fasta, vcf, cs)
    == M.launch(W.start(M.command(pre, post)), M.command(pre, post), fasta, vcf, cs) : Maybe<&2, M.Launch>}

def index(pre, x, post, fasta, vcf, cs, he, hx, hf, h, hb):
  +tl = {x <> post : List<&2, String>}
  FT.same_parse(B.Args.parse(M.command(pre, post)), M.command(pre, tl), M.command(pre, post), fasta, vcf, cs,
    {==}, parse_idx(pre, x, post, he, hx), hf, h, hb, FO.texts_drop(pre, [x], post, fasta, cs, hb))

# ---------------------------------------------------------------------------
# The state without its index format
# ---------------------------------------------------------------------------

def unidx(st: B.ArgSt) -> B.ArgSt:
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      B.ArgSt{p, s, w, B.Drv.set_idx(None{}, t), r, v, ok, k}

law pick_ui:
  for +b: Bool
  for +a1: B.ArgSt
  for +a2: B.ArgSt
  for +c1: B.ArgSt
  for +c2: B.ArgSt
  for +ha: {unidx(a1) == unidx(a2) : B.ArgSt}
  for +hc: {unidx(c1) == unidx(c2) : B.ArgSt}
  {unidx(Bool.pick(B.ArgSt, b, a1, c1)) == unidx(Bool.pick(B.ArgSt, b, a2, c2)) : B.ArgSt}

def pick_ui(b, a1, a2, c1, c2, ha, hc):
  match b:
    case True{}:
      ha
    case False{}:
      hc

law typ_ui:
  for +m: Maybe<&2, B.OType>
  for +s: B.Sci
  for +w: Maybe<&2, Nat>
  for +t0: Maybe<&2, Nat>
  for +o0: Maybe<&2, String>
  for +z0: Maybe<&2, Bool>
  for +l0: Maybe<&2, Nat>
  for +i0: Maybe<&2, B.IFmt>
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unidx(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k})) == unidx(B.Args.typ(m, B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k})) : B.ArgSt}

def typ_ui(m, s, w, t0, o0, z0, l0, i0, r, v, ok, k):
  match m:
    case Some{y}:
      match y:
        case B.OType{z1, l1}:
          {==}
    case None{}:
      {==}

law win_ui:
  for +m: Maybe<&2, Nat>
  for +s: B.Sci
  for +w: Maybe<&2, Nat>
  for +t0: Maybe<&2, Nat>
  for +o0: Maybe<&2, String>
  for +z0: Maybe<&2, Bool>
  for +l0: Maybe<&2, Nat>
  for +i0: Maybe<&2, B.IFmt>
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unidx(B.Args.win(m, B.ArgSt{B.PWin{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k})) == unidx(B.Args.win(m, B.ArgSt{B.PWin{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k})) : B.ArgSt}

def win_ui(m, s, w, t0, o0, z0, l0, i0, r, v, ok, k):
  match m:
    case Some{n}:
      {==}
    case None{}:
      {==}

law thrs_ui:
  for +m: Maybe<&2, Nat>
  for +s: B.Sci
  for +w: Maybe<&2, Nat>
  for +t0: Maybe<&2, Nat>
  for +o0: Maybe<&2, String>
  for +z0: Maybe<&2, Bool>
  for +l0: Maybe<&2, Nat>
  for +i0: Maybe<&2, B.IFmt>
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unidx(B.Args.thr(m, B.ArgSt{B.PThr{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k})) == unidx(B.Args.thr(m, B.ArgSt{B.PThr{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k})) : B.ArgSt}

def thrs_ui(m, s, w, t0, o0, z0, l0, i0, r, v, ok, k):
  match m:
    case Some{n}:
      {==}
    case None{}:
      {==}

# A step does not look at the index format (except to set it).
law ui_step:
  for +st: B.ArgSt
  for +x: String
  {unidx(B.Args.step(st, x)) == unidx(B.Args.step(unidx(st), x)) : B.ArgSt}

def ui_step(st, x):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              pick_ui(String.eq(x, "-f"), B.ArgSt{B.PRef{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, A.kx(k, x)}, B.ArgSt{B.PRef{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, A.kx(k, x)}, A.w2(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w2(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "-c"), B.ArgSt{B.PCheck{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, A.kx(k, x)}, B.ArgSt{B.PCheck{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, A.kx(k, x)}, A.w3(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w3(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "-w"), B.ArgSt{B.PWin{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, A.kx(k, x)}, B.ArgSt{B.PWin{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, A.kx(k, x)}, A.w3m(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w3m(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "-m"), B.ArgSt{B.PMulti{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, A.kx(k, x)}, B.ArgSt{B.PMulti{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, A.kx(k, x)}, A.w3o(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w3o(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "--multi-overlaps"), B.ArgSt{B.POver{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, A.kx(k, x)}, B.ArgSt{B.POver{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, A.kx(k, x)}, A.w3g(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w3g(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.starts_with(x, "-m"), B.ArgSt{B.PNone{}, B.Sci.multi(s), w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok && B.Args.multi(String.drop(x, 2n)), A.kx(k, x)}, B.ArgSt{B.PNone{}, B.Sci.multi(s), w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok && B.Args.multi(String.drop(x, 2n)), A.kx(k, x)}, A.w4(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w4(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "--threads"), B.ArgSt{B.PThr{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k}, B.ArgSt{B.PThr{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k}, A.w5(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w5(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "-o"), B.ArgSt{B.POut{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k}, B.ArgSt{B.POut{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k}, A.w6(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w6(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.eq(x, "-O"), B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k}, B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k}, A.w7(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w7(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                pick_ui(String.starts_with(x, "-O"), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k}), B.Args.typ(B.Args.otype(String.drop(x, 2n)), B.ArgSt{B.PType{}, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k}), A.w8(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w8(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), typ_ui(B.Args.otype(String.drop(x, 2n)), s, w, t0, o0, z0, l0, i0, r, v, ok, k),
                pick_ui(Maybe.is_some(&2, B.IFmt, B.Args.wfmt(x)), B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), B.Drv{t0, o0, z0, l0, i0}), r, v, ok, k}, B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), B.Drv{t0, o0, z0, l0, None{}}), r, v, ok, k}, A.w9(x, s, w, B.Drv{t0, o0, z0, l0, i0}, r, v, ok, k), A.w9(x, s, w, B.Drv{t0, o0, z0, l0, None{}}, r, v, ok, k), {==},
                {==})))))))))))
        case B.PRef{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              {==}
        case B.PCheck{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              {==}
        case B.PWin{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              win_ui(B.Pos.read(x), s, w, t0, o0, z0, l0, i0, r, v, ok, A.kx(k, x))
        case B.PThr{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              thrs_ui(B.Pos.read(x), s, w, t0, o0, z0, l0, i0, r, v, ok, k)
        case B.POut{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              {==}
        case B.PType{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              typ_ui(B.Args.otype(x), s, w, t0, o0, z0, l0, i0, r, v, ok, k)
        case B.PMulti{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              {==}
        case B.POver{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
              {==}

law ui_ui:
  for +st: B.ArgSt
  {unidx(st) == unidx(unidx(st)) : B.ArgSt}

def ui_ui(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match t:
        case B.Drv{t0, o0, z0, l0, i0}:
          {==}

law ui_go:
  for +xs: List<&2, String>
  for +st: B.ArgSt
  {unidx(B.Args.go(xs, st)) == unidx(B.Args.go(xs, unidx(st))) : B.ArgSt}

def ui_go(xs, st):
  match xs:
    case Nil{}:
      ui_ui(st)
    case x <> t:
      +s1 = B.Args.step(st, x)
      +s2 = B.Args.step(unidx(st), x)
      Equal.trans(B.ArgSt, unidx(B.Args.go(t, s1)), unidx(B.Args.go(t, unidx(s1))), unidx(B.Args.go(t, s2)),
        ui_go(t, s1),
        Equal.trans(B.ArgSt, unidx(B.Args.go(t, unidx(s1))), unidx(B.Args.go(t, unidx(s2))), unidx(B.Args.go(t, s2)),
          Equal.cong(B.ArgSt, B.ArgSt, z => unidx(B.Args.go(t, z)), unidx(s1), unidx(s2), ui_step(st, x)),
          Equal.sym(B.ArgSt, unidx(B.Args.go(t, s2)), unidx(B.Args.go(t, unidx(s2))), ui_go(t, s2))))

# B.Args.sink.done does not look at the index format.
law sink_ui:
  for +st: B.ArgSt
  {B.Args.sink.done(st) == B.Args.sink.done(unidx(st)) : Maybe<&2, B.Sink>}

def sink_ui(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
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
        case B.PMulti{}:
          {==}
        case B.POver{}:
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

law sink_same:
  for +post: List<&2, String>
  for +s1: B.ArgSt
  for +s2: B.ArgSt
  for +h: {unidx(s1) == unidx(s2) : B.ArgSt}
  {B.Args.sink.done(B.Args.go(post, s1)) == B.Args.sink.done(B.Args.go(post, s2)) : Maybe<&2, B.Sink>}

def sink_same(post, s1, s2, h):
  +g1 = B.Args.go(post, s1)
  +g2 = B.Args.go(post, s2)
  Equal.trans(Maybe<&2, B.Sink>, B.Args.sink.done(g1), B.Args.sink.done(unidx(g1)), B.Args.sink.done(g2),
    sink_ui(g1),
    Equal.trans(Maybe<&2, B.Sink>, B.Args.sink.done(unidx(g1)), B.Args.sink.done(unidx(g2)), B.Args.sink.done(g2),
      Equal.cong(B.ArgSt, Maybe<&2, B.Sink>, z => B.Args.sink.done(z), unidx(g1), unidx(g2),
        Equal.trans(B.ArgSt, unidx(g1), unidx(B.Args.go(post, unidx(s1))), unidx(g2),
          ui_go(post, s1),
          Equal.trans(B.ArgSt, unidx(B.Args.go(post, unidx(s1))), unidx(B.Args.go(post, unidx(s2))), unidx(g2),
            Equal.cong(B.ArgSt, B.ArgSt, z => unidx(B.Args.go(post, z)), unidx(s1), unidx(s2), h),
            Equal.sym(B.ArgSt, unidx(g2), unidx(B.Args.go(post, unidx(s2))), ui_go(post, s2))))),
      Equal.sym(Maybe<&2, B.Sink>, B.Args.sink.done(g2), B.Args.sink.done(unidx(g2)), sink_ui(g2))))

# B.Args.thr.done does not look at the index format.
law thr_ui:
  for +st: B.ArgSt
  {B.Args.thr.done(st) == B.Args.thr.done(unidx(st)) : Maybe<&2, Nat>}

def thr_ui(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match t:
            case B.Drv{t0, o0, z0, l0, i0}:
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
        case B.PMulti{}:
          {==}
        case B.POver{}:
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

law thr_same:
  for +post: List<&2, String>
  for +s1: B.ArgSt
  for +s2: B.ArgSt
  for +h: {unidx(s1) == unidx(s2) : B.ArgSt}
  {B.Args.thr.done(B.Args.go(post, s1)) == B.Args.thr.done(B.Args.go(post, s2)) : Maybe<&2, Nat>}

def thr_same(post, s1, s2, h):
  +g1 = B.Args.go(post, s1)
  +g2 = B.Args.go(post, s2)
  Equal.trans(Maybe<&2, Nat>, B.Args.thr.done(g1), B.Args.thr.done(unidx(g1)), B.Args.thr.done(g2),
    thr_ui(g1),
    Equal.trans(Maybe<&2, Nat>, B.Args.thr.done(unidx(g1)), B.Args.thr.done(unidx(g2)), B.Args.thr.done(g2),
      Equal.cong(B.ArgSt, Maybe<&2, Nat>, z => B.Args.thr.done(z), unidx(g1), unidx(g2),
        Equal.trans(B.ArgSt, unidx(g1), unidx(B.Args.go(post, unidx(s1))), unidx(g2),
          ui_go(post, s1),
          Equal.trans(B.ArgSt, unidx(B.Args.go(post, unidx(s1))), unidx(B.Args.go(post, unidx(s2))), unidx(g2),
            Equal.cong(B.ArgSt, B.ArgSt, z => unidx(B.Args.go(post, z)), unidx(s1), unidx(s2), h),
            Equal.sym(B.ArgSt, unidx(g2), unidx(B.Args.go(post, unidx(s2))), ui_go(post, s2))))),
      Equal.sym(Maybe<&2, Nat>, B.Args.thr.done(g2), B.Args.thr.done(unidx(g2)), thr_ui(g2))))

# Where no option waits for its value, an index option leaves the state as
# it was but for the index format.
law idx_ui0:
  for +s: B.Sci
  for +w: Maybe<&2, Nat>
  for +m: Maybe<&2, B.IFmt>
  for +t: B.Drv
  for +r: Maybe<&2, String>
  for +v: Maybe<&2, String>
  for +ok: Bool
  for +k: List<&2, String>
  {unidx(B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(m, t), r, v, ok, k}) == unidx(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}) : B.ArgSt}

def idx_ui0(s, w, m, t, r, v, ok, k):
  match t:
    case B.Drv{t0, o0, z0, l0, i0}:
      {==}

law idx_ui:
  for +st: B.ArgSt
  for +x: String
  for +he: {B.Args.expecting.of(st) == True{} : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  {unidx(B.Args.step(st, x)) == unidx(st) : B.ArgSt}

def idx_ui(st, x, he, hx):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          %Equal.sym(B.ArgSt, B.Args.step(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}, x), B.ArgSt{B.PNone{}, s, w, B.Drv.set_idx(B.Args.wfmt(x), t), r, v, ok, k}, idx_step(s, w, t, r, v, ok, k, x, String.eq(x, "-W"), String.eq(x, "--write-index"), String.eq(x, "-Wcsi"), String.eq(x, "-W=csi"), String.eq(x, "--write-index=csi"), String.eq(x, "-Wtbi"), String.eq(x, "-W=tbi"), String.eq(x, "--write-index=tbi"), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, hx)) :
            {unidx(_) == unidx(B.ArgSt{B.PNone{}, s, w, t, r, v, ok, k}) : B.ArgSt}
          idx_ui0(s, w, B.Args.wfmt(x), t, r, v, ok, k)
        case B.PRef{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PRef{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PMulti{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PMulti{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PMulti{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POver{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.POver{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.POver{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PCheck{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PCheck{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PWin{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PWin{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PThr{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PThr{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.POut{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.POut{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))
        case B.PType{}:
          Empty.absurd({unidx(B.Args.step(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}, x)) == unidx(B.ArgSt{B.PType{}, s, w, t, r, v, ok, k}) : B.ArgSt}, PB.false_ne_true(he))

# ---------------------------------------------------------------------------
# Law index_sink
# ---------------------------------------------------------------------------

law index_sink:
  for +pre: List<&2, String>
  for +x: String
  for +post: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +hx: {B.Args.idx_opt(x) == True{} : Bool}
  {M.route(M.command(pre, x <> post)) == M.route(M.command(pre, post)) : M.Route}

def index_sink(pre, x, post, he, hx):
  +st = B.Args.go(pre, B.Args.init())
  +tl = {x <> post : List<&2, String>}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, tl), B.Args.init()), B.Args.go(tl, st), A.go_append(pre, tl, B.Args.init())) :
    {M.Route{B.Args.sink.done(_), B.Args.thr.done(_)} == M.Route{B.Args.sink.done(B.Args.go(List.append(&2, String, pre, post), B.Args.init())), B.Args.thr.done(B.Args.go(List.append(&2, String, pre, post), B.Args.init()))} : M.Route}
  %Equal.sym(B.ArgSt, B.Args.go(List.append(&2, String, pre, post), B.Args.init()), B.Args.go(post, st), A.go_append(pre, post, B.Args.init())) :
    {M.Route{B.Args.sink.done(B.Args.go(tl, st)), B.Args.thr.done(B.Args.go(tl, st))} == M.Route{B.Args.sink.done(_), B.Args.thr.done(_)} : M.Route}
  %Equal.sym(Maybe<&2, B.Sink>, B.Args.sink.done(B.Args.go(post, B.Args.step(st, x))), B.Args.sink.done(B.Args.go(post, st)), sink_same(post, B.Args.step(st, x), st, idx_ui(st, x, he, hx))) :
    {M.Route{_, B.Args.thr.done(B.Args.go(post, B.Args.step(st, x)))} == M.Route{B.Args.sink.done(B.Args.go(post, st)), B.Args.thr.done(B.Args.go(post, st))} : M.Route}
  %Equal.sym(Maybe<&2, Nat>, B.Args.thr.done(B.Args.go(post, B.Args.step(st, x))), B.Args.thr.done(B.Args.go(post, st)), thr_same(post, B.Args.step(st, x), st, idx_ui(st, x, he, hx))) :
    {M.Route{B.Args.sink.done(B.Args.go(post, st)), _} == M.Route{B.Args.sink.done(B.Args.go(post, st)), B.Args.thr.done(B.Args.go(post, st))} : M.Route}
  {==}

# ---------------------------------------------------------------------------
# Args.index answers exactly when Args.parse does
# ---------------------------------------------------------------------------

law index_done_ok:
  for +st: B.ArgSt
  {Maybe.is_some(&2, B.Idx, B.Args.index.done(st)) == Maybe.is_some(&2, B.Cfg, B.Args.done(st)) : Bool}

def index_done_ok(st):
  match st:
    case B.ArgSt{p, s, w, t, r, v, ok, k}:
      match p:
        case B.PNone{}:
          match s:
            case B.Sci{sc, sm, sz}:
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
        case B.PMulti{}:
          {==}
        case B.POver{}:
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

law index_if:
  for +c: Bool
  for +rest: List<&2, String>
  {Maybe.is_some(&2, B.Idx, B.Args.index.if(c, rest)) == Maybe.is_some(&2, B.Cfg, B.Args.done.if(c, rest)) : Bool}

def index_if(c, rest):
  match c:
    case True{}:
      index_done_ok(B.Args.go(rest, B.Args.init()))
    case False{}:
      {==}

# Args.index gives an Idx exactly for the command lines Args.parse accepts
# (the driver treats a None after Norm.start began as an internal error).
law index_ok:
  for +argv: List<&2, String>
  {Maybe.is_some(&2, B.Idx, B.Args.index(argv)) == Maybe.is_some(&2, B.Cfg, B.Args.parse(argv)) : Bool}

def index_ok(argv):
  match argv:
    case Nil{}:
      {==}
    case cmd <> rest:
      index_if(String.eq(cmd, "norm"), rest)
