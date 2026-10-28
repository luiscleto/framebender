import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./MACHINE.bend as M
import ./norm_seq.bend as Q
import ./norm.bend as W
import ./bytes_enc.bend as E
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_cache.bend as K
import ./proof_e_task_buf.bend as BUF

# Phase E, area D (task): a task's windows (norm_par.bend's task.win) with
# the truthful answers: each is the window win_truths describes, or none for
# a contig name of more than 2^28 bytes; good pictures either way.

def parts_go1(+f: Nat, +c: String, +a: Nat, +b: Nat) -> {Q.parts.go(f, True{}, c, a, b) == [Pr.Req{c, a, b}] : List<&2, Pr.Req>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

# A read within 2^31 letters is its own parts.
def parts1(+c: String, +a: Nat, +b: Nat, +h: {E.le31(Nat.sub(b, a)) == True{} : Bool}) ->
  {Q.parts(c, a, b) == [Pr.Req{c, a, b}] : List<&2, Pr.Req>}:
  %Equal.sym(Bool, Q.le31(Nat.sub(b, a)), True{}, h) : {Q.parts.go(Nat.sub(b, a), _, c, a, b) == [Pr.Req{c, a, b}] : List<&2, Pr.Req>}
  parts_go1(Nat.sub(b, a), c, a, b)

def mbk.p(+one: Bool, +c: String, +a: Nat, +b: Nat,
  +hb: {E.is_bytes(c) == True{} : Bool},
  +hl: {Q.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_win.k(Bool.pick(PC.WP, one, PC.WPKnown{c, a, b}, PC.WPStr{c, a, b})) == True{} : Bool}:
  match one:
    case True{}:
      %Equal.sym(Bool, E.is_bytes(c), True{}, hb) : {Bool.and(_, Q.len_le(c, 268435456)) == True{} : Bool}
      %Equal.sym(Bool, Q.len_le(c, 268435456), True{}, hl) : {Bool.and(True{}, _) == True{} : Bool}
      {==}
    case False{}:
      {==}

def mbk.k(+m: Maybe<&2, String>, +c: String, +a: Nat, +b: Nat,
  +hb: {E.is_bytes(c) == True{} : Bool},
  +hl: {Q.len_le(c, 268435456) == True{} : Bool}) ->
  {S.mb_win.k(PC.wpOf.k(m, c, a, b)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      mbk.p(Q.le31(Nat.sub(b, a)), c, a, b, hb, hl)

def wt_eq(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +hfa: {PC.fa_bytes(fa) == True{} : Bool}) -> {Q.win_of(Q.parts(c, a, b), M.truths(fa, Q.parts(c, a, b))) == PC.mkWin(fa, PC.wpOf(fa, c, a, b)) : Q.Win}:
  Pair.fst({Q.win_of(Q.parts(c, a, b), M.truths(fa, Q.parts(c, a, b))) == PC.mkWin(fa, PC.wpOf(fa, c, a, b)) : Q.Win}, {PC.wp_ok(fa, PC.wpOf(fa, c, a, b)) == True{} : Bool}, K.win_truths(fa, c, a, b, hfa))

def wt_ok(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat, +hfa: {PC.fa_bytes(fa) == True{} : Bool}) -> {PC.wp_ok(fa, PC.wpOf(fa, c, a, b)) == True{} : Bool}:
  Pair.snd({Q.win_of(Q.parts(c, a, b), M.truths(fa, Q.parts(c, a, b))) == PC.mkWin(fa, PC.wpOf(fa, c, a, b)) : Q.Win}, {PC.wp_ok(fa, PC.wpOf(fa, c, a, b)) == True{} : Bool}, K.win_truths(fa, c, a, b, hfa))

def WPR.if(+sh: Bool, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat) -> PC.WP:
  match sh:
    case True{}:
      PC.wpOf(fa, c, a, b)
    case False{}:
      PC.WPNone{}

# The window picture of one read and its truthful answer.
def WPR(+fa: List<&2, B.Contig>, +r: Pr.Req) -> PC.WP:
  match r:
    case Pr.Req{+c, +a, +b}:
      WPR.if(Q.len_le(c, 268435456), fa, c, a, b)

def win1.if(+sh: Bool, +fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hsh: {Q.len_le(c, 268435456) == sh : Bool},
  +hl: {E.le31(Nat.sub(b, a)) == True{} : Bool},
  +hb: {E.is_bytes(c) == True{} : Bool}) ->
  {W.task.win.if(sh, Pr.Req{c, a, b}, M.truths.one(fa, Pr.Req{c, a, b})) == PC.mkWin(fa, WPR.if(sh, fa, c, a, b)) : Q.Win}
  & {Bool.and(PC.wp_ok(fa, WPR.if(sh, fa, c, a, b)), S.mb_win.k(WPR.if(sh, fa, c, a, b))) == True{} : Bool}:
  match sh:
    case True{}:
      +ep = parts1(c, a, b, hl)
      +e1 = {
        %ep :
          {Q.win_of(_, M.truths(fa, _)) == PC.mkWin(fa, PC.wpOf(fa, c, a, b)) : Q.Win}
        wt_eq(fa, c, a, b, hfa) :
          {W.task.win.if(True{}, Pr.Req{c, a, b}, M.truths.one(fa, Pr.Req{c, a, b})) == PC.mkWin(fa, WPR.if(True{}, fa, c, a, b)) : Q.Win}}
      +hw = wt_ok(fa, c, a, b, hfa)
      (e1, %Equal.sym(Bool, PC.wp_ok(fa, PC.wpOf(fa, c, a, b)), True{}, hw) : {Bool.and(_, S.mb_win.k(PC.wpOf(fa, c, a, b))) == True{} : Bool}
        mbk.k(B.Fasta.find(fa, c), c, a, b, hb, hsh))
    case False{}:
      ({==}, {==})

# One read's window: what the task builds is the picture's window.
def win1(+fa: List<&2, B.Contig>, +c: String, +a: Nat, +b: Nat,
  +hfa: {PC.fa_bytes(fa) == True{} : Bool},
  +hl: {E.le31(Nat.sub(b, a)) == True{} : Bool},
  +hb: {E.is_bytes(c) == True{} : Bool}) ->
  {W.task.win(Pr.Req{c, a, b}, M.truths.one(fa, Pr.Req{c, a, b})) == PC.mkWin(fa, WPR(fa, Pr.Req{c, a, b})) : Q.Win}
  & {Bool.and(PC.wp_ok(fa, WPR(fa, Pr.Req{c, a, b})), S.mb_win.k(WPR(fa, Pr.Req{c, a, b}))) == True{} : Bool}:
  win1.if(Q.len_le(c, 268435456), fa, c, a, b, hfa, {==}, hl, hb)
