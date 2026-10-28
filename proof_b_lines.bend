import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./norm_fast.bend as NF
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_fasteq.bend as FE
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT
import ./proof_b_lines_str.bend as S
import ./proof_b_lines_bt.bend as X
import ./proof_b_lines_pd.bend as Y
import ./proof_b_lines_room.bend as R
import ./proof_b_lines_piece.bend as PS
import ./proof_b_lit.bend as LT
import ../lawful-words/proof_u32.bend as U
import ./proof_b_enc.bend as EN
import ../lawful-bytes/proof_find.bend as FD
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-words/proof_nat.bend as N

# The machine's input (norm.bend: Src, Pd, NF.lf, pend.add, join.k,
# eof_src, line): the text not handled yet, P.srcstext of the sources then
# P.pdtext of the line end, splits into the lines B.Text.lines gives.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

# The source a complete line end becomes (norm.bend's Pd.src).
def pdsrc(+pp: P.PdP) -> P.SrcP:
  match pp:
    case P.PBP{+len, +t, +d}:
      P.SBP{len, t, d, 0}
    case P.PSP{+s}:
      P.SLP{s}

# ---------------------------------------------------------------------------
# Lemmas for join_ok (here, as they use pdsrc)
# ---------------------------------------------------------------------------

def JoinR(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +k: U32, -r: Norm.Pd & D.Bytes) -> Type:
  &pp2: P.PdP -> ({r == (P.mkPd(pp2), C.BT(bl, bt)) : Norm.Pd & D.Bytes}
  & ({Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(pdsrc(pp2)) : Norm.Src}
  & ({P.src_ok(pdsrc(pp2)) == True{} : Bool}
  & {P.srctext(pdsrc(pp2)) == String.append(P.pdtext(pp), P.btext(bl, bt, 0, (k + 1 : U32))) : String})))

# A small byte line end: bytes 0 .. k appended.
def join_ok.b(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bl: U32, +bt: AT.Tree<U32>, +k: U32,
  r: Y.PutR(len, t, bl, bt, 0, (k + 1 : U32), NR.put_bytes(C.BT(len, t), C.BT(bl, bt), 0, (k + 1 : U32)))) ->
  JoinR(P.PBP{len, t, d}, bl, bt, k, Norm.join.b(NR.put_bytes(C.BT(len, t), C.BT(bl, bt), 0, (k + 1 : U32)))):
  (+l3, r1) = r
  (+t3, r2) = r1
  (+d3, r3) = r2
  (+e, r4) = r3
  (+ok3, +v3) = r4
  +V = D.view(C.BT(len, t))
  +W = D.view(C.BT(l3, t3))
  +sl = D.slice(D.view(C.BT(bl, bt)), U32.to_nat(0), U32.to_nat((k + 1 : U32)))
  +heq = {
    %Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(len, t), C.BT(bl, bt), 0, (k + 1 : U32)), (C.BT(l3, t3), C.BT(bl, bt)), e) :
      {Norm.join.b(_) == (Norm.PB{C.BT(l3, t3)}, C.BT(bl, bt)) : Norm.Pd & D.Bytes}
    {==} : {Norm.join.b(NR.put_bytes(C.BT(len, t), C.BT(bl, bt), 0, (k + 1 : U32))) == (P.mkPd(P.PBP{l3, t3, d3}), C.BT(bl, bt)) : Norm.Pd & D.Bytes}}
  +htx = {
    %Equal.sym(List<&2, U32>, List.drop(&2, U32, W, 0n), W, FD.drop_zero(W)) :
      {NR.chars(_) == String.append(NR.chars(V), NR.chars(sl)) : String}
    %Equal.sym(List<&2, U32>, W, List.append(&2, U32, V, sl), v3) :
      {NR.chars(_) == String.append(NR.chars(V), NR.chars(sl)) : String}
    S.chars_app(V, sl) : {P.srctext(pdsrc(P.PBP{l3, t3, d3})) == String.append(P.pdtext(P.PBP{len, t, d}), P.btext(bl, bt, 0, (k + 1 : U32))) : String}}
  (P.PBP{l3, t3, d3}, (heq, ({==}, (Y.and_le0(D.ok(C.BT(l3, t3), d3), l3, ok3), htx))))

# A text line end (or one that would pass 2^28 bytes): the line as text.
def join_ok.s(+pp: P.PdP, +a: String, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32,
  +ha: {E.is_bytes(a) == True{} : Bool},
  +hta: {a == P.pdtext(pp) : String},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(C.BT(bl, bt)), U32.to_nat(k)) == Some{10} : Maybe<&2, U32>},
  +hna: {P.nolf(a) == True{} : Bool},
  +hnb: {P.nolf(P.btext(bl, bt, 0, k)) == True{} : Bool}) ->
  JoinR(pp, bl, bt, k, Norm.join.s(a, Norm.text(C.BT(bl, bt), 0, k))):
  +B1 = P.btext(bl, bt, 0, k)
  +hs0 = N.lt_to_le(U32.to_nat(k), U32.to_nat(bl), hk)
  +heq = {
    %Equal.sym(D.Bytes & String, Norm.text(C.BT(bl, bt), 0, k), (C.BT(bl, bt), B1), Y.text_eq(bl, bt, bd, 0, k, hok, hs0)) :
      {Norm.join.s(a, _) == (Norm.PS{String.append(a, B1)}, C.BT(bl, bt)) : Norm.Pd & D.Bytes}
    {==} : {Norm.join.s(a, Norm.text(C.BT(bl, bt), 0, k)) == (P.mkPd(P.PSP{String.append(a, B1)}), C.BT(bl, bt)) : Norm.Pd & D.Bytes}}
  +htx = {
    %hta : {String.append(String.append(a, B1), "\n") == String.append(_, P.btext(bl, bt, 0, (k + 1 : U32))) : String}
    %Equal.sym(String, P.btext(bl, bt, 0, (k + 1 : U32)), String.append(B1, "\n"), Y.bt_lf(bl, bt, bd, k, hok, hk, hlf)) :
      {String.append(String.append(a, B1), "\n") == String.append(a, _) : String}
    S.sassoc(a, B1, "\n") : {P.srctext(pdsrc(P.PSP{String.append(a, B1)})) == String.append(P.pdtext(pp), P.btext(bl, bt, 0, (k + 1 : U32))) : String}}
  (P.PSP{String.append(a, B1)}, (heq, ({==}, (Y.and_tt(E.is_bytes(String.append(a, B1)), P.nolf(String.append(a, B1)), S.bytes_app(a, B1, ha, Y.bytes_btext(bl, bt, 0, k)), S.nolf_app(a, B1, hna, hnb)), htx))))

def join_ok.bk(+len: U32, +t: AT.Tree<U32>, +d: Nat, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32, +z: Bool,
  +ez: {U32.is_le(((len + k : U32) + 1 : U32), 268435456) == z : Bool},
  +hp: {P.pd_ok(P.PBP{len, t, d}) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(C.BT(bl, bt)), U32.to_nat(k)) == Some{10} : Maybe<&2, U32>},
  +hn: {P.nolf(P.pdtext(P.PBP{len, t, d})) == True{} : Bool},
  +hn2: {P.nolf(P.btext(bl, bt, 0, k)) == True{} : Bool}) ->
  JoinR(P.PBP{len, t, d}, bl, bt, k, Norm.join.go(z, C.BT(len, t), C.BT(bl, bt), k)):
  match z:
    case True{}:
      +hokp = Y.pd_okb(len, t, d, hp)
      +hk1 = Y.k1(bl, bt, bd, k, hok, hk)
      +S1 = ((len + k : U32) + 1 : U32)
      +X1 = Nat.add(U32.to_nat(len), U32.to_nat((k + 1 : U32)))
      +hsz = AB.subst(Nat, w => {Nat.is_le(w, U32.to_nat(268435456)) == True{} : Bool}, U32.to_nat(S1), X1, Y.wk1(len, k, bl, bt, bd, Y.pd_okl(len, t, d, hp), hok, hk),
        Equal.trans(Bool, Nat.is_le(U32.to_nat(S1), U32.to_nat(268435456)), U32.is_le(S1, 268435456), True{},
          Equal.sym(Bool, U32.is_le(S1, 268435456), Nat.is_le(U32.to_nat(S1), U32.to_nat(268435456)), U.is_le_to_nat(S1, 268435456)), ez))
      +h28 = AB.subst(Nat, w => {Nat.is_le(X1, w) == True{} : Bool}, U32.to_nat(268435456), Nat.pow(2n, 28n), LT.lit28w(), hsz)
      +hx = N.le_trans(X1, Nat.pow(2n, 28n), Nat.pow(2n, 29n), h28, R.le28_29())
      +hs = AB.subst(Nat, w => {Nat.is_le(Nat.add(U32.to_nat(0), w), U32.to_nat(bl)) == True{} : Bool}, Nat.add(U32.to_nat(k), 1n), U32.to_nat((k + 1 : U32)),
        Equal.sym(Nat, U32.to_nat((k + 1 : U32)), Nat.add(U32.to_nat(k), 1n), hk1), C.succ_le(U32.to_nat(k), U32.to_nat(bl), hk))
      join_ok.b(len, t, d, bl, bt, k, Y.put_ok(len, t, d, bl, bt, bd, 0, (k + 1 : U32), hokp, hok, hs, hx))
    case False{}:
      +hokp = Y.pd_okb(len, t, d, hp)
      %Equal.sym(String, Norm.text_of(C.BT(len, t)), NR.chars(D.view(C.BT(len, t))), Y.textof_eq(len, t, d, hokp)) :
        JoinR(P.PBP{len, t, d}, bl, bt, k, Norm.join.s(_, Norm.text(C.BT(bl, bt), 0, k)))
      join_ok.s(P.PBP{len, t, d}, NR.chars(D.view(C.BT(len, t))), bl, bt, bd, k, Y.bytes_view(len, t), {==}, hok, hk, hlf, hn, hn2)

def join_ok.go(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32,
  +hp: {P.pd_ok(pp) == True{} : Bool},
  +hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  +hk: {Nat.is_lt(U32.to_nat(k), U32.to_nat(bl)) == True{} : Bool},
  +hlf: {List.get(&2, U32, D.view(C.BT(bl, bt)), U32.to_nat(k)) == Some{10} : Maybe<&2, U32>},
  +hn: {P.nolf(P.pdtext(pp)) == True{} : Bool},
  +hn2: {P.nolf(P.btext(bl, bt, 0, k)) == True{} : Bool}) ->
  JoinR(pp, bl, bt, k, Norm.join.k(P.mkPd(pp), C.BT(bl, bt), k)):
  match pp:
    case P.PBP{+len, +t, +d}:
      join_ok.bk(len, t, d, bl, bt, bd, k, U32.is_le(((len + k : U32) + 1 : U32), 268435456), {==}, hp, hok, hk, hlf, hn, hn2)
    case P.PSP{+str}:
      join_ok.s(P.PSP{str}, str, bl, bt, bd, k, hp, {==}, hok, hk, hlf, hn, hn2)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# The first LF at or after s, or the buffer's end (part).
def lf_ok(+len: U32, +t: AT.Tree<U32>, +d: Nat, +s: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(s, len) == True{} : Bool}) ->
  &j: U32 -> ({NF.lf(C.BT(len, t), s) == NF.Tb{C.BT(len, t), j, U32.is_eq(j, len), False{}} : NF.Tb}
  & {n(j) == D.first(xs(len, t), n(s), n(len), 10) : Nat}):
  X.lf_ok.go(len, t, d, s, hok, hs)

# A source whose first LF from at is lf: the line before it, the LF, and the
# source from lf + 1.
def src_line(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32, +lf: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(at, len) == True{} : Bool},
  hf: {D.first(xs(len, t), n(at), n(len), 10) == n(lf) : Nat},
  hl: {Nat.is_lt(n(lf), n(len)) == True{} : Bool}) ->
  {P.srctext(P.SBP{len, t, d, at}) == String.append(P.btext(len, t, at, (lf - at : U32)), String.append("\n", P.srctext(P.SBP{len, t, d, (lf + 1 : U32)}))) : String}
  & ({P.nolf(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool}
  & ({U32.is_le((lf + 1 : U32), len) == True{} : Bool}
  & {E.is_bytes(P.btext(len, t, at, (lf - at : U32))) == True{} : Bool})):
  X.src_line.go(len, t, d, at, lf, hok, hs, hf, hl)

# A source with no LF from at on: its text has none (it goes to pend).
def src_nolf(+len: U32, +t: AT.Tree<U32>, +d: Nat, +at: U32,
  hok: {D.ok(C.BT(len, t), d) == True{} : Bool},
  hs: {U32.is_le(at, len) == True{} : Bool},
  hf: {D.first(xs(len, t), n(at), n(len), 10) == n(len) : Nat}) ->
  {P.nolf(P.srctext(P.SBP{len, t, d, at})) == True{} : Bool}
  & {P.srctext(P.SBP{len, t, d, at}) == P.btext(len, t, at, (len - at : U32)) : String}:
  X.src_nolf.go(len, t, d, at, hok, hs, hf)

# Bytes s .. s+k-1 added to the line end.
def pend_add(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +k: U32,
  hp: {P.pd_ok(pp) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(n(s), n(k)), n(bl)) == True{} : Bool}) ->
  &pp2: P.PdP -> ({Norm.pend.add(P.mkPd(pp), C.BT(bl, bt), s, k) == P.mkPd(pp2) : Norm.Pd}
  & ({P.pd_ok(pp2) == True{} : Bool}
  & {P.pdtext(pp2) == String.append(P.pdtext(pp), P.btext(bl, bt, s, k)) : String})):
  Y.pend_add.go(pp, bl, bt, bd, s, k, hp, hok, hs)

# The line end's length (Pd.len hands it back).
def pd_len(+pp: P.PdP,
  hp: {P.pd_ok(pp) == True{} : Bool}) ->
  {Norm.Pd.len(P.mkPd(pp)) == (P.mkPd(pp), String.length(P.pdtext(pp))) : Norm.Pd & Nat}:
  Y.pd_len.go(pp, hp)

# A piece whose byte k is an LF completes the line end: the line, as a source
# (bytes with the LF, or text).
def join_ok(+pp: P.PdP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +k: U32,
  hp: {P.pd_ok(pp) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hk: {Nat.is_lt(n(k), n(bl)) == True{} : Bool},
  hlf: {List.get(&2, U32, xs(bl, bt), n(k)) == Some{10} : Maybe<&2, U32>},
  hn: {P.nolf(P.pdtext(pp)) == True{} : Bool},
  hn2: {P.nolf(P.btext(bl, bt, 0, k)) == True{} : Bool}) ->
  &pp2: P.PdP -> ({Norm.join.k(P.mkPd(pp), C.BT(bl, bt), k) == (P.mkPd(pp2), C.BT(bl, bt)) : Norm.Pd & D.Bytes}
  & ({Norm.Pd.src(P.mkPd(pp2)) == P.mkSrc(pdsrc(pp2)) : Norm.Src}
  & ({P.src_ok(pdsrc(pp2)) == True{} : Bool}
  & {P.srctext(pdsrc(pp2)) == String.append(P.pdtext(pp), P.btext(bl, bt, 0, (k + 1 : U32))) : String}))):
  join_ok.go(pp, bl, bt, bd, k, hp, hok, hk, hlf, hn, hn2)

# At the end of the file a non-empty line end becomes the last line, given
# an LF.
def eof_ok(+pp: P.PdP,
  hp: {P.pd_ok(pp) == True{} : Bool},
  hn: {P.nolf(P.pdtext(pp)) == True{} : Bool}) ->
  &sp: P.SrcP -> ({Norm.eof_src(P.mkPd(pp)) == P.mkSrc(sp) : Norm.Src}
  & ({P.src_ok(sp) == True{} : Bool}
  & {P.srctext(sp) == String.append(P.pdtext(pp), "\n") : String})):
  Y.eof_ok.go(pp, hp, hn)

# The empty line end the machine starts with (and keeps after a join).
def pd_empty() ->
  &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
  & ({P.pd_ok(pp) == True{} : Bool}
  & {P.pdtext(pp) == "" : String})):
  Y.pd_empty.go()

# A piece given by the driver (E.enc of a text of bytes, at most 2^31 bytes)
# as a source from 0.
def piece_src(+c: String,
  hb: {E.is_bytes(c) == True{} : Bool},
  hn: {P.le31(String.length(c)) == True{} : Bool}) ->
  &sp: P.SrcP -> ({Norm.SB{E.enc(c), 0} == P.mkSrc(sp) : Norm.Src}
  & ({P.src_ok(sp) == True{} : Bool}
  & {P.srctext(sp) == c : String})):
  PS.piece_src.k(c, EN.enc_ok(c, hb, hn))

# ---------------------------------------------------------------------------
# Lines of text (String level)
# ---------------------------------------------------------------------------

# The machine's line is B.Text.line.
def line_eq(+p: String) ->
  {Norm.line(p) == B.Text.line(p) : B.Line}:
  S.line_eq(p)

# A line and its LF in front of more text.
def lines_cons(+p: String, +y: String,
  hn: {P.nolf(p) == True{} : Bool}) ->
  {B.Text.lines(String.append(p, String.append("\n", y))) == B.Text.line(p) <> B.Text.lines(y) : List<&2, B.Line>}:
  S.lines_cons(p, y, hn)

# A last line without an LF reads the same with one.
def lines_eof(+y: String, +x: String,
  hn: {P.nolf(x) == True{} : Bool},
  hx: {String.is_empty(x) == False{} : Bool}) ->
  {B.Text.lines(String.append(y, String.append(x, "\n"))) == B.Text.lines(String.append(y, x)) : List<&2, B.Line>}:
  S.lines_eof.go(y, x, hn, hx)

# Text with no LF holds no complete line: its lines are what B.Text.last
# makes of it.
def lines_nolf(+x: String,
  hn: {P.nolf(x) == True{} : Bool}) ->
  {B.Text.lines(x) == B.Text.last(x) : List<&2, B.Line>}:
  S.lines_nolf(x, hn)

# Text with no LF in front of more text: its lines are those of the joined
# text (it is the start of the first line).
def lines_nolf_app(+x: String, +y: String, +z: String,
  hn: {P.nolf(x) == True{} : Bool},
  hn2: {P.nolf(y) == True{} : Bool}) ->
  {B.Text.lines(String.append(String.append(x, y), z)) == B.Text.lines(String.append(x, String.append(y, z))) : List<&2, B.Line>}:
  Equal.cong(String, List<&2, B.Line>, w => B.Text.lines(w), String.append(String.append(x, y), z), String.append(x, String.append(y, z)), S.sassoc(x, y, z))
