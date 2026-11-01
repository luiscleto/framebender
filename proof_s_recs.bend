import Base
import ./types.bend as B
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./proof_base.bend as PB
import ./proof_b_defs.bend as P
import ./proof_b_lines_str.bend as LSS
import ./proof_s_line.bend as LI
import lawful-fields@0.1.1.0/defs.bend as FD
import lawful-words@0.1.0.0/proof_nat.bend as N

# The records' buffer read back as lines (norm_seq.bend's SP source): its
# text is recs_text(ps, term), each piece followed by the terminator; when
# the pieces hold no LF (and, with an LF terminator, no CR), its lines are
# the records Line{p, term}, one per piece. Every variable is reusable.

def Ss() -> Data:
  List<&2, String>

def Ls() -> Data:
  List<&2, B.Line>

# How many times c occurs in s.
def cc(s: String, +c: U32) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{Chr{+x}, t}:
      FD.count.if(U32.is_eq(x, c), cc(t, c))

law cc_chars:
  for +xs: List<&2, U32>
  for +c: U32
  {cc(NR.chars(xs), c) == FD.count(xs, c) : Nat}

def cc_chars(xs, c):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.cong(Nat, Nat, k => FD.count.if(U32.is_eq(x, c), k), cc(NR.chars(r), c), FD.count(r, c), cc_chars(r, c))

def cif_add(+h: Bool, +a: Nat, +b: Nat) -> {Nat.add(FD.count.if(h, a), b) == FD.count.if(h, Nat.add(a, b)) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

law cc_app:
  for +a: String
  for +b: String
  for +c: U32
  {cc(String.append(a, b), c) == Nat.add(cc(a, c), cc(b, c)) : Nat}

def cc_app(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(Nat, cc(String.append(t, b), c), Nat.add(cc(t, c), cc(b, c)), cc_app(t, b, c)) :
        {FD.count.if(U32.is_eq(x, c), _) == Nat.add(FD.count.if(U32.is_eq(x, c), cc(t, c)), cc(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(FD.count.if(U32.is_eq(x, c), cc(t, c)), cc(b, c)), FD.count.if(U32.is_eq(x, c), Nat.add(cc(t, c), cc(b, c))), cif_add(U32.is_eq(x, c), cc(t, c), cc(b, c)))

# The pieces' own count.
def SUM(ps: Ss(), +c: U32) -> Nat:
  match ps:
    case Nil{}:
      0n
    case +p <> t:
      Nat.add(cc(p, c), SUM(t, c))

def LS(ps: Ss(), +term: String) -> Ls():
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      B.Line{p, term} <> LS(t, term)

def rt_cons(+p: String, +t: Ss(), +term: String) -> {Norm.recs_text(p <> t, term) == String.append(p, String.append(term, Norm.recs_text(t, term))) : String}:
  {==}

# The count over the records: the pieces' own, plus one per piece when the
# terminator holds c once, none when it holds no c.
law cc_recs1:
  for +ps: Ss()
  for +term: String
  for +c: U32
  for +h1: {cc(term, c) == 1n : Nat}
  {cc(Norm.recs_text(ps, term), c) == Nat.add(SUM(ps, c), List.length(&2, String, ps)) : Nat}

def cc_recs1(ps, term, c, h1):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +R = Norm.recs_text(t, term)
      %Equal.sym(Nat, cc(String.append(p, String.append(term, R)), c), Nat.add(cc(p, c), cc(String.append(term, R), c)), cc_app(p, String.append(term, R), c)) :
        {_ == Nat.add(SUM(Con{p, t}, c), List.length(&2, String, Con{p, t})) : Nat}
      %Equal.sym(Nat, cc(String.append(term, R), c), Nat.add(cc(term, c), cc(R, c)), cc_app(term, R, c)) :
        {Nat.add(cc(p, c), _) == Nat.add(SUM(Con{p, t}, c), List.length(&2, String, Con{p, t})) : Nat}
      %Equal.sym(Nat, cc(term, c), 1n, h1) :
        {Nat.add(cc(p, c), Nat.add(_, cc(R, c))) == Nat.add(SUM(Con{p, t}, c), List.length(&2, String, Con{p, t})) : Nat}
      %Equal.sym(Nat, cc(R, c), Nat.add(SUM(t, c), List.length(&2, String, t)), cc_recs1(t, term, c, h1)) :
        {Nat.add(cc(p, c), Nat.add(1n, _)) == Nat.add(SUM(Con{p, t}, c), List.length(&2, String, Con{p, t})) : Nat}
      +cp = cc(p, c)
      +St = SUM(t, c)
      +Lt = List.length(&2, String, t)
      Equal.trans(Nat, Nat.add(cp, 1n+Nat.add(St, Lt)), 1n+Nat.add(cp, Nat.add(St, Lt)), Nat.add(Nat.add(cp, St), 1n+Lt),
        N.add_succ(cp, Nat.add(St, Lt)),
        Equal.sym(Nat, Nat.add(Nat.add(cp, St), 1n+Lt), 1n+Nat.add(cp, Nat.add(St, Lt)),
          Equal.trans(Nat, Nat.add(Nat.add(cp, St), 1n+Lt), 1n+Nat.add(Nat.add(cp, St), Lt), 1n+Nat.add(cp, Nat.add(St, Lt)),
            N.add_succ(Nat.add(cp, St), Lt), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(cp, St), Lt), Nat.add(cp, Nat.add(St, Lt)), N.add_assoc(cp, St, Lt)))))

law cc_recs0:
  for +ps: Ss()
  for +term: String
  for +c: U32
  for +h0: {cc(term, c) == 0n : Nat}
  {cc(Norm.recs_text(ps, term), c) == SUM(ps, c) : Nat}

def cc_recs0(ps, term, c, h0):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +R = Norm.recs_text(t, term)
      %Equal.sym(Nat, cc(String.append(p, String.append(term, R)), c), Nat.add(cc(p, c), cc(String.append(term, R), c)), cc_app(p, String.append(term, R), c)) :
        {_ == SUM(Con{p, t}, c) : Nat}
      %Equal.sym(Nat, cc(String.append(term, R), c), Nat.add(cc(term, c), cc(R, c)), cc_app(term, R, c)) :
        {Nat.add(cc(p, c), _) == SUM(Con{p, t}, c) : Nat}
      %Equal.sym(Nat, cc(term, c), 0n, h0) : {Nat.add(cc(p, c), Nat.add(_, cc(R, c))) == SUM(Con{p, t}, c) : Nat}
      %Equal.sym(Nat, cc(R, c), SUM(t, c), cc_recs0(t, term, c, h0)) : {Nat.add(cc(p, c), _) == SUM(Con{p, t}, c) : Nat}
      {==}

# A count of zero: not this one, and none after.
def cz_b(+b: Bool, +k: Nat, +h: {FD.count.if(b, k) == 0n : Nat}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+k, 0n, h)))
    case False{}:
      {==}

def cz_k(+b: Bool, +k: Nat, +h: {FD.count.if(b, k) == 0n : Nat}) -> {k == 0n : Nat}:
  match b:
    case True{}:
      Empty.absurd({k == 0n : Nat}, PB.false_ne_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+k, 0n, h)))
    case False{}:
      h

# No LF.
law nolf_cc:
  for +p: String
  for +h: {cc(p, 10) == 0n : Nat}
  {P.nolf(p) == True{} : Bool}

def nolf_cc(p, h):
  match p:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      %Equal.sym(Bool, U32.is_eq(x, 10), False{}, cz_b(U32.is_eq(x, 10), cc(t, 10), h)) : {Bool.and(Bool.not(_), P.nolf(t)) == True{} : Bool}
      nolf_cc(t, cz_k(U32.is_eq(x, 10), cc(t, 10), h))

# No CR: the text does not end with one.
law ecr_go:
  for +t: String
  for +x: U32
  for +hx: {U32.is_eq(x, 13) == False{} : Bool}
  for +ht: {cc(t, 13) == 0n : Nat}
  {Norm.ends_cr.go(t, Chr{x}) == False{} : Bool}

def ecr_go(t, x, hx, ht):
  match t:
    case SNil{}:
      hx
    case SCon{Chr{+y}, +t2}:
      ecr_go(t2, y, cz_b(U32.is_eq(y, 13), cc(t2, 13), ht), cz_k(U32.is_eq(y, 13), cc(t2, 13), ht))

def ecr.k(+p: String, +h: {cc(p, 13) == 0n : Nat}) -> {Norm.ends_cr(p) == False{} : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      ecr_go(t, x, cz_b(U32.is_eq(x, 13), cc(t, 13), h), cz_k(U32.is_eq(x, 13), cc(t, 13), h))

law ecr:
  for +p: String
  for +h: {cc(p, 13) == 0n : Nat}
  {String.ends_with(p, "\r") == False{} : Bool}

def ecr(p, h):
  Equal.trans(Bool, String.ends_with(p, "\r"), Norm.ends_cr(p), False{}, Equal.sym(Bool, Norm.ends_cr(p), String.ends_with(p, "\r"), LSS.ends_cr(p)), ecr.k(p, h))

# The text then CR: a line ending CR LF.
def line_cr(+p: String) -> {B.Text.line(String.append(p, "\r")) == B.Line{p, "\r\n"} : B.Line}:
  +P2 = String.append(p, "\r")
  %Equal.sym(Bool, String.ends_with(P2, "\r"), True{}, LI.ends_cr(p, 13)) : {B.Text.line.if(_, P2) == B.Line{p, "\r\n"} : B.Line}
  %Equal.sym(Nat, String.length(P2), 1n+String.length(p), LI.len_snoc(p, '\r')) : {B.Line{String.take(P2, Nat.sub(_, 1n)), "\r\n"} == B.Line{p, "\r\n"} : B.Line}
  %Equal.sym(Nat, Nat.sub(String.length(p), 0n), String.length(p), N.sub_zero(String.length(p))) : {B.Line{String.take(P2, _), "\r\n"} == B.Line{p, "\r\n"} : B.Line}
  %Equal.sym(String, String.take(P2, String.length(p)), p, LI.take_app(p, "\r")) : {B.Line{_, "\r\n"} == B.Line{p, "\r\n"} : B.Line}
  {==}

# LF terminator: no LF and no CR in the pieces.
law lines_lf:
  for +ps: Ss()
  for +h10: {SUM(ps, 10) == 0n : Nat}
  for +h13: {SUM(ps, 13) == 0n : Nat}
  {B.Text.lines(Norm.recs_text(ps, "\n")) == LS(ps, "\n") : Ls()}

def lines_lf(ps, h10, h13):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +R = Norm.recs_text(t, "\n")
      %Equal.sym(Ls(), B.Text.lines(String.append(p, String.append("\n", R))), B.Text.line(p) <> B.Text.lines(R),
          LSS.lines_cons(p, R, nolf_cc(p, N.add_eq_zero_l(cc(p, 10), SUM(t, 10), h10)))) :
        {_ == LS(Con{p, t}, "\n") : Ls()}
      %Equal.sym(Bool, String.ends_with(p, "\r"), False{}, ecr(p, N.add_eq_zero_l(cc(p, 13), SUM(t, 13), h13))) :
        {B.Text.line.if(_, p) <> B.Text.lines(R) == LS(Con{p, t}, "\n") : Ls()}
      %Equal.sym(Ls(), B.Text.lines(R), LS(t, "\n"), lines_lf(t, N.add_eq_zero_r(cc(p, 10), SUM(t, 10), h10), N.add_eq_zero_r(cc(p, 13), SUM(t, 13), h13))) :
        {B.Line{p, "\n"} <> _ == LS(Con{p, t}, "\n") : Ls()}
      {==}

# CR LF terminator: no LF in the pieces.
law lines_crlf:
  for +ps: Ss()
  for +h10: {SUM(ps, 10) == 0n : Nat}
  {B.Text.lines(Norm.recs_text(ps, "\r\n")) == LS(ps, "\r\n") : Ls()}

def lines_crlf(ps, h10):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +R = Norm.recs_text(t, "\r\n")
      +X = String.append("\n", R)
      +P2 = String.append(p, "\r")
      %LSS.sassoc(p, "\r", X) : {B.Text.lines(_) == LS(Con{p, t}, "\r\n") : Ls()}
      %Equal.sym(Ls(), B.Text.lines(String.append(P2, X)), B.Text.line(P2) <> B.Text.lines(R),
          LSS.lines_cons(P2, R, LSS.nolf_app(p, "\r", nolf_cc(p, N.add_eq_zero_l(cc(p, 10), SUM(t, 10), h10)), {==}))) :
        {_ == LS(Con{p, t}, "\r\n") : Ls()}
      %Equal.sym(B.Line, B.Text.line(P2), B.Line{p, "\r\n"}, line_cr(p)) : {_ <> B.Text.lines(R) == LS(Con{p, t}, "\r\n") : Ls()}
      %Equal.sym(Ls(), B.Text.lines(R), LS(t, "\r\n"), lines_crlf(t, N.add_eq_zero_r(cc(p, 10), SUM(t, 10), h10))) :
        {B.Line{p, "\r\n"} <> _ == LS(Con{p, t}, "\r\n") : Ls()}
      {==}

# The pieces' own LFs are none when the whole holds one per piece.
def sum0(+ps: Ss(), +term: String, +c: U32, +xs: List<&2, U32>,
  +hx: {NR.chars(xs) == Norm.recs_text(ps, term) : String}, +h1: {cc(term, c) == 1n : Nat},
  +hk: {FD.count(xs, c) == List.length(&2, String, ps) : Nat}) -> {SUM(ps, c) == 0n : Nat}:
  +L = List.length(&2, String, ps)
  N.add_cancel_r(L, SUM(ps, c), 0n,
    Equal.trans(Nat, Nat.add(SUM(ps, c), L), cc(Norm.recs_text(ps, term), c), L,
      Equal.sym(Nat, cc(Norm.recs_text(ps, term), c), Nat.add(SUM(ps, c), L), cc_recs1(ps, term, c, h1)),
      Equal.trans(Nat, cc(Norm.recs_text(ps, term), c), cc(NR.chars(xs), c), L,
        Equal.cong(String, Nat, z => cc(z, c), Norm.recs_text(ps, term), NR.chars(xs), Equal.sym(String, NR.chars(xs), Norm.recs_text(ps, term), hx)),
        Equal.trans(Nat, cc(NR.chars(xs), c), FD.count(xs, c), L, cc_chars(xs, c), hk))))

def lines_ck.k(+ps: Ss(), +xs: List<&2, U32>, +cr: Bool,
  +hx: {NR.chars(xs) == Norm.recs_text(ps, Bool.pick(String, cr, "\r\n", "\n")) : String},
  +h10: {FD.count(xs, 10) == List.length(&2, String, ps) : Nat},
  +hcr: {(cr || Nat.is_eq(FD.count(xs, 13), 0n)) == True{} : Bool}) ->
  {B.Text.lines(NR.chars(xs)) == LS(ps, Bool.pick(String, cr, "\r\n", "\n")) : Ls()}:
  match cr:
    case True{}:
      %Equal.sym(String, NR.chars(xs), Norm.recs_text(ps, "\r\n"), hx) : {B.Text.lines(_) == LS(ps, "\r\n") : Ls()}
      lines_crlf(ps, sum0(ps, "\r\n", 10, xs, hx, {==}, h10))
    case False{}:
      +h13 = Equal.trans(Nat, SUM(ps, 13), cc(Norm.recs_text(ps, "\n"), 13), 0n,
        Equal.sym(Nat, cc(Norm.recs_text(ps, "\n"), 13), SUM(ps, 13), cc_recs0(ps, "\n", 13, {==})),
        Equal.trans(Nat, cc(Norm.recs_text(ps, "\n"), 13), cc(NR.chars(xs), 13), 0n,
          Equal.cong(String, Nat, z => cc(z, 13), Norm.recs_text(ps, "\n"), NR.chars(xs), Equal.sym(String, NR.chars(xs), Norm.recs_text(ps, "\n"), hx)),
          Equal.trans(Nat, cc(NR.chars(xs), 13), FD.count(xs, 13), 0n, cc_chars(xs, 13), N.eq_sound(FD.count(xs, 13), 0n, hcr))))
      %Equal.sym(String, NR.chars(xs), Norm.recs_text(ps, "\n"), hx) : {B.Text.lines(_) == LS(ps, "\n") : Ls()}
      lines_lf(ps, sum0(ps, "\n", 10, xs, hx, {==}, h10), h13)

# The records' buffer that passed the check (xs its bytes, their text the
# pieces each with the terminator): its lines are the records, one per piece.
law lines_ck:
  for +ps: Ss()
  for +term: String
  for +cr: Bool
  for +xs: List<&2, U32>
  for +hterm: {term == Bool.pick(String, cr, "\r\n", "\n") : String}
  for +hx: {NR.chars(xs) == Norm.recs_text(ps, term) : String}
  for +h10: {FD.count(xs, 10) == List.length(&2, String, ps) : Nat}
  for +hcr: {(cr || Nat.is_eq(FD.count(xs, 13), 0n)) == True{} : Bool}
  {B.Text.lines(NR.chars(xs)) == LS(ps, term) : Ls()}

def lines_ck(ps, term, cr, xs, hterm, hx, h10, hcr):
  %Equal.sym(String, term, Bool.pick(String, cr, "\r\n", "\n"), hterm) : {B.Text.lines(NR.chars(xs)) == LS(ps, _) : Ls()}
  lines_ck.k(ps, xs, cr, {%hterm : {NR.chars(xs) == Norm.recs_text(ps, _) : String}; hx : {NR.chars(xs) == Norm.recs_text(ps, Bool.pick(String, cr, "\r\n", "\n")) : String}}, h10, hcr)
