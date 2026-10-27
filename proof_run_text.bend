import Base
import ./types.bend as B
import ./proof_base.bend as P
import ./proof_run_base.bend as Q
import ./proof_run_sort.bend as S

# Text facts for twice_run: a good line's text splits back into the same line
# (B.Text.lines), and every line B.Text.lines gives is good.

def lapp(xs: List<&2, B.Line>, ys: List<&2, B.Line>) -> List<&2, B.Line>:
  List.append(&2, B.Line, xs, ys)

# Chars
# =====

law char_eq_sound:
  for +a: Char
  for +b: Char
  for e: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

def char_eq_sound(a, b, e):
  match a b:
    case Chr{U32{+x}} Chr{U32{+y}}:
      %Q.word_eq(32n, x, y, Q.is_eq_true(Word.cmp(32n, x, y), e)) : {Chr{U32{x}} == Chr{U32{_}} : Char}
      {==}

law char_eq_refl:
  for +a: Char
  {Char.is_eq(a, a) == True{} : Bool}

def char_eq_refl(a):
  match a:
    case Chr{U32{+x}}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, Q.word_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# s has no char c.
def no_c(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.not(Char.is_eq(h, c)) && no_c(t, c)

law no_c_app:
  for +a: String
  for +b: String
  for +c: Char
  for +ha: {no_c(a, c) == True{} : Bool}
  for +hb: {no_c(b, c) == True{} : Bool}
  {no_c(a ++ b, c) == True{} : Bool}

def no_c_app(a, b, c, ha, hb):
  match a:
    case SNil{}:
      hb
    case SCon{+h, +t}:
      S.and_intro(Bool.not(Char.is_eq(h, c)), no_c(t ++ b, c),
        P.and_true_l(Bool.not(Char.is_eq(h, c)), no_c(t, c), ha),
        no_c_app(t, b, c, P.and_true_r(Bool.not(Char.is_eq(h, c)), no_c(t, c), ha), hb))

# Splitting
# =========

def split.cut(+c: Char, +s: String, x: Bool, ex: {Char.is_eq(c, c) == x : Bool}) ->
  {String.split.fin(c, String.split(s, c), x) == SNil{} <> String.split(s, c) : List<&2, String>}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({String.split.fin(c, String.split(s, c), False{}) == SNil{} <> String.split(s, c) : List<&2, String>},
        P.true_ne_false(Equal.trans(Bool, True{}, Char.is_eq(c, c), False{}, Equal.sym(Bool, Char.is_eq(c, c), True{}, char_eq_refl(c)), ex)))

# Text without c, then c, splits at that c.
law split_app:
  for +b: String
  for +s: String
  for +c: Char
  for +h: {no_c(b, c) == True{} : Bool}
  {String.split(b ++ SCon{c, s}, c) == b <> String.split(s, c) : List<&2, String>}

def split_app(b, s, c, h):
  match b:
    case SNil{}:
      split.cut(c, s, Char.is_eq(c, c), {==})
    case SCon{+x, +t}:
      +nx = P.not_true(Char.is_eq(x, c), P.and_true_l(Bool.not(Char.is_eq(x, c)), no_c(t, c), h))
      %Equal.sym(Bool, Char.is_eq(x, c), False{}, nx) :
        {String.split.fin(x, String.split(t ++ SCon{c, s}, c), _) == SCon{x, t} <> String.split(s, c) : List<&2, String>}
      %Equal.sym(List<&2, String>, String.split(t ++ SCon{c, s}, c), t <> String.split(s, c),
        split_app(t, s, c, P.and_true_r(Bool.not(Char.is_eq(x, c)), no_c(t, c), h))) :
        {String.split.push(x, _) == SCon{x, t} <> String.split(s, c) : List<&2, String>}
      {==}

def List.disc_nil(-A: Data, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      Empty

law cons_ne_nil:
  for -A: Data
  for -x: A
  for -xs: List<&2, A>
  for e: {x <> xs == Nil{} : List<&2, A>}
  Empty

def cons_ne_nil(A, x, xs, e):
  %Equal.sym(List<&2, A>, x <> xs, Nil{}, e) : List.disc_nil(A, _)
  Unit{}

def split_nn.push(+h: Char, ps: List<&2, String>, e: {String.split.push(h, ps) == Nil{} : List<&2, String>}) -> Empty:
  match ps:
    case Nil{}:
      cons_ne_nil(String, SCon{h, SNil{}}, Nil{}, e)
    case p <> t:
      cons_ne_nil(String, SCon{h, p}, t, e)

def split_nn.fin(+h: Char, ps: List<&2, String>, x: Bool, e: {String.split.fin(h, ps, x) == Nil{} : List<&2, String>}) -> Empty:
  match x:
    case True{}:
      cons_ne_nil(String, SNil{}, ps, e)
    case False{}:
      split_nn.push(h, ps, e)

# A split has at least one piece.
law split_nn:
  for +s: String
  for +c: Char
  for e: {String.split(s, c) == Nil{} : List<&2, String>}
  Empty

def split_nn(s, c, e):
  match s:
    case SNil{}:
      cons_ne_nil(String, SNil{}, Nil{}, e)
    case SCon{+h, t}:
      split_nn.fin(h, String.split(t, c), Char.is_eq(h, c), e)

def lines_prepend.go(+b: String, ps: List<&2, String>, ne: {ps == Nil{} : List<&2, String>} -> Empty) ->
  {B.Text.lines.start(b <> ps) == B.Text.line(b) <> B.Text.lines.start(ps) : List<&2, B.Line>}:
  match ps:
    case Nil{}:
      Empty.absurd({B.Text.lines.start(b <> Nil{}) == B.Text.line(b) <> B.Text.lines.start(Nil{}) : List<&2, B.Line>}, ne({==}))
    case q <> t:
      {==}

law lines_prepend:
  for +b: String
  for +s: String
  {B.Text.lines.start(b <> String.split(s, '\n')) == B.Text.line(b) <> B.Text.lines(s) : List<&2, B.Line>}

def lines_prepend(b, s):
  lines_prepend.go(b, String.split(s, '\n'), e => split_nn(s, '\n', e))

# Strings ending with CR
# ======================

law rev_app:
  for +b: String
  for +c: String
  for +acc: String
  {String.reverse.go(b ++ c, acc) == String.reverse.go(c, String.reverse.go(b, acc)) : String}

def rev_app(b, c, acc):
  match b:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rev_app(t, c, SCon{h, acc})

law ends_cr_app:
  for +b: String
  {String.ends_with(b ++ "\r", "\r") == True{} : Bool}

def ends_cr_app(b):
  %Equal.sym(String, String.reverse.go(b ++ "\r", SNil{}), String.reverse.go("\r", String.reverse.go(b, SNil{})), rev_app(b, "\r", SNil{})) :
    {String.starts_with(_, "\r") == True{} : Bool}
  {==}

law take_app_cr:
  for +b: String
  {String.take(b ++ "\r", Nat.sub(String.length(b ++ "\r"), 1n)) == b : String}

def take_app_cr.go(+b: String) -> {String.take(b ++ "\r", String.length(b)) == b : String}:
  match b:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %take_app_cr.go(t) : {SCon{h, String.take(t ++ "\r", String.length(t))} == SCon{h, _} : String}
      {==}

def len_app_cr(+b: String) -> {String.length(b ++ "\r") == 1n+String.length(b) : Nat}:
  match b:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %len_app_cr(t) : {1n+String.length(t ++ "\r") == 1n+_ : Nat}
      {==}

def take_app_cr(b):
  %Equal.sym(Nat, String.length(b ++ "\r"), 1n+String.length(b), len_app_cr(b)) :
    {String.take(b ++ "\r", Nat.sub(_, 1n)) == b : String}
  %Equal.sym(Nat, Nat.sub(String.length(b), 0n), String.length(b), P.sub_zero(String.length(b))) :
    {String.take(b ++ "\r", _) == b : String}
  take_app_cr.go(b)

# Good lines
# ==========

# A line that B.Text.lines gives back from its text: no LF in the body, and a
# CR LF terminator or an LF one after a body not ending with CR.
def goodb(l: B.Line) -> Bool:
  match l:
    case B.Line{+b, +t}:
      no_c(b, '\n') && (String.eq(t, "\r\n") || (String.eq(t, "\n") && Bool.not(String.ends_with(b, "\r"))))

def all_good(ls: List<&2, B.Line>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> t:
      goodb(l) && all_good(t)

def good_line.lf(+b: String, +s: String, +ef: {String.ends_with(b, "\r") == False{} : Bool},
  +hn: {no_c(b, '\n') == True{} : Bool}) ->
  {B.Text.lines((b ++ "\n") ++ s) == B.Line{b, "\n"} <> B.Text.lines(s) : List<&2, B.Line>}:
  %Equal.sym(String, (b ++ "\n") ++ s, b ++ ("\n" ++ s), Q.s_append_assoc(b, "\n", s)) : {B.Text.lines(_) == B.Line{b, "\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(List<&2, String>, String.split(b ++ SCon{'\n', s}, '\n'), b <> String.split(s, '\n'), split_app(b, s, '\n', hn)) :
    {B.Text.lines.start(_) == B.Line{b, "\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines.start(b <> String.split(s, '\n')), B.Text.line(b) <> B.Text.lines(s), lines_prepend(b, s)) :
    {_ == B.Line{b, "\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(Bool, String.ends_with(b, "\r"), False{}, ef) : {B.Text.line.if(_, b) <> B.Text.lines(s) == B.Line{b, "\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  {==}

def good_line.crlf(+b: String, +s: String, +hn: {no_c(b, '\n') == True{} : Bool}) ->
  {B.Text.lines((b ++ "\r\n") ++ s) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}:
  +bc = b ++ "\r"
  +hc = no_c_app(b, "\r", '\n', hn, {==})
  %Equal.sym(String, (b ++ "\r\n") ++ s, b ++ ("\r\n" ++ s), Q.s_append_assoc(b, "\r\n", s)) : {B.Text.lines(_) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Q.s_append_assoc(b, "\r", SCon{'\n', s}) : {B.Text.lines(_) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(List<&2, String>, String.split(bc ++ SCon{'\n', s}, '\n'), bc <> String.split(s, '\n'), split_app(bc, s, '\n', hc)) :
    {B.Text.lines.start(_) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines.start(bc <> String.split(s, '\n')), B.Text.line(bc) <> B.Text.lines(s), lines_prepend(bc, s)) :
    {_ == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(Bool, String.ends_with(bc, "\r"), True{}, ends_cr_app(b)) : {B.Text.line.if(_, bc) <> B.Text.lines(s) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  %Equal.sym(String, String.take(bc, Nat.sub(String.length(bc), 1n)), b, take_app_cr(b)) :
    {B.Line{_, "\r\n"} <> B.Text.lines(s) == B.Line{b, "\r\n"} <> B.Text.lines(s) : List<&2, B.Line>}
  {==}

def good_line.go(+b: String, +t: String, +s: String, +hn: {no_c(b, '\n') == True{} : Bool}, +x: Bool,
  +ex: {String.eq(t, "\r\n") == x : Bool},
  +h: {Bool.or(x, Bool.and(String.eq(t, "\n"), Bool.not(String.ends_with(b, "\r")))) == True{} : Bool}) ->
  {B.Text.lines((b ++ t) ++ s) == B.Line{b, t} <> B.Text.lines(s) : List<&2, B.Line>}:
  match x:
    case True{}:
      %Equal.sym(String, t, "\r\n", Q.str_eq_sound(t, "\r\n", ex)) :
        {B.Text.lines((b ++ _) ++ s) == B.Line{b, _} <> B.Text.lines(s) : List<&2, B.Line>}
      good_line.crlf(b, s, hn)
    case False{}:
      +h1 = P.and_true_l(String.eq(t, "\n"), Bool.not(String.ends_with(b, "\r")), h)
      +h2 = P.not_true(String.ends_with(b, "\r"), P.and_true_r(String.eq(t, "\n"), Bool.not(String.ends_with(b, "\r")), h))
      %Equal.sym(String, t, "\n", Q.str_eq_sound(t, "\n", h1)) :
        {B.Text.lines((b ++ _) ++ s) == B.Line{b, _} <> B.Text.lines(s) : List<&2, B.Line>}
      good_line.lf(b, s, h2, hn)

# A good line's text, then anything: the line, then the lines of the rest.
law good_line:
  for +l: B.Line
  for +s: String
  for +h: {goodb(l) == True{} : Bool}
  {B.Text.lines(B.Line.text(l) ++ s) == l <> B.Text.lines(s) : List<&2, B.Line>}

def good_line(l, s, h):
  match l:
    case B.Line{+b, +t}:
      +rest = Bool.or(String.eq(t, "\r\n"), Bool.and(String.eq(t, "\n"), Bool.not(String.ends_with(b, "\r"))))
      good_line.go(b, t, s, P.and_true_l(no_c(b, '\n'), rest, h), String.eq(t, "\r\n"), {==}, P.and_true_r(no_c(b, '\n'), rest, h))

law lines_text_app:
  for +ls: List<&2, B.Line>
  for +s: String
  for +h: {all_good(ls) == True{} : Bool}
  {B.Text.lines(B.Lines.text(ls) ++ s) == lapp(ls, B.Text.lines(s)) : List<&2, B.Line>}

def lines_text_app(ls, s, h):
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      +h1 = P.and_true_l(goodb(l), all_good(t), h)
      +h2 = P.and_true_r(goodb(l), all_good(t), h)
      %Equal.sym(String, (B.Line.text(l) ++ B.Lines.text(t)) ++ s, B.Line.text(l) ++ (B.Lines.text(t) ++ s),
        Q.s_append_assoc(B.Line.text(l), B.Lines.text(t), s)) : {B.Text.lines(_) == l <> lapp(t, B.Text.lines(s)) : List<&2, B.Line>}
      %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Line.text(l) ++ (B.Lines.text(t) ++ s)), l <> B.Text.lines(B.Lines.text(t) ++ s),
        good_line(l, B.Lines.text(t) ++ s, h1)) : {_ == l <> lapp(t, B.Text.lines(s)) : List<&2, B.Line>}
      %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(t) ++ s), lapp(t, B.Text.lines(s)), lines_text_app(t, s, h2)) :
        {l <> _ == l <> lapp(t, B.Text.lines(s)) : List<&2, B.Line>}
      {==}

# The lines of good lines' text are those lines.
law lines_text:
  for +ls: List<&2, B.Line>
  for +h: {all_good(ls) == True{} : Bool}
  {B.Text.lines(B.Lines.text(ls)) == ls : List<&2, B.Line>}

def lines_text(ls, h):
  %Q.s_append_nil(B.Lines.text(ls)) : {B.Text.lines(_) == ls : List<&2, B.Line>}
  %Equal.sym(List<&2, B.Line>, B.Text.lines(B.Lines.text(ls) ++ ""), lapp(ls, B.Text.lines("")), lines_text_app(ls, "", h)) : {_ == ls : List<&2, B.Line>}
  P.append_nil(B.Line, ls)

# Every line of a text is good
# ============================

def all_noc(ps: List<&2, String>, +c: Char) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      no_c(p, c) && all_noc(t, c)

def pieces_noc.push(+h: Char, +c: Char, ps: List<&2, String>, +nh: {Char.is_eq(h, c) == False{} : Bool},
  +ih: {all_noc(ps, c) == True{} : Bool}) -> {all_noc(String.split.push(h, ps), c) == True{} : Bool}:
  match ps:
    case Nil{}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, nh) : {Bool.and(Bool.and(Bool.not(_), True{}), True{}) == True{} : Bool}
      {==}
    case +p <> +r:
      S.and_intro(no_c(SCon{h, p}, c), all_noc(r, c),
        S.and_intro(Bool.not(Char.is_eq(h, c)), no_c(p, c), (%Equal.sym(Bool, Char.is_eq(h, c), False{}, nh) : {Bool.not(_) == True{} : Bool}; {==}),
          P.and_true_l(no_c(p, c), all_noc(r, c), ih)),
        P.and_true_r(no_c(p, c), all_noc(r, c), ih))

def pieces_noc.fin(+h: Char, +c: Char, ps: List<&2, String>, +x: Bool, +ex: {Char.is_eq(h, c) == x : Bool},
  +ih: {all_noc(ps, c) == True{} : Bool}) -> {all_noc(String.split.fin(h, ps, x), c) == True{} : Bool}:
  match x:
    case True{}:
      ih
    case False{}:
      pieces_noc.push(h, c, ps, ex, ih)

# The pieces of a split have no separator.
law pieces_noc:
  for +s: String
  for +c: Char
  {all_noc(String.split(s, c), c) == True{} : Bool}

def pieces_noc(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      pieces_noc.fin(h, c, String.split(t, c), Char.is_eq(h, c), {==}, pieces_noc(t, c))

law no_c_take:
  for +p: String
  for +n: Nat
  for +c: Char
  for +h: {no_c(p, c) == True{} : Bool}
  {no_c(String.take(p, n), c) == True{} : Bool}

def no_c_take(p, n, c, h):
  match p n:
    case SNil{} _:
      {==}
    case SCon{+x, +t} 0n:
      {==}
    case SCon{+x, +t} 1n+k:
      S.and_intro(Bool.not(Char.is_eq(x, c)), no_c(String.take(t, k), c),
        P.and_true_l(Bool.not(Char.is_eq(x, c)), no_c(t, c), h),
        no_c_take(t, k, c, P.and_true_r(Bool.not(Char.is_eq(x, c)), no_c(t, c), h)))

def line_good.go(+p: String, +h: {no_c(p, '\n') == True{} : Bool}, +x: Bool, +ex: {String.ends_with(p, "\r") == x : Bool}) ->
  {goodb(B.Text.line.if(x, p)) == True{} : Bool}:
  match x:
    case True{}:
      S.and_intro(no_c(String.take(p, Nat.sub(String.length(p), 1n)), '\n'), True{},
        no_c_take(p, Nat.sub(String.length(p), 1n), '\n', h), {==})
    case False{}:
      %Equal.sym(Bool, String.ends_with(p, "\r"), False{}, ex) :
        {Bool.and(no_c(p, '\n'), Bool.or(String.eq("\n", "\r\n"), Bool.and(String.eq("\n", "\n"), Bool.not(_)))) == True{} : Bool}
      S.and_intro(no_c(p, '\n'), True{}, h, {==})

law line_good:
  for +p: String
  for +h: {no_c(p, '\n') == True{} : Bool}
  {goodb(B.Text.line(p)) == True{} : Bool}

def line_good(p, h):
  line_good.go(p, h, String.ends_with(p, "\r"), {==})

def lines_go_good(ps: List<&2, String>, +p: String, +hp: {no_c(p, '\n') == True{} : Bool},
  +hps: {all_noc(ps, '\n') == True{} : Bool}) -> {all_good(B.Text.lines.go(ps, p)) == True{} : Bool}:
  match ps:
    case Nil{}:
      match p:
        case SNil{}:
          {==}
        case SCon{+h, +t}:
          S.and_intro(goodb(B.Text.line(SCon{h, t})), True{}, line_good(SCon{h, t}, hp), {==})
    case +q <> +t:
      S.and_intro(goodb(B.Text.line(p)), all_good(B.Text.lines.go(t, q)), line_good(p, hp),
        lines_go_good(t, q, P.and_true_l(no_c(q, '\n'), all_noc(t, '\n'), hps), P.and_true_r(no_c(q, '\n'), all_noc(t, '\n'), hps)))

def lines_good.go(ps: List<&2, String>, +hps: {all_noc(ps, '\n') == True{} : Bool}) ->
  {all_good(B.Text.lines.start(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      lines_go_good(t, p, P.and_true_l(no_c(p, '\n'), all_noc(t, '\n'), hps), P.and_true_r(no_c(p, '\n'), all_noc(t, '\n'), hps))

# Every line of a text is good.
law lines_good:
  for +s: String
  {all_good(B.Text.lines(s)) == True{} : Bool}

def lines_good(s):
  lines_good.go(String.split(s, '\n'), pieces_noc(s, '\n'))
