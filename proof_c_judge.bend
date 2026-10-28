import Base
import ./types.bend as B
import ./run.bend as R
import ./LAWS.bend as L
import ./tan.bend as V
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./proof_window_defs.bend as WS
import ./proof_window.bend as PW
import ./proof_fast.bend as PF

# Phase C: the rewrite path's verdict, at the String level (as
# proof_b_adv_judge.bend's fast_res for the fast path): when the fields the
# machine keeps (J.pfs) pass the tests and var_in on a truthful answer gives a
# variant that is not the record as written, the spec's judge rewrites the
# record to it (Rec.rebuild), with no stale flag. Every variable is reusable.

def RW(+w: B.Var, +v: B.Var, +body: String) -> B.Res:
  B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(B.Rec.fields(body), v, w), False{}}

law fix_fast:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +body: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +alts: List<&2, List<&2, B.Base>>
  for +clen: Nat
  for +off: Nat
  for +raw: String
  for +w: B.Var
  for +h0: {String.is_empty(f0) == False{} : Bool}
  for +h1: {B.Pos.read(f1) == Some{p} : Maybe<&2, Nat>}
  for +hz: {Nat.is_eq(p, 0n) == False{} : Bool}
  for +hr: {B.Allele.read(f3) == Some{r} : Maybe<&2, List<&2, B.Base>>}
  for +ha: {B.Alleles.read(String.split(f4, ',')) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  for +hl: {B.Text.is_letters(f3) == True{} : Bool}
  for +he: {B.Text.any_empty(String.split(f4, ',')) == False{} : Bool}
  for +hn: {B.Text.any_not_letters(String.split(f4, ',')) == False{} : Bool}
  for +hd: {B.Alleles.distinct(r <> alts) == True{} : Bool}
  for +hv: {V.var_in(off, B.Bases.of_fasta(raw), B.Var{p, r, alts}) == Some{w} : Maybe<&2, B.Var>}
  for +hc: {J.ref_check(clen, off, B.Bases.of_fasta(raw), Nat.sub(p, 1n), r) == Some{True{}} : Maybe<&2, Bool>}
  for +hns: {Bool.and(B.Rec.same_var(B.Var{p, r, alts}, w), J.same.text(f1, f3, f4, B.Var{p, r, alts})) == False{} : Bool}
  for +hst: {B.Rec.stale(B.Rec.fields(body), B.Var{p, r, alts}, w) == False{} : Bool}
  {J.fast(Some{J.Known{clen, off, raw}}, [f0, f1, f2, f3, f4, f5, f6, ""], body) == J.Other{Some{RW(w, B.Var{p, r, alts}, body)}} : J.Fast}

def fix_fast(f0, f1, f2, f3, f4, f5, f6, body, p, r, alts, clen, off, raw, w, h0, h1, hz, hr, ha, hl, he, hn, hd, hv, hc, hns, hst):
  +e1 = Equal.sym(Maybe<&2, Nat>, B.Pos.read(f1), Some{p}, h1)
  +a = {Some{J.Known{clen, off, raw}} : Maybe<&2, J.Ans>}
  +FS = {[f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}
  +s4 = String.split(f4, ',')
  +G = {J.Other{Some{RW(w, B.Var{p, r, alts}, body)}} : J.Fast}
  %Equal.sym(Bool, String.is_empty(f0), False{}, h0) :
    {J.fast.go(Bool.or(Bool.or(Bool.or(_, Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1)))), Bool.not(B.Text.is_letters(f3))), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.is_letters(f3), True{}, hl) :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, B.Pos.read(f1))), Bool.not(_)), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == G : J.Fast}
  %e1 :
    {J.fast.go(Bool.or(Bool.or(Bool.not(Maybe.is_some(&2, Nat, _)), False{}), B.Text.any_empty(s4)), B.Text.any_not_letters(s4), a, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.any_empty(s4), False{}, he) :
    {J.fast.go(_, B.Text.any_not_letters(s4), a, FS, body) == G : J.Fast}
  %Equal.sym(Bool, B.Text.any_not_letters(s4), False{}, hn) :
    {J.fast.go(False{}, _, a, FS, body) == G : J.Fast}
  +bs = B.Bases.of_fasta(raw)
  %Equal.sym(Maybe<&2, List<&2, B.Base>>, B.Allele.read(f3), Some{r}, hr) :
    {J.fast.found(True{}, _, B.Alleles.read(s4), clen, off, bs, Maybe.default(&2, Nat, B.Pos.read(f1), 0n), f1, f3, f4, body) == G : J.Fast}
  %Equal.sym(Maybe<&2, List<&2, List<&2, B.Base>>>, B.Alleles.read(s4), Some{alts}, ha) :
    {J.fast.found(True{}, Some{r}, _, clen, off, bs, Maybe.default(&2, Nat, B.Pos.read(f1), 0n), f1, f3, f4, body) == G : J.Fast}
  %e1 :
    {J.fast.found(True{}, Some{r}, Some{alts}, clen, off, bs, Maybe.default(&2, Nat, _, 0n), f1, f3, f4, body) == G : J.Fast}
  +v = {B.Var{p, r, alts} : B.Var}
  %Equal.sym(Bool, Nat.is_eq(p, 0n), False{}, hz) :
    {J.fast.problem(_, B.Alleles.distinct(r <> alts), clen, off, bs, f1, f3, f4, v, p, body) == G : J.Fast}
  %Equal.sym(Bool, B.Alleles.distinct(r <> alts), True{}, hd) :
    {J.fast.problem(False{}, _, clen, off, bs, f1, f3, f4, v, p, body) == G : J.Fast}
  %Equal.sym(Maybe<&2, Bool>, J.ref_check(clen, off, bs, Nat.sub(p, 1n), r), Some{True{}}, hc) :
    {J.fast.ref(_, off, bs, f1, f3, f4, v, p, body) == G : J.Fast}
  %Equal.sym(Maybe<&2, B.Var>, V.var_in(off, bs, v), Some{w}, hv) :
    {J.fast.norm(_, f1, f3, f4, v, body) == G : J.Fast}
  %Equal.sym(Bool, Bool.and(B.Rec.same_var(v, w), J.same.text(f1, f3, f4, v)), False{}, hns) :
    {J.fast.norm.k(_, v, w, body) == G : J.Fast}
  %Equal.sym(Bool, B.Rec.stale(B.Rec.fields(body), v, w), False{}, hst) :
    {J.Other{Some{B.Res{B.Normalized{}, B.Var.pos(w), B.Rec.rebuild(B.Rec.fields(body), v, w), _}}} == G : J.Fast}
  {==}

law fix_res:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +alts: List<&2, List<&2, B.Base>>
  for +clen: Nat
  for +off: Nat
  for +raw: String
  for +w: B.Var
  for +hpf: {J.pfs(body) == [f0, f1, f2, f3, f4, f5, f6, ""] : List<&2, String>}
  for +h0: {String.is_empty(f0) == False{} : Bool}
  for +h1: {B.Pos.read(f1) == Some{p} : Maybe<&2, Nat>}
  for +hz: {Nat.is_eq(p, 0n) == False{} : Bool}
  for +hr: {B.Allele.read(f3) == Some{r} : Maybe<&2, List<&2, B.Base>>}
  for +ha: {B.Alleles.read(String.split(f4, ',')) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  for +hl: {B.Text.is_letters(f3) == True{} : Bool}
  for +he: {B.Text.any_empty(String.split(f4, ',')) == False{} : Bool}
  for +hn: {B.Text.any_not_letters(String.split(f4, ',')) == False{} : Bool}
  for +hd: {B.Alleles.distinct(r <> alts) == True{} : Bool}
  for +hv: {V.var_in(off, B.Bases.of_fasta(raw), B.Var{p, r, alts}) == Some{w} : Maybe<&2, B.Var>}
  for +hc: {J.ref_check(clen, off, B.Bases.of_fasta(raw), Nat.sub(p, 1n), r) == Some{True{}} : Maybe<&2, Bool>}
  for +hns: {Bool.and(B.Rec.same_var(B.Var{p, r, alts}, w), J.same.text(f1, f3, f4, B.Var{p, r, alts})) == False{} : Bool}
  for +hst: {B.Rec.stale(B.Rec.fields(body), B.Var{p, r, alts}, w) == False{} : Bool}
  for +ht: {WS.truthful(fa, WS.chrom_of(body), Some{J.Known{clen, off, raw}}) == True{} : Bool}
  {L.judge(fa, body) == RW(w, B.Var{p, r, alts}, body) : B.Res}

def fix_res(fa, body, f0, f1, f2, f3, f4, f5, f6, p, r, alts, clen, off, raw, w, hpf, h0, h1, hz, hr, ha, hl, he, hn, hd, hv, hc, hns, hst, ht):
  +a = {Some{J.Known{clen, off, raw}} : Maybe<&2, J.Ans>}
  +P0 = B.Rec.pos(B.Rec.fields(body))
  +RR = RW(w, B.Var{p, r, alts}, body)
  +es = {%Equal.sym(List<&2, String>, J.pfs(body), [f0, f1, f2, f3, f4, f5, f6, ""], hpf) : {J.fast(a, _, body) == J.Other{Some{RR}} : J.Fast};
    fix_fast(f0, f1, f2, f3, f4, f5, f6, body, p, r, alts, clen, off, raw, w, h0, h1, hz, hr, ha, hl, he, hn, hd, hv, hc, hns, hst) : {J.fast(a, J.pfs(body), body) == J.Other{Some{RR}} : J.Fast}}
  +ej = Equal.trans(Maybe<&2, B.Res>, J.judge_in(a, body), PF.fr_res(J.fast(a, J.pfs(body), body), P0, body), Some{RR},
    Equal.sym(Maybe<&2, B.Res>, PF.fr_res(J.fast(a, J.pfs(body), body), P0, body), J.judge_in(a, body), PF.fast_judge(a, body)),
    Equal.cong(J.Fast, Maybe<&2, B.Res>, f => PF.fr_res(f, P0, body), J.fast(a, J.pfs(body), body), J.Other{Some{RR}}, es))
  Equal.sym(B.Res, RR, L.judge(fa, body), PW.window(fa, body, a, RR, ht, ej))
