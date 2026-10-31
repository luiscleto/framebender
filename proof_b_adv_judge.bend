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
import ./proof_b_alleles.bend as AA

# The fast path's verdict, at the String level: when the fields the machine
# keeps (J.pfs) pass fast_same's tests (INFO's END check among them) with a
# truthful answer, the spec's
# judge leaves the record as it is (normalized, unchanged, sorted by its
# POS). Every variable is reusable.

def RN(+p: Nat, +body: String) -> B.Res:
  B.Res{B.Normalized{}, p, body, False{}}

law fast_res:
  for +fa: List<&2, B.Contig>
  for +body: String
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +f4: String
  for +f5: String
  for +f6: String
  for +f7: String
  for +p: Nat
  for +r: List<&2, B.Base>
  for +alts: List<&2, List<&2, B.Base>>
  for +clen: Nat
  for +off: Nat
  for +raw: String
  for +hpf: {J.pfs(body) == [f0, f1, f2, f3, f4, f5, f6, f7] : List<&2, String>}
  for +h0: {String.is_empty(f0) == False{} : Bool}
  for +h1: {B.Pos.read(f1) == Some{p} : Maybe<&2, Nat>}
  for +h1s: {Nat.show(p) == f1 : String}
  for +hz: {Nat.is_eq(p, 0n) == False{} : Bool}
  for +hr: {B.Allele.read(f3) == Some{r} : Maybe<&2, List<&2, B.Base>>}
  for +ha: {B.Alleles.read(String.split(f4, ',')) == Some{alts} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  for +hl: {B.Text.is_letters(f3) == True{} : Bool}
  for +he: {B.Text.any_empty(String.split(f4, ',')) == False{} : Bool}
  for +hn: {B.Text.any_not_letters(String.split(f4, ',')) == False{} : Bool}
  for +hs3: {B.Allele.show(r) == f3 : String}
  for +hs4: {String.join(B.Alleles.show(alts), ",") == f4 : String}
  for +hd: {B.Alleles.distinct(r <> alts) == True{} : Bool}
  for +hv: {V.var_in(off, B.Bases.of_fasta(raw), B.Var{p, r, alts}) == Some{B.Var{p, r, alts}} : Maybe<&2, B.Var>}
  for +hc: {J.ref_check(clen, off, B.Bases.of_fasta(raw), Nat.sub(p, 1n), r) == Some{True{}} : Maybe<&2, Bool>}
  for +ht: {WS.truthful(fa, WS.chrom_of(body), Some{J.Known{clen, off, raw}}) == True{} : Bool}
  for +hend: {J.end_ok(f7, Nat.sub(Nat.add(p, String.length(f3)), 1n)) == True{} : Bool}
  {L.judge(fa, body) == RN(B.Rec.pos(B.Rec.fields(body)), body) : B.Res}

def fast_res(fa, body, f0, f1, f2, f3, f4, f5, f6, f7, p, r, alts, clen, off, raw, hpf, h0, h1, h1s, hz, hr, ha, hl, he, hn, hs3, hs4, hd, hv, hc, ht, hend):
  +a = {Some{J.Known{clen, off, raw}} : Maybe<&2, J.Ans>}
  +P0 = B.Rec.pos(B.Rec.fields(body))
  +es = {%Equal.sym(List<&2, String>, J.pfs(body), [f0, f1, f2, f3, f4, f5, f6, f7], hpf) : {J.fast(a, _, body) == J.Same{} : J.Fast};
    AA.fast_same(f0, f1, f2, f3, f4, f5, f6, f7, body, p, r, alts, clen, off, raw, h0, h1, h1s, hz, hr, ha, hl, he, hn, hs3, hs4, hd, hv, hc, hend) : {J.fast(a, J.pfs(body), body) == J.Same{} : J.Fast}}
  +ej = Equal.trans(Maybe<&2, B.Res>, J.judge_in(a, body), PF.fr_res(J.fast(a, J.pfs(body), body), P0, body), Some{RN(P0, body)},
    Equal.sym(Maybe<&2, B.Res>, PF.fr_res(J.fast(a, J.pfs(body), body), P0, body), J.judge_in(a, body), PF.fast_judge(a, body)),
    Equal.cong(J.Fast, Maybe<&2, B.Res>, f => PF.fr_res(f, P0, body), J.fast(a, J.pfs(body), body), J.Same{}, es))
  Equal.sym(B.Res, RN(P0, body), L.judge(fa, body), PW.window(fa, body, a, RN(P0, body), ht, ej))
