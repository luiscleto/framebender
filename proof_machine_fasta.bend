import Base
import ./types.bend as B
import ./proof_base.bend as P
import ./proof_machine_nat.bend as PN

# Lemmas for the machine proof: a contig of a FASTA file has no more letters
# than the file has bytes (so the asks per line stay within L.bound).

# The bytes of a list of lines.
def total(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> t:
      Nat.add(String.length(l), total(t))

# Every contig has at most m letters.
def bounded(cs: List<&2, B.Contig>, +m: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case B.Contig{n, r} <> t:
      Nat.is_le(String.length(r), m) && bounded(t, m)

def mlen(x: Maybe<&2, String>) -> Nat:
  match x:
    case None{}:
      0n
    case Some{r}:
      String.length(r)

law strip_le.k:
  for +sp: Bool
  for +h: Char
  for +t: String
  for +ih: {Nat.is_le(String.length(B.Fasta.strip(t)), String.length(t)) == True{} : Bool}
  {Nat.is_le(String.length(B.Fasta.strip.put(sp, h, B.Fasta.strip(t))), 1n+String.length(t)) == True{} : Bool}

def strip_le.k(sp, h, t, ih):
  match sp:
    case True{}:
      PN.le_succ_r(String.length(B.Fasta.strip(t)), String.length(t), ih)
    case False{}:
      ih

law strip_le:
  for +s: String
  {Nat.is_le(String.length(B.Fasta.strip(s)), String.length(s)) == True{} : Bool}

def strip_le(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      strip_le.k(B.Fasta.ws(h), h, t, strip_le(t))

law seq_le.k:
  for +hd: Bool
  for +l: String
  for +t: List<&2, String>
  for +ih: {Nat.is_le(String.length(B.Fasta.seq(t)), total(t)) == True{} : Bool}
  {Nat.is_le(String.length(B.Fasta.seq.put(hd, l, B.Fasta.seq(t))), Nat.add(String.length(l), total(t))) == True{} : Bool}

def seq_le.k(hd, l, t, ih):
  match hd:
    case True{}:
      P.le_zero_l(Nat.add(String.length(l), total(t)))
    case False{}:
      %Equal.sym(Nat, String.length(String.append(B.Fasta.strip(l), B.Fasta.seq(t))),
        Nat.add(String.length(B.Fasta.strip(l)), String.length(B.Fasta.seq(t))), PN.str_len_append(B.Fasta.strip(l), B.Fasta.seq(t))) :
        {Nat.is_le(_, Nat.add(String.length(l), total(t))) == True{} : Bool}
      P.le_add(String.length(B.Fasta.strip(l)), String.length(l), String.length(B.Fasta.seq(t)), total(t), strip_le(l), ih)

law seq_le:
  for +ls: List<&2, String>
  {Nat.is_le(String.length(B.Fasta.seq(ls)), total(ls)) == True{} : Bool}

def seq_le(ls):
  match ls:
    case Nil{}:
      {==}
    case l <> t:
      seq_le.k(B.Fasta.is_head(l), l, t, seq_le(t))

law go_bounded.k:
  for +hd: Bool
  for +l: String
  for +t: List<&2, String>
  for +m: Nat
  for +h: {Nat.is_le(Nat.add(String.length(l), total(t)), m) == True{} : Bool}
  for +ih: {bounded(B.Fasta.go(t), m) == True{} : Bool}
  {bounded(B.Fasta.go.put(hd, l, t, B.Fasta.go(t)), m) == True{} : Bool}

def go_bounded.k(hd, l, t, m, h, ih):
  match hd:
    case True{}:
      PN.and_intro(Nat.is_le(String.length(B.Fasta.seq(t)), m), bounded(B.Fasta.go(t), m),
        PN.le_trans(String.length(B.Fasta.seq(t)), total(t), m, seq_le(t),
          PN.le_trans(total(t), Nat.add(String.length(l), total(t)), m,
            PN.le_add_left(total(t), String.length(l), total(t), P.le_refl(total(t))), h)),
        ih)
    case False{}:
      ih

law go_bounded:
  for +ls: List<&2, String>
  for +m: Nat
  for +h: {Nat.is_le(total(ls), m) == True{} : Bool}
  {bounded(B.Fasta.go(ls), m) == True{} : Bool}

def go_bounded(ls, m, h):
  match ls:
    case Nil{}:
      {==}
    case l <> t:
      go_bounded.k(B.Fasta.is_head(l), l, t, m, h,
        go_bounded(t, m, PN.le_trans(total(t), Nat.add(String.length(l), total(t)), m,
          PN.le_add_left(total(t), String.length(l), total(t), P.le_refl(total(t))), h)))

law keep_bounded.k:
  for +skip: Bool
  for +n: String
  for +r: String
  for +t: List<&2, B.Contig>
  for +seen: List<&2, String>
  for +m: Nat
  for +hr: {Nat.is_le(String.length(r), m) == True{} : Bool}
  for +rest: List<&2, B.Contig>
  for +ih: {bounded(rest, m) == True{} : Bool}
  {bounded(B.Fasta.keep.put(skip, n, r, t, seen, rest), m) == True{} : Bool}

def keep_bounded.k(skip, n, r, t, seen, m, hr, rest, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      PN.and_intro(Nat.is_le(String.length(r), m), bounded(rest, m), hr, ih)

law keep_bounded:
  for +cs: List<&2, B.Contig>
  for +seen: List<&2, String>
  for +m: Nat
  for +h: {bounded(cs, m) == True{} : Bool}
  {bounded(B.Fasta.keep(cs, seen), m) == True{} : Bool}

def keep_bounded(cs, seen, m, h):
  match cs:
    case Nil{}:
      {==}
    case B.Contig{n, r} <> t:
      +hr = P.and_true_l(Nat.is_le(String.length(r), m), bounded(t, m), h)
      +ht = P.and_true_r(Nat.is_le(String.length(r), m), bounded(t, m), h)
      +skip = String.is_empty(n) || B.Fasta.seen(n, seen)
      +seen2 = Bool.pick(List<&2, String>, skip, seen, n <> seen)
      keep_bounded.k(skip, n, r, t, seen, m, hr, B.Fasta.keep(t, seen2), keep_bounded(t, seen2, m, ht))

law find_bounded.k:
  for +hit: Bool
  for +r: String
  for +rest: Maybe<&2, String>
  for +m: Nat
  for +hr: {Nat.is_le(String.length(r), m) == True{} : Bool}
  for +ih: {Nat.is_le(mlen(rest), m) == True{} : Bool}
  {Nat.is_le(mlen(B.Fasta.find.put(hit, r, rest)), m) == True{} : Bool}

def find_bounded.k(hit, r, rest, m, hr, ih):
  match hit:
    case True{}:
      hr
    case False{}:
      ih

law find_bounded:
  for +fa: List<&2, B.Contig>
  for +name: String
  for +m: Nat
  for +h: {bounded(fa, m) == True{} : Bool}
  {Nat.is_le(mlen(B.Fasta.find(fa, name)), m) == True{} : Bool}

def find_bounded(fa, name, m, h):
  match fa:
    case Nil{}:
      P.le_zero_l(m)
    case B.Contig{n, r} <> t:
      +hr = P.and_true_l(Nat.is_le(String.length(r), m), bounded(t, m), h)
      +ht = P.and_true_r(Nat.is_le(String.length(r), m), bounded(t, m), h)
      find_bounded.k(String.eq(n, name), r, B.Fasta.find(t, name), m, hr, find_bounded(t, name, m, ht))

law split_total.fin:
  for +h: Char
  for +cut: Bool
  for +r: List<&2, String>
  {Nat.is_le(total(String.split.fin(h, r, cut)), 1n+total(r)) == True{} : Bool}

def split_total.fin(h, cut, r):
  match cut r:
    case True{} _:
      PN.le_succ(total(r))
    case False{} Nil{}:
      {==}
    case False{} p <> t:
      P.le_refl(1n+Nat.add(String.length(p), total(t)))

law split_total:
  for +s: String
  {Nat.is_le(total(String.split(s, '\n')), String.length(s)) == True{} : Bool}

def split_total(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      PN.le_trans(total(String.split.fin(h, String.split(t, '\n'), Char.is_eq(h, '\n'))), 1n+total(String.split(t, '\n')), 1n+String.length(t),
        split_total.fin(h, Char.is_eq(h, '\n'), String.split(t, '\n')), split_total(t))

# A contig found in a FASTA file has at most as many letters as the file has
# bytes.
law clen_le:
  for +fasta: String
  for +name: String
  {Nat.is_le(mlen(B.Fasta.find(B.Fasta.parse(fasta), name)), String.length(fasta)) == True{} : Bool}

def clen_le(fasta, name):
  +m = String.length(fasta)
  +ls = String.split(fasta, '\n')
  find_bounded(B.Fasta.parse(fasta), name, m, keep_bounded(B.Fasta.go(ls), Nil{}, m, go_bounded(ls, m, split_total(fasta))))
