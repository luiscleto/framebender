import Base
import ./types.bend as B
import ./bytes_enc.bend as E
import ./proof_b_cachedefs.bend as PC
import ./proof_b_lines_str.bend as LS
import ./proof_b_lines_pd.bend as LP
import lawful-arrays@0.1.0.0/proof_base.bend as AB

# B.Fasta.parse keeps the file's bytes: every contig's letters are a header
# line's following lines (split at LF) with their spaces, tabs and CRs
# dropped (Fasta.strip), so a file of bytes gives contigs of bytes
# (fa_bytes_parse, proof_b_assemble.bend).

# Splitting at LF
# ===============

def push_bytes(+h: Char, +ps: List<&2, String>, +hh: {U32.is_lt(Char.to_u32(h), 256) == True{} : Bool},
  +hp: {E.all_bytes(ps) == True{} : Bool}) ->
  {E.all_bytes(String.split.push(h, ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      LP.and_tt(Bool.and(U32.is_lt(Char.to_u32(h), 256), True{}), True{}, LP.and_tt(U32.is_lt(Char.to_u32(h), 256), True{}, hh, {==}), {==})
    case +q <> +r:
      +hq = AB.and_true_l(E.is_bytes(q), E.all_bytes(r), hp)
      +hr = AB.and_true_r(E.is_bytes(q), E.all_bytes(r), hp)
      LP.and_tt(E.is_bytes(SCon{h, q}), E.all_bytes(r), LP.and_tt(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(q), hh, hq), hr)

def fin_bytes(+h: Char, +ps: List<&2, String>, +cut: Bool, +hh: {U32.is_lt(Char.to_u32(h), 256) == True{} : Bool},
  +hp: {E.all_bytes(ps) == True{} : Bool}) ->
  {E.all_bytes(String.split.fin(h, ps, cut)) == True{} : Bool}:
  match cut:
    case True{}:
      hp
    case False{}:
      push_bytes(h, ps, hh, hp)

def split_bytes(+s: String, +hb: {E.is_bytes(s) == True{} : Bool}) ->
  {E.all_bytes(String.split(s, '\n')) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      fin_bytes(h, String.split(t, '\n'), Char.is_eq(h, '\n'),
        AB.and_true_l(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb),
        split_bytes(t, AB.and_true_r(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb)))

# A sequence line's letters
# =========================

def strip_put(+sp: Bool, +h: Char, +rest: String, +hh: {U32.is_lt(Char.to_u32(h), 256) == True{} : Bool},
  +hr: {E.is_bytes(rest) == True{} : Bool}) ->
  {E.is_bytes(B.Fasta.strip.put(sp, h, rest)) == True{} : Bool}:
  match sp:
    case True{}:
      hr
    case False{}:
      LP.and_tt(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(rest), hh, hr)

def strip_bytes(+s: String, +hb: {E.is_bytes(s) == True{} : Bool}) ->
  {E.is_bytes(B.Fasta.strip(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      strip_put(B.Fasta.ws(h), h, B.Fasta.strip(t),
        AB.and_true_l(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb),
        strip_bytes(t, AB.and_true_r(U32.is_lt(Char.to_u32(h), 256), E.is_bytes(t), hb)))

def seq_put(+hd: Bool, +l: String, +rest: String, +hl: {E.is_bytes(l) == True{} : Bool},
  +hr: {E.is_bytes(rest) == True{} : Bool}) ->
  {E.is_bytes(B.Fasta.seq.put(hd, l, rest)) == True{} : Bool}:
  match hd:
    case True{}:
      {==}
    case False{}:
      LS.bytes_app(B.Fasta.strip(l), rest, strip_bytes(l, hl), hr)

def seq_bytes(+ls: List<&2, String>, +hb: {E.all_bytes(ls) == True{} : Bool}) ->
  {E.is_bytes(B.Fasta.seq(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      seq_put(B.Fasta.is_head(l), l, B.Fasta.seq(t),
        AB.and_true_l(E.is_bytes(l), E.all_bytes(t), hb),
        seq_bytes(t, AB.and_true_r(E.is_bytes(l), E.all_bytes(t), hb)))

# The contigs
# ===========

def go_put(+hd: Bool, +l: String, +t: List<&2, String>, +rest: List<&2, B.Contig>,
  +ht: {E.all_bytes(t) == True{} : Bool}, +hr: {PC.fa_bytes(rest) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.go.put(hd, l, t, rest)) == True{} : Bool}:
  match hd:
    case True{}:
      LP.and_tt(E.is_bytes(B.Fasta.seq(t)), PC.fa_bytes(rest), seq_bytes(t, ht), hr)
    case False{}:
      hr

def go_bytes(+ls: List<&2, String>, +hb: {E.all_bytes(ls) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.go(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case +l <> +t:
      +ht = AB.and_true_r(E.is_bytes(l), E.all_bytes(t), hb)
      go_put(B.Fasta.is_head(l), l, t, B.Fasta.go(t), ht, go_bytes(t, ht))

def keep_put(+skip: Bool, +n: String, +r: String, +t: List<&2, B.Contig>, +seen: List<&2, String>, +rest: List<&2, B.Contig>,
  +hr: {E.is_bytes(r) == True{} : Bool}, +hrest: {PC.fa_bytes(rest) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.keep.put(skip, n, r, t, seen, rest)) == True{} : Bool}:
  match skip:
    case True{}:
      hrest
    case False{}:
      LP.and_tt(E.is_bytes(r), PC.fa_bytes(rest), hr, hrest)

def keep_bytes(+cs: List<&2, B.Contig>, +seen: List<&2, String>, +hb: {PC.fa_bytes(cs) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.keep(cs, seen)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case B.Contig{+n, +r} <> +t:
      +skip = String.is_empty(n) || B.Fasta.seen(n, seen)
      +hr = AB.and_true_l(E.is_bytes(r), PC.fa_bytes(t), hb)
      +ht = AB.and_true_r(E.is_bytes(r), PC.fa_bytes(t), hb)
      keep_put(skip, n, r, t, seen, B.Fasta.keep(t, Bool.pick(List<&2, String>, skip, seen, n <> seen)), hr,
        keep_bytes(t, Bool.pick(List<&2, String>, skip, seen, n <> seen), ht))

# The FASTA's contigs are bytes when the file is.
def fa_bytes_parse(+fasta: String, +hb: {E.is_bytes(fasta) == True{} : Bool}) ->
  {PC.fa_bytes(B.Fasta.parse(fasta)) == True{} : Bool}:
  keep_bytes(B.Fasta.go(String.split(fasta, '\n')), Nil{}, go_bytes(String.split(fasta, '\n'), split_bytes(fasta, hb)))
