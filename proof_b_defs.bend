import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm_seq.bend as Norm
import ./bytes_enc.bend as E
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Shared definitions of the phase-B proofs (notes/bytes_proofs.md): Data
# pictures of the machine's Type values (a D.Bytes is pictured by the mirror
# C.BT(len, t)), and what they stand for in the spec.

def n(+x: U32) -> Nat:
  U32.to_nat(x)

# ---------------------------------------------------------------------------
# The run on bytes (norm_run.bend's Run)
# ---------------------------------------------------------------------------

# A picture of NR.Run: every field as is, the two buffers (cb: the current
# CHROM's bytes, ob: the output buffer) as mirrors.
type RunP is Data:
  RunP{n: Nat, i: Bool, h: String, c: Maybe<&2, String>, cbl: U32, cbt: AT.Tree<U32>, e: List<&2, String>, l: Maybe<&2, NR.Ck>, f: List<&2, NR.Ck>, b: List<&2, NR.Ck>, bn: Nat, tl: Nat, k: R.Cnt, obl: U32, obt: AT.Tree<U32>, ow: U32, ns: List<&2, B.Note>, x: Bool}

def mkRun(+p: RunP) -> NR.Run:
  match p:
    case RunP{n, i, h, c, +cbl, +cbt, e, l, f, b, bn, tl, k, +obl, +obt, ow, ns, x}:
      NR.Run{n, i, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, x}

# The output buffer's text.
def obtext(+p: RunP) -> String:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, +obl, +obt, ow, ns, x}:
      NR.chars(D.view(C.BT(obl, obt)))

# What a run stands for: run.bend's RunSt with out the bytes written this
# step (ob's first ow), notes this step's messages in order, buf the waiting
# items with their texts (the rest of ob, in buffer order), and last the
# last item written with an empty text (NR.to_spec computes the same).
def specRun(+p: RunP) -> R.RunSt:
  match p:
    case RunP{n, i, h, +c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, +ow, ns, x}:
      +chrom = Maybe.default(&2, String, c, "")
      +t = obtext(p)
      R.RunSt{n, i, h, c, e, NR.spec.last(l, chrom), NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, String.drop(t, U32.to_nat(ow))), k, String.take(t, U32.to_nat(ow)), List.reverse(&2, B.Note, ns), x}

# The last item written with its text emptied: run.bend reads only its key
# and where it came from (a report from a state is the report from it
# blanked).
def blank(m: Maybe<&2, R.Item>) -> Maybe<&2, R.Item>:
  match m:
    case None{}:
      None{}
    case Some{R.Item{k, p, a, t}}:
      Some{R.Item{k, p, a, ""}}

def blank_st(st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, blank(l), b, k, o, ns, x}

# A state up to what nothing reads any more: the last item's text, and once
# the run has stopped its buffer and last item (L.line_step returns a stopped
# state as it is, and R.finish of one reads only out and notes).
def settle(st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, False{}}:
      R.RunSt{n, i, h, c, e, blank(l), b, k, o, ns, False{}}
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, True{}}:
      R.RunSt{n, i, h, c, e, None{}, Nil{}, k, o, ns, True{}}

# A state with what it wrote and its messages handed out.
def clear(st: R.RunSt) -> R.RunSt:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      R.RunSt{n, i, h, c, e, l, b, k, "", Nil{}, x}

def RunSt.out(st: R.RunSt) -> String:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      o

def RunSt.notes(st: R.RunSt) -> List<&2, B.Note>:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      ns

def RunP.c(p: RunP) -> Maybe<&2, String>:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      c

def RunP.i(p: RunP) -> Bool:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      i

def RunP.x(p: RunP) -> Bool:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      x

def RunP.n(p: RunP) -> Nat:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      n

def RunP.h(p: RunP) -> String:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      h

def RunP.obl(p: RunP) -> U32:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      obl

def RunP.ow(p: RunP) -> U32:
  match p:
    case RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}:
      ow

# The text of bytes s .. s+n-1 of a mirrored buffer.
def btext(+len: U32, +t: AT.Tree<U32>, +s: U32, +k: U32) -> String:
  NR.chars(D.slice(D.view(C.BT(len, t)), U32.to_nat(s), U32.to_nat(k)))

# A result's text.
def res_text(r: B.Res) -> String:
  match r:
    case B.Res{o, k, t, s}:
      t

# ---------------------------------------------------------------------------
# The input not handled yet (norm.bend's Src and Pd)
# ---------------------------------------------------------------------------

# A source: bytes from at on of a mirrored buffer (with the depth d of its
# block), or one line's text.
type SrcP is Data:
  SBP{len: U32, t: AT.Tree<U32>, d: Nat, at: U32}
  SLP{p: String}

# The end of a line not complete yet: bytes (block depth d), or text.
type PdP is Data:
  PBP{len: U32, t: AT.Tree<U32>, d: Nat}
  PSP{s: String}

def mkSrc(+sp: SrcP) -> Norm.Src:
  match sp:
    case SBP{+len, +t, d, at}:
      Norm.SB{C.BT(len, t), at}
    case SLP{p}:
      Norm.SL{p}

def mkSrcs(+sps: List<&2, SrcP>) -> List<&1, Norm.Src>:
  match sps:
    case Nil{}:
      Nil{}
    case Con{+sp, t}:
      Con{mkSrc(sp), mkSrcs(t)}

def mkPd(+pp: PdP) -> Norm.Pd:
  match pp:
    case PBP{+len, +t, d}:
      Norm.PB{C.BT(len, t)}
    case PSP{s}:
      Norm.PS{s}

# The text a source holds: its bytes from at on; a text line with its LF.
def srctext(+sp: SrcP) -> String:
  match sp:
    case SBP{+len, +t, d, +at}:
      NR.chars(List.drop(&2, U32, D.view(C.BT(len, t)), U32.to_nat(at)))
    case SLP{+p}:
      p ++ "\n"

def srcstext(+sps: List<&2, SrcP>) -> String:
  match sps:
    case Nil{}:
      ""
    case Con{+sp, t}:
      srctext(sp) ++ srcstext(t)

def pdtext(+pp: PdP) -> String:
  match pp:
    case PBP{+len, +t, d}:
      NR.chars(D.view(C.BT(len, t)))
    case PSP{+s}:
      s

# A text holds no LF.
def nolf(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.not(Char.is_eq(c, '\n')) && nolf(t)

# A source the machine can have: a well-formed buffer with at within it, or
# a text line of bytes.
def src_ok(+sp: SrcP) -> Bool:
  match sp:
    case SBP{+len, +t, +d, +at}:
      D.ok(C.BT(len, t), d) && U32.is_le(at, len)
    case SLP{+p}:
      E.is_bytes(p) && nolf(p)

# A line end the machine can have: a well-formed buffer of at most 2^28
# bytes, or a text of bytes.
def pd_ok(+pp: PdP) -> Bool:
  match pp:
    case PBP{+len, +t, +d}:
      D.ok(C.BT(len, t), d) && U32.is_le(len, 268435456)
    case PSP{+s}:
      E.is_bytes(s)

def items_bytes(xs: List<&2, R.Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{R.Item{k, p, a, t}, rest}:
      E.is_bytes(t) && items_bytes(rest)

# The texts a run state will write are bytes: the held header, the waiting
# items' texts, what it wrote.
def st_bytes(st: R.RunSt) -> Bool:
  match st:
    case R.RunSt{n, i, h, c, e, l, b, k, o, ns, x}:
      E.is_bytes(h) && items_bytes(b) && E.is_bytes(o)

# n is at most 2^31, in word form: the contract's E.le31 (bytes_enc.bend).
def le31(+n: Nat) -> Bool:
  E.le31(n)
