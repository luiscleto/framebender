import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm.bend as W
import ./proof_base.bend as PB
import ./proof_e_machine.bend as EM
import ./proof_f_args.bend as A

# Phase F: law threads (MACHINE.bend). Where no option waits for its value,
# --threads N changes nothing Args.parse returns (A.parse_thr), and the
# program's start depends on the command line only through Args.parse; so
# both command lines are usage errors together (law usage), or law machine
# gives both the same launch.

# The two words dropped, the rest of the command line is still bytes.
law ab_drop:
  for +pre: List<&2, String>
  for +x: String
  for +post: List<&2, String>
  for +h: {E.all_bytes(List.append(&2, String, pre, "--threads" <> x <> post)) == True{} : Bool}
  {E.all_bytes(List.append(&2, String, pre, post)) == True{} : Bool}

def ab_drop(pre, x, post, h):
  match pre:
    case Nil{}:
      PB.and_true_r(E.is_bytes(x), E.all_bytes(post), h)
    case p <> t:
      +hp = PB.and_true_l(E.is_bytes(p), E.all_bytes(List.append(&2, String, t, "--threads" <> x <> post)), h)
      +ht = PB.and_true_r(E.is_bytes(p), E.all_bytes(List.append(&2, String, t, "--threads" <> x <> post)), h)
      %Equal.sym(Bool, E.is_bytes(p), True{}, hp) : {Bool.and(_, E.all_bytes(List.append(&2, String, t, post))) == True{} : Bool}
      ab_drop(t, x, post, ht)

law texts_drop:
  for +pre: List<&2, String>
  for +x: String
  for +post: List<&2, String>
  for +fasta: String
  for +cs: List<&2, String>
  for +h: {E.texts_ok(M.command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
  {E.texts_ok(M.command(pre, post), fasta, cs) == True{} : Bool}

def texts_drop(pre, x, post, fasta, cs, h):
  +ha = PB.and_true_l(E.all_bytes(List.append(&2, String, pre, "--threads" <> x <> post)), E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs)), h)
  +hr = PB.and_true_r(E.all_bytes(List.append(&2, String, pre, "--threads" <> x <> post)), E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs)), h)
  %Equal.sym(Bool, E.all_bytes(List.append(&2, String, pre, post)), True{}, ab_drop(pre, x, post, ha)) :
    {Bool.and(_, E.is_bytes(fasta) && (E.all_bytes(cs) && E.pieces_ok(cs))) == True{} : Bool}
  hr

# Two command lines that parse the same, by what the shorter one parses to.
law same_parse:
  for +m: Maybe<&2, B.Cfg>
  for +lng: List<&2, String>
  for +sht: List<&2, String>
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +hm: {B.Args.parse(sht) == m : Maybe<&2, B.Cfg>}
  for +hp: {B.Args.parse(lng) == B.Args.parse(sht) : Maybe<&2, B.Cfg>}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hbl: {E.texts_ok(lng, fasta, cs) == True{} : Bool}
  for +hbs: {E.texts_ok(sht, fasta, cs) == True{} : Bool}
  {M.launch(W.start(lng), lng, fasta, vcf, cs) == M.launch(W.start(sht), sht, fasta, vcf, cs) : Maybe<&2, M.Launch>}

def same_parse(m, lng, sht, fasta, vcf, cs, hm, hp, hf, h, hbl, hbs):
  match m:
    case None{}:
      +hl = Equal.trans(Maybe<&2, B.Cfg>, B.Args.parse(lng), B.Args.parse(sht), None{}, hp, hm)
      %Equal.sym(W.Begin, W.start(lng), W.Usage{}, EM.usage(lng, hl)) :
        {M.launch(_, lng, fasta, vcf, cs) == M.launch(W.start(sht), sht, fasta, vcf, cs) : Maybe<&2, M.Launch>}
      %Equal.sym(W.Begin, W.start(sht), W.Usage{}, EM.usage(sht, hm)) :
        {M.launch(W.Usage{}, lng, fasta, vcf, cs) == M.launch(_, sht, fasta, vcf, cs) : Maybe<&2, M.Launch>}
      {==}
    case Some{B.Cfg{o, r, v}}:
      +hl = Equal.trans(Maybe<&2, B.Cfg>, B.Args.parse(lng), B.Args.parse(sht), Some{B.Cfg{o, r, v}}, hp, hm)
      Equal.trans(Maybe<&2, M.Launch>, M.launch(W.start(lng), lng, fasta, vcf, cs), Some{M.Launch{r, v, L.run(fasta, vcf, o)}}, M.launch(W.start(sht), sht, fasta, vcf, cs),
        EM.machine(lng, o, r, v, fasta, vcf, cs, hl, hf, h, hbl),
        Equal.sym(Maybe<&2, M.Launch>, M.launch(W.start(sht), sht, fasta, vcf, cs), Some{M.Launch{r, v, L.run(fasta, vcf, o)}},
          EM.machine(sht, o, r, v, fasta, vcf, cs, hm, hf, h, hbs)))

law threads:
  for +pre: List<&2, String>
  for +x: String
  for +n: Nat
  for +post: List<&2, String>
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +he: {B.Args.expecting(pre) == True{} : Bool}
  for +hx: {B.Pos.read(x) == Some{n} : Maybe<&2, Nat>}
  for +hn: {(Nat.is_le(1n, n) && Nat.is_le(n, B.Args.max_threads())) == True{} : Bool}
  for +hf: {Pr.Fasta.plain(fasta) == True{} : Bool}
  for +h: {String.concat(cs) == vcf : String}
  for +hb: {E.texts_ok(M.command(pre, "--threads" <> x <> post), fasta, cs) == True{} : Bool}
  {M.launch(W.start(M.command(pre, "--threads" <> x <> post)), M.command(pre, "--threads" <> x <> post), fasta, vcf, cs)
    == M.launch(W.start(M.command(pre, post)), M.command(pre, post), fasta, vcf, cs) : Maybe<&2, M.Launch>}

def threads(pre, x, n, post, fasta, vcf, cs, he, hx, hn, hf, h, hb):
  +tl = {"--threads" <> x <> post : List<&2, String>}
  same_parse(B.Args.parse(M.command(pre, post)), M.command(pre, tl), M.command(pre, post), fasta, vcf, cs,
    {==}, A.parse_thr(pre, x, n, post, he, hx, hn), hf, h, hb, texts_drop(pre, x, post, fasta, cs, hb))
