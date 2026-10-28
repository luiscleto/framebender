import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./norm.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_run_take.bend as TK
import ./proof_b_run_same.bend as SA
import ./proof_b_run_head.bend as HD
import ./proof_b_run_fin.bend as FN
import ./proof_b_run_bl.bend as BL
import ../lawful-bytes/proof_grow.bend as G
import ../lawful-bytes/proof_same.bend as SM
import ../lawful-bytes/proof_ops.bend as O
import ../lawful-arrays/proof_base.bend as AB
import ../lawful-arrays/proof_index.bend as I
import ../lawful-words/proof_nat.bend as N
import ../lawful-words/proof_u32.bend as U
import ./bytes_enc.bend as E
import ./proof_b_fasteq.bend as FE
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/bytes.bend as BY
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# The run on bytes (norm_run.bend) refines run.bend's: each operation the
# machine uses, on a pictured run (P.mkRun) that satisfies RunInv, gives a
# pictured run that satisfies RunInv again and stands (P.specRun) for what
# run.bend's operation gives, up to what nothing reads any more (P.settle:
# the last item's text, and a stopped run's buffer and last item). Lines are
# only handled while the run goes on (not stopped), header lines before the
# #CHROM line, body lines after it.

# ---------------------------------------------------------------------------
# The invariant (yours to define: whatever the deliverables need, e.g. ob
# well formed of depth at most 29, ow <= obl < 2^30, the items' lengths add
# up to obl - ow, bn counts them, tl is the largest key, the buffer is
# sorted, cb holds the current CHROM's bytes, nothing written or noted
# before #CHROM)
# ---------------------------------------------------------------------------

def RunInv(+p: P.RunP) -> Bool:
  RD.RunInv(p)

# ---------------------------------------------------------------------------
# Deliverables (each: the statement is fixed; replace ?TODO by a proof)
# ---------------------------------------------------------------------------

# The run the program starts with.
def run_start() ->
  &p: P.RunP -> ({NR.start() == P.mkRun(p) : NR.Run}
  & ({RunInv(p) == True{} : Bool}
  & {P.specRun(p) == R.start_st() : R.RunSt})):
  +t0 = G.tnew(0n, 0)
  +t1 = G.tnew(16n, 0)
  +k0 = {R.Cnt{0n, 0n, 0n, 0n} : R.Cnt}
  +ok0 = LM.ok_td(0, t0, 0n, C.ok_mk(0, t0, 0n, G.tnew_full(0n, 0), {==}, I.le0(Nat.mul(4n, Nat.pow(2n, 0n)))))
  +ok1 = LM.ok_td(0, t1, 16n, C.ok_mk(0, t1, 16n, G.tnew_full(16n, 0), {==}, I.le0(Nat.mul(4n, Nat.pow(2n, 16n)))))
  +p0 = {P.RunP{0n, False{}, "", None{}, 0, t0, Nil{}, None{}, Nil{}, Nil{}, 0n, 0n, k0, 0, t1, 0, Nil{}, False{}} : P.RunP}
  +hi = PI.inv_mk(False{}, "", None{}, 0, t0, Nil{}, Nil{}, 0n, 0n, 0, t1, 0, Nil{}, False{}, (ok1, ({==}, (ok0, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==})))))))))))
  +eq1 = AB.subst(D.Bytes, z => {NR.Run{0n, False{}, "", None{}, z, Nil{}, None{}, Nil{}, Nil{}, 0n, 0n, k0, C.BT(0, t1), 0, Nil{}, False{}} == P.mkRun(p0) : NR.Run},
    C.BT(0, t0), BY.empty(0n), Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), {==})
  +eq2 = AB.subst(D.Bytes, z => {NR.Run{0n, False{}, "", None{}, BY.empty(0n), Nil{}, None{}, Nil{}, Nil{}, 0n, 0n, k0, z, 0, Nil{}, False{}} == P.mkRun(p0) : NR.Run},
    C.BT(0, t1), BY.empty(16n), Equal.sym(D.Bytes, BY.empty(16n), C.BT(0, t1), G.empty_eq(16n)), eq1)
  (p0, (eq2, (hi, {==})))

# What a good run will write is bytes (the String mode keeps this).
def run_bytes(+p: P.RunP, hi: {RunInv(p) == True{} : Bool}) ->
  {P.st_bytes(P.specRun(p)) == True{} : Bool}:
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +t = NR.chars(D.view(C.BT(obl, obt)))
      +chrom = Maybe.default(&2, String, c, "")
      +m = U32.to_nat(ow)
      +ht = PI.chars_bytes(D.view(C.BT(obl, obt)), O.view_bytes_t(obl, obt))
      +hh = PI.pr9(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +hit = PI.items_bytes(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, String.drop(t, m), PI.drop_bytes(t, m, ht))
      +IB = P.items_bytes(NR.spec.items(NR.append_ck(f, NR.rev_ck(b, Nil{})), chrom, String.drop(t, m)))
      LM.and_mk(E.is_bytes(h) && IB, E.is_bytes(String.take(t, m)), LM.and_mk(E.is_bytes(h), IB, hh, hit), PI.take_bytes(t, m, ht))

# Before the #CHROM line a good run that has not stopped has written and
# noted nothing (finish's NoHeader stop notes before #CHROM).
def run_head_empty(+p: P.RunP, hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == False{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool}) ->
  {P.RunSt.out(P.specRun(p)) == "" : String}
  & {P.RunSt.notes(P.specRun(p)) == Nil{} : List<&2, B.Note>}:
  match p:
    case P.RunP{+n, True{}, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      Empty.absurd({P.RunSt.out(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x})) == "" : String}
        & {P.RunSt.notes(P.specRun(P.RunP{n, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x})) == Nil{} : List<&2, B.Note>},
        AB.false_ne_true(Equal.sym(Bool, True{}, False{}, hin)))
    case P.RunP{+n, False{}, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +hp = PI.pr10(False{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +hz = LM.andl(U32.is_zero(obl), RD.is_nil(f) && (RD.is_nil(b) && (x || RD.no_notes(ns))), hp)
      +e0 = U.is_eq_true(obl, 0, hz)
      +ho = AB.subst(U32, z => {P.RunSt.out(P.specRun(P.RunP{n, False{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, z, obt, ow, ns, x})) == "" : String}, 0, obl,
        Equal.sym(U32, obl, 0, e0),
        %Equal.sym(List<&2, U32>, D.view(C.BT(0, obt)), Nil{}, BF.view0(obt)) : {String.take(NR.chars(_), U32.to_nat(ow)) == "" : String};
        {==})
      +hr = LM.andr(U32.is_zero(obl), RD.is_nil(f) && (RD.is_nil(b) && (x || RD.no_notes(ns))), hp)
      +hn = LM.andr(RD.is_nil(b), x || RD.no_notes(ns), LM.andr(RD.is_nil(f), RD.is_nil(b) && (x || RD.no_notes(ns)), hr))
      +ens = PI.notes_nil(ns, PI.or_f(x, RD.no_notes(ns), hx, hn))
      +hns = AB.subst(List<&2, B.Note>, z => {List.reverse(&2, B.Note, z) == Nil{} : List<&2, B.Note>}, Nil{}, ns, Equal.sym(List<&2, B.Note>, ns, Nil{}, ens), {==})
      (ho, hns)

# The run as run.bend's state, computed (the String mode starts from it).
def run_to_spec(+p: P.RunP, hi: {RunInv(p) == True{} : Bool}) ->
  {NR.to_spec(P.mkRun(p)) == P.specRun(p) : R.RunSt}:
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hi)
      +LS = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(obl, obt), 0, obl))
      +SR = P.specRun(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x})
      +eLS = SM.to_list_view_t(obl, obt, RD.tdepth(obt), 0, obl, hok, N.le_refl(U32.to_nat(obl)))
      %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(obl, obt), 0, obl), (C.BT(obl, obt), LS), SM.to_list_pair_t(obl, obt, 0, obl)) :
        {NR.spec.k(n, i, h, c, e, l, f, b, k, ow, ns, x, _) == SR : R.RunSt}
      %Equal.sym(List<&2, U32>, LS, D.slice(D.view(C.BT(obl, obt)), U32.to_nat(0), U32.to_nat(obl)), eLS) :
        {NR.spec.k(n, i, h, c, e, l, f, b, k, ow, ns, x, (C.BT(obl, obt), _)) == SR : R.RunSt}
      %Equal.sym(List<&2, U32>, D.slice(D.view(C.BT(obl, obt)), U32.to_nat(0), U32.to_nat(obl)), D.view(C.BT(obl, obt)), BF.view_all(obl, obt, RD.tdepth(obt), hok)) :
        {NR.spec.k(n, i, h, c, e, l, f, b, k, ow, ns, x, (C.BT(obl, obt), _)) == SR : R.RunSt}
      {==}

def run_tick(+p: P.RunP, hi: {RunInv(p) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.tick(P.mkRun(p)) == P.mkRun(p2) : NR.Run}
  & ({RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == R.tick(P.specRun(p)) : R.RunSt}
  & ({P.RunP.n(p2) == 1n+P.RunP.n(p) : Nat}
  & ({P.RunP.obl(p2) == P.RunP.obl(p) : U32}
  & {P.RunP.ow(p2) == P.RunP.ow(p) : U32}))))):
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      (P.RunP{1n+n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, x}, ({==}, (hi, ({==}, ({==}, ({==}, {==}))))))

# A record in normal form, written as it came (the fast path's and the slow
# path's Same): its text is bytes s .. s+k-1 of the source buffer; p is the
# run after the line's tick; the run's sizes are as the machine checks them
# (norm.bend: Rs not big, not full; a line of at most 2^28 bytes).
def run_fast_done(+p: P.RunP, +o: B.Opts, +l: B.Line, +pos: Nat, +chrom: String,
  +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == True{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool},
  hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  hc: {P.RunP.c(p) == Some{chrom} : Maybe<&2, String>},
  hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  hk: {U32.is_le(k, 268435457) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.fast_done(P.mkRun(p), R.Opts.w(o), P.RunP.n(p), pos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, pos, B.Line.body(l), False{}}, P.specRun(p), o, l, B.At{P.RunP.n(p), chrom, Nat.show(pos)}, pos)) : R.RunSt})):
  BL.fd_t(p, o, l, pos, chrom, sl, st, sd, s, k, hi, hin, hx, hok, hs, ht, hc, hbig, hk)

# The same through NR.same_done (the slow path's Same), with the line's At.
def run_same_done(+p: P.RunP, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == True{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool},
  hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  hk: {U32.is_le(k, 268435457) == True{} : Bool},
  hcb: {E.is_bytes(NR.At.chrom(at)) == True{} : Bool},
  hcl: {Norm.len_le(NR.At.chrom(at), 268435456) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.same_done(P.mkRun(p), o, at, inpos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(B.Res{B.Normalized{}, inpos, B.Line.body(l), False{}}, P.specRun(p), o, l, at, inpos)) : R.RunSt})):
  BL.sd_t(p, o, l, at, inpos, sl, st, sd, s, k, hi, hin, hx, hok, hs, ht, hbig, hk, hcb, hcl)

# A body line with its result r (the slow path), when its new bytes fit
# (norm.bend's body.res: obl + res_len <= 2^30).
def run_body_line(+p: P.RunP, +r: B.Res, +o: B.Opts, +l: B.Line, +at: B.At, +inpos: Nat,
  +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +k: U32,
  hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == True{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool},
  hok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(k)), U32.to_nat(sl)) == True{} : Bool},
  ht: {P.btext(sl, st, s, k) == B.Line.text(l) : String},
  hbig: {U32.is_le(536870912, P.RunP.obl(p)) == False{} : Bool},
  hk: {U32.is_le(k, 268435457) == True{} : Bool},
  hfit: {Norm.res_fits(r, l, (1073741824 - P.RunP.obl(p) : U32)) == True{} : Bool},
  hb: {E.is_bytes(P.res_text(r)) == True{} : Bool},
  hcb: {E.is_bytes(NR.At.chrom(at)) == True{} : Bool},
  hcl: {Norm.len_le(NR.At.chrom(at), 268435456) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.body_line(r, P.mkRun(p), o, l, at, inpos, C.BT(sl, st), s, k) == (P.mkRun(p2), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RunInv(p2) == True{} : Bool}
  & {P.settle(P.specRun(p2)) == P.settle(R.body_line(r, P.specRun(p), o, l, at, inpos)) : R.RunSt})):
  BL.bl_t(p, r, o, l, at, inpos, sl, st, sd, s, k, hi, hin, hx, hok, hs, ht, hbig, hk, hfit, hb, hcb, hcl)

# A header line held (not the #CHROM line); p is the run after its tick.
def run_head_hold(+p: P.RunP, +o: B.Opts, +l: B.Line,
  hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == False{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool},
  hb: {E.is_bytes(B.Line.text(l)) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.head_line(False{}, P.mkRun(p), o, l) == P.mkRun(p2) : NR.Run}
  & ({RunInv(p2) == True{} : Bool}
  & {P.specRun(p2) == R.head_line(False{}, P.specRun(p), o, l) : R.RunSt})):
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +la, +f, +b, +bn, +tl, +k, +obl, +obt, +ow, +ns, +x}:
      +h2 = String.append(h, B.Line.text(l))
      +hj = hi
      +hb2 = PI.bytes_app(h, B.Line.text(l), PI.parts_hb(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, PI.inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hj)), hb)
      (P.RunP{n, i, h2, c, cbl, cbt, e, la, f, b, bn, tl, k, obl, obt, ow, ns, x}, ({==},
        (PI.inv_mk(i, h2, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, PI.parts_h(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, h2, PI.inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hj), hb2)), {==})))

# The #CHROM line writes the header, when it fits (norm.bend: the held
# header has at most 2^28 bytes); p is the run after its tick.
def run_head_write(+p: P.RunP, +o: B.Opts, +l: B.Line,
  hi: {RunInv(p) == True{} : Bool},
  hin: {P.RunP.i(p) == False{} : Bool},
  hx: {P.RunP.x(p) == False{} : Bool},
  hh: {Norm.len_le(P.RunP.h(p), 268435456) == True{} : Bool},
  hb1: {E.is_bytes(P.RunP.h(p)) == True{} : Bool},
  hb2: {E.is_bytes(B.Line.text(l)) == True{} : Bool},
  hb3: {E.is_bytes(R.added(o, B.Line.term(l))) == True{} : Bool},
  hl: {Norm.len_le(B.Line.text(l), 268435456) == True{} : Bool},
  hadd: {Norm.len_le(R.added(o, B.Line.term(l)), 268435456) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.head_line(True{}, P.mkRun(p), o, l) == P.mkRun(p2) : NR.Run}
  & ({RunInv(p2) == True{} : Bool}
  & {P.specRun(p2) == R.head_line(True{}, P.specRun(p), o, l) : R.RunSt})):
  HD.head_t(p, o, l, hi, hin, hh, hb1, hb2, hb3, hl, hadd)

# The end of the run: the code, and the run whose out and notes are
# run.bend's report's.
def run_finish(+p: P.RunP, +o: B.Opts,
  hi: {RunInv(p) == True{} : Bool}) ->
  &p2: P.RunP -> &code: Nat -> ({NR.finish(P.mkRun(p), R.Opts.w(o)) == (P.mkRun(p2), code) : NR.Run & Nat}
  & ({RunInv(p2) == True{} : Bool}
  & {R.Report{P.RunSt.out(P.specRun(p2)), P.RunSt.notes(P.specRun(p2)), code} == R.finish(P.specRun(p)) : R.Report})):
  FN.fin_t(p, o, hi)

# A step ends: the bytes written (a well-formed buffer, of depth at most 29)
# and the messages are handed out; the run keeps the rest.
def run_take(+p: P.RunP, +left: U32,
  hi: {RunInv(p) == True{} : Bool}) ->
  &ol: U32 -> &ot: AT.Tree<U32> -> &d: Nat -> &p2: P.RunP ->
  ({NR.take(P.mkRun(p), left) == ((C.BT(ol, ot), P.RunSt.notes(P.specRun(p))), P.mkRun(p2)) : (D.Bytes & List<&2, B.Note>) & NR.Run}
  & ({D.ok(C.BT(ol, ot), d) == True{} : Bool}
  & ({NR.chars(D.view(C.BT(ol, ot))) == P.RunSt.out(P.specRun(p)) : String}
  & ({RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == P.clear(P.specRun(p)) : R.RunSt}
  & {P.RunP.ow(p2) == 0 : U32}))))):
  +hj = hi
  TK.take_t(p, left, hj)

# Room for a piece's bytes: nothing else changes.
def run_reserve(+p: P.RunP, +k: U32,
  hi: {RunInv(p) == True{} : Bool}) ->
  &p2: P.RunP -> ({NR.reserve(P.mkRun(p), k) == P.mkRun(p2) : NR.Run}
  & ({RunInv(p2) == True{} : Bool}
  & ({P.specRun(p2) == P.specRun(p) : R.RunSt}
  & {P.RunP.ow(p2) == P.RunP.ow(p) : U32}))):
  match p:
    case P.RunP{+n, +i, +h, +c, +cbl, +cbt, +e, +l, +f, +b, +bn, +tl, +kc, +obl, +obt, +ow, +ns, +x}:
      +hj = hi
      +hok = PI.pr1(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hj)
      +T2 = BF.RVT(obl, obt, k)
      +p2 = {P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, kc, obl, T2, ow, ns, x} : P.RunP}
      +eq = AB.subst(D.Bytes, z => {NR.Run{n, i, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, kc, z, ow, ns, x} == P.mkRun(p2) : NR.Run},
        C.BT(obl, T2), NR.reserve.len(k, BY.len(C.BT(obl, obt))), Equal.sym(D.Bytes, NR.reserve.len(k, BY.len(C.BT(obl, obt))), C.BT(obl, T2), BF.reserve_eq(obl, obt, k, C.ok_full(obl, obt, RD.tdepth(obt), hok))), {==})
      +hinv = PI.inv_mk(i, h, c, cbl, cbt, f, b, bn, tl, obl, T2, ow, ns, x,
        PI.parts_ob(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, T2, PI.inv_parts(i, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, x, hj), BF.rs_ok(obl, obt, T2, BF.res_p(obl, obt, k, hok))))
      +hs = AB.subst(List<&2, U32>, z => {PI.SRT(n, i, h, c, e, l, f, b, kc, ow, ns, x, NR.chars(z)) == P.specRun(P.RunP{n, i, h, c, cbl, cbt, e, l, f, b, bn, tl, kc, obl, obt, ow, ns, x}) : R.RunSt},
        D.view(C.BT(obl, obt)), D.view(C.BT(obl, T2)), Equal.sym(List<&2, U32>, D.view(C.BT(obl, T2)), D.view(C.BT(obl, obt)), BF.rs_view(obl, obt, T2, BF.res_p(obl, obt, k, hok))), {==})
      (p2, (eq, (hinv, (hs, {==}))))

# The fast path's CHROM test: the run is handed back, and a passed test
# means CHROM (bytes s .. e0-1 of b) is the current CHROM run's.
def run_same(+p: P.RunP, +bl: U32, +bt: AT.Tree<U32>, +bd: Nat, +s: U32, +e0: U32,
  hi: {RunInv(p) == True{} : Bool},
  hok: {D.ok(C.BT(bl, bt), bd) == True{} : Bool},
  hs: {Nat.is_le(U32.to_nat(s), U32.to_nat(e0)) == True{} : Bool},
  hlt: {U32.is_lt(s, e0) == True{} : Bool},
  he: {Nat.is_le(U32.to_nat(e0), U32.to_nat(bl)) == True{} : Bool}) ->
  &q: Bool -> ({Norm.Run.same(P.mkRun(p), C.BT(bl, bt), s, e0) == (P.mkRun(p), (C.BT(bl, bt), q)) : NR.Run & (D.Bytes & Bool)}
  & {Bool.pick(Maybe<&2, String>, q, Some{P.btext(bl, bt, s, (e0 - s : U32))}, P.RunP.c(p)) == P.RunP.c(p) : Maybe<&2, String>}):
  SA.same_t(p, bl, bt, bd, s, e0, hi, hok, hs, hlt, he)

# A text as a new buffer (NR.of_str): well formed, holding the text's bytes.
def of_str(+s: String,
  hb: {E.is_bytes(s) == True{} : Bool},
  hn: {Norm.len_le(s, 1073741824) == True{} : Bool}) ->
  &l: U32 -> &t: AT.Tree<U32> -> &d: Nat ->
  ({NR.of_str(s) == C.BT(l, t) : D.Bytes}
  & ({D.ok(C.BT(l, t), d) == True{} : Bool}
  & {NR.chars(D.view(C.BT(l, t))) == s : String})):
  +L = String.length(s)
  +t0 = G.tnew(0n, 0)
  +hL = NM.lt_c0(L, Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(L, SZ.len30(s, hn)))
  +hok0 = AB.subst(D.Bytes, z => {D.ok(z, 0n) == True{} : Bool}, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n), G.empty_ok(0n, {==}))
  +eq = AB.subst(D.Bytes, z => {NR.put_str(z, s) == C.BT(BF.pstl(s, 0), BF.PSR(0, t0, s)) : D.Bytes}, C.BT(0, t0), BY.empty(0n),
    Equal.sym(D.Bytes, BY.empty(0n), C.BT(0, t0), G.empty_eq(0n)), BF.put_str_eq(0, t0, s, G.tnew_full(0n, 0)))
  (BF.pstl(s, 0), (BF.PSR(0, t0, s), (RD.tdepth(BF.PSR(0, t0, s)),
    (eq,
    (BF.put_str_ok(0, t0, 0n, s, hok0, hL),
    BF.put_str_text(0, t0, 0n, s, hok0, hb, hL))))))

