import Base
import ./types.bend as B
import ./run.bend as R
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as RD
import ./proof_b_run_lem.bend as LM
import ./proof_b_run_num.bend as NM
import ./proof_b_run_inv.bend as PI
import ./proof_b_run_buf.bend as BF
import ./proof_b_run_sz.bend as SZ
import ./proof_b_run_flush.bend as FL
import ./proof_b_run_ins.bend as INS
import ./proof_b_lit.bend as PL
import ./proof_b_run_head.bend as HD
import ./proof_run_base.bend as RBS
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_ops.bend as O
import lawful-bytes@0.1.1.0/proof_grow.bend as G
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import lawful-arrays@0.1.0.0/proof_tree.bend as AT
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-words@0.1.0.0/proof_u32.bend as U

# NR.add (an item and its text into the buffer) on a pictured run: at the
# end, or in the middle (proof_b_run_ins.bend gives run.bend's insert).

# Lists and texts
# ===============

law chars_len:
  for +xs: List<&2, U32>
  {String.length(NR.chars(xs)) == List.length(&2, U32, xs) : Nat}

def chars_len(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %chars_len(t) : {1n+String.length(NR.chars(t)) == 1n+_ : Nat}
      {==}

def txt_len(+obl: U32, +obt: AT.Tree<U32>, +hok: {D.ok(C.BT(obl, obt), RD.tdepth(obt)) == True{} : Bool}) ->
  {String.length(FL.TXT(obl, obt)) == U32.to_nat(obl) : Nat}:
  Equal.trans(Nat, String.length(FL.TXT(obl, obt)), List.length(&2, U32, D.view(C.BT(obl, obt))), U32.to_nat(obl), chars_len(D.view(C.BT(obl, obt))), O.view_size_t(obl, obt, RD.tdepth(obt), hok))

law lens_app:
  for +xs: List<&2, NR.Ck>
  for +ys: List<&2, NR.Ck>
  {RD.lens(NR.append_ck(xs, ys)) == Nat.add(RD.lens(xs), RD.lens(ys)) : Nat}

def lens_app(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat, RD.lens(NR.append_ck(t, ys)), Nat.add(RD.lens(t), RD.lens(ys)), lens_app(t, ys)) : {Nat.add(U32.to_nat(NR.Ck.len(x)), _) == Nat.add(Nat.add(U32.to_nat(NR.Ck.len(x)), RD.lens(t)), RD.lens(ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(NR.Ck.len(x)), RD.lens(t)), RD.lens(ys)), Nat.add(U32.to_nat(NR.Ck.len(x)), Nat.add(RD.lens(t), RD.lens(ys))), N.add_assoc(U32.to_nat(NR.Ck.len(x)), RD.lens(t), RD.lens(ys)))

law keys_mono:
  for +xs: List<&2, NR.Ck>
  for +a: Nat
  for +b: Nat
  for +h: {RD.keys_le(xs, a) == True{} : Bool}
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  {RD.keys_le(xs, b) == True{} : Bool}

def keys_mono(xs, a, b, h, hab):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LM.and_mk(Nat.is_le(NR.Ck.key(x), b), RD.keys_le(t, b), N.le_trans(NR.Ck.key(x), a, b, LM.andl(Nat.is_le(NR.Ck.key(x), a), RD.keys_le(t, a), h), hab),
        keys_mono(t, a, b, LM.andr(Nat.is_le(NR.Ck.key(x), a), RD.keys_le(t, a), h), hab))

law keys_app:
  for +xs: List<&2, NR.Ck>
  for +ys: List<&2, NR.Ck>
  for +k: Nat
  for +h1: {RD.keys_le(xs, k) == True{} : Bool}
  for +h2: {RD.keys_le(ys, k) == True{} : Bool}
  {RD.keys_le(NR.append_ck(xs, ys), k) == True{} : Bool}

def keys_app(xs, ys, k, h1, h2):
  match xs:
    case Nil{}:
      h2
    case Con{+x, +t}:
      LM.and_mk(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(NR.append_ck(t, ys), k), LM.andl(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), h1),
        keys_app(t, ys, k, LM.andr(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), h1), h2))

law keys_appl:
  for +xs: List<&2, NR.Ck>
  for +ys: List<&2, NR.Ck>
  for +k: Nat
  for +h: {RD.keys_le(NR.append_ck(xs, ys), k) == True{} : Bool}
  {RD.keys_le(xs, k) == True{} : Bool}

def keys_appl(xs, ys, k, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      LM.and_mk(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(t, k), LM.andl(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(NR.append_ck(t, ys), k), h),
        keys_appl(t, ys, k, LM.andr(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(NR.append_ck(t, ys), k), h)))

law keys_appr:
  for +xs: List<&2, NR.Ck>
  for +ys: List<&2, NR.Ck>
  for +k: Nat
  for +h: {RD.keys_le(NR.append_ck(xs, ys), k) == True{} : Bool}
  {RD.keys_le(ys, k) == True{} : Bool}

def keys_appr(xs, ys, k, h):
  match xs:
    case Nil{}:
      h
    case Con{+x, +t}:
      keys_appr(t, ys, k, LM.andr(Nat.is_le(NR.Ck.key(x), k), RD.keys_le(NR.append_ck(t, ys), k), h))

law len_app_ck:
  for +xs: List<&2, NR.Ck>
  for +ys: List<&2, NR.Ck>
  {List.length(&2, NR.Ck, NR.append_ck(xs, ys)) == Nat.add(List.length(&2, NR.Ck, xs), List.length(&2, NR.Ck, ys)) : Nat}

def len_app_ck(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %len_app_ck(t, ys) : {1n+List.length(&2, NR.Ck, NR.append_ck(t, ys)) == 1n+_ : Nat}
      {==}

# A word bound from a Nat bound of 2^30.
def F31() -> U32:
  1073741824

def le30w(+a: U32, +h: {Nat.is_le(U32.to_nat(a), Nat.pow(2n, 30n)) == True{} : Bool}) -> {U32.is_le(a, F31()) == True{} : Bool}:
  Equal.trans(Bool, U32.is_le(a, F31()), Nat.is_le(U32.to_nat(a), U32.to_nat(F31())), True{}, U.is_le_to_nat(a, F31()),
    AB.subst(Nat, y => {Nat.is_le(U32.to_nat(a), y) == True{} : Bool}, Nat.pow(2n, 30n), U32.to_nat(F31()), Equal.sym(Nat, U32.to_nat(F31()), Nat.pow(2n, 30n), PL.lit_pow(30n, F31(), {==}, {==})), h))

def w30(+a: U32, +h: {U32.is_le(a, F31()) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(a), Nat.pow(2n, 30n)) == True{} : Bool}:
  AB.subst(Nat, y => {Nat.is_le(U32.to_nat(a), y) == True{} : Bool}, U32.to_nat(F31()), Nat.pow(2n, 30n), PL.lit_pow(30n, F31(), {==}, {==}),
    Equal.trans(Bool, Nat.is_le(U32.to_nat(a), U32.to_nat(F31())), U32.is_le(a, F31()), True{}, Equal.sym(Bool, U32.is_le(a, F31()), Nat.is_le(U32.to_nat(a), U32.to_nat(F31())), U.is_le_to_nat(a, F31())), h))

# put_txt
# =======

# An item's text: bytes s .. s+n-1 of the source (Raw), or its own (Own).
def TxtP(+t: NR.Txt, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  match t:
    case NR.Raw{}:
      {D.ok(C.BT(sl, st), sd) == True{} : Bool}
      & ({Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sn)), U32.to_nat(sl)) == True{} : Bool}
      & {P.btext(sl, st, s, sn) == tx : String})
    case NR.Own{y}:
      {y == tx : String} & {E.is_bytes(y) == True{} : Bool}

def PutT(+l: U32, +tr: AT.Tree<U32>, +l2: U32, +t2: AT.Tree<U32>, +tx: String) -> Type:
  {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool}
  & ({FL.TXT(l2, t2) == String.append(FL.TXT(l, tr), tx) : String}
  & {U32.to_nat(l2) == Nat.add(U32.to_nat(l), String.length(tx)) : Nat})

def PutG(+t: NR.Txt, +l: U32, +tr: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  &l2: U32 -> &t2: AT.Tree<U32> -> ({NR.put_txt(t, C.BT(l, tr), C.BT(sl, st), s, sn) == (C.BT(l2, t2), C.BT(sl, st)) : D.Bytes & D.Bytes} & PutT(l, tr, l2, t2, tx))

def pt.raw(+l: U32, +tr: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hok: {D.ok(C.BT(l, tr), RD.tdepth(tr)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, sn) == tx : String},
  +elen: {String.length(tx) == U32.to_nat(sn) : Nat},
  pb: &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(l, tr, sl, st, s, sn, l2, t2)) -> PutG(NR.Raw{}, l, tr, sl, st, sd, s, sn, tx):
  (+l2, q1) = pb
  (+t2, q2) = q1
  (eq, q3) = q2
  (ok2, q4) = q3
  (vw, ln) = q4
  +SLs = D.slice(D.view(C.BT(sl, st)), U32.to_nat(s), U32.to_nat(sn))
  +etx = Equal.trans(String, FL.TXT(l2, t2), NR.chars(List.append(&2, U32, D.view(C.BT(l, tr)), SLs)), String.append(FL.TXT(l, tr), tx),
    Equal.cong(List<&2, U32>, String, z => NR.chars(z), D.view(C.BT(l2, t2)), List.append(&2, U32, D.view(C.BT(l, tr)), SLs), vw),
    Equal.trans(String, NR.chars(List.append(&2, U32, D.view(C.BT(l, tr)), SLs)), String.append(FL.TXT(l, tr), NR.chars(SLs)), String.append(FL.TXT(l, tr), tx),
      BF.chars_app(D.view(C.BT(l, tr)), SLs), Equal.cong(String, String, z => String.append(FL.TXT(l, tr), z), NR.chars(SLs), tx, ht)))
  +eln = Equal.trans(Nat, U32.to_nat(l2), Nat.add(U32.to_nat(l), U32.to_nat(sn)), Nat.add(U32.to_nat(l), String.length(tx)), ln,
    Equal.cong(Nat, Nat, z => Nat.add(U32.to_nat(l), z), U32.to_nat(sn), String.length(tx), Equal.sym(Nat, String.length(tx), U32.to_nat(sn), elen)))
  (l2, (t2, (eq, (ok2, (etx, eln)))))

def pt.r(+l: U32, +tr: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hok: {D.ok(C.BT(l, tr), RD.tdepth(tr)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(tx)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
  +hsok: {D.ok(C.BT(sl, st), sd) == True{} : Bool},
  +hs: {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sn)), U32.to_nat(sl)) == True{} : Bool},
  +ht: {P.btext(sl, st, s, sn) == tx : String}) -> PutG(NR.Raw{}, l, tr, sl, st, sd, s, sn, tx):
  +V = D.view(C.BT(sl, st))
  +hsl = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(s), U32.to_nat(sn)), y) == True{} : Bool}, U32.to_nat(sl), List.length(&2, U32, V),
    Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(sl), O.view_size_t(sl, st, sd, hsok)), hs)
  +elen = Equal.trans(Nat, String.length(tx), String.length(P.btext(sl, st, s, sn)), U32.to_nat(sn),
    Equal.cong(String, Nat, z => String.length(z), tx, P.btext(sl, st, s, sn), Equal.sym(String, P.btext(sl, st, s, sn), tx, ht)),
    Equal.trans(Nat, String.length(P.btext(sl, st, s, sn)), List.length(&2, U32, D.slice(V, U32.to_nat(s), U32.to_nat(sn))), U32.to_nat(sn),
      chars_len(D.slice(V, U32.to_nat(s), U32.to_nat(sn))), BF.slice_len(V, U32.to_nat(s), U32.to_nat(sn), hsl)))
  +hL2 = AB.subst(Nat, y => {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), y), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}, String.length(tx), U32.to_nat(sn), elen, hL)
  pt.raw(l, tr, sl, st, sd, s, sn, tx, hok, ht, elen, BF.put_bytes_t(l, tr, sl, st, sd, s, sn, hok, hsok, hs, hL2))

def pt.o(+y: String, +l: U32, +tr: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hok: {D.ok(C.BT(l, tr), RD.tdepth(tr)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(tx)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
  +ey: {y == tx : String},
  +hb: {E.is_bytes(y) == True{} : Bool}) -> PutG(NR.Own{y}, l, tr, sl, st, sd, s, sn, tx):
  +hLy = AB.subst(String, z => {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(z)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}, tx, y, Equal.sym(String, y, tx, ey), hL)
  +eq = AB.subst(D.Bytes, z => {(z, C.BT(sl, st)) == (C.BT(BF.pstl(y, l), BF.PSR(l, tr, y)), C.BT(sl, st)) : D.Bytes & D.Bytes}, C.BT(BF.pstl(y, l), BF.PSR(l, tr, y)), NR.put_str(C.BT(l, tr), y),
    Equal.sym(D.Bytes, NR.put_str(C.BT(l, tr), y), C.BT(BF.pstl(y, l), BF.PSR(l, tr, y)), BF.put_str_eq(l, tr, y, C.ok_full(l, tr, RD.tdepth(tr), hok))), {==})
  +etx = AB.subst(String, z => {FL.TXT(BF.pstl(y, l), BF.PSR(l, tr, y)) == String.append(FL.TXT(l, tr), z) : String}, y, tx, ey, BF.put_str_text(l, tr, RD.tdepth(tr), y, hok, hb, hLy))
  +eln = AB.subst(String, z => {U32.to_nat(BF.pstl(y, l)) == Nat.add(U32.to_nat(l), String.length(z)) : Nat}, y, tx, ey, BF.put_str_len(l, tr, RD.tdepth(tr), y, hok, hLy))
  (BF.pstl(y, l), (BF.PSR(l, tr, y), (eq, (BF.put_str_ok(l, tr, RD.tdepth(tr), y, hok, hLy), (etx, eln)))))

def put_txt_t(+t: NR.Txt, +l: U32, +tr: AT.Tree<U32>, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hok: {D.ok(C.BT(l, tr), RD.tdepth(tr)) == True{} : Bool},
  +hL: {Nat.is_lt(Nat.add(Nat.add(U32.to_nat(l), String.length(tx)), 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool},
  htx: TxtP(t, sl, st, sd, s, sn, tx)) -> PutG(t, l, tr, sl, st, sd, s, sn, tx):
  match t:
    case NR.Raw{}:
      (hsok, q) = htx
      (hs, ht) = q
      pt.r(l, tr, sl, st, sd, s, sn, tx, hok, hL, hsok, hs, ht)
    case NR.Own{+y}:
      (ey, hb) = htx
      pt.o(y, l, tr, sl, st, sd, s, sn, tx, hok, hL, ey, hb)

def AddG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  &obl2: U32 -> &obt2: AT.Tree<U32> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &tl2: Nat ->
  ({NR.add(P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, False{}}), NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl2, obl2, obt2, ow, ns, False{}) == True{} : Bool}
  & ({FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>}
  & ({String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String}
  & {U32.to_nat(obl2) == Nat.add(U32.to_nat(obl), String.length(tx)) : Nat}))))

def EndG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  &obl2: U32 -> &obt2: AT.Tree<U32> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &tl2: Nat ->
  ({NR.at_end(NR.Ck{kx, ipx, lnx, psx, nx}, kx, t, C.BT(sl, st), s, sn, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl2, obl2, obt2, ow, ns, False{}) == True{} : Bool}
  & ({FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>}
  & ({String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String}
  & {U32.to_nat(obl2) == Nat.add(U32.to_nat(obl), String.length(tx)) : Nat}))))

law len0_keys:
  for +xs: List<&2, NR.Ck>
  for +k: Nat
  for +h: {List.length(&2, NR.Ck, xs) == 0n : Nat}
  {RD.keys_le(xs, k) == True{} : Bool}

def len0_keys(xs, k, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({RD.keys_le(Con{x, t}, k) == True{} : Bool}, N.succ_ne_zero(List.length(&2, NR.Ck, t), h))

# At the end: every buffered key is at most the new one (or none is buffered).
def end_k(+zb: Bool, +bn: Nat, +tl: Nat, +kx: Nat, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>,
  +hzb: {Nat.is_eq(bn, 0n) == zb : Bool},
  +hz: {Bool.or(zb, Nat.is_le(tl, kx)) == True{} : Bool},
  +h6: {Nat.is_eq(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b))) == True{} : Bool},
  +hk7: {RD.keys_le(f, tl) == True{} : Bool},
  +hk8: {RD.keys_le(b, tl) == True{} : Bool}) ->
  {RD.keys_le(f, kx) == True{} : Bool} & {RD.keys_le(b, kx) == True{} : Bool}:
  match zb:
    case True{}:
      +e0 = N.eq_sound(bn, 0n, hzb)
      +es = Equal.trans(Nat, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), bn, 0n, Equal.sym(Nat, bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), N.eq_sound(bn, Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), h6)), e0)
      (len0_keys(f, kx, N.add_eq_zero_l(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b), es)), len0_keys(b, kx, N.add_eq_zero_r(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b), es)))
    case False{}:
      (keys_mono(f, tl, kx, hk7, hz), keys_mono(b, tl, kx, hk8, hz))

def add_end.k2(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +kf: {RD.keys_le(f, kx) == True{} : Bool},
  +kb: {RD.keys_le(b, kx) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>,
  +eqp: {NR.put_txt(t, C.BT(obl, obt), C.BT(sl, st), s, sn) == (C.BT(l2, t2), C.BT(sl, st)) : D.Bytes & D.Bytes},
  +ok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +etx: {FL.TXT(l2, t2) == String.append(FL.TXT(obl, obt), tx) : String},
  +eln: {U32.to_nat(l2) == Nat.add(U32.to_nat(obl), String.length(tx)) : Nat}) -> EndG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  +RP2 = {P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f, NR.Ck{kx, ipx, lnx, psx, nx} <> b, 1n+bn, kx, k, l2, t2, ow, ns, False{}} : P.RunP}
  +eq = AB.subst(D.Bytes & D.Bytes, z => {NR.at_end.fin(NR.Ck{kx, ipx, lnx, psx, nx}, kx, z, nl, True{}, h, c, C.BT(cbl, cbt), e, l, f, b, bn, k, ow, ns, False{}) == (P.mkRun(RP2), C.BT(sl, st)) : NR.Run & D.Bytes},
    (C.BT(l2, t2), C.BT(sl, st)), NR.put_txt(t, C.BT(obl, obt), C.BT(sl, st), s, sn), Equal.sym(D.Bytes & D.Bytes, NR.put_txt(t, C.BT(obl, obt), C.BT(sl, st), s, sn), (C.BT(l2, t2), C.BT(sl, st)), eqp), {==})
  +hok = PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
  +LX = RD.lens(RD.items(f, b))
  +esum = N.eq_sound(Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), PI.pr5(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
  +hwo = PI.pr11(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
  +htl = txt_len(obl, obt, hok)
  +hwoT = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(ow), y) == True{} : Bool}, U32.to_nat(obl), String.length(FL.TXT(obl, obt)), Equal.sym(Nat, String.length(FL.TXT(obl, obt)), U32.to_nat(obl), htl), hwo)
  +T = String.drop(FL.TXT(obl, obt), U32.to_nat(ow))
  +eT = Equal.trans(Nat, String.length(T), Nat.sub(String.length(FL.TXT(obl, obt)), U32.to_nat(ow)), LX, INS.s_len_drop(FL.TXT(obl, obt), U32.to_nat(ow)),
    Equal.trans(Nat, Nat.sub(String.length(FL.TXT(obl, obt)), U32.to_nat(ow)), Nat.sub(U32.to_nat(obl), U32.to_nat(ow)), LX,
      Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(ow)), String.length(FL.TXT(obl, obt)), U32.to_nat(obl), htl),
      Equal.trans(Nat, Nat.sub(U32.to_nat(obl), U32.to_nat(ow)), Nat.sub(Nat.add(U32.to_nat(ow), LX), U32.to_nat(ow)), LX,
        Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(ow)), U32.to_nat(obl), Nat.add(U32.to_nat(ow), LX), Equal.sym(Nat, Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), esum)),
        N.sub_add_l(U32.to_nat(ow), LX))))
  +hk = keys_app(f, NR.rev_ck(b, Nil{}), kx, kf, FL.keys_rev(b, Nil{}, kx, kb, {==}))
  +ie = INS.ins_end(RD.items(f, b), NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), T, tx, hk, eT, hxl)
  +eb = INS.end_buf(f, b, NR.Ck{kx, ipx, lnx, psx, nx})
  +eA = Equal.trans(String, String.drop(FL.TXT(l2, t2), U32.to_nat(ow)), String.drop(String.append(FL.TXT(obl, obt), tx), U32.to_nat(ow)), String.append(T, tx),
    Equal.cong(String, String, y => String.drop(y, U32.to_nat(ow)), FL.TXT(l2, t2), String.append(FL.TXT(obl, obt), tx), etx), INS.s_drop_app(FL.TXT(obl, obt), tx, U32.to_nat(ow), hwoT))
  +espec = Equal.trans(List<&2, R.Item>, FL.ISS(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b), c, l2, t2, ow), NR.spec.items(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), FL.chromof(c), String.drop(FL.TXT(l2, t2), U32.to_nat(ow))), R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)),
    Equal.cong(List<&2, NR.Ck>, List<&2, R.Item>, y => NR.spec.items(y, FL.chromof(c), String.drop(FL.TXT(l2, t2), U32.to_nat(ow))), RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b), NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), eb),
    Equal.trans(List<&2, R.Item>, NR.spec.items(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), FL.chromof(c), String.drop(FL.TXT(l2, t2), U32.to_nat(ow))), NR.spec.items(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), FL.chromof(c), String.append(T, tx)), R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)),
      Equal.cong(String, List<&2, R.Item>, y => NR.spec.items(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), FL.chromof(c), y), String.drop(FL.TXT(l2, t2), U32.to_nat(ow)), String.append(T, tx), eA),
      Equal.sym(List<&2, R.Item>, R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)), NR.spec.items(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), FL.chromof(c), String.append(T, tx)), ie)))
  +eout = Equal.trans(String, String.take(FL.TXT(l2, t2), U32.to_nat(ow)), String.take(String.append(FL.TXT(obl, obt), tx), U32.to_nat(ow)), String.take(FL.TXT(obl, obt), U32.to_nat(ow)),
    Equal.cong(String, String, y => String.take(y, U32.to_nat(ow)), FL.TXT(l2, t2), String.append(FL.TXT(obl, obt), tx), etx), INS.s_take_app(FL.TXT(obl, obt), tx, U32.to_nat(ow), hwoT))
  +A = U32.to_nat(ow)
  +NX = U32.to_nat(nx)
  +E5 = Equal.trans(Nat, Nat.add(A, RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b))), Nat.add(A, Nat.add(LX, Nat.add(NX, 0n))), U32.to_nat(l2),
    Equal.cong(Nat, Nat, y => Nat.add(A, y), RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b)), Nat.add(LX, Nat.add(NX, 0n)),
      Equal.trans(Nat, RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b)), RD.lens(NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}])), Nat.add(LX, Nat.add(NX, 0n)),
        Equal.cong(List<&2, NR.Ck>, Nat, y => RD.lens(y), RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b), NR.append_ck(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]), eb), lens_app(RD.items(f, b), [NR.Ck{kx, ipx, lnx, psx, nx}]))),
    Equal.trans(Nat, Nat.add(A, Nat.add(LX, Nat.add(NX, 0n))), Nat.add(A, Nat.add(LX, NX)), U32.to_nat(l2),
      Equal.cong(Nat, Nat, y => Nat.add(A, Nat.add(LX, y)), Nat.add(NX, 0n), NX, N.add_zero(NX)),
      Equal.trans(Nat, Nat.add(A, Nat.add(LX, NX)), Nat.add(Nat.add(A, LX), NX), U32.to_nat(l2), Equal.sym(Nat, Nat.add(Nat.add(A, LX), NX), Nat.add(A, Nat.add(LX, NX)), N.add_assoc(A, LX, NX)),
        Equal.trans(Nat, Nat.add(Nat.add(A, LX), NX), Nat.add(U32.to_nat(obl), NX), U32.to_nat(l2), Equal.cong(Nat, Nat, y => Nat.add(y, NX), Nat.add(A, LX), U32.to_nat(obl), esum),
          Equal.trans(Nat, Nat.add(U32.to_nat(obl), NX), Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l2), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(obl), y), NX, String.length(tx), Equal.sym(Nat, String.length(tx), NX, hxl)),
            Equal.sym(Nat, U32.to_nat(l2), Nat.add(U32.to_nat(obl), String.length(tx)), eln))))))
  +h5 = AB.subst(Nat, y => {Nat.is_eq(Nat.add(A, RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b))), y) == True{} : Bool}, Nat.add(A, RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b))), U32.to_nat(l2), E5, N.eq_refl(Nat.add(A, RD.lens(RD.items(f, NR.Ck{kx, ipx, lnx, psx, nx} <> b)))))
  +h6 = AB.subst(Nat, y => {Nat.is_eq(1n+bn, y) == True{} : Bool}, 1n+Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), Nat.add(List.length(&2, NR.Ck, f), 1n+List.length(&2, NR.Ck, b)),
    Equal.sym(Nat, Nat.add(List.length(&2, NR.Ck, f), 1n+List.length(&2, NR.Ck, b)), 1n+Nat.add(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b)), N.add_succ(List.length(&2, NR.Ck, f), List.length(&2, NR.Ck, b))), PI.pr6(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
  +hl2 = AB.subst(Nat, y => {Nat.is_le(y, Nat.pow(2n, 30n)) == True{} : Bool}, Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l2), Equal.sym(Nat, U32.to_nat(l2), Nat.add(U32.to_nat(obl), String.length(tx)), eln), hsz)
  +h11 = AB.subst(Nat, y => {Nat.is_le(A, y) == True{} : Bool}, Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l2), Equal.sym(Nat, U32.to_nat(l2), Nat.add(U32.to_nat(obl), String.length(tx)), eln),
    N.le_trans(A, U32.to_nat(obl), Nat.add(U32.to_nat(obl), String.length(tx)), hwo, N.le_add_r(U32.to_nat(obl), String.length(tx))))
  +hinv = PI.inv_mk(True{}, h, c, cbl, cbt, f, NR.Ck{kx, ipx, lnx, psx, nx} <> b, 1n+bn, kx, l2, t2, ow, ns, False{},
    (ok2, (le30w(l2, hl2), (PI.pr3(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr4(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), (h5, (h6, (kf, (LM.and_mk(Nat.is_le(kx, kx), RD.keys_le(b, kx), N.le_refl(kx), kb), (PI.pr9(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), ({==}, h11)))))))))))
  (l2, (t2, (f, (NR.Ck{kx, ipx, lnx, psx, nx} <> b, (1n+bn, (kx, (eq, (hinv, (espec, (eout, eln))))))))))

def add_end.k(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +kf: {RD.keys_le(f, kx) == True{} : Bool},
  +kb: {RD.keys_le(b, kx) == True{} : Bool},
  pt: PutG(t, obl, obt, sl, st, sd, s, sn, tx)) -> EndG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  (+l2, q1) = pt
  (+t2, q2) = q1
  (eqp, q3) = q2
  (ok2, q4) = q3
  (etx, eln) = q4
  add_end.k2(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, kf, kb, l2, t2, eqp, ok2, etx, eln)

def MidG(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  &obl2: U32 -> &obt2: AT.Tree<U32> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &tl2: Nat ->
  ({NR.mid(NR.Ck{kx, ipx, lnx, psx, nx}, kx, t, C.BT(sl, st), s, sn, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl2, obl2, obt2, ow, ns, False{}) == True{} : Bool}
  & ({FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>}
  & ({String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String}
  & {U32.to_nat(obl2) == Nat.add(U32.to_nat(obl), String.length(tx)) : Nat}))))

# The last step: the tail put back after the text.
def mid.k3(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +ktl: {Nat.is_le(kx, tl) == True{} : Bool},
  +ff: {U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)) == Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))) : Nat},
  +l2: U32, +t2: AT.Tree<U32>, +l3: U32, +t3: AT.Tree<U32>,
  +ecut: {NR.cut_tail(C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)) == (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)) : D.Bytes & D.Bytes},
  +ok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +etx2: {FL.TXT(l2, t2) == String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : String},
  +eln2: {U32.to_nat(l2) == Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : Nat},
  +eqt: {NR.put_txt(t, C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(sl, st), s, sn) == (C.BT(l3, t3), C.BT(sl, st)) : D.Bytes & D.Bytes},
  +etx3: {FL.TXT(l3, t3) == String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx) : String},
  +eln3: {U32.to_nat(l3) == Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)) : Nat},
  pb: &l4: U32 -> &t4: AT.Tree<U32> -> BF.PutB(l3, t3, l2, t2, 0, l2, l4, t4)) -> MidG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  (+l4, q1) = pb
  (+t4, q2) = q1
  (eq4, q3) = q2
  (ok4, q4) = q3
  (vw4, ln4) = q4
  +RP4v = {P.RunP{nl, True{}, h, c, cbl, cbt, e, l, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}, 1n+bn, tl, k, l4, t4, ow, ns, False{}} : P.RunP}
  +e1 = AB.subst(D.Bytes & D.Bytes, z => {(NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}, 1n+bn, tl, k, NR.mid.join(z), ow, ns, False{}}, C.BT(sl, st)) == (P.mkRun(RP4v), C.BT(sl, st)) : NR.Run & D.Bytes},
    (C.BT(l4, t4), C.BT(l2, t2)), NR.put_bytes(C.BT(l3, t3), C.BT(l2, t2), 0, l2), Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(l3, t3), C.BT(l2, t2), 0, l2), (C.BT(l4, t4), C.BT(l2, t2)), eq4), {==})
  +e2 = AB.subst(D.Bytes & D.Bytes, z => {NR.mid.fin(NR.Ck{kx, ipx, lnx, psx, nx}, INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)), z, C.BT(l2, t2), NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, Nil{}, bn, tl, k, BY.empty(0n), ow, ns, False{}}) == (P.mkRun(RP4v), C.BT(sl, st)) : NR.Run & D.Bytes},
    (C.BT(l3, t3), C.BT(sl, st)), NR.put_txt(t, C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(sl, st), s, sn), Equal.sym(D.Bytes & D.Bytes, NR.put_txt(t, C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(sl, st), s, sn), (C.BT(l3, t3), C.BT(sl, st)), eqt), e1)
  +e3 = AB.subst(D.Bytes & D.Bytes, z => {NR.mid.k(NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn, INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)), z, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, Nil{}, bn, tl, k, BY.empty(0n), ow, ns, False{}}) == (P.mkRun(RP4v), C.BT(sl, st)) : NR.Run & D.Bytes},
    (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)), NR.cut_tail(C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(D.Bytes & D.Bytes, NR.cut_tail(C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)), ecut), e2)
  +eq = AB.subst(NR.Ins, z => {NR.mid.go(NR.Ck{kx, ipx, lnx, psx, nx}, t, C.BT(sl, st), s, sn, z, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, Nil{}, Nil{}, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}) == (P.mkRun(RP4v), C.BT(sl, st)) : NR.Run & D.Bytes},
    NR.Ins{INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.iplen(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))}, NR.ins.start(RD.items(f, b), kx), Equal.sym(NR.Ins, NR.ins.start(RD.items(f, b), kx), NR.Ins{INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.iplen(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))}, INS.ins_eta(RD.items(f, b), kx)), e3)
  +hok = PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
  +LX = RD.lens(RD.items(f, b))
  +LR = RD.lens(INS.irest(NR.ins.start(RD.items(f, b), kx)))
  +NXn = U32.to_nat(nx)
  +esum = N.eq_sound(Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), PI.pr5(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
  +esp = INS.ins_split(RD.items(f, b), kx)
  +elx = Equal.trans(Nat, LX, RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), Equal.cong(List<&2, NR.Ck>, Nat, y => RD.lens(y), RD.items(f, b), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), Equal.sym(List<&2, NR.Ck>, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), RD.items(f, b), esp)), lens_app(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))))
  +htl = txt_len(obl, obt, hok)
  +hFO = AB.subst(Nat, y => {Nat.is_le(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y) == True{} : Bool}, Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), esum,
    AB.subst(Nat, y => {Nat.is_le(y, Nat.add(U32.to_nat(ow), LX)) == True{} : Bool}, Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), ff),
      N.le_add_mono_l(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LX, AB.subst(Nat, y => {Nat.is_le(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), y) == True{} : Bool}, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), LX, Equal.sym(Nat, LX, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), elx), N.le_add_r(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR)))))
  +hFT = AB.subst(Nat, y => {Nat.is_le(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y) == True{} : Bool}, U32.to_nat(obl), String.length(FL.TXT(obl, obt)), Equal.sym(Nat, String.length(FL.TXT(obl, obt)), U32.to_nat(obl), htl), hFO)
  +lX1 = INS.s_len_take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), hFT)
  +hAF = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(ow), y) == True{} : Bool}, Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), ff), N.le_add_r(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))))
  +hA1 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(ow), y) == True{} : Bool}, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Equal.sym(Nat, String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), lX1), hAF)
  +hA2 = N.le_trans(U32.to_nat(ow), String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx)), hA1,
    AB.subst(Nat, y => {Nat.is_le(String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), y) == True{} : Bool}, Nat.add(String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(tx)), String.length(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx)), Equal.sym(Nat, String.length(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx)), Nat.add(String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(tx)), HD.slen_app(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx)), N.le_add_r(String.length(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(tx))))
  +vl2 = BF.view_all(l2, t2, RD.tdepth(t2), ok2)
  +etx4 = Equal.trans(String, FL.TXT(l4, t4), NR.chars(List.append(&2, U32, D.view(C.BT(l3, t3)), D.view(C.BT(l2, t2)))), String.append(FL.TXT(l3, t3), FL.TXT(l2, t2)), Equal.cong(List<&2, U32>, String, y => NR.chars(y), D.view(C.BT(l4, t4)), List.append(&2, U32, D.view(C.BT(l3, t3)), D.view(C.BT(l2, t2))), Equal.trans(List<&2, U32>, D.view(C.BT(l4, t4)), List.append(&2, U32, D.view(C.BT(l3, t3)), D.slice(D.view(C.BT(l2, t2)), U32.to_nat(0), U32.to_nat(l2))), List.append(&2, U32, D.view(C.BT(l3, t3)), D.view(C.BT(l2, t2))), vw4, Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, D.view(C.BT(l3, t3)), y), D.slice(D.view(C.BT(l2, t2)), U32.to_nat(0), U32.to_nat(l2)), D.view(C.BT(l2, t2)), vl2))), BF.chars_app(D.view(C.BT(l3, t3)), D.view(C.BT(l2, t2))))
  +W4 = String.append(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))
  +e4w = Equal.trans(String, FL.TXT(l4, t4), String.append(FL.TXT(l3, t3), FL.TXT(l2, t2)), W4, etx4, Equal.trans(String, String.append(FL.TXT(l3, t3), FL.TXT(l2, t2)), String.append(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), FL.TXT(l2, t2)), W4, Equal.cong(String, String, y => String.append(y, FL.TXT(l2, t2)), FL.TXT(l3, t3), String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), etx3), Equal.cong(String, String, y => String.append(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), y), FL.TXT(l2, t2), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), etx2)))
  +TP = String.take(String.drop(FL.TXT(obl, obt), U32.to_nat(ow)), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))
  +DP = String.drop(String.drop(FL.TXT(obl, obt), U32.to_nat(ow)), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))
  +eD = Equal.trans(String, String.drop(FL.TXT(l4, t4), U32.to_nat(ow)), String.drop(W4, U32.to_nat(ow)), String.append(TP, String.append(tx, DP)), Equal.cong(String, String, y => String.drop(y, U32.to_nat(ow)), FL.TXT(l4, t4), W4, e4w), Equal.trans(String, String.drop(W4, U32.to_nat(ow)), String.append(String.drop(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), U32.to_nat(ow)), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.append(TP, String.append(tx, DP)), INS.s_drop_app(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow), hA2), Equal.trans(String, String.append(String.drop(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), U32.to_nat(ow)), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.append(String.append(String.drop(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow)), tx), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.append(TP, String.append(tx, DP)), Equal.cong(String, String, y => String.append(y, String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.drop(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), U32.to_nat(ow)), String.append(String.drop(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow)), tx), INS.s_drop_app(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx, U32.to_nat(ow), hA1)), Equal.trans(String, String.append(String.append(String.drop(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow)), tx), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.append(String.append(TP, tx), DP), String.append(TP, String.append(tx, DP)), AB.subst(Nat, y => {String.append(String.append(String.drop(String.take(FL.TXT(obl, obt), y), U32.to_nat(ow)), tx), String.drop(FL.TXT(obl, obt), y)) == String.append(String.append(TP, tx), DP) : String}, Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), ff), Equal.trans(String, String.append(String.append(String.drop(String.take(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))), U32.to_nat(ow)), tx), String.drop(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))))), String.append(String.append(TP, tx), String.drop(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))))), String.append(String.append(TP, tx), DP), Equal.cong(String, String, y => String.append(String.append(y, tx), String.drop(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))))), String.drop(String.take(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))), U32.to_nat(ow)), TP, INS.s_drop_take(FL.TXT(obl, obt), U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))), Equal.cong(String, String, y => String.append(String.append(TP, tx), y), String.drop(FL.TXT(obl, obt), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))), DP, INS.s_drop_drop(FL.TXT(obl, obt), U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))))), RBS.s_append_assoc(TP, tx, DP)))))
  +eO = Equal.trans(String, String.take(FL.TXT(l4, t4), U32.to_nat(ow)), String.take(W4, U32.to_nat(ow)), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), Equal.cong(String, String, y => String.take(y, U32.to_nat(ow)), FL.TXT(l4, t4), W4, e4w), Equal.trans(String, String.take(W4, U32.to_nat(ow)), String.take(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), U32.to_nat(ow)), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), INS.s_take_app(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow), hA2), Equal.trans(String, String.take(String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), U32.to_nat(ow)), String.take(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(ow)), String.take(FL.TXT(obl, obt), U32.to_nat(ow)), INS.s_take_app(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx, U32.to_nat(ow), hA1), AB.subst(Nat, y => {String.take(String.take(FL.TXT(obl, obt), y), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String}, Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), ff), INS.s_take_take(FL.TXT(obl, obt), U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))))))))
  +eT = Equal.trans(Nat, String.length(String.drop(FL.TXT(obl, obt), U32.to_nat(ow))), Nat.sub(String.length(FL.TXT(obl, obt)), U32.to_nat(ow)), LX, INS.s_len_drop(FL.TXT(obl, obt), U32.to_nat(ow)), Equal.trans(Nat, Nat.sub(String.length(FL.TXT(obl, obt)), U32.to_nat(ow)), Nat.sub(U32.to_nat(obl), U32.to_nat(ow)), LX, Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(ow)), String.length(FL.TXT(obl, obt)), U32.to_nat(obl), htl), Equal.trans(Nat, Nat.sub(U32.to_nat(obl), U32.to_nat(ow)), Nat.sub(Nat.add(U32.to_nat(ow), LX), U32.to_nat(ow)), LX, Equal.cong(Nat, Nat, y => Nat.sub(y, U32.to_nat(ow)), U32.to_nat(obl), Nat.add(U32.to_nat(ow), LX), Equal.sym(Nat, Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), esum)), N.sub_add_l(U32.to_nat(ow), LX))))
  +im = INS.ins_mid(RD.items(f, b), NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), String.drop(FL.TXT(obl, obt), U32.to_nat(ow)), tx, eT, hxl)
  +espec = Equal.trans(List<&2, R.Item>, FL.ISS(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), c, l4, t4, ow), NR.spec.items(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), FL.chromof(c), String.append(TP, String.append(tx, DP))), R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)), Equal.cong(String, List<&2, R.Item>, y => NR.spec.items(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), FL.chromof(c), y), String.drop(FL.TXT(l4, t4), U32.to_nat(ow)), String.append(TP, String.append(tx, DP)), eD), Equal.sym(List<&2, R.Item>, R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)), NR.spec.items(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), FL.chromof(c), String.append(TP, String.append(tx, DP))), im))
  +L2n = U32.to_nat(l2)
  +L3n = U32.to_nat(l3)
  +SUBn = Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))
  +eln = Equal.trans(Nat, U32.to_nat(l4), Nat.add(L3n, L2n), Nat.add(U32.to_nat(obl), String.length(tx)), ln4, Equal.trans(Nat, Nat.add(L3n, L2n), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), SUBn), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.trans(Nat, Nat.add(L3n, L2n), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), L2n), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), SUBn), Equal.cong(Nat, Nat, y => Nat.add(y, L2n), L3n, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), eln3), Equal.cong(Nat, Nat, y => Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), y), L2n, SUBn, eln2)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), SUBn), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(String.length(tx), SUBn)), Nat.add(U32.to_nat(obl), String.length(tx)), N.add_assoc(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx), SUBn), Equal.trans(Nat, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(String.length(tx), SUBn)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(SUBn, String.length(tx))), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y), Nat.add(String.length(tx), SUBn), Nat.add(SUBn, String.length(tx)), N.add_comm(String.length(tx), SUBn)), Equal.trans(Nat, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(SUBn, String.length(tx))), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), SUBn), String.length(tx)), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), SUBn), String.length(tx)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(SUBn, String.length(tx))), N.add_assoc(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), SUBn, String.length(tx))), Equal.cong(Nat, Nat, y => Nat.add(y, String.length(tx)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), SUBn), U32.to_nat(obl), N.le_sub_add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl), hFO)))))))
  +E5 = Equal.trans(Nat, Nat.add(U32.to_nat(ow), RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), Nat.add(NXn, LR))), U32.to_nat(l4), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(ow), y), RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), Nat.add(NXn, LR)), lens_app(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), Equal.trans(Nat, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), Nat.add(NXn, LR))), Nat.add(NXn, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))), U32.to_nat(l4), Equal.trans(Nat, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), Nat.add(NXn, LR))), Nat.add(U32.to_nat(ow), Nat.add(NXn, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))), Nat.add(NXn, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(ow), y), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), Nat.add(NXn, LR)), Nat.add(NXn, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR)), N.add_left_comm(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), NXn, LR)), N.add_left_comm(U32.to_nat(ow), NXn, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))), Equal.trans(Nat, Nat.add(NXn, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))), Nat.add(NXn, U32.to_nat(obl)), U32.to_nat(l4), Equal.cong(Nat, Nat, y => Nat.add(NXn, y), Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR)), U32.to_nat(obl), Equal.trans(Nat, Nat.add(U32.to_nat(ow), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR)), Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(ow), y), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), LX, Equal.sym(Nat, LX, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), elx)), esum)), Equal.trans(Nat, Nat.add(NXn, U32.to_nat(obl)), Nat.add(U32.to_nat(obl), NXn), U32.to_nat(l4), N.add_comm(NXn, U32.to_nat(obl)), Equal.trans(Nat, Nat.add(U32.to_nat(obl), NXn), Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l4), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(obl), y), NXn, String.length(tx), Equal.sym(Nat, String.length(tx), NXn, hxl)), Equal.sym(Nat, U32.to_nat(l4), Nat.add(U32.to_nat(obl), String.length(tx)), eln))))))
  +h5 = AB.subst(Nat, y => {Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), y) == True{} : Bool}, Nat.add(U32.to_nat(ow), RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), U32.to_nat(l4), E5, N.eq_refl(Nat.add(U32.to_nat(ow), RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))))))
  +LF = List.length(&2, NR.Ck, f)
  +LB = List.length(&2, NR.Ck, b)
  +LPRE = List.length(&2, NR.Ck, INS.ipre(NR.ins.start(RD.items(f, b), kx)))
  +LREST = List.length(&2, NR.Ck, INS.irest(NR.ins.start(RD.items(f, b), kx)))
  +eXl = Equal.trans(Nat, List.length(&2, NR.Ck, RD.items(f, b)), Nat.add(LF, List.length(&2, NR.Ck, NR.rev_ck(b, Nil{}))), Nat.add(LF, LB), len_app_ck(f, NR.rev_ck(b, Nil{})), Equal.cong(Nat, Nat, y => Nat.add(LF, y), List.length(&2, NR.Ck, NR.rev_ck(b, Nil{})), LB, Equal.trans(Nat, List.length(&2, NR.Ck, NR.rev_ck(b, Nil{})), Nat.add(LB, 0n), LB, FL.len_rev(b, Nil{}), N.add_zero(LB))))
  +E6 = Equal.trans(Nat, Nat.add(List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), 0n), List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), 1n+bn, N.add_zero(List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), Equal.trans(Nat, List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), Nat.add(LPRE, 1n+LREST), 1n+bn, len_app_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Equal.trans(Nat, Nat.add(LPRE, 1n+LREST), 1n+Nat.add(LPRE, LREST), 1n+bn, N.add_succ(LPRE, LREST), Equal.cong(Nat, Nat, y => 1n+y, Nat.add(LPRE, LREST), bn, Equal.trans(Nat, Nat.add(LPRE, LREST), List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), bn, Equal.sym(Nat, List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), Nat.add(LPRE, LREST), len_app_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), Equal.trans(Nat, List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), List.length(&2, NR.Ck, RD.items(f, b)), bn, Equal.cong(List<&2, NR.Ck>, Nat, y => List.length(&2, NR.Ck, y), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), RD.items(f, b), esp), Equal.trans(Nat, List.length(&2, NR.Ck, RD.items(f, b)), Nat.add(LF, LB), bn, eXl, Equal.sym(Nat, bn, Nat.add(LF, LB), N.eq_sound(bn, Nat.add(LF, LB), PI.pr6(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))))))))))
  +h6 = AB.subst(Nat, y => {Nat.is_eq(1n+bn, y) == True{} : Bool}, 1n+bn, Nat.add(List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), 0n), Equal.sym(Nat, Nat.add(List.length(&2, NR.Ck, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)))), 0n), 1n+bn, E6), N.eq_refl(1n+bn))
  +kXS = keys_app(f, NR.rev_ck(b, Nil{}), tl, PI.pr7(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), FL.keys_rev(b, Nil{}, tl, PI.pr8(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), {==}))
  +ksp = AB.subst(List<&2, NR.Ck>, y => {RD.keys_le(y, tl) == True{} : Bool}, RD.items(f, b), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), Equal.sym(List<&2, NR.Ck>, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), RD.items(f, b), esp), kXS)
  +h7 = keys_app(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx)), tl, keys_appl(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)), tl, ksp), LM.and_mk(Nat.is_le(kx, tl), RD.keys_le(INS.irest(NR.ins.start(RD.items(f, b), kx)), tl), ktl, keys_appr(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)), tl, ksp)))
  +hl4 = AB.subst(Nat, y => {Nat.is_le(y, Nat.pow(2n, 30n)) == True{} : Bool}, Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l4), Equal.sym(Nat, U32.to_nat(l4), Nat.add(U32.to_nat(obl), String.length(tx)), eln), hsz)
  +h11 = AB.subst(Nat, y => {Nat.is_le(U32.to_nat(ow), y) == True{} : Bool}, Nat.add(U32.to_nat(obl), String.length(tx)), U32.to_nat(l4), Equal.sym(Nat, U32.to_nat(l4), Nat.add(U32.to_nat(obl), String.length(tx)), eln),
    N.le_trans(U32.to_nat(ow), U32.to_nat(obl), Nat.add(U32.to_nat(obl), String.length(tx)), PI.pr11(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), N.le_add_r(U32.to_nat(obl), String.length(tx))))
  +h5b = AB.subst(List<&2, NR.Ck>, y => {Nat.is_eq(Nat.add(U32.to_nat(ow), RD.lens(y)), U32.to_nat(l4)) == True{} : Bool}, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), NR.append_ck(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}), Equal.sym(List<&2, NR.Ck>, NR.append_ck(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), FL.append_ck_nil(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), h5)
  +hinv = PI.inv_mk(True{}, h, c, cbl, cbt, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}, 1n+bn, tl, l4, t4, ow, ns, False{},
    (ok4, (le30w(l4, hl4), (PI.pr3(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), (PI.pr4(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), (h5b, (h6, (h7, ({==}, (PI.pr9(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), ({==}, h11)))))))))))
  +espec2 = AB.subst(List<&2, NR.Ck>, y => {FL.ISS(y, c, l4, t4, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>}, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), NR.append_ck(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}), Equal.sym(List<&2, NR.Ck>, NR.append_ck(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), Nil{}), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), FL.append_ck_nil(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))))), espec)
  (l4, (t4, (NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), NR.Ck{kx, ipx, lnx, psx, nx} <> INS.irest(NR.ins.start(RD.items(f, b), kx))), (Nil{}, (1n+bn, (tl, (eq, (hinv, (espec2, (eO, eln))))))))))

def mid.k2(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +ktl: {Nat.is_le(kx, tl) == True{} : Bool},
  +ff: {U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)) == Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))) : Nat},
  +hFO: {Nat.is_le(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl)) == True{} : Bool},
  +l2: U32, +t2: AT.Tree<U32>,
  +ecut: {NR.cut_tail(C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)) == (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)) : D.Bytes & D.Bytes},
  +ok2: {D.ok(C.BT(l2, t2), RD.tdepth(t2)) == True{} : Bool},
  +etx2: {FL.TXT(l2, t2) == String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : String},
  +eln2: {U32.to_nat(l2) == Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : Nat},
  +eTF: {FL.TXT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt) == String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : String},
  pt: &l3: U32 -> &t3: AT.Tree<U32> -> ({NR.put_txt(t, C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(sl, st), s, sn) == (C.BT(l3, t3), C.BT(sl, st)) : D.Bytes & D.Bytes} & PutT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt, l3, t3, tx))) -> MidG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  (+l3, q1) = pt
  (+t3, q2) = q1
  (eqt, q3) = q2
  (ok3, q4) = q3
  (etx3a, eln3a) = q4
  +eln3 = Equal.trans(Nat, U32.to_nat(l3), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), eln3a, {==})
  +etx3 = Equal.trans(String, FL.TXT(l3, t3), String.append(FL.TXT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), tx), String.append(String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), tx), etx3a, Equal.cong(String, String, y => String.append(y, tx), FL.TXT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), eTF))
  +L23 = Equal.trans(Nat, Nat.add(U32.to_nat(l3), U32.to_nat(l2)), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.trans(Nat, Nat.add(U32.to_nat(l3), U32.to_nat(l2)), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), U32.to_nat(l2)), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Equal.cong(Nat, Nat, y => Nat.add(y, U32.to_nat(l2)), U32.to_nat(l3), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), eln3), Equal.cong(Nat, Nat, y => Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), y), U32.to_nat(l2), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), eln2)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(String.length(tx), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))), Nat.add(U32.to_nat(obl), String.length(tx)), N.add_assoc(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Equal.trans(Nat, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(String.length(tx), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), String.length(tx))), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y), Nat.add(String.length(tx), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Nat.add(Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), String.length(tx)), N.add_comm(String.length(tx), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))), Equal.trans(Nat, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), String.length(tx))), Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(tx)), Nat.add(U32.to_nat(obl), String.length(tx)), Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.length(tx)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), String.length(tx))), N.add_assoc(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), String.length(tx))), Equal.cong(Nat, Nat, y => Nat.add(y, String.length(tx)), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), U32.to_nat(obl), N.le_sub_add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl), hFO))))))
  +hL3 = AB.subst(Nat, y => {Nat.is_lt(Nat.add(y, 8n), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}, Nat.add(U32.to_nat(obl), String.length(tx)), Nat.add(U32.to_nat(l3), U32.to_nat(l2)), Equal.sym(Nat, Nat.add(U32.to_nat(l3), U32.to_nat(l2)), Nat.add(U32.to_nat(obl), String.length(tx)), L23), SZ.lt31(Nat.add(U32.to_nat(obl), String.length(tx)), hsz))
  mid.k3(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, ktl, ff, l2, t2, l3, t3, ecut, ok2, etx2, eln2, eqt, etx3, eln3,
    BF.put_bytes_t(l3, t3, l2, t2, RD.tdepth(t2), 0, l2, ok3, ok2, N.le_refl(U32.to_nat(l2)), hL3))

def mid.k1(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +ktl: {Nat.is_le(kx, tl) == True{} : Bool},
  +ff: {U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)) == Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))) : Nat},
  +hFO: {Nat.is_le(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl)) == True{} : Bool},
  +eL2: {U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)) == Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))) : Nat},
  htx: TxtP(t, sl, st, sd, s, sn, tx),
  pb: &l2: U32 -> &t2: AT.Tree<U32> -> BF.PutB(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0), obl, obt, (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), (obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32), l2, t2)) -> MidG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  (+l2, q1) = pb
  (+t2, q2) = q1
  (eq1, q3) = q2
  (ok2, q4) = q3
  (vw2, ln2) = q4
  +ea = AB.subst(D.Bytes & D.Bytes, z => {NR.cut_tail.k((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), z) == (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)) : D.Bytes & D.Bytes}, (C.BT(l2, t2), C.BT(obl, obt)), NR.put_bytes(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0)), C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), (obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)),
    Equal.sym(D.Bytes & D.Bytes, NR.put_bytes(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0)), C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), (obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), (C.BT(l2, t2), C.BT(obl, obt)), eq1), {==})
  +ecut = AB.subst(D.Bytes, z => {NR.cut_tail.k((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), NR.put_bytes(z, C.BT(obl, obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), (obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32))) == (C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), C.BT(l2, t2)) : D.Bytes & D.Bytes}, C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0)), BY.empty(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32))),
    Equal.sym(D.Bytes, BY.empty(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32))), C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0)), G.empty_eq(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)))), ea)
  +hok = PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
  +V = D.view(C.BT(obl, obt))
  +hlv = Equal.sym(Nat, List.length(&2, U32, V), U32.to_nat(obl), O.view_size_t(obl, obt, RD.tdepth(obt), hok))
  +ev2 = Equal.trans(List<&2, U32>, D.view(C.BT(l2, t2)), List.append(&2, U32, D.view(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)))), List.drop(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), vw2, Equal.trans(List<&2, U32>, List.append(&2, U32, D.view(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32))), List.drop(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), AB.subst(List<&2, U32>, y => {List.append(&2, U32, y, D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)))) == D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32))) : List<&2, U32>}, Nil{}, D.view(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0))), Equal.sym(List<&2, U32>, D.view(C.BT(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0))), Nil{}, BF.view0(G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0))), {==}), Equal.trans(List<&2, U32>, D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(List.length(&2, U32, V), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), List.drop(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), Equal.trans(List<&2, U32>, D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(List.length(&2, U32, V), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Equal.cong(Nat, List<&2, U32>, y => D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), eL2), Equal.cong(Nat, List<&2, U32>, y => D.slice(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(y, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), U32.to_nat(obl), List.length(&2, U32, V), hlv)), BF.slice_rest(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))))
  +etx2 = Equal.trans(String, FL.TXT(l2, t2), NR.chars(List.drop(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.drop(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), Equal.cong(List<&2, U32>, String, y => NR.chars(y), D.view(C.BT(l2, t2)), List.drop(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), ev2), BF.chars_drop(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))
  +eln2 = Equal.trans(Nat, U32.to_nat(l2), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), ln2, eL2)
  +eTF = Equal.trans(String, FL.TXT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt), NR.chars(List.take(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), String.take(FL.TXT(obl, obt), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), Equal.cong(List<&2, U32>, String, y => NR.chars(y), D.view(C.BT((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt)), List.take(&2, U32, V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), O.truncate_view_t(obl, obt, (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), hFO)), BF.chars_take(V, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))))
  +okF = O.truncate_ok_t(obl, obt, RD.tdepth(obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), hok, hFO)
  +hL2 = SZ.lt31(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), N.le_trans(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), String.length(tx)), Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n), N.le_add_mono_r(String.length(tx), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl), hFO), hsz))
  mid.k2(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, ktl, ff, hFO, l2, t2, ecut, ok2, etx2, eln2, eTF, put_txt_t(t, (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obt, sl, st, sd, s, sn, tx, okF, hL2, htx))

def mid_t(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +ktl: {Nat.is_le(kx, tl) == True{} : Bool},
  htx: TxtP(t, sl, st, sd, s, sn, tx)) -> MidG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  +hok = PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi)
  +LX = RD.lens(RD.items(f, b))
  +LR = RD.lens(INS.irest(NR.ins.start(RD.items(f, b), kx)))
  +esum = N.eq_sound(Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), PI.pr5(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
  +esp = INS.ins_split(RD.items(f, b), kx)
  +elx = Equal.trans(Nat, LX, RD.lens(NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx)))), Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), Equal.cong(List<&2, NR.Ck>, Nat, y => RD.lens(y), RD.items(f, b), NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), Equal.sym(List<&2, NR.Ck>, NR.append_ck(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))), RD.items(f, b), esp)), lens_app(INS.ipre(NR.ins.start(RD.items(f, b), kx)), INS.irest(NR.ins.start(RD.items(f, b), kx))))
  +hob = w30(obl, PI.pr2(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))
  +hoM = N.le_trans(U32.to_nat(obl), Nat.add(U32.to_nat(obl), 8n), Nat.mul(4n, Nat.pow(2n, 29n)), N.le_add_r(U32.to_nat(obl), 8n), N.lt_to_le(Nat.add(U32.to_nat(obl), 8n), Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(U32.to_nat(obl), hob)))
  +hLX = AB.subst(Nat, y => {Nat.is_le(LX, y) == True{} : Bool}, Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), esum, N.le_add_l(LX, U32.to_nat(ow)))
  +epl = INS.ins_plen(RD.items(f, b), kx, N.le_trans(LX, U32.to_nat(obl), Nat.mul(4n, Nat.pow(2n, 29n)), hLX, hoM))
  +hPL = AB.subst(Nat, y => {Nat.is_le(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), y) == True{} : Bool}, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), LX, Equal.sym(Nat, LX, Nat.add(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR), elx), N.le_add_r(RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LR))
  +hAPo = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), y) == True{} : Bool}, Nat.add(U32.to_nat(ow), LX), U32.to_nat(obl), esum, N.le_add_mono_l(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), LX, hPL))
  +hfit = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat(ow), y), Nat.mul(4n, Nat.pow(2n, 29n))) == True{} : Bool}, RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), U32.to_nat(INS.iplen(NR.ins.start(RD.items(f, b), kx))), Equal.sym(Nat, U32.to_nat(INS.iplen(NR.ins.start(RD.items(f, b), kx))), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), epl), N.le_trans(Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat(obl), Nat.mul(4n, Nat.pow(2n, 29n)), hAPo, hoM))
  +eadd = C.add_fits(ow, INS.iplen(NR.ins.start(RD.items(f, b), kx)), 29n, {==}, hfit)
  +ff = Equal.trans(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), U32.to_nat(INS.iplen(NR.ins.start(RD.items(f, b), kx)))), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), eadd, Equal.cong(Nat, Nat, y => Nat.add(U32.to_nat(ow), y), U32.to_nat(INS.iplen(NR.ins.start(RD.items(f, b), kx))), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx))), epl))
  +hFO = AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(obl)) == True{} : Bool}, Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Equal.sym(Nat, U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.add(U32.to_nat(ow), RD.lens(INS.ipre(NR.ins.start(RD.items(f, b), kx)))), ff), hAPo)
  +hU = Equal.trans(Bool, U32.is_le((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obl), Nat.is_le(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl)), True{}, U.is_le_to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), obl), hFO)
  +eL2 = U.to_nat_sub_le(obl, (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), hU)
  +hs1 = AB.subst(Nat, y => {Nat.is_le(Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), y), U32.to_nat(obl)) == True{} : Bool}, Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Equal.sym(Nat, U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), eL2),
    AB.subst(Nat, y => {Nat.is_le(y, U32.to_nat(obl)) == True{} : Bool}, U32.to_nat(obl), Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), Equal.sym(Nat, Nat.add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)))), U32.to_nat(obl), N.le_sub_add(U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32)), U32.to_nat(obl), hFO)), N.le_refl(U32.to_nat(obl))))
  +hsub = AB.subst(Nat, y => {Nat.is_le(y, Nat.pow(2n, 30n)) == True{} : Bool}, Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Equal.sym(Nat, U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), eL2), N.le_trans(Nat.sub(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), U32.to_nat(obl), Nat.pow(2n, 30n), U.sub_le(U32.to_nat(obl), U32.to_nat((ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32))), hob))
  +hL1 = NM.lt_c0(U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), Nat.mul(4n, Nat.pow(2n, 29n)), SZ.lt31(U32.to_nat((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32)), hsub))
  mid.k1(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, ktl, ff, hFO, eL2, htx,
    BF.put_bytes_t(0, G.tnew(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), 0), obl, obt, RD.tdepth(obt), (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32), (obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32), BF.empty_ok_td(NR.depth(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32)), NM.depth_le(((obl - (ow + INS.iplen(NR.ins.start(RD.items(f, b), kx)) : U32) : U32) + 8 : U32))), hok, hs1, hL1))

def AddIf(z: Bool, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String) -> Type:
  &obl2: U32 -> &obt2: AT.Tree<U32> -> &f2: List<&2, NR.Ck> -> &b2: List<&2, NR.Ck> -> &bn2: Nat -> &tl2: Nat ->
  ({NR.add.if(z, NR.Ck{kx, ipx, lnx, psx, nx}, kx, t, C.BT(sl, st), s, sn, NR.Run{nl, True{}, h, c, C.BT(cbl, cbt), e, l, f, b, bn, tl, k, C.BT(obl, obt), ow, ns, False{}}) == (P.mkRun(P.RunP{nl, True{}, h, c, cbl, cbt, e, l, f2, b2, bn2, tl2, k, obl2, obt2, ow, ns, False{}}), C.BT(sl, st)) : NR.Run & D.Bytes}
  & ({RD.inv.k(True{}, h, c, cbl, cbt, f2, b2, bn2, tl2, obl2, obt2, ow, ns, False{}) == True{} : Bool}
  & ({FL.ISS(RD.items(f2, b2), c, obl2, obt2, ow) == R.insert(NR.spec.item(NR.Ck{kx, ipx, lnx, psx, nx}, FL.chromof(c), tx), FL.ISS(RD.items(f, b), c, obl, obt, ow)) : List<&2, R.Item>}
  & ({String.take(FL.TXT(obl2, obt2), U32.to_nat(ow)) == String.take(FL.TXT(obl, obt), U32.to_nat(ow)) : String}
  & {U32.to_nat(obl2) == Nat.add(U32.to_nat(obl), String.length(tx)) : Nat}))))

law or_false_r:
  for +a: Bool
  for +b: Bool
  for +h: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_false_r(a, b, h):
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, AB.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case False{}:
      h

def add_c(+zb: Bool, +ze: Bool, +t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  +hzb: {Nat.is_eq(bn, 0n) == zb : Bool},
  +hze: {Bool.or(zb, Nat.is_le(tl, kx)) == ze : Bool},
  htx: TxtP(t, sl, st, sd, s, sn, tx)) -> AddIf(ze, t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  match ze:
    case True{}:
      +hL = SZ.lt31(Nat.add(U32.to_nat(obl), String.length(tx)), hsz)
      add_end.k(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz,
        FL.pf({RD.keys_le(f, kx) == True{} : Bool}, {RD.keys_le(b, kx) == True{} : Bool}, end_k(zb, bn, tl, kx, f, b, hzb, hze, PI.pr6(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), PI.pr7(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), PI.pr8(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))),
        FL.ps({RD.keys_le(f, kx) == True{} : Bool}, {RD.keys_le(b, kx) == True{} : Bool}, end_k(zb, bn, tl, kx, f, b, hzb, hze, PI.pr6(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), PI.pr7(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), PI.pr8(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi))),
        put_txt_t(t, obl, obt, sl, st, sd, s, sn, tx, PI.pr1(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}, hi), hL, htx))
    case False{}:
      +ktl = N.lt_to_le(kx, tl, N.not_le_lt(tl, kx, or_false_r(zb, Nat.is_le(tl, kx), hze)))
      mid_t(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, ktl, htx)

def add_t(+t: NR.Txt, +nl: Nat, +h: String, +c: Maybe<&2, String>, +cbl: U32, +cbt: AT.Tree<U32>, +e: List<&2, String>, +l: Maybe<&2, NR.Ck>, +f: List<&2, NR.Ck>, +b: List<&2, NR.Ck>, +bn: Nat, +tl: Nat, +k: R.Cnt, +obl: U32, +obt: AT.Tree<U32>, +ow: U32, +ns: List<&2, B.Note>, +kx: Nat, +ipx: Nat, +lnx: Nat, +psx: Maybe<&2, String>, +nx: U32, +sl: U32, +st: AT.Tree<U32>, +sd: Nat, +s: U32, +sn: U32, +tx: String,
  +hi: {RD.inv.k(True{}, h, c, cbl, cbt, f, b, bn, tl, obl, obt, ow, ns, False{}) == True{} : Bool},
  +hxl: {String.length(tx) == U32.to_nat(nx) : Nat},
  +hsz: {Nat.is_le(Nat.add(U32.to_nat(obl), String.length(tx)), Nat.pow(2n, 30n)) == True{} : Bool},
  htx: TxtP(t, sl, st, sd, s, sn, tx)) -> AddG(t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx):
  add_c(Nat.is_eq(bn, 0n), Bool.or(Nat.is_eq(bn, 0n), Nat.is_le(tl, kx)), t, nl, h, c, cbl, cbt, e, l, f, b, bn, tl, k, obl, obt, ow, ns, kx, ipx, lnx, psx, nx, sl, st, sd, s, sn, tx, hi, hxl, hsz, {==}, {==}, htx)
