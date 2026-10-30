import Base
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
import lawful-bytes@0.1.0.0/proof_core.bend as C
import lawful-bytes@0.1.0.0/proof_same.bend as SM
import lawful-words@0.1.0.0/proof_nat.bend as N
import ./proof_b_cache_lem.bend as X
import ./proof_b_enc.bend as PE
import ./proof_b_enc_lem.bend as EL
import ./proof_b_defs.bend as P

# The text of a reference answer's buffer is its letters (from the enc
# area's enc_bt and enc_ok).

# The text of a byte text's buffer, from enc_ok's parts.
def te.go(+s: String,
  +hok: {D.ok(C.BT(U32.from_nat(String.length(s)), PE.enc_t(s)), E.depth(String.length(s))) == True{} : Bool},
  +hv: {D.view(C.BT(U32.from_nat(String.length(s)), PE.enc_t(s))) == E.codes(s) : List<&2, U32>},
  +hn: {U32.to_nat(U32.from_nat(String.length(s))) == String.length(s) : Nat}) ->
  {Norm.text_of(E.enc(s)) == s : String}:
  +l = U32.from_nat(String.length(s))
  +t = PE.enc_t(s)
  +xs = Pair.snd(D.Bytes, List<&2, U32>, BY.to_list(C.BT(l, t), 0, l))
  %Equal.sym(D.Bytes, E.enc(s), C.BT(l, t), PE.enc_bt(s)) : {Norm.text_of(_) == s : String}
  %Equal.sym(D.Bytes & List<&2, U32>, BY.to_list(C.BT(l, t), 0, l), (C.BT(l, t), xs), SM.to_list_pair_t(l, t, 0, l)) : {Norm.text.all(Norm.text.k(_)) == s : String}
  %Equal.sym(List<&2, U32>, xs, D.slice(D.view(C.BT(l, t)), U32.to_nat(0), U32.to_nat(l)), SM.to_list_view_t(l, t, E.depth(String.length(s)), 0, l, hok, N.le_refl(U32.to_nat(l)))) : {Norm.chars(_) == s : String}
  %Equal.sym(List<&2, U32>, D.view(C.BT(l, t)), E.codes(s), hv) : {Norm.chars(D.slice(_, 0n, U32.to_nat(l))) == s : String}
  %Equal.sym(Nat, U32.to_nat(l), String.length(s), hn) : {Norm.chars(List.take(&2, U32, List.drop(&2, U32, E.codes(s), 0n), _)) == s : String}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, E.codes(s), 0n), E.codes(s), X.drop0(E.codes(s))) : {Norm.chars(List.take(&2, U32, _, String.length(s))) == s : String}
  %Equal.sym(Nat, String.length(s), List.length(&2, U32, E.codes(s)), EL.length_codes(s)) : {Norm.chars(List.take(&2, U32, E.codes(s), _)) == s : String}
  %Equal.sym(List<&2, U32>, List.take(&2, U32, E.codes(s), List.length(&2, U32, E.codes(s))), E.codes(s), X.take_all(E.codes(s))) : {Norm.chars(_) == s : String}
  Pair.snd({E.chars(E.codes(s)) == s : String}, {Norm.chars(E.codes(s)) == s : String}, PE.chars_codes(s))

def te.k(+s: String,
  h: {D.ok(C.BT(U32.from_nat(String.length(s)), PE.enc_t(s)), E.depth(String.length(s))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(s)), PE.enc_t(s))) == E.codes(s) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(s)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(s))) == String.length(s) : Nat}))) ->
  {Norm.text_of(E.enc(s)) == s : String}:
  (h1, h234) = h
  (h2, h34) = h234
  (h3, h4) = h34
  te.go(s, h1, h2, h4)

# A text of bytes within 2^31 letters: the text of its buffer is itself.
def te(+s: String,
  hb: {E.is_bytes(s) == True{} : Bool},
  hn: {P.le31(String.length(s)) == True{} : Bool}) ->
  {Norm.text_of(E.enc(s)) == s : String}:
  te.k(s, PE.enc_ok(s, hb, hn))
