import Base
import ./norm_seq.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_enc.bend as EN
import ./proof_b_lines_str.bend as S
import ./proof_b_lines_pd.bend as Y
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/proof_core.bend as C
import lawful-bytes@0.1.1.0/proof_find.bend as FD

# A piece given by the driver as a source from 0 (piece_src of
# proof_b_lines.bend), through the enc area's enc_bt and enc_ok.

def piece_txt(+c: String, +hv: {D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}) ->
  {P.srctext(P.SBP{U32.from_nat(String.length(c)), EN.enc_t(c), E.depth(String.length(c)), 0}) == c : String}:
  +V = D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)))
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, V, 0n), V, FD.drop_zero(V)) : {NR.chars(_) == c : String}
  %Equal.sym(List<&2, U32>, V, E.codes(c), hv) : {NR.chars(_) == c : String}
  S.chars_codes(c)

def piece_src.k(+c: String,
  r: {D.ok(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c)), E.depth(String.length(c))) == True{} : Bool}
  & ({D.view(C.BT(U32.from_nat(String.length(c)), EN.enc_t(c))) == E.codes(c) : List<&2, U32>}
  & ({Nat.is_le(E.depth(String.length(c)), 29n) == True{} : Bool}
  & {U32.to_nat(U32.from_nat(String.length(c))) == String.length(c) : Nat}))) ->
  &sp: P.SrcP -> ({Norm.SB{E.enc(c), 0} == P.mkSrc(sp) : Norm.Src}
  & ({P.src_ok(sp) == True{} : Bool}
  & {P.srctext(sp) == c : String})):
  (hok, r1) = r
  (hv, r2) = r1
  +L = U32.from_nat(String.length(c))
  (P.SBP{L, EN.enc_t(c), E.depth(String.length(c)), 0},
    (Equal.cong(D.Bytes, Norm.Src, b => Norm.SB{b, 0}, E.enc(c), C.BT(L, EN.enc_t(c)), EN.enc_bt(c)),
    (Y.and_le0(D.ok(C.BT(L, EN.enc_t(c)), E.depth(String.length(c))), L, hok),
    piece_txt(c, hv))))
