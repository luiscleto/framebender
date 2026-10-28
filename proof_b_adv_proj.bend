import Base
import ./types.bend as B
import ./norm.bend as Norm
import ./norm_fast.bend as NF
import ./proof_b_defs.bend as P
import ./proof_b_cut.bend as CU
import ./proof_b_alleles.bend as AA
import ../lawful-bytes/defs.bend as D
import ../lawful-bytes/proof_core.bend as C
import ../lawful-arrays/proof_tree.bend as AT

# Projections of the tuples other areas' lemmas give (pass_lf, pass_pos,
# pass_alleles, alleles_pass): inner components of a pair pattern cannot be
# bound reusably, so each fact is read by its own lemma (generated).

def n(+x: U32) -> Nat:
  U32.to_nat(x)

def xs(+len: U32, +t: AT.Tree<U32>) -> List<&2, U32>:
  D.view(C.BT(len, t))

def LFT(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32) -> Type:
  CU.LFD(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)

def lf_first(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {D.first(xs(len, t), n(s), n(len), 10) == n(lf) : Nat}:
  match h:
    case (y, z):
      y

def lf_lt(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(lf), n(len)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          y

def lf_s0(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(s), n(e0)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (y, z):
              y

def lf_01(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e0), n(e1)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (y, z):
                  y

def lf_12(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e1), n(e2)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (y, z):
                      y

def lf_23(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e2), n(e3)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (y, z):
                          y

def lf_34(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e3), n(e4)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (y, z):
                              y

def lf_45(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e4), n(e5)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (y, z):
                                  y

def lf_56(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e5), n(e6)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (x7, r7):
                                  match r7:
                                    case (y, z):
                                      y

def lf_67(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_lt(n(e6), n(e7)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (x7, r7):
                                  match r7:
                                    case (x8, r8):
                                      match r8:
                                        case (y, z):
                                          y

def lf_7l(+len: U32, +t: AT.Tree<U32>, +s: U32, +e0: U32, +e1: U32, +e2: U32, +e3: U32, +e4: U32, +e5: U32, +e6: U32, +e7: U32, +lf: U32, h: LFT(len, t, s, e0, e1, e2, e3, e4, e5, e6, e7, lf)) ->
  {Nat.is_le(n(e7), n(lf)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (x7, r7):
                                  match r7:
                                    case (x8, r8):
                                      match r8:
                                        case (y, z):
                                          z

def PPT(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32) -> Type:
  {B.Pos.read(CU.fld(xs(len, t), CU.nx(e0), n(e1))) == Some{n(pos)} : Maybe<&2, Nat>}
  & ({Nat.show(n(pos)) == CU.fld(xs(len, t), CU.nx(e0), n(e1)) : String}
  & {Nat.is_eq(n(pos), 0n) == False{} : Bool})

def pp_read(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, h: PPT(len, t, pos, e0, e1)) ->
  {B.Pos.read(CU.fld(xs(len, t), CU.nx(e0), n(e1))) == Some{n(pos)} : Maybe<&2, Nat>}:
  match h:
    case (y, z):
      y

def pp_show(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, h: PPT(len, t, pos, e0, e1)) ->
  {Nat.show(n(pos)) == CU.fld(xs(len, t), CU.nx(e0), n(e1)) : String}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          y

def pp_nz(+len: U32, +t: AT.Tree<U32>, +pos: U32, +e0: U32, +e1: U32, h: PPT(len, t, pos, e0, e1)) ->
  {Nat.is_eq(n(pos), 0n) == False{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          z

def PAT(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32) -> Type:
  {NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}
  & ({Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat}
  & {Nat.add(n(e3), 1n) == n((e3 + 1 : U32)) : Nat})

def pa_al(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, h: PAT(len, t, e2, e3, e4)) ->
  {NF.alleles(C.BT(len, t), (e2 + 1 : U32), e3, (e3 + 1 : U32), e4) == (C.BT(len, t), True{}) : D.Bytes & Bool}:
  match h:
    case (y, z):
      y

def pa_2(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, h: PAT(len, t, e2, e3, e4)) ->
  {Nat.add(n(e2), 1n) == n((e2 + 1 : U32)) : Nat}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          y

def pa_3(+len: U32, +t: AT.Tree<U32>, +e2: U32, +e3: U32, +e4: U32, h: PAT(len, t, e2, e3, e4)) ->
  {Nat.add(n(e3), 1n) == n((e3 + 1 : U32)) : Nat}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          z

def APT(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32) -> Type:
  {B.Allele.read(Norm.chars(AA.sl(xs(len, t), s3, e3))) == Some{AA.REF(xs(len, t), s3, e3)} : Maybe<&2, List<&2, B.Base>>}
  & ({B.Alleles.read(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == Some{AA.ALTS(xs(len, t), s4, e4)} : Maybe<&2, List<&2, List<&2, B.Base>>>}
  & ({B.Text.is_letters(Norm.chars(AA.sl(xs(len, t), s3, e3))) == True{} : Bool}
  & ({B.Text.any_empty(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Text.any_not_letters(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}
  & ({B.Allele.show(AA.REF(xs(len, t), s3, e3)) == Norm.chars(AA.sl(xs(len, t), s3, e3)) : String}
  & ({String.join(B.Alleles.show(AA.ALTS(xs(len, t), s4, e4)), ",") == Norm.chars(AA.sl(xs(len, t), s4, e4)) : String}
  & ({B.Alleles.distinct(AA.REF(xs(len, t), s3, e3) <> AA.ALTS(xs(len, t), s4, e4)) == True{} : Bool}
  & ({AA.up(AA.sl(xs(len, t), s3, e3)) == True{} : Bool}
  & {Nat.is_lt(n(s3), n(e3)) == True{} : Bool}))))))))

def ap_r(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Allele.read(Norm.chars(AA.sl(xs(len, t), s3, e3))) == Some{AA.REF(xs(len, t), s3, e3)} : Maybe<&2, List<&2, B.Base>>}:
  match h:
    case (y, z):
      y

def ap_a(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Alleles.read(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == Some{AA.ALTS(xs(len, t), s4, e4)} : Maybe<&2, List<&2, List<&2, B.Base>>>}:
  match h:
    case (x0, r0):
      match r0:
        case (y, z):
          y

def ap_l(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Text.is_letters(Norm.chars(AA.sl(xs(len, t), s3, e3))) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (y, z):
              y

def ap_e(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Text.any_empty(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (y, z):
                  y

def ap_n(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Text.any_not_letters(String.split(Norm.chars(AA.sl(xs(len, t), s4, e4)), ',')) == False{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (y, z):
                      y

def ap_s3(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Allele.show(AA.REF(xs(len, t), s3, e3)) == Norm.chars(AA.sl(xs(len, t), s3, e3)) : String}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (y, z):
                          y

def ap_s4(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {String.join(B.Alleles.show(AA.ALTS(xs(len, t), s4, e4)), ",") == Norm.chars(AA.sl(xs(len, t), s4, e4)) : String}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (y, z):
                              y

def ap_d(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {B.Alleles.distinct(AA.REF(xs(len, t), s3, e3) <> AA.ALTS(xs(len, t), s4, e4)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (y, z):
                                  y

def ap_up(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {AA.up(AA.sl(xs(len, t), s3, e3)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (x7, r7):
                                  match r7:
                                    case (y, z):
                                      y

def ap_lt(+len: U32, +t: AT.Tree<U32>, +s3: U32, +e3: U32, +s4: U32, +e4: U32, h: APT(len, t, s3, e3, s4, e4)) ->
  {Nat.is_lt(n(s3), n(e3)) == True{} : Bool}:
  match h:
    case (x0, r0):
      match r0:
        case (x1, r1):
          match r1:
            case (x2, r2):
              match r2:
                case (x3, r3):
                  match r3:
                    case (x4, r4):
                      match r4:
                        case (x5, r5):
                          match r5:
                            case (x6, r6):
                              match r6:
                                case (x7, r7):
                                  match r7:
                                    case (y, z):
                                      z
