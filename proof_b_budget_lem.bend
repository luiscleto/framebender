import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN

# Lemmas about the budget's potential (proof_b_budget_need.bend).

def st.k(+sp: P.SrcP, +t: List<&2, P.SrcP>, +ih: {BN.srcT(P.mkSrcs(t)) == P.srcstext(t) : String}) ->
  {BN.srcT(P.mkSrcs(Con{sp, t})) == P.srcstext(Con{sp, t}) : String}:
  match sp:
    case P.SBP{+len, +tr, d, +at}:
      Equal.cong(String, String, z => String.append(P.srctext(P.SBP{len, tr, d, at}), z), BN.srcT(P.mkSrcs(t)), P.srcstext(t), ih)
    case P.SLP{+p}:
      Equal.cong(String, String, z => String.append(p ++ "\n", z), BN.srcT(P.mkSrcs(t)), P.srcstext(t), ih)

# The state's text is the picture's.
def srcT_pic(sps: List<&2, P.SrcP>) -> {BN.srcT(P.mkSrcs(sps)) == P.srcstext(sps) : String}:
  match sps:
    case Nil{}:
      {==}
    case Con{+sp, +t}:
      st.k(sp, t, srcT_pic(t))

def pdT_pic(+pd: P.PdP) -> {BN.pdT(P.mkPd(pd)) == P.pdtext(pd) : String}:
  match pd:
    case P.PBP{+len, +t, d}:
      {==}
    case P.PSP{+s}:
      {==}

def pdp(p: S.StP) -> P.PdP:
  match p:
    case S.StP{o, md, src, pd, eof, back, wp, asked, fneed}:
      pd

# The state's text still to come is the picture's (S.intext).
def text_pic(+p: S.StP, +cs: List<&2, String>) ->
  {String.append(BN.srcT(P.mkSrcs(S.StP.src(p))), String.append(BN.pdT(P.mkPd(pdp(p))), S.concat_if(S.StP.eof(p), cs))) == S.intext(p, cs) : String}:
  match p:
    case S.StP{o, md, +src, +pd, +eof, back, wp, asked, fneed}:
      Equal.trans(String, String.append(BN.srcT(P.mkSrcs(src)), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))),
        String.append(P.srcstext(src), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))),
        String.append(P.srcstext(src), String.append(P.pdtext(pd), S.concat_if(eof, cs))),
        Equal.cong(String, String, z => String.append(z, String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))), BN.srcT(P.mkSrcs(src)), P.srcstext(src), srcT_pic(src)),
        Equal.cong(String, String, z => String.append(P.srcstext(src), String.append(z, S.concat_if(eof, cs))), BN.pdT(P.mkPd(pd)), P.pdtext(pd), pdT_pic(pd)))
