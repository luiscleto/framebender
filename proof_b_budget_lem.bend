import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN

# Lemmas about the budget's potential (proof_b_budget_need.bend).

def st.k(+sp: P.SrcP, +t: List<&2, P.SrcP>, +ih: {BN.srcT(P.mkSrcs(t)) == P.srcstext(t) : String}) ->
  {BN.srcT(P.mkSrcs(Con{sp, t})) == P.srcstext(Con{sp, t}) : String}:
  ?TODO


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
    case S.StP{o, md, src, pd, eof, back, wp, asked, fneed, +dfs}:
      pd

# The state's text still to come is the picture's (S.intext).
def text_pic(+p: S.StP, +cs: List<&2, String>) ->
  {String.append(BN.srcT(P.mkSrcs(S.StP.src(p))), String.append(BN.pdT(P.mkPd(pdp(p))), S.concat_if(S.StP.eof(p), cs))) == S.intext(p, cs) : String}:
  ?TODO

