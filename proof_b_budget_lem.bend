import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./norm_seq.bend as Norm
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_budget_need.bend as BN
import ./proof_b_adv_wf.bend as W

# Lemmas about the budget's potential (proof_b_budget_need.bend).

# With no record source, the state's text is the picture's.
def srcT_pic(sps: List<&2, P.SrcP>, +hn: {S.no_recs(sps) == True{} : Bool}) -> {BN.srcT(P.mkSrcs(sps)) == P.srcstext(sps) : String}:
  match sps:
    case Nil{}:
      {==}
    case Con{P.SBP{+len, +tr, +d, +at}, +t}:
      Equal.cong(String, String, z => String.append(P.srctext(P.SBP{len, tr, d, at}), z), BN.srcT(P.mkSrcs(t)), P.srcstext(t),
        srcT_pic(t, W.and_r(Bool.not(S.is_rec(P.SBP{len, tr, d, at})), S.no_recs(t), hn)))
    case Con{P.SLP{+p}, +t}:
      Equal.cong(String, String, z => String.append(p ++ "\n", z), BN.srcT(P.mkSrcs(t)), P.srcstext(t),
        srcT_pic(t, W.and_r(Bool.not(S.is_rec(P.SLP{p})), S.no_recs(t), hn)))
    case Con{P.SPP{+len, +tr, +d, +at}, +t}:
      Empty.absurd({BN.srcT(P.mkSrcs(Con{P.SPP{len, tr, d, at}, t})) == P.srcstext(Con{P.SPP{len, tr, d, at}, t}) : String},
        W.ft(W.and_l(Bool.not(S.is_rec(P.SPP{len, tr, d, at})), S.no_recs(t), hn)))
    case Con{P.SRP{+l}, +t}:
      Empty.absurd({BN.srcT(P.mkSrcs(Con{P.SRP{l}, t})) == P.srcstext(Con{P.SRP{l}, t}) : String},
        W.ft(W.and_l(Bool.not(S.is_rec(P.SRP{l})), S.no_recs(t), hn)))

# Records first (WF): the state's text skips them, as the picture's plain
# sources do.
def rf_pic(sps: List<&2, P.SrcP>, +hf: {S.recs_first(sps) == True{} : Bool}) -> {BN.srcT(P.mkSrcs(sps)) == P.srcstext(S.plain(sps)) : String}:
  match sps:
    case Nil{}:
      {==}
    case Con{P.SPP{+len, +tr, +d, +at}, +t}:
      rf_pic(t, W.and_r(S.rtok(P.srctext(P.SPP{len, tr, d, at})), S.recs_first(t), hf))
    case Con{P.SRP{+l}, +t}:
      rf_pic(t, W.and_r(S.one_alt(l), S.recs_first(t), hf))
    case Con{P.SBP{+len, +tr, +d, +at}, +t}:
      srcT_pic(Con{P.SBP{len, tr, d, at}, t}, W.and_tt(Bool.not(S.is_rec(P.SBP{len, tr, d, at})), S.no_recs(t), {==}, hf))
    case Con{P.SLP{+p}, +t}:
      srcT_pic(Con{P.SLP{p}, t}, W.and_tt(Bool.not(S.is_rec(P.SLP{p})), S.no_recs(t), {==}, hf))

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

# The state's text still to come is the picture's (S.intext), records
# first.
def text_pic(+p: S.StP, +cs: List<&2, String>, +hf: {S.recs_first(S.StP.src(p)) == True{} : Bool}) ->
  {String.append(BN.srcT(P.mkSrcs(S.StP.src(p))), String.append(BN.pdT(P.mkPd(pdp(p))), S.concat_if(S.StP.eof(p), cs))) == S.intext(p, cs) : String}:
  match p:
    case S.StP{o, md, +src, +pd, +eof, back, wp, asked, fneed, +dfs}:
      Equal.trans(String, String.append(BN.srcT(P.mkSrcs(src)), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))),
        String.append(P.srcstext(S.plain(src)), String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))),
        String.append(P.srcstext(S.plain(src)), String.append(P.pdtext(pd), S.concat_if(eof, cs))),
        Equal.cong(String, String, z => String.append(z, String.append(BN.pdT(P.mkPd(pd)), S.concat_if(eof, cs))), BN.srcT(P.mkSrcs(src)), P.srcstext(S.plain(src)), rf_pic(src, hf)),
        Equal.cong(String, String, z => String.append(P.srcstext(S.plain(src)), String.append(z, S.concat_if(eof, cs))), BN.pdT(P.mkPd(pd)), P.pdtext(pd), pdT_pic(pd)))
