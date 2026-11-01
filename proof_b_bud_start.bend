import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./MACHINE.bend as M
import ./bytes_enc.bend as E
import ./norm_seq.bend as Norm
import ./norm_line.bend as J
import ./norm_run.bend as NR
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DD
import ./proof_b_budget_need.bend as BN
import ./proof_b_budget_run.bend as BR
import ./proof_b_budget_rec.bend as Q
import ./proof_b_budget_dig.bend as G
import ./proof_fast.bend as PF
import ./proof_machine_fasta.bend as MF
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import lawful-bytes@0.1.1.0/defs.bend as D
import lawful-bytes@0.1.1.0/bytes.bend as BY
import lawful-words@0.1.0.0/proof_nat.bend as N
import lawful-arrays@0.1.0.0/proof_base.bend as AB
import ./proof_f_args.bend as A

# The budget at the start (proof_b_budget_api.bend's bud_start): the start
# state's potential fits M.bound. Spec-level: the start state's picture has
# the whole file to come (intext = vcf) and back = 0, so
#   WA <= (FM + 2)(|vcf| + 1)   each line's allowance against its piece,
#   FM <= |fasta|               (proof_machine_fasta's bounded),
#   HO <= (|vcf| + 1) + args_len(argv)   (pb-cut's out_len, lim >= 248).

# The longest contig
# ==================

law max_le:
  for +a: Nat
  for +b: Nat
  for +m: Nat
  for +ha: {Nat.is_le(a, m) == True{} : Bool}
  for +hb: {Nat.is_le(b, m) == True{} : Bool}
  {Nat.is_le(Nat.max(a, b), m) == True{} : Bool}

def max_le(a, b, m, ha, hb):
  match a b m:
    case 0n _ _:
      hb
    case 1n+a1 0n _:
      ha
    case 1n+a1 1n+b1 0n:
      Empty.absurd({Nat.is_le(1n+Nat.max(a1, b1), 0n) == True{} : Bool}, PB.false_ne_true(ha))
    case 1n+a1 1n+b1 1n+m1:
      max_le(a1, b1, m1, ha, hb)

law fm_le:
  for +fa: List<&2, B.Contig>
  for +m: Nat
  for +h: {MF.bounded(fa, m) == True{} : Bool}
  {Nat.is_le(BN.FM(fa), m) == True{} : Bool}

def fm_le(fa, m, h):
  match fa:
    case Nil{}:
      N.le_zero_l(m)
    case Con{B.Contig{+nm, +r}, +t}:
      max_le(String.length(r), BN.FM(t), m, PB.and_true_l(Nat.is_le(String.length(r), m), MF.bounded(t, m), h),
        fm_le(t, m, PB.and_true_r(Nat.is_le(String.length(r), m), MF.bounded(t, m), h)))

law fa_fm:
  for +fasta: String
  {Nat.is_le(BN.FM(B.Fasta.parse(fasta)), String.length(fasta)) == True{} : Bool}

def fa_fm(fasta):
  +m = String.length(fasta)
  +ls = String.split(fasta, '\n')
  fm_le(B.Fasta.parse(fasta), m, MF.keep_bounded(B.Fasta.go(ls), Nil{}, m, MF.go_bounded(ls, m, MF.split_total(fasta))))

# The arguments
# =============

law clean_len:
  for +s: String
  {String.length(R.clean(s)) == String.length(s) : Nat}

def clean_len(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %clean_len(t) : {1n+String.length(R.clean(t)) == 1n+_ : Nat}
      {==}

law at_len:
  for +xs: List<&2, String>
  {String.length(R.args_text(xs)) == M.args_len(xs) : Nat}

def at_len(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +e1 = PN.str_len_append(R.clean(x), R.args_text(t))
      %Equal.sym(Nat, String.length(String.append(R.clean(x), R.args_text(t))), Nat.add(String.length(R.clean(x)), String.length(R.args_text(t))), e1) :
        {1n+_ == Nat.add(Nat.add(String.length(x), 1n), M.args_len(t)) : Nat}
      %Equal.sym(Nat, String.length(R.clean(x)), String.length(x), clean_len(x)) :
        {1n+Nat.add(_, String.length(R.args_text(t))) == Nat.add(Nat.add(String.length(x), 1n), M.args_len(t)) : Nat}
      %Equal.sym(Nat, String.length(R.args_text(t)), M.args_len(t), at_len(t)) :
        {1n+Nat.add(String.length(x), _) == Nat.add(Nat.add(String.length(x), 1n), M.args_len(t)) : Nat}
      %Equal.sym(Nat, Nat.add(String.length(x), 1n), 1n+String.length(x), N.add_one(String.length(x))) :
        {1n+Nat.add(String.length(x), M.args_len(t)) == Nat.add(_, M.args_len(t)) : Nat}
      {==}

def oargs(o: B.Opts) -> List<&2, String>:
  match o:
    case B.Opts{s, w, om_m, om_z, a}:
      a

def cfg_al(m: Maybe<&2, B.Cfg>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{B.Cfg{o, r, v}}:
      M.args_len(oargs(o))

law al_done:
  for +st: B.ArgSt
  {Nat.is_le(cfg_al(B.Args.done(st)), A.kl(st)) == True{} : Bool}

def al_done(st):
  match st:
    case B.ArgSt{pe, sc, w, t, r, v, ok, k}:
      match pe:
        case B.PNone{}:
          match sc:
            case B.Sci{c, m, z}:
              match r:
                case None{}:
                  N.le_zero_l(M.args_len(k))
                case Some{r1}:
                  match v:
                    case None{}:
                      N.le_zero_l(M.args_len(k))
                    case Some{v1}:
                      match ok:
                        case True{}:
                          N.le_refl(M.args_len(k))
                        case False{}:
                          N.le_zero_l(M.args_len(k))
        case B.PRef{}:
          N.le_zero_l(M.args_len(k))
        case B.PCheck{}:
          N.le_zero_l(M.args_len(k))
        case B.PWin{}:
          N.le_zero_l(M.args_len(k))
        case B.PThr{}:
          N.le_zero_l(M.args_len(k))
        case B.POut{}:
          N.le_zero_l(M.args_len(k))
        case B.PType{}:
          N.le_zero_l(M.args_len(k))
        case B.PMulti{}:
          N.le_zero_l(M.args_len(k))
        case B.POver{}:
          N.le_zero_l(M.args_len(k))


law al_if:
  for +c: Bool
  for +cmd: String
  for +rest: List<&2, String>
  {Nat.is_le(cfg_al(B.Args.done.if(c, rest)), M.args_len(cmd <> rest)) == True{} : Bool}

def al_if(c, cmd, rest):
  match c:
    case True{}:
      +st = B.Args.go(rest, B.Args.init())
      N.le_trans(cfg_al(B.Args.done(st)), A.kl(st), M.args_len(cmd <> rest),
        al_done(st),
        N.le_trans(A.kl(st), M.args_len(rest), M.args_len(cmd <> rest),
          A.kl_go(rest, B.Args.init()),
          N.le_add_l(M.args_len(rest), Nat.add(String.length(cmd), 1n))))
    case False{}:
      N.le_zero_l(M.args_len(cmd <> rest))

law al_parse:
  for +argv: List<&2, String>
  {Nat.is_le(cfg_al(B.Args.parse(argv)), M.args_len(argv)) == True{} : Bool}

def al_parse(argv):
  match argv:
    case Nil{}:
      {==}
    case +cmd <> +rest:
      al_if(String.eq(cmd, "norm"), cmd, rest)

# The arguments echoed in the header are no longer than the command line.
law args_le:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  {Nat.is_le(String.length(R.args_text(oargs(o))), M.args_len(argv)) == True{} : Bool}

def args_le(argv, o, ref, vcfpath, ha):
  %Equal.sym(Nat, String.length(R.args_text(oargs(o))), M.args_len(oargs(o)), at_len(oargs(o))) : {Nat.is_le(_, M.args_len(argv)) == True{} : Bool}
  %ha : {Nat.is_le(cfg_al(_), M.args_len(argv)) == True{} : Bool}
  al_parse(argv)

# Hand-outs
# =========

law add2:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +hab: {Nat.is_le(a, b) == True{} : Bool}
  for +hcd: {Nat.is_le(c, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}

def add2(a, b, c, d, hab, hcd):
  N.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), N.le_add_mono_r(c, a, b, hab), N.le_add_mono_l(b, c, d, hcd))

law le_124:
  for +x: Nat
  {Nat.is_le(x, Nat.mul(124n, x)) == True{} : Bool}

def le_124(x):
  %N.add_zero(x) : {Nat.is_le(_, Nat.mul(124n, x)) == True{} : Bool}
  N.le_mul_r(1n, 124n, x, {==})

law ob_v:
  for +v: Nat
  for +hv: {Nat.is_le(1n, v) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(63n, v), 61n), Nat.mul(124n, v)) == True{} : Bool}

def ob_v(v, hv):
  %Equal.sym(Nat, Nat.mul(Nat.add(63n, 61n), v), Nat.add(Nat.mul(63n, v), Nat.mul(61n, v)), N.mul_add_r(63n, 61n, v)) :
    {Nat.is_le(Nat.add(Nat.mul(63n, v), 61n), _) == True{} : Bool}
  N.le_add_mono_l(Nat.mul(63n, v), 61n, Nat.mul(61n, v), N.le_mul_l(61n, 1n, v, hv))

# One OB of out_len within 124 (v + A2), for v >= 1 and A <= A2.
law ob_le:
  for +v: Nat
  for +A: Nat
  for +A2: Nat
  for +hv: {Nat.is_le(1n, v) == True{} : Bool}
  for +hA: {Nat.is_le(A, A2) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(63n, v), Nat.add(61n, A)), Nat.mul(124n, Nat.add(v, A2))) == True{} : Bool}

def ob_le(v, A, A2, hv, hA):
  %Equal.sym(Nat, Nat.mul(124n, Nat.add(v, A2)), Nat.add(Nat.mul(124n, v), Nat.mul(124n, A2)), N.mul_add(124n, v, A2)) :
    {Nat.is_le(Nat.add(Nat.mul(63n, v), Nat.add(61n, A)), _) == True{} : Bool}
  %N.add_assoc(Nat.mul(63n, v), 61n, A) : {Nat.is_le(_, Nat.add(Nat.mul(124n, v), Nat.mul(124n, A2))) == True{} : Bool}
  add2(Nat.add(Nat.mul(63n, v), 61n), Nat.mul(124n, v), A, Nat.mul(124n, A2), ob_v(v, hv),
    N.le_trans(A, A2, Nat.mul(124n, A2), hA, le_124(A2)))

law ob1:
  for +vcf: String
  for +o: B.Opts
  for +AL: Nat
  for +hA: {Nat.is_le(String.length(R.args_text(oargs(o))), AL) == True{} : Bool}
  {Nat.is_le(BR.OB(vcf, o), Nat.mul(124n, Nat.add(1n+String.length(vcf), AL))) == True{} : Bool}

def ob1(vcf, o, AL, hA):
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      ob_le(1n+String.length(vcf), String.length(R.args_text(args)), AL, N.le_zero_l(String.length(vcf)), hA)

law ob2:
  for +vcf: String
  for +o: B.Opts
  for +AL: Nat
  for +hA: {Nat.is_le(String.length(R.args_text(oargs(o))), AL) == True{} : Bool}
  {Nat.is_le(Nat.add(BR.OB(vcf, o), BR.OB(vcf, o)), Nat.mul(248n, Nat.add(1n+String.length(vcf), AL))) == True{} : Bool}

def ob2(vcf, o, AL, hA):
  +X = Nat.add(1n+String.length(vcf), AL)
  %Equal.sym(Nat, Nat.mul(Nat.add(124n, 124n), X), Nat.add(Nat.mul(124n, X), Nat.mul(124n, X)), N.mul_add_r(124n, 124n, X)) :
    {Nat.is_le(Nat.add(BR.OB(vcf, o), BR.OB(vcf, o)), _) == True{} : Bool}
  add2(BR.OB(vcf, o), Nat.mul(124n, X), BR.OB(vcf, o), Nat.mul(124n, X), ob1(vcf, o, AL, hA), ob1(vcf, o, AL, hA))

# Division by a bound lm >= 248 (HO divides by 256n), kept abstract here.
law lt0:
  for +lm: Nat
  for +hl: {Nat.is_le(248n, lm) == True{} : Bool}
  {Nat.is_lt(0n, lm) == True{} : Bool}

def lt0(lm, hl):
  %N.le_succ_lt(0n, lm) : {_ == True{} : Bool}
  N.le_trans(1n, 248n, lm, {==}, hl)

law lt_mul_succ:
  for +a: Nat
  for +X: Nat
  for +lm: Nat
  for +hl: {Nat.is_le(248n, lm) == True{} : Bool}
  for +h: {Nat.is_le(a, Nat.mul(248n, X)) == True{} : Bool}
  {Nat.is_lt(a, Nat.mul(lm, 1n+X)) == True{} : Bool}

def lt_mul_succ(a, X, lm, hl, h):
  %Equal.sym(Nat, Nat.mul(lm, 1n+X), Nat.add(lm, Nat.mul(lm, X)), N.mul_succ_r(lm, X)) : {Nat.is_lt(a, _) == True{} : Bool}
  %N.le_succ_lt(a, Nat.add(lm, Nat.mul(lm, X))) : {_ == True{} : Bool}
  add2(1n, lm, a, Nat.mul(lm, X), N.le_trans(1n, 248n, lm, {==}, hl),
    N.le_trans(a, Nat.mul(248n, X), Nat.mul(lm, X), h, N.le_mul_r(248n, lm, X, hl)))

law div_le:
  for +a: Nat
  for +X: Nat
  for +lm: Nat
  for +hl: {Nat.is_le(248n, lm) == True{} : Bool}
  for +h: {Nat.is_le(a, Nat.mul(248n, X)) == True{} : Bool}
  {Nat.is_le(Nat.div(a, lm), X) == True{} : Bool}

def div_le(a, X, lm, hl, h):
  %N.lt_succ_iff(Nat.div(a, lm), X) : {_ == True{} : Bool}
  N.div_lt(a, lm, 1n+X, lt0(lm, hl), lt_mul_succ(a, X, lm, hl, h))

law sub0_le:
  for +n: Nat
  {Nat.is_le(Nat.sub(n, String.length("")), n) == True{} : Bool}

def sub0_le(n):
  %Equal.sym(Nat, Nat.sub(n, 0n), n, N.sub_zero(n)) : {Nat.is_le(_, n) == True{} : Bool}
  N.le_refl(n)

# The empty line end at the start holds no text.
law empty_text:
  {NR.chars(D.view(BY.empty(0n))) == "" : String}

def empty_text():
  {==}

# The Wants still to come
# =======================

law pick_le1:
  for +b: Bool
  for +n: Nat
  {Nat.is_le(BN.pick(b, n), n) == True{} : Bool}

def pick_le1(b, n):
  match b:
    case True{}:
      N.le_refl(n)
    case False{}:
      N.le_zero_l(n)

law pick_mono:
  for +g: Bool
  for +a: Nat
  for +b: Nat
  for +h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(BN.pick(g, a), BN.pick(g, b)) == True{} : Bool}

def pick_mono(g, a, b, h):
  match g:
    case True{}:
      h
    case False{}:
      {==}

law pick_le:
  for +g: Bool
  for +n: Nat
  for +m: Nat
  for h: @e: {g == True{} : Bool} -> {Nat.is_le(n, m) == True{} : Bool}
  {Nat.is_le(BN.pick(g, n), m) == True{} : Bool}

def pick_le(g, n, m, h):
  match g:
    case True{}:
      h({==})
    case False{}:
      N.le_zero_l(m)

# At the start (fast path open, back 0, no window, nothing asked) the line
# being handled has at most its whole allowance left.
law rem_le:
  for +fa: List<&2, B.Contig>
  for +l: B.Line
  {Nat.is_le(BN.rem(fa, True{}, 0n, Norm.WNone{}, None{}, l), BN.LA(fa, l)) == True{} : Bool}

def rem_le(fa, l):
  +RR = Nat.add(BN.RW(l), BN.RW(l))
  +Z = BN.ZW(fa)
  +q = BN.pick(Nat.is_lt(0n, BN.lpos(l)), Z)
  pick_mono(BN.lgate(l), Nat.add(RR, Nat.add(Z, q)), Nat.add(RR, Nat.add(Z, Z)),
    N.le_add_mono_l(RR, Nat.add(Z, q), Nat.add(Z, Z), N.le_add_mono_l(Z, q, Z, pick_le1(Nat.is_lt(0n, BN.lpos(l)), Z))))

law wa_le:
  for +fa: List<&2, B.Contig>
  for +ls: List<&2, B.Line>
  {Nat.is_le(BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, ls), BN.LAs(fa, ls)) == True{} : Bool}

def wa_le(fa, ls):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      add2(BN.rem(fa, True{}, 0n, Norm.WNone{}, None{}, l), BN.LA(fa, l), BN.LAs(fa, t), BN.LAs(fa, t), rem_le(fa, l), N.le_refl(BN.LAs(fa, t)))

# Back 0: the invariant holds whatever the lines.
law bi0:
  for +ls: List<&2, B.Line>
  {BN.bi.ls(0n, Norm.WNone{}, None{}, ls) == True{} : Bool}

def bi0(ls):
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      {==}

# A line's allowance against its piece
# ====================================

# A list of at least 8 fields: field 3 and 8 separators fit in SN.
law lay:
  for +a: Nat
  for +n: Nat
  for +m: Nat
  for +h: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.is_le(1n+n, 1n+Nat.add(a, m)) == True{} : Bool}

def lay(a, n, m, h):
  N.le_trans(n, m, Nat.add(a, m), h, N.le_add_l(m, a))

law sn_one:
  for +a: Nat
  for +S: Nat
  for +hr: {Nat.is_le(4n, S) == True{} : Bool}
  {Nat.is_le(Nat.add(4n, a), Nat.add(a, S)) == True{} : Bool}

def sn_one(a, S, hr):
  %N.add_comm(S, a) : {Nat.is_le(Nat.add(4n, a), _) == True{} : Bool}
  N.le_add_mono_r(a, 4n, S, hr)

law sn_f3:
  for +f0: String
  for +f1: String
  for +f2: String
  for +f3: String
  for +rest: List<&2, String>
  for +hr: {Nat.is_le(4n, Q.SN(rest)) == True{} : Bool}
  {Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN(f0 <> f1 <> f2 <> f3 <> rest)) == True{} : Bool}

def sn_f3(f0, f1, f2, f3, rest, hr):
  +a3 = String.length(f3)
  lay(String.length(f0), Nat.add(7n, a3), Q.SN(f1 <> f2 <> f3 <> rest),
    lay(String.length(f1), Nat.add(6n, a3), Q.SN(f2 <> f3 <> rest),
      lay(String.length(f2), Nat.add(5n, a3), Q.SN(f3 <> rest), sn_one(a3, Q.SN(rest), hr))))

law sn_4:
  for +f4: String
  for +f5: String
  for +f6: String
  for +rest: List<&2, String>
  for +hr: {Nat.is_le(1n, Q.SN(rest)) == True{} : Bool}
  {Nat.is_le(4n, Q.SN(f4 <> f5 <> f6 <> rest)) == True{} : Bool}

def sn_4(f4, f5, f6, rest, hr):
  lay(String.length(f4), 3n, Q.SN(f5 <> f6 <> rest),
    lay(String.length(f5), 2n, Q.SN(f6 <> rest),
      lay(String.length(f6), 1n, Q.SN(rest), hr)))

law short_f3:
  for +fs: List<&2, String>
  for +h: {Bool.not(B.Rec.malformed(fs)) == True{} : Bool}
  {Nat.is_le(Nat.add(8n, String.length(B.Rec.field(fs, 3n))), Q.SN(fs)) == True{} : Bool}

def short_f3(fs, h):
  match fs:
    case Nil{}:
      Empty.absurd({Nat.is_le(8n, 0n) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Nil{}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, 0n), Q.SN([f0])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, 0n), Q.SN([f0, f1])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, 0n), Q.SN([f0, f1, f2])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN([f0, f1, f2, f3])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN([f0, f1, f2, f3, f4])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN([f0, f1, f2, f3, f4, f5])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN([f0, f1, f2, f3, f4, f5, f6])) == True{} : Bool}, PB.false_ne_true(h))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +t}}}}}}}}:
      sn_f3(f0, f1, f2, f3, f4 <> f5 <> f6 <> f7 <> t, sn_4(f4, f5, f6, f7 <> t, N.le_zero_l(Nat.add(String.length(f7), Q.SN(t)))))

law split1:
  for +r: String
  {Nat.is_le(1n, Q.SN(String.split(r, '\t'))) == True{} : Bool}

def split1(r):
  %Equal.sym(Nat, Q.SN(String.split(r, '\t')), 1n+Q.SL(r), Q.split_sn(r, '\t')) : {Nat.is_le(1n, _) == True{} : Bool}
  N.le_zero_l(String.length(r))

# The fields the machine keeps (J.pfs): field 3 and 7 tabs fit in the body.
# With 7 tabs found (Got) this holds of any body; otherwise (Short) the
# fields are all the body's, and a line that is not malformed has 8.
law body_f3.g:
  for +g: J.C7
  for +body: String
  for +e: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}
  for +hg: {Bool.not(B.Rec.malformed(J.pfs.g(g, body))) == True{} : Bool}
  {Nat.is_le(Nat.add(8n, String.length(B.Rec.field(J.pfs.g(g, body), 3n))), 1n+String.length(body)) == True{} : Bool}

def body_f3.g(g, body, e, hg):
  match g:
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      %Q.split_sn(body, '\t') : {Nat.is_le(Nat.add(8n, String.length(f3)), _) == True{} : Bool}
      %e : {Nat.is_le(Nat.add(8n, String.length(f3)), Q.SN(_)) == True{} : Bool}
      sn_f3(f0, f1, f2, f3, f4 <> f5 <> f6 <> String.split(r, '\t'), sn_4(f4, f5, f6, String.split(r, '\t'), split1(r)))
    case J.Short{}:
      %Q.split_sn(body, '\t') : {Nat.is_le(Nat.add(8n, String.length(B.Rec.field(B.Rec.fields(body), 3n))), _) == True{} : Bool}
      short_f3(B.Rec.fields(body), hg)

law body_f3:
  for +body: String
  for +hg: {Bool.not(B.Rec.malformed(J.pfs(body))) == True{} : Bool}
  {Nat.is_le(Nat.add(8n, String.length(B.Rec.field(J.pfs(body), 3n))), 1n+String.length(body)) == True{} : Bool}

def body_f3(body, hg):
  body_f3.g(J.c7(body), body, PF.c7_split(body), hg)

law bl:
  for +cr: Bool
  for +p: String
  {Nat.is_le(String.length(B.Line.body(B.Text.line.if(cr, p))), String.length(p)) == True{} : Bool}

def bl(cr, p):
  match cr:
    case True{}:
      BR.take_sl(p, Nat.sub(String.length(p), 1n))
    case False{}:
      N.le_refl(String.length(p))

law body_le:
  for +p: String
  {Nat.is_le(String.length(B.Line.body(B.Text.line(p))), String.length(p)) == True{} : Bool}

def body_le(p):
  bl(String.ends_with(p, "\r"), p)

# The arithmetic: with R = |REF|, Z = 2 + F and 8 + R <= n,
# 2 (1 + max(1, R)) + 2 Z <= n Z.
law m1:
  for +R: Nat
  {Nat.is_le(BN.max1(R), 1n+R) == True{} : Bool}

def m1(R):
  match R:
    case 0n:
      {==}
    case 1n+r:
      N.le_add_l(r, 1n)

law sw2:
  for +R: Nat
  for +Z: Nat
  for +hz: {Nat.is_le(2n, Z) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(2n, R), Nat.add(2n, R)), Nat.add(Nat.add(Z, Z), Nat.add(R, R))) == True{} : Bool}

def sw2(R, Z, hz):
  %Equal.sym(Nat, Nat.add(Nat.add(2n, R), Nat.add(2n, R)), Nat.add(Nat.add(2n, 2n), Nat.add(R, R)), N.add_swap(2n, R, 2n, R)) :
    {Nat.is_le(_, Nat.add(Nat.add(Z, Z), Nat.add(R, R))) == True{} : Bool}
  add2(Nat.add(2n, 2n), Nat.add(Z, Z), Nat.add(R, R), Nat.add(R, R), add2(2n, Z, 2n, Z, hz, hz), N.le_refl(Nat.add(R, R)))

law rw2:
  for +R: Nat
  for +Z: Nat
  for +hz: {Nat.is_le(2n, Z) == True{} : Bool}
  {Nat.is_le(Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(Nat.add(Z, Z), Nat.add(R, R))) == True{} : Bool}

def rw2(R, Z, hz):
  N.le_trans(Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(Nat.add(2n, R), Nat.add(2n, R)), Nat.add(Nat.add(Z, Z), Nat.add(R, R)),
    add2(1n+BN.max1(R), Nat.add(2n, R), 1n+BN.max1(R), Nat.add(2n, R), m1(R), m1(R)), sw2(R, Z, hz))

law rr_le:
  for +R: Nat
  for +F: Nat
  {Nat.is_le(Nat.add(R, R), Nat.mul(R, 2n+F)) == True{} : Bool}

def rr_le(R, F):
  %N.mul_comm(2n+F, R) : {Nat.is_le(Nat.add(R, R), _) == True{} : Bool}
  N.le_add_mono_l(R, R, Nat.add(R, Nat.mul(F, R)), N.le_add_r(R, Nat.mul(F, R)))

law la_mid:
  for +R: Nat
  for +F: Nat
  {Nat.is_le(Nat.add(Nat.add(Nat.add(2n+F, 2n+F), Nat.add(R, R)), Nat.add(2n+F, 2n+F)), Nat.mul(Nat.add(4n, R), 2n+F)) == True{} : Bool}

def la_mid(R, F):
  +Z = Nat.add(2n, F)
  +X = Nat.add(Z, Z)
  +RR = Nat.add(R, R)
  +T = Nat.mul(Nat.add(4n, R), Z)
  %Equal.sym(Nat, Nat.add(Nat.add(X, RR), X), Nat.add(X, Nat.add(RR, X)), N.add_assoc(X, RR, X)) : {Nat.is_le(_, T) == True{} : Bool}
  %N.add_comm(X, RR) : {Nat.is_le(Nat.add(X, _), T) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(Z, Z), Nat.add(X, RR)), Nat.add(Z, Nat.add(Z, Nat.add(X, RR))), N.add_assoc(Z, Z, Nat.add(X, RR))) :
    {Nat.is_le(_, T) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(Z, Z), RR), Nat.add(Z, Nat.add(Z, RR)), N.add_assoc(Z, Z, RR)) :
    {Nat.is_le(Nat.add(Z, Nat.add(Z, _)), T) == True{} : Bool}
  N.le_add_mono_l(Z, Nat.add(Z, Nat.add(Z, Nat.add(Z, RR))), Nat.add(Z, Nat.add(Z, Nat.add(Z, Nat.mul(R, Z)))),
    N.le_add_mono_l(Z, Nat.add(Z, Nat.add(Z, RR)), Nat.add(Z, Nat.add(Z, Nat.mul(R, Z))),
      N.le_add_mono_l(Z, Nat.add(Z, RR), Nat.add(Z, Nat.mul(R, Z)),
        N.le_add_mono_l(Z, RR, Nat.mul(R, Z), rr_le(R, F)))))

law la_ar:
  for +R: Nat
  for +F: Nat
  for +n: Nat
  for +hn: {Nat.is_le(Nat.add(8n, R), n) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(2n+F, 2n+F)), Nat.mul(n, 2n+F)) == True{} : Bool}

def la_ar(R, F, n, hn):
  +Z = Nat.add(2n, F)
  +mid = Nat.add(Nat.add(Nat.add(Z, Z), Nat.add(R, R)), Nat.add(Z, Z))
  N.le_trans(Nat.add(Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(Z, Z)), mid, Nat.mul(n, Z),
    N.le_add_mono_r(Nat.add(Z, Z), Nat.add(1n+BN.max1(R), 1n+BN.max1(R)), Nat.add(Nat.add(Z, Z), Nat.add(R, R)), rw2(R, Z, N.le_zero_l(F))),
    N.le_trans(mid, Nat.mul(Nat.add(4n, R), Z), Nat.mul(n, Z), la_mid(R, F),
      N.le_mul_r(Nat.add(4n, R), n, Z, N.le_trans(Nat.add(4n, R), Nat.add(8n, R), n, N.le_add_l(R, 4n), hn))))

# A line's allowance is at most (|piece| + 1) Z, the piece being its text
# before the LF.
law la_le:
  for +fa: List<&2, B.Contig>
  for +p: String
  {Nat.is_le(BN.LA(fa, B.Text.line(p)), Nat.mul(1n+String.length(p), BN.ZW(fa))) == True{} : Bool}

def la_le(fa, p):
  +l = B.Text.line(p)
  pick_le(BN.lgate(l), Nat.add(Nat.add(BN.RW(l), BN.RW(l)), Nat.add(BN.ZW(fa), BN.ZW(fa))), Nat.mul(1n+String.length(p), BN.ZW(fa)),
    hg => la_ar(BN.lref(l), BN.FM(fa), 1n+String.length(p),
      N.le_trans(Nat.add(8n, BN.lref(l)), 1n+String.length(B.Line.body(l)), 1n+String.length(p), body_f3(B.Line.body(l), hg), body_le(p))))

# Summed over the lines of the file: at most (|vcf| + 1) Z.
law lgo_last:
  for +fa: List<&2, B.Contig>
  for +p: String
  {Nat.is_le(BN.LAs(fa, B.Text.last(p)), Nat.mul(Q.SN([p]), BN.ZW(fa))) == True{} : Bool}

def lgo_last(fa, p):
  match p:
    case SNil{}:
      N.le_zero_l(Nat.mul(Q.SN([""]), BN.ZW(fa)))
    case SCon{+h, +t}:
      +LA = BN.LA(fa, B.Text.line(SCon{h, t}))
      +n = String.length(SCon{h, t})
      %Equal.sym(Nat, Nat.add(LA, 0n), LA, N.add_zero(LA)) : {Nat.is_le(_, Nat.mul(1n+Nat.add(n, 0n), BN.ZW(fa))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(n, 0n), n, N.add_zero(n)) : {Nat.is_le(LA, Nat.mul(1n+_, BN.ZW(fa))) == True{} : Bool}
      la_le(fa, SCon{h, t})

law lgo:
  for +fa: List<&2, B.Contig>
  for +ps: List<&2, String>
  for +p: String
  {Nat.is_le(BN.LAs(fa, B.Text.lines.go(ps, p)), Nat.mul(Q.SN(p <> ps), BN.ZW(fa))) == True{} : Bool}

def lgo(fa, ps, p):
  match ps:
    case Nil{}:
      lgo_last(fa, p)
    case Con{+q, +t}:
      +Z = BN.ZW(fa)
      +a = Nat.add(1n, String.length(p))
      +S = Q.SN(q <> t)
      %Equal.sym(Nat, Nat.mul(Nat.add(a, S), Z), Nat.add(Nat.mul(a, Z), Nat.mul(S, Z)), N.mul_add_r(a, S, Z)) :
        {Nat.is_le(Nat.add(BN.LA(fa, B.Text.line(p)), BN.LAs(fa, B.Text.lines.go(t, q))), _) == True{} : Bool}
      add2(BN.LA(fa, B.Text.line(p)), Nat.mul(a, Z), BN.LAs(fa, B.Text.lines.go(t, q)), Nat.mul(S, Z), la_le(fa, p), lgo(fa, t, q))

law lstart:
  for +fa: List<&2, B.Contig>
  for +ps: List<&2, String>
  {Nat.is_le(BN.LAs(fa, B.Text.lines.start(ps)), Nat.mul(Q.SN(ps), BN.ZW(fa))) == True{} : Bool}

def lstart(fa, ps):
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      lgo(fa, t, p)

law lvcf:
  for +fa: List<&2, B.Contig>
  for +vcf: String
  {Nat.is_le(BN.LAs(fa, B.Text.lines(vcf)), Nat.mul(1n+String.length(vcf), BN.ZW(fa))) == True{} : Bool}

def lvcf(fa, vcf):
  %Q.split_sn(vcf, '\n') : {Nat.is_le(BN.LAs(fa, B.Text.lines(vcf)), Nat.mul(_, BN.ZW(fa))) == True{} : Bool}
  lstart(fa, String.split(vcf, '\n'))

# The start
# =========

# The lines to come at the start are the file's.
law las_cs:
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +vcf: String
  for +h: {String.concat(cs) == vcf : String}
  {Nat.is_le(BN.LAs(fa, BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs)), Nat.mul(1n+String.length(vcf), BN.ZW(fa))) == True{} : Bool}

def las_cs(fa, cs, vcf, h):
  %Equal.sym(String, String.concat(cs), vcf, h) : {Nat.is_le(BN.LAs(fa, B.Text.lines(_)), Nat.mul(1n+String.length(vcf), BN.ZW(fa))) == True{} : Bool}
  lvcf(fa, vcf)

law core:
  for +H: Nat
  for +W: Nat
  for +AL: Nat
  for +v: Nat
  for +Qv: Nat
  for +hH: {Nat.is_le(H, Nat.add(v, AL)) == True{} : Bool}
  for +hW: {Nat.is_le(W, Qv) == True{} : Bool}
  {Nat.is_le(Nat.add(H, W), Nat.add(AL, Nat.add(v, Qv))) == True{} : Bool}

def core(H, W, AL, v, Qv, hH, hW):
  %N.add_assoc(AL, v, Qv) : {Nat.is_le(Nat.add(H, W), _) == True{} : Bool}
  %N.add_comm(v, AL) : {Nat.is_le(Nat.add(H, W), Nat.add(_, Qv)) == True{} : Bool}
  add2(H, Nat.add(v, AL), W, Qv, hH, hW)

# need at the start against M.bound: c + 1 + 2 + H + W within
# c + 3 + AL + v (F + 3), with H <= v + AL and W <= v (2 + FM), FM <= F.
law fin:
  for +c: Nat
  for +H: Nat
  for +W: Nat
  for +AL: Nat
  for +v: Nat
  for +F: Nat
  for +FM: Nat
  for +hH: {Nat.is_le(H, Nat.add(v, AL)) == True{} : Bool}
  for +hW: {Nat.is_le(W, Nat.mul(v, 2n+FM)) == True{} : Bool}
  for +hF: {Nat.is_le(FM, F) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), Nat.add(Nat.add(Nat.add(c, 3n), AL), Nat.mul(v, Nat.add(F, 3n)))) == True{} : Bool}

def fin(c, H, W, AL, v, F, FM, hH, hW, hF):
  +Qv = Nat.mul(v, Nat.add(2n, F))
  +Y = Nat.add(v, Qv)
  %N.add_comm(3n, F) : {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), Nat.add(Nat.add(Nat.add(c, 3n), AL), Nat.mul(v, _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(v, 1n+(2n+F)), Y, N.mul_succ_r(v, 2n+F)) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), Nat.add(Nat.add(Nat.add(c, 3n), AL), _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(c, 3n), AL), Y), Nat.add(Nat.add(c, 3n), Nat.add(AL, Y)), N.add_assoc(Nat.add(c, 3n), AL, Y)) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(c, 3n), Nat.add(AL, Y)), Nat.add(c, Nat.add(3n, Nat.add(AL, Y))), N.add_assoc(c, 3n, Nat.add(AL, Y))) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(H, W))), Nat.add(c, Nat.add(1n, Nat.add(2n, Nat.add(H, W)))), N.add_assoc(c, 1n, Nat.add(2n, Nat.add(H, W)))) :
    {Nat.is_le(_, Nat.add(c, Nat.add(3n, Nat.add(AL, Y)))) == True{} : Bool}
  N.le_add_mono_l(c, Nat.add(1n, Nat.add(2n, Nat.add(H, W))), Nat.add(3n, Nat.add(AL, Y)),
    core(H, W, AL, v, Qv, hH, N.le_trans(W, Nat.mul(v, 2n+FM), Qv, hW, N.le_mul_l(v, 2n+FM, 2n+F, hF))))

law bud_bi:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hst: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {BN.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}

def bud_bi(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hst):
  %hst : {BN.biS(_, cs) == True{} : Bool}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) : {BN.biS(DD.start_st(dfs, Norm.start.of(_)), cs) == True{} : Bool}
  bi0(BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs))

# The start under -m (start_fit)
# ==============================
#
# With v = |vcf| + 1, Z = 2 + FM, AL = args_len(argv): a line of piece p
# (n = |p| + 1) has LA <= n Z; a line -m may split (k ALTs, REF of R bytes)
# has R + 2k + 9 <= n, so (1 + k) LA + k n <= n Z + n n. Its records' output
# share (out_len's XO) is within 128 k n, so the hand-outs HO + K fit in
# v + AL + XQ (XQ: k (1 + |body|) per such line). Summed: the Wants and the
# records' extra allowances fit in v Z + v^2 (n^2 summed is at most v^2), the
# split room with -m; without -m the extra terms vanish.

law or_f_l:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_f_l(a, b, e):
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.true_ne_false(e))
    case False{}:
      {==}

law or_f_r:
  for +a: Bool
  for +b: Bool
  for +e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_f_r(a, b, e):
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, PB.true_ne_false(e))
    case False{}:
      e

law not_t:
  for +b: Bool
  for +h: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_t(b, h):
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PB.false_ne_true(h))
    case False{}:
      {==}

def ne_f(+s: String, +h: {String.is_empty(s) == False{} : Bool}) -> {Nat.is_le(1n, String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PB.true_ne_false(h))
    case SCon{+c, +t}:
      N.le_zero_l(String.length(t))

def pos_f(+s: String, +h: {Maybe.is_none(&2, Nat, B.Pos.read(s)) == False{} : Bool}) -> {Nat.is_le(1n, String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PB.true_ne_false(h))
    case SCon{+c, +t}:
      N.le_zero_l(String.length(t))

# No empty piece: each counts 2 or more in SN.
law ae_sn:
  for +xs: List<&2, String>
  for +h: {B.Text.any_empty(xs) == False{} : Bool}
  {Nat.is_le(Nat.add(List.length(&2, String, xs), List.length(&2, String, xs)), Q.SN(xs)) == True{} : Bool}

def ae_sn(xs, h):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +L = List.length(&2, String, t)
      +hx = ne_f(x, or_f_l(String.is_empty(x), B.Text.any_empty(t), h))
      +ht = ae_sn(t, or_f_r(String.is_empty(x), B.Text.any_empty(t), h))
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(String.length(x), Q.SN(t))) == True{} : Bool}, 1n+Nat.add(L, L), Nat.add(L, 1n+L), Equal.sym(Nat, Nat.add(L, 1n+L), 1n+Nat.add(L, L), N.add_succ(L, L)),
        add2(1n, String.length(x), Nat.add(L, L), Q.SN(t), hx, ht))

def F8(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String, +t: List<&2, String>) -> List<&2, String>:
  f0 <> f1 <> f2 <> f3 <> f4 <> f5 <> f6 <> f7 <> t

# A record that is not MALFORMED: R + 2k + 9 <= SN of its fields (CHROM and
# POS not empty, k non-empty ALTs).
def cl8(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String, +f7: String, +t: List<&2, String>,
  +hm: {B.Rec.malformed(F8(f0, f1, f2, f3, f4, f5, f6, f7, t)) == False{} : Bool}) ->
  {Nat.is_le(6n+Nat.add(String.length(f3), Nat.add(Nat.add(List.length(&2, String, String.split(f4, ',')), List.length(&2, String, String.split(f4, ','))), 3n)), Q.SN(F8(f0, f1, f2, f3, f4, f5, f6, f7, t))) == True{} : Bool}:
  +fs = F8(f0, f1, f2, f3, f4, f5, f6, f7, t)
  +A = Nat.is_lt(List.length(&2, String, fs), 8n)
  +B0 = String.is_empty(f0)
  +C = Maybe.is_none(&2, Nat, B.Pos.read(f1))
  +D = Bool.not(B.Text.is_letters(f3))
  +al = String.split(f4, ',')
  +E = B.Text.any_empty(al)
  +h4 = or_f_l(Bool.or(Bool.or(Bool.or(A, B0), C), D), E, hm)
  +h3 = or_f_l(Bool.or(Bool.or(A, B0), C), D, h4)
  +h2 = or_f_l(Bool.or(A, B0), C, h3)
  +hf0 = ne_f(f0, or_f_r(A, B0, h2))
  +hf1 = pos_f(f1, or_f_r(Bool.or(A, B0), C, h3))
  +k = List.length(&2, String, al)
  +hae = AB.subst(Nat, z => {Nat.is_le(Nat.add(k, k), z) == True{} : Bool}, Q.SN(al), 1n+String.length(f4), Q.split_sn(f4, ','), ae_sn(al, or_f_r(Bool.or(Bool.or(Bool.or(A, B0), C), D), E, hm)))
  +S7 = Q.SN(f7 <> t)
  +L6 = Nat.add(String.length(f6), S7)
  +h6 = N.le_trans(1n, S7, L6, N.le_zero_l(Nat.add(String.length(f7), Q.SN(t))), N.le_add_l(S7, String.length(f6)))
  +W5 = {1n+Nat.add(String.length(f5), 1n+L6) : Nat}
  +h5 = N.le_trans(2n, 1n+L6, Nat.add(String.length(f5), 1n+L6), h6, N.le_add_l(1n+L6, String.length(f5)))
  +KK3 = Nat.add(Nat.add(k, k), 3n)
  +Y = Nat.add(1n+String.length(f4), W5)
  +hY = add2(Nat.add(k, k), 1n+String.length(f4), 3n, W5, hae, h5)
  +X = Nat.add(String.length(f3), KK3)
  +V3 = {1n+Nat.add(String.length(f3), Y) : Nat}
  +h3b = N.le_add_mono_l(String.length(f3), KK3, Y, hY)
  +V2 = {1n+Nat.add(String.length(f2), V3) : Nat}
  +h2b = add2(0n, String.length(f2), 1n+X, V3, N.le_zero_l(String.length(f2)), h3b)
  +V1 = {1n+Nat.add(String.length(f1), V2) : Nat}
  +h1b = add2(1n, String.length(f1), 2n+X, V2, hf1, h2b)
  add2(1n, String.length(f0), 4n+X, V1, hf0, h1b)

def CL(+fs: List<&2, String>) -> Bool:
  Nat.is_le(6n+Nat.add(String.length(B.Rec.field(fs, 3n)), Nat.add(Nat.add(List.length(&2, String, B.Rec.alts(fs)), List.length(&2, String, B.Rec.alts(fs))), 3n)), Q.SN(fs))

law cand_len:
  for +fs: List<&2, String>
  for +hm: {Bool.not(B.Rec.malformed(fs)) == True{} : Bool}
  {CL(fs) == True{} : Bool}

def cand_len(fs, hm):
  match fs:
    case Nil{}:
      Empty.absurd({CL(Nil{}) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Nil{}}:
      Empty.absurd({CL([f0]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Nil{}}}:
      Empty.absurd({CL([f0, f1]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Nil{}}}}:
      Empty.absurd({CL([f0, f1, f2]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Nil{}}}}}:
      Empty.absurd({CL([f0, f1, f2, f3]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Nil{}}}}}}:
      Empty.absurd({CL([f0, f1, f2, f3, f4]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Nil{}}}}}}}:
      Empty.absurd({CL([f0, f1, f2, f3, f4, f5]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Nil{}}}}}}}}:
      Empty.absurd({CL([f0, f1, f2, f3, f4, f5, f6]) == True{} : Bool}, PB.false_ne_true(hm))
    case Con{+f0, Con{+f1, Con{+f2, Con{+f3, Con{+f4, Con{+f5, Con{+f6, Con{+f7, +t}}}}}}}}:
      cl8(f0, f1, f2, f3, f4, f5, f6, f7, t, not_t(B.Rec.malformed(F8(f0, f1, f2, f3, f4, f5, f6, f7, t)), hm))

# The fields the machine keeps (J.pfs) have the line's REF.
def f3.g(+g: J.C7, +body: String, +e: {PF.gsplit(g, B.Rec.fields(body)) == B.Rec.fields(body) : List<&2, String>}) ->
  {B.Rec.field(J.pfs.g(g, body), 3n) == B.Rec.field(B.Rec.fields(body), 3n) : String}:
  match g:
    case J.Got{+f0, +f1, +f2, +f3, +f4, +f5, +f6, +r}:
      %e : {f3 == B.Rec.field(_, 3n) : String}
      {==}
    case J.Short{}:
      {==}

def f3_eq(+body: String) -> {B.Rec.field(J.pfs(body), 3n) == B.Rec.field(B.Rec.fields(body), 3n) : String}:
  f3.g(J.c7(body), body, PF.c7_split(body))

# A line's allowance: at most 2 (R + 2) + 2 Z; at most n Z for n >= 1 + |body|.
def la_bound(+fa: List<&2, B.Contig>, +l: B.Line) ->
  {Nat.is_le(BN.LA(fa, l), Nat.add(Nat.add(2n+BN.lref(l), 2n+BN.lref(l)), Nat.add(BN.ZW(fa), BN.ZW(fa)))) == True{} : Bool}:
  +RW = BN.RW(l)
  +Z = BN.ZW(fa)
  +R = BN.lref(l)
  N.le_trans(BN.LA(fa, l), Nat.add(Nat.add(RW, RW), Nat.add(Z, Z)), Nat.add(Nat.add(2n+R, 2n+R), Nat.add(Z, Z)), pick_le1(BN.lgate(l), Nat.add(Nat.add(RW, RW), Nat.add(Z, Z))),
    N.le_add_mono_r(Nat.add(Z, Z), Nat.add(RW, RW), Nat.add(2n+R, 2n+R), add2(RW, 2n+R, RW, 2n+R, m1(R), m1(R))))

def la_n(+fa: List<&2, B.Contig>, +l: B.Line, +n: Nat, +hn: {Nat.is_le(1n+String.length(B.Line.body(l)), n) == True{} : Bool}) ->
  {Nat.is_le(BN.LA(fa, l), Nat.mul(n, BN.ZW(fa))) == True{} : Bool}:
  pick_le(BN.lgate(l), Nat.add(Nat.add(BN.RW(l), BN.RW(l)), Nat.add(BN.ZW(fa), BN.ZW(fa))), Nat.mul(n, BN.ZW(fa)),
    hg => la_ar(BN.lref(l), BN.FM(fa), n, N.le_trans(Nat.add(8n, BN.lref(l)), 1n+String.length(B.Line.body(l)), n, body_f3(B.Line.body(l), hg), hn)))

# A line -m may split: (1 + k) LA + k n <= n Z + n n.
law cand_ar:
  for +R: Nat
  for +k: Nat
  for +n: Nat
  for +Z: Nat
  for +la: Nat
  for +hn: {Nat.is_le(6n+Nat.add(R, Nat.add(Nat.add(k, k), 3n)), n) == True{} : Bool}
  for +hl: {Nat.is_le(la, Nat.add(Nat.add(2n+R, 2n+R), Nat.add(Z, Z))) == True{} : Bool}
  {Nat.is_le(Nat.add(la, Nat.add(Nat.mul(k, la), Nat.mul(k, n))), Nat.add(Nat.mul(n, Z), Nat.mul(n, n))) == True{} : Bool}

def cand_ar(R, k, n, Z, la, hn, hl):
  +P = {2n+R : Nat}
  +a = {1n+k : Nat}
  +y = Nat.add(a, a)
  +KK = Nat.add(k, k)
  +KK3 = Nat.add(KK, 3n)
  +L0 = Nat.add(Nat.add(P, P), Nat.add(Z, Z))
  +hk1 = AB.subst(Nat, z => {Nat.is_le(1n+z, Nat.add(3n, KK)) == True{} : Bool}, 1n+KK, Nat.add(k, 1n+k), Equal.sym(Nat, Nat.add(k, 1n+k), 1n+KK, N.add_succ(k, k)), N.le_add_l(KK, 1n))
  +hKK = AB.subst(Nat, z => {Nat.is_le(y, z) == True{} : Bool}, Nat.add(3n, KK), KK3, N.add_comm(3n, KK), hk1)
  +hpk = N.le_trans(Nat.add(R, y), Nat.add(R, KK3), 4n+Nat.add(R, KK3), N.le_add_mono_l(R, y, KK3, hKK), N.le_add_l(Nat.add(R, KK3), 4n))
  +hPy = N.le_trans(Nat.add(P, y), 6n+Nat.add(R, KK3), n, hpk, hn)
  +hy = N.le_trans(y, Nat.add(P, y), n, N.le_add_l(y, P), hPy)
  +hk = N.le_trans(k, a, y, N.le_add_l(k, 1n), N.le_add_r(a, a))
  +eP = Equal.trans(Nat, Nat.mul(a, Nat.add(P, P)), Nat.add(Nat.mul(a, P), Nat.mul(a, P)), Nat.mul(y, P), N.mul_add(a, P, P), Equal.sym(Nat, Nat.mul(y, P), Nat.add(Nat.mul(a, P), Nat.mul(a, P)), N.mul_add_r(a, a, P)))
  +eZ = Equal.trans(Nat, Nat.mul(a, Nat.add(Z, Z)), Nat.add(Nat.mul(a, Z), Nat.mul(a, Z)), Nat.mul(y, Z), N.mul_add(a, Z, Z), Equal.sym(Nat, Nat.mul(y, Z), Nat.add(Nat.mul(a, Z), Nat.mul(a, Z)), N.mul_add_r(a, a, Z)))
  +eC = Equal.trans(Nat, Nat.mul(a, L0), Nat.add(Nat.mul(a, Nat.add(P, P)), Nat.mul(a, Nat.add(Z, Z))), Nat.add(Nat.mul(y, P), Nat.mul(y, Z)), N.mul_add(a, Nat.add(P, P), Nat.add(Z, Z)),
    Equal.trans(Nat, Nat.add(Nat.mul(a, Nat.add(P, P)), Nat.mul(a, Nat.add(Z, Z))), Nat.add(Nat.mul(y, P), Nat.mul(a, Nat.add(Z, Z))), Nat.add(Nat.mul(y, P), Nat.mul(y, Z)),
      Equal.cong(Nat, Nat, w => Nat.add(w, Nat.mul(a, Nat.add(Z, Z))), Nat.mul(a, Nat.add(P, P)), Nat.mul(y, P), eP),
      Equal.cong(Nat, Nat, w => Nat.add(Nat.mul(y, P), w), Nat.mul(a, Nat.add(Z, Z)), Nat.mul(y, Z), eZ)))
  +hB = AB.subst(Nat, z => {Nat.is_le(Nat.mul(a, la), z) == True{} : Bool}, Nat.mul(a, L0), Nat.add(Nat.mul(y, P), Nat.mul(y, Z)), eC, N.le_mul_l(a, la, L0, hl))
  +A = Nat.mul(n, P)
  +B1 = Nat.mul(n, Z)
  +C1 = Nat.mul(n, y)
  +hD = add2(Nat.mul(y, P), A, Nat.mul(y, Z), B1, N.le_mul_r(y, n, P, hy), N.le_mul_r(y, n, Z, hy))
  +hk2 = AB.subst(Nat, z => {Nat.is_le(z, C1) == True{} : Bool}, Nat.mul(n, k), Nat.mul(k, n), N.mul_comm(n, k), N.le_mul_l(n, k, y, hk))
  +h3 = add2(Nat.mul(a, la), Nat.add(A, B1), Nat.mul(k, n), C1, N.le_trans(Nat.mul(a, la), Nat.add(Nat.mul(y, P), Nat.mul(y, Z)), Nat.add(A, B1), hB, hD), hk2)
  +eE = Equal.trans(Nat, Nat.add(Nat.add(A, B1), C1), Nat.add(A, Nat.add(B1, C1)), Nat.add(B1, Nat.add(A, C1)), N.add_assoc(A, B1, C1), N.add_left_comm(A, B1, C1))
  +hF = N.le_add_mono_l(B1, Nat.add(A, C1), Nat.mul(n, n),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(n, n)) == True{} : Bool}, Nat.mul(n, Nat.add(P, y)), Nat.add(A, C1), N.mul_add(n, P, y), N.le_mul_l(n, Nat.add(P, y), n, hPy)))
  +TG = Nat.add(B1, Nat.mul(n, n))
  +h4 = N.le_trans(Nat.add(Nat.mul(a, la), Nat.mul(k, n)), Nat.add(Nat.add(A, B1), C1), TG, h3,
    AB.subst(Nat, z => {Nat.is_le(z, TG) == True{} : Bool}, Nat.add(B1, Nat.add(A, C1)), Nat.add(Nat.add(A, B1), C1), Equal.sym(Nat, Nat.add(Nat.add(A, B1), C1), Nat.add(B1, Nat.add(A, C1)), eE), hF))
  AB.subst(Nat, z => {Nat.is_le(z, TG) == True{} : Bool}, Nat.add(Nat.mul(a, la), Nat.mul(k, n)), Nat.add(la, Nat.add(Nat.mul(k, la), Nat.mul(k, n))),
    N.add_assoc(la, Nat.mul(k, la), Nat.mul(k, n)), h4)

# A line -m may split, its records' share of the hand-outs: k (1 + |body|).
def XQ1(+o: B.Opts, +l: B.Line) -> Nat:
  BN.pick(BN.cand(o, l), Nat.mul(BN.nalts(l), 1n+String.length(B.Line.body(l))))

def XQ(+o: B.Opts, ls: List<&2, B.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> t:
      Nat.add(XQ1(o, l), XQ(o, t))

# One line's Wants, records' allowances and hand-out share, against n.
def WL(+fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line) -> Nat:
  Nat.add(BN.LA(fa, l), Nat.add(BN.xa(o, fa, l), XQ1(o, l)))

def GL(+sp: Bool, +Z: Nat, +n: Nat) -> Nat:
  Nat.add(Nat.mul(n, Z), BN.pick(sp, Nat.mul(n, n)))

def lw.k(+fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line, +n: Nat, +hn: {Nat.is_le(1n+String.length(B.Line.body(l)), n) == True{} : Bool}, +c: Bool, +ec: {BN.cand(o, l) == c : Bool}) ->
  {Nat.is_le(Nat.add(BN.LA(fa, l), Nat.add(BN.pick(c, Nat.mul(BN.nalts(l), BN.LA(fa, l))), BN.pick(c, Nat.mul(BN.nalts(l), 1n+String.length(B.Line.body(l)))))), GL(R.Opts.split(o), BN.ZW(fa), n)) == True{} : Bool}:
  match c:
    case False{}:
      +la = BN.LA(fa, l)
      +Z = BN.ZW(fa)
      +sp = R.Opts.split(o)
      AB.subst(Nat, z => {Nat.is_le(z, GL(sp, Z, n)) == True{} : Bool}, la, Nat.add(la, 0n), Equal.sym(Nat, Nat.add(la, 0n), la, N.add_zero(la)),
        N.le_trans(la, Nat.mul(n, Z), GL(sp, Z, n), la_n(fa, l, n, hn), N.le_add_r(Nat.mul(n, Z), BN.pick(sp, Nat.mul(n, n)))))
    case True{}:
      +la = BN.LA(fa, l)
      +Z = BN.ZW(fa)
      +sp = R.Opts.split(o)
      +bd = B.Line.body(l)
      +fs = B.Rec.fields(bd)
      +k = BN.nalts(l)
      +b1 = {1n+String.length(bd) : Nat}
      +nm = Bool.not(B.Rec.malformed(fs))
      +two = Nat.is_le(2n, k)
      +hc1 = PB.and_true_l(Bool.and(sp, nm), two, ec)
      +hsp = PB.and_true_l(sp, nm, hc1)
      +hm = PB.and_true_r(sp, nm, hc1)
      +R0 = String.length(B.Rec.field(fs, 3n))
      +hl = AB.subst(String, z => {Nat.is_le(la, Nat.add(Nat.add(2n+String.length(z), 2n+String.length(z)), Nat.add(Z, Z))) == True{} : Bool},
        B.Rec.field(J.pfs(bd), 3n), B.Rec.field(fs, 3n), f3_eq(bd), la_bound(fa, l))
      +hn2 = N.le_trans(6n+Nat.add(R0, Nat.add(Nat.add(k, k), 3n)), Q.SN(fs), n, cand_len(fs, hm),
        AB.subst(Nat, z => {Nat.is_le(z, n) == True{} : Bool}, b1, Q.SN(fs), Equal.sym(Nat, Q.SN(fs), 1n+String.length(bd), Q.split_sn(bd, '\t')), hn))
      +TG = Nat.add(Nat.mul(n, Z), Nat.mul(n, n))
      +hq = N.le_trans(Nat.add(la, Nat.add(Nat.mul(k, la), Nat.mul(k, b1))), Nat.add(la, Nat.add(Nat.mul(k, la), Nat.mul(k, n))), TG,
        N.le_add_mono_l(la, Nat.add(Nat.mul(k, la), Nat.mul(k, b1)), Nat.add(Nat.mul(k, la), Nat.mul(k, n)),
          N.le_add_mono_l(Nat.mul(k, la), Nat.mul(k, b1), Nat.mul(k, n), N.le_mul_l(k, b1, n, hn))),
        cand_ar(R0, k, n, Z, la, hn2, hl))
      AB.subst(Bool, z => {Nat.is_le(Nat.add(la, Nat.add(Nat.mul(k, la), Nat.mul(k, b1))), Nat.add(Nat.mul(n, Z), BN.pick(z, Nat.mul(n, n)))) == True{} : Bool},
        True{}, sp, Equal.sym(Bool, sp, True{}, hsp), hq)

law lw:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +l: B.Line
  for +n: Nat
  for +hn: {Nat.is_le(1n+String.length(B.Line.body(l)), n) == True{} : Bool}
  {Nat.is_le(WL(fa, o, l), GL(R.Opts.split(o), BN.ZW(fa), n)) == True{} : Bool}

def lw(fa, o, l, n, hn):
  lw.k(fa, o, l, n, hn, BN.cand(o, l), {==})

# Summed over the lines of a file.
def TW(+fa: List<&2, B.Contig>, +o: B.Opts, +ls: List<&2, B.Line>) -> Nat:
  Nat.add(BN.LAs(fa, ls), Nat.add(BN.XA(o, fa, ls), XQ(o, ls)))

def sh3(+a: Nat, +A: Nat, +b: Nat, +B1: Nat, +c: Nat, +C: Nat) ->
  {Nat.add(Nat.add(a, A), Nat.add(Nat.add(b, B1), Nat.add(c, C))) == Nat.add(Nat.add(a, Nat.add(b, c)), Nat.add(A, Nat.add(B1, C))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, A), Nat.add(Nat.add(b, B1), Nat.add(c, C))), Nat.add(Nat.add(a, A), Nat.add(Nat.add(b, c), Nat.add(B1, C))), Nat.add(Nat.add(a, Nat.add(b, c)), Nat.add(A, Nat.add(B1, C))),
    Equal.cong(Nat, Nat, w => Nat.add(Nat.add(a, A), w), Nat.add(Nat.add(b, B1), Nat.add(c, C)), Nat.add(Nat.add(b, c), Nat.add(B1, C)), N.add_swap(b, B1, c, C)),
    N.add_swap(a, A, Nat.add(b, c), Nat.add(B1, C)))

def t_cons(+fa: List<&2, B.Contig>, +o: B.Opts, +l: B.Line, +t: List<&2, B.Line>) -> {TW(fa, o, l <> t) == Nat.add(WL(fa, o, l), TW(fa, o, t)) : Nat}:
  sh3(BN.LA(fa, l), BN.LAs(fa, t), BN.xa(o, fa, l), BN.XA(o, fa, t), XQ1(o, l), XQ(o, t))

def PS(+sp: Bool, +Z: Nat, ps: List<&2, String>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case +q <> t:
      Nat.add(GL(sp, Z, 1n+String.length(q)), PS(sp, Z, t))

def lw_last(+fa: List<&2, B.Contig>, +o: B.Opts, +p: String) -> {Nat.is_le(TW(fa, o, B.Text.last(p)), PS(R.Opts.split(o), BN.ZW(fa), [p])) == True{} : Bool}:
  match p:
    case SNil{}:
      N.le_zero_l(PS(R.Opts.split(o), BN.ZW(fa), [""]))
    case SCon{+h, +t}:
      +l = B.Text.line(SCon{h, t})
      +G0 = GL(R.Opts.split(o), BN.ZW(fa), 1n+String.length(SCon{h, t}))
      AB.subst(Nat, z => {Nat.is_le(z, Nat.add(G0, 0n)) == True{} : Bool}, Nat.add(WL(fa, o, l), TW(fa, o, Nil{})), TW(fa, o, [l]), Equal.sym(Nat, TW(fa, o, [l]), Nat.add(WL(fa, o, l), TW(fa, o, Nil{})), t_cons(fa, o, l, Nil{})),
        N.le_add_mono_r(0n, WL(fa, o, l), G0, lw(fa, o, l, 1n+String.length(SCon{h, t}), body_le(SCon{h, t}))))

law lw_go:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ps: List<&2, String>
  for +p: String
  {Nat.is_le(TW(fa, o, B.Text.lines.go(ps, p)), PS(R.Opts.split(o), BN.ZW(fa), p <> ps)) == True{} : Bool}

def lw_go(fa, o, ps, p):
  match ps:
    case Nil{}:
      lw_last(fa, o, p)
    case Con{+q, +t}:
      +l = B.Text.line(p)
      +rest = B.Text.lines.go(t, q)
      AB.subst(Nat, z => {Nat.is_le(z, PS(R.Opts.split(o), BN.ZW(fa), p <> q <> t)) == True{} : Bool}, Nat.add(WL(fa, o, l), TW(fa, o, rest)), TW(fa, o, l <> rest),
        Equal.sym(Nat, TW(fa, o, l <> rest), Nat.add(WL(fa, o, l), TW(fa, o, rest)), t_cons(fa, o, l, rest)),
        add2(WL(fa, o, l), GL(R.Opts.split(o), BN.ZW(fa), 1n+String.length(p)), TW(fa, o, rest), PS(R.Opts.split(o), BN.ZW(fa), q <> t),
          lw(fa, o, l, 1n+String.length(p), body_le(p)), lw_go(fa, o, t, q)))

def lw_start(+fa: List<&2, B.Contig>, +o: B.Opts, +ps: List<&2, String>) -> {Nat.is_le(TW(fa, o, B.Text.lines.start(ps)), PS(R.Opts.split(o), BN.ZW(fa), ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      lw_go(fa, o, t, p)

def sq_add(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(b, b)), Nat.mul(Nat.add(a, b), Nat.add(a, b))) == True{} : Bool}:
  +s = Nat.add(a, b)
  AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.mul(a, a), Nat.mul(b, b)), z) == True{} : Bool}, Nat.add(Nat.mul(a, s), Nat.mul(b, s)), Nat.mul(s, s),
    Equal.sym(Nat, Nat.mul(s, s), Nat.add(Nat.mul(a, s), Nat.mul(b, s)), N.mul_add_r(a, b, s)),
    add2(Nat.mul(a, a), Nat.mul(a, s), Nat.mul(b, b), Nat.mul(b, s), N.le_mul_l(a, a, s, N.le_add_r(a, b)), N.le_mul_l(b, b, s, N.le_add_l(b, a))))

def pk_sq(+sp: Bool, +a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(BN.pick(sp, Nat.mul(a, a)), BN.pick(sp, Nat.mul(b, b))), BN.pick(sp, Nat.mul(Nat.add(a, b), Nat.add(a, b)))) == True{} : Bool}:
  match sp:
    case True{}:
      sq_add(a, b)
    case False{}:
      {==}

def gl_add(+sp: Bool, +Z: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(GL(sp, Z, a), GL(sp, Z, b)), GL(sp, Z, Nat.add(a, b))) == True{} : Bool}:
  +ma = Nat.mul(a, Z)
  +mb = Nat.mul(b, Z)
  +pa = BN.pick(sp, Nat.mul(a, a))
  +pb = BN.pick(sp, Nat.mul(b, b))
  +ms = Nat.mul(Nat.add(a, b), Z)
  AB.subst(Nat, z => {Nat.is_le(z, GL(sp, Z, Nat.add(a, b))) == True{} : Bool}, Nat.add(Nat.add(ma, mb), Nat.add(pa, pb)), Nat.add(Nat.add(ma, pa), Nat.add(mb, pb)),
    Equal.sym(Nat, Nat.add(Nat.add(ma, pa), Nat.add(mb, pb)), Nat.add(Nat.add(ma, mb), Nat.add(pa, pb)), N.add_swap(ma, pa, mb, pb)),
    add2(Nat.add(ma, mb), ms, Nat.add(pa, pb), BN.pick(sp, Nat.mul(Nat.add(a, b), Nat.add(a, b))),
      AB.subst(Nat, z => {Nat.is_le(z, ms) == True{} : Bool}, ms, Nat.add(ma, mb), N.mul_add_r(a, b, Z), N.le_refl(ms)), pk_sq(sp, a, b)))

law ps_le:
  for +sp: Bool
  for +Z: Nat
  for +ps: List<&2, String>
  {Nat.is_le(PS(sp, Z, ps), GL(sp, Z, Q.SN(ps))) == True{} : Bool}

def ps_le(sp, Z, ps):
  match ps:
    case Nil{}:
      N.le_zero_l(GL(sp, Z, 0n))
    case Con{+q, +t}:
      +nq = {1n+String.length(q) : Nat}
      N.le_trans(PS(sp, Z, q <> t), Nat.add(GL(sp, Z, nq), GL(sp, Z, Q.SN(t))), GL(sp, Z, Nat.add(nq, Q.SN(t))),
        N.le_add_mono_l(GL(sp, Z, nq), PS(sp, Z, t), GL(sp, Z, Q.SN(t)), ps_le(sp, Z, t)), gl_add(sp, Z, nq, Q.SN(t)))

# The Wants, the records' allowances and hand-out shares of a file's lines:
# within v Z + v^2 with -m, v Z without.
law lines_fit:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +s: String
  {Nat.is_le(TW(fa, o, B.Text.lines(s)), GL(R.Opts.split(o), BN.ZW(fa), 1n+String.length(s))) == True{} : Bool}

def lines_fit(fa, o, s):
  +sp = R.Opts.split(o)
  +Z = BN.ZW(fa)
  +ps = String.split(s, '\n')
  N.le_trans(TW(fa, o, B.Text.lines(s)), PS(sp, Z, ps), GL(sp, Z, 1n+String.length(s)), lw_start(fa, o, ps),
    AB.subst(Nat, z => {Nat.is_le(PS(sp, Z, ps), GL(sp, Z, z)) == True{} : Bool}, Q.SN(ps), 1n+String.length(s), Q.split_sn(s, '\n'), ps_le(sp, Z, ps)))

# The records' output share (out_len's XO) against the hand-out share XQ.
def tl.if(+cr: Bool, +p: String) -> {Nat.is_le(String.length(B.Line.text(B.Text.line.if(cr, p))), 2n+String.length(B.Line.body(B.Text.line.if(cr, p)))) == True{} : Bool}:
  match cr:
    case True{}:
      +u = String.take(p, Nat.sub(String.length(p), 1n))
      +e = Equal.trans(Nat, String.length(u ++ "\r\n"), Nat.add(String.length(u), 2n), Nat.add(2n, String.length(u)), G.slen_app(u, "\r\n"), N.add_comm(String.length(u), 2n))
      AB.subst(Nat, z => {Nat.is_le(z, 2n+String.length(u)) == True{} : Bool}, Nat.add(2n, String.length(u)), String.length(u ++ "\r\n"), Equal.sym(Nat, String.length(u ++ "\r\n"), Nat.add(2n, String.length(u)), e), N.le_refl(2n+String.length(u)))
    case False{}:
      +e = Equal.trans(Nat, String.length(p ++ "\n"), Nat.add(String.length(p), 1n), Nat.add(1n, String.length(p)), G.slen_app(p, "\n"), N.add_comm(String.length(p), 1n))
      AB.subst(Nat, z => {Nat.is_le(z, 2n+String.length(p)) == True{} : Bool}, Nat.add(1n, String.length(p)), String.length(p ++ "\n"), Equal.sym(Nat, String.length(p ++ "\n"), Nat.add(1n, String.length(p)), e), N.le_add_l(String.length(p), 1n))

def tl(+p: String) -> {Nat.is_le(String.length(B.Line.text(B.Text.line(p))), 2n+String.length(B.Line.body(B.Text.line(p)))) == True{} : Bool}:
  tl.if(String.ends_with(p, "\r"), p)

def lc3(+l: B.Line, +ht: {Nat.is_le(String.length(B.Line.text(l)), 2n+String.length(B.Line.body(l))) == True{} : Bool}) ->
  {Nat.is_le(BR.LC(B.Line.text(l)), Nat.mul(63n, 1n+String.length(B.Line.body(l)))) == True{} : Bool}:
  +bb = String.length(B.Line.body(l))
  +b1 = {1n+bb : Nat}
  +m3 = Nat.mul(3n, b1)
  +h1 = N.le_trans(1n+String.length(B.Line.text(l)), 3n+bb, m3, ht, BR.three(bb))
  AB.subst(Nat, z => {Nat.is_le(BR.LC(B.Line.text(l)), z) == True{} : Bool}, G.LIN(21n, 0n, m3), Nat.mul(63n, b1),
    Equal.trans(Nat, G.LIN(21n, 0n, m3), Nat.mul(21n, m3), Nat.mul(63n, b1), BR.lin_mul(21n, m3), Equal.sym(Nat, Nat.mul(Nat.mul(21n, 3n), b1), Nat.mul(21n, m3), N.mul_assoc(21n, 3n, b1))),
    G.lin_x(21n, 0n, 1n+String.length(B.Line.text(l)), m3, h1))

def xo1.k(+c: Bool, +k: Nat, +lc: Nat, +b1: Nat, +h: {Nat.is_le(lc, Nat.mul(63n, b1)) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(BN.pick(c, Nat.mul(k, lc)), BN.pick(c, Nat.mul(k, lc))), Nat.mul(256n, BN.pick(c, Nat.mul(k, b1)))) == True{} : Bool}:
  match c:
    case False{}:
      N.le_zero_l(Nat.mul(256n, 0n))
    case True{}:
      +Y = Nat.mul(k, b1)
      +M0 = Nat.mul(k, lc)
      +e = Equal.trans(Nat, Nat.mul(k, Nat.mul(128n, b1)), Nat.mul(Nat.mul(k, 128n), b1), Nat.mul(128n, Y),
        Equal.sym(Nat, Nat.mul(Nat.mul(k, 128n), b1), Nat.mul(k, Nat.mul(128n, b1)), N.mul_assoc(k, 128n, b1)),
        Equal.trans(Nat, Nat.mul(Nat.mul(k, 128n), b1), Nat.mul(Nat.mul(128n, k), b1), Nat.mul(128n, Y),
          Equal.cong(Nat, Nat, w => Nat.mul(w, b1), Nat.mul(k, 128n), Nat.mul(128n, k), N.mul_comm(k, 128n)), N.mul_assoc(128n, k, b1)))
      +hm = AB.subst(Nat, z => {Nat.is_le(M0, z) == True{} : Bool}, Nat.mul(k, Nat.mul(128n, b1)), Nat.mul(128n, Y), e,
        N.le_mul_l(k, lc, Nat.mul(128n, b1), N.le_trans(lc, Nat.mul(63n, b1), Nat.mul(128n, b1), h, N.le_mul_r(63n, 128n, b1, {==}))))
      AB.subst(Nat, z => {Nat.is_le(Nat.add(M0, M0), z) == True{} : Bool}, Nat.add(Nat.mul(128n, Y), Nat.mul(128n, Y)), Nat.mul(256n, Y),
        Equal.sym(Nat, Nat.mul(Nat.add(128n, 128n), Y), Nat.add(Nat.mul(128n, Y), Nat.mul(128n, Y)), N.mul_add_r(128n, 128n, Y)), add2(M0, Nat.mul(128n, Y), M0, Nat.mul(128n, Y), hm, hm))

def xo1(+o: B.Opts, +l: B.Line, +ht: {Nat.is_le(String.length(B.Line.text(l)), 2n+String.length(B.Line.body(l))) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(BR.XO1(o, l), BR.XO1(o, l)), Nat.mul(256n, XQ1(o, l))) == True{} : Bool}:
  xo1.k(BN.cand(o, l), BN.nalts(l), BR.LC(B.Line.text(l)), 1n+String.length(B.Line.body(l)), lc3(l, ht))

def xo_cons(+o: B.Opts, +l: B.Line, +t: List<&2, B.Line>, +hl: {Nat.is_le(Nat.add(BR.XO1(o, l), BR.XO1(o, l)), Nat.mul(256n, XQ1(o, l))) == True{} : Bool},
  +ht: {Nat.is_le(Nat.add(BR.XO(o, t), BR.XO(o, t)), Nat.mul(256n, XQ(o, t))) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(BR.XO(o, l <> t), BR.XO(o, l <> t)), Nat.mul(256n, XQ(o, l <> t))) == True{} : Bool}:
  +x = BR.XO1(o, l)
  +X = BR.XO(o, t)
  +q = XQ1(o, l)
  +Qt = XQ(o, t)
  AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(x, X), Nat.add(x, X)), z) == True{} : Bool}, Nat.add(Nat.mul(256n, q), Nat.mul(256n, Qt)), Nat.mul(256n, Nat.add(q, Qt)),
    Equal.sym(Nat, Nat.mul(256n, Nat.add(q, Qt)), Nat.add(Nat.mul(256n, q), Nat.mul(256n, Qt)), N.mul_add(256n, q, Qt)),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Nat.mul(256n, q), Nat.mul(256n, Qt))) == True{} : Bool}, Nat.add(Nat.add(x, x), Nat.add(X, X)), Nat.add(Nat.add(x, X), Nat.add(x, X)),
      Equal.sym(Nat, Nat.add(Nat.add(x, X), Nat.add(x, X)), Nat.add(Nat.add(x, x), Nat.add(X, X)), N.add_swap(x, X, x, X)),
      add2(Nat.add(x, x), Nat.mul(256n, q), Nat.add(X, X), Nat.mul(256n, Qt), hl, ht)))

law xo_go:
  for +o: B.Opts
  for +ps: List<&2, String>
  for +p: String
  {Nat.is_le(Nat.add(BR.XO(o, B.Text.lines.go(ps, p)), BR.XO(o, B.Text.lines.go(ps, p))), Nat.mul(256n, XQ(o, B.Text.lines.go(ps, p)))) == True{} : Bool}

def xo_go(o, ps, p):
  match ps:
    case Nil{}:
      match p:
        case SNil{}:
          N.le_zero_l(Nat.mul(256n, XQ(o, Nil{})))
        case SCon{+h, +t}:
          xo_cons(o, B.Text.line(SCon{h, t}), Nil{}, xo1(o, B.Text.line(SCon{h, t}), tl(SCon{h, t})), N.le_zero_l(Nat.mul(256n, XQ(o, Nil{}))))
    case Con{+q, +t}:
      xo_cons(o, B.Text.line(p), B.Text.lines.go(t, q), xo1(o, B.Text.line(p), tl(p)), xo_go(o, t, q))

def xo_start(+o: B.Opts, +ps: List<&2, String>) ->
  {Nat.is_le(Nat.add(BR.XO(o, B.Text.lines.start(ps)), BR.XO(o, B.Text.lines.start(ps))), Nat.mul(256n, XQ(o, B.Text.lines.start(ps)))) == True{} : Bool}:
  match ps:
    case Nil{}:
      N.le_zero_l(Nat.mul(256n, XQ(o, Nil{})))
    case Con{+p, +t}:
      xo_go(o, t, p)

# Hand-outs: HO + K within v + AL + XQ (K: 256 K <= 12 |vcf|).
def lt256(+a: Nat, +X: Nat, +h: {Nat.is_le(a, Nat.mul(256n, X)) == True{} : Bool}) -> {Nat.is_lt(a, Nat.mul(256n, 1n+X)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(256n, 1n+X), Nat.add(256n, Nat.mul(256n, X)), N.mul_succ_r(256n, X)) : {Nat.is_lt(a, _) == True{} : Bool}
  %N.le_succ_lt(a, Nat.add(256n, Nat.mul(256n, X))) : {_ == True{} : Bool}
  add2(1n, 256n, a, Nat.mul(256n, X), {==}, h)

def div256(+a: Nat, +X: Nat, +h: {Nat.is_le(a, Nat.mul(256n, X)) == True{} : Bool}) -> {Nat.is_le(Nat.div(a, 256n), X) == True{} : Bool}:
  %N.lt_succ_iff(Nat.div(a, 256n), X) : {_ == True{} : Bool}
  N.div_lt(a, 256n, 1n+X, {==}, lt256(a, X, h))

def lin63(+u: Nat, +c: Nat) -> {Nat.mul(c, 1n+u) == G.LIN(c, c, u) : Nat}:
  Equal.trans(Nat, Nat.mul(c, 1n+u), Nat.add(c, Nat.mul(c, u)), G.LIN(c, c, u), N.mul_succ_r(c, u),
    Equal.trans(Nat, Nat.add(c, Nat.mul(c, u)), Nat.add(c, G.LIN(c, 0n, u)), G.LIN(c, c, u),
      Equal.cong(Nat, Nat, w => Nat.add(c, w), Nat.mul(c, u), G.LIN(c, 0n, u), Equal.sym(Nat, G.LIN(c, 0n, u), Nat.mul(c, u), BR.lin_mul(c, u))),
      AB.subst(Nat, z => {Nat.add(c, G.LIN(c, 0n, u)) == G.LIN(c, z, u) : Nat}, Nat.add(c, 0n), c, N.add_zero(c), G.lin_c(c, c, 0n, u))))

def ob_core(+u: Nat, +A1: Nat, +AL: Nat, +hA: {Nat.is_le(A1, AL) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(Nat.mul(63n, 1n+u), Nat.add(61n, A1)), Nat.add(Nat.mul(63n, 1n+u), Nat.add(61n, A1)))), Nat.mul(256n, Nat.add(1n+u, AL))) == True{} : Bool}:
  +M0 = Nat.mul(63n, 1n+u)
  +C = Nat.add(61n, A1)
  +x = Nat.mul(12n, u)
  +y = Nat.add(M0, M0)
  +w = Nat.add(A1, A1)
  +eC = N.add_swap(61n, A1, 61n, A1)
  +eL = Equal.trans(Nat, Nat.add(x, Nat.add(Nat.add(M0, C), Nat.add(M0, C))), Nat.add(x, Nat.add(y, Nat.add(122n, w))), Nat.add(Nat.add(Nat.add(x, y), 122n), w),
    Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(Nat.add(M0, C), Nat.add(M0, C)), Nat.add(y, Nat.add(122n, w)),
      Equal.trans(Nat, Nat.add(Nat.add(M0, C), Nat.add(M0, C)), Nat.add(y, Nat.add(C, C)), Nat.add(y, Nat.add(122n, w)), N.add_swap(M0, C, M0, C),
        Equal.cong(Nat, Nat, z => Nat.add(y, z), Nat.add(C, C), Nat.add(122n, w), eC))),
    Equal.trans(Nat, Nat.add(x, Nat.add(y, Nat.add(122n, w))), Nat.add(Nat.add(x, y), Nat.add(122n, w)), Nat.add(Nat.add(Nat.add(x, y), 122n), w),
      Equal.sym(Nat, Nat.add(Nat.add(x, y), Nat.add(122n, w)), Nat.add(x, Nat.add(y, Nat.add(122n, w))), N.add_assoc(x, y, Nat.add(122n, w))),
      Equal.sym(Nat, Nat.add(Nat.add(Nat.add(x, y), 122n), w), Nat.add(Nat.add(x, y), Nat.add(122n, w)), N.add_assoc(Nat.add(x, y), 122n, w))))
  +hx = AB.subst(Nat, z => {Nat.is_le(x, z) == True{} : Bool}, x, G.LIN(12n, 0n, u), Equal.sym(Nat, G.LIN(12n, 0n, u), x, BR.lin_mul(12n, u)), N.le_refl(x))
  +hM = AB.subst(Nat, z => {Nat.is_le(M0, z) == True{} : Bool}, M0, G.LIN(63n, 63n, u), lin63(u, 63n), N.le_refl(M0))
  +hy = G.lin_add(M0, M0, 63n, 63n, 63n, 63n, u, hM, hM)
  +hxy = G.lin_add(x, y, 12n, 0n, 126n, 126n, u, hx, hy)
  +h122 = G.lin_add(Nat.add(x, y), 122n, 138n, 126n, 0n, 122n, u, hxy, G.lin_k(122n, 122n, u, N.le_refl(122n)))
  +p1 = AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(x, y), 122n), z) == True{} : Bool}, G.LIN(256n, 256n, u), Nat.mul(256n, 1n+u), Equal.sym(Nat, Nat.mul(256n, 1n+u), G.LIN(256n, 256n, u), lin63(u, 256n)),
    N.le_trans(Nat.add(Nat.add(x, y), 122n), G.LIN(138n, 248n, u), G.LIN(256n, 256n, u), h122, G.lin_mono(138n, 248n, 256n, 256n, u, {==}, {==})))
  +p2 = N.le_trans(w, Nat.add(AL, AL), Nat.mul(256n, AL), add2(A1, AL, A1, AL, hA, hA),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(256n, AL)) == True{} : Bool}, Nat.mul(2n, AL), Nat.add(AL, AL), Equal.trans(Nat, Nat.mul(2n, AL), Nat.double(AL), Nat.add(AL, AL), N.mul2(AL), N.dbl_add(AL)),
      N.le_mul_r(2n, 256n, AL, {==})))
  AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(256n, Nat.add(1n+u, AL))) == True{} : Bool}, Nat.add(Nat.add(Nat.add(x, y), 122n), w), Nat.add(x, Nat.add(Nat.add(M0, C), Nat.add(M0, C))),
    Equal.sym(Nat, Nat.add(x, Nat.add(Nat.add(M0, C), Nat.add(M0, C))), Nat.add(Nat.add(Nat.add(x, y), 122n), w), eL),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(Nat.add(x, y), 122n), w), z) == True{} : Bool}, Nat.add(Nat.mul(256n, 1n+u), Nat.mul(256n, AL)), Nat.mul(256n, Nat.add(1n+u, AL)),
      Equal.sym(Nat, Nat.mul(256n, Nat.add(1n+u, AL)), Nat.add(Nat.mul(256n, 1n+u), Nat.mul(256n, AL)), N.mul_add(256n, 1n+u, AL)),
      add2(Nat.add(Nat.add(x, y), 122n), Nat.mul(256n, 1n+u), w, Nat.mul(256n, AL), p1, p2)))

def obfit(+vcf: String, +o: B.Opts, +AL: Nat, +hA: {Nat.is_le(String.length(R.args_text(oargs(o))), AL) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.mul(12n, String.length(vcf)), Nat.add(BR.OB(vcf, o), BR.OB(vcf, o))), Nat.mul(256n, Nat.add(1n+String.length(vcf), AL))) == True{} : Bool}:
  match o:
    case B.Opts{+s, +w, +om_m, +om_z, +args}:
      ob_core(String.length(vcf), String.length(R.args_text(args)), AL, hA)

law hoK:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +K: Nat
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hK: {Nat.is_le(Nat.mul(256n, K), Nat.mul(12n, String.length(vcf))) == True{} : Bool}
  {Nat.is_le(Nat.add(BN.HO(L.run(fasta, vcf, o), ""), K), Nat.add(Nat.add(1n+String.length(vcf), M.args_len(argv)), XQ(o, B.Text.lines(vcf)))) == True{} : Bool}

def hoK(dfs, argv, o, ref, vcfpath, fasta, vcf, K, ha, hK):
  +nO = String.length(R.Report.out(L.run(fasta, vcf, o)))
  +a = Nat.sub(nO, String.length(""))
  +u = String.length(vcf)
  +AL = M.args_len(argv)
  +ls = B.Text.lines(vcf)
  +XQV = XQ(o, ls)
  +XOV = BR.XO(o, ls)
  +OB = BR.OB(vcf, o)
  +X = Nat.add(Nat.add(1n+u, AL), XQV)
  +KM = Nat.mul(K, 256n)
  +ho = Nat.div(a, 256n)
  +e1 = Equal.trans(Nat, Nat.add(ho, K), Nat.add(K, ho), Nat.div(Nat.add(KM, a), 256n), N.add_comm(ho, K),
    Equal.sym(Nat, Nat.div(Nat.add(KM, a), 256n), Nat.add(K, ho), N.div_add_mul(K, 256n, a, {==})))
  +hK2 = AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(12n, u)) == True{} : Bool}, Nat.mul(256n, K), KM, N.mul_comm(256n, K), hK)
  +hout = N.le_trans(a, nO, Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV)), sub0_le(nO), BR.out_len(dfs, fasta, vcf, o))
  +eO = Equal.trans(Nat, Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV))), Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, OB), Nat.add(XOV, XOV))),
    Nat.add(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(XOV, XOV)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(12n, u), z), Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV)), Nat.add(Nat.add(OB, OB), Nat.add(XOV, XOV)), N.add_swap(OB, XOV, OB, XOV)),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(XOV, XOV)), Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, OB), Nat.add(XOV, XOV))),
      N.add_assoc(Nat.mul(12n, u), Nat.add(OB, OB), Nat.add(XOV, XOV))))
  +hR = AB.subst(Nat, z => {Nat.is_le(z, Nat.mul(256n, X)) == True{} : Bool}, Nat.add(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(XOV, XOV)), Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV))),
    Equal.sym(Nat, Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV))), Nat.add(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(XOV, XOV)), eO),
    AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.add(XOV, XOV)), z) == True{} : Bool}, Nat.add(Nat.mul(256n, Nat.add(1n+u, AL)), Nat.mul(256n, XQV)), Nat.mul(256n, X),
      Equal.sym(Nat, Nat.mul(256n, X), Nat.add(Nat.mul(256n, Nat.add(1n+u, AL)), Nat.mul(256n, XQV)), N.mul_add(256n, Nat.add(1n+u, AL), XQV)),
      add2(Nat.add(Nat.mul(12n, u), Nat.add(OB, OB)), Nat.mul(256n, Nat.add(1n+u, AL)), Nat.add(XOV, XOV), Nat.mul(256n, XQV),
        obfit(vcf, o, AL, args_le(argv, o, ref, vcfpath, ha)), xo_start(o, String.split(vcf, '\n')))))
  AB.subst(Nat, z => {Nat.is_le(z, X) == True{} : Bool}, Nat.div(Nat.add(KM, a), 256n), Nat.add(ho, K), Equal.sym(Nat, Nat.add(ho, K), Nat.div(Nat.add(KM, a), 256n), e1),
    div256(Nat.add(KM, a), X, N.le_trans(Nat.add(KM, a), Nat.add(Nat.mul(12n, u), Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV))), Nat.mul(256n, X), add2(KM, Nat.mul(12n, u), a, Nat.add(Nat.add(OB, XOV), Nat.add(OB, XOV)), hK2, hout), hR)))

# The sum against the bound: c + 1 + 2 + (H + K) + (W + XA) within
# c + 3 + AL + v (F + 3) + SR, with H + K <= v + AL + XQ and
# W + XA + XQ <= v (2 + FM) + SR.
law fitfin:
  for +c: Nat
  for +H: Nat
  for +K: Nat
  for +W: Nat
  for +XA0: Nat
  for +XQ0: Nat
  for +AL: Nat
  for +v: Nat
  for +F: Nat
  for +FM: Nat
  for +SR: Nat
  for +hH: {Nat.is_le(Nat.add(H, K), Nat.add(Nat.add(v, AL), XQ0)) == True{} : Bool}
  for +hW: {Nat.is_le(Nat.add(W, Nat.add(XA0, XQ0)), Nat.add(Nat.mul(v, 2n+FM), SR)) == True{} : Bool}
  for +hF: {Nat.is_le(FM, F) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(Nat.add(H, K), Nat.add(W, XA0)))), Nat.add(Nat.add(Nat.add(Nat.add(c, 3n), AL), Nat.mul(v, Nat.add(F, 3n))), SR)) == True{} : Bool}

def fitfin(c, H, K, W, XA0, XQ0, AL, v, F, FM, SR, hH, hW, hF):
  +P = Nat.add(v, AL)
  +Qv = Nat.mul(v, 2n+FM)
  +Y = Nat.add(P, Qv)
  +B0 = Nat.add(Nat.add(Nat.add(c, 3n), AL), Nat.mul(v, Nat.add(F, 3n)))
  +E0 = fin(c, P, Qv, AL, v, F, FM, N.le_refl(P), N.le_refl(Qv), hF)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(P, XQ0), Nat.add(W, XA0)), Nat.add(P, Nat.add(XQ0, Nat.add(W, XA0))), Nat.add(P, Nat.add(W, Nat.add(XA0, XQ0))),
    N.add_assoc(P, XQ0, Nat.add(W, XA0)),
    Equal.cong(Nat, Nat, z => Nat.add(P, z), Nat.add(XQ0, Nat.add(W, XA0)), Nat.add(W, Nat.add(XA0, XQ0)),
      Equal.trans(Nat, Nat.add(XQ0, Nat.add(W, XA0)), Nat.add(W, Nat.add(XQ0, XA0)), Nat.add(W, Nat.add(XA0, XQ0)), N.add_left_comm(XQ0, W, XA0),
        Equal.cong(Nat, Nat, z => Nat.add(W, z), Nat.add(XQ0, XA0), Nat.add(XA0, XQ0), N.add_comm(XQ0, XA0)))))
  +h1 = N.le_trans(Nat.add(Nat.add(H, K), Nat.add(W, XA0)), Nat.add(Nat.add(P, XQ0), Nat.add(W, XA0)), Nat.add(Y, SR),
    N.le_add_mono_r(Nat.add(W, XA0), Nat.add(H, K), Nat.add(P, XQ0), hH),
    AB.subst(Nat, z => {Nat.is_le(z, Nat.add(Y, SR)) == True{} : Bool}, Nat.add(P, Nat.add(W, Nat.add(XA0, XQ0))), Nat.add(Nat.add(P, XQ0), Nat.add(W, XA0)),
      Equal.sym(Nat, Nat.add(Nat.add(P, XQ0), Nat.add(W, XA0)), Nat.add(P, Nat.add(W, Nat.add(XA0, XQ0))), e1),
      AB.subst(Nat, z => {Nat.is_le(Nat.add(P, Nat.add(W, Nat.add(XA0, XQ0))), z) == True{} : Bool}, Nat.add(P, Nat.add(Qv, SR)), Nat.add(Y, SR),
        Equal.sym(Nat, Nat.add(Y, SR), Nat.add(P, Nat.add(Qv, SR)), N.add_assoc(P, Qv, SR)),
        N.le_add_mono_l(P, Nat.add(W, Nat.add(XA0, XQ0)), Nat.add(Qv, SR), hW))))
  +C1 = Nat.add(c, 1n)
  +h2 = N.le_add_mono_l(C1, Nat.add(2n, Nat.add(Nat.add(H, K), Nat.add(W, XA0))), Nat.add(2n, Nat.add(Y, SR)), N.le_add_mono_l(2n, Nat.add(Nat.add(H, K), Nat.add(W, XA0)), Nat.add(Y, SR), h1))
  N.le_trans(Nat.add(C1, Nat.add(2n, Nat.add(Nat.add(H, K), Nat.add(W, XA0)))), Nat.add(C1, Nat.add(Nat.add(2n, Y), SR)), Nat.add(B0, SR), h2,
    AB.subst(Nat, z => {Nat.is_le(z, Nat.add(B0, SR)) == True{} : Bool}, Nat.add(Nat.add(C1, Nat.add(2n, Y)), SR), Nat.add(C1, Nat.add(Nat.add(2n, Y), SR)),
      N.add_assoc(C1, Nat.add(2n, Y), SR), N.le_add_mono_r(SR, Nat.add(C1, Nat.add(2n, Y)), B0, E0)))

def sp_eq(+o: B.Opts, +r: String, +vp: String) -> {M.splits.of(Some{B.Cfg{o, r, vp}}) == R.Opts.split(o) : Bool}:
  match o:
    case B.Opts{+s, +w, +sp, +o0, +args}:
      {==}

def sr_eq(+sp: Bool, +vcf: String) -> {BN.pick(sp, Nat.mul(1n+String.length(vcf), 1n+String.length(vcf))) == M.split_room(sp, vcf) : Nat}:
  match sp:
    case True{}:
      {==}
    case False{}:
      {==}

# The start's potential, with K more (the threads machine's), fits M.bound.
law start_fit:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +K: Nat
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  for +hst: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  for +hK: {Nat.is_le(Nat.mul(256n, K), Nat.mul(12n, String.length(vcf))) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(List.length(&2, String, cs), 1n), Nat.add(2n, Nat.add(Nat.add(BN.HO(L.run(fasta, vcf, o), ""), K), BN.WAS(B.Fasta.parse(fasta), S.mkSt(B.Fasta.parse(fasta), p), cs)))), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def start_fit(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, K, ha, h, hst, hK):
  +fa = B.Fasta.parse(fasta)
  +T = L.run(fasta, vcf, o)
  +c = List.length(&2, String, cs)
  +H = BN.HO(T, "")
  +bd = M.bound(argv, fasta, vcf, cs)
  +sp = R.Opts.split(o)
  +Z = BN.ZW(fa)
  +v = Nat.add(1n, String.length(vcf))
  +AL = M.args_len(argv)
  +lv = B.Text.lines(vcf)
  +XQV = XQ(o, lv)
  +SRp = BN.pick(sp, Nat.mul(v, v))
  +B0 = Nat.add(Nat.add(Nat.add(c, 3n), AL), Nat.mul(v, Nat.add(String.length(fasta), 3n)))
  %hst : {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(Nat.add(H, K), BN.WAS(fa, _, cs)))), bd) == True{} : Bool}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(Nat.add(H, K), BN.WAS(fa, DD.start_st(dfs, Norm.start.of(_)), cs)))), Nat.add(B0, M.split_room(M.splits.of(_), vcf))) == True{} : Bool}
  %Equal.sym(Bool, M.splits.of(Some{B.Cfg{o, ref, vcfpath}}), sp, sp_eq(o, ref, vcfpath)) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(Nat.add(H, K), BN.WAS(fa, DD.start_st(dfs, Norm.start.of(Some{B.Cfg{o, ref, vcfpath}})), cs)))), Nat.add(B0, M.split_room(_, vcf))) == True{} : Bool}
  %sr_eq(sp, vcf) :
    {Nat.is_le(Nat.add(Nat.add(c, 1n), Nat.add(2n, Nat.add(Nat.add(H, K), BN.WAS(fa, DD.start_st(dfs, Norm.start.of(Some{B.Cfg{o, ref, vcfpath}})), cs)))), Nat.add(B0, _)) == True{} : Bool}
  +hWv = N.le_trans(Nat.add(BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, lv), Nat.add(BN.XA(o, fa, lv), XQV)), TW(fa, o, lv), GL(sp, Z, v),
    N.le_add_mono_r(Nat.add(BN.XA(o, fa, lv), XQV), BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, lv), BN.LAs(fa, lv), wa_le(fa, lv)), lines_fit(fa, o, vcf))
  +hW = AB.subst(String, z => {Nat.is_le(Nat.add(BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, B.Text.lines(z)), Nat.add(BN.XA(o, fa, B.Text.lines(z)), XQV)), GL(sp, Z, v)) == True{} : Bool},
    vcf, String.concat(cs), Equal.sym(String, String.concat(cs), vcf, h), hWv)
  fitfin(c, H, K, BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, B.Text.lines(String.concat(cs))), BN.XA(o, fa, B.Text.lines(String.concat(cs))), XQV, AL, v, String.length(fasta), BN.FM(fa), SRp,
    hoK(dfs, argv, o, ref, vcfpath, fasta, vcf, K, ha, hK), hW, fa_fm(fasta))

law bud_need:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  for +hst: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {Nat.is_le(BN.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def bud_need(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst):
  +fa = B.Fasta.parse(fasta)
  +H = BN.HO(L.run(fasta, vcf, o), "")
  AB.subst(Nat, z => {Nat.is_le(Nat.add(Nat.add(List.length(&2, String, cs), 1n), Nat.add(2n, Nat.add(z, BN.WAS(fa, S.mkSt(fa, p), cs)))), M.bound(argv, fasta, vcf, cs)) == True{} : Bool},
    Nat.add(H, 0n), H, N.add_zero(H), start_fit(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, 0n, ha, h, hst, N.le_zero_l(Nat.mul(12n, String.length(vcf)))))

# bud_start (proof_b_budget_api.bend).
law bud_start_h:
  for +dfs: B.Defs
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +h: {String.concat(cs) == vcf : String}
  for +hst: {DD.start_st(dfs, Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {BN.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}
    & {Nat.is_le(BN.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def bud_start_h(dfs,argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst):
  (bud_bi(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hst), bud_need(dfs, argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst))
