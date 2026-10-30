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
import ./proof_fast.bend as PF
import ./proof_machine_fasta.bend as MF
import ./proof_base.bend as PB
import ./proof_machine_nat.bend as PN
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/bytes.bend as BY
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
    case B.Opts{s, w, a}:
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
    case B.ArgSt{pe, s, w, t, r, v, ok, k}:
      match pe:
        case B.PNone{}:
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
    case B.Opts{+s, +w, +args}:
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

# The hand-outs still to come at the start: at most (|vcf| + 1) + args_len.
law ho_le:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  {Nat.is_le(BN.HO(L.run(fasta, vcf, o), ""), Nat.add(1n+String.length(vcf), M.args_len(argv))) == True{} : Bool}

def ho_le(argv, o, ref, vcfpath, fasta, vcf, ha):
  +n = String.length(R.Report.out(L.run(fasta, vcf, o)))
  +X = Nat.add(1n+String.length(vcf), M.args_len(argv))
  div_le(Nat.sub(n, String.length("")), X, 256n, {==},
    N.le_trans(Nat.sub(n, String.length("")), n, Nat.mul(248n, X), sub0_le(n),
      N.le_trans(n, Nat.add(BR.OB(vcf, o), BR.OB(vcf, o)), Nat.mul(248n, X), BR.out_len(fasta, vcf, o),
        ob2(vcf, o, M.args_len(argv), args_le(argv, o, ref, vcfpath, ha)))))

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
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +fasta: String
  for +vcf: String
  for +cs: List<&2, String>
  for +p: S.StP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hst: {DD.start_st(Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {BN.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}

def bud_bi(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hst):
  %hst : {BN.biS(_, cs) == True{} : Bool}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) : {BN.biS(DD.start_st(Norm.start.of(_)), cs) == True{} : Bool}
  bi0(BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs))

law bud_need:
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
  for +hst: {DD.start_st(Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {Nat.is_le(BN.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def bud_need(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst):
  +fa = B.Fasta.parse(fasta)
  +T = L.run(fasta, vcf, o)
  +bd = M.bound(argv, fasta, vcf, cs)
  +ls = BN.lines(Nil{}, Norm.PB{BY.empty(0n)}, False{}, cs)
  +v = Nat.add(1n, String.length(vcf))
  %hst : {Nat.is_le(BN.needS(fa, T, _, cs, False{}, Pr.More{}, ""), bd) == True{} : Bool}
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {Nat.is_le(BN.needS(fa, T, DD.start_st(Norm.start.of(_)), cs, False{}, Pr.More{}, ""), bd) == True{} : Bool}
  fin(List.length(&2, String, cs), BN.HO(T, ""), BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, ls), M.args_len(argv), v, String.length(fasta), BN.FM(fa),
    ho_le(argv, o, ref, vcfpath, fasta, vcf, ha),
    N.le_trans(BN.WA.ls(fa, True{}, 0n, Norm.WNone{}, None{}, ls), BN.LAs(fa, ls), Nat.mul(v, BN.ZW(fa)), wa_le(fa, ls), las_cs(fa, cs, vcf, h)),
    fa_fm(fasta))

# bud_start (proof_b_budget_api.bend).
law bud_start_h:
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
  for +hst: {DD.start_st(Norm.start(argv)) == S.mkSt(B.Fasta.parse(fasta), p) : Norm.St}
  {BN.bi(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, "") == True{} : Bool}
    & {Nat.is_le(BN.need(B.Fasta.parse(fasta), L.run(fasta, vcf, o), p, cs, False{}, Pr.More{}, ""), M.bound(argv, fasta, vcf, cs)) == True{} : Bool}

def bud_start_h(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst):
  (bud_bi(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, hst), bud_need(argv, o, ref, vcfpath, fasta, vcf, cs, p, ha, h, hst))
