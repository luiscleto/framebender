import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./norm.bend as Norm
import ./norm_run.bend as NR
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_run.bend as PR
import ./proof_b_lines.bend as PL
import ./proof_b_drivedefs.bend as DR
import ./proof_b_drive_out.bend as DO
import ./proof_base.bend as PB
import ./proof_b_frame_fr.bend as FR
import ../lawful-bytes/bytes.bend as BY

# Helpers for proof_b_drive.bend's start_ok. start_ok as stated is false
# (proof_b_drive_cex.bend, third case): S.WF asks the options' arguments to
# be bytes, and start_ok does not assume the command line is. start_ok_g is
# the statement with that hypothesis added (hab, as E.texts_ok gives it to
# the law machine).

# The options' arguments of a parsed command line (none for a usage error).
def cfg_args(m: Maybe<&2, B.Cfg>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{B.Cfg{o, r, v}}:
      S.opts_args(o)

law args_done:
  for +st: B.ArgSt
  for +args: List<&2, String>
  for +h: {E.all_bytes(args) == True{} : Bool}
  {E.all_bytes(cfg_args(B.Args.done(st, args))) == True{} : Bool}

def args_done(st, args, h):
  match st:
    case B.ArgSt{pe, s, w, r, v, ok}:
      match pe:
        case B.PNone{}:
          match r:
            case None{}:
              {==}
            case Some{r1}:
              match v:
                case None{}:
                  {==}
                case Some{v1}:
                  match ok:
                    case True{}:
                      h
                    case False{}:
                      {==}
        case B.PRef{}:
          {==}
        case B.PCheck{}:
          {==}
        case B.PWin{}:
          {==}

law args_if:
  for +c: Bool
  for +rest: List<&2, String>
  for +h: {E.all_bytes(rest) == True{} : Bool}
  {E.all_bytes(cfg_args(B.Args.done.if(c, rest))) == True{} : Bool}

def args_if(c, rest, h):
  match c:
    case True{}:
      args_done(B.Args.go(rest, B.ArgSt{B.PNone{}, True{}, None{}, None{}, None{}, True{}}), rest, h)
    case False{}:
      {==}

# A command line of bytes gives options whose arguments are bytes.
law args_parse:
  for +argv: List<&2, String>
  for +h: {E.all_bytes(argv) == True{} : Bool}
  {E.all_bytes(cfg_args(B.Args.parse(argv))) == True{} : Bool}

def args_parse(argv, h):
  match argv:
    case Nil{}:
      {==}
    case +cmd <> +rest:
      args_if(String.eq(cmd, "norm"), rest, PB.and_true_r(E.is_bytes(cmd), E.all_bytes(rest), h))

# S.WF of the start state's shape: every test that does not reduce by
# itself holds.
law x8_start:
  for +a: Bool
  for +b2: Bool
  for +b3: Bool
  for +b7: Bool
  for +ha: {a == True{} : Bool}
  for +h2: {b2 == True{} : Bool}
  for +h3: {b3 == True{} : Bool}
  for +h7: {b7 == True{} : Bool}
  {DO.X8(a, True{}, b2, b3, True{}, True{}, True{}, True{}, b7) == True{} : Bool}

def x8_start(a, b2, b3, b7, ha, h2, h3, h7):
  %Equal.sym(Bool, a, True{}, ha) : {DO.X8(_, True{}, b2, b3, True{}, True{}, True{}, True{}, b7) == True{} : Bool}
  %Equal.sym(Bool, b2, True{}, h2) : {DO.X8(True{}, True{}, _, b3, True{}, True{}, True{}, True{}, b7) == True{} : Bool}
  %Equal.sym(Bool, b3, True{}, h3) : {DO.X8(True{}, True{}, True{}, _, True{}, True{}, True{}, True{}, b7) == True{} : Bool}
  %Equal.sym(Bool, b7, True{}, h7) : {DO.X8(True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, _) == True{} : Bool}
  {==}

# The options' arguments are bytes, from the parse and a command line of bytes.
law AB_args:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hab: {E.all_bytes(argv) == True{} : Bool}
  {E.all_bytes(S.opts_args(o)) == True{} : Bool}

def AB_args(argv, o, ref, vcfpath, ha, hab):
  %ha : {E.all_bytes(cfg_args(_)) == True{} : Bool}
  args_parse(argv, hab)

law g_st:
  for +fa: List<&2, B.Contig>
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +rp: P.RunP
  for +pp: P.PdP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +e1: {NR.start() == P.mkRun(rp) : NR.Run}
  for +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
  {DR.start_st(Norm.start(argv)) == S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}) : Norm.St}

law mk_p0:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +pp: P.PdP
  {S.mkSt(fa, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}) == Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pp), False{}, 0n, Norm.WNone{}, None{}, False{}} : Norm.St}

def mk_p0(fa, o, rp, pp):
  {==}

def g_st(fa, argv, o, ref, vcfpath, rp, pp, ha, e1, f1):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {DR.start_st(Norm.start.of(_)) == Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pp), False{}, 0n, Norm.WNone{}, None{}, False{}} : Norm.St}
  %Equal.sym(NR.Run, NR.start(), P.mkRun(rp), e1) :
    {Norm.St{o, Norm.MB{_}, Nil{}, Norm.PB{BY.empty(0n)}, False{}, 0n, Norm.WNone{}, None{}, False{}} == Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pp), False{}, 0n, Norm.WNone{}, None{}, False{}} : Norm.St}
  %Equal.sym(Norm.Pd, Norm.PB{BY.empty(0n)}, P.mkPd(pp), f1) :
    {Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, _, False{}, 0n, Norm.WNone{}, None{}, False{}} == Norm.St{o, Norm.MB{P.mkRun(rp)}, Nil{}, P.mkPd(pp), False{}, 0n, Norm.WNone{}, None{}, False{}} : Norm.St}
  {==}

law g_paths:
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  {DR.start_paths(Norm.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}

def g_paths(argv, o, ref, vcfpath, ha):
  %Equal.sym(Maybe<&2, B.Cfg>, B.Args.parse(argv), Some{B.Cfg{o, ref, vcfpath}}, ha) :
    {DR.start_paths(Norm.start.of(_)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  {==}

law g_more:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +rp: P.RunP
  for +pp: P.PdP
  for +hwf: {S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}) == True{} : Bool}
  {DR.more_ok(fa, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}) == True{} : Bool}

def g_more(fa, o, rp, pp, hwf):
  %Equal.sym(Bool, S.WF(fa, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}), True{}, hwf) : {Bool.and(Bool.and(Bool.and(_, True{}), True{}), True{}) == True{} : Bool}
  {==}

law nolf_pp:
  for +pp: P.PdP
  for +f3: {P.pdtext(pp) == "" : String}
  {P.nolf(P.pdtext(pp)) == True{} : Bool}

def nolf_pp(pp, f3):
  %Equal.sym(String, P.pdtext(pp), "", f3) : {P.nolf(_) == True{} : Bool}
  {==}

law g_rep:
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +cs: List<&2, String>
  for +rp: P.RunP
  for +pp: P.PdP
  for +e3: {P.specRun(rp) == R.start_st() : R.RunSt}
  for +f3: {P.pdtext(pp) == "" : String}
  {S.report(fa, cs, "", Nil{}, S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}

def g_rep(fa, o, cs, rp, pp, e3, f3):
  %Equal.sym(String, P.pdtext(pp), "", f3) :
    {R.finish(L.run.go(B.Text.lines(String.append("", String.append(_, String.concat(cs)))), fa, o, S.pre("", Nil{}, P.specRun(rp)))) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}
  %Equal.sym(R.RunSt, P.specRun(rp), R.start_st(), e3) :
    {R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, S.pre("", Nil{}, _))) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}
  {==}

def StartR() -> Type:
  &p: P.RunP -> ({NR.start() == P.mkRun(p) : NR.Run} & ({PR.RunInv(p) == True{} : Bool} & {P.specRun(p) == R.start_st() : R.RunSt}))

def PdR() -> Type:
  &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd} & ({P.pd_ok(pp) == True{} : Bool} & {P.pdtext(pp) == "" : String}))

def StartG(+fa: List<&2, B.Contig>, +argv: List<&2, String>, +o: B.Opts, +ref: String, +vcfpath: String, +cs: List<&2, String>) -> Type:
  &p: S.StP -> ({DR.start_st(Norm.start(argv)) == S.mkSt(fa, p) : Norm.St}
  & ({DR.start_paths(Norm.start(argv)) == Some{DR.Paths{ref, vcfpath}} : Maybe<&2, DR.Paths>}
  & ({DR.more_ok(fa, p) == True{} : Bool}
  & ({S.report(fa, cs, "", Nil{}, p) == R.finish(L.run.go(B.Text.lines(String.concat(cs)), fa, o, R.start_st())) : R.Report}
  & {S.guard("", Nil{}, p) == True{} : Bool}))))

# Nothing collected: the guard holds.
law guard_nil:
  for +p: S.StP
  {S.guard("", Nil{}, p) == True{} : Bool}

def guard_nil(p):
  match p:
    case S.StP{+o, +md, +src, +pd, +eof, +back, +wp, +asked, +fneed}:
      FR.or_true_r(R.RunSt.inbody(S.smd(md)))

law start_go2:
  for +fa: List<&2, B.Contig>
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +cs: List<&2, String>
  for +rp: P.RunP
  for +pp: P.PdP
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hab: {E.all_bytes(argv) == True{} : Bool}
  for +e1: {NR.start() == P.mkRun(rp) : NR.Run}
  for +hi: {PR.RunInv(rp) == True{} : Bool}
  for +e3: {P.specRun(rp) == R.start_st() : R.RunSt}
  for +f1: {Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd}
  for +hp: {P.pd_ok(pp) == True{} : Bool}
  for +f3: {P.pdtext(pp) == "" : String}
  StartG(fa, argv, o, ref, vcfpath, cs)

def start_go2(fa, argv, o, ref, vcfpath, cs, rp, pp, ha, hab, e1, hi, e3, f1, hp, f3):
  +hwf = x8_start(PR.RunInv(rp), P.pd_ok(pp), P.nolf(P.pdtext(pp)), E.all_bytes(S.opts_args(o)), hi, hp, nolf_pp(pp, f3), AB_args(argv, o, ref, vcfpath, ha, hab))
  (S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}, (g_st(fa, argv, o, ref, vcfpath, rp, pp, ha, e1, f1), (g_paths(argv, o, ref, vcfpath, ha), (g_more(fa, o, rp, pp, hwf), (g_rep(fa, o, cs, rp, pp, e3, f3), guard_nil(S.StP{o, S.MBP{rp}, Nil{}, pp, False{}, 0n, PC.WPNone{}, None{}, False{}}))))))

law start_go:
  for +fa: List<&2, B.Contig>
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hab: {E.all_bytes(argv) == True{} : Bool}
  for rs: &p: P.RunP -> ({NR.start() == P.mkRun(p) : NR.Run} & ({PR.RunInv(p) == True{} : Bool} & {P.specRun(p) == R.start_st() : R.RunSt}))
  for pe: &pp: P.PdP -> ({Norm.PB{BY.empty(0n)} == P.mkPd(pp) : Norm.Pd} & ({P.pd_ok(pp) == True{} : Bool} & {P.pdtext(pp) == "" : String}))
  StartG(fa, argv, o, ref, vcfpath, cs)

def start_go(fa, argv, o, ref, vcfpath, cs, ha, hab, rs, pe):
  (+rp, rs1) = rs
  (+e1, rs2) = rs1
  (hi, e3) = rs2
  (+pp, pe1) = pe
  (+f1, pe2) = pe1
  (hp, f3) = pe2
  start_go2(fa, argv, o, ref, vcfpath, cs, rp, pp, ha, hab, e1, hi, e3, f1, hp, f3)

# start_ok with the command line's bytes assumed.
law start_ok_g:
  for +fa: List<&2, B.Contig>
  for +argv: List<&2, String>
  for +o: B.Opts
  for +ref: String
  for +vcfpath: String
  for +cs: List<&2, String>
  for +ha: {B.Args.parse(argv) == Some{B.Cfg{o, ref, vcfpath}} : Maybe<&2, B.Cfg>}
  for +hab: {E.all_bytes(argv) == True{} : Bool}
  StartG(fa, argv, o, ref, vcfpath, cs)

def start_ok_g(fa, argv, o, ref, vcfpath, cs, ha, hab):
  start_go(fa, argv, o, ref, vcfpath, cs, ha, hab, PR.run_start(), PL.pd_empty())
