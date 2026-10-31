import Base
import ./types.bend as B
import ./protocol.bend as Pr
import ./run.bend as R
import ./LAWS.bend as L
import ./bytes_enc.bend as E
import ./proof_b_defs.bend as P
import ./proof_b_rundefs.bend as PR
import ./proof_b_cachedefs.bend as PC
import ./proof_b_simdefs.bend as S
import ./proof_b_drivedefs.bend as DR
import ./proof_e_defs.bend as SD
import ./proof_e_task.bend as PT
import ./proof_e_wrap_defs.bend as WD
import lawful-bytes@0.1.0.0/defs.bend as D
import lawful-bytes@0.1.0.0/proof_core.bend as C

# Phase E, area E2: a good wrapper state's facts, twice. InvW is a Type (a
# proof of it is used once), but every leaf is an equality (Data) or a
# witness of Data; E1's step and the budget each take a copy.

# An equality, twice.
def eq_dup(-A: Data, +a: A, +b: A, e: {a == b : A}) -> {a == b : A} & {a == b : A}:
  %Equal.sym(A, a, b, e) : {_ == b : A} & {_ == b : A}
  ({==}, {==})

# Two copies of A and of B make two copies of A & B.
def pair2(-A: Type, -B: Type, a: A & A, b: B & B) -> (A & B) & (A & B):
  (a1, a2) = a
  (b1, b2) = b
  ((a1, b1), (a2, b2))

# A fact of Data in front of two copies.
def cons2(-A: Data, -B: Type, +a: A, b: B & B) -> (A & B) & (A & B):
  (b1, b2) = b
  ((a, b1), (a, b2))

# Two facts of Data, twice.
def p2d(-A: Data, -B: Data, +a: A, +b: B) -> (A & B) & (A & B):
  ((a, b), (a, b))

law pcok_k:
  for +c: String
  for +rs: List<&2, Pr.Req>
  for +k: U32
  for +c0: String
  for +l: Nat
  for +X: String
  for +a1: {PT.rs_ok(rs) && PT.two(rs) == True{} : Bool}
  for +a2: {E.is_bytes(c0) == True{} : Bool}
  for +a3: {SD.first_chrom(B.Text.lines(String.append(PT.after(c, k), X))) == Some{c0} : Maybe<&2, String>}
  for +a4: {U32.is_lt((k + 1 : U32), U32.from_nat(String.length(c))) == True{} : Bool}
  for +a: String
  for +a5: {c == String.append(a, String.append("\n", PT.after(c, k))) : String}
  for d: {P.nolf(a) == True{} : Bool} & {P.nolf(a) == True{} : Bool}
  PT.PcOK(PT.Pc{c, rs, True{}, k, c0, l}, X) & PT.PcOK(PT.Pc{c, rs, True{}, k, c0, l}, X)

def pcok_k(c, rs, k, c0, l, X, a1, a2, a3, a4, a, a5, d):
  (d1, d2) = d
  ((a1, (a2, (a3, (a4, (a, (a5, d1)))))), (a1, (a2, (a3, (a4, (a, (a5, d2)))))))

law pcok_dup:
  for +p: PT.Pc
  for +X: String
  for h: PT.PcOK(p, X)
  PT.PcOK(p, X) & PT.PcOK(p, X)

def pcok_dup(p, X, h):
  match p:
    case PT.Pc{+c, +rs, True{}, +k, +c0, +l}:
      (+a1, h1) = h
      (+a2, h2) = h1
      (+a3, h3) = h2
      (+a4, h4) = h3
      (+a, h5) = h4
      (+a5, h6) = h5
      pcok_k(c, rs, k, c0, l, X, a1, a2, a3, a4, a, a5, eq_dup(Bool, P.nolf(a), True{}, h6))
    case PT.Pc{+c, +rs, False{}, +k, +c0, +l}:
      eq_dup(List<&2, Pr.Req>, rs, Nil{}, h)

law pcsok_k:
  for +p: PT.Pc
  for +t: List<&2, PT.Pc>
  for +dcs: List<&2, String>
  for a: PT.PcOK(p, String.concat(List.append(&2, String, PT.texts(t), dcs))) & PT.PcOK(p, String.concat(List.append(&2, String, PT.texts(t), dcs)))
  for b: PT.PcsOK(t, dcs) & PT.PcsOK(t, dcs)
  PT.PcsOK(p <> t, dcs) & PT.PcsOK(p <> t, dcs)

def pcsok_k(p, t, dcs, a, b):
  (a1, a2) = a
  (b1, b2) = b
  ((a1, b1), (a2, b2))

law pcsok_dup:
  for +ps: List<&2, PT.Pc>
  for +dcs: List<&2, String>
  for h: PT.PcsOK(ps, dcs)
  PT.PcsOK(ps, dcs) & PT.PcsOK(ps, dcs)

def pcsok_dup(ps, dcs, h):
  match ps:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+p, +t}:
      (h1, h2) = h
      pcsok_k(p, t, dcs, pcok_dup(p, String.concat(List.append(&2, String, PT.texts(t), dcs)), h1), pcsok_dup(t, dcs, h2))


law tcok_k:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +cs: List<&2, String>
  for +rp: P.RunP
  for +pd: P.PdP
  for +wp: PC.WP
  for +a1: {PR.RunInv(rp) && P.RunP.i(rp) && Bool.not(P.RunP.x(rp)) && P.pd_ok(pd) && P.nolf(P.pdtext(pd)) && PC.wp_ok(fa, wp) && S.mb_win(S.MBP{rp}, wp) == True{} : Bool}
  for +ls: List<&2, B.Line>
  for +a2: {B.Text.lines(String.append(PT.after(c, k), String.concat(cs))) == List.append(&2, B.Line, ls, B.Text.lines(String.append(P.pdtext(pd), String.concat(cs)))) : List<&2, B.Line>}
  for d: {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt} & {P.settle(P.specRun(rp)) == P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))) : R.RunSt}
  PT.TcOK(dfs, fa, o, c, k, c0, l, cs, PT.TcP{rp, pd, wp}) & PT.TcOK(dfs, fa, o, c, k, c0, l, cs, PT.TcP{rp, pd, wp})

def tcok_k(dfs,fa, o, c, k, c0, l, cs, rp, pd, wp, a1, ls, a2, d):
  (d1, d2) = d
  ((a1, (ls, (a2, d1))), (a1, (ls, (a2, d2))))

law tcok_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c: String
  for +k: U32
  for +c0: String
  for +l: Nat
  for +cs: List<&2, String>
  for +x: PT.TcP
  for h: PT.TcOK(dfs, fa, o, c, k, c0, l, cs, x)
  PT.TcOK(dfs, fa, o, c, k, c0, l, cs, x) & PT.TcOK(dfs, fa, o, c, k, c0, l, cs, x)

def tcok_dup(dfs,fa, o, c, k, c0, l, cs, x, h):
  match x:
    case PT.TcP{+rp, +pd, +wp}:
      (+a1, h1) = h
      (+ls, h2) = h1
      (+a2, h3) = h2
      tcok_k(dfs, fa, o, c, k, c0, l, cs, rp, pd, wp, a1, ls, a2, eq_dup(R.RunSt, P.settle(P.specRun(rp)), P.settle(L.run.go(ls, fa, dfs, o, SD.rs0(c0, l))), h3))

law tresok_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +c: String
  for +ok: Bool
  for +k: U32
  for +c0: String
  for +l: Nat
  for +cs: List<&2, String>
  for +r: PT.TResP
  for h: PT.TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r)
  PT.TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r) & PT.TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r)

def tresok_dup(dfs,fa, o, c, ok, k, c0, l, cs, r, h):
  match ok r:
    case _ PT.TDirtyP{}:
      (Unit{}, Unit{})
    case True{} PT.TCleanP{+x}:
      tcok_dup(dfs, fa, o, c, k, c0, l, cs, x, h)
    case False{} PT.TCleanP{+x}:
      Empty.absurd(PT.TResOK(dfs, fa, o, c, False{}, k, c0, l, cs, PT.TCleanP{x}) & PT.TResOK(dfs, fa, o, c, False{}, k, c0, l, cs, PT.TCleanP{x}), h)

law toutok_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +p: PT.Pc
  for +cs: List<&2, String>
  for +x: PT.TOutP
  for h: PT.TOutOK(dfs, fa, o, p, cs, x)
  PT.TOutOK(dfs, fa, o, p, cs, x) & PT.TOutOK(dfs, fa, o, p, cs, x)

def toutok_dup(dfs,fa, o, p, cs, x, h):
  match p x:
    case PT.Pc{+c, +rs, +ok, +k, +c0, +l} PT.TOutP{+len, +t, +d, +r}:
      (+a1, h1) = h
      (+a2, h2) = h1
      cons2({D.ok(C.BT(len, t), d) == True{} : Bool}, {D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>} & PT.TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r), a1,
        cons2({D.view(C.BT(len, t)) == E.codes(c) : List<&2, U32>}, PT.TResOK(dfs, fa, o, c, ok, k, c0, l, cs, r), a2,
          tresok_dup(dfs, fa, o, c, ok, k, c0, l, cs, r, h2)))

law batchok_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +o: B.Opts
  for +ps: List<&2, PT.Pc>
  for +xs: List<&2, PT.TOutP>
  for +dcs: List<&2, String>
  for h: PT.BatchOK(dfs, fa, o, ps, xs, dcs)
  PT.BatchOK(dfs, fa, o, ps, xs, dcs) & PT.BatchOK(dfs, fa, o, ps, xs, dcs)

def batchok_dup(dfs,fa, o, ps, xs, dcs, h):
  match ps xs:
    case Nil{} Nil{}:
      (Unit{}, Unit{})
    case Con{+p, +pt} Con{+x, +xt}:
      (h1, h2) = h
      pair2(PT.TOutOK(dfs, fa, o, p, List.append(&2, String, PT.texts(pt), dcs), x), PT.BatchOK(dfs, fa, o, pt, xt, dcs),
        toutok_dup(dfs, fa, o, p, List.append(&2, String, PT.texts(pt), dcs), x, h1), batchok_dup(dfs, fa, o, pt, xt, dcs, h2))
    case Nil{} Con{+x, +xt}:
      Empty.absurd(PT.BatchOK(dfs, fa, o, Nil{}, x <> xt, dcs) & PT.BatchOK(dfs, fa, o, Nil{}, x <> xt, dcs), h)
    case Con{+p, +pt} Nil{}:
      Empty.absurd(PT.BatchOK(dfs, fa, o, p <> pt, Nil{}, dcs) & PT.BatchOK(dfs, fa, o, p <> pt, Nil{}, dcs), h)

law eofok_dup:
  for +e: Bool
  for +ef: Bool
  for +cs: List<&2, String>
  for h: WD.EofOK(e, ef, cs)
  WD.EofOK(e, ef, cs) & WD.EofOK(e, ef, cs)

def eofok_dup(e, ef, cs, h):
  match e:
    case True{}:
      (+a, h1) = h
      cons2({ef == True{} : Bool}, {cs == Nil{} : List<&2, String>}, a, eq_dup(List<&2, String>, cs, Nil{}, h1))
    case False{}:
      eq_dup(Bool, ef, False{}, h)

law qnext_dup:
  for +fa: List<&2, B.Contig>
  for +p: S.StP
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.QNext(fa, p, nx, ef)
  WD.QNext(fa, p, nx, ef) & WD.QNext(fa, p, nx, ef)

def qnext_dup(fa, p, nx, ef, h):
  match nx:
    case Pr.More{}:
      (+a, h1) = h
      cons2({DR.more_ok(fa, p) == True{} : Bool}, {ef == False{} : Bool}, a, eq_dup(Bool, ef, False{}, h1))
    case Pr.Ask{+rs}:
      (+a1, h1) = h
      (+a2, h2) = h1
      (+a3, h3) = h2
      (+a4, h4) = h3
      (+a5, h5) = h4
      cons2({S.WF(fa, p) == True{} : Bool}, ({E.reqs_ok(rs) == True{} : Bool}) & (({rs == S.rq(rs) : List<&2, Pr.Req>}) & (({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}) & (({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}) & ({S.StP.eof(p) == ef : Bool})))), a1,
        cons2(({E.reqs_ok(rs) == True{} : Bool}), ({rs == S.rq(rs) : List<&2, Pr.Req>}) & (({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}) & (({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}) & ({S.StP.eof(p) == ef : Bool}))), a2,
          cons2(({rs == S.rq(rs) : List<&2, Pr.Req>}), ({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}) & (({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}) & ({S.StP.eof(p) == ef : Bool})), a3,
            cons2(({S.mb_reqs(S.StP.md(p), rs) == True{} : Bool}), ({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}) & ({S.StP.eof(p) == ef : Bool}), a4, cons2(({S.StP.asked(p) == S.asked_of(rs) : Maybe<&2, List<&2, Pr.Req>>}), ({S.StP.eof(p) == ef : Bool}), a5, eq_dup(Bool, S.StP.eof(p), ef, h5))))))
    case Pr.Finish{+c}:
      Empty.absurd(WD.QNext(fa, p, Pr.Finish{c}, ef) & WD.QNext(fa, p, Pr.Finish{c}, ef), h)

law phase_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +cs: List<&2, String>
  for +p: S.StP
  for +b: WD.BatP
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.PhaseOK(dfs, fa, cs, p, b, nx, ef)
  WD.PhaseOK(dfs, fa, cs, p, b, nx, ef) & WD.PhaseOK(dfs, fa, cs, p, b, nx, ef)

def phase_dup(dfs,fa, cs, p, b, nx, ef, h):
  match b:
    case WD.BNoneP{}:
      qnext_dup(fa, p, nx, ef, h)
    case WD.BColP{+hs, +k}:
      (+a0, h0) = h
      (+a1, h1) = h0
      (+a2, h2) = h1
      (+a3, h3) = h2
      (+a4, h4) = h3
      cons2({S.StP.dfs(p) == dfs : B.Defs}, {nx == Pr.More{} : Pr.Next} & ({DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({ef == False{} : Bool} & {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}))), a0,
  cons2({nx == Pr.More{} : Pr.Next}, {DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({ef == False{} : Bool} & {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool})), a1,
        cons2({DR.more_ok(fa, p) == True{} : Bool}, {S.stopped(S.StP.md(p)) == False{} : Bool} & ({ef == False{} : Bool} & {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}), a2,
          cons2({S.stopped(S.StP.md(p)) == False{} : Bool}, {ef == False{} : Bool} & {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}, a3,
            cons2({ef == False{} : Bool}, {Nat.is_eq(k, List.length(&2, String, hs)) == True{} : Bool}, a4, eq_dup(Bool, Nat.is_eq(k, List.length(&2, String, hs)), True{}, h4))))))
    case WD.BAskP{+ps, +e}:
      (+a0, h0) = h
      (+a1, h1) = h0
      (+a2, h2) = h1
      (+a3, h3) = h2
      (+a4, h4) = h3
      (h5, h6) = h4
      cons2({S.StP.dfs(p) == dfs : B.Defs}, {nx == Pr.Ask{PT.reqs_of(ps)} : Pr.Next} & ({DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & (PT.PcsOK(ps, cs) & WD.EofOK(e, ef, cs))))), a0,
  cons2({nx == Pr.Ask{PT.reqs_of(ps)} : Pr.Next}, {DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & (PT.PcsOK(ps, cs) & WD.EofOK(e, ef, cs)))), a1,
        cons2({DR.more_ok(fa, p) == True{} : Bool}, {S.stopped(S.StP.md(p)) == False{} : Bool} & ({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & (PT.PcsOK(ps, cs) & WD.EofOK(e, ef, cs))), a2,
          cons2({S.stopped(S.StP.md(p)) == False{} : Bool}, {E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool} & (PT.PcsOK(ps, cs) & WD.EofOK(e, ef, cs)), a3,
            cons2({E.reqs_ok(PT.reqs_of(ps)) == True{} : Bool}, (PT.PcsOK(ps, cs) & WD.EofOK(e, ef, cs)), a4,
              pair2(PT.PcsOK(ps, cs), WD.EofOK(e, ef, cs), pcsok_dup(ps, cs, h5), eofok_dup(e, ef, cs, h6)))))))
    case WD.BCombP{+ps, +xs, +e, False{}}:
      (+a1, h1) = h
      (+a2, h2) = h1
      (+a3, h3) = h2
      (h4, h5) = h3
      (h6, h7) = h5
      cons2({nx == Pr.Ask{Nil{}} : Pr.Next}, {DR.more_ok(fa, p) == True{} : Bool} & ({S.stopped(S.StP.md(p)) == False{} : Bool} & (PT.PcsOK(ps, cs) & ((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs)))), a1,
        cons2({DR.more_ok(fa, p) == True{} : Bool}, {S.stopped(S.StP.md(p)) == False{} : Bool} & (PT.PcsOK(ps, cs) & ((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs))), a2,
          cons2({S.stopped(S.StP.md(p)) == False{} : Bool}, (PT.PcsOK(ps, cs) & ((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs))), a3,
            pair2(PT.PcsOK(ps, cs), (PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs), pcsok_dup(ps, cs, h4),
              pair2((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)), WD.EofOK(e, ef, cs), batchok_dup(dfs, fa, S.StP.o(p), ps, xs, cs, h6), eofok_dup(e, ef, cs, h7))))))
    case WD.BCombP{+ps, +xs, +e, True{}}:
      (h1, h2) = h
      (+a2, h3) = h2
      (h4, h5) = h3
      (h6, h7) = h5
      pair2(WD.QNext(fa, p, nx, False{}), {WD.next_is_more(nx) == False{} : Bool} & (PT.PcsOK(ps, cs) & ((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs))), qnext_dup(fa, p, nx, False{}, h1),
        cons2({WD.next_is_more(nx) == False{} : Bool}, (PT.PcsOK(ps, cs) & ((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs))), a2,
          pair2(PT.PcsOK(ps, cs), (PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)) & WD.EofOK(e, ef, cs), pcsok_dup(ps, cs, h4),
            pair2((PT.BatchOK(dfs, fa, S.StP.o(p), ps, xs, cs)), WD.EofOK(e, ef, cs), batchok_dup(dfs, fa, S.StP.o(p), ps, xs, cs, h6), eofok_dup(e, ef, cs, h7)))))

def eofd_dup(+e: Bool, +d: B.Defs, +dfs: B.Defs, h: WD.EofD(e, d, dfs)) -> WD.EofD(e, d, dfs) & WD.EofD(e, d, dfs):
  match e:
    case True{}:
      (Unit{}, Unit{})
    case False{}:
      eq_dup(B.Defs, d, dfs, h)

law inv_dup:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef)
  WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef)

def inv_dup(dfs,fa, T, cs, O, N, x, nx, ef, h):
  match x:
    case WD.WPic{+p, +b}:
      (h0, hh) = h
      (+a1, h1) = hh
      (+a2, h2) = h1
      (+a3, h3) = h2
      pair2(WD.EofD(S.StP.eof(p), S.DEFS(p, List.append(&2, String, WD.held(b), cs)), dfs), {E.all_bytes(WD.held(b)) && E.pieces_ok(WD.held(b)) == True{} : Bool} & ({S.guard(O, N, p) == True{} : Bool} & ({WD.wreport(fa, cs, O, N, WD.WPic{p, b}) == T : R.Report} & (WD.PhaseOK(dfs, fa, cs, p, b, nx, ef)))),
        eofd_dup(S.StP.eof(p), S.DEFS(p, List.append(&2, String, WD.held(b), cs)), dfs, h0),
      cons2({E.all_bytes(WD.held(b)) && E.pieces_ok(WD.held(b)) == True{} : Bool}, {S.guard(O, N, p) == True{} : Bool} & ({WD.wreport(fa, cs, O, N, WD.WPic{p, b}) == T : R.Report} & (WD.PhaseOK(dfs, fa, cs, p, b, nx, ef))), a1,
        cons2({S.guard(O, N, p) == True{} : Bool}, {WD.wreport(fa, cs, O, N, WD.WPic{p, b}) == T : R.Report} & (WD.PhaseOK(dfs, fa, cs, p, b, nx, ef)), a2,
          cons2({WD.wreport(fa, cs, O, N, WD.WPic{p, b}) == T : R.Report}, (WD.PhaseOK(dfs, fa, cs, p, b, nx, ef)), a3, phase_dup(dfs, fa, cs, p, b, nx, ef, h3)))))

law inv_dup3.k:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +nx: Pr.Next
  for +ef: Bool
  for d: WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef)
  WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & (WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef))

def inv_dup3.k(dfs,fa, T, cs, O, N, x, nx, ef, d):
  (a, b) = d
  (a, inv_dup(dfs, fa, T, cs, O, N, x, nx, ef, b))

law inv_dup3:
  for +dfs: B.Defs
  for +fa: List<&2, B.Contig>
  for +T: R.Report
  for +cs: List<&2, String>
  for +O: String
  for +N: List<&2, B.Note>
  for +x: WD.WPic
  for +nx: Pr.Next
  for +ef: Bool
  for h: WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef)
  WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & (WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef) & WD.InvW(dfs, fa, T, cs, O, N, x, nx, ef))

def inv_dup3(dfs,fa, T, cs, O, N, x, nx, ef, h):
  inv_dup3.k(dfs, fa, T, cs, O, N, x, nx, ef, inv_dup(dfs, fa, T, cs, O, N, x, nx, ef, h))
