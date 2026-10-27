# Proving framebender's laws: brief for the proof agents

framebender is a VCF normalizer written in Bend 2 (2.0.39) as a "law-driven development" trial: the
laws in `LAWS.bend` are approved and fixed; the job is to prove every one of them. Four agents work in
parallel, one per area, coordinated by the lead (the Claude session that wrote the laws). Read this
file, then `bend guide` (the section "Laws and Proofs" and the syntax reference), then your area below.

## Files

Spec (never edit): `LAWS.bend` (the laws and the definitions they use), `types.bend`, `run.bend`.
Code: `norm_var.bend` (normalizing one variant), `norm_line.bend` (one VCF line through a reference
window), `norm.bend` (the state machine; `Norm.var` and `Norm.judge_in` are wrappers).
Proofs: `proof_var.bend`, `proof_window.bend`, `proof_run.bend`, `proof_machine.bend`; each restates
its laws with every variable reusable (`for +x`). `PROOF.bend` forwards `L.name` to them once a proof
is complete (the lead does that). `proof_base.bend`: shared Bool/Nat/List lemmas (read-only; copy a
lemma into your own file if you need a variant).
Concrete cases: `examples.bend` (`bend examples.bend --check-only`; must keep passing).
Reference proofs in the same style: `../minebender/proof_*.bend` (read-only).

## Rules

- Never edit the spec files, `examples.bend`, `PROOF.bend`, or another area's files.
- You own your proof file (and may add `proof_<area>_*.bend` helper files) and, where noted, one code
  file. You may change your code file to make proofs easier, without changing behaviour: every
  example must still pass, and write down why in your notes. Keep the names the laws use.
- Do not weaken a restated law: same statement as in `LAWS.bend`, only `+` added.
- Run checks under `nice -n 19` with a `timeout`, with `BEND_NO_TELEMETRY=1`, e.g.
  `timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend proof_var.bend --check-only 2>&1 | head -40`.
  A check prints `ALL PROOFS CHECK`, `N TODOs found` (open laws), or the first error.
- No git commits (the lead commits). No network.
- Keep `notes/proof_<area>.md` up to date: what is proven, the plan for the rest, and short bullets
  on where proofs got hard and why (this is research data: be specific, e.g. "rewrite direction",
  "affine hypothesis used twice", "needed a code change: ...").

## Bend proof notes (from the minebender project)

- `%e : G` rewrites with `e : {new == old}`: `G` is the goal with `_` where `old` is; the rest of the
  def proves `G` with `new` there. Use `Equal.sym` to turn an equation around. `Equal.trans`,
  `Equal.cong` are in Base.
- `match` only inspects parameters or pattern-bound variables; a computed value needs a helper def
  that takes it as a parameter. Matches must follow parameter order (match an earlier parameter before
  a later one, or both at once: `match a b:`).
- No mutual recursion, no forward references (define helpers first). Termination: the first argument
  that changes must shrink structurally; put it first.
- Unfilled laws are dead claims: live code (any proof) cannot call an open law. A proof that depends
  on another area's law must wait for it, or take what it needs as a hypothesis argument. Function-
  typed hypotheses are affine (usable once): turn "for every element" facts into a Bool check over
  the whole list plus a lemma that reads it back at one element (equalities are copyable).
- A law's `for x` without `+` cannot be reused in its proof; the restated laws already carry `+`.
- Refuting `{True{} == False{}}` or `{1n+n == 0n}`: rewrite through a `disc` motive that sends one
  constructor to `Empty` and the other to `Unit`, answer `Unit{}` (see `proof_base.bend`).
- `Bool.pick(T, c, a, b)` is "if c then a else b" but evaluates both; to reason about it, case-split
  on `c`.
- `?name` prints the goal at that point; `?TODO` leaves a hole. Errors print expected/observed terms.
- Bare constructors in a let need an annotation: `+v = {B.Var{p, r, a} : B.Var}`.

## Areas

### var (agent `prove-var`): `proof_var.bend`, code `norm_var.bend`

Laws: `same_change`, `stays_valid`, `standard_form`, `normal_unchanged`, `twice`, `one_form`,
`shortest`, and two interface laws for the window area, `var_in_sound` and `var_in_enough`
(at the end of `proof_var.bend`; their statements may be adjusted only with the lead's agreement).
This is the hardest area: uniqueness of Tan et al.'s normal form. A possible route (the lead's
analysis, not checked): a representation of the same haplotypes is a window `[x, y)` of the contig
(0-based, `x = pos - 1`, `y = x + len(ref)`), with each `alt_i` determined by its haplotype `h_i`.
With `P` = the longest common prefix of the contig and all `h_i`, `Q` = the longest common suffix,
`N` = the contig length and `D = max(1, max_i(N - len(h_i) + 1))`, the windows representing the same
change are exactly `0 <= x <= P`, `N - Q <= y <= N`, `y - x >= D`. Then `drop_first`/`drop_last` keep
the change iff the corresponding bound allows it, `shift` by `k` keeps it iff `x - k >= 0` and
`y - k >= N - Q`, so `normalized` holds iff `(x = 0 or y = N - Q)` and `(y - x = D or (x = P and
y = N - Q))`, which has exactly one solution: `y = N - Q`, `x = min(P, y - D)` when `N - Q >= D`,
else `(0, D)`. The code's loops (trim/shift from the right, then trim the left) reach it. You may
also restructure `norm_var.bend` (for example to compute that closed form directly) if it makes the
proofs simpler, as long as the examples pass.

### window (agent `prove-window`): `proof_window.bend`, code `norm_line.bend`

Laws: `window` (a result from any truthful reference answer is the result for the whole reference)
and `window_enough` (a truthful answer that covers what the line needs gives a result). `judge`
(spec, `LAWS.bend`) and `J.judge_in` (code) follow the same classification; the difference is that
`judge_in` reads letters through an answer (`B.Ans`) and normalizes with `V.var_in` on the window,
where `judge` uses the whole contig and `Norm.var`. You will need: `B.Bases.of_fasta` commutes with
taking a slice of the raw letters; the REF check through a window equals the whole-contig check
when covered; and the var area's `var_in_sound` / `var_in_enough` (call them once they are proven;
until then, structure your proof so they are the only missing pieces).

### run (agent `prove-run`): `proof_run.bend`, no code

Laws: `sorted`, `grouped_in`, `no_unsorted`, `twice_run`, all about the spec function `L.run` and the
bookkeeping in `run.bend` (buffer, flush rule, CHROM runs). `twice_run` also needs the var laws
(`normal_unchanged`, `stays_valid`, `standard_form`) and facts about `B.Rec.rebuild` (canonical text,
END consistent): do it last, once the var laws are proven.

### machine (agent `prove-machine`): `proof_machine.bend`, code `norm.bend` (machine part only)

Law: `machine`: driving the state machine (`Norm.start`, `Norm.step`) with any split of the VCF text
into pieces and truthful reference answers gives exactly `L.run(...)` within `L.bound` steps. Key
pieces: the pieces-to-lines invariance (`feed`/`feed_eof` against `B.Text.lines` of the whole text);
each line handled by `R.head_line`/`R.body_line` with `judge_in`'s result, which equals `judge`'s
(the window area's `window` law) once the window grows enough (`window_enough`; the window starts
100 letters back and grows to `2 * back + 1`); out/notes collected per step equal to the spec's
accumulation; the step count stays within `L.bound`. The window laws come from another agent: until
they are proven, keep them as the only missing pieces.

## Reporting

When your area is complete (or you are blocked), say so in your final answer: what is proven, what
is open, any code changes, and the path to your notes file. The lead may send follow-up messages.
