# Proof notes: machine area (`machine`)

## Status (2026-10-27)

- `machine` (`proof_machine.bend`): **proven modulo the window area's two laws**. The only open
  pieces are `window` and `window_enough` in `proof_machine_win.bend` (`?TODO`, the same statements
  as `PW.window` / `PW.window_enough`). Those are themselves proven in `proof_window.bend` modulo
  the var area's `var_in_sound` / `var_in_enough`.
- To finish once `proof_window.bend` fills its two laws: in `proof_machine_win.bend` add
  `import ./proof_window.bend as PW` and make the bodies `PW.window(fa, body, a, r, ht, hr)` and
  `PW.window_enough(fa, body, a, ht, he)`. Checked ahead of time on a scratch copy with PW's laws
  stubbed: it type-checks.
- `bend proof_machine.bend --check-only`: 17 TODOs = 15 open laws of LAWS.bend + the 2 stubs; no
  errors. `PROOF.bend` and `examples.bend` still check (only open-law TODOs).
- Kernel (`--verdict`): it cannot run while a law is open. On a scratch copy with LAWS.bend's law
  blocks removed, `--verdict` gives ALL PROOFS CHECK for every lemma file
  (`proof_machine_nat/lines/frame/fasta/ask.bend`). `proof_machine_sim.bend` uses the window laws,
  so its kernel check waits for them (replacing them by `@unsafe` defs makes `--verdict` stop
  before the kernel).

Files (about 3000 lines):
- `proof_machine_nat.bend`: Nat/String lemmas (le_trans, le_mul_r, mul_add_r, str_assoc, ...).
- `proof_machine_lines.bend`: pieces to lines. `L1`: `Text.lines(x ++ y) == FL(x) ++
  Text.lines(FR(x) ++ y)`; `L2`: `feed.start(split x) == Fed{FL x, FR x}`; `L3`:
  `Text.lines(FR x) == Text.last(FR x)` (feed_eof); `N2`: at most `len + 1` lines. The core is
  `S1`: `split(x ++ y) == pinit(split x) ++ split(plast(split x) ++ y)`.
- `proof_machine_frame.bend`: run.bend only appends to out/notes. `pre(O, N, st)` puts O, N in
  front; `fr_body_line`, `fr_tick`, `fr_head_line` (only with O = ""): they commute with `pre`;
  `ib_*`: inbody is kept; `good(st)`: before #CHROM out and notes are empty.
- `proof_machine_fasta.bend`: `clen_le`: a contig found in a FASTA file has at most as many
  letters as the file has bytes (through Fasta.parse = keep(go(split))).
- `proof_machine_ask.bend`: the driver's answers (`L.truth`) are truthful (`truthful_truth`, needs
  `String.eq` reflexive, down to `Word.cmp` on the bits); an answer from the contig's first letter
  to the end of REF is `L.enough` for every line (`E_main` + `ok_zero`), and an Unknown answer is
  enough when the contig is missing (`ok_none`).
- `proof_machine_sim.bend`: the simulation (below).
- `proof_machine_win.bend`: the window laws as used (stubs).

## How the proof goes

Driver states between two steps are More (machine idle, queue empty, not at EOF), Ask (a line
waits for a read) or Finish. `Good(fa, T, d)` (a Type, by matching d) says, through a dependent
pair `&S`: the machine's bookkeeping is `clear(S)`, the driver's out/notes are S's, `good(S)`,
S not halted, (Ask: S in the body, the asked window is the line's), the pending text satisfies
`Text.lines(pend) == Text.last(pend)`, and `T == R.finish(run.go(lines still to come, S))`.
`need(d)` counts the driver steps left: pieces + 1 (EOF) + 1 (stop) + (lines left) x cost,
`cost = len(FASTA) + 3`, and for a waiting line `asks0` more reads.

- `PL` (pump, induction on the queue): from `clear(S)` with the queue q, pumping ends in a Good
  state with `need <= |q| * cost + rest`. Head lines: `S` and `clear S` are the same term (good S),
  so the machine step is the spec step. Body lines: `LS_body` (spec step = `pre(out S, notes S,
  machine step)`) plus `TL`.
- `TL` (one try_line): with a result, the window law turns it into judge's and pump goes on (the
  induction hypothesis is passed in as a value, so TL serves both PL and the Ask step); without
  one, the Ask state is Good.
- `fin_ok`: finishing (halted, or EOF with an empty queue) gives `R.finish(S)`; NO_HEADER needs
  `good(S)` (nothing written before #CHROM).
- `MS` (More step): EOF uses `L3`/`Text.last`; a chunk uses `L1`/`L2`/`L3`.
- `AS` (Ask step): the answer is truthful; with no result, `askdec` shows the reads left go down
  (window_enough's contrapositive: when the window starts at 0 it would have been enough).
- `STEP`, `Z`, `drive_good` (induction on fuel), `start_ok` (the first state is Good and
  `need <= L.bound`), then `machine`.

## Code change (norm.bend, committed by the lead in c21c3ff)

- `resolve` used to ask again with `back * 2 + 1`. Now `grow(a, back, l)`: the same, except that
  once the answer says the contig is no longer than `back`, the next window starts at the contig's
  first letter (back = POS). Why: L.bound allows about len(FASTA) reads per line. With plain
  doubling a line whose POS is far past the contig's end could need about POS reads, unless one
  proves such a line never asks twice (REF_MISMATCH decided at once), which needs facts about
  judge's internals (malformed => REF nonempty, Allele.read, the REF check's length). With `grow`
  the reads per line are at most clen + 2 whatever the line, and clen <= len(FASTA).
- Behaviour: output unchanged (a window from 0 is what doubling reaches anyway when POS <= clen;
  only Ask values for lines past the contig's end change). `examples.bend` passes; `main.bend`
  builds as before (it just answers what it is asked).

## Where it got hard (research data)

- Rewrite direction: `%e : G` needs `e : {new == old}`, with `old` in the goal. I got it backwards
  about ten times (Equal.sym needed for every lemma stated `{f(x) == simpler}`). The error message
  (expected vs observed) makes it quick to see.
- Match order: a match must follow binder order, including fields bound by an earlier pattern vs
  later parameters: `match q S f` then `match so sns` is refused (so is a field of S, f is later);
  fix by putting the nested patterns into the one joint match. Also `GA` had to match `eof` before
  `wait` (field order of `St`).
- No `match` after a let, and no destructuring let of a computed pair: `drive_good` takes the pair
  `Ok(...)` as a parameter instead of destructuring `STEP(...)`.
- No holes for erased arguments (`Empty.absurd(_, ...)` is refused): impossible branches name their
  goal through small abbreviation defs (`PLG`, `FING`, `ZG`, `ADG`). Where the impossible case is
  a Type that reduces to `Empty` (`Good` of a bad shape), `match g:` with no cases closes it.
- Wildcards in a Type-valued def are fine, but a consumer must split the scrutinee until the def
  reduces (`case _` in the consumer leaves `Good(D{True, _10})` stuck). So `Good` is written as
  nested matches with a known order and STEP/Z enumerate 12 shapes.
- Big goals: keep motives small with abbreviation defs (`PD`, `WD`, `AskG`, `MoreG`, `CD`, `AD`,
  `S1.rhs`); generalize computed scrutinees into lemma parameters with a "remember" equation
  (`S1.k`'s `ec`, `TL`'s `hm`, `askdec.b`'s `hm`), then instantiate with `{==}` at the call.
  Motives may contain several `_` (askdec.b rewrites `find` in three places at once).
- The out/notes "frame": the machine clears out/notes after every line and the driver collects
  them; the spec keeps them in the state. Relating the two needed the frame lemmas through every
  function of run.bend (fr_*), plus the fact that inbody is never reset (ib_*), plus
  `good` (head_line overwrites out, so its frame lemma only holds with nothing written yet).
- Affine hypotheses: the window laws are used once per line and per read, so they cannot be
  hypotheses; they are called (stubbed) laws. TL's `hnone` (a function hypothesis) is used once.
- Fuel: `St.fuel = |queue| + 2` is not syntactically a successor; `pump` only reduces after
  rewriting `add(|q|, 2)` to `2 + |q|` (`add2`) in AS; PL takes any `f` with `1 + |q| <= f`.
- The step bound needed `clen <= len(FASTA)` through Fasta.parse (split/go/keep/find) and
  `#lines <= len(VCF) + 1`; plain bookkeeping, but about 300 lines.
