I accept the law change: the (VCF length + 1)² term with `-m` only, `splits(argv)`, the comment's new sentence, and leaving `docs/LAWS.md` as it is. Nothing is a blocker. Three steps of the fit argument in `notes/split.md` are wrong as written, though the conclusion survives them, so they should be fixed before the proof work starts. I ran no `bend` checks; everything was checked by reading the code and the existing budget proofs.

1. **Should fix: the field-count inequality is false** (`notes/split.md:71-72`).
   - A line that is not malformed may have an empty ID, QUAL, FILTER and INFO (`B.Rec.malformed`, `types.bend:401`).
   - Counterexample: `c⇥1⇥⇥A⇥C,G⇥⇥⇥⏎` is 14 bytes and is split, but R + 2k + 13 = 18.
   - Fix: use R + 2k + 9 ≤ n. The argument only needs 2a + R ≤ n and a ≤ n/2, which still hold (7 ≤ 14 here).
   - R ≥ 1 does hold, since `Text.is_letters("")` is False.

2. **Should fix: the existing term is counted twice** (`notes/split.md:76-78`).
   - The proof already spends (V+1)(F+3) in two parts: W ≤ (V+1)(FM+2) and H ≤ (V+1) + AL (`fin` in `proof_b_bud_start.bend`, around line 715).
   - The step "a(2F+6) ≤ L(F+3)" takes the whole of it, including H's (V+1).
   - Fix: charge H's base share to the new term too. The extra is then at most (V+1)²/4 + (V+1) plus the growth in hand-outs.

3. **Should fix: the output step uses a bound the proofs don't have** (`notes/split.md:79-82`).
   - "A record is at most its line + 22 bytes" is neither proven nor used anywhere.
   - `out_len` (`proof_b_budget_run.bend`) allows each record the judge's bound, 21(|line|+1), and counts the output twice on a stop.
   - Fix: redo the step with those constants. It also needs a new lemma: a split record's text is no longer than its line's. `Rec.piece` keeps the fields, takes one ALT, keeps a subset of the INFO and FORMAT values, and recodes GT with no more digits.
   - Hand-outs then grow by at most ((V+1)² + (V+1))/12. The total extra is at most (V+1)²/3 + 13(V+1)/12, which is ≤ (V+1)² whenever the file has a line.
   - The margin is about 3×, not 3.9×.
   - The threads machine's wrapper share (12 per piece, `proof_e_bud_start.bend:21-25`) sits inside H's share and doesn't change with `-m`.

4. **Minor: measure lines the way the proof does** (`notes/split.md:69,77`).
   - Write the argument with n = |text| + 1, as `la_le` does. Then Σn ≤ V+1 and Σn² ≤ (V+1)².
   - This handles a last line without LF directly, and it is why (V+1)² is the natural term.
   - CRLF only adds room. A CR inside a line gives BAD_CR, so the line is not split (a = 1).
   - Pieces that cut a line don't matter: lines come from the joined text, and pieces only enter through the |cs| term.

5. **Minor: when to charge a line's records** (proof plan).
   - Charge them whenever the line is a candidate (`-m`, not malformed, two or more ALTs: the `go` condition in `Rec.parts.if`), times its ALT count, not only when it is actually split.
   - That covers a line under `-c w` that is refused and passes as it came (ALT_DUP, BAD_CR, a record's refusal), and any records begun before the refusal.
   - Records with `*` or symbolic ALTs are overcharged, which does no harm. Symbolic ALTs only make the line longer.

6. **Q2: `splits(argv)` is right.**
   - The machine itself parses with `B.Args.parse` (`norm_seq.bend:170`), so under the law's premise `splits(argv)` equals the parsed `split` option.
   - Every accepted spelling sets it: `-m X` and the glued `-mX`, for X in `-any`, `-both`, `-`. Repeating `-m` keeps it set, because `Sci.multi` never resets it.
   - A bad `-m` value is a usage error, and `launch` is then None whatever the bound is.
   - `-m` as another option's value (`-f -m`, `-o -m`) does not split, and the parser agrees.
   - Keep the condition rather than adding the term always. Without `-m`, law `machine` then stays exactly the approved statement. Adding the term always would loosen every run's guarantee just to save one small definition.
   - Laws `threads`, `output` and `index` are unaffected, because `--threads`, `-o`, `-O` and `-W` never change the split option.

7. **Q3, minor: the comment's sentence is true but could read better.**
   - To match the comment's wording, write "plus (VCF length + 1) squared" instead of "^2".
   - Say "the records of a split line (one per ALT) may each need as many reads as a line".
   - `docs/LAWS.md:130-133` never mentions the bound, so it needn't change.
   - Nothing else is weakened: output, messages and exit codes must still match `run` exactly, and the bound only limits steps and reads.
   - One practical note: `drive` always uses up all its fuel (`MACHINE.bend:91-96`). A future `-m` example in `examples_machine.bend` would therefore cost (V+1)² empty steps in the check, so keep such examples small. There are none today.

8. **Q4: no smaller term is as simple.**
   - No constant multiple of the existing term fits; the notes' own 10-base-contig example shows this.
   - (V+1) × (longest line + 1) is smaller, but it needs a new definition and an argument that is no simpler.
   - c × (V+1)² with c < 1 gains nothing for a bound that exists only for the proof, and needs extra checks for small files.
   - Keep (V+1)².
