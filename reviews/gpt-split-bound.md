1. **Should fix — [notes/split.md:46](/home/luisc/Work/bend-projects/framebender-split/notes/split.md:46).** The proposed `splits` does not compile: Bend rejects matching directly on `B.Args.parse(argv)`. Confirmed on a `/tmp` copy. Add `splits.of(parsed)` that matches its parameter, then call `splits.of(B.Args.parse(argv))`. Its intended semantics correctly cover all accepted spellings, repetitions and usage errors.

2. **Should fix — [notes/split.md:69](/home/luisc/Work/bend-projects/framebender-split/notes/split.md:69).** Two inequalities are false. Empty ID, QUAL, FILTER and INFO fields are accepted: `1\t1\t\tA\tC,G\t\t\t\n` splits but has only 14 bytes, contradicting `R + 2k + 13 ≤ L`. Also, the reader supplies a missing final LF, so `ΣL` can equal `V + 1`. Use `U = V + 1`, `R + 2k + 9 ≤ L`, and `ΣL² ≤ U²`. Preserve the existing output/wrapper reserve by charging
   `a LA ≤ 2a(R+1) + 2a(F+2) ≤ L²/4 + L(F+2)`.
   Recompute the output and margin with `U`. The square remains ample; half the square also fits. CRLF, symbolic ALTs, warning pass-through and piece boundaries introduce no further multiplier.

3. **Should fix — [notes/split.md:29](/home/luisc/Work/bend-projects/framebender-split/notes/split.md:29).** One hundred one-base ALTs necessarily repeat, causing `ALT_DUP` rather than splitting. Replace the example with distinct ALTs and recompute it. For example, REF=`A` repeated 100 times and ALTs `A,C,G,T,N,AA,AC,AG,AT,AN` give a 138-byte LF-terminated line: ten full allowances total `2460`, exceeding `139 × 17 = 2363` for FASTA length 14.

The conditional bound, proposed comment and unchanged `docs/LAWS.md` statement are otherwise sound. Keep the condition to preserve the existing allowance without splitting; output, messages and exit codes remain fixed.
