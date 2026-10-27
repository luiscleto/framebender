# Gemini, round 6 (rewritten laws)

  No law in LAWS.bend is false (all 14 laws are jointly satisfiable; 0
  blockers). Below are the remaining issues in the rewrite:
  1. dstep.more / machine — Severity: should fix
      • Problem: dstep.more sends B.Eof whenever cs is Nil{} and next is
      B.More, without recording that EOF was already delivered. Because bound
      has spare steps, machine is too weak at EOF: a broken Norm.step that
      answers the first B.Eof with B.More (e.g., queueing the repaired final
      line and waiting for a second Eof{} to flush and finish) satisfies
      every law, yet violates DSt's comment ("then the end of the file") and
      blocks or fails under a real driver that sends Eof{} once or calls
      read() again on stdin/a pipe.
      • Example: On cs = ["#CHROM\tPOS\tID\tREF\tALT\tQUAL\tFILTER\tINFO"]
      (no trailing LF), a machine that returns More{} on Chunk, repairs the
      #CHROM line and returns More{} on the first Eof{}, and emits header +
      Summary + Finish{0n} on the second Eof{} evaluates to Some{run(...)}
      under drive, passing machine while hanging a streaming stdin driver.
      • Fix: Add eof: Bool (initially False{}) to DSt. When next is B.More{}
      and cs is Nil{}, send B.Eof{} with eof = True{} if eof is False{}, and
      otherwise leave DSt unchanged (done = None{}).
  2. Fasta.parse, Fasta.find, Fasta.name, and Fasta.bases — Severity: should
  fix
      • Problem: Two deviations from M3 (responses-3.md:33-38) and from
      types.bend's own comments:
          1. M3 states that a header with an empty name or an already-seen
          name is skipped with its sequence block, and Fasta.find's comment
          claims "an empty name never matches". In code, Fasta.parse retains
          empty-named and duplicate-named contigs, and Fasta.find checks only
          String.eq(n, name)—so "" does match, and truth in machine answers
          B.Ask{"", ...} with Known{...} where .fai (samtools faidx) gives
          Unknown{}.
          2. M3 specifies FASTA delimiters/stripped sequence bytes as space,
          tab, CR, and LF (and Fasta.bases's comment says (space, tab, CR)),
          with any other sequence byte mapped to N (R5). Code uses Char.
          ￺is_space, which also strips vertical tab (0x0B) and form feed
          (0x0C) from sequence lines, shifting downstream coordinates instead
          of mapping them to N (and splitting contig names on 0x0B/0x0C).
      • Example: (1) B.Fasta.find(B.Fasta.parse(">\nACGT\n"), "") returns
      Some{[A{}, C{}, G{}, T{}]} instead of None{}. (2) On >c\nA\x0bGT\n and
      c\t3\t.\tG\tC\t.\t.\t.\n, M3+R5 yields contig ANGT (POS=3 is G,
      NORMALIZED), whereas Fasta.bases strips \x0b to AGT (POS=3 is T,
      REF_MISMATCH).
      • Fix: Replace Char.is_space in Fasta.name.go and Fasta.bases with a
      helper checking only ' ', '\t', and '\r' ('\n' is already split out),
      and skip empty and already-seen contig names in Fasta.go (and/or guard
      Bool.not(String.is_empty(n)) in Fasta.find).
  3. Note.render — Severity: minor
      • Problem: For Stop{Unsorted{}, at, cause}, cause is the arriving line
      whose arrival triggered the flush (types.bend:643-644), not the earlier
      written line that at would appear out of order after, yet Note.render
      renders cause with "\tafter\t". When at != cause this reads backwards,
      and on every sorted-input long-left-move UNSORTED stop (key(x) + w <=
      ￹inpos(x)), the moving record triggers its own flush (at == cause),
       printing "line N after line N".
       • Example: Inrun_unsorted_notee, the stop note is Stop{Unsorted{},
       ￹Some{At{5n, "c", "4"}}, Some{At{5n, "c", "4"}}}, whicNote.renderer
        formats as "error: UNSORTED\tc\t4\tline 5\tafter\tc\t4\tline 5\n".
        • Fix: Replace "\tafter\t" iNote.renderer with "\ton reading\t" or
        "\tflushed at\t".
  4. enough / enough.go — Severity: minor
      • Problem: Two mismatches between enough and its comment:
          1. For Normalized, the comment (LAWS.bend:404-405) says "every base
          from one before the new POS (or the contig's first base) to the end
          of the input REF", omitting the start of the input REF when left-
          trimming moves POS right by ≥ 2 (line 399's Nat.min(Nat.sub(p, 1n),
          ￹Nat.sub(k, 2n)) is right; the comment repeats the old range).
          2. For NoContig, the comment (LAWS.bend:402) says "the answer
          \"unknown\"", whereas line 393 uses is_asked, which also accepts B.
          ￺Known{...} truthful rules Known out inside window_enoughh, so the
          law still holds, but enough standalone disagrees with its comment).
      • Example: (1) On >c\nACG\n and c\t1\t.\tACG\tACT\t.\t.\t. (p = 1, k =
      ￹3), the comment says 1-based [2, 3] while line 399 requires 1-based [1,
       ￹3]. (2) enough(Nil{}, "c\t1\t.\tA\tG\t.\t.\t.", B.Known{4n, 0n, Nil{}})
        evaluates to True{}.
        • Fix: Update lines 404–405's comment to include the input REF start
        (min(POS, max(1, newPOS - 1))), and match only B.Unknown{} in line 393.
  5. Top-of-file law summary comment (LAWS.bend:18) — Severity: minor
      • Problem: Line 18 names the grouping law grouped, whereas line 944
      declares grouped_in (grouped is the helper predicate).
      • Example: # sorted, grouped, no_unsorted, twice_run (LAWS.bend:18) vs
      law grouped_in: (LAWS.bend:944).
      • Fix: Rename grouped to grouped_in in the comment on line 18.

