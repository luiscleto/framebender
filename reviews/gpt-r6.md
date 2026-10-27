# GPT, round 6 (rewritten laws)

• I found no concrete contradiction making the laws unsatisfiable. These gaps
  remain:

  1. Fasta.bases / Fasta.name.go (types.bend:488) — should fix.
     Char.is_space includes vertical tab and form feed, whereas the agreed rule
     removes only space, tab, CR and LF. Other characters should reach
     Base.of_fasta and become N. For FASTA >c\nA\x0bC\n, the rewrite produces AC
     instead of ANC; record (3,C,T) consequently becomes REF_MISMATCH.
     Fix: use an explicit predicate for the four agreed whitespace characters in
     both FASTA functions.

  2. Fasta.parse, Fasta.find, truth (types.bend:529) — should fix.
     Unnamed sequence blocks are retained, contrary to M3. For >\nA\n>c\nC\n,
     looking up "" returns [A], and truth supplies a known-contig answer. The
     agreed parser should discard that block and report unknown. Empty CHROM
     being MALFORMED protects ordinary records, but machine reference requests
     are not restricted to those records’ names.
     Fix: discard unnamed blocks during parsing, and filter repeated names as
     specified, so the reference oracle matches the agreed lookup contract.

  3. machine (LAWS.bend:1104) — should fix.
     The law compares only the final accumulated report. A machine can read
     every chunk through EOF, then compute and emit the correct report,
     satisfying every law while violating immediate header emission and stopping
     input consumption at the first fatal record. For example, it may keep
     requesting chunks after receiving a complete header and a REF-mismatching
     record.
     Fix: add a trace or prefix-refinement law enforcing the agreed output,
     reference-request, and input-consumption sequence—not just equality after
     termination.

  4. bound, window_enough, machine (LAWS.bend:1089) — should fix.
     The agreed doubling of retry windows is not enforced. The machine can
     request windows of sizes 1,2,3,…,clen, ignore already-sufficient answers,
     and still finish within bound; its separately correct Norm.judge_in need
     never be used. Also, bound budgets using VCF byte length, not the per-line
     quantity described in its comment.
     Fix: constrain retry requests to the agreed growth/progress rule and
     require processing to continue once sufficient information is available.
     Make the bound’s comment accurately describe its formula.

  5. machine trust boundary / Args.parse (LAWS.bend:1099) — should fix.
     The proof starts with arbitrary Opts and explicitly excludes command-line
     integration. A wrapper can ignore -c e, supply strict=False, and still
     satisfy every listed law. Likewise, Args.parse returns None for -w 0, but
     no law specifies the resulting usage-error output or exit status. This
     expands the agreed trusted driver beyond faithful I/O execution.
     Fix: add a verified entry contract connecting argv, Args.parse, selected
     file paths, machine options, and usage-error results; leave only execution
     of the resulting I/O actions trusted.

