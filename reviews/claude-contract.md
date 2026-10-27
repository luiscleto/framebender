❯ Next: please review framebender's implementation contract change. Read
  ../framebender/notes/briefs/CONTRACT_REVIEW.md (on its git branch bytes; do
  not switch branches) and do the review it describes. Read-only: do not modify
  any file. End with the full report as your final message.

● Bash(cd /home/luisc/Work/bend-projects/framebender && git branch
      --show-current; git branch -a | head; git show
      bytes:notes/briefs/CONTRACT_REVIEW.md)
  ⎿  Error: Exit code 128
     bytes
     * bytes
       main
       remotes/origin/main
       two-layer
     fatal: path 'notes/briefs/CONTRACT_REVIEW.md' exists on disk, but not in
     'bytes'

● Bash(cd /home/luisc/Work/bend-projects/framebender && cat
      notes/briefs/CONTRACT_REVIEW.md; git status --short | head -20)
  ⎿  You are reviewing a change to framebender's implementation contract. f
     ramebender is a VCF normalizer
     in Bend 2. Its science layer (`LAWS.bend`, `types.bend`, `run.bend`, `
     … +44 lines (ctrl+o to expand)
  ⎿  Shell cwd was reset to /home/luisc/Work/bend-projects/lawful-arrays
  ⎿  Allowed by auto mode classifier

● Bash(cd /home/luisc/Work/bend-projects/framebender && git log --oneline
      main..bytes | head; git diff main --stat; git diff main -- protocol.bend
      MACHINE.bend)
  ⎿  d461fb7 bytes branch: brief for the bytes agent
     0943445 bytes branch: implementation contract on packed buffers (draft
     )
     … +135 lines (ctrl+o to expand)
  ⎿  Shell cwd was reset to /home/luisc/Work/bend-projects/lawful-arrays
  ⎿  Allowed by auto mode classifier

● Bash(cd /home/luisc/Work/bend-projects/framebender && cat -n bytes_enc.bend;
      cat -n test/enc_spot.bend; grep -n "Step\|type St\b\|Begin" norm.bend |
      head -20)
  ⎿       1  import Base
          2  import ../lawful-words/defs.bend as W
          3  import ../lawful-bytes/defs.bend as D
     … +102 lines (ctrl+o to expand)
  ⎿  Shell cwd was reset to /home/luisc/Work/bend-projects/lawful-arrays
  ⎿  Allowed by auto mode classifier

● Bash(cd /home/luisc/Work/bend-projects/framebender && cat -n MACHINE.bend |
      sed -n 1,200p)
  ⎿       1  import Base
          2  import ./types.bend as B
          3  import ./protocol.bend as P
     … +174 lines (ctrl+o to expand)
  ⎿  Shell cwd was reset to /home/luisc/Work/bend-projects/lawful-arrays
  ⎿  Allowed by auto mode classifier

● Reading the contract change; checking whether MACHINE.bend still type-checks
  and how run uses input characters.

● Bash(cd /home/luisc/Work/bend-projects/framebender && (timeout 300 bend
      MACHINE.bend --check-only 2>&1 | head -25); grep -n
      "header\|verbatim\|unchanged\|as is" LAWS…)
  ⎿  SOME PROOFS FAIL
     Error:
     - expected : Data
     … +26 lines (ctrl+o to expand)
  ⎿  Shell cwd was reset to /home/luisc/Work/bend-projects/lawful-arrays
  ⎿  Allowed by auto mode classifier

● Bash(cd /home/luisc/Work/bend-projects/framebender && grep -ln "def
      judge_in.ans" *.bend; sed -n 485,500p LAWS.bend; grep -n
      "Fasta.plain\b\|def Fasta.line" -A3 prot…)
  ⎿  norm_line.bend
         case Nil{}:
           acc
     … +17 lines (ctrl+o to expand)
  ⎿  Allowed by auto mode classifier

● Review: framebender's contract on packed buffers

  Not ACCEPT: the changed law machine has two blockers.
  - Its driver definition now packs input with E.enc.
  - The law still holds for every String and every way of cutting the VCF into
    pieces. For some of those inputs no program can satisfy it, or a program
    built on lawful-bytes can't be proven to.
  - Separately, the contract doesn't type-check yet, and the output buffers
    aren't constrained enough for a C driver.

  What I ran:
  - I read git diff main -- protocol.bend MACHINE.bend, the full files,
    bytes_enc.bend, test/enc_spot.bend, and the parts of LAWS.bend, norm.bend
    and main.bend the contract depends on.
  - bend MACHINE.bend --check-only fails.
  - I stayed on branch bytes, which was already checked out, and didn't modify
    any file. The brief itself is untracked on disk, not committed. io64.c has
    uncommitted changes, which I didn't review.

  (a) Does the law still mean what it did? With these fixes, yes:
  - text maps each byte b to Chr{b}, and every byte in D.view is below 256
    (lawful-bytes' view_bytes). So text(o) determines view(o) exactly.
  - A driver that writes exactly D.view(o) therefore writes exactly run's output
    bytes.
  - Messages and the exit code are unchanged.

  Findings

  1. The law allows characters of 256 or more, and then no program can satisfy
  it (blocker). MACHINE.bend:160–171.
  - law machine holds for every vcf: String and fasta: String, but a buffer can
    only hold bytes.
    - E.enc packs each character code with pack4, which assumes values below
      256: larger values spill into the next byte.
    - E.text(o) only ever produces characters below 256.
  - Example: a VCF whose header line holds Chr{256}.
    - run copies header lines as written (LAWS.bend:490, head), so the expected
      output contains Chr{256}.
    - The program receives enc, where that character became the byte 0 and
      spilled into the next byte. And no output buffer can produce Chr{256}.
    - So the law is false for every program.
  - FASTA letters reach the output too: REF is rewritten from reference letters.
    So the same applies to fasta.
  - The old law fed Strings directly, so it didn't have this problem.
  - Fix: add hypotheses that every character of vcf and fasta is below 256, for
    example with a new E.is_bytes(s). The trusted driver already guarantees
    this, because it reads one Char per byte.

  2. The law allows pieces of more than 2^31 bytes, which buffers can't hold
  (blocker). MACHINE.bend:167, bytes_enc.bend:66–68.
  - The law holds "for every way the VCF is cut into pieces", including cs =
    [vcf] for a 3 GB file.
  - For a piece longer than 2^31, E.depth is 30 or more, so D.ok fails and none
    of lawful-bytes' laws apply. A program built on lawful-bytes can't be proven
    for that cut.
  - At 2^32 or more, U32.from_nat(n) also wraps.
    - Example: a piece of 2^32 + 5 bytes becomes Bytes{5, …}, and text(enc(c))
      is just the first 5 characters.
  - Fix: add a hypothesis that every piece in cs has at most 2^31 characters. At
    exactly 2^31, depth 29 holds it and the length still fits in a U32. The
    driver chooses the pieces and reads 4 MiB at a time (main.bend:128), so it
    can always keep to this. Say so in the trust-boundary comment.

  3. Output buffers needn't be well formed, so the driver's "write D.view(o)"
  can go wrong (should fix). MACHINE.bend:51–54, trust comment at line 144.
  - text(o) is defined for any Bytes. A proven program could emit o = Bytes{8,
    ALeaf{w}}: its view is 4 bytes, but its length field says 8.
  - A C driver that writes len bytes from the block would read 4 bytes past the
    end of the block.
  - A lopsided tree built by hand has no clear flat layout for the driver to
    read.
  - Fix: make absorb fail (the step yields no result) unless the output is well
    formed. For example, use a computable E.sane(o): the block is perfect at its
    left-spine depth, that depth is at most 29, and len ≤ capacity. The driver
    can then write len bytes from the flat block.

  4. The reference-read size limit isn't in the law (should fix). Trust comment
  at MACHINE.bend:158–159.

  - The law's driver answers a read of any size. Only the real driver refuses "2
    GiB or more".
  - A program that asks for a whole contig longer than 2 GiB satisfies the law,
    but fails when run. Human chr1 at about 250 MB is fine. Axolotl and lungfish
    chromosomes are larger.
  - There is also an off-by-one: enc handles exactly 2^31 letters, but the
    driver refuses 2^31.
  - The program chooses the windows, so this can be a proof obligation for the
    program.
  - Fix: in dstep, track whether any read exceeded the limit, the way reads is
    already counted. Make result answer None unless every Req had upto − from ≤
    2^31. Make the driver's refusal use the same bound.

  5. The contract doesn't type-check, and its output type lives in the program
  (should fix). MACHINE.bend:54.
  - absorb applies E.text to the step's output, but Norm.Step{…, out: String, …}
    is still defined in norm.bend:52, which is program code.
  - bend MACHINE.bend --check-only fails. The first error is in
    norm_line.bend:162 (P.Ans is now Type, but it is used in a Data position).
  - The program's port is a later step. But the type of the output buffer is
    part of the contract, and it is now defined in a file the program's author
    edits.
    protocol.bend plus MACHINE.bend against a stub norm.bend until the real port
    exists.

  6. The driver is required to build exactly enc, where any well-formed buffer
  would do (should fix). bytes_enc.bend:63–68, trust comment at
  MACHINE.bend:141–143.
  - enc is well defined.
    - depth searches with n + 1 steps of fuel, which is enough.
    - The empty text gets one zero word.
    - In C it is: allocate 2^d words, zero them, copy the bytes, set len.
  - Requiring exactly enc costs something, though:
    - It forbids reading straight into one reusable 4 MiB block, since a short
      final piece must get the smallest block that fits.
    - It puts zero padding and the block-size rule into the trusted, untested
      part.
  - The program's proofs only use D.view and D.ok, so a weaker requirement is
    just as provable. The law could say it like this:
    - For the pieces: take the VCF as bs: List<&1, D.Bytes>, with hypotheses
      that each buffer is well formed (E.sane from finding 3) and that the texts
      of bs are cs. dstep.more then feeds bs.
    - For the answers: take an encoder f: String -> D.Bytes, with function
      hypotheses @s: String -> {E.text(f(s)) == s : String} and @s ->
      {E.sane(f(s)) == True{} : Bool}. lawful-words' bit_ext already uses this
      style of hypothesis. truth.of then uses f in place of E.enc.
  - The driver's obligation shrinks to "a well-formed buffer holding exactly
    these bytes".

  7. enc has no laws, and its spot tests miss the interesting bytes (minor).
  bytes_enc.bend, test/enc_spot.bend.
  - Program proofs will need two laws:
    - view_enc: D.view(E.enc(s)) == codes(s), for byte strings of at most 2^31
      characters;
    - enc_ok: D.ok(E.enc(s), E.depth(n)).
  - Their absence is moot if finding 6 is taken.
  - The spot tests cover neither bytes ≥ 128, NUL and CR, nor lengths at block
    boundaries such as 8 and 16. Add them.

  (c) Bytes ≥ 128, NUL and CR: nothing is lost once finding 1's hypothesis is in
  place. text is one Chr{b} per byte, the same as the driver's existing
  bytes_str (main.bend:60). NUL is an ordinary character in both. How CR is
  handled is unchanged: the science layer drops CRs from FASTA letters, and the
  program sees VCF bytes as they are.

  (d) The 2 GiB limit: the driver can always keep to it.
  - Pieces: the driver chooses the piece size. The limit belongs in the law as a
    hypothesis (finding 2).
  - Reads: the program chooses the windows, and the driver can't split one
    answer. The limit belongs in the law as an obligation on the program
    (finding 4).

✻ Churned for 2m 48s · done 9:45 PM

────────────────────────────────────────────────────────────────────────────────
❯ 
────────────────────────────────────────────────────────────────────────────────
  ⏸ plan mode on (shift+tab to cycle)
                                    Update available! Run: mise upgrade claude
