# Claude, driver review
● The driver is correct for normal inputs, but I found two ways it answers a
  read differently from truth. Both produce wrong output silently, so I would
  fix them before calling main.bend trusted. Everything else matches the comment
  on law machine. I only read files and did not run anything.

  1. Should fix: reads past 4 GiB, or longer than 2 GiB, come back wrong without
     any error (main.bend:189).
     - Offsets go through U32.from_nat, which wraps at 2^32 (U32.inc →
       Word.inc).
     - In the Bend runtime, file_read_start silently caps a read at INT32_MAX
       bytes, and pread is called once with no check of how many bytes came
       back.
     - Inputs that trigger it:
       - A FASTA larger than 4 GiB (plant genomes, pangenome references) with a
         VCF record on a contig whose .fai offset is at or above 2^32. The
         driver reads the bytes at offset mod 2^32 and returns them as Known.
         Unless those bytes happen to contain a blank, the result is a wrong
         REF_MISMATCH or a wrong normalization, exit 0.
       - A stale .fai after the FASTA was rewritten shorter. pread returns fewer
         bytes than asked, and the driver answers Known{n, a, <short slice>}.
     - Fix: in answer.go, stop with exit 2 and a clear message when o1 ≥ 2^32 or
       o1 − o0 > INT32_MAX (or move to a 64-bit read). In answer.k, stop when
       the number of bytes returned is not exactly o1 − o0.
  2. Should fix: an empty contig is answered Unknown (main.bend:198,
     main.bend:220).
     - The driver decides a contig is absent when its line length is 0. That
       covers a contig missing from the .fai, because the default is
       Fai{0,0,0,0}. But samtools writes linebases 0 for a sequence with no
       letters too.
     - Input: FASTA >chrE\n>chr1\nACGT\n and the VCF line chrE 1 . A G.
       - The spec's Fasta.parse has Contig{"chrE", ""}, so truth gives Known{0,
         0, ""} and the line is REF_MISMATCH.
       - The driver answers Unknown, so the line is UNKNOWN_CHROM instead: a
         different message, and a different outcome under -c.
     - Fix: decide presence by whether the name is in the map (e.g. store
       Maybe<Fai> or a sentinel that cannot be a real entry). When the entry has
       line length 0, answer Known{n, min(a, n), ""} without reading, which
       also avoids dividing by zero in fai_at.
  3. Minor: the exit-2 errors don't match what the comment lists.
     - Read errors in the middle of a run print error: cannot read the FASTA
       file, … the VCF file or … the .fai index, not cannot read <path>.
     - A failed write prints error: cannot write, which the comment doesn't
       mention at all.
     - When stdout is a socket, opening /dev/stdout fails and prints error:
       cannot read /dev/stdout.
     - A malformed .fai field silently reads as 0, so the contig is treated as
       unknown.
     - Fix: list every exit-2 message in the machine comment, or make the
       messages follow it. Optionally reject .fai lines that don't parse.

  The rest checks out:
  - Answer order: answers/answers.k/answers.cons run each read before the rest
    and cons it in front, so answers come back in order. An empty Ask gets
    Ref{Nil}.
  - Clipping: a2 = min(a, n) and b2 = min(max(a2, b), n) match truth's min(a, n)
    and take(drop(r, a), b − a) in every case: a > n, b < a, b > n.
  - Line breaks: fai_at handles CRLF line widths, and letters removes LF and CR.
  - Bytes in and out: the VCF goes in one byte per Char with any split, and an
    empty read gives Eof. Stdout and stderr are written byte for byte, and the
    write loop retries partial writes.
  - Messages and exit code: every step's output and notes are written before its
    Finish is handled, and the exit code is the machine's. The usage error
    prints B.usage with exit 2.

