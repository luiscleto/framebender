# Grok, driver review

     The driver matches the machine comment on the normal path:      2:22 PM
     Ask answers stay in order, a uniform .fai slice matches
     truth, VCF and stdout bytes are copied unchanged, notes go
     out through B.Note.render, and usage and failed opens exit 2
     with the comment's text. Four edge cases do not.
     1. Should fix. main.bend:177-180 treats lb == 0 as "no such
     contig". A present zero-length entry is therefore Unknown,
     while truth is Known{0, 0, ""}. Example: FASTA >c\n\r\n,
     samtools line c\t0\t3\t0\t2, record c 1 . A T. The driver
     reports UNKNOWN_CHROM; run reports REF_MISMATCH. Fix: use
     Map.has. If the name is present and the length is 0, return
     Known{0, 0, ""} and do not divide by lb.
     2. Should fix. A header with no sequence lines is kept by
     Fasta.parse and omitted by samtools, so the driver answers
     Unknown and truth answers Known{0, 0, ""}. Example:
     >empty\n>c\nACGT\n and a record on empty (same UNKNOWN_CHROM
     versus REF_MISMATCH split). The .fai has no line to read.
     Fix: state in the machine comment that a contig samtools
     omits is Unknown, not truth.
     3. Should fix. main.bend:79-85 and 163-190 locate bases with
     the .fai formula, then strip CR. A CR before the end of a
     line shifts those offsets, and has_blank does not reject it.
     Example: line AC\rGT (raw ACGT). Req{"c", 3n, 4n} must be T;
     fai_at(3) is the G, so the driver returns G. Fix: if
     String.length(letters(bs)) is not b2 - a2, stop with error:
     unsupported FASTA, exit 2. CRLF still passes, because its CR
     sits in the line terminator.
     4. Should fix. main.bend:189 passes the offset and the byte
     count through U32.from_nat, which wraps at 2³², and
     File.read_at then caps the count at 2³¹−1. A short read is
     still returned as Known. Example: a contig whose .fai offset
     is 5000000000, or one Ask whose span is 3000000000 bytes. The
     slice is not Contig.raw. Fix: reject an offset or a span that
     does not fit in that range with a distinct error, instead of
     returning the wrapped bytes.

