# GPT, round 7

• 1. Q1 — AGREE. Fasta.ws now matches exactly space, tab and CR; VT and FF
     remain available for conversion to N.

  2. Q2 — AGREE. Fasta.keep removes unnamed and repeated contigs, including
     their sequence blocks.

  3. Q3 — AGREE. The EOF flag prevents repeated EOF delivery; requesting more
     input afterward cannot satisfy machine.

  4. Q4 — DISAGREE — should fix. Moving nucleotide conversion into the proven
     core is correct, but the reference-reader contract remains inconsistent.
     Contig.raw removes spaces and tabs as well as line breaks; the trusted
     reader is described as removing only line breaks.

     For FASTA >c\nA C\n, the oracle’s sequence is "AC", and (2,C,T) matches.
     Copying the physical sequence while removing only its newline produces "A
     C"; converting that string gives ANC, changing coordinates and potentially
     producing REF_MISMATCH.

     Change: explicitly require reference reads to return slices of Contig.raw,
     skipping exactly space/tab/CR/LF and translating logical base offsets
     accordingly. Keep nucleotide conversion in the proven core. Add a
     whitespace-containing reference-fetch example, not just a parser example.

  5. Q5 — AGREE. The revised machine binds accepted argv to paths and behavior;
     usage constrains rejected argv, with rendering and exit handling explicitly
     assigned to the trusted driver.

  6. Q6 — AGREE. The run now retains the previous emitted item, and UNSORTED
     diagnostics identify that record correctly.

  7. Q7 — AGREE. The outcome predicates and range comments now agree; the bound
     is identified as a proof budget.

  8. Q8 — AGREE. Explicitly limiting the proof to final results for finite
     inputs is an acceptable scope choice; streaming responsiveness remains
     unproved.

  9. Q9 — AGREE. Sufficiency and termination remain constrained; window-growth
     efficiency can be a separately benchmarked implementation property.

  10. Q10 — AGREE. Rewriting the driver is an implementation follow-up; approval
     of these laws does not establish conformance of the current CLI.

  NEW — should fix: the mismatch between whitespace-stripped reference
  coordinates and the stated raw-fetch contract, described under Q4. I found no
  additional new blocker or should-fix problem.

