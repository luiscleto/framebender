# Grok 4.7 (standing in for Gemini), draft-3 review

First answer (partly lost from the terminal; recovered parts):

two-layer ~/Work/framebender                       105K / 256K │ [Dashboard]
❯ You are an independent reviewer standing in for a reviewer    1:58 PM
whose quota ran out. Work read-only (do not modify, create
or delete files). Read reviews/DRAFT2_PROMPT.md: it …
▲
result and launch both use bound. An Ask of 10⁹ copies of
Req{"c", 0n, 1n} makes reads > bound, so launch is None.
T2. AGREE. LAWS.bend imports only types, tan and run.
types.bend has no Ans, Req, In or Next. Those live in
protocol.bend. machine and usage live in MACHINE.bend.
T3. AGREE. The headers say the science files stay frozen, and
a faster copy is proved equal to run inside the machine
proof. draft/run.bend already has the lazy take_ready.go and
drop_ready.go. On a buffer sorted by key the ready items are
a prefix, so the flush is the same as a full walk.
T4. DISAGREE. The premise only withdraws the law. It does not
make the result depend only on the files. Fasta.plain.go
rejects every non-> line, including preamble and dropped
contigs, and the comment still stops "when a read holds a
space or tab". Example: "note: draft\n>c\nACGT\n" as in (a).
To agree: use kept sequence lines only, and require the exit-
2 outcome up front.
T5. AGREE. unique plus same_change, stays_valid and
standard_form leave one valid normalized variant.
normalized_valid is the bridge: a Normalized record has
already passed malformed, out_of_scope and checks, and
line_valid is that variant. Rewriting tan.bend would not
change what those laws say.

T6. AGREE. P.Ans is only Unknown and Known. truth.of builds
nothing else.

T7. AGREE. The .fai comment says "has", and run.bend's header
does not mention Norm.judge_in. R.has and R.added that remain
are the real functions.

T8. AGREE. The text is not adopted until ./check.sh passes
and the batched driver is reviewed. That gate is open.

Worked for 11m42s

╭──────────────────────────────────────────────────────────────────────────╮
│ ❯                                                                        │
╰───────────────────────────────────────────────── Grok 4.7 (high) · plan ─╯
Shift+Tab:mode  │  Ctrl+.:shortcuts

Follow-up verdict:

     Yes. I approve draft 3, with adoption still waiting on ./       2:13 PM
     check.sh and the driver review.
     Fasta.plain now follows Fasta.parse: Fasta.flags and
     Fasta.kept_blank use the same header cut, Fasta.name, and
     empty-or-repeated skip as Fasta.go and Fasta.keep. Your three
     examples come out plain, plain, and not plain.
     machine_part.txt is gone. The length comment now says
     String.length(Contig.raw).
     The read-dependent error: unsupported FASTA on a kept contig
     that actually contains a space or tab stays outside the law.
     A full startup scan is not required. Nothing else remains.
