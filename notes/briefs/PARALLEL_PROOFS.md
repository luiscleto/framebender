# Brief: the parallel machine's proofs, one area

You prove one area of the parallel machine (`norm_par.bend`, a wrapper that runs `norm.bend`'s
machine unchanged and handles the VCF in batches). Your coordinator is the phase E agent `fb-par`
(Herdr workspace "fb-par"); it gave you the area name in your prompt.

Read first: `notes/parallel_proofs.md` (the design, your area's section, the rules), then
`notes/parallel.md` ("Step 3: the code, resumed", the argument for the merge), then your area's
statement file. Phase B's proof notes are in `notes/bytes_proofs*.md`; `notes/bytes_proofs_drive.md`,
"Where it got hard", lists Bend pitfalls worth knowing before you start (let-before-match,
`+` on destructured parts, no import cycles, definitions that refuse to unfold).

Rules:
- Every check: `timeout 1800 test/bcheck.sh <file.bend> [--check-only|--verdict]`, never `bend`
  directly. At most two checks run at once across all agents (the script waits for a slot), each
  capped at 4 GB. Never let the checker compute with a big closed Nat (2^28, 2^31, a `Nat.pow`, two
  big literals compared): keep such bounds abstract or go through U32 lemmas
  (`../lawful-words/notes/proof.md`).
- Statements of deliverables (marked `?TODO` in your statement file, or given in your area's
  section) are fixed. Helpers are yours. If a statement is false or misses a hypothesis, write the
  counterexample in your notes and tell the coordinator; do not change it.
- Edit only your area's files; create new ones as `proof_e_<area>_*.bend` (run `ls` first: another
  agent's file may exist). Do not edit `norm*.bend`, `main.bend`, the contract (`protocol.bend`,
  `MACHINE.bend`, `bytes_enc.bend`) or `../lawful-*`.
- No commits, pushes or branch switches. No benchmarks.
- Notes in `notes/parallel_proofs_<area>.md`: status first (what checks, what is open), then what was
  hard. Keep them current.
- When your deliverables check (`--check-only`, then `--verdict` on your statement file), report to
  the coordinator in your last message: files, what checks, anything open.
