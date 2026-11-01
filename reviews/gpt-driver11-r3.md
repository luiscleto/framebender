ACCEPT.

Decisions 6–8 are implemented. `plan_long_500` now takes **0.050–0.051 s**, versus main’s **0.058–0.062 s** on one thread. All spot-checks matched stdout, stderr and exit status.

The README wording is fair for the stated disk benchmark. My `/dev/null` runs reproduced the gap; `/tmp` is tmpfs here and also retained a small gap, so the reported file-output tie is storage-specific.

No new merge blockers found in `8646585..813b394`.
