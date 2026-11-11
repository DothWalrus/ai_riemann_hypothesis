# Agent research reports

Save all future substantive agent reports and batch syntheses here. Use names
such as `YYYY-MM-DD-topic-agent.md` and `YYYY-MM-DD-topic-synthesis.md`; add a
batch suffix if needed to avoid overwriting earlier reports.

Each report should include:

- A short explanation in plain language of the question and outcome.
- The exact mathematical statement, hypotheses, and proof attempt or objection.
- Its verification level: kernel-checked, conditional kernel-checked,
  draft/not checked, or not yet formalized. Distinguish numerical evidence from
  mathematical proof, and an independently reviewed argument from a Lean check.
- Relative links to supporting notes, code, Lean source, and build/axiom evidence,
  with replay commands and any failed checks or unresolved assumptions.
- The exact unresolved step and the next concrete test or proof obligation.
- The scope and outcome of independent adversarial review, if performed.

Keep Lean files in `../../formalization/RhCertificates/` and replay evidence in
`../../formalization/evidence/`. Keep proof attempts even when they fail, with a
clear explanation, so later agents do not repeat rejected approaches. Link
useful progress into `../../docs/PROGRESS.md` and keep the open question in
`../../docs/RESEARCH_DIRECTION.md` current.

Do not include credentials, personal session transcripts, quota/account details,
or publisher PDFs. Use relative repository paths and source citations.
