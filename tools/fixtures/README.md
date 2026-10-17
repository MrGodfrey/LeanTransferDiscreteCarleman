# Regression fixtures

These are frozen, unstarted inputs from the 2026-10-17 starter kit, used only by
tests. They are not a runtime ledger and must not be updated when proofs or tasks
progress. Tests may assert their original 19 claims, 26 paper results, zero
completed results, and idle state.

The only runtime records are `/state/progress.json` and
`/state/paper_coverage.json`. Separate integration checks validate those records
against the manuscript without requiring an initial progress count or state.
