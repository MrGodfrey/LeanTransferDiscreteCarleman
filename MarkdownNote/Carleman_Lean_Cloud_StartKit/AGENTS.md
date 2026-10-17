# Project agent instructions

This repository is a long-running Lean 4/mathlib formalization project for the manuscript in `paper/main.tex` and `paper/paper.pdf`.

**Main goal:** Verify the mathematical content of Theorem 2.1. First formalize a faithful conditional Section 5 transfer theorem with the weighted space-time approximation theorem explicitly assumed; then discharge that auxiliary assumption by formalizing Sections 3 and 4; then formalize Corollaries 2.2–2.3 and downstream applications.

Treat the manuscript as the authoritative specification for mathematical statements, including quantifiers, uniformity of constants, both signs of time differentiation, full discrete state space and the original assumptions. You may redesign proof architecture and generalize helper results; never silently weaken the target or add assumptions and still label it as the original theorem.

Use mathlib first. Search existing reputable formalizations before implementing major infrastructure. Verify license, theorem statement, toolchain compatibility and dependency cost before adopting an external package.

For each completed unit: build with Lean; audit the declaration and its assumptions against the manuscript; check its axioms and proof dependencies; record concrete Lean declaration names, commit SHA and manuscript references. An explicitly stated conditional theorem may be marked *conditional*, not *paper theorem complete*. Development placeholders must never appear in verified release artifacts. Do not use new unjustified axioms or hidden definitions of the conclusion.

Maintain `state/progress.json`, `governance/PROOF_LOG.md` and the dependency map. Work autonomously, submitting small reviewable commits or PRs. If blocked, state the exact missing lemma and switch to the most valuable independent task. Never make unsupported claims of completion or usage metrics. Do not purchase credits or change external billing settings without user approval.

After every coherent work unit, report: what was proven; exact Lean declarations; which manuscript claims were audited; what remains conditional; successful checks; source commit; and the next most valuable step.
