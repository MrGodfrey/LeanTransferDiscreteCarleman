# Project agent instructions

Use **Dots + Codex Web**. One Dot supervises; Codex Web tasks in the published cloud environment implement and review bounded work. GitHub stores durable results and CI evidence.

The first core delivery is the faithful Theorem 2.1 in `paper/main.tex`. Conditional Section 5 transfer is intermediate: expose every bridge assumption in `governance/MATH_SPEC.md`, then discharge Sections 3–4 dependencies. The long-term target includes downstream results and all named results in `state/paper_coverage.json`, not merely the 19 initial work items.

Read the relevant canonical files: `governance/MATH_SPEC.md` for mathematical interfaces; `governance/PROJECT_OPERATIONS.md` for task continuation, merge and pause rules; `state/README.md` for evidence/status; `governance/MILESTONES.md` and `governance/PAPER_COVERAGE.md` for scope. Keep this file as a concise pointer rather than duplicating those protocols.

Preserve the manuscript, quantifiers and uniformity (including T), both time directions, full discrete state space and original assumptions. Do not silently weaken a goal. Conditional results retain their mathematical scope after review. A scalar absorption helper is not Section 5 formalization.

Pin Lean and mathlib. Reuse shared periodic sequence, norm, reconstruction and error interfaces. Interface improvements may be made autonomously with affected callers updated in the same PR. Search mathlib first; validate only needed external declarations before adopting dependencies.

Each task records its actual branch and base_commit. Continue the same task/branch for unmerged work or corrections; start new work from a verified merged baseline. Executors deliver a PR and a compact result record; the supervisor merges evidence into the canonical task ledger. Do not have several executors overwrite overall progress.

Build the relevant declarations. For paper-level results and major interfaces, review the statement, quantifiers, extra hypotheses and dependency axioms at the same declaration version. Completed results may not depend on sorry or unjustified mathematical axioms. Interpret normal foundational axioms correctly. `Carleman.lean` must import every announced completed module; merge checks build this target. Incremental development does not require rebuilding all dependencies or replaying the entire kernel after each helper.

Work autonomously within the activated startup agreement. Save useful checkpoints and precise blockers, change strategy after repeated failures, and continue independent goals. Record results once in PR/ledger; keep the proof log as an index. Never infer mathematical completion from dashboard validation or fabricate CI success. Follow the four operational spending rules in PROJECT_OPERATIONS.
