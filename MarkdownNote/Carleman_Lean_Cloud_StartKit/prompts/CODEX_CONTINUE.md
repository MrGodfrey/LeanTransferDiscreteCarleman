# Codex Cloud 后续任务模板

根据当前 GitHub 仓库的 `AGENTS.md`、`state/progress.json`、`governance/PROOF_LOG.md` 和最近 PR 的真实状态，自主选择一项最有价值且有明确验证终点的 Lean 证明工作。以原论文 `paper/main.tex`/`paper/paper.pdf` 为数学规格；优先服务于 Section 5 条件性 transfer 与 Sections 3–4 的依赖消去。

做完本轮可验证成果后停止并交付 PR/commit：列出 Lean 声明和原文定位、通过的构建和审计、仍作为假设的数学性质、下一未解依赖；更新进度 JSON。遇到阻碍时不要无限重试，可以转而证明一项必要的更小引理或提交严格说明的 blocker。
