# Codex Cloud 第一个任务：启动与审计

在本仓库开始一个长期 Lean 4 + mathlib 形式化项目。论文 `paper/main.tex` 和 `paper/paper.pdf` 是数学规格，`AGENTS.md` 及 `governance/MATH_SPEC.md` 定义目标与边界。

本轮请自主完成 M0 中价值最高、可交付的部分：建立可以在云端构建的固定版本 Lean 工程，准确形式化 Theorem 2.1 的规格（允许只创建声明或独立规格文件，不得将未证明结论冒充完整定理），检索并测试最有价值的 mathlib / 公开 Lean 引理，写出可执行的证明依赖图，并选取下一轮最短的 Section 5 proof target。

你可以自主决定目录结构、证明方法和技术顺序；无需机械遵循论文章节。此轮结束时提交可审查结果（commit 或 PR），记录确切 Lean 声明、编译状态、对应论文式号、外部依赖版本、尚缺的引理，并更新 `state/progress.json` 与 `governance/PROOF_LOG.md`。

不要为赶进度而添加改变原主定理含义的新前提。条件性成果需明确其额外前提；无证据不报告 token 数或完成率。
