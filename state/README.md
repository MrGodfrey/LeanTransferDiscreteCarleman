# 状态和证据协议（schema 2）

`progress.json.tasks` 是唯一任务台账；`paper_coverage.json` 单独登记原文结果。执行者在 PR 提交有版本的结果，Dot 核实后整合总状态。CI 产出构建证据，生成器只做格式/关联检查，不查询 GitHub、重放 Lean 或判断数学忠实性。

## 两个证明维度

- `verification_status`：PLANNED、SPECIFIED、BUILT、REVIEWED。
- `scope`：PAPER、CONDITIONAL、AUXILIARY。
- `extra_hypotheses`：相对于所声称原文目标新增、尚未清偿的前提。Theorem 2.1 自带的 (A1)–(A4)、(N1)–(N5) 不列作额外前提。

BUILT/REVIEWED 必须记录 `lean_declarations`、完整 40 位 `declaration_version` 和同 SHA 的成功 `build_evidence`。REVIEWED 另需 `semantic_review`，字段为 `checked_sha`、`declarations`、`result=PASS`、`axiom_check=PASS`、`review_ref`、带时区 `reviewed_at`。每次改变声明或影响它的依赖时重新核对并更新版本，不能沿用旧结论。纯快照提交不必成为声明版本。

只有范围 PAPER、状态 REVIEWED、无额外前提、证据版本一致的**覆盖表结果**才计入原文完成。条件性成果无论核验到哪一步都单列；辅助吸收引理不算 Section 5。将 claim 的成果用于 coverage 前，明确它是否覆盖整个原文结果并同步对应证据；不自动把工作项完成等同于定理完成。26 项结果是当前论文版本的具名结论覆盖，不表示全部证明步骤或实验复现。

## 任务记录模板

`tasks` 初始为空；实际派单后增加记录，不填伪造 task 或 SHA：

```json
{
  "id": "T001", "platform_task_id": null, "task_url": null,
  "title": "周期离散分部求和", "goal_ids": ["C001"],
  "acceptance": ["两种差分符号及周期伴随符合原文，实际构建通过"],
  "dependencies": [], "branch": null, "base_commit": null,
  "status": "TODO", "pr_url": null, "checkpoint_commit": null,
  "merge_commit": null, "lean_declarations": [], "build_evidence": null,
  "blocker": null, "attempts": [], "next_action": "从已核实基线开始"
}
```

状态为 TODO/RUNNING/REVIEW/MERGED/BLOCKED/PAUSED。非 TODO 记录实际分支、完整 base_commit 和平台身份；MERGED 记录实际合并 SHA 和 PR。同任务修正继续原 branch；新目标从合并基线开始。`execution.current_task_id` 指向当前主任务。`schedules` 只录真实保存的调度：id、timezone=Asia/Shanghai、destination、purpose、status；初始为空。

## 构建记录

`verification.latest_build` 和 `last_successful_build` 分开。构建对象包含 status（NOT_RUN/PASS/FAIL/RUNNING/CANCELLED）、checked_sha、ci_url、finished_at、lean_version、mathlib_commit、targets。PASS 需要实际版本和目标；安装失败可记录版本为 null。CI 的 source_head_sha 额外记录 PR HEAD，checked_sha 是实际检出的测试提交（PR 可能是合并测试提交）。监督者核实它与待合并内容的关系，不把两者当成同一个 SHA。

同次 CI 结果在生成快照时覆盖 latest_build，只有 PASS 才更新上次成功记录，不改写源 JSON。Dot 后续将事实同步进台账；状态提交不需预知自身 SHA。生成器检查 SHA 形状不代表确认该提交存在，CI URL 非空也不代表该运行通过；必须访问真实证据。

## 展示和时间

`snapshot.synced_at` 是数据快照同步时刻，`snapshot.source_commit` 是快照读取的源提交；`execution.supervisor_checked_at` 是平台任务状态最后核实时刻；证明记录的构建/审核时间各自独立。初始均为 null。时间须带时区；网页按 Asia/Shanghai 显示。生成本地文件不会假装刚核实了任务；CI 仅刷新快照时间。

展示文字使用登记的 title/blocker/next_action，写入前检查受众。事件使用独立的 `public_summary`；未提供则不展示。展示链接必须 HTTPS 且精确列入 `dashboard.approved_urls`。内部 task URL、平台身份、私人暂停理由、未知嵌套备注不会输出；白名单不会自动批准 URL 或文字中的敏感信息。

运行 `python3 tools/update_dashboard.py` 同步 `docs/data.js` 和覆盖表 Markdown；`--check` 检查同步。CI 用 `--ci-result … --expected-sha … --expected-ci-url …`，拒绝拼接另一次提交或运行的结果。工作流从自身上下文传入精确的仓库/run/attempt URL；只有与同次下载结果完全匹配的该地址临时加入本次展示白名单，源台账和任务核查时间不变。结果文件不能自行批准地址；普通本地投影仍只使用源白名单。此关联检查不替代监督者读取真实运行。构建与页面失败分别报告；不抹掉此前可恢复成果。
