# Codex Web：维护进度快照

维护已有 `docs/` 静态页面，不引入新托管服务。数据来自 `state/progress.json`、`state/paper_coverage.json` 与同次 CI 结果；使用 `tools/update_dashboard.py` 逐字段投影生成，禁止直接复制整个内部状态。

展示当前目标、原文结果与条件性成果、额外前提、阻塞和下一步、最近构建及稳定提交、允许展示的 PR/CI/审核链接、Lean/mathlib 版本。区分证明成果时间、快照同步时间和监督核实时刻。过期 RUNNING 必须显示“最近记录为运行中，当前状态待更新”，不能仍亮绿灯。

默认本地预览或私有仓库 artifact。仅有明确公开展示授权时启用 Pages；仓库私有不保证 Pages 私密。展示字段和事件 public_summary 必须先筛选；链接须在 dashboard.approved_urls 中逐项批准，内部 task 链接不输出。构建失败也生成快照，保留上一稳定结果。不要添加账户指标或旧的单文件数据副本。

运行状态回归检查、生成同步检查和浏览器预览。网站仅是带时间的快照，未验证的数据连接不称实时监控。页面维护失败不阻塞 Lean 任务。
