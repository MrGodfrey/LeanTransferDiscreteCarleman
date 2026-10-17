# Codex × Dot：额度与断点续跑政策

## 实际产品约束（2026-10-17 官方文档）

1. Codex Cloud 的标准云环境没有单独的 VM 收费（官方在当前说明中称 *at launch*）；模型使用仍计入 Codex 的额度/credits。账户实际限额和 reset 以官方 Usage 页为准。
2. Plus / Pro 在适用情况下可购买额外 credits；**订阅包含量优先扣除，之后才使用可用的已购 credits**。已购 credits 不等同于 API credits。若开启自动充值，可能发生额外付款。
3. 额度达到上限的当次 Codex turn **可能继续执行到这一轮结束**，受 fair-use 限制；不能设想每项任务在阈值到达一刻就被强制杀死。
4. 如果并发任务在 credit 余额仍为正时开始，结算时可出现短暂负余额，之后购买可能先抵消该负余额。因此“余额严格不低于 0”不能作为无条件保证。
5. 官方没有保证个人 Pro 订阅会向任意自建网页提供可读取的逐 Codex Cloud 任务精确 token API；不能爬取带 cookie 的私有计费页面、编造 token 消耗或将估计值当作实测。

## 默认预算模式（保守且可修改）

- **不开启自动充值**；没有用户明确同意，不购买 credits，不调用额外的付费 API 或云主机。
- 同一时刻最多 **1 个主证明任务**；只有确有独立需要且账单许可时增加单独审计任务。
- 建议 Dot 每 6 小时检查一次任务状况，每日汇总一次，不在上一次任务仍在执行时重复启动相同任务。
- 初始运行 1–3 个有限范围的 Codex Cloud 任务，记录实测用量、耗时、验证输出；再讨论更高吞吐的运行策略。
- 如果能够从官方渠道得到准确的额度数据，可设用户指定的软阈值（例如已用比例达到 80% 不再启动昂贵任务，90% 进入仅审查/暂停）；**这些百分数是建议的运营阈值，不是用户账户实际限额。** 用户可自行改变。
- 如果无法获得额度数据，应标记 `UNKNOWN`，只开展已授权的有限范围工作；不可假装执行严格的支付上限控制。

## 状态机

- `IDLE`：当前没有任务，待调度。
- `RUNNING`：已有活动任务；优先监督现有任务，不重复派单。
- `PAUSED_LIMIT`：供应商报告额度/速率限制；按实际 reset 或追加额度后再恢复。
- `PAUSED_APPROVAL`：需要用户授权，尤其是付费、发布未发表论文、改变仓库权限。
- `PAUSED_BLOCKER`：数学或技术问题阻塞，写入可复现说明。
- `PAUSED_MANUAL`：用户主动暂停。

恢复时先检查仓库的已合并成果、最新 PR 和 CI 状态，再继续新任务，不依靠未保存的对话记忆推断进度。

## token 用量表的真实性规则

- `tokens_total=null`：官方逐任务用量无法取得；仪表盘显示 **未取得**，不是 **0**。
- `credits_used=null`：未读取到可靠数据；仪表盘显示 **未取得**。
- `usage.source` 必须标记来源（`official_ui_manual`, `agent_api_report`, `cli_status`, 或 `unavailable`），并记录时间。UI 摘录为人工核对记录，不是实时 API 同步。
- Codex Cloud、Dot 深度任务、Sites 创建/编辑可能共享或相互影响有关 agentic usage 限额；不要简单按“一个 Codex 任务 × 固定 token 数”预测费用。
- 若未来迁移至独立 Agents API，可构建独立精确计费 telemetry；**此路径属于另一种计费与部署方案**，不能默认等同于 ChatGPT 订阅 Codex Cloud。

官方：
- https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan
- https://help.openai.com/en/articles/12642688-using-credits-for-flexible-usage-in-chatgpt-personal-plans
- https://learn.chatgpt.com/docs/pricing
