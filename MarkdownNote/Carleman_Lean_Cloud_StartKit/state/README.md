# State protocol

`progress.json` 是唯一机器可读状态源。由执行者/监督者在取得 GitHub CI/commit 等证据之后更新，不由仪表盘推测。

- 更新必须通过 `python3 tools/update_dashboard.py`；该脚本会验证数据约束并输出 `docs/data.js`。
- `milestone.status`：`TODO`, `IN_PROGRESS`, `VERIFIED`, `BLOCKED`。
- `claims.status`：`PLANNED`, `SPECIFIED`, `CONDITIONAL`, `PROVEN`, `AUDITED`。只有 `AUDITED` 且提供 declaration、commit、核查证据的才进入绿色“已审核证明”计数。`PROVEN` 仅表示通过机器构建尚未独立完成数学语义审查。
- `usage` 不得自行推测：未知是 null，不是零；注明来源及观测时间。
- `events` 只记录真实历史，起始为空；不要在初始化时虚构一次 Codex 运行。
- 状态文件必须带 ISO 8601 UTC 时间戳；起始 `updated_at=null`，网页会显示“尚未运行”。
