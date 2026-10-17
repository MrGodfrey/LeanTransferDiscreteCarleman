# Lean Transfer 长期形式化：云端启动包（2026-10-17）

## 先看这段

这是**项目启动包**，不是形式化已经完成、GitHub 仓库已经建立或 Codex/Dot 任务已经启动的证明。论文源文件与原 PDF 均按上传内容复制；可视化网页已经预制但未在线发布。所有初始数学进度为未启动、额度数据为未知，故不会伪造已证明定理或者 token 消耗。

目标论文：Qi Lü、Yu Wang, *From Continuous to Fully Discrete Carleman Estimates: A Transfer Principle for Parabolic Schemes*，44 页。优先 Theorem 2.1，先形式化 Section 5 的条件性 transfer，再补 Theorem 4.2 的分析依赖，最后完成原定理和应用。

## 现在怎么启动（推荐）

1. 在 GitHub 创建一个仓库，例如 `lean-carleman-transfer`。如果论文还未公开，建议先设为 private。把**此启动包的文件作为仓库根目录内容**上传（不要只上传 ZIP）。根目录有 `AGENTS.md`，Codex 将能够读取项目指令。
2. 在 Codex 的 Cloud 环境管理页面选择这个仓库，安装并固定 Lean 4/mathlib，完成测试后 **Publish environment**。由于 Lean 形式化尚未建立，首次应允许云端配置阶段建立 `lakefile.toml` / `lakefile.lean`、`lean-toolchain` 和 `lake-manifest.json`。
3. 在 Codex Cloud 创建第一项任务，把 `prompts/CODEX_BOOTSTRAP.md` 的全文作为启动指令。目标是 M0 规格检查与工程搭建，**不是立刻声称 Theorem 2.1 已经证明**。
4. 把 `prompts/DOT_SUPERVISOR.md` 发给你的 Dot，并提供仓库地址、已发布的 Codex Cloud 环境名称。建议按 6 小时检查一次在途任务，每天发送一次中文总结。Dot 已确认可在已建立的 Codex Cloud 环境中发起云端任务，但此启动包本身不会创建这些任务。
5. 首选使用 GitHub Pages 的 GitHub Actions 模式部署 `docs/`：进入仓库 Settings → Pages → Build and deployment → GitHub Actions。仓库更新可触发网页更新。**注意 GitHub Pages 默认可能是公开的，即使仓库本身是 private。** 如果涉及未发表研究或私有用量，不要公开部署；可先在本地预览，或者在 ChatGPT Work 中用 Sites 建立仅本人可见的展示界面。
6. 查看项目状态优先以 `state/progress.json` 和每次通过校验的 GitHub commit/PR 为依据；仪表盘只是可视化，不是数学证明的认证机构。

## 包内重点文件

- `paper/main.tex`，`paper/paper.pdf`：用户上传论文的逐字节副本。
- `AGENTS.md`：Codex 长期通用指令（英语，精简且强调数学忠实性）。
- `prompts/CODEX_BOOTSTRAP.md`，`prompts/DOT_SUPERVISOR.md`：可直接粘贴的两份初始提示词。
- `governance/MATH_SPEC.md`，`governance/MILESTONES.md`：主定理规格、证明依赖与分阶段里程碑。
- `governance/USAGE_POLICY.md`：额度、暂停与恢复协议。
- `governance/EXTERNAL_LIBRARIES.md`：已找到的 Lean 公开资源；导入兼容性还未验证。
- `governance/SITES_AND_SECURITY.md`：ChatGPT Sites、GitHub Pages 的实现边界及隐私注意事项。
- `state/progress.json`：完整、机器可读的项目状态；起始状态为 0。
- `docs/index.html`：无需 npm、不依赖 CDN 的交互式仪表盘。
- `tools/update_dashboard.py`：校验项目状态，生成供网页读取的经过筛选的数据。
- `.github/workflows/dashboard.yml`：自动将静态网页发布到 GitHub Pages（仅在启用 GitHub Actions 页面后）。

## 本地看网页

直接用浏览器打开 `docs/index.html`；网页数据由旁边的 `docs/data.js` 提供，无需启动服务器。也可以在仓库根目录运行：

```bash
python3 tools/update_dashboard.py
python3 -m http.server 8000 -d docs
```

然后访问 http://localhost:8000 。本地预览不连接 Codex、GitHub 计费或 Dot。

## 论文 TeX 说明

上传的单一 `.tex` 文件引用外部 `draft.cls`、`references.bib`、`siam-paper-no.bst` 和 `images/revision/*.pdf`，这些依赖**不在上传附件中**。因此原始 TeX 作为论文语义规格可直接使用，但目前不能保证单独编译。PDF 已完整附带，不需要重新生成。参见 `paper/SOURCE_MANIFEST.md`。

## 重要产品文档（核实日期 2026-10-17）

- Codex Cloud 环境： https://learn.chatgpt.com/docs/environments/cloud-environments
- Dot 与 Codex Cloud： https://help.openai.com/en/articles/20001530-getting-started-with-your-dot
- ChatGPT Sites： https://help.openai.com/en/articles/20001339-creating-and-using-chatgpt-sites
- Codex 用量及耗尽行为： https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan
- 个人计划 credits： https://help.openai.com/en/articles/12642688-using-credits-for-flexible-usage-in-chatgpt-personal-plans
- GitHub Pages 安全： https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site
