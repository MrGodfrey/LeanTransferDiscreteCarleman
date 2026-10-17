# Dashboard 部署与权限

## 建议：GitHub 状态为主，展示可选

状态源位于 `state/progress.json`。`tools/update_dashboard.py` 会校验字段并生成 `docs/data.js`。网页展示已审核的数学状态、里程碑和明确来源的用量统计，不直接调用 Codex 的计费界面。GitHub Actions 只部署 `docs/` 目录；不上传 `paper/` 和仓库私密日志。

**方案 A：ChatGPT Sites（私密首选）**

在 ChatGPT 网页端选择 Work，描述制作一个“研究项目进度 website”，提供 `docs/index.html`、`docs/style.css`、`docs/app.js` 和按需更新的状态数据，要求仅本人访问，先预览再发布。Sites 可托管网站，建立私密版本；符合条件时也可设置 Site 自动任务。**个人 Plus/Pro 用户不能仅凭有 GitHub connector 就假定 Sites 有可供后台定期使用的 GitHub 连接器权限。** 应测试真实同步链路，未打通前使用审查过的状态快照/手工更新。

**方案 B：GitHub Pages（公开状态展示，推荐第一版自动更新）**

在仓库 Settings → Pages → Build and deployment → Source: GitHub Actions。每次推送 `main` 触发 `.github/workflows/dashboard.yml` 生成页面并发布 `docs/`。网页无后端也无访问令牌。GitHub Pages 站点**可能是公开的，即使源仓库私有**，所以只发布无敏感数据的状态，或不启用 Pages。

**方案 C：Vercel / 私有托管（后续）**

需要自动读取私有 GitHub 状态并进行真正的身份验证时，配置受保护的后端服务；访问令牌只能存在服务端 secret 中，且原则上只授予必要权限。除非有授权，不自动部署或修改域名。

## 仪表盘必须展示的内容

- 总体状态与最近更新时刻（包括过期提示）
- M0–M6 各阶段状态、验收内容、具体阻塞
- 已登记与已通过语义审计的核心定理数；条件性成果须单独标注
- 最新 GitHub commit、Lean 版本、CI 最近成功/失败状态、未审核 PR
- 在途 Codex 任务及其日志/PR 链接（由监督者填写）
- 最近若干运行和可复现成果日志
- 官方额度/credits 使用数据，若无法取得，则明确显示“未取得”及来源和最后核查时间
- 是否因额度不足、人工授权或技术阻塞而暂停

## 不允许的隐私和真实性缺陷

- 不公开 unpublished manuscript 或数学证明内部细节，除非用户明确同意公开。
- 不在 HTML、JS、status JSON、GitHub Actions 日志中储存 GitHub PAT、OpenAI cookie、API key、账单截图原件。
- “Lean build passed” 与 “原论文完整形式化”不是同义词。
- 上次更新时间过旧应显示陈旧状态，而非持续假装“正在运行”。

官方参考：
- https://help.openai.com/en/articles/20001339-creating-and-using-chatgpt-sites
- https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site
- https://docs.github.com/en/enterprise-cloud@latest/pages/getting-started-with-github-pages/changing-the-visibility-of-your-github-pages-site
