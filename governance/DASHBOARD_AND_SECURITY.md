# 进度快照与访问范围

本流程只使用 Dots + Codex Web。默认直接打开 `docs/index.html`，或从私有仓库 Actions 下载 `progress-dashboard` artifact 后打开；artifact 的权限/保留期以实际仓库配置为准。没有独立网站登录或已部署私人网址，不把本地快照称作在线监控。

`state/progress.json` 与 `state/paper_coverage.json` 保存长期事实。生成器逐字段构造前端对象；未知嵌套字段、内部 task URL、私人暂停理由和内部日志均不输出。事件只输出人工筛选的 `public_summary`。可点击证据必须是 HTTPS，且精确列入 `dashboard.approved_urls`；该白名单也是展示授权记录，不能自动批准整个域名。允许字段的文字仍需检查是否适合目标受众。

页面回答：当前目标；哪些原文结果完成；条件性成果和额外前提；阻塞/下一步；最近构建及上一稳定提交与证据；快照时间和任务核实时间。论文文本与 PDF 不进入部署目录。无账户指标。使用 textContent 输出文本，链接不能执行脚本。

`lean-ci.yml` 在 PR 和 main 实际构建，在 always 步骤保存该次结果 artifact；同次运行调用 `dashboard.yml`，检出同一个 github.sha，使用该结果生成快照。成功与失败均保存快照 artifact，失败不抹掉台账中上次成功记录。PR 和 main 都检查私有快照打包，均不部署网站。上传目录 `site-artifact/` 不是隐藏目录，只复制四个允许的页面文件，避免 upload-artifact 默认忽略隐藏目录。没有 GITHUB_TOKEN 回写 push 或 workflow_run，避免触发循环和新旧 main/CI 混拼。状态提交的 SHA 可与其引用的历史证明 SHA 不同。

Dot 后续将 CI artifact 中经核实的事实写入台账（包括最近稳定记录），保留耐久证据，不能只依赖会过期的 artifact。若任务取消或基础设施失败未能上传产物，快照不伪造新结果，旧记录随时间显示待更新，Dot 兜底巡检核实。

本次工程准备明确保持 Pages 关闭：workflow 已移除部署步骤和 Pages 写权限，仓库变量不能启用部署。未来需单独授权并修改 workflow，之后再检查部署和实际访问权限。私有仓库不自动产生私密 Pages；未发表信息不可因默认上传整个 docs 而泄露。仅打包 index.html、style.css、app.js、data.js，不发布 README 或旧预览。网页故障只阻塞展示。

[GitHub Pages 访问控制](https://docs.github.com/en/enterprise-cloud@latest/pages/getting-started-with-github-pages/changing-the-visibility-of-your-github-pages-site)；[workflow 触发规则](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow)。
