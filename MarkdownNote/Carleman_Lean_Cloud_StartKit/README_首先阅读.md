# Lean Transfer 长期形式化启动包（2026-10-17 修订）

本流程只使用 **Dots + Codex Web**：一个 Dot 是唯一监督者，Codex Web 中的云端任务承担证明、数学核对、文献调查和工程维护。本文的“云端环境”指 Codex Web 使用的 Codex Cloud 环境，不增加 ChatGPT Work 或 Sites 角色。

这是待启动的工程包，尚未建立 Lean 工程、运行远端 CI、发布环境或启动调度。论文源码与 PDF 保持原样；数学进度均为未启动。已修改与待启动项目见 `CHANGELOG_修改说明.md`。

## 研究目标

论文：Qi Lü、Yu Wang, *From Continuous to Fully Discrete Carleman Estimates: A Transfer Principle for Parabolic Schemes*（44 页）。首个核心交付是 Theorem 2.1：先完成 Section 5 条件性 transfer，明确所有暂用桥接前提，再证明 Sections 3–4 依赖并消去额外前提。原文 (A1)–(A4)、(N1)–(N5) 本来就是该定理的假设。

长期交付包括尺度推论、具体 PDE 与离散格式、观测控制、收敛以及全部具名结论的必要证明依赖。`state/progress.json` 保留原有 19 个初始工作目标；`state/paper_coverage.json` 另列论文全部 26 个具名结果。19/19 或完成 Theorem 2.1 均不等于全文完成。Section 8 数值实验复现另行登记，不计入形式化定理完成数。

## 启动顺序

1. 将本目录内容放在目标 GitHub 仓库**根目录**。启动执行者用已有连接、CLI/API 和权限完成仓库、分支及环境配置；缺少目标地址或登录时才向用户索取。默认保留私有访问，不预设账户管理权限。
2. 在 Codex Web 配置并发布云端环境，按 `prompts/CODEX_BOOTSTRAP.md` 建立固定 Lean/mathlib 工程。提交 `lean-toolchain`、Lake 配置和 `lake-manifest.json`，从干净环境测试仓库内的恢复步骤。缓存不承担成果保存。
3. 把仓库与已发布环境交给 Dot，发送 `prompts/DOT_SUPERVISOR.md`。由 Dot 创建首个证明任务，以便核实它能检查并继续自己创建的任务。已存在的配置任务记录在台账；接管能力不明时先核实，避免重复派单。
4. 实际完成一个服务于主线的小证明，运行 Lean CI，核对声明后按启动约定合并常规 PR；在下一任务中记录新的 `base_commit` 并引用已合并的小成果。这一次交付和一次接续是首轮验收。
5. 若账户支持分支规则，实际启用 `Lean CI / lean` 与 `Lean CI / state-check`（以仓库中真实检查名称为准）。不支持时由 Dot 核对同一提交的检查后普通合并；不以升级套餐为开工条件。写入 AGENTS 不等于已配置 GitHub 设置。
6. 默认在本地或私有仓库的 Actions artifact 查看静态进度快照。只有用户授权公开展示、核对展示内容后，才设置 Pages 来源为 GitHub Actions，并设置仓库变量 `PUBLISH_PROGRESS_PAGES=true`。网页问题不阻塞证明接续。

本次修改启动包并未授权或执行特定远端 PR 的合并。上述持续合并与派单约定在用户将启动提示词交给监督者开始项目时使用。

## 最小启动验收

- 固定工具链真实构建通过；重建环境和一个新任务可复用同样版本。
- 有一个真实 Lean 小成果；`Carleman.lean` 导入成果，`lake build Carleman` 确实覆盖它。
- 在测试分支引入受控类型错误，CI 失败；修正后 CI 恢复。记录三次对应 SHA/链接。
- PR 经必要声明和依赖核对后合并；下一任务从合并基线接续。
- 已审核条件性成果仍单列；前端不含账户数据、内部备注或任务链接。
- 失败构建保留最近稳定提交；陈旧运行记录显示待更新；暂停显示正确。
- Dot 检查和继续任务的能力实际验证。若采用六小时兜底巡检，记录已保存的调度 ID、Asia/Shanghai 时区和通知位置；日摘要不作为继续派单条件。
- 26 项覆盖表与 19 项工作清单分开；初始数学状态不伪造完成。

## 文件入口

- `AGENTS.md`：长期代理指令与规范入口。
- `prompts/`：启动、后续任务、Dot 监督与 Codex Web 仪表盘维护提示词。
- `governance/MATH_SPEC.md`、`MILESTONES.md`、`PAPER_COVERAGE.md`：数学规格、路线和全文覆盖。
- `governance/PROJECT_OPERATIONS.md`：台账、接续、合并、暂停恢复。
- `governance/DASHBOARD_AND_SECURITY.md`：本地快照与可选公开发布。
- `state/README.md`：状态、证据和展示协议；`tools/update_dashboard.py` 只做格式与一致性检查。
- `.github/workflows/lean-ci.yml`：PR/主分支真实 Lean 构建与证据产物。
- `.github/workflows/dashboard.yml`：由同一 CI 调用，使用同一提交及其结果生成快照；公开部署默认关闭。

## 本地检查和预览

```bash
python3 -m unittest discover -s tools -p 'test_*.py'
node --test tools/test_dashboard.js
python3 tools/update_dashboard.py
python3 tools/update_dashboard.py --check
```

随后直接打开 `docs/index.html`。本机 Python 优先用 `/Users/wangyu/miniforge3/envs/codexPython/bin/python`；云端使用其配置中的 Python。独立旧预览已删除，避免发布陈旧数据。

上传的 TeX 缺少 `draft.cls`、参考文献及图片依赖，暂不保证独立编译；PDF 已完整附带，见 `paper/SOURCE_MANIFEST.md`。

## 产品与工作流依据（2026-10-17 核对）

- [Dot 任务与接续](https://learn.chatgpt.com/docs/dots/tasks-and-memory)：可在事先建立的 Codex 云端环境创建任务，检查并继续自己创建的任务。
- [Codex 云端环境](https://learn.chatgpt.com/docs/environments/cloud-environments)：在 Web 配置、发布和复用；已有任务保留各自工作状态，新任务仍需核对分支与提交。
- [Dot 暂停控制](https://learn.chatgpt.com/docs/dots/controls)：监督者、在途任务和调度需分别处理。
- [GitHub 可复用 workflow](https://docs.github.com/en/actions/how-tos/reuse-automations/reuse-workflows) 与 [Pages workflow](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages)：同次运行传递检查结果和快照。

账户可用性、连接和权限以启动时的真实操作结果为准。
