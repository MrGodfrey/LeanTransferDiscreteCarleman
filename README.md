# Lean Transfer Discrete Carleman

本仓库进行长期 Lean 形式化。2026-10-18 起按用户要求在本机 **main** 开发，验证后直接 commit、push；常规阶段无需 PR。根目录是唯一运行版本：
`AGENTS.md`、`paper/`、`state/`、`tools/`、`docs/`、`prompts/`、`governance/`
及 `.github/workflows/` 均在这里。旧 `MarkdownNote/Carleman_Lean_Cloud_StartKit/`
已迁入根目录，不再保留另一套状态。`MarkdownNote/云端意见/` 和论文原件保持不变。

首个核心目标是原文 Theorem 2.1；条件性 Section 5 是中间目标，长期覆盖全部
26 个具名结果。工程辅助引理不计为原文结果完成。协议见 [AGENTS.md](AGENTS.md)
和 [运行约定](governance/PROJECT_OPERATIONS.md)。[原云端启动说明](README_首先阅读.md)保留作历史参考；当前工作流以本机运行约定为准。

## 固定工程与构建

- Lean **4.35.0**，由 `lean-toolchain` 指定。
- mathlib **v4.35.0**，提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。
- `lake-manifest.json` 锁定全部传递依赖；日常恢复不运行 `lake update`。
- 工程目标 `Carleman`；聚合模块导入全部已登记的证明模块。

从仓库根目录执行（需要 Git、curl、tar、zstd、C 编译器、Python 3.12+、Node 22+）：

```bash
bash tools/setup_lean.sh
bash tools/lean_ci.sh
python3 -m unittest discover -s tools -p 'test_*.py'
node --test tools/test_dashboard.js
python3 tools/update_dashboard.py --check
```

setup 使用 `ELAN_HOME`（默认 `~/.elan`），不设置浮动默认工具链；它按已提交的
manifest 恢复 mathlib，并下载当前基础模块的缓存。新模块需要其它 mathlib imports 时，
可传入缓存根，例如 `bash tools/setup_lean.sh Mathlib.Data.ZMod.Basic`；未缓存的依赖仍由
Lake 正常构建。更改工具链或依赖版本需作为明确的代码变更提交。

CI 构建 `lake build Carleman`，检查已解析的 mathlib SHA，并用
`tools/CheckAxioms.lean` 检查 `Carleman` 命名空间全部声明的公理依赖；`sorryAx` 或新增数学公理会导致失败。
正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 允许使用。
新增已完成模块须加入 `Carleman.lean`，重要成果输出对应声明类型和公理依赖。

历史云端激活和恢复步骤见 [governance/ENVIRONMENT.md](governance/ENVIRONMENT.md)。本机继续复用同一固定工具链与构建命令。

## 基础成果与后续目标

`Carleman.sum_sub_perm` 对任意有限索引类型、交换加法群、置换 `σ` 及函数 `f` 证明
`∑ i, (f i - f (σ i)) = 0`。这是周期差分总和为零的代数基础，范围为 **AUXILIARY**；
它被 C001 的周期分部求和复用。

T001/C001 建立共享 `TimeGrid`（`N > 0`、`δt > 0`、`T = N δt`）、全部 `Fin N → H`
周期状态和论文符号的 `dPlus/dMinus`。`pairing_dPlus/pairing_dMinus` 在任意实内积空间的
`δt * ∑ inner ℝ` 配对中证明双向伴随关系。后续已建立实际空间权、弱 Sobolev 范数、重构算子和 Section3 分析；当前接续 Section4 的空间误差与完整 transfer。
验收状态及版本以台账为准，辅助成果不计为原 Theorem 2.1 完成。

工程合并、CI 正/负/修复记录和剩余配置见 [启动交接记录](governance/BOOTSTRAP_ACCEPTANCE.md)。

## 状态、网页与证据

运行状态只有 `state/progress.json` 与 `state/paper_coverage.json`。
`tools/fixtures/` 是冻结测试输入，不是第二套运行状态；实际状态可以新增目标、完成成果和运行任务。
修改状态后运行 `python3 tools/update_dashboard.py`，再运行 `--check`。

GitHub Actions 只生成仓库权限范围内的构建证据和静态网页 artifact；
本次配置移除了 Pages 部署步骤及写权限，任何仓库变量都不会启用 Pages。
未来公开发布需要单独授权并修改 workflow。不增加付费服务；已由监督者保存的私人巡检／摘要调度仅在台账登记，不进入公开展示。

`MarkdownNote/启动包原始清单_SHA256.txt` 保存原始修订包的历史校验值，
不作为后续代码版本的文件校验清单。论文校验值仍见 `paper/SOURCE_MANIFEST.md`。
