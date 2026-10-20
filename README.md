# Lean Transfer Discrete Carleman

本仓库进行长期 Lean 形式化。2026-10-18 起按用户要求在本机 **main** 开发，验证后直接 commit、push；常规阶段无需 PR。根目录是唯一运行版本：
`AGENTS.md`、`paper/`、`state/`、`tools/`、`docs/`、`prompts/`、`governance/`
及 `.github/workflows/` 均在这里。旧 `MarkdownNote/Carleman_Lean_Cloud_StartKit/`
已迁入根目录，不再保留另一套状态。`MarkdownNote/云端意见/` 和论文原件保持不变。

原稿的 **26 个具名结果已全部完成 Lean 证明及独立数学验收**，包括原始
Theorem 2.1、一般凸多面体完整 P1 与 Cartesian FD 实现、观测与控制，以及
Corollary 7.9 的连续零控制极限。原稿未修改，无新增未清偿前提；辅助及条件性
中间结果不计入 26 项。完整证据见 [最终验收](governance/FINAL_ACCEPTANCE.md)
和 [逐项原文映射](governance/PAPER_COVERAGE.md)。Section 8 实验复现是独立可选交付。
协议见 [AGENTS.md](AGENTS.md)
和 [运行约定](governance/PROJECT_OPERATIONS.md)。[原云端启动说明](README_首先阅读.md)保留作历史参考；当前工作流以本机运行约定为准。

## 固定工程与构建

- Lean **4.35.0**，由 `lean-toolchain` 指定。
- mathlib **v4.35.0**，提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。
- `lake-manifest.json` 锁定全部传递依赖；日常恢复不运行 `lake update`。
- 工程目标 `Carleman`；聚合模块导入全部已登记的证明模块。

从仓库根目录执行（需要 Git、curl、tar、zstd、C 编译器、Python 3.12+、Node 22+）：

```bash
bash tools/setup_lean.sh
lake build Carleman
lake env lean tools/CheckAxioms.lean
```

setup 使用 `ELAN_HOME`（默认 `~/.elan`），不设置浮动默认工具链；它按已提交的
manifest 恢复 mathlib，并下载当前基础模块的缓存。新模块需要其它 mathlib imports 时，
可传入缓存根，例如 `bash tools/setup_lean.sh Mathlib.Data.ZMod.Basic`；未缓存的依赖仍由
Lake 正常构建。更改工具链或依赖版本需作为明确的代码变更提交。

本地验收执行 `lake build Carleman`，核对已解析的 mathlib SHA，并用
`tools/CheckAxioms.lean` 检查 `Carleman` 命名空间全部声明的公理依赖；`sorryAx` 或新增数学公理会导致失败。
正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 允许使用。
最终根目标覆盖全部 1,080 个数学模块，10,681 项声明的递归公理审计通过。
远端 CI 保留作后台复现检查，不是每批验收门槛。新增模块仍须加入 `Carleman.lean`。

历史云端激活和恢复步骤见 [governance/ENVIRONMENT.md](governance/ENVIRONMENT.md)。本机继续复用同一固定工具链与构建命令。

## 主要证明入口

- 原 Theorem 2.1：[OriginalUniform.lean](Carleman/Transfer/OriginalUniform.lean)，`Carleman.OriginalForm.transfer_uniform`。
- 原完整 P1 实现：[FullP1Realization.lean](Carleman/Control/FullP1Realization.lean)。
- 一般凸多面体的连续热 Carleman 估计：[FiniteHalfspaceHeatContinuous.lean](Carleman/Transfer/FiniteHalfspaceHeatContinuous.lean)。
- 原物理观测与控制：[FiniteHalfspaceP1PhysicalControl.lean](Carleman/Control/FiniteHalfspaceP1PhysicalControl.lean)。
- 原过滤观测与控制：[FiniteHalfspaceP1FilteredControl.lean](Carleman/Control/FiniteHalfspaceP1FilteredControl.lean)。
- 原 Corollary 7.9：[FiniteHalfspaceP1NullControlLimits.lean](Carleman/Control/FiniteHalfspaceP1NullControlLimits.lean) 及 [CartesianNullControlLimits.lean](Carleman/Control/CartesianNullControlLimits.lean)。

全部 26 项的声明、固定证明版本和独立报告以唯一台账及其生成的覆盖表为准。
历史工程启动记录保留在 [BOOTSTRAP_ACCEPTANCE.md](governance/BOOTSTRAP_ACCEPTANCE.md)。

## 状态、网页与证据

运行状态只有 `state/progress.json` 与 `state/paper_coverage.json`。
`tools/fixtures/` 是冻结测试输入，不是第二套运行状态；实际状态可以新增目标、完成成果和运行任务。
修改状态后运行 `python3 tools/update_dashboard.py`，再运行 `--check`。

GitHub Actions 只生成仓库权限范围内的构建证据和静态网页 artifact；
本次配置移除了 Pages 部署步骤及写权限，任何仓库变量都不会启用 Pages。
未来公开发布需要单独授权并修改 workflow。不增加付费服务；已由监督者保存的私人巡检／摘要调度仅在台账登记，不进入公开展示。

`MarkdownNote/启动包原始清单_SHA256.txt` 保存原始修订包的历史校验值，
不作为后续代码版本的文件校验清单。论文校验值仍见 `paper/SOURCE_MANIFEST.md`。
