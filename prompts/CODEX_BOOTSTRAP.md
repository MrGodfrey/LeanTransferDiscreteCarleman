# Codex Web 首轮：工程、小成果与接续验收

在指定仓库启动长期 Lean 4/mathlib 形式化。读取 `AGENTS.md`、`governance/MATH_SPEC.md`、`governance/PROJECT_OPERATIONS.md` 和 `state/README.md`；论文 `paper/` 保持不变。唯一监督者是 Dot，执行入口是 Codex Web 的已发布云端环境。

自主完成可做的 GitHub/环境配置并记录实际结果。目标仓库、连接或管理权限确实缺少时，指出具体操作和缺失信息；不要把全部配置工作交回用户。将本启动包放在仓库根目录，核对默认分支并相应调整 workflow 的 main。

M0a：建立固定 Lean 4/mathlib 工程，提交明确 release 的 `lean-toolchain`、`lakefile.toml` 或 `lakefile.lean`、锁定 mathlib commit 的 `lake-manifest.json`。建立 Lean 库目标 `Carleman` 与导入成果模块的 `Carleman.lean`。在仓库记录从干净环境恢复的命令，验证 `bash tools/setup_lean.sh` 和 `bash tools/lean_ci.sh`；发布环境后在新任务再次验证工具链与代码基线。

M0b：先写忠实的规格对照、依赖和有限的 M2 桥接接口。完整 Theorem 2.1 的 Lean 类型随空间、范数和算子接口逐步落实，不把巨大类型声明作为首轮开工门槛。不要把占位声明标作成果。

实际证明一个服务于主线的小目标（如周期分部求和或辅助载荷恒等式），而不是只搭空工程。复用 mathlib，仅调查当前缺失依赖。提交 PR，记录声明、论文标签/页码、额外假设、实际 SHA、构建和依赖检查。执行者把结果放进该任务记录或 PR，整体台账由 Dot 整合。

验收 `.github/workflows/lean-ci.yml`：通过正确源码；在测试分支做受控错误改动，确认检查失败；修复后恢复。禁止将故意错误合入主分支。让有管理权限的执行者实际启用选定分支检查；功能不可用时保留真实 CI 与监督者普通合并。保持 Pages 默认关闭。

将已核对成果交给 Dot 按启动授权合并；Dot 创建下一任务，从新的合并提交记录 `base_commit`，实际使用首轮成果，并验证检查/继续该任务的操作。启动完成的标志是一次真实交付加一次接续，不是提示词或环境名称已填好。缺少外部权限时保存当前成果和具体待办，其余独立工作继续。
