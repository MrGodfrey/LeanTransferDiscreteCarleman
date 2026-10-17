# 工程启动验收与 Dot 交接

工程 PR [#1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/pull/1) 已合并。
实际工程合并基线：`fc466e43e93ce2b8322c9abe6e54b785a04dec27`（`main`）。
本文件在后续交接记录提交中保存；Dot 开始新任务时仍须读取远端 main 的最新完整 SHA，不能把历史验收 SHA 当作自动更新的指针。

仓库：https://github.com/MrGodfrey/LeanTransferDiscreteCarleman 。访问范围保持 private，默认分支为 main。

## 真实 CI 验收

| 验收 | 源码 HEAD | 实际 checkout / checked_sha | CI |
| --- | --- | --- | --- |
| 正确源码：PASS | `5dabcb9775b60b548d5c15da53da26c5d78202b6` | `592c13850de7de513c579f069a61cd945faacd97` | [PASS](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39022242419/attempts/1) |
| 隔离错误：预期 FAIL | `1e051ae02959f28749b7248e0579528cac9313d4` | `630dd54228a08f82e581a97671e1b976fd92646a` | [FAIL](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39022284684/attempts/1) |
| 修复源码：PASS | `bb681b5fbc8c173d7dc1095fdc07d6eeb8f90355` | `fee69a8a4bac2fe3fe6eaef9da817c08c3228223` | [PASS](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39022501773/attempts/1) |

PR 构建使用 GitHub 的合并测试提交，故源码 HEAD 与 checked_sha 分别记录，不能混用。原始 CI result artifact 已下载并核实。
负向测试 PR [#2](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/pull/2) 的 setup 成功，Lean 在 `Carleman/Periodic/Telescoping.lean:31` 报出 `True.intro : True` 不能用于 `False` 的类型错误。恢复提交与正确源码的文件树完全一致。该 PR 已关闭、未合并，远端测试分支已删除；负向提交不是 main 的祖先。

## 工程与辅助成果

- Lean 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。
- mathlib v4.35.0，提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`；Lake manifest 锁定全部 9 项依赖。
- 构建命令：`bash tools/setup_lean.sh`，随后 `bash tools/lean_ci.sh`；实际库目标为 `Carleman`。
- 声明 `Carleman.sum_sub_perm`：对任意有限索引类型、交换加法群、置换及函数，`∑ i, (f i - f (σ i)) = 0`。
- 陈述核对：这是有限和重排与减法分配的组合，含所有有限索引（也允许空索引），无需时间步长或分析前提。论文周期时间接口可在 N > 0 时实例化它；本成果不承担完整周期分部求和、Section 5 或 Theorem 2.1。登记范围为 AUXILIARY。
- Lean 公理检查输出仅为 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或新增数学公理；CI 会拒绝未许可公理。
- 初始构建为 719 个 Lake jobs，复用了 701 个依赖缓存文件；本地和全新临时克隆均通过。临时克隆使用新安装的 Elan/Lean 和全新依赖，不复用原 checkout 的 `.lake`。
- 17 项 Python、10 项 JavaScript 回归测试及网页同步检查通过；初始 19/26/零完成/IDLE 断言仅属于冻结样例，真实状态可推进。
- 启动包运行目录已移到根目录并移除旧副本；所有 paper 文件及云端修改意见保持原内容。

## 环境与权限

- 当前实例 ID：`ccarenv_b64_Y2NhcmVudl8xYmQyYzgwODA5NzQ4MTkxYTQ4MTBmNGQ3YzZmNmJlOQ`。工具没有返回环境显示名称或可核实的环境管理链接。
- `install_script`、`start_skill` 和必要网络域名已保存到环境草稿并回读核实。保存配置不等于发布；本次新工程快照仍需用户在环境设置中保存后点击 **Publish**。
- 发布后的新 Codex Web 任务恢复尚未验证；同一机器上的干净克隆恢复不能替代这项验证。
- main 最后检查为未保护。实际配置 required checks `lean`、`state-check` 的 REST PUT 返回 HTTP 403 `Resource not accessible by integration`，没有成功启用。应由有管理 API 权限的连接或用户配置；在此之前，由 Dot 核对同一待合并 SHA 的这两个真实检查。无需购买套餐作为开工条件。
- GitHub Git、PR、CI 读取和合并已验证。仓库保持 private；Pages API 字段 `has_pages=false`，工作流无 Pages 部署步骤及写权限。
- 未购买 credits、增加付费服务或启动长期证明调度。仓库自动触发的 Copilot review 不属于另行建立的长期证明循环。

## Dot 首次接续

1. 用户发布环境后，让 Dot 创建它自己的第一个 Codex Web 任务；不要把检查/继续本次工程任务的能力当成已验证。
2. 新任务读取 root AGENTS.md、governance/PROJECT_OPERATIONS.md、state/README.md 和唯一台账；记录 actual branch/base_commit，验证固定工具链及 `lake build Carleman`。
3. 首个证明目标推荐 C001：建立周期索引与 `N > 0`、`δt > 0`、`T = N δt`，按论文符号定义 `D₊ zⁿ = (zⁿ-zⁿ⁻¹)/δt`、`D₋ zⁿ = (zⁿ-zⁿ⁺¹)/δt`，证明周期分部求和/伴随关系；复用 AUX001，保持全离散状态与两种方向。
4. 当前不把 M0a 标为完整 VERIFIED：环境发布、新云端任务恢复、Dot 检查及接续能力仍待真实验证。主定理完整类型与长期主证明循环不在本次工程准备内。

## 首次主分支检查发现的打包问题

[首次 main CI](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39022672100)
在工程合并提交 `fc466e43e93ce2b8322c9abe6e54b785a04dec27` 上，Lean 和 state-check
均成功，但 dashboard 上传失败：upload-artifact 默认排除隐藏目录 `.site`。
后续交接变更将目录改为非隐藏的 `site-artifact/`，仍只复制四个展示资产，并将相同
快照检查纳入 PR CI。此问题与 Lean 证明失败不同；以交接 PR 和最终 main CI 的实际结果
确认修复，不把首个 workflow 的整体结果称为成功。

## T002 接续后的 M0a 终验收更新（2026-10-17）

上文为初始工程交接时的历史状态。T002 已从已合并基线
`8c002e37849fb476608cf4f636a9fa4187e33508` 真实恢复固定工具链、构建 Carleman，
并直接使用 T001 双向分部求和和差分声明；M0a 现按受托台账记为 VERIFIED。
同 SHA main CI、父监督者 C001 语义 PASS 及本次复用证据见
`state/progress.json` 的 M0a/T001/T002。此工程验收不增加 0/26 原文完成数。
