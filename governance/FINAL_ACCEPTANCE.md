# 原稿 26 项结果的最终验收

原稿 *From Continuous to Fully Discrete Carleman Estimates* 的 **26/26 个具名结果均已完成 Lean 证明及独立数学验收**。最终数学提交是 `99d519544e0eb8d42a955ca6bff3935c322d855f`；此后的提交只记录验收、文档和状态。完成登记时间：`2026-10-20T12:49:04.967718+00:00`。

覆盖原始 Theorem 2.1、Sections 3–4 的时间与空间估计、原 P1/Cartesian 数值实现、Section 7 观测与控制、Corollary 7.9 的零控制极限，以及 Appendices A/B。原文映射及每项固定证据见 [PAPER_COVERAGE.md](PAPER_COVERAGE.md) 和唯一台账 [paper_coverage.json](../state/paper_coverage.json)。条件性中间命题和辅助引理不增加这 26 项的计数。

## 最后一批独立验收

- [T267](reviews/T267-local-acceptance.md)：完整原域、原弱周期轨迹上的连续热 Carleman 估计，P024。
- [T268](reviews/T268-local-acceptance.md)：真实 P1/Cartesian 物理观测与近似零控制，P014/P015。
- [T269](reviews/T269-local-acceptance.md)：任意终端子空间的过滤观测、精确投影消除与完整终态指数界，P017/P018。
- [T270](reviews/T270-local-acceptance.md)：原两种实现的独立空间/时间加密、真实区域控制及每个弱聚点的连续零控制结论，P021；并完成全部 26 项的标签、范围和源码版本复核。

T270 冻结验收：[2026-10-20T12:41:09+00:00](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/blob/ad75f2876a46b2b4e0fc4d1a8f0fe906cf25bd1e/governance/reviews/T270-local-acceptance.md)。主执行者全文读取并核对报告与固定本地证据后登记；编译通过没有替代原命题语义验收。

## 最终本地验证

| 检查 | 实际结果 |
| --- | --- |
| `lake build Carleman.Control.FiniteHalfspaceP1NullControlLimits` | 4,170 jobs，exit 0 |
| `lake build Carleman` | 4,327 jobs，exit 0 |
| `lake env lean tools/CheckAxioms.lean` | 全部 10,681 项 Carleman 声明递归公理审计 PASS，exit 0 |
| 根入口完整性 | 全部 1,080 个数学模块均由 `Carleman.lean` 导入 |
| 源码绑定 | 1,085 个 Lean 源文件与固定配置逐 Git blob 核对 |
| 旧成果有效性 | 26 项覆盖的 19 个不同证明版本均可达最终提交；各版本全部既有数学模块、三个工具链配置和原稿均未改变 |

Lean 固定为 4.35.0，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。最终本地审计完成时间为 `2026-10-20T12:27:10.790056+00:00`。

- 源文件清单 SHA256：`8eefad9a39e0979ca9fccae128ab8b49c23edde850b891dff1e4113cf56e139b`。
- 完整公理审计输出 SHA256：`afc286b5b5428afa187e1b30e3b5dff3956af66304d01265ffc1d826bd419bd0`。
- 依赖公理只允许 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx` 或新增未证明数学公理。

原稿 TeX 的 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，原 PDF 的 SHA256 保持 `6b266e7b89c841fec178f56f2f832ff743199c3c36b48c5f9bc287ffa8e9fd5c`。未弱化原结论，也未添加未清偿前提。远端 CI 保留为后台复现检查，本次完成判断使用已执行的本地验证及独立验收。

## 台账收尾与范围

全部任务已集成，全部里程碑已验收，待验收队列为空。最初规划中的 10 个空占位按同一原文标签补齐其既有完整证明和验收证据：C005→P004, C006→P006, C007→P008, C013→P024, C014→P011, C015→P012, C016→P014, C017→P015, C018→P017, C019→P021。这是历史映射清理，没有新增定理或重复计数。条件性中间成果继续保留其原范围。

完成范围是当前原稿的 26 个具名数学结果及其必要依赖。Section 8 数值实验复现按原 [MILESTONES.md](MILESTONES.md) 是单独的可选交付，不纳入本次 Lean 完成结论。
