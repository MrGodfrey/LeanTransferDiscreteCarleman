# T199 / C215 独立本机验收

- checked_sha: `c8020ad62e0ebb26a1c9144edc50d2ac2458a6d9`
- base_commit: `714954acb8b017b09da56c71d4bd91b7d0ccffe2`
- reviewed_at: `2026-10-20T03:12:04+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 5/5 显式声明**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；按当前协议核对固定提交的实际本地构建与审计，未查询或声称远端 CI 成功。

直接读取该 Git 对象中的三个新模块、完整声明类型与证明、关键依赖、T199 分析及原稿。结论是：原有限张量弱恒等式确已扩展到全部真实 H¹₀ 空间测试，沿用同一 Y、U、b、y₀。尚未构造 V′ 时间导数或 H 连续时间迹，不能据本批认定完整控制极限命题完成。

## 原文对应与逐声明结论

原稿 `paper/main.tex:2395–2415` 先给 `eq:conv-limit-identity`，再以任意 w∈V 的单张量测试得到分布形式。本批完成这里的空间测试扩展。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已接受版本一致。

| 固定声明 | 实际核查及结论 |
| --- | --- |
| `Carleman.exists_refining_time_grids` | **PASS**。对任意 T>0 实际取 N=n+1、dt=T/(n+1)，证明周期严格等于 T 且 dt→0。此网格仅用于固定测试表示的身份识别，没有更换原控制网格、抽取控制子列或增加 h/dt 关系。 |
| `Carleman.finiteTensorTestMultiplier_eq_product` | **PASS**。任意有限指标集、原 SpatialTest 及 Icc 上 C¹ 时间系数，实际 J(Σ η⊗ψ) 等于有限产品测试乘子的 L² 类。将同一胞元重构分别送到 Bochner 张量极限和实际产品函数极限，再用极限唯一性。未假设 J 满射或目标产品身份。 |
| `Carleman.exists_dirichlet_test_sequence` | **PASS**。对任意开 S 及完整 `DirichletEnergyState S` 构造原 SpatialTest 序列，在真实 H¹ 能量拓扑收敛；不要求 S 有限体积，不以 L² 稠密性代替 H¹ 稠密性。 |
| `Carleman.FiniteDirichletControlIdentity.spatial_test` | **PASS**。从原完整有限恒等式取 Fin 1，使用已证明的产品身份，恢复同一 ψ 的值、完整弱梯度和真实产品势配对。初值项为 η(0)y₀，时间项负号正确。 |
| `Carleman.FiniteDirichletControlIdentity.all_energy_tests` | **PASS**。对任意 w∈H¹₀，沿上面的能量稠密序列对实际值映射、梯度映射、张量映射、J 及各配对传极限；Y、U、b、y₀ 全部固定，没有依赖测试重新选择状态或控制。 |

三个模块分别为 `Carleman/Control/FiniteTensorProductIdentity.lean`（2 项）、`DirichletTestDensity.lean`（1 项）、`AllEnergyControlTests.lean`（2 项）。已核对清单与实际源码声明一一对应、根导入及五项 `#check @...` / `#print axioms`。

## 关键数学核对与条件边界

**实际产品身份。** `timeTensor` 是 scalar-vector 的真实连续双线性 Bochner 映射，具有 f(t)·v 的 a.e. 代表身份；J 由实际简单函数的乘积代表等距延拓得到。新证明沿辅助时间网格调用真实前层取样强收敛；另一侧对固定 ψ 的空间误差取零，得到趋零的时间 L∞ 误差。旧 L∞→L² 引理使用有限产品测度和 ENNReal 范数估计，处理 a.e. 代表替换并在 0 处取 `toReal`；没有除以体积，也不排除零测度空间。所需有限测度在新产品命题中明确保留，原有界盒满足。

**完整能量稠密性。** `dirichletJetSpace` 正是原紧支光滑测试 jet 的线性 span 在完整弱 H¹ 图拓扑中的闭包。`mem_dirichletJetSpace_iff` 用开放域上的弱导数唯一性，从同一值类的 H¹₀ 资格恢复当前 jet 的闭包资格。每个 span 元素通过真实测试的加法、数乘和零测试仍是一个 SpatialTest。闭包序列经 `SobolevHilbert.ofJet` 连续映射，再进入子类型，得到完整能量收敛；实际范数平方为值 L² 范数平方与完整一阶 fiber L² 范数平方之和。

这里使用的是 `SobolevHilbert.jetEquiv : … ≃L[ℝ] …` 的**连续线性等价**，无须等距。分析文件中“jet 等距等价”的措辞不精确；实际声明和证明没有依赖该更强性质，不构成数学阻断项。

**固定数据、测试族及端点。** 最终定理的显式输入是 T>0、S 开且测度有限、原有界可测乘子 b、任意 L² 初值 y₀、完整 Bochner 能量状态 Y、完整 Bochner L² 控制 U，以及同一数据的 `FiniteDirichletControlIdentity`。后者是本辅助定理的明确前提，T198 已在原控制弱积点分支内部供应。对任意 η、f，只要求闭区间 Icc 上连续以及真实 `HasDerivWithinAt η (f t)`，没有区间外延拓、周期、伴随方程或端点零条件。空间 w 只属于原 H¹₀，无光滑代表或 H² 前提。

最终式的三项左侧依次为负时间配对、真实梯度配对及 `⟪b.map(J Yv), J(η⊗w)⟫`；右侧为 `⟪y₀,η(0)w⟫+⟪U,η⊗w⟫`。梯度取自同一 Y 的实际一阶弱字段，Dirichlet 形式按全部坐标配对。势项保留原乘子和原状态，没有换成任意抽象双线性形式。η 在 0、T 的值均自由；无终端项的形式承接 T198 的终端极限，尚不能代替连续迹及其端点识别的证明。

## 依赖与本地证据

已全文读取并核对 T198 冻结报告 `governance/reviews/T198-local-acceptance.md`（报告提交 `c1734158e7981e99e96131efdac9d72f456696b8`，与当前报告文件逐字节相同），并读取实际 `FiniteWeakControlIdentity` 定义和调用。对三个新模块递归解析得到 **415 个 Carleman 模块**；其中 **412 个旧模块均与基线 Git blob 相同**。另外核对实际关键闭包：有限产品乘子与 T195（390 模块）、时间张量与 T191（69 模块）、Dirichlet 时间能量空间与 T188（59 模块）、原测试线性运算与已接受版本（31 模块）全部不变。已直接检查本次所需的原闭包定义、弱值注入、jet 连续等价、真实梯度形式、时间张量、J 简单函数身份及有限测度 L² 极限桥；未把旧报告作为新证明的替代。

独立读取 `/tmp/carleman-t199-local-evidence.json`：`checked_sha`、`source_head_sha` 均为本报告 proof SHA，`source=local`、`status=PASS`，完成时间为 `2026-10-20T03:05:23.526383+00:00`。执行证据记录 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均 exit 0；本报告核验这些实际执行记录与源码对应关系，没有声称重新执行全库构建。

| 证据 | 独立读取结果 |
| --- | --- |
| `/tmp/carleman-t199-target-build.log` | 三个新模块实际完成，3617 jobs；251 bytes，SHA256 `9898db6c1243fc3f4f62b0aaf9aa51e2c2e74f7040feb06a57b4d093a4d30939`。 |
| `/tmp/carleman-t199-build.log` | 根目标实际完成，4195 jobs；80 bytes，SHA256 `f8f310af91b501aa6ab1ceaa30db597d4692684d972e5dde81b84a6b5d0017ed`。 |
| `/tmp/carleman-t199-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t199-all-tests-local-axioms.txt` | 2,898,922 bytes；SHA256 `6e4c965a734bca2256f70f93a4c836b6f737f618355f2d73e6797486990667d8`；末行确认全部 **8786** 个 Carleman 声明递归审计通过。 |
| `/tmp/carleman-t199-local-source-manifest.txt` | 104,063 bytes；SHA256 `3d5f6dce8a261f11af1e9e5ff8a8d8732595bd539657c1e8f7d1772ed2463102`。独立枚举固定 Git 树，全部 tracked Lean 文件和三个工具链配置共 **960** 项，覆盖精确、无重复；每项 SHA256 均与 proof Git blob 相同。 |

审计文件中五项展开类型均与所审源码一致，每项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。已读固定 `CheckAxioms.lean` 的全命名空间循环：使用 `privateToUserName` 和 `collectAxioms` 覆盖私有及生成声明，遇到白名单外公理即失败；并检查全部 3441 个打印公理记录均无白名单外项。8786 是实际递归审计数，不是五项公开声明的替代计数。Lean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定配置及执行证据一致。

**签发结论：** C215 本阶段可按 AUXILIARY 接受，五项声明均 PASS，无阻断缺陷；保留上述说明措辞更正。V′ 时间导数、H 连续时间迹及 y(0)=y₀、y(T)=0 的识别仍待，P021 和原文覆盖数不变。本报告签发后冻结正文与时间，仅提交此报告，不修改数学、台账或原稿。
