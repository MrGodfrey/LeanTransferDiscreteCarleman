# T208 / C224 独立本机验收

- checked_sha: `7d343224295439a2c5b91f1128facfc9b42feafd`
- base_commit: `fefa061545a3eaad908531f9a9b322fbab55707c`
- reviewed_at: `2026-10-20T04:12:05+00:00`
- reviewer: independent local Agent `/root/accept_spatial_foundations`
- result: **PASS — 7/7 显式声明，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；17/26 不变，P021 不提升**
- evidence_source: **local**；依当前简化协议核对实际本地构建、公理和固定源清单，不查询或声称远端 CI。

直接读取固定 Git 对象中的三模块全部证明、七项展开类型、分析/MATH_SPEC/台账，对照原稿 `paper/main.tex:2366–2398`。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。已完整读取 T207 冻结报告 `c0ac2d84fb45eda398af02ddd2525c65a1f1789b`，并直接检查本批调用的实际 Dirichlet 提升、状态能量预算、Hilbert 弱子列、时间重构、离散分部求和、投影配对及节点 H¹₀ 成员证明；没有以执行者说明代替数学检查。

## 七项声明

下表源码均位于固定 SHA 的 `Carleman/Control/`；声明省略公共前缀 `Carleman.`。raw 行号指 `/tmp/carleman-t208-conforming-compactness-local-axioms.txt` 中的完整展开类型。

| 模块:行 | 实际声明 | raw 行 | 结论 |
| --- | --- | --- | --- |
| ConformingStateWeakCompactness:15 | `conforming_controlled_states_weak_subsequence` | 38736 | **PASS**：原方程内部给出完整能量预算，返回同一状态及同一严格递增子列的三组全测试弱极限。 |
| ConformingWeakTesting:18 | `conforming_forward_reconstructed_weak_identity` | 38818 | **PASS**：真实时间重构上的六项精确恒等式，包含两个端点。 |
| ConformingWeakTesting:62 | `conforming_fixed_forward_reconstructed_weak_identity` | 38844 | **PASS**：仅由 `g.period=T` 搬运到共同的原时间空间，保持所有项。 |
| P1GalerkinTests:19 | `SimplicialPartition.testGalerkinState` | 38872 | **PASS**：实际节点插值属于完整原 conforming P1 子空间。 |
| P1GalerkinTests:25 | `SimplicialPartition.testGalerkinState_value` | 38883 | **PASS**：原 L² 值严格为同一个 `nodalLp ψ.value`。 |
| P1GalerkinTests:30 | `SimplicialPartition.testGalerkinState_lift` | 38888 | **PASS**：实际 Galerkin 能量提升等于原 `testDirichletState`。 |
| P1GalerkinTests:41 | `SimplicialPartition.testGalerkinState_finite_lift` | 38896 | **PASS**：任意有限线性组合的同一提升身份，包含空索引集。 |

## 数学核对

**完整状态弱紧性。** `X n` 是变化的实际 L² 有限维子空间，仅要求包含于原 Dirichlet 值子空间；没有固定自由度、嵌套、统一提升算子范数或预先给定状态弱极限的假设。原 `ForwardEquation`、原势界、`dt*M≤1/2`、初值范数界 `Y` 和控制费用界 `U`，经 `conforming_state_dirichlet_time_uniform` 在内部产生 `stateTimeEnergyBound T M Y U`。该预算同时包含零阶值与全部弱梯度；有限维连续性仅用于建立实际提升 CLM，其范数未进入此预算。

共同空间是实际 `Lp (DirichletEnergyState S) 2 (volume.restrict (Ioc 0 T))`。真实 Hilbert 弱紧性给出一个 `v` 和一个 `StrictMono φ`，对该空间的全部测试成立；再以实际值/梯度 CLM 与时间重构交换导出同一 `φ` 上的值、完整梯度弱极限。值身份由 `dirichletGalerkinState_value` 恢复原 `y n i.succ`。没有另选梯度、另选值子列或输入强收敛。`T` 固定且预算允许依赖 `T`；没有宣称此预算对 `T` 统一。紧性本身不需 `h→0`、`dt→0` 或耦合条件。开域、有界性、`0<d`、可测观测区和明确预算前提均在完整类型中保留。

**六项与原端点符号。** 质量映射 `E` 是 `X⊂L²` 的等距包含；`G` 是原 H¹₀ 提升的实际全部弱梯度；`K` 是原区域限制的伴随。由原方程逐节点测试和真实离散分部求和，左边依次为负的 `y^{i+1}` 与 `dt⁻¹(φ^{i+1}−φ^i)` 配对、正的梯度配对、正的步势配对；右边为正初值配对、正控制配对、负终值配对。测试确为前端 `i.castSucc`，状态为后端 `i.succ`，并允许任意完整 `N+1` 测试序列。时间积分精确变成 `dt` 乘有限和，差商中的逆步长精确抵消，没有意外节点数或时间因子。

刚度配对通过 `dirichletGalerkinState_stiffness` 识别真实梯度。势算子实际是 `P_X(b_i·)`，控制算子实际是 `P_X K`；证明利用测试属于 `X` 消去内积中的正交投影，没有把这些投影算子直接等同于环境乘法或零延拓。对原可测观测区，`K` 已由真实限制伴随身份识别为区域零延拓；纯代数恒等式对任意 `ω` 有意义，并不凭此声称任意不可测集合的点态零延拓。固定 `T` 版本仅代入 `g.period=T`，无新分析前提。

**原 P1 测试。** `testGalerkinState` 使用原点态 `SpatialTest.value` 的真实 `nodalLp`，不对 Lp 等价类取节点值。`nodalLp_mem_dirichletConformingSpace` 同时给出分片仿射性及原图闭包 H¹₀ 成员；边界节点零来自原测试的紧支撑包含开域，保留真实 FaceMatching/BoundaryFitted 与凸域假设。所构造测试属于完整 `M.conformingSpace (dirichletSubspace S)`，没有把状态空间替换成较小节点空间。两提升相等由原值嵌入单射和双方同一个实际 L² 值推出，因此是整个 H¹₀ 状态及其梯度的相等。有限和结论由真实线性性得出，足以接既有有限张量测试一致性。

**范围边界。** 本批 `b n i` 仍为一般有界空间步势族，尚未内部识别为同一个原时空势的时间平均。没有完成有限元控制族选择、原势极限运输、全部测试的极限方程或端点识别，也没有宣称完整 P1 控制收敛。原文后续步骤及 P021 保持未完成。

## 固定本地证据与依赖

`/tmp/carleman-t208-local-evidence.json` 的 checked/source SHA 均精确为本报告固定提交，status=PASS，source=local，finished_at=`2026-10-20T04:07:21.244838+00:00`；实际 `lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 均记录 exit 0。已读取定向 `target-build.log` 的三模块 **3769 jobs** 成功及全库 `build.log` 的 **4216 jobs** 成功，审计 `axioms.log` 为空。Lean 为 v4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

逐字节核对 `/tmp/carleman-t208-local-source-manifest.txt` 的 **981** 个源/构建配置项与固定 Git blobs，集合完整且无缺项、额外项或重复路径。清单 106384 bytes，SHA256=`52636e88b5d93a2c7c7e1f6fa6e202b4ed6007314ebf1fa833b940575f46009b`，与 evidence 绑定一致。三模块递归导入闭包共 **549** 个 Carleman 源文件，其中 **546** 个旧依赖与数学基线逐字节不变；仅三模块为新证明。工作区后续 T209 增量及动态审计未作为本报告依据。

固定 raw 为 **2978156 bytes**，SHA256=`d930712d0c91159de351723e623a9021d2cf021f810f7ce1a6ab702b41034353`。已核对七项完整类型和公理记录、root 的三模块实际导入、七项 `#check`/`#print axioms`，以及遍历所有 `Carleman`（含 private 映回名称）并递归 `collectAxioms` 的检查循环。raw 的 **3517** 条显式公理记录（3513 个唯一声明）均只含 `propext`、`Classical.choice`、`Quot.sound` 或无公理；末行确认 **8979** 项全命名空间递归审计 PASS。未发现 sorryAx、自定义未批准公理或新增估计假设。

本报告在上述 reviewed_at 冻结，只提交本报告；不修改数学实现、原稿、总台账或覆盖统计。
