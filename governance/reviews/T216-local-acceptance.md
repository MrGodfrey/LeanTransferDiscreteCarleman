# T216 / C232 独立本机验收

- checked_sha: `17b0a22b45b9d314f90414b72d3c3198ef129f0d`
- mathematical_base: `2bbedbc1881148eb48d0280570a98d0234ef0813`
- reviewed_at: `2026-10-20T05:04:58+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，25/25 声明，无阻断缺陷；C232 可按 AUXILIARY 验收，原文覆盖仍为 17/26。**

本次直接读取固定 Git 对象中的两模块全部定义与证明、原稿 `paper/main.tex:2615–2652`、T216 分析、MATH_SPEC 和固定 C232/T216 声明清单；逐项读取固定 raw 的完整 `#check @` 类型及公理结果。原 Proposition A.1 的目标还包括 W^{2m,∞} 系数形式、关联算子域及加权估计；本次只清偿其中真实 H₀ᵐ 空间基础，不提升整条 `prop:spatial-operators`。

## 数学核对

1. `SpatialTest` 的 value 是整个欧氏空间上的真实 C∞ 函数，具有紧支撑且 `tsupport ⊆ S`。`derivativeTest` 使用实际 `fderiv`，以导数支撑包含原支撑及实际连续可微性证明仍是测试；`wordTest` 的递归没有输入目标射流。`wordTest_perm` 的相邻交换展开为对同一个光滑尾词测试的两次实际方向导数。已读取 `smoothD_comm` 中 CLM 作用的求导及固定 mathlib `ContDiffAt.isSymmSndFDerivAt`，后者对实 C² 函数给真实二阶 Fréchet 对称性；其余 Perm 分支正确传递相等。排序仅选无序多指标的代表，`multiTest_cons` 用刚证明的置换相等恢复任意新增方向。
2. `allOrderJet` 对每个 `Fin (m+1)` 的全部 `Sym (Fin d) k`，组装原测试导数的真实 L² 类。实际紧支光滑性内部供应每个 `MemLp`。已读取 `derivativeFieldAssembly` 的真实有限 CLM 及逐分量/范数平方身份：每个无序多指标仅出现一次，不含排列重复或阶乘。其弱链展开为对**所有**原测试 ψ 的 `⟨D^αφ,D_iψ⟩=−⟨D_iD^αφ,ψ⟩`；`TestPoincare.weakDerivative` 经真实 Lipschitz 分部积分给该身份，`multiTest_cons` 与 `derivativeTest_toLp` 识别同一场。零阶、每个高阶分量和截断均保留原对象。
3. 在开域上，原 `WeakSobolevJet.value_injective` 由全部弱测试的导数唯一性逐阶证明；因此 m=1 身份、零/加/实数倍射流身份没有假设目标高阶射流已存在。真实测试相加/数乘保持光滑、紧支及原域支撑。`higherDirichletJetSpace_eq_closure` 对 span 的每个构造明确构造一个测试，证明 span 的载体本来就是测试射流集合，再取闭包；没有把未经证明的 span 闭包当作测试闭包。
4. `higherDirichletSubspace` 是上述闭包的零阶 L² 像，`mem_higherDirichletJetSpace_iff` 用值注入性恢复同一射流。`higherDirichletSubspace_closed` 的结论是 **Hᵐ 图空间中该值像的原像闭**，不是其 L² 像闭。`higherDirichletSubspace_dense` 通过所有测试已在空间内、正交补与实际分布分离定理给 L² 稠密性；没有添加有限体积或边界迹假设。这两种拓扑没有混淆。
5. 已读取 `SobolevTopology`、`SobolevHilbert`、`ConformingHilbert`：完整弱链是有限 L² 场积中的闭条件；原 jet 的积范数与平方和 Hilbert 范数有实际连续线性双向等价。`SobolevHilbert.norm_sq` 是所有阶场 L² 范数平方之和。最终完备性来自该真实 Hilbert 空间中值原像的闭性，而非从 L² 完备性错误转移到稠密值像。m=1 的生成射流和原 `dirichletJetSpace` 一致，再经同一 value 映射得到 `higherDirichletSubspace_one`。
6. 类型量词允许任意有限 d 和任意 m∈ℕ；原命题 m≥1 是其中子范围。m=0 只保留零阶字段；d=0 的正阶坐标与非空 Sym 指标为空，S=∅ 使用零限制测度；代码没有除以维数、体积或阶数，所用唯一性/完备性/密度均覆盖这些情形。核心测试构造不要求开性；线性识别、闭包等同、密度等定理显式要求 `IsOpen S`。没有额外的测试射流存在、系数光滑性、椭圆正则性或边界迹前提。

## 完整声明清单

源码定位均相对于 `Carleman/Spatial/` 下固定版本文件；raw 行号相对于 `/tmp/carleman-t216-high-order-space-local-axioms.txt`。表内均核对完整类型，而非仅名称。

| 固定源码定位 | 完整声明 | raw 起始行 | 逐项结论 |
|---|---|---:|---|
| SpatialTestAllOrders:20 | `Carleman.SpatialTest.eq_of_value_eq` | 40118 | PASS；测试结构其余字段均为性质，实际 value 相同给测试相同。 |
| SpatialTestAllOrders:26 | `Carleman.SpatialTest.wordTest` | 40121 | PASS；逐次实际 fderiv 沿标准坐标方向，仍属原 SpatialTest S。 |
| SpatialTestAllOrders:30 | `Carleman.SpatialTest.wordTest_perm` | 40124 | PASS；List.Perm 的 nil/cons/swap/trans 全部覆盖，swap 用真实二阶导数对称性。 |
| SpatialTestAllOrders:41 | `Carleman.SpatialTest.multiTest` | 40127 | PASS；Sym 无序多指标取排序词构造实际测试。 |
| SpatialTestAllOrders:44 | `Carleman.SpatialTest.multiTest_nil` | 40130 | PASS；空多指标精确回到原测试。 |
| SpatialTestAllOrders:49 | `Carleman.SpatialTest.multiTest_cons` | 40133 | PASS；排序词置换给新增任意坐标的真实导数测试身份。 |
| SpatialTestAllOrders:60 | `Carleman.SpatialTest.allOrderJet` | 40137 | PASS；所有 0≤k≤m 实际 L² 场及每个相邻阶弱链内部构造。 |
| SpatialTestAllOrders:67 | `Carleman.SpatialTest.allOrderJet_value` | 40141 | PASS；零阶恰为原测试的 L² 类。 |
| SpatialTestAllOrders:72 | `Carleman.SpatialTest.allOrderJet_component` | 40145 | PASS；每阶每个 Sym 分量恰为对应真实测试导数的 L² 类。 |
| SpatialTestAllOrders:77 | `Carleman.SpatialTest.allOrderJet_truncate` | 40150 | PASS；任意 m≤n 截断精确保留低阶射流。 |
| SpatialTestAllOrders:80 | `Carleman.SpatialTest.allOrderJet_one` | 40154 | PASS；开域上弱射流值注入给与旧 H¹ 射流完全相等。 |
| SpatialTestAllOrders:85 | `Carleman.SpatialTest.zeroTest_allOrderJet` | 40157 | PASS；真实零测试的所有阶射流为零。 |
| SpatialTestAllOrders:92 | `Carleman.SpatialTest.addTest_allOrderJet` | 40160 | PASS；真实测试相加与所有阶射流相加交换。 |
| SpatialTestAllOrders:99 | `Carleman.SpatialTest.smulTest_allOrderJet` | 40163 | PASS；任意实数倍与所有阶射流交换。 |
| HigherDirichletSpace:14 | `Carleman.higherDirichletJetSpace` | 40168 | PASS；定义于完整弱 Hᵐ 图空间的闭线性子空间。 |
| HigherDirichletSpace:17 | `Carleman.higherDirichletSubspace` | 40172 | PASS；上述空间在真实零阶 L² 映射下的像。 |
| HigherDirichletSpace:20 | `Carleman.higherDirichletSubspace_sobolev` | 40175 | PASS；像内每个元素有同一真实 Hᵐ 射流。 |
| HigherDirichletSpace:25 | `Carleman.test_mem_higherDirichletJetSpace` | 40178 | PASS；每个原紧支光滑测试的全阶射流均为成员。 |
| HigherDirichletSpace:29 | `Carleman.test_mem_higherDirichletSubspace` | 40181 | PASS；每个原测试的实际 L² 类均为成员。 |
| HigherDirichletSpace:33 | `Carleman.higherDirichletJetSpace_eq_closure` | 40184 | PASS；span 归纳构造一个原测试，故闭线性包就是测试集合的闭包。 |
| HigherDirichletSpace:54 | `Carleman.mem_higherDirichletJetSpace_iff` | 40187 | PASS；真实值映射注入，成员资格不依赖另选射流。 |
| HigherDirichletSpace:64 | `Carleman.higherDirichletSubspace_closed` | 40192 | PASS；明确证明值像的 Hᵐ 原像闭；没有宣称 L² 闭。 |
| HigherDirichletSpace:73 | `Carleman.higherDirichletSubspace_dense` | 40195 | PASS；全部原测试消灭正交补，得到真实 L² 稠密性。 |
| HigherDirichletSpace:82 | `Carleman.higherDirichletSubspace_one` | 40198 | PASS；m=1 的原 L² 子空间与 dirichletSubspace 精确相等。 |
| HigherDirichletSpace:90 | `Carleman.higherDirichletEnergy_complete` | 40201 | PASS；闭 Hᵐ 子空间的完整 Sobolev Hilbert 实现完备。 |

## 固定本地证据与依赖边界

- 独立逐项校验 `/tmp/carleman-t216-local-source-manifest.txt` 的 **1003** 条路径及 SHA256；集合恰为固定提交全部受检 `.lean` 和三项工具链配置，全部摘要与 Git blob 字节一致。manifest 为 **108797 bytes**，SHA256 `333fe1f4b227d3f50e0958e58d95d9a8393d94c793d8af0446559128e4992ad6`，与 `local-evidence.json` 相同。两新模块均实际进入固定 `Carleman.lean`；原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。
- 从两模块实际 import 递归得到 **79** 个 Carleman 模块；其中 **77** 个既有模块在 mathematical_base 与 checked_sha 的 Git blob 全部不变，另 2 个就是本次新模块。直接复核上述关键定义/证明和旧 H¹ 闭包，未重审无关历史。已检查的 mathlib `FDeriv/Symmetric.lean` 字节与锁定提交 `56a005855ea17e0b0958f73ec801ae140b0a1679` 一致；工具链为 Lean **4.35.0**。
- 实际读取 `/tmp/carleman-t216-target-build.log`：两目标成功、**3221 jobs**；`/tmp/carleman-t216-build.log`：`Carleman` 成功、**4239 jobs**。`/tmp/carleman-t216-local-evidence.json` 精确绑定 checked/source SHA，记录两命令 `lake build Carleman`、`lake env lean tools/CheckAxioms.lean` 均 exit 0，完成时间 `2026-10-20T04:59:33.750361+00:00`。本次审核复核这些实际日志与固定源绑定，没有声称独立重跑全库。
- raw **3089613 bytes**，SHA256 `c917b89693ffedc332308f93df117eedddce1c4c6cc2f61b7a8a3aca413c2042`，与 evidence 及固定任务登记一致；`/tmp/carleman-t216-axioms.log` 为 **0 bytes**。独立扫描 raw 的 **3589** 条显式公理输出，全部只含 `propext`、`Classical.choice`、`Quot.sound` 或无公理；本批 25 项全部含完整类型和对应公理记录。另读取固定 `CheckAxioms.lean` 的全命名空间遍历：对含私有声明的所有 Carleman 常量执行 `collectAxioms`，遇未批准公理即抛错。raw 最后一行实际为 `Axiom audit passed for all 9130 Carleman declarations.`，这 **9130** 是完整递归审计数，区别于显式打印数。未发现 `sorryAx` 或新增数学公理。
- 遵照本机简化协议，没有查询、等待或下载远端 CI，也没有把本地 PASS 写成远端结论。

本报告仅验收一般阶 H₀ᵐ 空间及测试射流；一般 W^{2m,∞} 系数乘法、闭形式/关联算子域及完整 A2/A3 结论仍待。本次没有发现需修复的数学或证据缺陷。正文与 reviewed_at 在签发后冻结；只提交本报告，未修改证明、原稿或台账。
