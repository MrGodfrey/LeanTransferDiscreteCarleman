# T039 / C055 独立本机验收

- `checked_sha`: `fa61af9d4b260cac83d599ef4e228af88f67aee8`
- `base_commit`: `756ee9cedb6af22baf308c796fbe0f1d7885e26d`
- `reviewed_at`: `2026-10-18T18:27:45+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际节点零延拓的全空间 H¹、全部原 SpatialTest 的真实 H¹ jet、紧支光滑 jet 在 H¹ 图范数中的闭包及其标量 L² 实现、该空间在 H¹ 中闭合且在 L² 中稠密。**不提升 P011、P014、P015 或任何完整原文结果，原文完成仍为 12/26。**

本次从固定提交导出源码，独立读取五个新模块的全部证明、27 项实际展开类型及所调用依赖，对照原 `paper/main.tex` Section 3/6。执行者规格和 CI 是核实对象，没有代替数学审查；后续未提交的新模块不在本报告范围。

## 全部 27 项声明

完整名称均以前缀 `Carleman.` 开始。位置属于固定版本的 `Carleman/Spatial/`，顺序与交付清单、C055 和 T039 一致。

| # | 声明（省略 Carleman.） | 位置 | 独立核对结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.nodalDerivativeFunction_zero_outside` | `SimplicialGlobalDerivative.lean:14` | PASS；closure S 外每个开单元 indicator 为零，实际 CLM 字段为零。 |
| 2 | `SimplicialPartition.nodalFunction_hasFDerivAt_global_ae` | `SimplicialGlobalDerivative.lean:20` | PASS；全空间排除有限零测骨架，覆盖内用单元内部邻域，覆盖外用恒零邻域，得到真实经典导数 a.e.。 |
| 3 | `SimplicialPartition.nodalDerivativeFunction_global_memLp` | `SimplicialGlobalDerivative.lean:38` | PASS；有限紧单元各自有限体积，常值 CLM 的开单元 indicator 有真实全空间 MemLp 2。 |
| 4 | `SimplicialPartition.nodalGlobalDerivativeLp` | `SimplicialGlobalDerivative.lean:47` | PASS；由已证全空间 MemLp.toLp 构造实际导数 L² 类。 |
| 5 | `SimplicialPartition.nodalGlobalDerivativeLp_ae` | `SimplicialGlobalDerivative.lean:51` | PASS；在完整 volume 下以 a.e. 等式恢复逐片导数字段。 |
| 6 | `SimplicialPartition.nodalFunction_global_memLp` | `SimplicialGlobalDerivative.lean:54` | PASS；公开的边界几何及边界节点零给全空间连续，有限紧单元给紧支，从而证明真实标量 MemLp。 |
| 7 | `SimplicialPartition.nodalGlobalLp` | `SimplicialGlobalDerivative.lean:61` | PASS；同一 nodalFunction 的全空间 L² 类，没有换成任意延拓。 |
| 8 | `SimplicialPartition.nodalGlobalLp_ae` | `SimplicialGlobalDerivative.lean:66` | PASS；实际 toLp 代表在 volume 下 a.e. 等于同一节点函数。 |
| 9 | `weakSpatialDerivative_of_lipschitz_full` | `LipschitzGlobalSobolev.lean:13` | PASS；对每个真实 SpatialTest univ 和任意方向 e，由实际 Lipschitz 积分分部推出正确负号的完整弱身份。 |
| 10 | `lipschitzGlobalJet` | `LipschitzGlobalSobolev.lean:33` | PASS；实际 L² 导数字段的 a.e. HasFDerivAt 供应所有坐标弱导数，构造原 WeakSobolevJet。 |
| 11 | `lipschitzGlobalJet_value` | `LipschitzGlobalSobolev.lean:45` | PASS；所构造 jet 的零阶 value 精确等于输入 u。 |
| 12 | `SimplicialPartition.nodalGlobalSobolevJet` | `SimplicialGlobalSobolev.lean:14` | PASS；以同一零延拓、实际全空间 L² 类、真实 a.e. 导数和已证全局 Lipschitz 构造全空间 H¹ jet。 |
| 13 | `SimplicialPartition.nodalGlobalSobolevJet_value` | `SimplicialGlobalSobolev.lean:23` | PASS；value 精确等于同一 nodalGlobalLp。 |
| 14 | `SimplicialPartition.nodalGlobalLp_mem_sobolev` | `SimplicialGlobalSobolev.lean:29` | PASS；具体 jet 给原 sobolevSubspace d 1 volume univ 的成员见证。 |
| 15 | `SpatialTest.memLp_fderiv` | `SpatialTestSobolev.lean:12` | PASS；每个原测试函数的真实连续 Fréchet 导数有紧支，限制测度下 MemLp 由此证明。 |
| 16 | `SpatialTest.fderivLp` | `SpatialTestSobolev.lean:15` | PASS；实际 fderiv 的 CLM 值 L² 类。 |
| 17 | `SpatialTest.fderivLp_ae` | `SpatialTestSobolev.lean:18` | PASS；仅以 a.e. 身份识别所选 L² 代表。 |
| 18 | `SpatialTest.sobolevJet` | `SpatialTestSobolev.lean:20` | PASS；C∞ 紧支内部给全局 Lipschitz，真实 fderiv 与 lineDeriv 一致，全部坐标弱身份均证明。 |
| 19 | `SpatialTest.sobolevJet_value` | `SpatialTestSobolev.lean:30` | PASS；准确恢复原 φ.toLp(volume.restrict S)。 |
| 20 | `dirichletJetSpace` | `DirichletSpace.lean:15` | PASS；全部真实紧支光滑 jet 的线性张成在 WeakSobolevJet 的 H¹ 图范数中取闭包。 |
| 21 | `dirichletSubspace` | `DirichletSpace.lean:18` | PASS；上述闭包经实际 value 线性映射在标量 L² 中的像。 |
| 22 | `dirichletSubspace_sobolev` | `DirichletSpace.lean:21` | PASS；映射见证本身给原 Sobolev range 成员，没有附加弱导数假设。 |
| 23 | `test_mem_dirichletJetSpace` | `DirichletSpace.lean:25` | PASS；每个测试 jet 属于 span，继而属于其闭包。 |
| 24 | `test_mem_dirichletSubspace` | `DirichletSpace.lean:28` | PASS；实际测试 L² 类由上一项和准确 value 身份进入标量像。 |
| 25 | `mem_dirichletJetSpace_iff` | `DirichletSpace.lean:31` | PASS；S 开时真实弱导数唯一性给 value 单射，从标量像成员恢复原 jet 成员。 |
| 26 | `dirichletSubspace_closed` | `DirichletSpace.lean:40` | PASS；所断言的集合位于 WeakSobolevJet，等于已定义闭包；不声称标量子空间在 L² 中闭合。 |
| 27 | `dirichletSubspace_dense` | `DirichletSpace.lean:49` | PASS；L² 正交补中的元素与全部原测试正交，真实测试分离性推出零，故 L² 闭包为全空间。 |

## 全空间零延拓、实际导数与可积性

`nodalDerivativeFunction` 沿用基线的实际局部 AffineMap 线性部分，定义为各开单元 indicator 乘该常值 CLM 的有限和。内部不交保证在单元内部只留下该单元导数；closure S 外因 inside 条件每一项都为零。全空间 a.e. 导数证明首先用实际紧凸单纯形的 frontier 零测，有限交排除所有单元边界。若 x 属于 closure S，真实 cells_union 给某单元，而不在该单元 frontier 使 x 位于其内部；已有全局插值与局部仿射映射在整个单元上的一致性遂给邻域导数。若 x 不属于 closure S，其开补集提供恒零邻域，导数为零。这里没有把单元上的点态一致错误地直接用于共享面微分。

这项经典 a.e. 导数结论不要求边界节点零，是正确的：边界跳跃可能位于零测骨架，经典 a.e. 导数本身不能排除分布导数中的边界项。新代码没有用该结论直接推出弱导数；后续全空间 H¹ 还明确使用边界节点零、BoundaryFitted、FaceMatching 和 S 开所导出的全局 Lipschitz。

导数字段的全空间 MemLp 不再依赖基线的 `IsFiniteMeasure (volume.restrict S)`，更没有使用全空间体积有限的假设。每一开单元的体积由 `interior ⊆ cell` 和真实 cell 的紧性控制为有限，`memLp_indicator_const` 随后给各项可积，有限和给整个字段可积。标量函数则由真实连续零延拓和支集包含于有限紧单元并得到紧支连续，从而直接证明全空间 MemLp。所有 toLp 身份均以 a.e. 公式使用，没有给任意 L² 代表附加逐点连续性。

最终节点函数的输入为任意点态 f，其实际边界顶点值为零；不要求 f 先验可测、连续或属于某个 Sobolev 空间，因为输出仅使用有限节点值。任意维 d、有限索引、原分区 inside/cover/内部不交、FaceMatching、BoundaryFitted 和 S 开均在真实参数中；没有隐藏的有限体积、形状正则、边界光滑或目标弱身份假设。空网格使覆盖强迫 S 为空；d=0 时一阶坐标条件为空而零阶值仍准确恢复。

## 完整弱测试与真实 H¹ 身份

已直接检查原 SpatialTest、IsWeakSpatialDerivative、firstOrderJet 以及 mathlib 固定版本的 `LipschitzWith.integral_lineDeriv_mul_eq`。SpatialTest univ 包含所有真实全空间 C∞ 紧支实值测试函数；一般 SpatialTest S 要求同样的全空间光滑性和 `tsupport ⊆ S`，没有缩减为有限元测试或任意指定子族。

全空间积分分部使用实际 Euclidean Lebesgue volume，满足 mathlib 的有限维加性 Haar 测度条件。该依赖通过真实差商、受控积分极限和平移换元证明 `∫ D_e f·φ = ∫ D_{-e}φ·f`。测试函数 C∞ 紧支内部产生 Lipschitz 条件，且真实 `lineDeriv φ (-e) = -fderiv φ e`，故最终恰为 `∫ D_e φ·u = -∫ φ·v`。u、v 是实际 L² 类并以 a.e. 等式与 f、lineDeriv f 联系；这既保证实际配对有意义，也避免以目标分布恒等式作输入。符号和方向均正确。

`lipschitzGlobalJet` 的 hA 是真实 `HasFDerivAt f (A x) x` a.e.，其中 A 是实际 CLM 值 L² 类。连续线性求值在各正交基方向上得到标量 L² 类，再由 HasFDerivAt 给真实 lineDeriv 的 a.e. 身份。firstOrderJet 将全部坐标弱导数放入原 weakJetSubmodule；零阶只有空多重指标，一阶 Sym 指标与实际坐标方向对应。因此结果是原完整弱 H¹ jet，value 与 u 严格相等。对节点函数的实例化清偿了所有这些输入，输出确为 volume/univ 下的 H¹，而不只是 S 上的 H¹。

所用全局 Lipschitz 常数仍是有限个真实局部导数算子范数之和；它可以依赖节点值、网格和单元数，只用于成员证明。此处没有将其计入原统一数值误差或逆估计常数，也没有新增 T 或权参数的统一性结论。

对于每个原 SpatialTest S，新模块独立构造真实 fderivLp。其 MemLp 来自实际连续导数、导数紧支及限制测度在紧集上的有限性，不要求 S 有限体积或已有 H¹ 成员。光滑紧支函数的实际全局 Lipschitz 和真实 fderiv/lineDeriv 关系，代入已核对的限制测度弱导数桥，得到所有坐标弱身份。该桥因测试函数及其导数在 S 外为零，正确把全空间积分限制到 S。最终 value 就是原 φ.toLp，没有改变测试空间或所代表的函数。

## Dirichlet 闭包与两种拓扑

WeakSobolevJet 是 L² 导数字段有限乘积中满足全部分布身份的子空间。已直接复核 SobolevTopology：分布约束是连续 L² 配对的闭等式，故 jet 空间完备；其继承范数是各阶 L² 字段范数的最大值，并由已有上下界与字段范数之和等价。m=1 时这正是与通常 H¹ 范数等价的完整图范数拓扑，包含标量和真实全部一阶导数，绝非仅使用零阶 L² 范数。

`dirichletJetSpace` 对所有原紧支光滑测试的真实 jet 的线性张成取该拓扑下的闭包。线性张成没有引入额外函数类别：光滑紧支且支集包含于 S 的函数对有限线性组合封闭，且所组装字段是真实线性导数。这是 H¹₀ 所需的光滑闭包构造；没有把点态边界零作为其定义。`dirichletSubspace` 是该空间通过原 value 的线性像，所以自然包含于原 H¹ 标量 range 并包含所有测试类。

S 开时，`value_injective` 来自原完整测试空间上的弱导数唯一性；限制体积测度确实 a.e. 位于 S，且其局部有限性由实际体积测度供应。像成员见证 v 与给定 u 的 value 相等后，单射性严格得到 v=u。因此 `mem_dirichletJetSpace_iff` 合法，随后 `dirichletSubspace_closed` 的实际类型是在 WeakSobolevJet 中断言 `{u | value u ∈ dirichletSubspace S}` 闭合。它没有声称 L² 子空间本身在其 L² 子空间范数下闭合或完备；H¹ 拓扑是通过真实 jet 实现的。

另一个结论 `dirichletSubspace_dense` 则确实使用标量 L² 的 Hilbert 拓扑。若 u 在该子空间的正交补中，所有实际 φ.toLp 都已证属于该空间，故 u 与全部紧支光滑测试正交。已直接核对 `spatial_eq_zero_of_tests`：由 u 的 L² 性得到局部可积性，mathlib 在开集上的完整光滑测试分离定理给 u 在 S 内 a.e. 为零，再由限制测度 a.e. 位于 S 得 u=0。L² 完备内积空间的正交补刻画遂给其 L² 闭包为全空间。此处没有假设目标密度或 H¹ 逼近，也没有把 H¹ 闭合用于错误地推出 L² 闭合。

## 原文对应与剩余义务

原 Section 3 以真实空间导数和 Sobolev 图范数组织连续形式及演化估计；原 Section 6 明确取 `V=H₀¹(Ω)`、梯度形式和 Dirichlet Laplacian，并要求 P1 空间属于 H₀¹。当前工作提供其中真实 H¹ 零延拓与 H₀¹ 光滑闭包定义的基础，但没有构造原完整 Dirichlet 形式或推导具体 P1 实例。

两项新构造之间尚有公开的实质缺口：节点零延拓属于 H¹(ℝᵈ)，不等于已经证明其在 S 上属于上述紧支光滑 H¹ 闭包；当前没有 nodalLp 的 dirichletSubspace 成员定理。对原凸多面体的支撑内缩、光滑逼近及其 H¹ 收敛仍需证明。Poincaré、梯度形式强制性、实际 Dirichlet OriginalForm、H² 连续代表和点值、具体网格的几何条件、形状正则与分级、局部误差、加权投影稳定、逆估计及连续热 CE 均未因此完成。

这些尚未完成的桥梁不构成本批辅助声明的证明缺陷，但阻止把本报告用于提升 P011/P014/P015 或完整原文结果。C055 的 `extra_hypotheses=[]` 仅对本次公开参数下的辅助目标理解，不能解释为完整 P1 命题已经无条件实现。

## 固定依赖、实际 CI 与公理

本次五模块的导入闭包包含 47 个 Carleman 模块，其中 42 个既有模块与基线逐字节一致，新增恰为本次五模块；固定 Carleman.lean 显式导入全部五模块。基线 [T038 验收](T038-local-acceptance.md) 已读取，并直接复核其实际全局 Lipschitz、边界零、紧支和导数构造。原稿、AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE、工具链和两份 CI 工作流均与基线相同；MATH_SPEC 增加本阶段说明。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

已核实本机 mathlib HEAD 为固定 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净；读取的 Rademacher 差商积分分部、光滑测试分离和闭包正交补定理均属该 pin。Lean 为 4.35.0，CI 报告其提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。

固定 CheckAxioms 对本次 27 项逐一执行 `#check @...` 与 `#print axioms ...`，再遍历以 privateToUserName 识别的全部 Carleman 声明，对每个声明递归 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。已核对实际输出中的 27/27 展开类型及每项公理集合，均恰为上述正常基础公理。`/tmp/carleman-dirichlet-full.log` 实际包含 `Build completed successfully (3554 jobs).` 和 `Axiom audit passed for all 4294 Carleman declarations.`。

已独立通过 GitHub connector 核实 [main CI 39153888300 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39153888300/attempts/1)：main/push，head SHA 正确，completed/success。lean（117752977639）、state-check（117752977792）、dashboard / snapshot（117753640152）三个 jobs 均 success；Lean pin、root 构建、checked source 记录和两份证据上传步骤均成功。同 run 的 lean-ci-result artifact（12146670608）和 lean-declaration-evidence artifact（12145904119）均绑定固定 SHA。

已实际读取 `/tmp/carleman-dirichlet-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=fa61af9d4b260cac83d599ef4e228af88f67aee8`，targets 为 Carleman，`finished_at=2026-10-18T18:24:48.121358+00:00`，CI URL 与上述 run/attempt 完全一致，Lean/mathlib pin 正确。

远端原始 `/tmp/carleman-dirichlet-main-axioms/axioms.txt` 与固定本机 `/tmp/carleman-dirichlet-local-axioms.txt` 已逐字节比较，完全相同：**1,225,863 bytes**，SHA256 **`aa6d492cb18ff22b91168a64881a43f85566943b40e7ba0ef20ff4df1fa69fa3`**。另逐名复核远端 27/27 实际类型与允许公理集合，确认末行实际为 **`Axiom audit passed for all 4294 Carleman declarations.`**，没有 sorryAx 或未批准数学公理。C055、T039 与交付 JSON 的 27 项顺序一致，未混用后续源码或产物。

## 验收决定

**C055：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 本次固定版本 27 项未发现数学、量词、代表、全空间可积性、弱测试或拓扑混淆缺陷。同 SHA 的完整类型、递归公理和正式 main CI 均已独立核实。节点 H¹₀ 成员与 Poincaré／Dirichlet 形式等义务仍待证明，完整原文计数保持 12/26。

本次仅写本报告，没有修改数学源码、台账、覆盖表、原稿或 root 导入，没有 commit/push。
