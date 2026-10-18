# T037 / C053 独立本机验收

- `checked_sha`: `6923ae3b24d9590bd0afb4e66830b30fe49165d3`
- `base_commit`: `885add73e59dd08e5609597cac3c2ddd7fd395bd`
- `reviewed_at`: `2026-10-18T17:54:03+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：面匹配单纯形上的实际全局节点插值、闭区域连续性、真实 L2 类及其从点态函数出发的线性算子。**不提升 Proposition 6.1 / P011 或任何具名原文结果；论文完成计数保持 12/26。**

本次独立读取固定提交导出的三个新模块、全部 30 项实际展开类型及相关数学依赖，对照原 `paper/main.tex` Section 6 的 conforming P1 空间与节点插值使用，另核对固定 C053/T037 台账和阶段规格。没有用执行者说明或构建成功代替数学检查，后续工作区草稿不属于本报告。

## 全部 30 项声明

下表完整名称均以 `Carleman.` 开头，位置均为固定提交的 `Carleman/Spatial/` 文件。顺序与 C053/T037 及声明交付清单一致。表中 PASS 是逐项语义结论。

| # | 声明（省略 Carleman.） | 位置 | 独立核对结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.FaceMatching` | `SimplicialNodalGluing.lean:17` | PASS；真实交集包含于共同顶点凸包的几何条件，没有直接假设函数一致。 |
| 2 | `SimplicialPartition.localNodal` | `SimplicialNodalGluing.lean:21` | PASS；实际 f 在本单元顶点的值送入已构造的重心仿射插值。 |
| 3 | `SimplicialPartition.localNodal_vertex` | `SimplicialNodalGluing.lean:24` | PASS；本单元全部节点精确保持。 |
| 4 | `SimplicialPartition.localNodal_agree` | `SimplicialNodalGluing.lean:28` | PASS；共同顶点一致经仿射包扩张，得到整个单元交上一致。 |
| 5 | `SimplicialPartition.nodalFunction` | `SimplicialNodalGluing.lean:41` | PASS；覆盖内选一真实局部插值，覆盖外取零，定义域为点态函数。 |
| 6 | `SimplicialPartition.nodalFunction_on_cell` | `SimplicialNodalGluing.lean:45` | PASS；任意单元上的值等于该单元插值，消除选择依赖。 |
| 7 | `SimplicialPartition.nodalFunction_vertex` | `SimplicialNodalGluing.lean:52` | PASS；所有单元顶点包括共享顶点均保留原 f 值。 |
| 8 | `SimplicialPartition.nodalFunction_continuousOn` | `SimplicialNodalGluing.lean:60` | PASS；有限闭单元覆盖 closure S，逐片仿射连续经闭覆盖拼接。 |
| 9 | `SimplicialPartition.nodalFunction_reproduces` | `SimplicialNodalGluing.lean:69` | PASS；任意真实仿射函数在 closure S 上精确再现。 |
| 10 | `affinePolynomialCoefficients` | `SimplicialNodalLp.lean:13` | PASS；常数系数 p(0)，线性系数为线性部分在真实坐标基上的值。 |
| 11 | `affinePolynomialCoefficients_apply` | `SimplicialNodalLp.lean:16` | PASS；对全部 x 精确展开为 c0+Σcj*xj。 |
| 12 | `SimplicialPartition.nodalBound` | `SimplicialNodalLp.lean:31` | PASS；有限全部单元顶点绝对值之和，仅为粗可积性界。 |
| 13 | `SimplicialPartition.nodalBound_nonneg` | `SimplicialNodalLp.lean:34` | PASS；有限和各项非负。 |
| 14 | `SimplicialPartition.nodalBound_vertex` | `SimplicialNodalLp.lean:37` | PASS；任一节点值由两次有限和单项比较控制。 |
| 15 | `SimplicialPartition.nodalFunction_bound` | `SimplicialNodalLp.lean:46` | PASS；覆盖内用局部稳定，外部零值也满足粗界。 |
| 16 | `SimplicialPartition.nodalFunction_memLp` | `SimplicialNodalLp.lean:58` | PASS；实际连续性给限制测度下强可测，有限测度与粗界给 MemLp 2。 |
| 17 | `SimplicialPartition.nodalLp` | `SimplicialNodalLp.lean:64` | PASS；以已证 MemLp.toLp 构造实际 L2 等价类。 |
| 18 | `SimplicialPartition.nodalLp_ae` | `SimplicialNodalLp.lean:68` | PASS；仅按正确的 a.e. 意义识别该类的代表与点态插值。 |
| 19 | `SimplicialPartition.nodalLp_piecewise_affine` | `SimplicialNodalLp.lean:71` | PASS；属于实际 piecewiseAffineSpace；未把该结论写成 H1/零迹或 conformingSpace 成员。 |
| 20 | `SimplicialPartition.nodalFunction_congr` | `SimplicialNodalOperator.lean:14` | PASS；节点值相同给全函数相同；没有把输入 a.e. 相同误作节点相同。 |
| 21 | `SimplicialPartition.nodalFunction_add` | `SimplicialNodalOperator.lean:23` | PASS；全空间逐点加法，含覆盖外零值。 |
| 22 | `SimplicialPartition.nodalFunction_smul` | `SimplicialNodalOperator.lean:32` | PASS；任意实标量的全空间逐点线性。 |
| 23 | `SimplicialPartition.nodalFunctionLinearMap` | `SimplicialNodalOperator.lean:41` | PASS；点态函数空间到同一函数空间的真实 LinearMap。 |
| 24 | `SimplicialPartition.nodalFunction_unique` | `SimplicialNodalOperator.lean:47` | PASS；与节点相同的实际逐单元仿射 g 在每个单元相等，未声称覆盖外唯一。 |
| 25 | `SimplicialPartition.nodalFunction_idempotent` | `SimplicialNodalOperator.lean:61` | PASS；节点保持加节点依赖给全函数幂等。 |
| 26 | `SimplicialPartition.nodalFunction_abs_le` | `SimplicialNodalOperator.lean:68` | PASS；closure S 上的节点上界以常数 1 传给插值值。 |
| 27 | `SimplicialPartition.nodalLp_congr` | `SimplicialNodalOperator.lean:78` | PASS；节点相同经实际 a.e. 代表识别得到 L2 类相同。 |
| 28 | `SimplicialPartition.nodalLp_add` | `SimplicialNodalOperator.lean:86` | PASS；以 Lp.ext、各 toLp 代表及 Lp 加法 a.e. 公式证明。 |
| 29 | `SimplicialPartition.nodalLp_smul` | `SimplicialNodalOperator.lean:95` | PASS；以实际代表及 Lp 数乘 a.e. 公式证明。 |
| 30 | `SimplicialPartition.nodalLpLinearMap` | `SimplicialNodalOperator.lean:104` | PASS；定义域是点态实函数，值域是真实 L2(volume.restrict S)，未声明 L2 定义域或连续算子。 |

## 面匹配与共享面一致

M 的每个单元是非退化 d-simplex 顶点的真实凸包。`FaceMatching` 要求 `Ki∩Kj ⊆ convexHull(common vertices)`，而非要求两插值已相等。共同顶点的凸包反向包含于两个凸单元，故此输入确实表达交为共同顶点所生成的面；没有依据相近顶点、单元编号或 a.e. 重叠来判定共享节点。

`localNodal` 从同一个实际全局函数 f 取点值。同一个几何点即使有不同单元局部编号，取到的 f 值仍相同；`localNodal_agree` 明确使用两个 range 成员见证把这一点代入节点保持等式。两个真实 AffineMap 在共同顶点集上相等，因此在其仿射包上相等；共同顶点凸包包含于仿射包，再用 FaceMatching 得全部交上一致。已读取固定 mathlib 的 `AffineMap.eqOn_affineSpan` 实际陈述和证明，空共同顶点集也被正确处理。

`nodalFunction` 的选择条件只依赖 x 和几何 M。`nodalFunction_on_cell` 使用上述交上一致，证明选中单元与任意给定成员单元的值相同；不是默认 classical choice 恰好选了指定单元。局部节点保持因而提升为全局节点保持，没有对共享面点或边界点做 a.e. 忽略。

## 闭覆盖连续与边界范围

有限性 `[Fintype ι]` 是连续性定理的显式要求。既有 `cells_union` 从单元 inside、覆盖 S 及有限闭并得 `⋃i Ki=closure S`。每个实际局部仿射映射因空间有限维而连续；通过 `nodalFunction_on_cell`，全局函数在每个闭单元上的限制连续。固定 mathlib 的 `LocallyFinite.continuousOn_iUnion` 对有限从而局部有限的闭覆盖适用，准确输出 `ContinuousOn ... (closure S)`。

这并不声称覆盖外零延拓在整个环境空间连续。若边界节点非零，零延拓可能跨边界不连续；当前类型没有作该错误断言。仿射再现也仅声称 closure S 内，覆盖外全局定义取零不会被误认为再现任意仿射 p。

底层逐点线性、节点依赖和幂等不要求有限索引；它们只展开同一几何选择及一个 simplex 的有限重心和。有限性在闭覆盖、节点粗界、Lp 与统一节点稳定处公开。空索引时覆盖迫使 S 为空，相关闭区域结论为空集上的结论；d=0 仍有单节点 simplex，公式无除零或维数下限问题。

## 实际 L2 类与分片仿射成员

输入 f 可以是任意真实点态实函数；它不必本身可测或连续，因为输出仅依赖有限节点值并已独立证明连续。`nodalBound` 把各单元各节点绝对值求和，共享节点可以重复计数；该有限非负数只用来给 `MemLp.of_bound` 一个有限界。它可能随节点数量与 f 改变，没有被作为网格统一稳定常数。

`nodalFunction_memLp` 显式要求 `MeasurableSet S` 和 `IsFiniteMeasure (volume.restrict S)`。由 closure S 上连续缩到 S，得到限制测度下的实际 a.e. 强可测性；与粗界组合产生 MemLp 2。`nodalLp` 才用该证明形成 toLp，`nodalLp_ae` 给合法 a.e. 代表等式，未断言所选 Lp 代表在全部节点保留原 f 值。

`affinePolynomialCoefficients` 通过实际 Euclidean 坐标基和仿射映射的线性部分，证明完整常数加坐标和公式，包括 d=0 的常数情形。成员证明为每个单元选取其真实 `localNodal` 的系数，再用点态单元公式与 toLp 的 a.e. 等式，调用既有双向 `mem_piecewiseAffineSpace_iff_on_cells`。该依赖的 a.e. 存在唯一归属由 M 的真实覆盖、内部不交及零测边界提供，没有把重叠边界上多个 indicator 的和误作单片函数。

正式结论只进入 `piecewiseAffineSpace`，不是它与某个给定 V 的交。有限测度仍是输入，没有把它或 Sobolev/Dirichlet 成员冒充为本阶段新证明的结果。S 不必在此被假定为开集；Lp 结论均相对于 `volume.restrict S`，不能由其 a.e. 等式自行恢复边界或节点信息。

## 线性、唯一性、幂等及常数 1

函数线性展开选中单元的有限重心和；同一个 x 的选择与 f 无关，所以加法与数乘都在同一单元计算。覆盖外双方均为零。点态 LinearMap 不需要 FaceMatching；FaceMatching 在全局连续性、节点保持及与各单元一致处另行使用。这种分离与实际声明一致。

唯一性假设是实际点态 g 在每个单元上与某个真实 AffineMap 相等，并在所有节点与 f 相同。对给定单元，用该仿射 p 的节点值再现定理得到插值=p，再由逐点 EqOn 得插值=g。结论仅在该单元内；有限覆盖时可覆盖 closure S，不能推导覆盖外的 g 也等于零。没有把“a.e. 分片仿射 Lp 类”直接当成可以取节点值的 g。

幂等性用已证全局节点保持，再应用只依赖节点的函数同一性，得到 `I(I f)=I f` 的整个点态函数等式，覆盖外的零值也一致。这里没有声称 `nodalLp` 自复合幂等：它的值域是 Lp，定义域是点态函数，当前接口没有从 Lp 到节点值的反向映射。

`nodalFunction_abs_le` 从 closure S 选一单元，直接应用局部稳定：每个重心坐标非负且和为 1，故若所有节点绝对值≤C，则插值绝对值≤C。常数精确为 1，无节点数、维数、形状或直径系数；该证明没有使用前述粗和界。C 不必另假设非负：当结论的 x 存在时，可选单元及其节点假设已足够。声明是节点上界的点态稳定性，不是一个已经构造的 L∞ 或 L2 定义域算子的范数界。

Lp 的加法、数乘和节点依赖用 `Lp.ext`，同时合并相关 toLp 代表及 Lp 运算的 a.e. 等式证明。`nodalLpLinearMap` 的实际展开类型明确为 `(SpatialCoordinates d→ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict S)`。没有从任意 Lp/H1/H2 等价类读取点值，也没有仅凭输入 a.e. 相同就断言输出相同；没有声称该线性映射在某个未给拓扑的定义域上连续。

## 原文映射与剩余义务

原 Section 6 使用 `Vh={v∈H₀¹: v|K∈P1}`，并在 Step 2 由 d=2,3 的 H2→C0 连续代表定义节点插值。本批给出了有限面匹配网格上的全局点态拼接及真实 L2 实现，符合节点插值构造中这部分几何和代数内容。

尚未证明的内容包括：具体网格及 FaceMatching、统一形状正则和原分级条件、H2 连续代表与等价类上的合法节点赋值、输出 H1/弱梯度成员、零迹和边界保持、进入原 H₀¹ conformingSpace、局部 h/h² 误差、梯度逆估计、加权投影稳定性、超逼近及原连续热 CE。常数 1 的节点稳定不能替代这些结果。因此 C053 必须保持 AUXILIARY；不能提升完整 N3/N4、Proposition 6.1 或物理观测/控制覆盖。

## 固定依赖、构建和公理

已读取 T036 固定基线验收，并直接复核本次用到的 SimplexNodalInterpolation、SimplicialPartition、SimplicialCells 和实际分片仿射空间构造。最终模块导入闭包为 31 个 Carleman 模块，28 个旧模块相对基线逐字节未变，新增恰为本次三模块，均由固定 `Carleman.lean` 显式导入。原稿、治理协议、MATH_SPEC、Lean/mathlib pin 和 CI 工作流未变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

检查的 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，实际使用的闭覆盖拼接及仿射包一致性源文件无本地修改。固定 `CheckAxioms.lean` 对本次 30 项均有类型与公理输出，并遍历所有经 `privateToUserName` 归属 Carleman 的公开/私有声明，递归 `collectAxioms`，仅准许 `propext`、`Classical.choice`、`Quot.sound`。

本机 `/tmp/carleman-global-nodal-full.log` 实际记载 `Build completed successfully (3538 jobs).`。固定本机 `/tmp/carleman-global-nodal-local-axioms.txt` 为 1,193,753 bytes，SHA256 为 `f985837e1bce3a9af207044e950703ccbf9a37e5d9e0fa59e24ccbaa5c61533c`。30/30 项实际展开类型与源码一致，各项公理均仅为上述三项正常基础公理。末行实际为 `Axiom audit passed for all 4111 Carleman declarations.`，无 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实 [main CI 39151180933 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39151180933/attempts/1)：固定 head SHA、main/push、completed/success；state-check（117745166082）、lean（117745166453）、dashboard / snapshot（117745752501）三个 jobs 均成功。Lean job 的 pin、root target 构建、checked source 记录和声明/公理证据上传步骤均 success。同次 `lean-ci-result` artifact（12145496679）与 `lean-declaration-evidence` artifact（12145675773）均绑定该 run 和固定 head SHA。

原始 `/tmp/carleman-global-nodal-main-ci/result.json` 已实际读取，状态 PASS，`checked_sha=source_head_sha=6923ae3b24d9590bd0afb4e66830b30fe49165d3`，target=Carleman，`finished_at=2026-10-18T17:49:51.670221+00:00`；Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码一致。

正式远端 `/tmp/carleman-global-nodal-main-axioms/axioms.txt` 为 1,193,753 bytes，SHA256 为 `f985837e1bce3a9af207044e950703ccbf9a37e5d9e0fa59e24ccbaa5c61533c`；已实际逐字节比较，与固定本机副本完全相同。再次逐名核对远端 30/30 项完整类型及三项标准基础公理集合，确认全局 4111 声明递归审计 PASS。没有使用其他提交的产物替代本次证据。

## 验收决定

**C053：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 本次 30 项未发现需要修复的数学、类型、代表、边界或量词缺陷。该结论覆盖固定版本的面匹配全局连续节点插值与真实 L2 线性算子，不覆盖尚未证明的 H1、零迹、H2 连续代表或误差估计；原文完成仍为 12/26。

本次只写本报告，未修改数学源码、台账、覆盖表、原稿或 root 导入，未 commit/push。
