# T063 / C079 独立本机验收

- `checked_sha`: `36278e60193f3453a60bcdf33ef089ace1398350`
- `base_commit`: `699fd4292136039b671d27e09f6e5758a1083f2a`
- `semantic_checked_at`: `2026-10-18T21:33:51+00:00`
- `reviewed_at`: `2026-10-18T21:35:40+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。真实全域节点残差的值和实际 fderiv 加权平方积分界，完整 V_h 原状态的节点/弱梯度识别，以及加权节点测试属于真实 H¹₀ 一致空间。左端残差本身的弱 H¹ 身份、ℓ⁻¹ 项及投影组合仍待；完整原文覆盖保持 12/26。

本 Agent 直接读取固定 SHA 的六模块、全部 13 项完整类型和证明、关键依赖及原 `paper/main.tex` Step 3，对照 `governance/analysis/T063-global-nodal-errors.md`。未以执行者说明、旧报告或 CI 成功替代语义验收。工作树后续 NodalResidualSobolev、SupportedLipschitzProduct、FullWeakNodalResidual 不纳入本次检查。

## 全部 13 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定 SHA 的 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.integrable_of_cells` | `Spatial/SimplicialProductResidual.lean:15` | PASS；一般 NormedAddCommGroup 值函数的有限单元并可积性，经真实覆盖限制到 S。 |
| 2 | `SimplicialPartition.nodalProductResidual` | `Spatial/SimplicialProductResidual.lean:20` | PASS；实际函数 e=w·N(f)−N(wf)，没有自由残差场。 |
| 3 | `SimplicialPartition.localNodal_weighted_interpolant` | `Spatial/SimplicialProductResidual.lean:23` | PASS；真实节点再现把局部 w·p 的插值精确识别为 localNodal(wf)。 |
| 4 | `SimplicialPartition.nodalProductResidual_on_cell` | `Spatial/SimplicialProductResidual.lean:30` | PASS；整个闭单元上全局残差等于实际局部残差，含共享边界。 |
| 5 | `SimplicialPartition.nodalProductResidual_fderiv_ae` | `Spatial/SimplicialProductResidual.lean:38` | PASS；内部邻域函数相等加零测边界给实际 fderiv 的单元 a.e. 身份。 |
| 6 | `SimplicialPartition.nodalFunction_fderiv_on_cell_ae` | `Spatial/SimplicialProductResidual.lean:51` | PASS；真实全局节点函数和局部仿射函数导数 a.e. 相等。 |
| 7 | `SimplicialPartition.squaredNodal_integrability` | `Weights/SquaredNodalIntegrability.lean:13` | PASS；残差值/导数及状态值/导数四种加权平方被积函数均真实可积。 |
| 8 | `allowedSquaredWeight_nodal_cell_integrals` | `Weights/SquaredNodalCell.lean:12` | PASS；真实 cellDiameter、实际残差/状态积分，把已证局部估计精确转为全局函数在该单元上的估计。 |
| 9 | `allowedSquaredWeight_nodal_global_integrals` | `Weights/SquaredNodalGlobal.lean:12` | PASS；精确积分求和给 h⁴、h² 误差及 q⁴/q² 原能量，无单元个数因子。 |
| 10 | `SimplicialPartition.nodal_representation_weak_gradient` | `Spatial/FullNodalGradient.lean:15` | PASS；任意实际 H¹ jet 的 scalar 节点表示内部推出完整原弱梯度与节点函数实际导数 fiber 的 a.e. 身份。 |
| 11 | `SimplicialPartition.conforming_dirichlet_nodal_with_gradient` | `Spatial/FullNodalGradient.lean:31` | PASS；任意完整 V_h 状态内部取得同一个零边界节点代表、scalar 身份和完整梯度身份。 |
| 12 | `SimplicialPartition.weighted_nodal_mem_dirichletConformingSpace` | `Spatial/FullNodalGradient.lean:42` | PASS；真实边界节点乘任意标量权后仍为零，通过已有 H¹₀ 密度结论得到完整一致空间成员。 |
| 13 | `allowedSquaredWeight_full_nodal_residual` | `Weights/FullNodalResidual.lean:13` | PASS；对任意完整 V_h 的实际 H¹ jet，提供加权节点测试及两种全域残差积分界，右端为该原状态的真实 scalar/弱梯度 L² 代表。 |

## 原文对应、几何与量词

原 `paper/main.tex:1469–1485` 的空间是完整 `V_h={v∈H¹₀(Ω):v|K∈P₁}`。本批入口的 `conformingSpace (dirichletSubspace S)` 已检查为真实分片仿射 L² 像与真实 H¹₀ scalar 像的交；`mem_conformingSpace_iff` 双向给出各单元 a.e. 仿射多项式表示。H¹₀ 使用所有真实紧支 C∞ 测试在 H¹ 图拓扑中的闭包，未改成点值边界条件或预设节点子空间。

原 Step 3 在 `paper/main.tex:1569–1593` 取残差 σ²z_h−I_h(σ²z_h)，需要 `9.26-eq10` 的梯度和 ℓ⁻¹ 项、`9.26-eq11` 的零阶项，以及节点测试在 V_h 中，再与投影/逆估计组合得到 `eq:testsuper`。本批的 e 正是这一残差的实际节点代表，且证明了测试成员性和两种积分界。它没有把左端 fderiv 积分直接改称弱梯度范数；完整 eq10/eq11/testsuper、时间算子身份和一般 H² 插值并未在本批完成，故 AUXILIARY 范围正确。

固定 d、开凸 S、紧闭包、闭域 C² profile ρ 和 κ≥0 后，∃C>0 在索引类型 ι、Fintype、网格 M、q、τ、η、内球 a/r、节点数据 f 或完整状态 u 之前。C 可以依赖 d、S、ρ、κ，不依赖单元数、网格大小、时间值、指数 τ、符号或状态。最终显式有限测度实例不增加实质域限制：紧闭包已保证限制体积有限。

实际 `allowedSquaredWeight` 是 `(q^τ exp(qηρ))²`，不是替代权；已有 actual TimeWeight 乘子平方身份接到同一权。所有 q≥1、τ∈ℝ、|η|=1 均保留，涵盖两种符号。闭域 C² 比原光滑 profile 所需更弱，无边界外可微前提。这里是固定时刻的空间结论，常数选择先于任意 q 和 τ，未引入 T 依赖，也没有声称已经建立最终时间测试算子。

`SimplicialPartition` 使用真实满维非退化单纯形、S 的覆盖、单元位于 closure S 和内部两两不交。FaceMatching 是交集包含在共有几何顶点凸包中的实际条件；BoundaryFitted 是单元边界部分由其边界顶点生成，符合原边界贴合的一致网格。内球 B(aᵢ,rᵢ)⊆Kᵢ、rᵢ>0、diam(Kᵢ)≤κrᵢ 保留为显式形状条件，未假设误差结论。h 是有限个真实 Metric.diam 的 NNReal 上确界，不是自由尺度；hq≤1 与原后续选择 δ_num≤1 的辅助阶段一致。

## 真实残差、导数和可积性

N(f) 的定义在覆盖内选择一个实际 localNodal 仿射函数，覆盖外取零。FaceMatching 及共有顶点相同数据证明选择无关，得到闭单元上的精确值身份和 closure S 上连续性；未用闭单元指示函数求和而在共享边界重复计算。

局部 p=N(f)|K 在每个顶点准确等于 f(vᵢ)，所以局部 w·p 的节点插值就是 N(wf)|K。由此残差闭单元身份成立。在单元内部，存在真实开邻域，所有邻近点均满足该值身份，因此 `EventuallyEq.fderiv_eq` 给实际全空间 fderiv 的相等；真实 simplexCell_ae_interior 去除零测骨架。第一条导数身份即使 w 任意也合法，因为它只比较同一函数芽；在应用中闭域 C² 的平方权和实际乘积规则进一步保证内部确实可微，不靠不可微时 fderiv 的默认值取得估计。

四项可积性分别落实：w 正且在闭域连续，N(f)、N(wf) 在闭域连续，故 e²/w 与 wN(f)² 在紧单元上连续可积。导数项利用闭域 UniqueDiff、C² 权的 fderivWithin 连续性，构造真实局部字段 G=wDp+pD_within w；G−DI 的 Euclidean fiber 范数平方除以 w 连续可积，再经两条 a.e. 导数身份得到实际全局残差 fderiv 的积分可积性。状态导数项同样等于局部仿射恒定导数的权平方密度。有限单元并和覆盖把这些可积性传到 S，未把未证明可积的积分默认为零，也未声称骨架上经典可微。

## 精确求和与原能量

单元估计从已证 `allowedSquaredWeight_local_residual_integrals` 出发。四个积分——残差值、残差梯度、状态值、状态梯度——分别通过真实值或导数 a.e. 身份替换；没有遗漏任何权因子。cellDiameter≤maxDiameter 与 q≥1 保证每个局部 h_K q≤1；局部能量是 `q⁴∫K wN(f)² + q²∫K w|DN(f)|²`。

已检查 `integral_eq_sum_cells` 的证明：a.e. 唯一单元使实际 f 等于单元指标函数的有限和；可积性允许交换有限求和与积分。开凸域保证单元内部包含于 S，零测单元边界给 `(volume.restrict S).restrict K = volume.restrict K`，闭单元积分不会重复计算边界或引入域外部分。

各局部能量非负，因而 h_K⁴≤h⁴、h_K²≤h² 可以合法逐项放大；常数 C 提出求和后，能量和精确等于全域能量。最终是

`∫S e²/w ≤ C h⁴ [q⁴∫S wN(f)² + q²∫S w|DN(f)|²]`，

`∫S |De|²/w ≤ C h² [q⁴∫S wN(f)² + q²∫S w|DN(f)|²]`。

没有取单元能量最大值再乘单元数，也没有平方求和引出的数量因子。证明不除以 h 或能量；空网格、空域和零状态仍覆盖。d=0 没有被排除，空梯度 fiber、零直径及有限和的相应退化不要求不存在的单位方向。

## 完整状态和真实 H¹₀ 节点测试

`conforming_dirichlet_nodal_with_gradient` 从任意 jet u 的 scalar 属于完整 V_h 出发。所用既有节点表示证明先取真实 H¹₀ jet，逐单元的实际弱梯度给有界全域弱梯度，真实零延拓和弱导数定理给全空间连续 Lipschitz 代表。其单元 a.e. 仿射身份经连续性成为整个闭单元上的身份；域外零延拓加连续性给边界节点为零。因此这里不是新增“状态已经有节点表示”假设。该代表构造中的辅助 Lipschitz 界可以依赖网格和状态，但不会进入已经在所有这些对象之前选好的误差常数 C。

对给定 u 与此 scalar 身份，新梯度引理限制 u 到每个开单元，用真实弱导数唯一性将其各方向分量识别为局部仿射的实际导数，再经零测边界和 a.e. 单元覆盖汇总。`derivativeOneFiber` 已核对为在真实 Euclidean 基上的 CLM 方向导数向量，索引 Sym(Fin d,1) 与 Fin d 一一对应；这里比较的是完整 Euclidean 梯度 fiber，不是任意能量或抽象场。

最后入口用 scalar Lp 的 a.e. 代表身份和上述完整弱梯度身份，把右端两项积分精确换回原 u 的 value 和 field 1。因此右端确为原实际 H¹ 状态的加权能量，且由已证可积性与 a.e. 身份保证可积。它覆盖任意同 scalar 的合法弱 jet，而不是只覆盖构造时选出的某个 jet。

加权节点数据 wf 在每个边界节点仍为零；`weighted_nodal_mem_dirichletConformingSpace` 调用真实零边界节点成员定理。已检查该依赖通过向内收缩、光滑卷积和完整 H¹ 收敛进入紧支光滑测试闭包，再与真实分片仿射成员性交合。没有把“边界节点为零”本身当作 H¹₀ 定义，亦没有把任意连续函数直接断言为 H¹。该步骤只需有限顶点上的权值，故允许任意点态 w 是正确的更强辅助结论。

## 版本、构建及递归公理

六新模块的 Carleman 导入闭包共 173 个模块，其中 167 个既有模块相对 base 逐字节不变；root 明确导入全部六模块。重点读了 SquaredCellIntegral/Gradient、SimplicialIntegrals、SimplicialLocalGradient、AffineWeakGradient、FullConformingNodal、ConformingLipschitzRepresentative、NodalDirichletMembership、SimplicialNodalGluing、FirstOrderSobolevJet、DirichletSpace 等实际依赖，而非仅引用旧验收结论。

AGENTS、流程规则、原论文、工具链 pin 及 CI 流程相对 base 未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。公理审计程序仅增加本批 13 项显式类型/公理打印；实际遍历所有 Carleman（含内部生成）声明、递归 collectAxioms 并拒绝白名单外项的代码未改。

实际固定 `/tmp/carleman-global-nodal-errors-full.log` 含 `Build completed successfully (3647 jobs).`。固定 `/tmp/carleman-global-nodal-errors-local-axioms.txt` 中 13 项完整类型均与源码一致；13 项递归公理仅有正常 `propext`、`Classical.choice`、`Quot.sound`。全部 1401 项不同显式打印的递归公理集合扫描也通过，末行确认全部 4965 个 Carleman 声明审计通过，无 sorry 或额外数学公理。

固定本机产物为 1,450,756 bytes，SHA256 `c721ef8c1895adf52059e34d8340a72c2f3f3ae5be497365b5aaba1b25e0cf13`。Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据和签发状态

已独立读取真实 [main/push run 39168240151](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39168240151/attempts/1)，attempt 1，head SHA 精确匹配本次 checked SHA，顶层 completed/success。三项 jobs 均 completed/success：lean `117795636024`、state-check `117795636326`、dashboard / snapshot `117796232523`。Lean 的实际构建、记录源版本、上传两种证据及收尾步骤均 success。

已独立读取同次 artifact 元数据：`lean-ci-result` id `12151393493`、`lean-declaration-evidence` id `12151517950` 均绑定该 run/main/同一 head SHA。实际读取 `/tmp/carleman-global-nodal-errors-main-ci/result.json`，status=PASS，checked_sha/source_head_sha 均为 `36278e60193f3453a60bcdf33ef089ace1398350`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T21:33:33.764593+00:00`，target 为 `Carleman`。Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均匹配。

实际读取 `/tmp/carleman-global-nodal-errors-main-axioms/axioms.txt` 并与固定本机产物逐字节比较，完全相同：1,450,756 bytes，SHA256 `c721ef8c1895adf52059e34d8340a72c2f3f3ae5be497365b5aaba1b25e0cf13`。远端产物再次核对全部 13 项完整类型及递归公理，并扫描全部 1401 项不同显式打印声明的公理集合，只有正常基础公理；末行确认全部 4965 项递归审计通过。

最终结论：**T063 / C079 PASS，可将 C079 升为 REVIEWED，保留 AUXILIARY。** 13 项和所声称范围通过，未发现数学缺陷。残差弱 H¹、ℓ⁻¹ 项、Lp 乘子范数及投影组合仍待，完整原文覆盖保持 12/26。本 Agent 仅写本报告，未修改证明、台账、root 或原稿，未 commit/push。
