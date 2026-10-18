# T044 / C060 独立本机验收

- `checked_sha`: `50ea3111057c5d7b796cca799c10a9a900d14caf`
- `base_commit`: `28e1f4df08f31b4337f32bd20b61dbe566762f15`
- `reviewed_at`: `2026-10-18T19:15:30+00:00`
- `result`: **PASS**；C060 可升 REVIEWED，范围保持 AUXILIARY
- `axiom_check`: **PASS**；固定本机与同次远端原始产物逐字节一致
- `scope`: **AUXILIARY**
- 范围：真实紧支 Lipschitz 函数的强 H¹ 光滑卷积逼近、任意阶全空间弱 jet 的域限制，以及零边界节点函数的实际 H¹₀ 和一致分片仿射空间成员。**本阶段清偿节点 H¹₀ 成员，不提升 Proposition 6.1 或其他完整原文结果，原文完成仍为 12/26。**

独立读取固定五模块全部证明、30 项实际展开类型、相关旧依赖及原 `paper/main.tex` Section 6。阶段规格和执行者说明仅用于定位；真实声明、证明依赖、a.e. 代表与完整图拓扑均另行核对。工作区后续局部节点 Lp 草稿不属于本次范围。

## 全部 30 项声明

名称均加前缀 `Carleman.`；位置相对于固定提交的 `Carleman/Spatial/`。顺序与 C060、T044 及交付声明清单逐项一致。以下全部结论已结合实际展开类型、递归公理审计和同次远端 CI 核实。

| # | 声明 | 位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SpatialTest.convolution_norm_bound` | `CompactConvolution.lean:15` | PASS；非负单位质量核的真实积分模界保留全局函数上界 B。 |
| 2 | `SpatialTest.convolution_lipschitz` | `CompactConvolution.lean:28` | PASS；两个实际可积卷积之差经积分模界控制，Lipschitz 常数不增加。 |
| 3 | `SpatialTest.convolution_tsupport_subset_thickening` | `CompactConvolution.lean:50` | PASS；Minkowski 支撑包含加闭包最小性给完整闭支撑的精确半径厚化包含。 |
| 4 | `SpatialTest.convolution_smooth` | `CompactConvolution.lean:60` | PASS；紧支 C∞ 核与真实连续、局部可积函数卷积，得到实际 C∞。 |
| 5 | `SpatialTest.convolution_compact` | `CompactConvolution.lean:64` | PASS；两个紧支函数卷积的真实闭支撑紧。 |
| 6 | `compactLipschitz_weakDerivative` | `CompactConvolutionDerivative.lean:13` | PASS；任意方向的弱导数是实际 fderiv L² 字段经 CLM 求值，不是假设的候选梯度。 |
| 7 | `compactLipschitz_convolution_fderiv` | `CompactConvolutionDerivative.lean:25` | PASS；对每个 x 的实际 CLM 值等式 `D(κ⋆f)=κ⋆Df`，弱交换、a.e. 同余和积分求值均合法。 |
| 8 | `shrinkingBump_radius_tendsto` | `CompactMollificationLimit.lean:14` | PASS；实际外半径 2/(n+1) 趋于零。 |
| 9 | `shrinkingBump_radius_le_two` | `CompactMollificationLimit.lean:19` | PASS；所有 n≥0 的外半径≤2，含首项。 |
| 10 | `compactMollification` | `CompactMollificationLimit.lean:25` | PASS；实际 spatialMollifier 与 f 的卷积定义。 |
| 11 | `compactMollification_smooth` | `CompactMollificationLimit.lean:28` | PASS；每项为真实 C∞ 函数。 |
| 12 | `compactMollification_compact` | `CompactMollificationLimit.lean:31` | PASS；每项具有实际紧支撑。 |
| 13 | `compactMollification_lipschitz` | `CompactMollificationLimit.lean:34` | PASS；每项保留原 Lipschitz 常数 C，统一于 n。 |
| 14 | `compactMollification_support` | `CompactMollificationLimit.lean:38` | PASS；闭支撑落在原 tsupport 的实际 rOut 闭厚化中。 |
| 15 | `compactMollification_tendsto` | `CompactMollificationLimit.lean:44` | PASS；每个 x 的函数值趋于原连续 f(x)。 |
| 16 | `compactMollification_fderiv_tendsto` | `CompactMollificationLimit.lean:49` | PASS；CLM 值 fderiv 的局部可积性与有界半径比给真实导数 a.e. 极限。 |
| 17 | `compactMollification_tendsto_H1` | `CompactMollificationLimit.lean:64` | PASS；内部供应共同紧支、统一值/Lipschitz 界及两类极限，得到完整 H¹ 图拓扑强收敛。 |
| 18 | `SpatialTest.toUniv` | `SobolevRestriction.lean:16` | PASS；同一个光滑紧支测试视作全空间测试，函数未改变。 |
| 19 | `IsWeakSpatialDerivative.restrictDomain` | `SobolevRestriction.lean:22` | PASS；通过真实限制 a.e. 身份和 S 外测试及其导数为零，保留全部方向和全部原测试弱身份。 |
| 20 | `derivativeComponent_restrict` | `SobolevRestriction.lean:49` | PASS；任意阶任意多重指标的实际 L² 分量与限制严格交换。 |
| 21 | `WeakSobolevJet.restrictDomain` | `SobolevRestriction.lean:58` | PASS；任意 m 的每个真实字段逐项限制，全部相邻阶弱身份内部证明。 |
| 22 | `WeakSobolevJet.restrictDomain_value` | `SobolevRestriction.lean:68` | PASS；零阶 value 精确等于原 value 的真实 L² 限制。 |
| 23 | `WeakSobolevJet.restrictDomain_tendsto` | `SobolevRestriction.lean:71` | PASS；各字段实际 L² 限制连续，保留完整图拓扑的序列极限。 |
| 24 | `restrictedJet_eq_test` | `SobolevRestriction.lean:81` | PASS；开域上由准确 value 身份及完整弱导数唯一性识别整个限制 jet 与原测试 jet。 |
| 25 | `compactLipschitzSobolevJet_value_ae` | `NodalDirichletMembership.lean:15` | PASS；通用紧支 Lipschitz jet 的标量类确实表示同一个 f。 |
| 26 | `compactLipschitz_mem_dirichletJetSpace` | `NodalDirichletMembership.lean:21` | PASS；紧支包含于开域给正缓冲，全部充分大光滑项为原测试，强 H¹ 极限给实际闭包成员。 |
| 27 | `SimplicialPartition.nodal_inward_mem_dirichletJetSpace` | `NodalDirichletMembership.lean:45` | PASS；每个具体内缩函数满足上项全部条件，真实限制 jet 属于 H¹₀。 |
| 28 | `SimplicialPartition.nodal_global_restrict_mem_dirichletJetSpace` | `NodalDirichletMembership.lean:58` | PASS；已证节点内缩强 H¹ 极限经限制及 H¹₀ 闭性传给同一原节点 jet。 |
| 29 | `SimplicialPartition.nodalLp_mem_dirichletSubspace` | `NodalDirichletMembership.lean:71` | PASS；实际 value 精确识别为原 nodalLp；空域用零受限测度直接处理，最终不要求非空中心。 |
| 30 | `SimplicialPartition.nodalLp_mem_dirichletConformingSpace` | `NodalDirichletMembership.lean:93` | PASS；同一个 nodalLp 的实际逐片仿射成员与新证 H¹₀ 成员组成真实交空间成员。 |

## 实际卷积界、光滑性和闭支撑

卷积使用真实 Lebesgue volume 和标量乘法连续双线性映射，不是命名为 mollifier 的自由算子。核 κ 是原 SpatialTest univ，故其实际 C∞ 函数紧支且可积。非负性把 |κ| 替换为 κ，单位质量使积分上界精确为 B 或 C·dist(x,y)。Lipschitz 证明先由紧支核和连续 f 的局部可积性证明每个点的两个卷积确实可积，才使用 integral_sub；随后 `dist(x−t,y−t)=dist(x,y)` 给非增常数 C。

独立的 convolution_norm_bound 类型允许任意点态 f，仅要求全局模≤B；这使用 mathlib 对总定义 Bochner 积分的合法模上界，并不自行声明任意此类 f 的可测性。所有本阶段 Sobolev 应用中 f 都是真正 Lipschitz 连续函数，其实际卷积可积性由上述紧支核论证供应，没有依赖不可积积分默认值来证明光滑化。B 不需另假设非负，因为全局模界在环境空间任一点已蕴含 B≥0；H¹ 极限调用处仍明确供应 hB0。

支撑证明先用真实 `support_convolution_subset`：非零卷积点 x=y+z，其中 κ(y) 和 f(z) 非零。核闭支撑位于 closedBall(0,r) 给 ‖y‖≤r，于是 dist(x,z)≤r，且 z∈tsupport f。再用闭厚化集合的闭性把点态 support 包含提升到整个 tsupport，未忽略卷积支撑的边界。光滑性由紧支核的实际卷积微分定理给出，紧支性由两紧支函数的卷积支撑定理给出；没有假设目标光滑函数已经存在。

## 实际 fderiv 的 CLM 值卷积身份

已直接复核 compactLipschitzDerivativeLp：它是实际 `fderiv ℝ f` 的 MemLp.toLp，非可微点处使用 fderiv 的标准定义。可测性、紧支外为零及 Lipschitz 导数范数界证明它在全空间 L²。Rademacher 给 volume-a.e. DifferentiableAt，真实 fderiv 因而与 lineDeriv 在任意方向 e 上一致。结合已证全空间 Lipschitz 积分分部，得到第 6 项的完整弱身份，测试族没有缩小。

第 7 项先将 κ⋆f 按真实卷积交换律和 a.e. 同余改写为 u⋆κ，其中 u 是原 f 的实际 L² 类。对于每个方向 e，v 是实际 CLM 导数类经求值的标量 L² 类，a.e. 等于 `Df(x)e`。已直接读取 `WeakConvolution` 的旧依赖：以真实反射核 κ(x−y) 作完整光滑紧支测试，其 y 导数为 `−Dκ(x−y)e`；弱积分分部的另一负号抵消，给正确的导数交换。紧支 C∞ 核的实际微分定理及可积性证明，再把交换式识别为真实 `fderiv(u⋆κ)(x)e`。

最后通过 scalar convolution 的 a.e. 同余，将 v 换成真实 `Df(·)e`。CLM 值 Df 已有局部可积性，紧支连续 κ 因而使 CLM 值卷积在每个 x 可积；`ContinuousLinearMap.integral_apply` 合法交换方向求值和 Bochner 积分。由所有 e 的相等得到完整 CLM 相等。结论对每个 x 成立，既不是只给自由候选梯度，也不是将 a.e. 梯度身份错误升为原函数处处可微。

## 从真实近似恒等到强 H¹

既有 shrinkingBump 的内半径为 1/(n+1)、外半径为 2/(n+1)，二者正且比值恒为 2；spatialMollifier 是此实际 bump 的 volume 归一化，非负和积分 1 均由实际构造证明。外半径趋零给每个连续 f 的卷积逐点极限。对 Df，已证明的全空间 L² 给局部可积性；固定 mathlib `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` 使用 Lebesgue 微分及有界半径比，给 Banach 值卷积的 a.e. 极限。

已读取该 mathlib 定理的实际类型与证明：目标只需完备实赋范空间，因此适用于真实 CLM 空间及其算子范数；源为有限维 Euclidean 空间，volume 满足加性 Haar 条件。没有只证明各坐标标量极限后未经论证声称算子范数收敛。通过前述每个 x 的真实导数卷积身份，得到光滑函数实际 fderiv 的 a.e. 极限。

强 H¹ 不是由此 a.e. 极限直接断言。所有卷积闭支撑共同位于 `cthickening 2 (tsupport f)`；Euclidean 空间的适当性与原紧支保证它紧且体积有限。原紧支连续函数给一个全局 B 界，每项通过单位质量保持 B；每项的 Lipschitz 常数仍为 C，故实际 fderiv 范数也统一≤C，支撑外函数和导数均为零。

直接复核 `compactLipschitzSobolevJet_tendsto` 及 `LpDominatedLimit`：分别对标量 L² 类和 CLM 值 L² 导数类使用共同支撑上的平方差支配 `1_K(2B)²`、`1_K(2C)²`。自然数序列的所有 toLp a.e. 身份经 ae_all_iff 置于共同 a.e. 集；主导收敛给平方差积分趋零，平方根给真正 L² 范数收敛。两个真实连续字段映射 scalarZeroFiber/derivativeOneFiber 随后给全部 Fin 2 字段强收敛，最后由 subtype 拓扑得到原 WeakSobolevJet 收敛。该图拓扑与真实 H¹ Hilbert 拓扑通过既有双向连续等价一致，包含零阶和完整一阶导数。

这些界统一于光滑化指标 n，但可依赖当前 f、C 及其支撑；没有宣称网格族、节点状态、维数或原误差估计的统一常数。C=0、f=0 和 n=0 都未被丢弃。

## 任意阶弱 jet 的真实限制

`restrictRegionLp` 是同一函数代表在 volume.restrict S 下由实际 MemLp 构造的 L² 类，范数≤原范数，其真实连续线性限制映射已证明。限制 a.e. 公式没有把原等价类变成处处规定的函数。

对任意域测试 φ，toUniv 保留同一全空间光滑紧支函数。将它代入原全空间弱身份后，φ 和实际方向 fderiv 在 S 外都为零：后者由不在 tsupport 的邻域恒零性质证明。因此两个全空间积分准确等于 S 上的积分，再用 restrictRegionLp_ae 给限制后的全部弱身份；没有遗漏边界项，也没有在节点函数上附加光滑性。该一般限制引理甚至不需要 S 开；最终唯一性和闭包使用处另有明确 hS。

derivativeComponent_restrict 对任意 k、任意 α 使用四个正确的 a.e. 等式证明精确 L² 类相等。restrictDomain 对任意 m 的每个原字段逐项限制，并对全部 k、α、i 使用原弱身份及该交换公式，构造真正的完整域内 jet；不是只限制零阶后假设梯度存在。value 等式恰为零阶分量交换。

restrictDomain 当前封装为函数，所证明的 restrictDomain_tendsto 是本证明所需的完整序列极限保持：逐字段通过实际 L² 限制 CLM 的连续性，再经有限乘积和 subtype 拓扑得到结果。没有把仅零阶 L² 限制连续性误作整个 jet 连续性。restrictedJet_eq_test 在开域上使用已证完整弱导数唯一性；同一 value 的 a.e. 身份足以识别整个 jet，是因为两边都已经是真正弱 jet，不是因为任意梯度可由名字确定。

## 两次闭包极限、空域及实际 P1 成员

对任意紧支 Lipschitz f，若 tsupport f⊆开 S，实际紧集与开补集分离给某 δ>0，使整个闭 δ 厚化仍包含于 S。已核对 mathlib 的缓冲定理。外半径趋零保证全部充分大的光滑卷积都满足 rOut<δ；准确闭支撑包含与已证光滑、紧支性质使每个这样的函数真正构成原 SpatialTest S。没有只要求点态非零支撑在域内，也没有错误地要求从 n=0 起的全部卷积都在域内。

这些光滑项的全空间真实 jet 限制后，借 restrictedJet_eq_test 与同一标量代表，严格等于它作为 SpatialTest 的原 sobolevJet，因而属于原 dirichletJetSpace。完整 H¹ 极限经限制后仍成立；dirichletJetSpace 是全部原光滑测试 span 的 H¹ 图拓扑闭包，已知闭性对最终成员足够。由最终处于闭集及真实极限，得到原 f 的限制 jet 成员。这一步已真正清偿紧含于 S 的紧支 Lipschitz 函数的 H¹₀ 光滑逼近，不是仅使用边界点态零值。

对节点函数，每个固定 r_n=(n+1)/(n+2)∈(0,1) 的实际内缩为 `f_node∘H_{r_n}^{-1}`。开凸域、中心 a∈S 及原闭支撑包含于 closure S，使其闭支撑严格落在 S；紧性和 Lipschitz 性由真实同胚复合证明。因此上一段适用于每个内缩，并不需要一个对全部 n 统一的正 δ。

第二次极限使用已验收且本次直接复核的 `nodal_inward_tendsto_H1`：有限零测骨架外，逆像点最终位于同一局部仿射或外部恒零邻域，实际链式导数为 r_n⁻¹A 并趋于 A；r_n⁻¹≤2、共同紧支 closure S 及值界给真实完整 H¹ 极限。连续限制与同一 H¹₀ 闭性遂将所有内缩成员传回原 nodalGlobalSobolevJet。两次极限的顺序清楚，没有未经证明交换两个参数极限，也不需要选择一个统一双参数光滑序列。

最终标量定理先区分 S=∅。该分支 volume.restrict∅=0，实际 nodalLp 由 Lp.ext 证明等于零，继而属于子空间；没有从空集选择中心。非空分支才取 a∈S，前述 jet 给实际 dirichletSubspace 的像成员见证。其 value 通过真实限制、nodalGlobalLp_ae 和原 nodalLp_ae 精确等于同一个已构造的 nodalLp，没有以另一个 a.e. 不相关插值代替它。

最后 `M.conformingSpace (dirichletSubspace S)` 展开为真实 piecewiseAffineSpace 与 dirichletSubspace 的交。已有 nodalLp_piecewise_affine 对同一 L² 类证明每单元上的实际仿射多项式 a.e. 公式，新结果供应 H¹₀ 成员，故最后的二元见证准确给原意的 H¹₀∩P1 成员。该定理没有另行证明全空间的节点基展开或具体网格的几何条件。

## 原文对应与公开条件

原 Section 6.1（`paper/main.tex:1469–1485`）在有界凸多面体上定义 `Vh={v∈H₀¹: v|K∈P1}`；Step 2/3 使用 Ih 及 `Ih(σ²zh)∈Vh`。本批在原真实空间上清偿零边界节点插值属于 H¹₀∩P1 这一基础成员事实。原 Section 6.2 的盒子与 Kuhn 重构同样需要零边界节点分片仿射函数的此类成员；本批可服务该目标，但尚未提供具体 Kuhn 网格实例。

最终公开输入为任意自然数维 d、有限真实非退化 d-simplex 分区（inside/cover/内部不交）、开凸 S、FaceMatching、BoundaryFitted，以及实际点态 f 在所有边界顶点取零。原 nodalLp 接口仍带 `IsFiniteMeasure (volume.restrict S)` 实例；有限紧单元覆盖已给 closure S 紧，且原目标域本来有界，故这不是新增几何限制，但该实例在最终实际类型中仍保留。最终两个标量成员定理不含 a∈S 或 Nonempty 条件。d=0 与零函数不存在除以维数或 C 的问题。

FaceMatching/BoundaryFitted 是真实几何输入，具体网格必须另行供应；本批不把它们当作已经自动从 grading 推出。输入 f 是真实点态函数、输出只依赖节点值，未在任意 Lp/H¹/H² 等价类上取点值。H² 连续代表及边界代表、反向 H² 椭圆正则性、形状正则/分级下的原局部 h/h² 误差、逆估计、加权投影稳定、超逼近和连续热 CE 均未由本批证明。没有 T、权族、状态或网格统一误差结论。因此 C060 保持 AUXILIARY；P011/P012/P014/P015 等完整原文覆盖不提升，仍为 12/26。`extra_hypotheses=[]` 只针对这个公开范围的辅助目标理解。

## 固定依赖、构建与公理

已读取 [T042 内缩与真实 H¹ 验收](T042-local-acceptance.md)、[T043 内缩强 H¹ 极限验收](T043-local-acceptance.md)，并直接检查其本次所用证明。也直接核对既有 FullSpaceInterpolation 的真实 bump、WeakConvolution 的反射测试交换、CompactLipschitzSobolev 的实际 fderiv、LpDominatedLimit 的两个字段强收敛、原 Dirichlet 闭包、ObservedRegionLp 的实际限制及 SimplicialPartition 的真实交空间，未仅依赖先前 PASS 标签。

五新模块的 Carleman 导入闭包共 113 模块，其中 108 个旧模块相对 base 逐字节未改；新增恰为本批五模块，固定 Carleman.lean 对它们均显式导入。原稿、治理协议、Lean/mathlib pin 和工作流未改，MATH_SPEC 仅增加本阶段说明；原稿 SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机实际 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净；已读取所用 bump 卷积收敛、积分模界和紧集厚化缓冲的固定源码。

固定 CheckAxioms 对 30 项逐一输出 `#check @...` 和公理列表，末尾通过 privateToUserName 遍历全部 Carleman 公开/私有声明、递归 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。30 项实际完整类型与源码、C060/T044 及交付清单一致，没有隐藏的目标 H¹ 极限、光滑逼近、H¹₀ 成员或梯度识别前提。

固定本机 `/tmp/carleman-nodal-dirichlet-local-axioms.txt` 为 1,277,288 bytes，SHA256 `d521952f796897ce790ea40d9321a68a8ab1bba8260677f57017e84354c92f62`。30/30 项的递归公理集合均恰为上述三项正常基础公理，末行实际为 `Axiom audit passed for all 4578 Carleman declarations.`。`/tmp/carleman-nodal-dirichlet-full.log` 实际记载 `Build completed successfully (3575 jobs).` 及同一全局审计 PASS，无 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实 [main CI 39157419093 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39157419093/attempts/1)：head SHA 为本次固定证明提交，main/push，run completed/success；`lean`（117763409751）、`state-check`（117763410003）、`dashboard / snapshot`（117764132240）三个 jobs 均 completed/success。Lean job 的 pin、构建证明、记录 checked source、保存 result 和保存声明公理证据步骤均成功。

同 run 的 `lean-ci-result` artifact 12147133159 与 `lean-declaration-evidence` artifact 12147416573 元数据均绑定该固定 SHA。另独立读取实际下载的 `/tmp/carleman-nodal-dirichlet-main-ci/result.json`：status PASS，checked_sha 与 source_head_sha 均为 `50ea3111057c5d7b796cca799c10a9a900d14caf`，finished_at 为 `2026-10-18T19:11:08.436594+00:00`，Lean 4.35.0、mathlib pin 及 Carleman target 与固定版本一致。

实际下载的 `/tmp/carleman-nodal-dirichlet-main-axioms/axioms.txt` 与上述固定本机文件逐字节一致：1,277,288 bytes，SHA256 `d521952f796897ce790ea40d9321a68a8ab1bba8260677f57017e84354c92f62`。独立确认其中 30 项展开类型及对应三项标准公理，末行审计覆盖全部 4578 声明。远端原始证据、固定源码与本机检查相互一致。

## 验收决定

**C060：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 30 项未发现需修复的数学、类型、a.e. 代表、支撑、完整测试族、拓扑或量词缺陷；固定版本语义、实际类型、公理以及同 SHA 三项 CI 均通过。接受本报告所界定的节点 H¹₀ 及真实一致空间成员阶段已完成；不接受 H² 点值/正则性、原量化数值估计、加权投影或连续热 CE 已完成的扩大解释。完整原文覆盖仍为 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
