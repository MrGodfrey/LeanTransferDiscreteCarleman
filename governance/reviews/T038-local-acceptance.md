# T038 / C054 独立本机验收

- `checked_sha`: `756ee9cedb6af22baf308c796fbe0f1d7885e26d`
- `base_commit`: `6923ae3b24d9590bd0afb4e66830b30fe49165d3`
- `reviewed_at`: `2026-10-18T18:15:56+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：节点插值的实际逐片导数、边界节点零下的连续零延拓和全局 Lipschitz、完整测试空间下的弱导数及真实 H¹ 成员。**不提升 Proposition 6.1 / P011 或其他具名原文结果；原文完成仍为 12/26。**

本次独立读取固定提交的八模块全部源码、39 项实际展开类型及相关依赖，核对原 `paper/main.tex` Section 6 的 conforming P1 空间和节点插值使用。后续未追踪的全空间 Sobolev 草稿不属于本报告。执行者规格和 CI 只作为待核实证据，没有代替逐项数学检查。

## 全部 39 项声明

完整名称均以前缀 `Carleman.` 开始。表中位置均属于固定提交的 `Carleman/Spatial/`；顺序与声明清单、C054 和 T038 一致。各项语义检查均 PASS，同版本远端证据也已完成核实。

| # | 声明（省略 Carleman.） | 位置 | 独立核对结论 |
|---|---|---|---|
| 1 | `lipschitzWith_of_eventually_norm_sub_le` | `FiniteLipschitzSelection.lean:16` | PASS；实赋范空间上沿每条线段把统一局部点对界提升为全局同常数 Lipschitz。 |
| 2 | `finite_selection_eventually_norm_sub_le` | `FiniteLipschitzSelection.lean:62` | PASS；有限候选与连续性排除在基点不相等的选择，得到邻域点对界。 |
| 3 | `lipschitzWith_finite_selection` | `FiniteLipschitzSelection.lean:76` | PASS；连续实值有限选择保持同一个 Lipschitz 常数，调用前两项证明。 |
| 4 | `SimplicialPartition.localNodalDerivative` | `SimplicialNodalDerivative.lean:15` | PASS；真实连续仿射插值的 contLinear，没有自设导数。 |
| 5 | `SimplicialPartition.localNodalDerivative_apply` | `SimplicialNodalDerivative.lean:20` | PASS；任意方向上精确等于原 AffineMap.linear 的作用。 |
| 6 | `SimplicialPartition.localNodal_hasFDerivAt` | `SimplicialNodalDerivative.lean:24` | PASS；整个环境空间各点的真实 Fréchet 导数由仿射映射定理供应。 |
| 7 | `SimplicialPartition.nodalFunction_hasFDerivAt_on_interior` | `SimplicialNodalDerivative.lean:30` | PASS；单元内部有实际邻域等式，局部导数合法转给全局函数。 |
| 8 | `SimplicialPartition.ae_mem_cell_interior` | `SimplicialNodalDerivative.lean:40` | PASS；有限零测边界与覆盖给限制体积测度下 a.e. 位于某单元内部。 |
| 9 | `SimplicialPartition.nodalDerivativeFunction` | `SimplicialNodalDerivative.lean:52` | PASS；实际 CLM 值字段为开单元指示函数乘常值导数之有限和。 |
| 10 | `SimplicialPartition.nodalDerivativeFunction_on_interior` | `SimplicialNodalDerivative.lean:56` | PASS；内部不交消除其他求和项，精确等于本单元导数。 |
| 11 | `SimplicialPartition.nodalFunction_hasFDerivAt_ae` | `SimplicialNodalDerivative.lean:68` | PASS；全局点态插值以该实际字段为导数 a.e. 成立。 |
| 12 | `SimplicialPartition.nodalDerivativeFunction_memLp` | `SimplicialNodalDerivative.lean:78` | PASS；有限测度、可测开单元和有限和证明真实字段 MemLp 2。 |
| 13 | `SimplicialPartition.nodalDerivativeLp` | `SimplicialNodalDerivative.lean:87` | PASS；由已证 MemLp.toLp 得实际 CLM 值 L² 类。 |
| 14 | `SimplicialPartition.nodalDerivativeLp_ae` | `SimplicialNodalDerivative.lean:91` | PASS；正确以 a.e. 等式识别 L² 代表与逐片字段。 |
| 15 | `SimplicialPartition.nodalFunction_fderiv_memLp` | `SimplicialNodalDerivative.lean:94` | PASS；通过实际 HasFDerivAt 的 a.e. 唯一性，证明真实 fderiv 可积。 |
| 16 | `SimplicialPartition.BoundaryFitted` | `SimplicialNodalBoundary.lean:15` | PASS；公开的边界几何条件，不直接假设插值边界为零。 |
| 17 | `SimplicialPartition.localNodal_zero_on_boundary` | `SimplicialNodalBoundary.lean:18` | PASS；边界节点零经仿射包扩张及 BoundaryFitted 给整个单元边界交上零值。 |
| 18 | `SimplicialPartition.nodalFunction_zero_outside` | `SimplicialNodalBoundary.lean:30` | PASS；closure S 外无单元覆盖，实际定义取零。 |
| 19 | `SimplicialPartition.nodalFunction_zero_on_boundary` | `SimplicialNodalBoundary.lean:40` | PASS；有限闭覆盖和 FaceMatching 把局部零值转给整个 frontier S。 |
| 20 | `SimplicialPartition.nodalFunction_zero_on_compl` | `SimplicialNodalBoundary.lean:50` | PASS；S 开时，边界与 closure S 外两种情况覆盖整个 S 补集。 |
| 21 | `SimplicialPartition.nodalFunction_continuous_of_boundary` | `SimplicialNodalBoundary.lean:60` | PASS；在 closure S 与 S 补集这两个闭集上拼接，得到全空间连续。 |
| 22 | `SimplicialPartition.nodalFunction_hasCompactSupport` | `SimplicialNodalBoundary.lean:76` | PASS；有限紧单元并给紧 closure S，支集包含于其中；未声称支集紧含于 S。 |
| 23 | `SimplicialPartition.nodalLipschitzConstant` | `SimplicialNodalLipschitz.lean:17` | PASS；常数明确为各局部实际导数 NNReal 算子范数之和。 |
| 24 | `SimplicialPartition.localNodal_lipschitzWith` | `SimplicialNodalLipschitz.lean:20` | PASS；真实仿射差等于线性部分作用，算子范数界再放大到有限和。 |
| 25 | `SimplicialPartition.nodalFunction_lipschitzWith` | `SimplicialNodalLipschitz.lean:34` | PASS；加入零函数的 Option ι 有限族与已证连续性给真正全空间 Lipschitz。 |
| 26 | `weakSpatialDerivative_of_lipschitz` | `LipschitzWeakDerivative.lean:17` | PASS；真实 lineDeriv 代表和差商积分分部给原完整 IsWeakSpatialDerivative。 |
| 27 | `SimplicialPartition.nodalDirectionalLp` | `SimplicialNodalWeakDerivative.lean:15` | PASS；CLM 求值算子作用于真实导数 L² 字段，方向任意。 |
| 28 | `SimplicialPartition.nodalDirectionalLp_ae` | `SimplicialNodalWeakDerivative.lean:19` | PASS；方向 L² 类的代表准确等于逐片实际导数作用于 e。 |
| 29 | `SimplicialPartition.nodalLp_weakDerivative` | `SimplicialNodalWeakDerivative.lean:25` | PASS；全局 Lipschitz 与内部实际导数给每个方向的完整弱导数身份。 |
| 30 | `scalarZeroFiber` | `FirstOrderSobolevJet.lean:12` | PASS；真实连续线性映射将标量送入唯一零阶多重指标分量。 |
| 31 | `derivativeOneFiber` | `FirstOrderSobolevJet.lean:16` | PASS；真实 CLM 字段在正交坐标方向的求值组成一阶 Sym fiber。 |
| 32 | `scalarZeroFiber_component` | `FirstOrderSobolevJet.lean:21` | PASS；任意零阶分量在 L² 中精确恢复原标量类。 |
| 33 | `derivativeOneFiber_component` | `FirstOrderSobolevJet.lean:29` | PASS；Sym 单元素识别给该坐标分量与实际方向求值 L² 类严格相等。 |
| 34 | `firstOrderFields` | `FirstOrderSobolevJet.lean:43` | PASS；将真实零阶与一阶字段组装成项目既有 JetFields d 1。 |
| 35 | `firstOrderJet` | `FirstOrderSobolevJet.lean:52` | PASS；全部坐标弱导数身份清偿 weakJetSubmodule 的全部一阶条件。 |
| 36 | `firstOrderJet_value` | `FirstOrderSobolevJet.lean:69` | PASS；该实际 jet 的零阶 value 精确等于输入 L² 类。 |
| 37 | `SimplicialPartition.nodalSobolevJet` | `SimplicialNodalSobolev.lean:15` | PASS；以实际 nodalLp、导数 L² 字段和已证弱身份构造真实 WeakSobolevJet。 |
| 38 | `SimplicialPartition.nodalSobolevJet_value` | `SimplicialNodalSobolev.lean:22` | PASS；值就是先前已构造的 nodalLp，没有换代表或换插值。 |
| 39 | `SimplicialPartition.nodalLp_mem_sobolev` | `SimplicialNodalSobolev.lean:28` | PASS；具体 jet 给既有 sobolevSubspace 的 range 见证，结论为实际 H¹ 成员。 |

## 实际导数、骨架及 L²

`localNodalDerivative` 使用真实 AffineMap 经有限维连续性形成 ContinuousAffineMap，再取 contLinear；作用等式是定义相等。`localNodal_hasFDerivAt` 调用连续仿射映射的实际 Fréchet 导数定理，既没有导数作为额外输入，也没有重新命名一个任意线性映射。

全局插值与任一局部仿射函数在整个单元上相等来自已验收的 FaceMatching。只有点属于单元内部时，证明才使用该等式在邻域上转移导数。随后实际有限单元的 Lebesgue 零测 frontier 排除所有骨架点；覆盖 S 和内部不交均来自原 SimplicialPartition，得到限制体积测度下的 a.e. 导数公式。没有假定插值在共享面可微，也没有仅凭 a.e. 覆盖就作局部邻域推断。

导数字段是开单元 indicator 的有限和；每个内部点至多激活一个真实常值导数。骨架和覆盖外选零不影响限制测度下的 L² 类。`MemLp` 由公开的有限测度实例与常值函数 indicator 的可积性证明，随后 toLp 和 a.e. 等式给实际字段。经典 fderiv 的 L² 性质以已证 HasFDerivAt a.e. 转移，未把“经典导数存在 a.e.”直接当成弱导数存在。

## 边界零、零延拓和全局 Lipschitz

BoundaryFitted 的实际内容是 `Ki ∩ frontier S ⊆ convexHull(vertices_i ∩ frontier S)`，它是需要具体网格另行供应的几何条件。输入 hf 仅要求所有实际边界顶点的 f 值为零。局部仿射插值与零映射在这些顶点相等，`AffineMap.eqOn_affineSpan` 扩张到仿射包；边界部分由 BoundaryFitted 落入其中，所以整个相交部分为零。该证明没有把只在顶点为零当作任意函数在整个面为零。

有限单元的闭并为 closure S；FaceMatching 让全局选择与给定单元一致，因而边界零是逐点结论。S 开时，closure S 中而不在 S 的点恰在 frontier S，结合原定义在 closure S 外取零，得到整个补集为零。已有 closure S 上连续性与补集上的常零连续性通过闭集覆盖拼接，得到整个环境空间上的连续性。紧支集来自有限紧单元覆盖；仅有 `tsupport ⊆ closure S`，没有推出支集紧含于 S 或 H¹₀ 的光滑闭包条件。

有限选择定理确实证明了跨面全局界：对固定 x，候选 gi 若在 x 不等于 f，则相等集因两函数连续而闭，其补集给排除该候选的邻域。有限交后，邻近 y 选中的 gi 在 x 必须也等于 f，故 `|f(y)-f(x)|≤C‖y-x‖`。沿任意线段 `x+t(y-x)` 拉回这一点对界，得到每个 t 的右侧 slope 上界，再应用固定 mathlib 的 `image_le_of_liminf_slope_right_le_deriv_boundary` 对线性比较函数的完整 fencing 定理。交换端点给绝对值界，常数不变；没有要求在切换点有导数或有限次切换。

全局 nodalFunction 在每一点属于有限族 `{0}∪{localNodal_i}`，零函数对任意非负 C 都 Lipschitz，各仿射函数用真实导数的算子范数界控制。取 `C=Σi ‖localNodalDerivative_i‖₊` 并使用已证明的连续性，得到整个 Euclidean 空间的真正 LipschitzWith。C 允许依赖网格、节点数、单元几何与节点值；它是存在性桥接所用的有限常数，不是原统一逆估计、h 缩放或加权稳定常数。没有 T、q、权函数或状态统一性的未披露断言。

## 完整测试空间上的积分分部

已直接核对原 `SpatialTest`、`IsWeakSpatialDerivative.iff_integral` 和固定 mathlib `LipschitzWith.integral_lineDeriv_mul_eq`。SpatialTest 仍为所有真实全空间 C∞、紧支且 tsupport 包含于 S 的测试函数，未换成有限元测试函数或一个稠密子族。每个测试函数的真实 C∞ 与紧支性质内部推出其全局 Lipschitz。

mathlib 的积分分部定理由真实差商在正步长趋零时的受控积分极限及平移换元证明；本次在 Euclidean 空间用实际 Lebesgue volume 满足其有限维 Haar 测度条件。由 f 的全局 Lipschitz 和测试函数的 Lipschitz/紧支，得到 `∫ lineDeriv f e · φ = ∫ lineDeriv φ (-e) · f`。测试函数光滑使后项 lineDeriv 精确等于 `-fderiv φ e`，符号正确。

测试函数的 tsupport 包含于 S，故 S 外函数值为零，真实 fderiv 也由不在 tsupport 的邻域恒零性质为零。这两项全空间积分可准确限制到 S，再代入 u、v 的 a.e. 代表，恰得原弱身份 `∫ D_e φ·u = -∫ φ·v`。这里的 u、v 均为真实 L² 类；没有假定它们的所选代表连续，没有额外施加测试函数的边界正规性。该通用桥没有假设目标积分身份。

`nodalDirectionalLp` 是 CLM 求值作用于实际 nodalDerivativeLp。各内部点已证 HasFDerivAt，因而真实 lineDeriv 与该字段作用于任意 e 相等 a.e.。代入通用桥即可得到 `nodalLp_weakDerivative` 的每个方向结论。零边界与 BoundaryFitted 是本证明采用全空间零延拓路线的公开前提；没有宣称已证明任意非零边界输入的这一最终接口。

## 真正的一阶 Sobolev jet 与假设边界

`DerivativeFiber d k` 是 Sym 多重指标上的实际 Euclidean fiber。零阶只有空指标，scalarZeroFiber 用真实连续线性映射复制该标量；一阶用 Sym.oneEquiv 把单元素指标对应到实际正交坐标基。两个 component 身份以 OperatorMultiplier 的 a.e. 公式和 Lp.ext 证明，未选任意梯度，也未混用点态等式和 L² 代表。

一阶 jet 的唯一相邻层是 k=0，零阶多重指标必须为 Sym.nil。`firstOrderJet` 将全部坐标弱导数 h i 逐一代入原 weakJetSubmodule，完整清偿其条件。`firstOrderJet_value` 精确恢复 u。最终 nodalSobolevJet 采用同一个 nodalLp 和实际 CLM 值导数字段；所有 h i 都来自上一模块刚证明的实际弱身份，未留目标式为外部假设。

既有 `sobolevSubspace d 1 (volume.restrict S) S` 是 WeakSobolevJet.value 的真实 range。最终成员证明给出具体 jet 及准确的 value 等式，因而确为原弱 H¹ 子空间成员，不是名为 Sobolev 的任意给定空间。已核对原完整测试空间及导数分量接口，坐标方向足以构成项目的一阶弱 Sobolev 定义。

最终全部条件明确为：任意 d，有限索引的真实非退化 d-simplex 分区、其 inside/cover/内部不交字段，S 开、FaceMatching、BoundaryFitted、`IsFiniteMeasure (volume.restrict S)`，实际点态 f 在所有边界顶点取零。有限测度仍为显式输入，本批没有把它的推导计为新结果。f 无可测、连续或先验 Sobolev 条件，因为输出仅使用有限节点值。空索引时覆盖强迫 S 为空；d=0 时坐标弱导数条件为空，零阶 value 仍正常恢复。没有隐藏正维、非空网格、边界光滑或统一形状条件。

## 原文对应与未完成义务

原 Section 6 的 P1 部分定义 `Vh={v∈H₀¹(Ω): v|K∈P1}`；Step 2 通过 d=2,3 的 H² 连续嵌入定义 Ih，Step 3 使用 `Ih(σ² zh)∈Vh`。本批把已经构造的点态连续逐片仿射节点插值推进到真实 H¹，并证明边界节点零时的逐点零延拓性质，符合这些论证所需的部分基础。

仍未证明 H¹₀ 作为紧支光滑闭包的成员/密度或零迹识别；全空间连续、边界零和紧支本身没有在接口中被当作这项结论。没有从任意 Lp/H¹/H² 等价类取节点值，H² 连续代表及其节点赋值仍待供应。具体网格的 FaceMatching/BoundaryFitted、统一形状正则与原分级、局部 h/h² 误差、梯度逆界、加权投影稳定、超逼近以及原连续 Dirichlet 热 CE 也未在本批完成。因此不能据此提升 P011、P014、P015 或任何完整 N3/N4/数值实例；C054 必须保持 AUXILIARY，原文仍为 12/26。台账 `extra_hypotheses=[]` 只能针对该辅助目标理解，不能用来省略以上真实参数或宣称完整 Proposition 6.1 已无未清偿条件。

## 固定依赖、构建和公理

已读取基线的 [T037 独立验收](T037-local-acceptance.md)，并直接复核本批调用的 FaceMatching/真实 nodalFunction、单元一致、闭覆盖连续性、nodalLp 及其代表公式；不是仅沿用验收标签。导入闭包为 41 个 Carleman 模块，其中 33 个旧模块与基线逐字节相同，新增恰为本次八模块，固定 Carleman.lean 对它们均显式导入。原稿、治理协议、MATH_SPEC、工具链 pin 和工作流均未改变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 mathlib HEAD 实际为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净，所读 MeanValue、Rademacher 和相关依赖均属该固定版本。已读取 fencing 定理的实际条件及 Rademacher 差商积分分部的实际证明；调用处满足其全空间连续、Lipschitz、紧支及测度条件。

固定 CheckAxioms 对 39 项逐一输出 `#check @...` 和 `#print axioms ...`，最后遍历所有归属 Carleman 的公开/私有声明，递归 collectAxioms，仅许可 `propext`、`Classical.choice`、`Quot.sound`。本机固定 `/tmp/carleman-nodal-h1-local-axioms.txt` 实际为 1,214,020 bytes，SHA256 `79840d094068a22361ac2d4e3bdb57d107b604634a7045cda74fe4f7401c254d`。39/39 实际展开类型与源码一致，每项依赖公理集合都恰为这三项标准基础公理，末行是 `Axiom audit passed for all 4210 Carleman declarations.`。本机 `/tmp/carleman-nodal-h1-full.log` 实际包含 `Build completed successfully (3549 jobs).` 和同样的 4210 项全局审计通过记录。

已独立通过 GitHub connector 核实 [main CI 39152713399 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39152713399/attempts/1)：head SHA 正确，main/push，最终 completed/success。state-check（117749462926）、lean（117749463085）、dashboard / snapshot（117750481227）三个 jobs 均成功；Lean 的 pin、root target 构建、checked source 记录及两份证据上传步骤全部 success。同次 lean-ci-result artifact（12145318262）和 lean-declaration-evidence artifact（12145084131）的 workflow_run 均绑定该 run 与固定 SHA。

已实际读取 `/tmp/carleman-nodal-h1-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=756ee9cedb6af22baf308c796fbe0f1d7885e26d`，targets 为 Carleman，`finished_at=2026-10-18T18:10:24.599863+00:00`；Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 均符合固定 pin。

已逐字节比较 `/tmp/carleman-nodal-h1-main-axioms/axioms.txt` 与固定本机副本，完全相同：1,214,020 bytes，SHA256 同为 `79840d094068a22361ac2d4e3bdb57d107b604634a7045cda74fe4f7401c254d`。另逐名核对远端 39/39 项完整类型存在、各自公理集合恰为上述三项标准基础公理，并验证 C054/T038 两份声明列表与交付清单顺序完全一致。远端末行实际为 `Axiom audit passed for all 4210 Carleman declarations.`，无 sorryAx 或未批准数学公理；没有混用后续版本的产物。

## 验收决定

**C054：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 本次 39 项未发现需要修复的数学、类型、代表、边界或量词缺陷。固定版本语义、完整类型、递归公理及同 SHA main CI 证据均已核实。该结论只覆盖实际弱导数、连续零延拓和真实 H¹ 成员；H¹₀ 闭包、H² 点值代表及统一数值估计仍未完成，不提升任何完整原文结果，原文计数保持 12/26。

本次仅写本报告，没有修改数学源码、台账、覆盖表、原稿或 root 导入，没有 commit/push。
