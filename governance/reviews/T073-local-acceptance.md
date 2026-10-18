# T073 / C089 独立本机验收

- checked_sha: `c99262c4a0d65a4d23f2efb57748bda490e971d7`
- base_commit: `36c57dbc4edf3d9671f7b00f8c0675230f6b4380`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`（固定版本 21 项可升 REVIEWED；保持 AUXILIARY）
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T22:48:18+00:00`
- scope: `AUXILIARY`。原有界开凸域任意弱 H¹ 状态的真实均值 Poincaré；尚非一般 H² 仿射逼近、边界校正、节点 H² 插值或原完整 B1/B2/P1/N3。原文仍 **12/26**。

## 固定范围与全部 21 项声明

依项目 AGENTS 和治理/状态协议，直接读取固定提交五模块的全部源码、固定产物中全部 21 项实际展开类型和所调用的真实依赖，核对 `governance/analysis/T073-convex-weak.md` 与原 `paper/main.tex`。未以执行者说明、旧验收或 CI 替代语义核查；后续工作区不在本次范围。

模块为 `Spatial/PairwiseL2Limit`（5 项）、`Spatial/MollifiedGradientEnergy`（3 项）、`Spatial/InteriorWeakPoincare`（5 项）、`Geometry/ConvexCompactExhaustion`（5 项）、`Spatial/ConvexWeakPoincare`（3 项），均在 `Carleman/` 下。下列名单精确匹配固定 C089 与 `/tmp/carleman-convex-weak-declarations.json`，root 显式导入全部五模块。

| 完整声明 | 独立核查的实际内容 |
| --- | --- |
| `Carleman.l2_square_bound_of_ae_tendsto` | 实际 L² 函数序列 a.e. 收敛和最终平方积分上界，通过 eLpNorm Fatou 传到极限；C≥0、有限 eLpNorm 及实数转换均明确。 |
| `Carleman.pairwise_memLp` | 有限测度下，真实 f(x)−f(y) 属于 ν×ν 的 L²；有限测度前提保留。 |
| `Carleman.pairwise_integral_congr_ae` | 两个代表在 ν 下 a.e. 相同，则两层差平方积分相同；分别在两层应用 a.e. 积分一致性。 |
| `Carleman.pairwise_square_bound_of_ae_tendsto` | 在真实乘积测度上构造双差的 a.e. 极限和 L² 可积性，再应用 Fatou；每次 Fubini 都有实际平方可积证据。 |
| `Carleman.l2_square_bound_on_exhaustion` | 可测 A_n 上的限制积分统一有界，且 a.e. 点最终属于 A_n，即通过指标函数极限得到全域界；不要求 A_n 单调或积分先有极限。 |
| `Carleman.spatialLinearMap_norm_sq` | 真正实标量 CLM 的算子范数平方等于对标准正交基的各坐标作用平方和；无维数放大。 |
| `Carleman.mollified_gradient_energy_le` | 在反射核支撑完整留在 S 的 K 上，实际卷积 fderiv 能量≤原完整坐标弱导数的 L² 平方和；单位非负核收缩常数 1。 |
| `Carleman.convex_mollified_pairwise_bound` | 将真实光滑卷积代入已证紧凸光滑双差界，再用上述梯度能量界；保留 2^d·volume(K)·D²。 |
| `Carleman.shrinkingBump_rOut_tendsto` | 实际外半径 2/(n+1) 趋零，不是抽象假定的近似单位。 |
| `Carleman.compact_mollifier_eventually_inside` | 紧 K⊆开 S 给正缓冲半径，实际核闭支撑半径最终小于它，因此所有 x∈K、y∈tsupport κ_n 都有 x−y∈S。 |
| `Carleman.interior_weak_pairwise_fullLp` | 全空间 L² 数据仅在 S 内满足弱导数身份时，真实卷积极限给紧凸 K 上双差界；不要求全空间弱 H¹。 |
| `Carleman.interior_weak_pairwise` | 原限制 L² 数据经真实等距零延拓进入前项，再用 K⊆S 下的 a.e. 代表一致性还原原双差，右端范数精确保持。 |
| `Carleman.interior_weak_mean_poincare` | K 正体积时以精确均值恒等式消去 2volume(K)，右端仍为原 S 上弱导数能量。 |
| `Carleman.convexInnerCompact` | 显式定义 K_n=a+r_n(closure S−a)，r_n=(n+1)/(n+2)，通过真实中心缩放同胚取像。 |
| `Carleman.convexInnerCompact_compact` | 有界 S 的闭包在有限维 Euclidean 空间紧，连续缩放像仍紧。 |
| `Carleman.convexInnerCompact_convex` | 原凸性传到闭包及实际仿射像，不额外假定穷竭集凸。 |
| `Carleman.convexInnerCompact_subset` | a∈S、S 开凸及 0<r_n<1，严格内缩 closure S 后确实在 S 内。 |
| `Carleman.convexInnerCompact_eventually_mem` | 对每个 x∈S，逆缩放点趋 x，开性保证最终仍在 S，因此 x 最终属于 K_n。 |
| `Carleman.convex_weak_pairwise_bound` | 原 ν=volume.restrict S 的 ν×ν 上以 K_n×K_n 指标穷竭，准确限制乘积测度并用 volume(K_n)≤volume(S) 取得全域双差界。 |
| `Carleman.convex_weak_mean_poincare` | 正体积原域上的精确均值与全部真实坐标弱导数，给显式 (2^d/2)D² 能量界。 |
| `Carleman.convex_weakJet_mean_poincare` | 从任意原完整 H¹ jet 取得所有坐标弱身份，经 Sym.oneEquiv 精确合并为原 field₁ 的 L² 范数平方，无零迹或光滑状态条件。 |

## 局部弱导数、反射核与 L² 零延拓

已直接读取 `DomainConvolution`、`WeakConvolution` 和 `ZeroExtensionLp`。原零延拓是限制 L² 类的真实指标延拓，已证明其全空间 L² 范数等于原范数，并在 S 上 a.e. 等于原类。`IsWeakSpatialDerivative.zeroExtend` 的结论是 `IsWeakSpatialDerivative volume S ...`，测试域仍为 S，**不是** univ；它通过实际积分乘指标公式保留原测试身份，未丢弃边界分布项后声称全空间弱导数存在。

核 κ 的反射测试取 y↦κ(x−y)。`reflectedWithin` 使用准确的闭支撑逆像，并以假设“∀y∈tsupport κ，x−y∈S”证明其闭支撑包含于 S，故是原完整 SpatialTest。真实链式法则给 y 方向导数 `−Dκ(x−y)`；原弱导数积分分部自带的负号与此负号抵消，最终得到 `u*Dκ=v*κ`，方向正确。

卷积的真实 fderiv 身份先由紧支光滑核与 u 的局部可积性得到 CLM 值的导数积分，再用具有卷积存在/可积证据的 CLM 积分求值交换；不是把 v*κ 自定义成“梯度”。局部弱测试只在上述支撑条件成立的 x 上使用，不对贴近边界的任意 x 无条件套用。

`compact_mollifier_eventually_inside` 对紧 K⊆开 S 调用真实 `exists_cthickening_subset_open` 得 δ>0 和闭 δ 邻域包含于 S。实际 normalized bump 的闭支撑就是以 0 为中心的闭 rOut 球，rOut=2/(n+1)→0。最终对所有 x∈K、核支撑内 y，一致有 `dist(x−y,x)=‖y‖≤rOut<δ`，于是反射核留在 S。缓冲半径可以依赖 K，但只决定序列何时开始合法，不进入估计常数。

原 u、v_i 的零延拓只负责全空间卷积的数据与等距范数。回到 K 时，用 K⊆S 的限制测度单调性转移 a.e. 恒等式，再由 `pairwise_integral_congr_ae` 还原双差积分。没有在 S 外把任意 L² 代表当作实际状态点值，也没有引入 H¹₀、迹、Lipschitz 边界或全空间 H¹ 延拓前提。

## 实际卷积能量与常数

`spatialLinearMap_norm_sq` 调用固定 mathlib 的真实 `OrthonormalBasis.norm_dual`。因导数是 Euclidean 空间到 ℝ 的线性泛函，其算子范数平方正好等于标准正交基上的作用平方和；这不是对一般向量值导数使用错误的 Hilbert–Schmidt/算子范数等式。

对每个 i，局部卷积交换证明 `Df_n(x)e_i=(v_i*κ_n)(x)`。每个 v_i*κ_n 的全空间 L² 资格及范数≤‖v_i‖由真实非负单位核收缩提供。已直接检查 `ConvolutionL2`：先对 sqrt κ 加权使用真实 L² Cauchy–Schwarz，证明卷积平方被 κ*v_i² 控制，再由实际卷积积分和单位质量取得 L² 收缩；平方密度的可积性在比较之前由可积卷积支配证明。

因此在 K 上，将真实导数算子范数平方精确展开成有限坐标平方和。每个坐标卷积已属于全空间 L²，其在 K 上的平方可积，有限和积分交换合法；非负性使 K 上积分≤全空间积分，再分别用收缩，得到

`∫K ‖Df_n‖² ≤ ∑ᵢ‖v_i‖²`。

这里没有额外 d、K 的体积或单位核范数因子。真实卷积是全空间 C∞，故可以合法应用 T072 的全空间 C¹ 紧凸双差定理，得到 `2^d volume(K) D²` 乘同一原梯度能量。T072 的 2^d 常数沿用的是半线段 Jacobian、同一中点平方三角和实际积分所得的结论；本次没有将该光滑性要求错误传给原弱状态。

## 两次 Fatou、可积性与代表

新一般极限引理明确假定 f、所有 F_n 真正属于 L²，C≥0，a.e. 收敛和最终积分≤C。先把平方积分转换成真实 bochnerL2Norm²，再以非负平方根转换成 eLpNorm 的 ENNReal 上界；所有 toReal 转换都使用 MemLp 给出的有限性。固定 mathlib 的 `Lp.eLpNorm_le_of_ae_tendsto` 确实允许 eventually 的上界，并以 Fatou/liminf 证明，不需要积分已收敛或统一点态支配。

双差版在有限 ν 下由两个坐标拉回的 L² 函数之差构造 ν×ν 上的真实 L² 对象。投影的 quasiMeasurePreserving 将各自 a.e. 极限拉回乘积测度，共同得到 F_n(x)−F_n(y) 的极限。双差平方可积后才用 Fubini 转换两层积分，因此不会因不可积积分的默认值形成伪估计。

对固定 K，ν=volume.restrict K 的有限性来自紧性；所有卷积的 L² 资格来自实际收缩并限制。原实际 normalized bump 的 a.e. 逼近已直接核对：外半径趋零、外/内半径比恒为 2，以及 u 的局部可积性满足 mathlib 的 Lebesgue 微分近似单位定理。收敛从 volume 限制到 K；紧内域合法性仅最终成立，与新 Fatou 引理的 eventually 条件完全匹配。

穷竭版用 `(A_n).indicator f`，每个指标函数的 L² 资格来自可测性。a.e. 点最终进入 A_n，使指标函数最终等于 f，故 a.e. 收敛。指标平方等于平方密度的指标，限制积分与全积分精确转换。没有假定 A_n 单调、梯度沿穷竭收敛、积分极限存在或域边界零测。

## 显式紧凸穷竭与原乘积测度

对非空 S，代码实际取 a∈S，并设 `r_n=(1+n)/(2+n)`、`K_n=a+r_n(closure S−a)`。已核对 `centeredDilation` 及其逆为 `x↦a+r_n⁻¹(x−a)`；r_n 正且小于 1、趋于 1。紧性来自有限维有界闭包及连续像，凸性来自闭包凸性和真实仿射像。

严格域内包含使用凸集的“内点与闭包点的严格凸组合仍为内点”，不是从 closure S⊆S 得出。对任意 x∈S，逆内缩点趋 x，S 的开性保证该逆像最终属于 S⊆closure S；同胚的 apply_symm 身份随后给 x∈K_n。此最终包含不需要另行证明 K_n 单调。空 S 在全域双差定理中先单独处理，没有从空集选择 a。

全域步骤固定 **原** ν=volume.restrict S，并在 ν×ν 上穷竭 `K_n×K_n`。该空间的双差 f(x,y)=u(x)−u(y) 真正属于 L²，因为 S 有界故 ν 有限。`Measure.prod_restrict` 及 K_n⊆S 将对 ν×ν 的限制精确化为 `(volume.restrict K_n)×(volume.restrict K_n)`；没有误用未限制的全空间乘积或把两个域的体积混合。

每个 K_n 的局部估计使用同一个原 S 上的 ∑‖v_i‖² 和同一个 D；D 对 S 所有实际两点距离的上界经 K_n⊆S 传入。`volume.real K_n≤volume.real S` 的转换具有 S 的有限测度证明，因此局部双差有统一上界 `2^d volume(S) D²∑‖v_i‖²`。最终包含通过两个乘积投影的 a.e. 域成员资格分别得到，正好符合指标穷竭的 a.e. eventually 条件。这里不需要 volume(K_n)→volume(S)。

## 均值、真实弱梯度和量词

已直接读取 `MeanSquareDifference` 的完整真实积分证明。在有限 ν 下，L² 给 L¹ 和平方可积，准确恒等式为

`2ν(Ω)∫(u−(∫u)/ν(Ω))²=∫∫(u(x)−u(y))²`。

最终 mean 定理明确要求 `0<volume.real S`，因此除以/消去正数 `2volume.real S` 合法，得到系数 `(2^d/2)D²`。局部 mean 版本同样明确要求 K 正体积；前置双差估计不要求正体积。没有把 volume 当概率测度或遗漏一个体积因子。

`convex_weakJet_mean_poincare` 输入是任意 `WeakSobolevJet d 1 (volume.restrict S) S`。其零阶值是实际 L² 类，每个 v_i 取原 field₁ 的 `Sym.cons i nil` 分量；原 jet 自带的所有 SpatialTest 弱身份准确供应前项 hv。`derivativeField_norm_sq` 与 `Sym.oneEquiv` 将 ∑ᵢ‖v_i‖² 精确转换成 **同一原** field₁ 的 L² 范数平方，各坐标一次，没有替代能量或自由选取梯度。

最终只要求 S 开、凸、有界、正体积，D≥0 是全 S 两点距离上界。常数显式仅为 `2^d/2`，先于 S、D、状态、内缩中心、核半径与穷竭阶段；没有形状正则、内球比、网格、权、时间参数或边界迹依赖。d 为任意自然数，包括 d=0；此时真实一阶坐标为空，均值结论在零维正体积域仍合法，不使用空间单点零测论证。D=0 未被除法排除。

本阶段确实将 T072 的全空间 C¹ 假设从最终状态结论中消去，得到原完整弱 H¹ 状态的结论。没有要求状态具有连续代表、点态导数、零边界或属于算子域。

## 原文定位与依赖范围

原 Section 6 P1 Step 2（1523–1557 行）仍需一般 H² 的节点插值及 Hessian 控制；Appendix B `lem:fd-boundary-affine`（2803–2837 行）要求一般 H²、指定物理面的零迹、满足这些边界面的仿射近似及二阶误差，后续 B2 还涉及局部矩重构与网格组合。本阶段的均值 Poincaré 是后续一般 H² 仿射构造的基础，不构成这些完整结论。

已读取 [T072 独立验收](T072-local-acceptance.md)，其 checked SHA 正是本阶段基线，并直接核查本次使用的 ConvexSmoothPoincare 与 MeanSquareDifference 的全部实际前提/常数。另直接追踪零延拓、局部反射弱测试、卷积光滑/收缩/近似单位、中心缩放、坐标范数和 Fatou 等依赖；既有结论没有被扩大到其未证明的边界或全空间弱导数范围。

## 固定版本、构建与公理

五模块的 Carleman import 闭包共 86 个模块，81 个既有模块与基线逐字节不变。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。AGENTS、治理/状态协议、CI workflow 和工具链 pin 未改；Lean 为 `leanprover/lean4:v4.35.0`，mathlib pin/本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且 mathlib 工作树干净。

固定 CheckAxioms 仅增本批 21 项完整 `#check @...` 与 `#print axioms ...`，原 namespace/privateToUserName 全量递归 collectAxioms 保留。21 项实际展开类型逐一核对，每项恰有一条公理打印且仅含 `propext`、`Classical.choice`、`Quot.sound`。全部 1509 条显式公理打印（1505 个不同声明）也已扫描，只有标准基础公理。五新模块没有 sorry、admit 或新增数学公理。

实际 `/tmp/carleman-convex-weak-full.log` 包含 `Build completed successfully (3685 jobs).` 和全部 **5178** 声明递归审计 PASS。固定 `/tmp/carleman-convex-weak-local-axioms.txt` 实测 **1,541,114 bytes**，SHA256 **`4860f1ce84c233631ad15e65b791a81f95da03a207d74b9bf9112e6a41b83e50`**。

已独立读取 GitHub 实际 run、jobs 和 artifacts API：[main/push run 39173511962 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39173511962/attempts/1) 为 completed/success，head SHA 精确匹配本次 checked_sha。三项 jobs 均为相同 SHA 且 completed/success：lean（117811334753，2026-10-18T22:47:20Z）、state-check（117811334925，22:44:11Z）、dashboard / snapshot（117812039365，22:47:30Z）。在全部 job 真正完成后签发。

同次原始 artifacts `lean-ci-result`（12153641824）和 `lean-declaration-evidence`（12153497380）均绑定此 run/main/SHA 且未过期。已直接读取 `/tmp/carleman-convex-weak-main-ci/result.json`：status PASS，checked_sha 与 source_head_sha 均为 `c99262c4a0d65a4d23f2efb57748bda490e971d7`，ci_url 精确对应上述 attempt，finished_at=`2026-10-18T22:46:25.936718+00:00`，target 为 Carleman。实际 Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 均匹配；此 result 生成时间与最终 job 完成时间分开记录。

已读取 `/tmp/carleman-convex-weak-main-axioms/axioms.txt`，与固定本机副本逐字节完全一致：**1,541,114 bytes**、SHA256 **`4860f1ce84c233631ad15e65b791a81f95da03a207d74b9bf9112e6a41b83e50`**。远端逐名复核本批 21 项完整类型/公理，全部 1509 条显式公理打印也仅含标准基础公理，末行确认 **5178** 声明递归审计 PASS。未使用后续工作区的 `.ci/axioms.txt` 替代本次产物。

## 验收决定

**T073 / C089：PASS，可升 REVIEWED，scope 保持 AUXILIARY。** 21 项实际类型、边界/弱导数处理、可积性、局部卷积能量、两次极限、穷竭几何、原乘积测度、均值归一化、真实完整梯度及同 SHA 远端证据均通过；未发现需要修复的数学缺陷。

本批确实证明原有界开凸域上任意真实弱 H¹ jet 的均值误差平方积分≤`(2^d/2)D²‖field₁ u‖²`，没有全空间 H¹ 延拓、零迹或光滑状态前提。一般 H² 仿射逼近、边界校正、节点 H² 插值及完整 B1/B2/P1/N3 仍待，原文保持 12/26。本次仅写本报告，未修改实现、台账、原稿或 root 导入，未 commit/push。
