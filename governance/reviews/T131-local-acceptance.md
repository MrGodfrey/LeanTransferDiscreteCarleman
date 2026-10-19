# T131 / C147 独立本机验收

- checked_sha: `94f7ddd96b42ac046a4dc2cb14fffb5cd97f1402`
- base_commit: `5c1c62ee09ab89d7e28c0b484c02494958856b33`
- reviewed_at: `2026-10-19T07:06:43+00:00`
- reviewer: `/root/accept_spatial_foundations`，独立本机验收 Agent。
- result: **PASS**；axiom_check: **PASS**。
- scope: **AUXILIARY**。可将 C147 在本固定版本登记为 REVIEWED；P023 / `prop:analytic-realizations` 不提升，原文完成数保持 **14/26**。

本报告直接读取固定 Git 对象中的全部七模块、21 项实际展开类型、关键证明依赖、原稿、MATH_SPEC、T131 分析和台账；独立查询同 SHA 三项正式 CI，独立下载并比较原始证据。执行者说明及 CI 不能替代数学核查。仅写本报告，未修改实现、台账、原稿或根导入，未提交或推送。后续工作树与动态 `.ci/axioms.txt` 不作为本批证据。

## 全部 21 项声明

下表行号均属于 checked_sha，文件均位于 `Carleman/Spatial/`。声明及模块 JSON 与固定 C147 台账一致；七模块均由固定 `Carleman.lean` 导入，21 项在 `tools/CheckAxioms.lean` 中均有 `#check @...` 和 `#print axioms ...`，实际原始产物包含全部展开类型。

| # | 完整声明 | 固定源码位置 | 逐项结论 |
|---|---|---|---|
| 1 | `Carleman.subdomainZeroExtend` | `SubdomainZeroExtension.lean:13` | PASS。先作真实全空间 L² 零延拓，再限制到 S；不是形式域转换。 |
| 2 | `Carleman.subdomainZeroExtend_ae` | `SubdomainZeroExtension.lean:18` | PASS。在 volume.restrict S 上 a.e. 等于 T.indicator u。 |
| 3 | `Carleman.subdomainLp_zeroExtend` | `SubdomainZeroExtension.lean:23` | PASS。T⊆S 时限制回 T 严格恢复原 L² 类。 |
| 4 | `Carleman.subdomainZeroExtend_norm` | `SubdomainZeroExtension.lean:33` | PASS。真实零延拓范数严格相等，适用于标量和向量 L²。 |
| 5 | `Carleman.subdomainZeroExtend_inner` | `SubdomainZeroExtension.lean:40` | PASS。零延拓与限制的实际 L² 内积精确对应。 |
| 6 | `Carleman.SpatialTest.restrictSubdomain_mono` | `DirichletExtensionPairing.lean:14` | PASS。同一测试视为外域测试后，限制回内域恢复完整原 H¹ jet。 |
| 7 | `Carleman.WeakSobolevJet.extendDirichlet_field` | `DirichletExtensionPairing.lean:25` | PASS。原 H¹₀ 延拓的 0、1 阶字段等于各字段的实际 L² 子域零延拓。 |
| 8 | `Carleman.WeakSobolevJet.extendDirichlet_field_norm` | `DirichletExtensionPairing.lean:29` | PASS。嵌套域上两阶字段范数均严格保持。 |
| 9 | `Carleman.WeakSobolevJet.extendDirichlet_pairing` | `DirichletExtensionPairing.lean:34` | PASS。真实完整弱梯度内积等于内域与限制后测试 jet 的配对。 |
| 10 | `Carleman.WeakSobolevJet.extendDirichlet_poisson_test` | `DirichletExtensionPairing.lean:41` | PASS。同一 f 的内域弱方程传到外域，但仅针对原支持在 T 的测试。 |
| 11 | `Carleman.subdomainZeroExtend_test_inner` | `DirichletExtensionHessianTest.lean:14` | PASS。实际标量 L² 与同一紧支测试的配对严格保持。 |
| 12 | `Carleman.subdomainZeroExtend_derivativeTest_inner` | `DirichletExtensionHessianTest.lean:25` | PASS。实际方向导数测试的配对严格保持，使用已证明支持不扩大的导数测试。 |
| 13 | `Carleman.derivativeComponent_subdomainZeroExtend` | `DirichletExtensionHessianTest.lean:34` | PASS。任意阶 Sym 坐标抽取与真实 L² 零延拓交换。 |
| 14 | `Carleman.WeakSobolevJet.extendDirichlet_hessian_test` | `DirichletExtensionHessianTest.lean:41` | PASS。原 H¹ 延拓梯度与内域支持测试的分部积分，右侧为单独延拓的实际 Hessian 分量，负号正确。 |
| 15 | `Carleman.exists_dirichlet_weak_solution` | `DirichletWeakSolve.lean:13` | PASS。有界开域、d>0 上通过真实 coercive form 的零移位 resolvent 构造 H¹₀ 弱解。 |
| 16 | `Carleman.dirichlet_weak_solution_gradient_bound` | `DirichletWeakSolve.lean:25` | PASS。原方程以解自身为测试，得到 ‖∇u‖≤2R‖f‖。 |
| 17 | `Carleman.dirichlet_weak_solution_energy_bound` | `DirichletWeakSolve.lean:41` | PASS。真实 value 与全部梯度的平方能量≤(((2R)²+2R)‖f‖)²。 |
| 18 | `Carleman.dirichlet_subdomain_energy_bound` | `DirichletSubdomainSolve.lean:13` | PASS。外域同一 slab 界和载荷限制收缩，给原外域延拓 jet 的统一 H¹ 界。 |
| 19 | `Carleman.exists_uniform_dirichlet_subdomain_solutions` | `DirichletSubdomainSolve.lean:26` | PASS。先固定外域及 f、选同一非负常数，再量化所有开内域并构造真实弱解。 |
| 20 | `Carleman.SpatialTest.eventually_support_subset` | `SpatialTestExhaustion.lean:12` | PASS。实际紧支持由递增开覆盖最终包含，阈值允许依赖测试。 |
| 21 | `Carleman.exists_dirichlet_H2_of_exhaustion` | `DirichletExhaustionLimit.lean:17` | PASS。给定真实 H² 内域解族和统一 Hessian 界后，内部供应全部原 H¹₀ 逼近及最终测试身份，得到同一 f 的真实 H²∩H¹₀ 解。 |

## 原文对应与完整前提

固定原稿 2659–2664 行 `prop:analytic-realizations` 用 Grisvard Theorem 3.2.1.2 证明实际 Dirichlet Laplacian 的 D(A)=H²∩H¹₀ 及椭圆估计。本报告同时参照本验收线程已直接查看的 `/tmp/carleman-pdf-read/regularity-159.png` 至 `regularity-161.png`：印刷 147 页给平滑凸内域逼近，148 页取真实内域解及统一二阶界，149 页用测试支持最终进入内域后的积分身份识别极限二阶导数。

T131 已把这一过程中“由实际内域解构造全域 H¹₀ 逼近、取得统一一阶界、验证最终局部测试身份、完成极限”组合起来。最终定理仍明确输入：S 有界且开、d>0、同一 f∈L²(S)；Tₙ 开、Tₙ⊆S、单调递增并覆盖 S；每个 uₙ 是 Tₙ 上实际 H² jet，其一阶截断在原 H¹₀(Tₙ)，且 −Δuₙ=f|Tₙ；最后要求同一 C≥0 对全部 n 满足 ‖field₂uₙ‖≤C。没有把这些内域 H² 解及二阶界当作已构造事实。

输出 v 是 S 上真实 H² jet，value(v)∈原 H¹₀(S)，`negativeLaplacian v=f` 是原 L² 中的严格等式，并有 ‖field₂v‖²≤card(Sym(Fin d),2)C²。最终定理不输入全域逼近族、统一 H¹ 界、测试极限、候选 Hessian 收敛或 H² 零延拓。凸性和内域光滑性不被这个极限工具使用；它们应在后续构造上述内域解和统一二阶估计时落实。

## 测度、延拓与实际配对

第 1–5 项的底层对象是 volume.restrict T 与 volume.restrict S 的真实 L² 等价类。零延拓的 a.e. 表示是 T.indicator u；T 可测是明确输入，T⊆S 仅在恢复、等距和伴随配对等需要嵌套的结论中要求。限制恢复通过真实 a.e. 代表和测度单调性证明。范数上界由限制收缩与全空间零延拓等距给出，下界由限制回 T 后恢复 u 给出，没有丢失或添加边界质量。

内积等式直接展开 L² 积分，将零延拓写为 indicator，然后使用 `(volume.restrict S).restrict T=volume.restrict T`，其关键集合等式是 T∩S=T。最后使用限制后的 a.e. 代表。这既适用于标量，也适用于原 Euclidean 梯度字段；没有把不同区域的积分当成定义性相等。

`extendDirichlet` 的既有定义是：先由原 H¹₀ 图闭包证明全空间真实 H¹ 零延拓，再限制到 S。`extendDirichlet_mem` 使用真实紧支测试逼近序列、全字段延拓连续性、外域 H¹₀ 的闭性证明延拓仍属于原 H¹₀(S)。新字段等式是该实际构造的定义性等式；精确字段范数及梯度配对随后由第 4、5 项得到。

第 6 项用原弱 jet 的 value 单射恢复测试的完整 H¹ jet，不能理解为仅恢复点函数。第 10 项先把外域梯度配对拉回 T，在 T 上用实际弱 Poisson 身份；右端通过测试自身的零延拓身份和限制伴随关系恢复为外域同一个 f 的配对。它量化的是 φ∈SpatialTest T，未声称零延拓的解对所有 SpatialTest S 都满足外域方程。

## Hessian 局部身份及边界处理

第 12 项把真实 `derivativeTest e` 送入测试配对等式；其值是实际 Dφ·e，拓扑支持包含于 φ 的原支持，所以仍是 T 的合法测试。第 13 项只是任意阶 Euclidean 分量的 L² 映射与延拓交换，本身不宣称任何二阶弱可微性。

对 u∈H²(T) 且 truncate₁u∈H¹₀(T)，第 14 项把外域延拓梯度分量移回 T，并把延拓 Hessian 分量移回 T。剩余正是原 u 的第 1 层弱链：

\[
\langle D_i u,D_j\varphi\rangle_T
=-\langle D_jD_i u,\varphi\rangle_T.
\]

因此外域配对的右侧是单独零延拓的 D_jD_i u，负号严格保留；没有假设 H² 零延拓，没有删除边界通量，也没有对支持越出 T 的测试套用这条身份。混合指标是原 `Sym.cons j (Sym.cons i Sym.nil)`，与原弱导数字段的次序一致。

## 真实弱解与外域统一一阶界

第 15 项使用 `boundedDirichletOriginalForm` 的真实梯度形式。该依赖在原 H¹₀ Hilbert 图空间上，由已证明的 slab Poincaré 不等式给 coercivity；真实形式定义域、闭性、L² 稠密性及完整梯度均来自原 Dirichlet 空间。`FormSolve.resolvent 0` 用 coercive 双线性形式的实际可逆映射构造解，`resolvent_equation` 给 Au=f。`dirichlet_operator_graph_iff` 将真实关联算子图识别为 H¹₀ 中的分布负 Laplacian 图。没有先假设 D(A)⊆H²，也没有把二阶正则性藏在弱解存在性里。

第 16 项使用 `isWeakNegativeLaplacian_iff_dirichlet` 将原全部紧支测试身份经 H¹₀ 图闭包延伸到所有 H¹₀ 变分测试，因此可以合法地取解自身，得到

\[
Y^2=\langle f,u\rangle\le\|f\|X,\qquad
X=\|u\|\le 2RY,\qquad Y=\|\nabla u\|.
\]

由非负性推出 Y≤2R‖f‖；证明用正反例排除法处理 Y=0，没有除以零。继而 X≤(2R)²‖f‖，并以原 `norm_zero_field` 将标量 value 范数精确识别为第 0 阶字段范数，得到 X²+Y²≤(((2R)²+2R)‖f‖)²。

第 18 项对任何内域 T 使用外域同一 slab 条件，载荷是同一 f 的实际限制，且 ‖f|T‖≤‖f‖；两阶字段延拓等距将该界移到 S。第 19 项先从外域有界性选 R>0 及坐标 i=0，令 C₁=((2R)²+2R)‖f‖，然后才量化任意开 T⊆S。C₁ 可以依赖固定 f 的范数，比例系数仅来自外域 R；不依赖内域边界曲率、大小、编号或网格。每个内域弱解在代码内通过上述真实形式求解得到，不要求调用者提供 H¹ 界。

存在性与穷竭主定理明确要求 d>0，梯度/能量界要求 i:Fin d；这正覆盖原论文 d≥1，未错误声称零维负 Laplacian 对任意载荷可逆。一般 L² 延拓、测试及紧覆盖引理不需此正维限制。空外域或空内域、f=0、R=0 的有意义条件情形均未被除法排除；没有额外非空假设。

## 紧支持最终进入内域及真实极限

第 20 项使用 φ 的实际紧拓扑支持、开覆盖和单调性，以 max(i,j) 证明覆盖有向；pinned mathlib 的 `IsCompact.elim_directed_cover` 给一个 N 包含整个支持。单调性再给所有 n≥N 的包含。N 可以依赖 φ；这不是对所有测试断言同一个统一起始指标，也不需要预设定量到边界距离。

主定理定义 Uₙ 为 uₙ 一阶截断的真实 H¹₀(S) 延拓，Aₙᵢⱼ 为 Hessian 分量单独的 L² 子域零延拓。Uₙ∈H¹₀(S) 由真实闭包延拓定理供应；统一 H¹ 界来自第 18 项。A 的范数由延拓等距、原 Euclidean 坐标投影收缩和输入完整 Hessian 界得到 ≤C。

对每个原 φ∈SpatialTest S，待其支持进入 Tₙ，代码以同一个值函数、同一个光滑性和紧支性构造 ψ∈SpatialTest Tₙ，并证明 `ψ.monoDomain (hTS n)=φ`。用第 14 项得到二阶最终测试身份，用第 10 项得到同一 f 的最终 Poisson 身份。导数测试与原测试没有在这一过程中被替换成不同函数。

随后实际调用的 `exists_dirichlet_H2_of_bounded_approximants` 不是一个待证明的紧性假设：其已验收源码从真实可分 Hilbert H¹ 图空间中、在原闭 H¹₀ 子空间内抽取同一个严格递增子列。全部字段配对沿该子列弱收敛，H¹₀ 成员和统一能量界保留；使用 CLM 的真实伴随把弱收敛传给梯度分量。C144 的有界测试构造内部得到同一 H¹ 极限的 H² jet，不要求候选 Hessian 收敛。

同一子列也保留逐测试最终 Poisson 身份，故极限 H¹ 状态满足原 f 的弱方程。真实 `negativeLaplacian` 是二阶对角分量之和的负值；其 H² 测试身份和 `unique_rhs` 的原测试密度证明，使输出 `negativeLaplacian v=f` 为实际 L² 等式。没有换成任意替代右端项。二阶范数平方中的 card(Sym(Fin d),2) 维数因子保留，没有虚称最优常数 1。

## 依赖版本与公理

七模块的 Carleman import 闭包共 **122** 个模块，其中 **115** 个既有模块与 base 逐文件相同。另对关键已接受 declaration_version 检查递归闭包：C146 `DirichletSubdomainExtension` 的 71 个模块与 `5c1c62ee09ab89d7e28c0b484c02494958856b33` 相同；C145 `DirichletH2ApproximationLimit` 的 80 个与 `bee8a93d0856f84c9280d10a19f50da7da2a362f` 相同；C056 `DirichletForm` 的 49 个与 `4f669626b3228adea39a16fbf6c1d22313763331` 相同；C098 `SubdomainContinuity` 的 66 个与 `59452751f05398e3446ed5305638a1e20dc89061` 相同；C144 `SpatialTestDerivative` / `WeakH2BoundedLimit` 的联合闭包 57 个与 `5f407936e769fa9742463e35a8d7d8e29970aa36` 相同。未将旧验收直接套用于发生变化的依赖。

21 项实际公理输出仅含 `propext`、`Classical.choice`、`Quot.sound`。核查全部原始文件的 **2421** 条显式公理记录：2413 条仅使用该基础集合，8 条不依赖公理，无异常公理；末行为 **6934** 项 Carleman 声明递归审计 PASS。显式打印条数与全局递归审计数未混同，无 `sorryAx` 或未证明的数学公理。

固定 Lean toolchain 为 4.35.0，远端记录编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；manifest 与本机干净 mathlib checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿未改，其 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 实际 CI、日志及原始产物

实际读取固定 `/tmp/carleman-t131-exhaustion-target.log` 的 **3285 jobs** 成功，以及 `/tmp/carleman-t131-exhaustion-full.log` 的 **3919 jobs** 成功和 6934 项审计末行。本验收核查已有固定日志，未声称重新运行全库构建。

独立通过 GitHub API 最终查询 [run 39213443617 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39213443617/attempts/1)：main head SHA 精确匹配 checked_sha，run 为 completed/success；state-check **117931770665**、lean **117931770793**、dashboard / snapshot **117932978769** 三个实际作业全部 completed/success。

独立查询 artifact 元数据并自行 `gh run download`：`lean-ci-result`（artifact ID **12168722128**）下载至 `/tmp/carleman-t131-exhaustion-main-ci/result.json`；`lean-declaration-evidence`（artifact ID **12168950965**）下载至 `/tmp/carleman-t131-exhaustion-main-axioms/axioms.txt`。result 实际 PASS，checked_sha 与 source_head_sha 均为本报告完整 SHA，finished_at 为 **2026-10-19T07:05:11.567417+00:00**，target 是 `Carleman`。

远端原始 axioms 与固定 `/tmp/carleman-t131-exhaustion-local-axioms.txt` 独立逐字节比较完全一致：均 **2,120,125 bytes**，SHA256 均为 **`dcd04a59278984515610a0139ce55b7ee5779b1bf115cc06e96d502f3d18abb1`**。摘要对应原始文本，未混同 artifact ZIP；前缀包含 T131，未复用历史其他阶段的同名证据。

## 最终结论与剩余义务

固定版本 21 项声明通过独立语义、完整类型、依赖、公理及同 SHA 三项 CI 验收，无阻断发现。C147 可登记为 **REVIEWED / AUXILIARY**。实际 H¹₀ 弱解存在、外域统一 H¹ 界，以及给定真实 H² 内域解和统一 Hessian 界后的完整穷竭极限已成立。

光滑内域 H² 正则性、统一二阶先验界和具有所需光滑凸几何的穷竭构造仍未清偿；弱解存在性不自动提供这些 H² 内域输入。本批不据此宣称原 Dirichlet 正则性及 A1–A3 已全部完成，P023 与其他 PAPER 项不提升，14/26 不变。通知后冻结本报告及 reviewed_at。
