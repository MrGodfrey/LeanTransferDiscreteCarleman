# T264 / C280 独立本机数学验收

- checked_sha / source_sha：`a53469931caaf52a06accc38b94778d5e007a5b8`
- mathematical_base：`556cdaef8f161664657049e6fc2829b82fbb4404`
- reviewed_at：`2026-10-20T11:33:57+00:00`
- reviewer：独立 Agent `/root/accept_spatial_foundations`，未参与实现。
- result：**PASS，13 / 13 显式定理；公理检查 PASS。**
- scope：**AUXILIARY**。C280 可登记 REVIEWED；不提升 P024，原文覆盖保持 **20 / 26**。
- evidence_source：**local**。核对固定 Git 源码、本地构建及完整递归公理证据；未查询远端 CI 或看板，未重复构建不变闭包。

本报告完整读取三个新增模块的实际证明及 raw 中全部 13 项展开类型，并核对原稿、T264 分析、MATH_SPEC、唯一台账和直接数学依赖。报告或执行者说明不替代源码审查。后续工作树中的 `DirichletExhaustionStrong`、`SubdomainLpLimit` 及动态审计文件均未用作本批数学证据。

## 原文对应与实际最终结论

原 `paper/main.tex:292–299` 的权族为闭区间 C²、零至二阶端点匹配及
\[
q\ge q_c\ge1,\qquad |q'|\le\beta q^2,\qquad |q''|\le\beta^2q^3.
\]
原 `prop:continuousCE`（2672–2731）要求对完整弱周期轨迹，以原梯度、原热残差及指数 \((3,1;3)\) 给出双向、T 统一估计。本批清偿的是该证明的**光滑内域上的全弱态密度传递**，并非外域 Proposition A.3。

固定正维有限严格半空间外域
\(S=\{x:\forall i,\ b_i<\ell_i x\}\) 有界，固定非空开集 \(W\subset S\)。定理先选择
\[
c\in W,\quad \lambda\ge1,\quad 0<\beta\le1,\quad q_c\ge1,\quad C>0,
\]
以及同一实际函数 \(\rho(x)=e^{-\lambda\lVert x-c\rVert^2}-2\)，满足全空间 \(-2<\rho\le-1\)。随后才量化全部内域序号 n（保留明确的 \(c\in S_n\) 条件）、TimeGrid g 及其任意正周期 T、原闭区间 q、两个符号及全部原弱轨迹。这里
\[
S_n=\left\{x:\sum_i e^{(n+1)(b_i-\ell_i x)}<\tfrac12\right\}.
\]
最终对同一 `PeriodicWeakTrajectory g B.domain B.operator`，其中 B 是 \(S_n\) 上原 Dirichlet 形式关联算子，得到
\[
\int_0^T q^3\|\theta u\|_{L^2(S_n)}^2
+\int_0^T q\|\theta\nabla u\|_{L^2(S_n)}^2
\le C\left(
\int_0^T\|\theta(\epsilon\partial_tu+Au)\|_{L^2(S_n)}^2
+\int_0^Tq^3\|\theta 1_Wu\|_{L^2(S_n)}^2\right),
\quad \epsilon\in\{1,-1\}.
\]
其中 \(A=-\Delta\)，\(\theta=e^{q\rho}\)，梯度是同一原 `domainValue` 的 canonical 弱 H¹ jet 的完整一阶字段。观察项实际位于 \(S_n\cap W\)，不要求 W 包含于每个内域。最终定理没有光滑轨迹、H² 逼近、图密度、全局 q 延拓或假设热估计等额外输入。TimeWeight 的辅助全局界由区间连续性构造，不成为原权族的新限制。

## 全部声明逐项审查

以下源码位置均指 checked_sha；全部声明位于 `Carleman` 命名空间。raw 行号指固定 `carleman-t264-uniform-inner-weak-heat-local-axioms.txt`。

| # | 声明与固定源码位置 | raw 行 | 独立数学结论 |
|---|---|---:|---|
| 1 | `exists_smooth_operator_graph_approximation_of_H2` — `Spatial/InnerGraphDensity.lean:14` | 45471 | PASS。泛型 helper 显式保留 H² 状态、其原值/算子身份及真实强逼近。每个 approximant 的 H¹₀ 资格构造原 `dirichletH2DomainElement`，实际作用为负 Laplacian；值 CLM 与负 Laplacian CLM 的两项强极限给完整算子图强极限。 |
| 2 | `exists_halfspaceSmoothInner_operator_graph_approximation` — 同文件:51 | 45484 | PASS。对任意原算子图元素，从原关联图恢复 H¹₀ 弱 Poisson 解，内部调用实际内域 H² 正则性与 T257 强密度，清偿第 1 项的所有特殊前提。未预先缩小原关联域。 |
| 3 | `halfspaceSmoothInner_classicalTimeCore_dense` — 同文件:73 | 45500 | PASS。每个整数频率的两个任意原算子图系数均取真实强逼近，实际 harmonic 图 CLM 与全周期图稠密性给完整 `classicalDirichletTimeCore` 稠密。包含 H 连续迹、弱时间导数及实际 A 场的拓扑。 |
| 4 | `weighted_domain_density_integrable` — `Spatial/DomainHeatIntegral.lean:17` | 45508 | PASS。真实 \([0,T]\times\overline S\) 紧性、连续 q/ρ/F 给实际加权产品积分可积性，再限制至真实 S；不假设待证积分可积。 |
| 5 | `timeSq_eq_domainTimeIntegral_of_norm_sq` — 同文件:34 | 45516 | PASS。保留泛型真实可积性前提，以 Fubini、Icc/Ioo 时间测度相等及乘子半范数平方积分身份得到精确等式；正确处理先时间 a.e.、再空间 a.e. 的代表。 |
| 6 | `timeSq_eq_domainTimeIntegral_of_continuous` — 同文件:61 | 45528 | PASS。由第 4 项内部供应第 5 项可积性，`rpow_natCast` 精确还原自然数指数。未丢失任何权因子。 |
| 7 | `timeSq_eq_domainTimeIntegral_of_indicator` — 同文件:74 | 45538 | PASS。只要求 W 可测；连续的是未乘示性的密度，实际示性函数由可积性限制处理。逐点示性乘法身份与两层 a.e. 身份正确，不假设观察边界光滑或零测。 |
| 8 | `dirichletHeatLeft_eq_domainIntegral` — 同文件:117 | 45552 | PASS。原 pathL2 代表与实际弱梯度范数身份分别给 q³ 值项、q 梯度项；同一个 F，完整 Euclidean 梯度，精确系数一。 |
| 9 | `dirichletHeatRight_eq_domainIntegral` — 同文件:139 | 45565 | PASS。显式原字段身份给 \(\epsilon\partial_tF-\Delta F\)，残差符号正确；原 cutoff 的 compLp 身份给真实 W 示性 q³ 观察项。可积性内部供应。 |
| 10 | `dirichletHeat_le_of_classical_of_dense` — `Spatial/UniformInnerWeakHeat.lean:15` | 45584 | PASS。泛型 helper 明确保留核心密度和核心估计输入；四能量连续性使同一不等式的解集闭合，直接以原 C 取闭包，无新损失。 |
| 11 | `halfspaceSmoothInner_uniform_weak_C2_heat_both_signs` — 同文件:30 | 45595 | PASS。T263 同一中心、profile、β、qc、C 先于所有 n/g/w/ε/p。实际核心成员同时提供光滑 F、严格周期、全 frontier 零值及真实导数字段；第 3、8、9 项清偿第 10 项前提，扩到全部原周期图。 |
| 12 | `halfspaceSmoothInner_uniform_weak_interval_C2_heat_both_signs` — 同文件:78 | 45632 | PASS。对任意原区间 q 构造实际有界 TimeWeight，closed-interval EqOn 同时保持两阶 `derivWithin`、三个端点条件和原预算；能量 EqOn 身份消去该辅助扩张，无全局 q 正则/周期假设。 |
| 13 | `halfspaceSmoothInner_uniform_original_weak_C2_heat_both_signs` — 同文件:141 | 45669 | PASS。对每个完整原弱轨迹使用实际 `toPeriodicGraph` 和原四能量身份，保持同一值、弱导数、canonical 梯度、算子作用及观察。没有替换轨迹或新增逐时 D(A) 连续性前提。 |

## 关键证明与量词核对

**同一原算子与完整图密度。** `dirichlet_operator_graph_iff` 从实际关联形式恢复原 H¹₀ 与全分布测试方程。第 2 项取得的 H² jet 的整个 H¹ 截断等于原状态，负 Laplacian 等于原图的 A 分量。第 1 项的每个图元素由真正 H²∩H¹₀ 成员构造，`graphH` 与 `graphA` 分别等于同一光滑函数的原 L² 类及负 Laplacian。收敛在 \(H\times H\) 的原闭算子图子类型中，未仅证明值 L² 收敛。

已直接读取 `HarmonicStateDensity`、`HarmonicGraphContinuity`、`ClassicalHarmonicTimeCore` 和 `ClassicalDirichletTimeCore`。全周期图的空间是连续 H 迹与两个 L² 场的闭子空间，弱导数、原算子图及周期端点条件均真实。谐波稠密性由载荷谐波稠密性和真实 `constantSolve` 的连续满射推出；系数逼近经完整图上的 harmonic CLM 传递，不是任意有限维替代轨道。核心定义要求全时空 C∞、对所有时间的真实边界零值，并明确给出时间导数及负空间 Laplacian 的 a.e. 身份。

**真实四积分与代表。** 已读取 `DirichletPeriodicGradient`、`PeriodicClassicalRepresentatives`、`DirichletHeatIntegral` 和新 `DomainHeatIntegral`。梯度由实际原能量载体的原梯度 CLM 构造；能量嵌入等于原 pathL2 后，弱导数唯一性识别同一光滑代表的梯度平方范数。原 ε 倍时间导数与 A 场相加产生 ε∂t−Δ；并非任意替身 residual。Fubini 在实际受限产品测度的可积密度上调用，时间 Icc/Ioo 仅由端点零测转换。每个有限 a.e. 合并均在真实 Lp 操作身份下进行，没有不可数测试的 a.e. 量词交换。观察只用可测 W 的实际乘子，未把示性函数当连续函数。

**完整弱态与原闭区间权。** 已直接读取 `PeriodicGraphSpace`、`PeriodicGraphEquivalence`、`IntervalTimeWeight`、`IntervalHeatEnergies` 与 `WeakTrajectoryHeatEnergies`。`toPeriodicGraph` 保持原闭区间 H 迹及两个实际 L² 字段；D(A) 成员只需原来的时间 a.e. 条件。canonical 梯度通过同值弱 jet 的唯一性与周期能量字段对齐，原轨迹无需另假设梯度可积。TimeWeight 的 clamp 扩张只辅助固定区间估计；EqOn 保持闭端点处一阶及二阶 within 导数，最后陈述只含原 q。对任意原 C² q，有限上界由紧区间连续性供应，与原稿允许取 \(q_{\max}=\max q\) 一致。

**统一性。** 核心调用的是已审 T263 的实际 `halfspaceSmoothInner_uniform_interval_C2_heat_both_signs`，本次重读其完整实现及两个符号、闭区间权结论。所有全局参数在 n、T、q、ε、状态之前选定；profile 的函数值不依赖 n，只有其 L² 测度接口随域变化。固定域/权下的 CLM 连续性常数可以依赖该域、T、q；它们只证明闭包资格，没有被乘入 C，也没有用作跨域统一估计。第 10 项只是对已成立的同一个不等式取闭包，因此不改变 β、qc 或 C。第 12、13 项是精确身份改写，也没有任何常数损失。

保留 \(d>0\)，包括原 d=2,3；本批未声称零维版本。保留 \(c\in S_n\)，没有把空内域当成非空正则域；该条件在未来外域极限中需由真实穷竭供给。没有假设 W 完全落入各内域，也没有引入网格尺度、小时间步或时间空间耦合。

## 固定依赖与本地证据

从三个新模块递归解析得到 **418 个 Carleman 源模块**：三个是本批新增，另外 **415 个与数学 base 的 Git blob 逐字节相同**。进一步按各自已验收 proof 独立比较：

| 关键根模块 | 已验收 proof | 完整相关递归源码逐字节不变 |
|---|---|---:|
| `UniformInnerC2Heat` | `556cdaef8f161664657049e6fc2829b82fbb4404` | 286 |
| `FiniteStrongH2Density` | `e90a9dc75ebc85da3ccb5dd1bb740fd3d255db1a` | 298 |
| `FiniteLocalH2Gluing` | `ebc85ddad04c9b4008fa5b3e89a05696eff19bfb` | 249 |

T263 冻结报告 `37f8ca79e4c59de8d834defb1e17cf28521952ce`（reviewed_at `2026-10-20T11:21:48+00:00`，18/18 PASS）已全文读取。T257 强密度的冻结报告为 `ce10da05a21b2b2bcf4ef5f5661d3da7f64927ae`；T246 原内域 H² 正则性为此前独立验收边界。实际当前调用的两个终端证明、原关联图身份均重新读取；没有以报告替代调用和版本检查。

本地证据前缀 `/tmp/carleman-t264-`：

| 项目 | 实际读取及核对结果 |
|---|---|
| `local-evidence.json` | `source=local`，`status=PASS`；checked_sha/source_head_sha 均为本报告 proof；`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 记录 exit 0；finished_at `2026-10-20T11:25:28.846056+00:00`。 |
| `foundation-build.log` | `DomainHeatIntegral`、`InnerGraphDensity` 构建成功，3636 jobs。 |
| `target-build.log` | `UniformInnerWeakHeat` 构建成功，3645 jobs；109 bytes，SHA256 `3cab2c8cdaa7cd21fea24c57f9ebd5b849fc59ce256cdc10c0e0c895da4bc2f9`。 |
| `build.log` | 根 `Carleman` 构建成功，4309 jobs；80 bytes，SHA256 `62c0d9901fe04f35906808a68008cf0e4b7e8bd2bbee3c7393325c3f0d87bd2c`。 |
| `local-source-manifest.txt` | 1067 项、115799 bytes，SHA256 `9e8ba3d32ff095e3a58d3818a34f9f29bea44d6eb1dc4c7cff8ca5aef3746e94`。集合精确等于固定树全部 Lean 文件及三个工具链/包配置文件；逐项 SHA256 对固定 Git blob 全部匹配，无重复或遗漏。 |
| `uniform-inner-weak-heat-local-axioms.txt` | 3521761 bytes，SHA256 `ac0e054e14982e3f5c56eb8bd5cf4f5a84abe06208ee4b00b2141a25dd9ea9db`；raw 全部 4209 条显式公理记录仅含正常基础公理或无公理；末行完整递归检查 **10371** 个 Carleman 声明通过。 |
| `axioms.log` | 0 bytes。 |

Lean 为 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），固定 mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；实际固定配置与证据相符。全部新模块均由固定根 `Carleman.lean` 导入，13 项声明均有实际 `#check` 和 `#print axioms`。递归审计遍历全部 Carleman 命名空间（含私有名还原），调用 `collectAxioms`，只允许 `propext`、`Classical.choice`、`Quot.sound`，且检查器与基线相同。无 `sorryAx` 或额外数学公理。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改变原命题。

独立核对中间结果保存在 `/tmp/carleman-t264-review-evidence.json`、`review-types.txt`、`review-dependency-check.json`；它们是审查记录，原始构建/公理证据仍是上表文件。本报告没有将本地结果写成远端 CI 成功。

## 最终范围判断

**13/13 PASS，无阻断缺陷。** 本批已经在每个含共同中心的真实光滑内域，对全部原弱周期轨迹、原区间 C² 权和两个时间方向完成同一统一估计；通用 helper 的 density/CE 前提在具体终端定理内部清偿。

尚未完成的是原外域轨迹与内域解的实际极限传递。不能从各内域的完整估计直接宣称外域 `prop:continuousCE` 已完成，也不能仅凭同一常数省略该极限。C280 可按 **AUXILIARY REVIEWED** 接受；P024 保持未完成，覆盖 **20/26**。本报告正文和 reviewed_at 在提交后冻结。
