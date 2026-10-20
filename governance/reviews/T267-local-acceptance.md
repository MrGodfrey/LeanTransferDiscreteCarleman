# T267 / C283 / P024 独立论文级验收

- checked_sha: `0a1808091e23386fc8c06d4e2a3434d1fa9f2a34`
- mathematical_base: `eb792343d4c1d275d0341ca5dc93e17b4bc89b7d`
- reviewed_at: `2026-10-20T12:15:19+00:00`
- reviewer: 本机独立 Agent `/root/accept_spatial_foundations`
- result: **PASS，16/16；完整 PAPER Proposition A.3 / P024**
- scope: 15 个新显式声明（3 定义、12 定理）及固定版本既有 `Carleman.box_heat_continuous_data`。C283 可按 PAPER 范围验收，P024 可升级为完成，原文覆盖可由 20/26 增至 21/26；本报告不修改台账。

未发现阻断缺陷。以下结论来自固定 Git 源码、完整展开声明、实际调用依赖和原稿的独立数学核对；构建和公理证据用于确认该版本的形式验证，不代替语义审核。按照现行本机验收协议，没有查询远端 CI、看板或重新运行整库构建。

## 原命题与最终结论

已核对固定 `paper/main.tex:2672–2731` 的 Proposition A.3、`:2659–2665` 的适用域、`:292–299` 的时间权类，以及 `:374–381` 的 A4。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，本批未修改原稿。

实际结论是原 Dirichlet Laplacian 的估计

\[
\int_0^T q^3\|\theta u\|_H^2+
\int_0^T q\|\theta\nabla u\|_{L^2(\Omega;\mathbb R^d)}^2
\le C\left(\int_0^T\|\theta(\epsilon\partial_tu+Au)\|_H^2+
\int_0^T q^3\|\theta\,1_{\omega_0}u\|_H^2\right),
\qquad \theta=e^{q\rho}.
\]

这里的梯度是实际一阶弱导数字段，`A` 是同一原闭形式的关联 Dirichlet 算子，右端观察量是真实区域示性乘法，指数为 `(3,1;3)`。不是假定某个抽象连续估计后再包装。

新有限半空间定理适用于有界开域 `{x | ∀ i, b i < ℓ i x}`、非空开观察集 `W ⊆ Ω` 和任意正维数，因而覆盖原二维、三维凸多面体。原 A4 明确观察集是非空开集；此处只要求包含于域内，未增加超出原 `ω₀ ⊂⊂ Ω` 的限制。既有实际盒定理对 `Fin (d+1)` 的任意正边长盒成立，覆盖原任意正整数维盒分支。

所得同一个全局函数为 `ρ(x)=exp(λ(-‖x-c‖²))-2`。实际 `interiorCarlemanProfile_contDiff` 给全局光滑性，且 `-2 < ρ ≤ -1`，满足原负权条件。`c, λ, β, q_c, C` 在所有时间网格、周期、时间权、方向和状态之前选定，`0<β≤1`、`q_c≥1`、`C>0`。任意 `T>0` 均可由一步、步长 `T` 的 `TimeGrid` 表示，使用该载体没有限制原周期。

最终区间定理直接量化任意 `q : ℝ → ℝ`，只要求原闭区间上的 C²、函数值及一二阶导数的两端匹配、下界和两项原导数预算。没有要求 q 在区间外光滑或满足额外全局界。两种 `ε=±1` 都在上述固定常数之后量化。

`finite_halfspace_original_weak_C2_heat_both_signs` 作用于同一原 `PeriodicWeakTrajectory` 的值、弱时间导数、原算子值及 canonical 弱梯度。已检查其定义和转入完整 `PeriodicGraph` 的桥：这是原 `H¹(0,T;H) ∩ L²(0,T;D(A))` 周期状态的表达，不要求状态在时间上光滑、逐时属于更小算子核、有限谐波，或另给空间 H²/密度前提。

## 全部声明逐项审核

下表名称统一位于 `Carleman` 命名空间，行号均为 checked_sha 的源码行号。完整类型同时核对固定原始审计文件；15 个新项位于其中第 45950–46130 行起，既有盒项位于第 32479 行起。

| # | 声明及固定源码位置 | 数学核对及结论 |
|---|---|---|
| 1 | `dirichletExhaustionApproximable`，`Spatial/ExhaustionPeriodicDensity.lean:16` | 定义原完整周期图内的真实子模；见证是每个原内域的周期图序列，四个零延拓场在共同 Bochner L² 乘积中同时强收敛。零、加法、数乘由实际 CLM 和极限规则构造，未预设闭性或稠密性。PASS。 |
| 2 | `dirichletExhaustionApproximable_dense`，同文件 `:35` | 每个真实双系数谐波图由 T266 构造同索引四场逼近；子模包含其线性张成，再由原完整周期图的谐波稠密性推出 Dense。不是只覆盖某个有限时间空间。PASS。 |
| 3 | `heatFieldsLeft`，`Spatial/HeatFieldEnergies.lean:10` | 四场中的真实值与完整梯度组成 q³/q 两项平方能量，未舍弃坐标。PASS。 |
| 4 | `heatFieldsRight`，同文件 `:15` | 使用同一四场的 `ε·dtime + operator` 整体残差及真实 `W` cutoff，观察指数 q³。PASS。 |
| 5 | `continuous_heatFieldsLeft`，同文件 `:22` | 由真实加权时间 CLM 和范数平方连续性得到乘积 L² 拓扑连续性；实际有限权界保证定义和积分，不靠不可积时默认零。PASS。 |
| 6 | `continuous_heatFieldsRight`，同文件 `:27` | 先连续线性组合残差和 cutoff，再取同一加权平方范数。固定 q、T 所需有界性只用于连续性。PASS。 |
| 7 | `heatFieldsLeft_dirichlet`，同文件 `:38` | 与原 `dirichletHeatLeft` 精确身份，字段来自实际原周期图和 canonical 弱梯度。PASS。 |
| 8 | `heatFieldsRight_dirichlet`，同文件 `:43` | 与原 `dirichletHeatRight` 精确身份，保留 ε、原 A 和观察区。PASS。 |
| 9 | `heatFieldsLeft_subdomain`，同文件 `:49` | 在 `T⊆S`、同一 profile 的内域 a.e. 身份下，实际 L² 零延拓保持两项加权能量，常数恰为 1。PASS。 |
| 10 | `heatFieldsRight_subdomain`，同文件 `:58` | 先以线性性把整个 `ε·dtime+operator` 零延拓，再用精确等距；cutoff 与零延拓实际交换。没有分别估计两项而放大常数，W 无需包含于内域。PASS。 |
| 11 | `dirichletHeat_le_of_exhaustion`，`Spatial/ExhaustionHeatTransfer.lean:13` | 对真实可逼近状态取四场强极限，再由原能量不等式集合闭性及第 2 项稠密性覆盖全部原周期图。此通用 helper 的共同内域 CE 前提明确暴露，并由第 12 项内部清偿。PASS。 |
| 12 | `finite_halfspace_weak_C2_heat_both_signs`，`Spatial/FiniteHalfspaceWeakHeat.lean:13` | 从 T264 取得统一 c/λ/β/qc/C；实际内域尾段包含 c、单调且覆盖原域，profile 是同一全局函数的限制；调用第 11 项时逐内域给出真实 CE。对全部原周期图、两方向成立。PASS。 |
| 13 | `finite_halfspace_weak_interval_C2_heat_both_signs`，同文件 `:65` | 真实区间延拓供应 `TimeWeight`；EqOn 同时传递端点值及两阶 within derivative；左右能量身份消去包装，结论回到原任意区间 q。PASS。 |
| 14 | `finite_halfspace_original_weak_C2_heat_both_signs`，同文件 `:128` | 原弱轨迹转入原周期图，并用实际能量身份返回同一 u、弱 dtime、A 和梯度。没有添加内域估计、光滑性、密度或目标能量假设。PASS。 |
| 15 | `finite_halfspace_heat_continuous_data`，`Transfer/FiniteHalfspaceHeatContinuous.lean:16` | 展开真实 `sobolevGeometry`、`heatDifferentialFamily`，将第 14 项逐项改写为原连续接口；`IntervalQClass` 的全部字段实际用于调用。离散辅助载体位于常数之后，不限制连续轨迹。PASS。 |
| 16 | `box_heat_continuous_data`，`Transfer/BoxHeatContinuous.lean:16`，既有 | 重新核对固定最终类型和实际盒弱轨迹/区间权证明链；任意正边长、任意正整数维、完整原周期轨迹及两方向，内部供给连续估计。其完整数学依赖闭包与已验收 T166 逐字节不变。PASS。 |

## 真实穷竭及闭包传递

已直接检查 `HarmonicDomainLimit`、`InnerGraphLimit`、`DirichletExhaustionStrong` 和 `SubdomainLpLimit` 的实际构造。内域谐波系数由原零位移 coercive resolvent 产生，算子值恰是外域 `Az` 的真实限制；H¹ 强逼近来自能量正交、原 H¹₀ 紧支测试逼近和最终支撑包含。载荷零延拓是实际 `1_T f`，用真实 L² 支配收敛得到其强极限。

对任一原谐波，两系数分别逼近后，值、时间导数、算子值和梯度分别由实际谐波 CLM 表达。时间导数中的频率及两个系数的符号保留；四场使用同一内域索引。没有把“存在某个弱极限”改写成所需的强收敛，也没有逐场重新挑不相容的状态。

`HarmonicStateDensity` 的稠密性来自原载荷谐波稠密性和实际 `constantSolve`，覆盖完整原周期图。T267 因而分两步证明：先在第 1 项子模中由内域强极限传递同一个 C，再对原周期图的闭不等式集合取闭包。没有假设第 1 项子模本身闭合，也不需要未经证明地声称任意外域状态已有某种选定内域强逼近序列。

实际零延拓仅作用于四个 L² 场。特别是内域 `A_n p_n` 的零延拓，不被错误识别为 `A(E₀p_n)`；代码没有要求 `E₀p_n ∈ D(A)` 或假定 H² 状态可以跨真实边界零延拓。梯度的零延拓资格由真实 H¹₀ 桥保证。

对于 `T_n=halfspaceSmoothInner ℓ b (N+n)`，原几何定理供应开性、闭包内含、单调性和全覆盖。选择包含 c 的尾段后，每个内域都适用同一个已证 CE。该尾段的选择在证明脚本中出现在固定 g 后，但所用事实只依赖原几何和 c；最终常数已在 g 之前选定，N 不出现在估计常数或结论限制中。

## 常数、范数及完整接口检查

1. T264 的内域估计已针对全部原弱周期状态、两方向及区间 C² 权成立，并具有同一个先于内域序号的 C。T267 不是重新输入这一结论：最终定理的证明内部逐项调用它。
2. `SubdomainWeightedExtension` 给出同一 profile 下真正加权 L² 等距；Bochner 交换沿实际 `compLpL`。观察乘法在内域自然对应 `W∩T_n`，在外域为同一个 W，不要求原观察集整体落入每个内域。
3. 四场能量与原时间积分的身份来自真实加权 Bochner 范数和 Fubini 桥。`heatDifferentialFamily` 的 0/id 系数确实返回完整一阶弱导数场。原轨迹 `domainValue` 只在几乎处处用于原算子/梯度，值配对用真实 a.e. 还原，未交换不合法的逐时 Lp 代表。
4. 固定周期的谐波频率、`√T` 连续性界、外域 Poincaré 常数及固定权的有界乘法常数只服务于收敛和连续性，没有进入最终 CE 常数。两次极限都保留原共同 C；不存在内域个数、时间步数或网格参数额外因子。
5. 最终接口没有只使用一阶 `TimeWeight.Regularity` 代替原 qclass。`IntervalQClass` 的 C²、两阶预算和三个端点条件均被读取；原 q 区间定理还消去了全局 TimeWeight 表示。
6. 未保留额外的算子域、光滑轨迹、内域正则性、密度或共同内域估计假设。有限半空间几何与非空开观察集是原域/观察集条件的具体表达；原 P023 的实际关联域结果和原闭形式被复用，没有换成任意替身算子。

证明路线通过真实光滑内域和四场极限展开原稿最后的密度步骤。它与原命题有相同最终范围和量词；不要求逐字复现原稿对多面体面通量的证明路线。此处完整 PAPER 验收仅针对 Proposition A.3，不自动验收之后的物理控制、其他命题或任何未来工作树文件。

## 依赖版本和独立报告

直接读取本批五个新模块全部证明和 16 项完整展开类型，并对上述数学关键依赖作实际源码检查。五个新模块加既有盒入口的本地递归源码闭包共有 454 模块，其中 449 个既有模块与 mathematical_base 的 blob 完全相同；没有夹带旧证明改写。

进一步逐文件比较下列关键已验收边界：

- `HarmonicDomainLimit` 的 386 模块闭包与 T266 proof `eb792343d4c1d275d0341ca5dc93e17b4bc89b7d` 全部不变。
- `UniformInnerWeakHeat` 的 418 模块闭包与 T264 proof `a53469931caaf52a06accc38b94778d5e007a5b8` 全部不变。
- `BoxHeatContinuous` 的 386 模块闭包与 T166 proof `28789e8973368055acc0c17d5b395332e6ee7364` 全部不变。

T264 冻结报告提交 `128807c3503e575763831f7e3a450ecf11db7c3f` 已在本 proof 树中，14020 bytes，SHA256 `abc484e80eb127bde959a3ac31e19d1263a67178cf69fddec6b4f3aa1af944b1`，本次核对原版本边界并复核实际调用。

已完整读取 T266 冻结报告 `4655a9d59448298a504143f523d2bf417c617aba`，reviewed_at `2026-10-20T12:04:34+00:00`，23/23 PASS；16057 bytes，SHA256 `6dd2520423d46407db57409dd8f266ac8929f22f4977a5c3f112fa7bec457e0b`。**该报告晚于本 proof，未在 checked_sha 树中**，作为分离的固定验收证据使用；相应数学源码在本 proof 中与其所审版本完全相同。没有把根 Agent 的说明或上述报告替代实际调用核对。

## 固定本地形式验证证据

`/tmp/carleman-t267-local-evidence.json` 为 `source=local`、`status=PASS`，checked_sha 与 source_head_sha 均精确等于本报告 proof；记录 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均 exit 0，finished_at `2026-10-20T12:05:35.902830+00:00`。这是本地证据，不称为远端 CI。

已独立读取并比对：

| 项目 | 实际核验 |
|---|---|
| 源清单 | `/tmp/carleman-t267-local-source-manifest.txt`，1080 项、117219 bytes，SHA256 `baf5c075a2fe49b454f7a112bfcced1f29608703e2df0b4ae9c5459810ec8817`。集合精确覆盖固定树全部 `.lean` 及三项工具链/依赖配置，逐项内容哈希匹配固定 Git blob，没有遗漏或重复。 |
| 工具链 | Lean 4.35.0，commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定配置一致。 |
| 定向构建 | `/tmp/carleman-t267-target-build.log`，实际 3688 jobs 成功；119 bytes，SHA256 `8321a21d92a265662966c6c3f14cf9695c53a12432781aa49254060377fab2da`。 |
| 根构建 | `/tmp/carleman-t267-root-build.log`，实际 4322 jobs 成功；80 bytes，SHA256 `1f4fd0e5a837e29fad9d213a9c6613780a02e72add254dec16ce9e5fcc658b47`。固定根入口包含全部新模块。 |
| 中间目标 | 已读取同前缀 density/energy/transfer/original 的实际日志，分别为 3611/3527/3613/3676 jobs 成功；最终结论以完整定向及根构建为准。 |
| 原始审计 | `/tmp/carleman-t267-original-weak-heat-local-axioms.txt`，3559836 bytes，SHA256 `8f1b1005355c16dfbd3687853c090f6660b104c8b1cf223aa2a024640aa7a6f3`，完整递归审计 10579 声明 PASS。 |
| 公理范围 | 4257 条显式打印公理记录逐条检查，仅出现正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或空依赖；16 项均有完整类型/公理输出。无 `sorryAx` 或未证明数学公理。 |

复核摘要保存在 `/tmp/carleman-t267-review-evidence.json` 和 `/tmp/carleman-t267-review-dependency-check.json`，不是替代原始日志或源码。未使用动态 `.ci`、之后的 T268 实现、变化的工作树根入口或台账作为本版本证明依据。

## 签发

**16/16 PASS；没有发现需修复的数学缺项或附加前提。完整 Proposition A.3 / P024 已由本固定版本覆盖，可以按 PAPER 完成验收并计入 21/26。** 本报告正文与 reviewed_at 冻结，提交范围仅此文件。
