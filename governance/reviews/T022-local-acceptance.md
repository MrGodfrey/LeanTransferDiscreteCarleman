# T022 — 原 Theorem 2.1 独立本机验收

- checked_sha: `5fbbfa1714af4a34facdf933a0f37736a4b7e6cd`
- reviewed_at: `2026-10-18T15:03:30Z`（UTC；固定提交 CI 产物核验完成）
- reviewer: 独立本机数学验收 Agent `/root/accept_section3`，非 T022 执行者。
- targets: C010 / P001；原 `thm:main`，五个模块、全部 18 项显式声明。
- semantic_result: **PASS**。
- axiom_check: **PASS**（固定提交真实 main CI 的 3170 项递归审计，全部 18 项实际类型与公理输出逐项核验）。
- result: **PASS**；C010 / P001 可升为 REVIEWED/PAPER，`extra_hypotheses=[]`。

未发现数学保真缺口。最终入口 `OriginalForm.transfer_uniform` 确实从原解析与数值假设导出载荷、稳定右逆残差两版原结论；没有剩余 B1–B5、CombinedEstimate、目标图估计或目标误差估计作为最终输入。本报告只作独立验收记录，不修改台账。

## 固定版本与证据

本次沿用已经读取且仍适用的根 AGENTS、PROJECT_OPERATIONS 和 state 协议，并直接读取固定提交的五个新模块全部源码、实际 elaborated 类型和递归公理输出。对照 `paper/main.tex` 的允许权、A1–A4、N1–N5、`thm:main`（525 行起）、Section 5 四步证明（1310 行起）及真实 N/R 定义。执行者分析记录只作定位，未作为 PASS 的依据。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。基线 `9d8230090dad2c5b5a2efa74f5d085728866d139` 的 Theorem 4.2 已有 [T021 独立验收](T021-local-acceptance.md)。检查基线至本次提交的 diff：既有数学依赖未修改；数学变化为五个新模块及 root 导入。固定 root 的项目导入闭包 264 个模块，五个新模块全部可达。

本机 `/tmp/carleman-original-full.log` 记录 `Build completed successfully (3454 jobs).` 和 `Axiom audit passed for all 3170 Carleman declarations.`。检查时 `.ci/axioms.txt` 为 897066 字节，SHA256 `230919fb64b2d861fac74c586ba40f073332eac5581556a0e7d5004dbb27e24e`。本次 18/18 声明逐项有 `#check @...` 实际类型及 `#print axioms` 输出，名称和顺序与固定 `state/progress.json` 的 C010 清单及 `/tmp/carleman-original-declarations.json` 完全一致；每项递归公理集合恰为 `[propext, Classical.choice, Quot.sound]`。

固定提交真实 [main CI 39137974197 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39137974197/attempts/1) 已成功。直接读取下载产物 `/tmp/carleman-original-main-ci/result.json`：`status=PASS`，`checked_sha` 和 `source_head_sha` 均为本报告固定 SHA，`finished_at=2026-10-18T14:56:05.110784+00:00`，目标 `Carleman`，Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。同次下载的 `/tmp/carleman-original-main-axioms/axioms.txt` 为 897066 字节，SHA256 与上述本机审查产物完全一致；末行是 `Axiom audit passed for all 3170 Carleman declarations.`。对该正式产物再次核对 18/18 的实际 elaborated 类型、逐项递归公理和固定审计入口，均通过。

直接检查了固定提交 `tools/CheckAxioms.lean`：遍历所有项目声明，对 `privateToUserName` 后属于 `Carleman` 的每项调用 `collectAxioms`，除上述三项外一律报错。因而不是只检查新文件是否出现 `sorry`；没有未清偿数学公理或 `sorryAx`。正式证据与本机编译分开核实，且以同一固定 SHA 绑定。

## 原假设输入逐项核查

| 原假设 | 最终实际输入与判断 |
|---|---|
| A1 | `OriginalForm` 是原闭、H 稠密 V 的真实 Sobolev Hilbert 实现；`hD` 与 `hell` 是 D(A)⊂H^(2m) 和正向椭圆界。原双线性形式、原全域/算子的识别沿用已验收 `ofBilinear_scalarForm`、`associated_iff`、`identify_operator` 的域相等/作用相等，可据此转移到 `a.model`。没有更小核心、零迹或反向椭圆界。 |
| A2/A3 | 原 `AllowedFamily` 对 ±ρ、全部 `|τ|≤τStar` 提供域/V 保持、真实交换子和形式上下界；无解、图或误差结论字段。 |
| A4 | `TransferUniform` 中 `hCE` 对所有方向、所有 `PeriodicWeakTrajectory`，以真实连续能量控制真实 `εU_t+AU` 与区域观测。左端不出现 z、R、A_h、Γ 或离散残差；原 A4 正好供应它。Cce 在 T、q、数值空间和状态之前固定。 |
| N1 质量接口 | `Reconstruction.mass_adjoint` 是原 J 的定义；Q=RJ、G=JR 保留。无 Q²=Q、G=Id 或正交性要求。原有限维 X 可构造这一 J；最终定理对更大的 X 类仍成立。 |
| N1 刚度与缺陷 | `NumericalData.stiffness` 是原刚度等式；`defect` 是每节点、每允许权的原 ηA·Nσ·Nσ⁻¹ 界。`b` 时间独立且双线性；原对称性在此不再额外要求。 |
| N1 范数 | `reconstruction_upper/lower` 只是 θ 节点重构范数等价平方后的两个方向。共同 Cnum 可在原统一常数的平方及倒数平方中取最大。原所有允许权、所有时间的界比这一要求更强。 |
| N2 | 普通函数 Γ、lift 和 JL=Γ 位于 `LoadInterface`，未要求线性；`lift_bound` 为原 θ 提升界平方。残差结论另对每个普通 I、ΓI=Id 及原稳定界平方成立，所以原 N2 的稳定右逆直接实例化该结论。 |
| N3 | `approximation` 的 `WeightedApproximation.energy/l2` 是原闭区间每时刻、所有 v∈D(A) 的真实 v−Qv 估计，系数仍为 aE、a0。没有输入时空误差或数值解误差。 |
| N4 | `test` 的 `WeightedTest` 只要求原测试族的周期端点、标量二次型可微性、自伴非负、原 qσ 时间导数界与 Csuper·h·qmax 的真实 superapproximation。原可微正定族及测试范数等价蕴含这些字段；没有新强制性、稳定性或 Céa 界字段。`superapprox` 对 V 保持证明参数的全称量化不改变 σ²Rz，相关构造具有相同实际值。 |
| N5 | `observation_bound` 是 θ 节点上实际区域观测的原界平方。`Bstar` 可取原 B_h 的实际 Hilbert 伴随；定理不要求额外控制空间有限维性。 |

`NumericalData` 是所用原假设的打包，包含 N3/N4 的原始局部数值估计，但没有隐含 Theorem 4.2 或最终离散 Carleman 估计。它选择每个允许权的 N4 测试族；原逐权存在可由正常经典选择提供统一数据，未增加解析前提。Cnum 对重构双向界、提升、观测和稳定右逆共同取大，保持原统一性。

数值 state/load/control 为真范数的 Seminorm 表示，definiteness 对应原范数；其 θ 族可在区间外按原范数延拓。q 幂直接进入 `powerSq`，原权标量齐次性和范数的状态齐次性识别原 `‖q^(b/2)z‖²`。没有要求数值权族扩大到超出原允许区间的指数。

省略原 X 有限维、A_h 自伴非负、测试正定/测试范数等价等未使用条件只扩大定理适用范围。证明对满足原方程的任意 z 直接工作，无需再构造另一全离散解。原 Ω、ρ 和 q 的表示桥仍在已验收 Section 3 中：原 bounded Lipschitz 域、内禀闭包光滑、q 在 [0,T] 的实际值与周期迹；没有新边界或邻域限制。原更强 q''/端点条件、ρ 负性、观测区开且紧包含等未被替换为新限制。

## B1–B5 的实际清偿

| 桥接 | 固定提交实际供应 |
|---|---|
| B1 连续解及真实正规性 | `sobolevGeometry_transferBridges` 对任意方向/载荷/状态，调用 `existsUnique_variable_periodic` 解真实非负冻结乘子问题，载荷为 `lift f+μRz`；从 evolution 方程和 `extensionLp_ae` 得实际 a.e. 方程。PeriodicGraph 只要求 a.e. D(A)、真实 H 弱时间导数及闭区间周期 H 迹。 |
| B2 离散对应 | `ErrorBridge.derivative_bound/lower_bound` 调用 `Orientation.state_solves_shifted`，由原状态方程与 JL=Γ 直接证明给定 z 满足含 G 的辅助离散方程；随后 CombinedEstimate 对这个任意解适用。构造连续解的 `_hz` 未用不构成缺口：给定 z 的方程在误差估计使用时实际提供，未无条件假定 z 是辅助解。 |
| B3 范数、单元及残差比较 | `sobolevGeometry_comparisonBridge` 用已证 cell 比较、原数值节点界和 hCE；所有 finite_* 字段由 A1/真实弱轨迹及有限节点延拓证明。`ComparisonBridge.comparison` 使用真实 `residual_ae`，消去 μRbar z 后得到 lift f−bar μ·e。 |
| B4 两个完整误差率 | 最终入口内部调用 `a.combined_uniform`。`transfer_uniform_of_combined` 用原 NumericalData 对每个需要的 τ 供应 CombinedEstimate；逆权通过 `signed_neg` 和 τ↦−τ 从原同一允许权族取得。`sobolevGeometry_errorBridge_of_combined` 调用实际解、实际转移载荷上的完整 Theorem 4.2，平方后识别全部 N/L² 误差项。有限性、微分阶数界与冻结移位界由已有证明补齐。 |
| B5 吸收与残差 | `conditional_transfer_defect/load` 已证明真实误差汇总与吸收；本次把整份真实 TransferBridges 填满，再取 cStar=1/(2 transferConstant)。`residual_estimate` 使用普通稳定右逆 I 作用于每个节点真实 `D_s z+A_hz`，得到所有状态的残差版。 |

中间 `transfer_uniform_of_combined` 显式有 combined 前提，`errorBridge_of_combined` 显式有各权 combined 估计；这些是复用构造器，不是最终 `OriginalForm.transfer_uniform` 的新增前提。最后一行调用已证明的 `a.combined_uniform` 清偿它们，没有留下条件性缺口。

## 规范范数、弱误差与幂次

前四项新声明证明无损等式：`timeSq(q,b,θ,u)=‖q^(b/2)θu‖²`；相同节点等式；真实时空 N_m² 等于各阶 q^(2(m−k)+b)θ² 密度积分之和；该和恰为既有 `graphSq`。时间等式均有实际 `MemLp`，每阶字段 `MemLp` 来自完整弱 jet，未使用不可积时的默认积分值。

`Section4.reconstructedError` 与 `TransferGeometry.error` 是同一个 V 值代表 `inclusion(U.domainValue)−R(bar z)`，其 H 值由 `reconstructedError_value_ae` 与实际 `U−Rbar z` a.e. 相同。L² 误差通过该 a.e. 等式转移；能量误差是原弱导数字段的 N_m，不是 H 范数或任意标量替代。没有要求 U 每个时刻属于 D(A)。

`ErrorScales.energy=aE+ηA+sqrt(dt)`，`l2=a0+aE²+ηA+dt`。新平方步骤先验证 Kc、误差率、载荷范数非负，再将和项重排为上述定义；共同系数由 Kc² 放大到 K。原 dStar=max(0,max_j(c_j−2(m−j)))、bStar=max(c0,o,4m) 逐项一致；能量指数是 `energyPower j/2`，低阶三权是 c0/2、o/2、2m，全部由原 coverage 得 `|τ|≤τStar`，没有遗漏负差值时取 θ 的分支。

两个缺陷严格保留为

`Λf=εE² qmax^dStar+ε0² qmax^bStar`，

`Λz=εE² max(1,qmax^(4m+dStar−c0))+ε0² max(1,qmax^(4m+bStar−c0))`。

`LoadBound.transferLoad_powerSq_le` 从实际 μ²=L^(4m)q^(4m)、重构/提升界和真实节点权指数转换给这两个幂次，保留负指数时的 max(1,·)。不存在替代误差阶、额外 h/dt 耦合或漏掉 ηA/aE² 的情况。

`p.nodeEnergy` 恰为原离散零阶 X 范数与所有 `D_j Rz` 的加权平方和；`p.loadSq` 为原 θ 载荷平方范数，`p.observationSq` 为原 q^(o/2)B* z 的控制范数平方；残差版使用原 X 的 θ 范数。P 的真实有界系数表达式按 j+1 阶过滤，索引覆盖原 j=1,…,m；两方向仍是原 D_plus/D_minus 与 ε=±1。

## 参数选择与统一性

先固定 Ω、m、原形式/正则界、ρ、P、指数与 A/N 共同界，内部从 CombinedUniform 选定 `L=Lmin`；再取得 `δx≤δnum`、ηstar、Kc，取

`K=9+9 Cnum+Kc²+(2L)^(4m)+differentialFamilyBound(P)+Cce`。

令 `δtime=min(δcombined,cellThreshold β comparisonExponent ρ.bound)`；空间阈值沿用已经保证 `δx≤δnum` 的正阈值。接着选

`cStar=1/(2 transferConstant α K)`，`Cfinal=4 transferConstant α K·K`。

这些常数全部先于 X/F/Y 类型和实例、重构/算子/载荷/控制映射、数值范数族、T/网格/q/qmax、h、误差尺度、方向、f、z。Cce 是前置共同常数，虽然每个网格的 A4 实例在后面供给，常数不因具体 U 或网格另选。L 是内部固定量，不是新的最终输入。原 δt≤1 没有作为额外字段重复要求；这里证明的范围至少包含原满足该条件的网格，且内部共同阈值继承 Section 3 的限制，不构成弱化。

`comparisonExponent` 较大只供纯解析单元密度比较，不要求 NumericalData 在这些更大指数上成立。原 `aE≤1`、`ηA≤ηstar`、h·qmax 和 dt·qmax² 约束、Λf≤1、Λz≤cStar 均在最终声明中保留。所有 z 仍是完整周期 `Fin N→X`，无频谱、低频或核限制；N>0 的库接口包含原 N≥2。

## 全部 18 项声明

下表各项均已直接阅读固定源码、核对实际类型，语义 PASS；每项递归公理都是 propext/Classical.choice/Quot.sound。

| # | 声明 | 核对结果 |
|---|---|---|
| 1 | `Carleman.SpatialProfile.timeSq_eq_bochnerL2Norm_sq` | PASS：实际 MemLp 下的时间平方密度与 q^(b/2)θ 范数平方完全相等。 |
| 2 | `Carleman.SpatialProfile.nodeMap_l2Norm_sq_powerSq` | PASS：真实节点加权 ℓ² 范数平方与 powerSq 完全相等。 |
| 3 | `Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum` | PASS：每阶真实弱导数字段先取 L² 后平方求和；全部可积性供应。 |
| 4 | `Carleman.sobolevGeometry_graphSq_eq` | PASS：原 V jet 上既有 graphSq 与真实 N_m² 无损识别。 |
| 5 | `Carleman.sobolevGeometry_errorBridge_of_combined` | PASS：各所需原允许权调用实际 CombinedEstimate，补足能量/L²；载荷、误差和方向一致。 |
| 6 | `Carleman.sobolevGeometry_transferBridges` | PASS：构造实际冻结连续解、B3/B4 及所有有限性；不输入最终离散估计。 |
| 7 | `Carleman.Section5.NumericalData` | PASS：八字段恰为所用 N1–N5 数据；具体映射见上表。 |
| 8 | `Carleman.Section5.NumericalData.stiffness` | PASS：原 A_h/a/R/b 等式，没有误差估计字段。 |
| 9 | `Carleman.Section5.NumericalData.approximation` | PASS：原全允许权的逐时 N3，完整原 D(A)。 |
| 10 | `Carleman.Section5.NumericalData.test` | PASS：原 N4 可微周期测试族及 h·qmax superapproximation。 |
| 11 | `Carleman.Section5.NumericalData.defect` | PASS：原 ηA 的正/逆权 N_m 乘积界，节点特例。 |
| 12 | `Carleman.Section5.NumericalData.reconstruction_upper` | PASS：原 N1 θ 重构上界平方。 |
| 13 | `Carleman.Section5.NumericalData.reconstruction_lower` | PASS：原 N1 θ 重构下界的等价平方方向。 |
| 14 | `Carleman.Section5.NumericalData.lift_bound` | PASS：原 N2 θ 提升界平方。 |
| 15 | `Carleman.Section5.NumericalData.observation_bound` | PASS：原 N5 真实区域观测界平方。 |
| 16 | `Carleman.Section5.TransferUniform` | PASS：完整原阈值、缺陷条件、全状态两方向及载荷/普通稳定右逆残差两版。 |
| 17 | `Carleman.Section5.transfer_uniform_of_combined` | PASS：阈值先于全部变化参数，内部构造完整桥接并应用真实吸收；中间 combined 前提明确。 |
| 18 | `Carleman.OriginalForm.transfer_uniform` | PASS：内部调用已证明的 combined_uniform 清偿第17项的唯一中间前提，原 A1–A4/N1–N5 保真。 |

模块定位：[CombinedNorms](../../Carleman/Transfer/CombinedNorms.lean)、[CombinedErrors](../../Carleman/Transfer/CombinedErrors.lean)、[CompleteBridges](../../Carleman/Transfer/CompleteBridges.lean)、[OriginalData](../../Carleman/Transfer/OriginalData.lean)、[OriginalUniform](../../Carleman/Transfer/OriginalUniform.lean)。

## 最终结论与验收边界

数学语义、原命题保真、全部 18 项声明、递归公理与同一 `checked_sha` 的真实 main CI 均为 PASS，没有待修复项。可将 C010/P001 标为 REVIEWED/PAPER、`extra_hypotheses=[]`，同时绑定本次声明版本、成功构建和语义记录。

本报告只覆盖原 Theorem 2.1，不自动宣告 Corollaries 2.2/2.3、具体应用、观测或控制后续结果完成。历史条件性 C004 保留其原用途，不能用本次完成反向伪称它当时已经无条件。本次只新增本报告，不修改数学代码、root 导入或台账，不 commit/push。
