# T028 — 完整原权条件与空间加权预算的独立本机验收

- checked_sha: `fba691ef4acce0af1d303f19cae7ceaccfe7eb20`
- base_commit: `c3ab9aaef14a4f5beca82505cdfd325e507c653e`
- reviewed_at: `2026-10-18T16:15:57Z`（UTC；固定提交真实 CI 产物核验完成）
- reviewer: 独立数学验收 Agent `/root/accept_section3`，非 T028 执行者。
- target: T028 / C044；五个模块、全部 22 项显式声明。
- scope: **AUXILIARY**。
- semantic_result: **PASS**。
- axiom_check: **PASS**（同 SHA 真实 main CI 的 3482 项递归审计；全部 22 项实际类型与递归公理逐项核验）。
- result: **PASS**；C044 可升为 REVIEWED/AUXILIARY，P014 不得提升。
- extra_hypotheses: `[]`（相对于声明的辅助结果；显式质量比较条件与尚未完成的原定理组装见下文）。

独立读取固定提交的五个新模块全部证明和实际 elaborated 类型，对照原 `paper/main.tex` 的 `eq:qclass`（291–301 行）、Theorem 7.2 的参数选择及 Steps 1–3（1855–2021 行），并直接复查所用真导数、乘法 Lp、物理截断、能量及节点接口。未发现所声明辅助结论的数学或量词缺口。执行者说明只用于定位，不代替源码及原文检查。

## 范围与保留义务

本批确实构造原正则化正弦权的完整 qclass，选择先于 T/M/网格的统一 Cb，并把端点衰减、中部下界、去权多项式预算作用到真实空间 Lp 乘法范数及实际物理伴随轨迹。**本次只能把 C044 升为 REVIEWED/AUXILIARY，不能提升 P014 / 原 Theorem 7.2。** 固定提交中 C044 的 AUXILIARY 和 P014 的 PLANNED 与实际范围一致。

具体 P1/FD 重构质量比较、原数值物理加权范数与这些 Lp 重构范数的接口、势载荷及右逆的加权界、原热 Carleman 供应、潜势吸收与统一最终观测组装仍未完成。`spatial_observation_weight_bound` 是实际 Lp 场的去权估计，尚不是对具体 `B_h^*p` 的完整数值观测定理。Cb 对任意前置 Cmin 可选，提供后续吸收余量，但本批没有供应那个吸收常数或完成吸收。

## 原 qb、统一 Cb 与零势

`physicalBaseAmplitude Cb qc T M` 严格等于 `Cb*(qc+T⁻¹+M^(2/3))`，2/3 是实指数。三个界直接来自非负项和正 T：

\[
q_b\ge C_bq_c,\qquad q_bT\ge C_b,\qquad q_b^3\ge C_b^3M^2.
\]

第三个界使用非负 M 下的真实实幂恒等式 `(M^(2/3))^3=M²`，没有除以 M 或假定 M>0；M=0 被完整包含。`Cb≥2`、`qc≥1` 给 qb≥2 和 qb≥2qc。导数预算从 `qb*T≥Cb≥2π/β>0` 推出 `π/(qb*T)≤β` 和 `4π²/(qb²*T²)≤β²`；所有除数正性由原条件提供。

`physical_qclass_uniform` 的实际类型先固定 β>0、qc≥1、任意固定 Cmin，再选

\[
C_b=\max\{2,2\pi/\beta,C_{\min}\},
\]

之后才量化 `g : TimeGrid`、M、S；因此 Cb 不依赖 T=g.period、M、N、dt、S 或轨迹。`Cmin≤Cb` 真正在存在输出中保留。原 `16qb≤S≤qb*T/(4dt)` 供应 δ=qb/S>0、δ≤1/16、qb/δ=S、正截断宽度和 dt≤δT/4，没有隐藏新增尺度约束。N>0 的共享网格包含原 N≥2；对原网格，T=Ndt 为定义等式。

## 实际 qclass、端点与允许权接口

`PhysicalQClass` 存储全局 C∞ 的实际 q、qc 下界、真实 `deriv q` 的 βq² 界、真实 `deriv (deriv q)` 的 β²q³ 界，以及 0、1、2 阶端点匹配。这里是三个阶次的迹，**没有要求三阶导数**。TimeWeight 自带全时 `1≤q≤w.max`，与 `PhysicalQClass.lower`、`w.max=S` 合起来正是原 qclass 的上下界。

本批选定的 q 为原 `qb/sqrt(sin²(πt/T)+δ²)`。δ>0 保证所有实 t 上分母非零；既有 `physicalWeight_hasDerivAt` 和 `physicalWeightDerivative_hasDerivAt` 确认一、二阶公式是真导数，`physicalWeight_deriv/second_deriv` 将其识别为 Lean 的实际 deriv。此次直接检查这些实现，未把一个仅命名为 derivative 的函数当作导数。新增 `physicalWeightSecondDerivative_periodic` 用 sin/cos 加 π 同时变号，验证真实二阶表达式 T 周期；再与零阶和首阶周期性一起得到三个端点等式。

`physicalTimeWeight_qclass` 逐字段供应全光滑、qc 下界、两导数预算和全部端点，不把 qclass 作为假设。`physical_qclass_uniform` 进一步内部供应其所有预算前提。`w.max=S` 不只是另一个任意上界：既有 `physicalWeight_zero` 给 q(0)=qb/δ=S，真实公式确实达到 S。`PhysicalQClass.toRegularity` 取 `deriv w.q`，由真实可微性给闭区间 HasDerivWithinAt，正确接到已有一阶接口；输出还保留完整二阶 qclass，并未因旧接口只用一阶而丢失原二阶条件。

该构造比原 C²([0,T]) 光滑要求更强，是特定原正弦函数的已证明性质，没有向任意原 q 额外索取全局 C∞。

## 真正的空间加权范数

`SpatialProfile.multiplier w 0 t` 的实际值是 `exp(ρ(x)*q(t))`。`BoundedMultiplier.map` 在 mathlib 的 a.e. 商 Lp 空间上乘该函数，先证明乘积 MemLp；`seminorm` 就是该实际乘法结果的 L² 范数。相关比较通过 a.e. 代表与 `Lp.norm_le_mul_norm_of_ae_le_mul`，不对 Lp 等价类作不合法点值识别，也不靠不可积函数的默认积分值。

`spatial_weight_upper` 从原 a.e. `ρ≤−ρstar` 得 `‖θu‖≤exp(−ρstar q)‖u‖`。`spatial_weight_lower` 从 profile 的 `|ρ|≤ρ.bound` 得 `exp(−ρ.bound q)‖u‖≤‖θu‖`，使用反向乘法比较并准确抵消正指数；两平方版先核对非负性，平方后指数因子确实乘二。

`physical_spatial_endpoint` 在真实 transitionNodes 上调用真实正弦权的端点界，得到原

\[
\|\theta_i u\|^2\le e^{-c_{\rm end}S}\|u\|^2,
\qquad c_{\rm end}=2\rho_*/\sqrt{1+9\pi^2}>0.
\]

`physical_spatial_middle` 对 `[T/3,2T/3]` 的实际节点使用 q≤2qb，得到 `exp(−4ρ.bound qb)‖u‖²≤‖θ_i u‖²`。这两个空间包络都在证明中推出，不是新的输入假设。a.e. 负性和有界性弱于原光滑闭域 profile 条件，允许标量或向量 E；本层不需要添加域边界或光滑性限制。

## 多项式预算与指数率

`cubic_exponential_bound` 由 exp 级数第三项 `(ρstar*q)^3/6≤exp(ρstar*q)` 和 `exp(−ρstar*q)≤1` 得到
`q³exp(−2ρstar*q)≤6/ρstar³`，所有 q≥0 有效。`spatial_observation_weight_bound` 真正将此作用到上面的 Lp 乘法范数平方，常数不依赖 q、qb、S、T 或网格；具体 B* 的实现和时间求和仍待组装。

`linear_exponential_decay` 由 exp 的一次项证明

\[
S e^{-cS}\le(2/c)e^{-(c/2)S}\quad(c>0,\ S\ge0).
\]

因此余项中的 S 真实被指数吸收，半指数没有漏掉。后续可以取原 `2d0=c_end/2`（即 d0=c_end/4，满足 2d0<c_end），但本阶段只供应该预算，不宣称已完成最终 Theorem 7.2 的观测吸收。

## 实际轨迹、截断索引与质量比较方向

三项 `physical_weighted_*` 使用全 N+1 节点轨迹 p 和真实递推 `Adjoint dt L p`，及原二次型下界 `⟨L_i x,x⟩≥−M‖x‖²`。这正是 T024/T027 中从非负自伴 A、有界自伴 V 和实际 `AdjointEquation` 得到的输入；并非一个假定能量界的轨迹接口。对原 L=A+V，`stiffness_potential_lower` 与 `adjoint_equation_iff` 可直接供应；本批辅助层保留更一般的 L 和实际递推，没有把 p 本身周期化，也没有要求完整轨迹在某个子空间内。

实际 `cutoffState_i=χ_i p^i`，`cutoffRemainder_i=((χ_(i+1)−χ_i)/dt)p^(i+1)`；两者取 N 个周期载荷/状态节点。**余项的 p^(i+1) 使用的是 θ_i**，与原 `eq:endpointbudget` 一致。最后一个步的 p^N 保留；只有截断后状态首末为零才允许周期索引。使用的 χ 是 T027 已验收的显式 Lipschitz 截断，值域、边界零、中间一、差商界和过渡位置均已证明；这里没有新增 χ 条件或假定差商支持集测度。

`physical_weighted_remainder_energy` 对每节点分情况：在过渡集合上用原端点指数和 **上质量界** `‖Rx‖²≤Cmass‖x‖²`；集合外调用真实 `cutoff_remainder_zero`，再由线性 R 和 seminorm 的零值消去。求和后调用已证明的真实伴随截断能量，得到

\[
dt\sum_i\|\theta_iRr_i\|^2
\le C_{\rm mass}e^{-c_{\rm end}S}
\frac{5}{\delta T}e^{4MT}\|p^N\|^2.
\]

其中 5 来自安全的过渡测度 5δT（原稿较精细是 3δT），只放大固定系数。代 δ=qb/S，并应用实际指数预算，`physical_weighted_remainder_decay` 精确给

\[
dt\sum_i\|\theta_iRr_i\|^2
\le\frac{10C_{\rm mass}}{c_{\rm end}q_bT}
e^{4MT}e^{-c_{\rm end}S/2}\|p^N\|^2.
\]

qc≥1、qb≥2、S≥16qb、T>0、ρstar>0 给全部相关正分母；没有遗漏 S 或 dt 因子，M=0 仍成立。

`physical_weighted_initial_recovery` 使用相反的 **下质量界** `‖x‖²≤Cmass‖Rx‖²`。中部 χ=1，真实空间下包络将 Rx 范数转成加权范数，再用 q³≥1。中部时间测度至少 T/6 及原伴随能量给

\[
e^{-4\rho.bound\,q_b}\frac T6e^{-4MT}\|p^0\|^2
\le C_{\rm mass}\,dt\sum_i q_i^3\|\theta_iRz_i\|^2.
\]

扩展中部求和到全周期节点使用各项非负性；未错用质量界方向。Cmass≥0 显式保留，证明不除以 Cmass，包含退化零空间情形；后续正质量等价常数的具体选择仍是实例义务。

该恢复界较原中间展示式保守：它以 q³≥1 丢弃了更强的 qb³ 因子，但仍给正且独立于 h/dt 的 C(T,M)，保留最终所需指数及全状态范围。因此这是合格的所声明辅助界，不能据此宣称已经识别原完整离散能量或证明所有 Step 3 组装。

## 全部 22 项声明

每项已核对固定源码、真实类型、公理依赖和原文用途。递归公理集合均恰为 `[propext, Classical.choice, Quot.sound]`。

| # | 声明 | 结果与作用 |
|---|---|---|
| 1 | `Carleman.Physical.physicalBaseAmplitude` | PASS：原 qb 公式，实指数 2/3。 |
| 2 | `Carleman.Physical.physicalBaseAmplitude_bounds` | PASS：原三个统一预算，包含 M=0。 |
| 3 | `Carleman.Physical.physicalBaseAmplitude_ge_two` | PASS：qb≥2 与 qb≥2qc。 |
| 4 | `Carleman.Physical.physicalBaseAmplitude_derivative_budgets` | PASS：同一 Cb 控制 β 与 β² 两导数比例。 |
| 5 | `Carleman.Physical.physicalWeightSecondDerivative_periodic` | PASS：原真实二阶导数表达式周期性。 |
| 6 | `Carleman.Physical.PhysicalQClass` | PASS：真光滑/导数/三阶次端点字段，与 TimeWeight 上下界配合。 |
| 7 | `Carleman.Physical.PhysicalQClass.toRegularity` | PASS：真 deriv 接到已有闭区间一阶接口。 |
| 8 | `Carleman.Physical.physicalWeight_lower_qc` | PASS：全部实时间 qc 下界。 |
| 9 | `Carleman.Physical.physicalTimeWeight_qclass` | PASS：从原正弦函数实际构造完整 qclass。 |
| 10 | `Carleman.Physical.physical_qclass_uniform` | PASS：前置统一 Cb、原 q、准确 qmax=S，所有字段内部供应。 |
| 11 | `Carleman.Physical.spatial_weight_upper` | PASS：真 Lp 乘法范数的上指数包络。 |
| 12 | `Carleman.Physical.spatial_weight_lower` | PASS：由 |ρ| 界得到下包络。 |
| 13 | `Carleman.Physical.spatial_weight_upper_sq` | PASS：平方范数上界，指数因子二。 |
| 14 | `Carleman.Physical.spatial_weight_lower_sq` | PASS：平方范数下界，方向正确。 |
| 15 | `Carleman.Physical.physical_spatial_endpoint` | PASS：真实过渡节点，原 c_end S。 |
| 16 | `Carleman.Physical.physical_spatial_middle` | PASS：真实中部节点，exp(−4ρ.bound qb) 下界。 |
| 17 | `Carleman.Physical.cubic_exponential_bound` | PASS：q³ 对指数的统一 6/ρstar³ 预算。 |
| 18 | `Carleman.Physical.linear_exponential_decay` | PASS：S 吸收到半指数，系数 2/c。 |
| 19 | `Carleman.Physical.spatial_observation_weight_bound` | PASS：实际 Lp 场去权；具体 B* 组装尚未声称。 |
| 20 | `Carleman.Physical.physical_weighted_remainder_energy` | PASS：真实 r、θ_i、上质量界、原 e^(4MT) 端点预算。 |
| 21 | `Carleman.Physical.physical_weighted_remainder_decay` | PASS：准确 10 Cmass/(c_end qb T) 与半指数率。 |
| 22 | `Carleman.Physical.physical_weighted_initial_recovery` | PASS：下质量界、真实中部 χ=1、全周期 q³ 加权能量恢复。 |

模块对应：1–4 为 [PhysicalBaseAmplitude](../../Carleman/Control/PhysicalBaseAmplitude.lean)，5–10 为 [PhysicalQClass](../../Carleman/Control/PhysicalQClass.lean)，11–16 为 [PhysicalSpatialWeights](../../Carleman/Control/PhysicalSpatialWeights.lean)，17–19 为 [PhysicalExponentialBudgets](../../Carleman/Control/PhysicalExponentialBudgets.lean)，20–22 为 [PhysicalWeightedEnergy](../../Carleman/Control/PhysicalWeightedEnergy.lean)。

## 固定版本、构建与依赖证据

已读取根 AGENTS、PROJECT_OPERATIONS、state 协议和固定 MATH_SPEC T028。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。基线至本次提交的数学变化只有这五个新模块及 root 导入，既有数学依赖和原稿未改；root 显式导入全部五模块。基线有 [T027 独立验收](T027-local-acceptance.md)，本次仍直接复查所用依赖的关键定义与证明。

`/tmp/carleman-full-weight-full.log` 记录 `Build completed successfully (3495 jobs).` 和 `Axiom audit passed for all 3482 Carleman declarations.`。锁定本机公理副本 `/tmp/carleman-full-weight-local-axioms.txt` 为 988663 字节，SHA256 `ef0d1e56ad51fb5508875940d00b094f6ec349c24d6abaca6cf95bebe86bd123`。22/22 项实际类型与公理输出均齐全；名称、顺序与固定 C044/T028 和 `/tmp/carleman-full-weight-declarations.json` 一致。实际类型确认没有 section 变量意外进入均匀 Cb 定理或缺失轨迹、质量界前提。

固定审计入口逐项 `#check @...`、`#print axioms ...`，同时遍历包含私有声明的全部 Carleman 常量，递归 `collectAxioms` 并拒绝三项正常基础公理之外的任何依赖。自动生成的结构字段也在全局审计中；不是仅对 22 个源码名字扫描。未见 sorryAx、无依据数学公理或隐藏目标估计。

正式远端证据已核验：读取 [main CI 39143907384 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39143907384/attempts/1) 的下载产物 `/tmp/carleman-full-weight-main-ci/result.json`，确认 `status=PASS`，`checked_sha=source_head_sha=fba691ef4acce0af1d303f19cae7ceaccfe7eb20`，target 为 `Carleman`，`finished_at=2026-10-18T16:13:25.420230+00:00`。工具链为 Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；result 原始文件 SHA256 为 `d5e05c8486f05510212465e8d033d0d8bf017696e163871ac8f2f12cb549a0ba`。

同次正式 `/tmp/carleman-full-weight-main-axioms/axioms.txt` 为 988663 字节，SHA256 `ef0d1e56ad51fb5508875940d00b094f6ec349c24d6abaca6cf95bebe86bd123`，直接逐字节比较与锁定本机副本一致。再次核对正式产物的全部 22 项实际类型和递归公理，均仅上述三项正常基础公理；末行确认 3482 项审计通过。正式结论绑定该同 SHA 远端产物，不依赖后续工作树或把本机日志冒充远端记录。

## 当前结论

语义、全部 22 项声明、递归公理及同 SHA 真实 main CI 均 PASS，无需修复所声明的辅助数学结论。可将 C044 升为 REVIEWED/AUXILIARY，`extra_hypotheses=[]`；P014 不得因此计入完成。上述显式质量界实例和原定理组装义务仍须后续供应并独立验收。

本次只新增本报告，未修改证明、root、论文、台账或覆盖表，未 commit/push。
