# T027 — 原物理观测证明基础的独立本机验收

- checked_sha: `c3ab9aaef14a4f5beca82505cdfd325e507c653e`
- base_commit: `549cde718bcf26f00b24f4a1493ee92b839f30b4`
- reviewed_at: `2026-10-18T16:04:16+00:00`
- reviewer: 独立数学验收 Agent `/root/accept_spatial_lemma`
- target: C043，八模块 / 70 项声明
- scope: **AUXILIARY**
- result: **PASS**；源码语义核对及同 SHA 远端构建门槛均通过
- axiom_check: **PASS**；同 SHA 远端 3436 声明递归审计及本批 70 项逐项核对通过
- extra_hypotheses: `[]`（没有隐藏的目标估计前提；辅助引理的显式参数条件和后续组装义务见下文）

本报告独立读取固定提交的全部八模块、70 项实际声明和证明体，并回查原稿 Section 7 数据、已验收 Lemma 7.1 及 `prop:physicalO` 的 Steps 1–3（`paper/main.tex:1713–2021`）。源码用 `git show <checked_sha>:<path>` 读取；没有把执行者说明、后续未提交代码或旧版本 CI 当作本次结论。根 AGENTS、PROJECT_OPERATIONS 和状态证据协议与此前已读版本相同；本次另读了 MATH_SPEC 的 T027 范围和固定提交的 C043/P014 记录。

## 结论与范围

本批实际建立了原正则化正弦权、真实两阶导数、具体截断及物理/周期索引转换、离散窗口计数、未加空间权的真实伴随能量预算、参数 δ=qb/S 的网格后果和原端点指数。未发现所声明辅助结论的数学、全局/边界条件或变量量词缺陷。同 SHA 正式构建门槛已通过，C043 可升为 `REVIEWED/AUXILIARY`。

**本次不能提升 P014 / 原 Theorem 7.2。** 本批没有证明实际空间加权 seminorm 比较、具体势载荷及其加权界、完整 Carleman 供应、统一 Cb 的全部选择、潜势吸收、观察项去权或最终指数余项吸收。原 FEM/FD 实例与连续热 Carleman 的供应也不因这些辅助结果而完成。固定提交中 P014 仍为 PLANNED，符合实际证明范围。

原文 smooth χ 被明确的 Lipschitz 截断替代，过渡测度的 3δT 被安全常数 5δT 替代。这两个改变都已在 MATH_SPEC 说明，原稿保留不改；下文核查它们只改变证明选择和绝对常数，不削弱最终原结论或改变指数率。

## 实际权函数、真导数与允许性边界

`physicalWeightDenom δ T t = sqrt(sin²(πt/T)+δ²)`，`physicalWeight = qb/denom`，与原 `eq:physical-weight` 相同。δ>0 使分母在**所有实 t** 上严格正；没有只在节点假定正性。`physicalWeightDenom_bounds` 证明 δ≤denom≤sqrt(1+δ²)，从而在 qb≥0、δ>0 下得到全时上下界；`physicalWeight_zero` 实际达到 qb/δ，`physicalWeight_periodic` 用 sin(x+π)=−sin x 证明 T 周期。T=0 不用于任何物理比界；周期性要求 T≠0，比界要求 T>0。T、qb、δ 的非零条件在除法和清分母时由显式假设供应。

`physicalWeight_smooth` 通过严格正的平方根和除法给出全局 C∞。一阶表达式由 `physicalWeight_hasDerivAt` 证明为实际导数；二阶表达式由 `physicalWeightDerivative_hasDerivAt` 对该一阶函数再次求导得到。`physicalWeight_deriv` 和 `physicalWeight_second_deriv` 进一步将两者与 Lean 的实际 `deriv q`、`deriv (deriv q)` 识别；不是独立命名两个无关函数。

令 s=sin(πt/T)、c=cos(πt/T)、D=denom，则公式实际为

\[
q'=-\frac{q_b(\pi/T)sc}{D^3},\qquad
q''=\frac{q_b(\pi/T)^2\{3s^2c^2-(c^2-s^2)D^2\}}{D^5}.
\]

一阶界用 |s|≤D、|c|≤1；二阶界用 s²c²≤D²、|c²−s²|≤1，使分子绝对值≤4D²。结果严格为 `|q'|≤π/(qb*T)*q²` 和 `|q''|≤4π²/(qb²*T²)*q³`，系数不含 δ、qmax、N、状态或空间维数。首阶导数在 0 为零且 T 周期；全局光滑和周期性的证明保留原端点结构。

`physicalTimeWeight` 只将 q≥1 和上界 qb/δ 接入已有 `TimeWeight`；其条件是 `sqrt(1+δ²)≤qb`。`physicalTimeWeightRegularity` 实际供应已有**一阶**正则接口，显式要求 `π/(qb*T)≤β`。该预算单独不能推出二阶 β² 界；完整原 `qclass` 的后续组装还须选 Cb 保证 `4π²/(qb²*T²)≤β²`（例如 `2π/(qb*T)≤β`）、`qb/sqrt(1+δ²)≥qc` 及全部端点匹配。二阶端点匹配可由这里的真实光滑周期函数继续推导，但本批没有一个宣称完整 qclass 已组装的结论。`qb≥2` 也仍是参数选择辅助引理的显式条件，须由最终原式 `qb=Cb(qc+T⁻¹+M^(2/3))` 的统一 Cb 选择供应。上述工作尚待，不能把它们误登记为已清偿的 Theorem 7.2 入口。

## 截断、物理轨迹和周期末格

`clipUnit x=max 0 (min 1 x)` 全局取值于 [0,1] 且 1-Lipschitz；`endpointDistance T t=min(t,T−t)` 在 `[0,T]` 恰为距端点的距离，且作为定义在全实线上 1-Lipschitz。区间外该表达式可以负值，代码没有把它当作全局非负几何距离；涉及正弦端点定位时明确要求 0≤t≤T。

`physicalCutoff T a t=clipUnit((endpointDistance T t−a)/a)`，a>0 时在距端点≤a 处为零、距端点≥2a 处为一，并具有 1/a 的全局 Lipschitz 界。此函数不声称光滑，也不声称与某个预先指定的 smooth χ 逐节点相同；原证明允许自由选择 χ，而实际离散步骤只需要这里证明的节点取值、首末消失和差商界。因此采用该具体选择保留原证明所需性质，无额外状态正规性或可微轨迹假设。

`cutoffNodes` 取完整 N+1 个物理时刻。`cutoffState` 只限制到 i=0,…,N−1，而 `cutoffRemainder` 仍取
`((χ^(i+1)−χ^i)/dt) • p^(i+1)`，保留真实物理末端 p^N。`periodic_next_of_endpoints` 对最后一格单独处理 `i+1=N` 的模回绕；使用的是**截断后的** χp 两端都为零，不是 p^0=p^N。没有把伴随轨迹本身周期化。

`cutoff_difference` 使用既有 `D_-z_i=dt⁻¹(z_i−z_next(i))`，给出准确的 `χ_i D_-p_i−r_i`；`cutoff_residual` 从真实 `AdjointEquation` 中的 Hilbert 伴随，经 `(A+V_i).IsSymmetric` 识别实际 L*=L，得到
`D_-z_i+A z_i=−V_i z_i−r_i`。这里 V_i 对应原物理 V^(i+1)。`concrete_cutoff_residual` 实际调用已证明的具体 χ 首末消失，未把残差等式作为输入或改掉余项符号。

## 实际节点计数、定位和参数后果

左右节点集都是真实 `Fin N` 的过滤子集，时刻为 i*dt，包含边界时用非严格不等号。左窗口用自然数 floor 与 Fin.val 单射，证明 `dt*card≤b+dt`；右窗口用 `Fin.rev` 注入左窗口，因右侧没有重复纳入物理终点 T，保留了需要的一个 dt 余量。

`middleNodes` 为 `[T/3,2T/3]` 内真实周期代表节点。用全部 N 节点被中部、左右窗口覆盖，结合 `dt≤T/12` 得到 `dt*card(middle)≥T/6`；没有把连续区间长度直接冒作离散测度。`cutoffNodes_one_middle` 在 a≤T/16 下把这里的实际 χ_i 证明为 1。

`transitionNodes` 明确定义为实际 χ 差分非零的节点。若两个端点都在中部 plateau，则差分为零；据此得到起点距某一端点≤2a+dt。将其包入两个真实窗口后有
`dt*card(transition)≤4a+4dt≤5a`（dt≤a/4）。这比原稿的精细 3a 界宽，但仅把可选择的绝对常数放大，不改变 a=δT 的阶数、状态范围或 S 的指数。证明并未误称给出原 3a 精确常数。

`physical_delta_conditions` 从 `qb≥2`、`16qb≤S` 和 `S≤qb*T/(4dt)` 实际推导 δ=qb/S>0、δ≤1/16、qb/δ=S、sqrt(1+δ²)≤qb、a=δT>0、a≤T/16、dt≤a/4。S>0 和 qb>0 均由前提推出，未利用实数除零的默认值。dt≤a/4 是原物理条件的后果而非后来新增网格限制。

`sine_endpoint_bound` 在真实 [0,T] 上用反射与 |sin x|≤|x| 得到 `|sin(πt/T)|≤(π/T)min(t,T−t)`。对实际过渡节点，由 2a+dt≤3a 得 |sin|≤3πδ，再得到原
`q_i≥S/sqrt(1+9π²)`。`physical_weight_endpoint_decay` 对任意空间标量 r≤−rstar、rstar>0，准确推出
`exp(q_i*r)²≤exp(−(2*rstar/sqrt(1+9π²))*S)`；指数仍是原 c_end，没有因 5a 的测度常数被削弱。此结果是点态指数界，尚不是离散空间加权范数比较。中部用真实 sin 单调性和反射得到 sin≥1/2，从而 q≤2qb；与全时下界一起提供原 q≍qb 的需要。

## 真实伴随的未加权预算与依赖

通用 `cutoff_remainder_energy_bound` 先用真实差商≤1/a、真实轨迹的点态上界 K，以及过渡集外余项=0，得到 `dt Σ‖r_i‖²≤5K²/a`。它明确保留 K 的来源；后续 `physical_cutoff_remainder_energy` 实际调用已验收 Lemma 7.1 的 `adjoint_energy`，供给 `K=exp(2MT)‖p^N‖`，故得到 `(5/a)exp(4MT)‖p^N‖²`，没有把该最终预算假设进来。

`physical_adjoint_initial_lower` 用同一个真实反向稳定性，取 j=0、ell=n，平方并合法抵消正指数，得到 `exp(−4MT)‖p^0‖²≤‖p^n‖²`。`physical_middle_energy` 对真实中部节点求和并使用 T/6 测度，给出 `(T/6)exp(−4MT)‖p^0‖²≤dt Σ_middle ‖p^i‖²`。这里没有擅自引入空间指数权；原 `eq:initial-adjoint-recovery` 中 Carleman 能量的空间权下界仍待以后连接。

这组能量引理以 `Adjoint dt L p` 和真实二次型下界 `⟨L_i x,x⟩≥−M‖x‖²` 为显式接口。原 Section 7 的数据可由 `stiffness_potential_lower` 供应下界，并由 `adjoint_equation_iff` 在真实自伴 L=A+V 下转入该递推。相关 Lemma 7.1 六模块相对已验收 SHA `1aa9b1f253dd759ccc18d92d151aa7c81646f51c` 没有修改；本次实际核查了调用的参数和方向。未要求 A 或势的特征子空间、低频截断、时间独立势或伴随轨迹的额外空间正规性。

## 70 项显式声明

下表逐项语义结论均为 PASS；基础定义不被冒作完整观测定理，带显式辅助参数的定理只按其实际条件验收。

| # | 声明 | 实际内容 |
| --- | --- | --- |
| 1 | `Carleman.Physical.periodic_next_of_endpoints` | 真实 N+1 端点相容后，末格正确转为周期 next。 |
| 2 | `Carleman.Physical.cutoffState` | 真实 χ_i p_i 限制到 N 个周期代表节点。 |
| 3 | `Carleman.Physical.cutoffRemainder` | 实际差商乘物理 p^(i+1)。 |
| 4 | `Carleman.Physical.cutoff_next` | 使用 χ 的两个零端点，不要求 p 周期。 |
| 5 | `Carleman.Physical.cutoff_difference` | D_- 的准确乘积差分及 −r 符号。 |
| 6 | `Carleman.Physical.cutoff_residual` | 由真实 Hilbert 伴随方程得到 −Vz−r。 |
| 7 | `Carleman.Physical.physicalWeightDenom` | 原正则化正弦分母。 |
| 8 | `Carleman.Physical.physicalWeight` | 原 qb/分母函数。 |
| 9 | `Carleman.Physical.physicalWeightDenom_pos` | δ>0 时全实线严格正。 |
| 10 | `Carleman.Physical.physicalWeightDenom_sq` | 分母平方准确还原。 |
| 11 | `Carleman.Physical.physicalWeightDenom_bounds` | 原 δ 与 sqrt(1+δ²) 上下界。 |
| 12 | `Carleman.Physical.physicalWeight_bounds` | 原全时 q 上下界。 |
| 13 | `Carleman.Physical.physicalWeight_zero` | 端点实际达到 qb/δ。 |
| 14 | `Carleman.Physical.physicalWeight_periodic` | 正弦平方给出真实 T 周期。 |
| 15 | `Carleman.Physical.physicalWeightDenom_hasDerivAt` | 正分母的实际平方根导数。 |
| 16 | `Carleman.Physical.physicalWeightDerivative` | 显式一阶表达式，随后被真实识别。 |
| 17 | `Carleman.Physical.physicalWeight_hasDerivAt` | 实际 q 的一阶导数证明。 |
| 18 | `Carleman.Physical.physicalWeight_smooth` | δ>0 下全局 C∞。 |
| 19 | `Carleman.Physical.physicalWeight_derivative_bound` | 准确 π/(qbT) 比界。 |
| 20 | `Carleman.Physical.physicalTimeWeight` | 原函数进入 q≥1 和 qmax 数据接口。 |
| 21 | `Carleman.Physical.physicalTimeWeightRegularity` | 实际一阶正则性及 q 周期端点；预算显式。 |
| 22 | `Carleman.Physical.physicalWeightSecondDerivative` | 显式二阶表达式，随后被真实识别。 |
| 23 | `Carleman.Physical.physicalWeightDerivative_hasDerivAt` | 对实际一阶表达式再次求导。 |
| 24 | `Carleman.Physical.physicalWeight_second_derivative_bound` | 准确 4π²/(qb²T²) 比界。 |
| 25 | `Carleman.Physical.physicalWeight_deriv` | 识别实际 deriv q。 |
| 26 | `Carleman.Physical.physicalWeight_second_deriv` | 识别实际 deriv(deriv q)。 |
| 27 | `Carleman.Physical.physicalWeightDerivative_zero` | 原 q'(0)=0。 |
| 28 | `Carleman.Physical.physicalWeightDerivative_periodic` | 实际首阶导数 T 周期。 |
| 29 | `Carleman.Physical.clipUnit` | 具体截断至 [0,1]。 |
| 30 | `Carleman.Physical.clipUnit_bounds` | 全局 [0,1] 值域。 |
| 31 | `Carleman.Physical.clipUnit_zero` | 非正输入取零。 |
| 32 | `Carleman.Physical.clipUnit_one` | 输入≥1 取一。 |
| 33 | `Carleman.Physical.clipUnit_lipschitz` | 真实 1-Lipschitz 界。 |
| 34 | `Carleman.Physical.endpointDistance` | min(t,T−t)，在物理区间为端点距离。 |
| 35 | `Carleman.Physical.endpointDistance_lipschitz` | 全局 1-Lipschitz。 |
| 36 | `Carleman.Physical.physicalCutoff` | 具体宽度 a 的截断函数。 |
| 37 | `Carleman.Physical.physicalCutoff_bounds` | 具体 χ 取值 [0,1]。 |
| 38 | `Carleman.Physical.physicalCutoff_zero` | 距端点≤a 为零。 |
| 39 | `Carleman.Physical.physicalCutoff_one` | 距端点≥2a 为一。 |
| 40 | `Carleman.Physical.physicalCutoff_endpoints` | 实际 t=0、T 同时消失。 |
| 41 | `Carleman.Physical.physicalCutoff_lipschitz` | 实际 1/a 差值界。 |
| 42 | `Carleman.Physical.cutoffNodes` | 完整 N+1 物理节点取样。 |
| 43 | `Carleman.Physical.cutoffNodes_endpoints` | 节点 0 与 N 消失。 |
| 44 | `Carleman.Physical.cutoffNodes_difference` | 真差商≤1/a，步长正确消去。 |
| 45 | `Carleman.Physical.cutoffNodes_transition_location` | 非零差分起点距某端点≤2a+dt。 |
| 46 | `Carleman.Physical.leftNodes` | 实际 Fin N 左窗口。 |
| 47 | `Carleman.Physical.rightNodes` | 实际 Fin N 右窗口。 |
| 48 | `Carleman.Physical.leftNodes_measure` | floor 计数得到 dt*card≤b+dt。 |
| 49 | `Carleman.Physical.rightNodes_measure` | rev 注入保留右窗口端点偏移。 |
| 50 | `Carleman.Physical.middleNodes` | 原中央三分之一中的实际节点。 |
| 51 | `Carleman.Physical.middleNodes_measure` | 原 dt≤T/12 下离散测度≥T/6。 |
| 52 | `Carleman.Physical.transitionNodes` | 实际差商非零集。 |
| 53 | `Carleman.Physical.transitionNodes_measure` | dt≤a/4 时安全 5a 上界。 |
| 54 | `Carleman.Physical.sine_reflect` | 真实正弦端点反射恒等式。 |
| 55 | `Carleman.Physical.sine_endpoint_bound` | 物理区间上由端点距离控制正弦。 |
| 56 | `Carleman.Physical.physicalWeight_near_endpoint` | 距端点≤3δT 时的原分母常数。 |
| 57 | `Carleman.Physical.sine_middle_lower` | 中部真实 sin≥1/2。 |
| 58 | `Carleman.Physical.physicalWeight_middle_upper` | 原中部 q≤2qb。 |
| 59 | `Carleman.Physical.concrete_cutoff_residual` | 具体 χ 的真实伴随残差。 |
| 60 | `Carleman.Physical.cutoffNodes_one_middle` | a≤T/16 时真实中部 χ_i=1。 |
| 61 | `Carleman.Physical.cutoff_remainder_zero` | 过渡集外实际 r_i=0。 |
| 62 | `Carleman.Physical.cutoff_remainder_norm_bound` | 真实轨迹点态界 K 给 K/a。 |
| 63 | `Carleman.Physical.cutoff_remainder_energy_bound` | 真节点求和得到 5K²/a。 |
| 64 | `Carleman.Physical.physical_adjoint_terminal_bound` | 实际 Lemma 7.1 给所有节点终端控制。 |
| 65 | `Carleman.Physical.physical_cutoff_remainder_energy` | 真伴随给 (5/a)e^(4MT)‖pN‖²。 |
| 66 | `Carleman.Physical.physical_adjoint_initial_lower` | 真伴随反向界平方后恢复初值。 |
| 67 | `Carleman.Physical.physical_middle_energy` | 真实中部测度和初值下界合成。 |
| 68 | `Carleman.Physical.physical_delta_conditions` | δ=qb/S 的正性、大小、qmax 和原网格后果。 |
| 69 | `Carleman.Physical.physical_transition_weight` | 真实过渡节点 q_i≥S/sqrt(1+9π²)。 |
| 70 | `Carleman.Physical.physical_weight_endpoint_decay` | 原点态端点指数，c_end 完全不变。 |

## 构建与公理证据

固定本机日志 `/tmp/carleman-observation-foundations-full.log` 包含 `Build completed successfully (3490 jobs).`。固定公理副本 `/tmp/carleman-observation-foundations-local-axioms.txt` 为 973302 字节，SHA-256 为 `774557b39badad5efa4d0eaed0dab9f72622868e4e187b4633c7b3727cd777bd`。70/70 项都有实际展开类型及逐项公理输出，全部只含 `propext, Classical.choice, Quot.sound`；全局结尾为 `Axiom audit passed for all 3436 Carleman declarations.`。

固定提交审计器递归 `collectAxioms` 检查所有公开/私有 Carleman 声明，只允许三项标准基础公理；无 sorryAx 或未批准数学公理。根 `Carleman.lean` 显式导入八模块。工具链、mathlib pin、CI 工作流和构建脚本相对基线未变；本次修改没有改变既有数学依赖，仅新增这八个数学模块及根导入/审计清单。

已通过 GitHub connector 独立读取 [main CI 39142758460 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39142758460/attempts/1)，确认 `event=push`、`head_branch=main`、`head_sha=c3ab9aaef14a4f5beca82505cdfd325e507c653e`、`status=completed`、`conclusion=success`。实际三个 jobs 均完成且成功：`lean`（117720368708）、`state-check`（117720368920）、`dashboard / snapshot`（117721011653）。同时独立读取该运行的 artifact 元数据，`lean-ci-result`（12142246617）与 `lean-declaration-evidence`（12142261689）均绑定上述同一 head SHA，且未过期。

下载的原始 `/tmp/carleman-observation-foundations-main-ci/result.json` 为 537 字节，SHA-256 为 `c8fea3b6fe7c2b034a2cddc96fb65e944b8cc502ec3e90fc57fc1f54c3052d1b`；其中 `status=PASS`，`checked_sha` 与 `source_head_sha` 均为本次固定 SHA，`finished_at=2026-10-18T15:58:53.251430+00:00`，目标 `Carleman`，Lean 4.35.0，mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

原始 `/tmp/carleman-observation-foundations-main-axioms/axioms.txt` 为 973302 字节，SHA-256 为 `774557b39badad5efa4d0eaed0dab9f72622868e4e187b4633c7b3727cd777bd`，与固定本机副本逐字节相同。再次针对远端产物核对 70/70 项实际类型与公理输出，每项仅有三项标准基础公理；全库递归审计为 3436 声明 PASS。报告表格的 70 项名称和顺序也与交付名单逐项一致。正式 PASS 由这些同 SHA 原始产物支持，不借用后续模块或其它提交的构建结果。

本报告只写验收文件，未修改源码、台账、论文或根导入，未 commit/push。
