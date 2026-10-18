# T026 — 真实物理 HUM 条件桥独立本机验收

- `checked_sha`：`549cde718bcf26f00b24f4a1493ee92b839f30b4`
- `base_commit`：`12d18c9c6548cc70165ad9e4c01314f4438dc5f1`
- `reviewed_at`：`2026-10-18T15:45:39+00:00`（UTC）。
- reviewer：独立本机验收 Agent `/root/accept_spatial_foundations`，非本阶段执行者。
- target：C042，四个新模块、全部 23 项显式声明；原 Theorem 7.3 `prop:physicalC` 的完整 HUM 条件桥。
- `result`：**PASS**（真实物理 HUM 完整条件桥）。
- `axiom_check`：**PASS**（同 SHA 真实 CI，3349 项递归审计）。
- scope：**CONDITIONAL**。
- `extra_hypotheses`：`["真实伴随轨迹的松弛观测估计；原Theorem7.2尚未供应"]`。

独立阅读固定提交导出树 `/tmp/carleman-hum-review-549c` 的全部四模块、实际 elaborated 类型及关键上游证明，核对原 `paper/main.tex` Section 7 的算子和真实物理时间方程、Theorem 7.3（2032 行起）及完整 HUM 证明（2051–2103 行）。原 Theorem 7.2 的观测结论（1827 行起）用于检查显式输入内容，未将其视为已证明。未审核后续工作树代码；执行者规格说明仅用于范围和定位。

## 审核范围及最终条件结论

最终 `relaxed_control_of_observation` 在真实有限维实 Hilbert 状态空间 X、任意完备实 Hilbert 控制空间 U、非负自伴 A、每步自伴势 V_i 且 `‖V_i‖≤M`、`dt*M≤1/2` 下，显式输入真实伴随轨迹的估计

\[
\|p^0\|^2\le C\left(dt\sum_{i=0}^{N-1}\|B^*p^i\|^2+e^{-2dS}\|p^N\|^2\right).
\]

其输出对每个真实初值 y0，存在控制 u 和完整 N+1 节点轨迹 y，满足 y⁰=y0、原 `ForwardEquation`，以及

\[
\|u\|_{\ell^2_{dt}(U)}\le\sqrt C\,\|y_0\|,
\qquad
\|y^N\|_X\le\sqrt C\,e^{-dS}\|y_0\|.
\]

这正是原 Theorem 7.3 的 HUM 推导部分，保留原控制符号、真实控制范数和实际终端状态；没有以任意替代向量的范数界充当终值结论。最终轨迹满足每一时间步的实际方程，未施加谱截止、终端子空间、周期回绕或初值限制。

但上述松弛观测是明确假设，原 C(T,M)、d0、S_(h,dt) 及其允许网格条件仍需原 Theorem 7.2 和具体离散实现供应。因此本报告只允许 C042 升为 `REVIEWED/CONDITIONAL`，不能据此将 P015 或原 Theorem 7.3 标为 PAPER 完成。

## 真实伴随流、控制空间与时间权重

`physicalStepEquiv` 使用原 `Id+dt L_i` 的有限维双射构造真实线性等价，不输入一个任意逆。`adjointNode n` 从终端恒等映射开始，按物理时间反向施加相应步逆。`adjointNode_last` 保证末值严格为给定 z；`adjointNode_step` 保证 `(Id+dt L_i)p^i=p^(i+1)`。结合已验收的原初末值唯一性，它就是任意终值 z 对应的真实伴随解。节点单射来自各步逆的复合，未要求不同时间算子可交换。

`initialMap`（此处简称 R，与前文空间重构符号无关）是 z↦p⁰。其连续性由有限维定义域给出，单射由实际伴随流给出。`initialMap_bound` 对 M≥0 调用原反向能量界，得到 `‖Rz‖≤exp(2M N dt)‖z‖`；没有另加节点数因子。

`observationMap` 的值域是 `PiLp 2 (fun _ : Fin N => U)`，第 i 项恰为 `sqrt(dt) • B.adjoint(p^i)`。对原编号 n=i+1，这一位置正是 p^(n−1)，最后一步观察 p^(N−1)，不观察 p^N。`observationMap_norm_sq` 从 PiLp 的真实 L² 范数公式得到

`‖Oz‖² = dt ∑ i ‖B* p^i‖²`。

U 仅要求 `NormedAddCommGroup`、实 `InnerProductSpace` 和 `CompleteSpace`，没有 `FiniteDimensional U`；有限乘积 PiLp 同样为 Hilbert 空间。所有 B*、O*、R* 均是实际 `ContinuousLinearMap.adjoint`。X 的完备性由原有限维性供应，O 的连续性由有限维定义域供应；没有利用有限维值域的错误推断。

`controlVector dt u` 使用相同的 sqrt(dt) 嵌入，`controlVector_norm` 证明其范数严格等于原 `sqrt(dt∑‖u_i‖²)`。`controlVector_unscale` 在 dt>0 下证明所有 PiLp 控制向量均可通过 `(sqrt dt)⁻¹` 逆缩放得到。最终 TimeGrid 的 dt>0 清偿逆缩放的非零条件，不在 dt=0 时使用总化逆元。

`control_observation_pairing` 用真实 PiLp 内积和两次 sqrt(dt) 精确得到 `dt∑⟨u_i,B*p^i⟩`。控制代价中不存在额外 sqrt(dt)、dt⁻¹、sqrt(N) 或 sqrt(T) 因子。

## 正定 HUM 方程与代价

`humOperator O ε = O*O+ε² Id` 是真实连续线性自映射。`humOperator_pairing` 对任意 x、v 给出 `⟨Hx,v⟩=⟨Ox,Ov⟩+ε²⟨x,v⟩`。在 ε>0 时，若 Hx=0，则 `‖Ox‖²+ε²‖x‖²=0` 强制 x=0；随后仅对有限维自映射 X→X 使用单射蕴含满射。U 可以无限维，证明并未对 O 或 U 使用该推论。

`hum_optimality` 解真实线性方程 `Hz=R*y0`，并证明唯一性与所有测试 v 的完整最优性方程

`⟨Oz,Ov⟩+ε²⟨z,v⟩=⟨y0,Rv⟩`。

这是原 `eq:hum-optimality` 在加权观测映射下的准确表达。形式化直接用正定双射取得唯一最优性解；相对于原先定义严格凸 J 再取极小点的路线，这是等价证明路线。具体而言，对原 `J(z)=‖Oz‖²/2+ε²‖z‖²/2−⟨y0,Rz⟩`，该最优性方程消去展开中的线性项，得到 `J(z+w)−J(z)=‖Ow‖²/2+ε²‖w‖²/2`，故 w≠0 时严格为正。实际声明证明的是唯一最优性方程，并未将未知极小点、可控性结论或观测常数的存在作为隐藏输入。

`penalized_hum_control` 令 `Q=‖Oz‖²+ε²‖z‖²≥0`。代入 v=z 后得到 `Q=⟨y0,Rz⟩≤‖y0‖‖Rz‖`，再用显式观测 `‖Rz‖²≤C Q` 得 `Q(Q−C‖y0‖²)≤0`。通过非负性推出 `Q≤C‖y0‖²`，包括 Q=0；没有除以可能为零的 sqrt(Q)。C=0 也由同一代数论证覆盖。

取 v_control=−Oz，得到 `‖v_control‖≤sqrt(C)‖y0‖` 和准确恒等式

`R*y0+O*v_control = ε² • z`。

由 `ε‖z‖≤sqrt(C)‖y0‖` 再乘 ε 得余量 `≤ε sqrt(C)‖y0‖`。ε² 在 HUM 惩罚和精确终值恒等式中出现，ε 在最终范数估计中出现，二者未混淆。逆缩放后的实际控制满足原 `u^n=−B* p_hat^(n−1)`；构造中使用同一真实伴随流与同一 B。

## 实际终值与原方程连接

`terminal_representation` 对任意满足真实前向递推的完整轨迹 y 和任意控制 u，使用原精确物理对偶及任意终值测试 z，证明

`y^N = R*(y^0) + O*(controlVector u)`。

该等式使用全部 z∈X 的内积分离性；实际伴随节点的终端恒等映射消除了 p^N 的中间表示。首末端项均保留，没有使用周期求和使它们相消。

`physical_hum_control` 首先把显式伴随观测应用于每个实际 `adjointNode` 解，得到 HUM 所需映射观测。它取得 PiLp 控制后逆缩放，再调用已证 `existsUnique_forward`，从给定任意 y0 和实际载荷 Bu 构造全部前向节点。随后把这个真实解代入 `terminal_representation`，所以末端余量确实控制该前向解的 y^N。

最终 `relaxed_control_of_observation` 取 L_i=A+V_i，由 A 非负和原势算子范数得 `⟨L_i x,x⟩≥−M‖x‖²`，由二者自伴性得 L_i 自伴。`adjoint_equation_iff` 使用真实 `.adjoint` 与自伴性，把原除以 dt 的 `AdjointEquation` 连接到已证递推；`forward_equation_iff` 将输出还原为原除以 dt 的前向方程。没有把一个自由命名的算子直接称为伴随。

取 `ε=exp(−dS)>0`，实际证明 `ε²=exp(−2dS)` 后调用 HUM，输出精确 `sqrt(C)exp(−dS)`。桥允许任意实 d、S；代数结论在这些参数下有效。要解释为原指数衰减，需要原 Theorem 7.2 供应 d=d0>0 和正确的 S=S_(h,dt)，本阶段没有证明这些参数与网格、权函数的来源。

代价恰为观测常数的平方根，独立于 y0；一旦输入观测的 C 对 h、dt、维数统一，输出自动保持同样统一性。桥没有另外乘上初值映射范数、势范数、时间长度或步数。原 Section 7 允许 C 依赖 T、M；本报告不将它误称为对 T 无依赖的常数。最终省略未用于该条件蕴含的 `‖B‖≤1`、独立 M≥0 等原条件是扩大适用范围，不是新增前提；本阶段不因此宣称已完成具体 B、A、V 的离散实现验证。

## 全部 23 项显式声明

模块路径相对于 `Carleman/Control/`。每项均核对实际源码、elaborated 类型与递归公理输出。

| # | 完整声明 | 固定模块及行 | 独立核查结论 |
| --- | --- | --- | --- |
| 1 | `Carleman.Physical.physicalStepEquiv` | `PhysicalFlow.lean:15` | PASS；真实步算子的有限维双射及其逆。 |
| 2 | `Carleman.Physical.adjointNode` | `PhysicalFlow.lean:18` | PASS；从终端恒等映射逐步反向构造全部物理节点。 |
| 3 | `Carleman.Physical.adjointNode_last` | `PhysicalFlow.lean:22` | PASS；实际末端等于给定终值。 |
| 4 | `Carleman.Physical.adjointNode_step` | `PhysicalFlow.lean:25` | PASS；准确物理伴随步方程，无周期回绕。 |
| 5 | `Carleman.Physical.adjointNode_injective` | `PhysicalFlow.lean:33` | PASS；每个节点为可逆步复合，无交换假设。 |
| 6 | `Carleman.Physical.initialMap` | `PhysicalFlow.lean:41` | PASS；真实终值到初值的连续线性映射。 |
| 7 | `Carleman.Physical.initialMap_injective` | `PhysicalFlow.lean:43` | PASS；由实际节点单射继承。 |
| 8 | `Carleman.Physical.initialMap_bound` | `PhysicalFlow.lean:46` | PASS；原 exp(2M N dt) 初值界。 |
| 9 | `Carleman.Physical.observationLinear` | `PhysicalFlow.lean:58` | PASS；真实 B*、p^(n−1) 及 sqrt(dt) 时间权。 |
| 10 | `Carleman.Physical.observationMap` | `PhysicalFlow.lean:68` | PASS；有限维定义域给连续性，U 保持任意 Hilbert。 |
| 11 | `Carleman.Physical.observationMap_norm_sq` | `PhysicalFlow.lean:71` | PASS；真实 N 步离散观测积分精确识别。 |
| 12 | `Carleman.Physical.humOperator` | `PenalizedHUM.lean:13` | PASS；真实 O*O+ε²Id。 |
| 13 | `Carleman.Physical.humOperator_pairing` | `PenalizedHUM.lean:15` | PASS；所有 x、v 的精确对称正型配对。 |
| 14 | `Carleman.Physical.humOperator_bijective` | `PenalizedHUM.lean:21` | PASS；ε>0 给核为零，仅在 X 自映射上使用有限维满射。 |
| 15 | `Carleman.Physical.hum_optimality` | `PenalizedHUM.lean:40` | PASS；唯一终值 z、对所有测试向量的完整最优性方程。 |
| 16 | `Carleman.Physical.penalized_hum_control` | `PenalizedHUM.lean:53` | PASS；显式观测下负号控制、统一 cost、准确余量，Q=0 安全。 |
| 17 | `Carleman.Physical.controlVector` | `PhysicalHUM.lean:14` | PASS；真实控制序列的 sqrt(dt) 加权嵌入。 |
| 18 | `Carleman.Physical.controlVector_norm` | `PhysicalHUM.lean:17` | PASS；与原 ℓ²_dt 控制范数严格相等。 |
| 19 | `Carleman.Physical.controlVector_unscale` | `PhysicalHUM.lean:26` | PASS；dt>0 下完整 PiLp 控制可逆缩放。 |
| 20 | `Carleman.Physical.control_observation_pairing` | `PhysicalHUM.lean:36` | PASS；原 dt 乘时间和，观察位置 p^(n−1)。 |
| 21 | `Carleman.Physical.terminal_representation` | `PhysicalHUM.lean:45` | PASS；任意真实前向解的实际终值等于对偶表达式。 |
| 22 | `Carleman.Physical.physical_hum_control` | `PhysicalHUM.lean:62` | PASS；任意真实初值的完整前向轨迹、实际控制和终值界。 |
| 23 | `Carleman.Physical.relaxed_control_of_observation` | `RelaxedControl.lean:13` | PASS／CONDITIONAL；原真实算子/伴随方程与 exp(−dS) 余量，观测明确保留为前提。 |

## 版本、依赖与构建证据

23 项名称及顺序与固定 C042/T026 台账和 `/tmp/carleman-hum-declarations.json` 完全一致。四模块均由固定 `Carleman.lean` 导入，其本地 import 闭包含自身共 11 模块，根 import 闭包共 285 模块。与 base `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` 比较，本阶段数学源码仅新增上述四模块；import 闭包中既有数学文件、工具链及 mathlib pin 均未变化。

原 Lemma 7.1 已有固定 `1aa9b1f253dd759ccc18d92d151aa7c81646f51c` 的 [T024 独立验收报告](T024-local-acceptance.md)。本次额外直接核对 `FiniteResolvent`、`PhysicalSolutions`、`PhysicalDuality`、`PhysicalEnergy`、`PhysicalEquations`、`PhysicalLemma` 真实接口与所用证明；未借用与本阶段无关的滤波反向界。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

本机 `/tmp/carleman-hum-full.log` 记录 `Build completed successfully (3475 jobs).`。固定审计 `/tmp/carleman-hum-local-axioms.txt` 为 949649 字节，SHA256 为 `86cd8704bcc24a85c98de0fa5553940651ec2ccbb3792e07ad3f191871b75d1e`，末尾为 `Axiom audit passed for all 3349 Carleman declarations.`。23 项实际类型均已读过，各项公理输出均恰为 `propext`、`Classical.choice`、`Quot.sound`。全环境审计器递归 `collectAxioms`，覆盖还原私有名后的 Carleman 声明，并拒绝任何其它公理；不存在 sorryAx 或新增数学公理。显式观测前提是命题的条件，而不是被隐藏为公理。

通过 GitHub connector 独立读取 [main CI 39141525842 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39141525842/attempts/1) 的 run 与 jobs：`head_sha=549cde718bcf26f00b24f4a1493ee92b839f30b4`、`head_branch=main`、`event=push`、`status=completed`、`conclusion=success`。`state-check`（117716812781）、`lean`（117716812986）、`dashboard / snapshot`（117717358446）三项均成功；实际 proof target 构建、checked source 记录及证据上传步骤均成功。另独立读取 artifacts 元数据，`lean-ci-result`（12141712037）和 `lean-declaration-evidence`（12142030551）的 `workflow_run.head_sha` 均为本次固定 SHA。

实际读取下载产物 `/tmp/carleman-hum-main-ci/result.json`，确认 `status=PASS`、`checked_sha=source_head_sha=549cde718bcf26f00b24f4a1493ee92b839f30b4`、target=`Carleman`、`finished_at=2026-10-18T15:41:58.029847+00:00`。结果 JSON 的 SHA256 为 `b7e14ec2419b9d86325119465e238b98581db6556a58c7915e7d4c4008451b69`。Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 与固定源码 pin 一致。

正式公理证据为同次下载的 `/tmp/carleman-hum-main-axioms/axioms.txt`，949649 字节，SHA256 为 `86cd8704bcc24a85c98de0fa5553940651ec2ccbb3792e07ad3f191871b75d1e`。实际比较确认它与固定本机审计逐字节一致，并在正式 CI 文件内再次逐名验证全部 23 项实际类型和三项标准基础公理集合，末尾完整 3349 声明审计通过。未使用后续源码或其它 SHA 的构建产物。

## 结论边界

固定 SHA 下，全部 23 项的数学语义、原物理方程连接、同 SHA 真实构建及递归公理检查均为 **PASS**，未发现需要修正的数学缺陷。C042 可升级为 `REVIEWED`，范围必须保持 `CONDITIONAL`，显式观测额外假设必须保留，并绑定本报告及同 SHA 构建证据。

本结果完成了从真实松弛观测到任意初值真实物理控制的完整 HUM 蕴含。原 Theorem 7.2 的观测估计及参数/网格条件尚待证明，故 P015 / 原 Theorem 7.3 不得因此升级为原文完成；也不据此验收具体 FEM/FD 实现、后续滤波控制、收敛或整篇论文。

本次仅写本报告；未修改源码、根导入、论文、台账或覆盖表，未 commit/push。
