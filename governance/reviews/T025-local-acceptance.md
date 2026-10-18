# T025 — 原 Lemma 7.4 独立本机验收

- checked_sha: `12d18c9c6548cc70165ad9e4c01314f4438dc5f1`
- base_commit: `1aa9b1f253dd759ccc18d92d151aa7c81646f51c`
- reviewed_at: `2026-10-18T15:35:53Z`（UTC；同 SHA 真实 CI 产物核验完成）
- reviewer: 独立数学验收 Agent `/root/accept_section3`，非 T025 执行者。
- targets: C041 / P016；原 `lem:filter-reverse`，四个模块、全部 19 项显式声明。
- semantic_result: **PASS**。
- axiom_check: **PASS**（同 SHA 真实 main CI 的 3287 项递归审计；全部 19 项类型与递归公理逐项核验）。
- result: **PASS**；C041 / P016 可升为 REVIEWED/PAPER。
- extra_hypotheses: `[]`（相对于原 Section 7 算子数据）。

直接阅读固定提交的四个模块全部证明、19 项实际类型及公理输出，对照 `paper/main.tex` 的 Section 7 算子设置、`eq:adjoint`、`eq:physicalconditions`、原 Lemma 7.4（2164 行起）与附录证明（2962 行起）。未发现数学保真缺口；没有把执行者分析记录或先前报告代替本次检查。

## 原命题与最终入口

`Carleman.Physical.filter_reverse` 对任意原有限维实 Hilbert 状态空间 X、非负自伴 A、每步自伴势 V_i 且 `‖V_i‖≤M`、`M≥0`、`dt*M≤1/2`，以及任意终端子空间 F 和真实伴随解 p，证明

\[
\|p^N\|\le \exp\bigl(T\Lambda_F+MT+M^2T^2/2\bigr)\|p^0\|,
\qquad p^N\in F.
\]

`filterRayleigh A F` 定义为非零 F 向量的真实 Rayleigh 商集合在 ℝ 中的 `sSup`，F=0 时单独定义为 0；`filterConstant` 是上述原 K_F 的确切表达式。最终没有输入商增长、逆算子下界、反向范数界或滤波观测结论。

所有范数和内积来自同一个 X 实 Hilbert 结构，实际 `.adjoint` 也使用该结构。有限维性是原 X_h 数据，连续线性算子表示不增加限制。没有严格正刚度下界、A 的统一算子范数界、势正性、不同步势交换、F 不变性或低频轨迹条件。F 只在最后一步用于 `p^N∈F`；中间 p^n 从未要求留在 F。

原 filtering 小节继承的物理网格条件包含 `dt*M≤1/2`。本引理不使用其余 h、Carleman 参数或观测条件，形式化省略这些条件扩大适用范围，没有新增前提。`TimeGrid` 仅提供正 N、正 dt 和定义上的 `T=N*dt`；轨迹是 `Fin (N+1)→X`，使用 `castSucc/succ/last` 的物理节点，不调用周期 next/prev。N>0 包含原 N≥2。T 在此按原公式明确进入 K_F；没有声称本引理常数与 T 无关。

## 单步 Rayleigh 增长

`rayleigh A z=⟨Az,z⟩/‖z‖²` 使用原真实算子与范数。`rayleigh_nonneg` 从 A 的非负二次型推出非负，`rayleigh_smul` 对所有非零缩放给出准确齐次性。

`rayleigh_step_normalized` 对 `‖z‖=1` 设置原证明中的 r、b、v、w、ξ、γ。直接从真实内积证明 v、w、ξ 与 z 正交，并由 `‖Vz‖≤M` 得 `‖w‖²≤M²`。原小性条件给

\[
2\gamma-dt\,r\ge1,
\qquad \|x\|^2=\gamma^2+dt^2\|\xi\|^2,
\quad x=(I+dt(A+V))z.
\]

证明以 `‖ξ−γw‖²≥0` 完成平方，再使用 A 非负及 `γ²≤‖x‖²`，得到
`r‖x‖²≤⟨Ax,x⟩+dt*M²‖x‖²`。这是原附录所需的最终单步增长；省略较精细中间分母 `2(1−dtM)` 不改变原最终界。

`rayleigh_step` 对任意非零 z 作真实范数归一化。除以 `‖x‖²` 之前，由既有 `step_norm_lower` 和 `dt*M≤1/2` 证明该分母严格正。之后通过齐次性还原，得到 `ν(z)≤ν(x)+dt*M²`。没有依赖 Lean 在零分母处的除法默认值，也没有要求 V 对称；辅助层省略 V 对称是加强，而最终真实伴随入口仍保留原自伴势。

## 正算子逆界与 incoming 商

`positive_form_cauchy` 从 `⟨B(tx+y),tx+y⟩≥0` 对所有实 t 成立，应用二次判别式，证明真实正对称形式的 Cauchy–Schwarz。它不假设逆界或谱结论。

`positive_resolvent_lower` 令 B=I+dt A，使用该形式不等式及 `By=x` 得 `‖x‖⁴≤⟨x,y⟩⟨Bx,x⟩`，再用普通内积 Cauchy–Schwarz。因 x≠0，可约去正因子 `‖x‖³`，得

\[
\|x\|\le(1+dt\,\nu(x))\|y\|.
\]

因此 Rayleigh 商确实在逆映射的输入 x 上。`perturbed_resolvent_lower` 用既有有限维双射证明构造真实 `E=I+dt A` 的逆，取 y=E⁻¹x、w=E⁻¹Vz，证 y=z+dt w 和 `‖w‖≤‖Vz‖`。由原势范数界得 `‖y‖≤(1+dt M)‖z‖`，合成

\[
\|x\|\le(1+dtM)(1+dt\nu(x))\|z\|,
\quad x=(I+dt(A+V))z.
\]

这逐字对应原附录 incoming 的 `ν_{j−1}`。没有把它错误换成 outgoing 的 `ν_j`；也没有借助 ‖A‖、维数、F 不变或原目标估计。

## 全轨迹、零终值与精确迭代

中间 `Adjoint` 是每步 `step(L_i)p^i=p^(i+1)`。`adjoint_nonzero` 从非零终值反向归纳：若前节点为零，线性步映射给后一节点零，与归纳假设矛盾。这个论证本身无需单步逆存在，足以保证后续所有商分母合法。

`adjoint_rayleigh_bound` 对 `ν(p^n)+n*dt*M²` 证明沿物理 n 单调，得到
`ν(p^n)≤ν(p^N)+(N−n)dt*M²`，方向与原 z_j=p^(N−j) 一致。

`adjoint_reverse_rayleigh` 首先单独处理 p^N=0，结论由指数正和范数非负立即成立。非零终值时，将上述 incoming 逆界应用于 x=p^(i+1)、z=p^i，用 `1+r≤exp(r)` 放大各正因子，再对精确离散原函数

\[
H(n)=dt(M+\nu(p^N))n+
\frac{dt^2M^2}{2}n(2N-n-1)
\]

证明 `‖p^(i+1)‖≤exp(H(i+1)−H(i))‖p^i‖`。`exponential_recurrence` 通过有限归纳和 exp 加法恒等式望远镜相乘；没有使用未说明的无穷乘积或对数合法性。末端实际指数为
`T(M+ν(p^N))+M²dt²N(N−1)/2`，以非负的 `M²dt²N/2` 放大后恰为原 `Tν(p^N)+MT+M²T²/2`。N 个步、N+1 个状态和半系数均准确。

最终 `filter_reverse` 用 `A+V_i` 的原自伴性，通过已证明 `adjoint_equation_iff` 和 mathlib 的 `IsSymmetric.clm_adjoint_eq`，把原
`dt⁻¹(p^i−p^(i+1))+(A+V_i).adjoint(p^i)=0`
转为上述递推；不是将一个任意算子命名为伴随。它对任意满足真实方程的 p 成立，不只适用于选定构造解；先前已验收的存在唯一性确保原终值问题可解，本次不把该事实改作额外假设。

## 真实上确界与常数依赖

`rayleigh_le_opNorm` 以普通内积 Cauchy–Schwarz 与实际连续线性算子范数证明所有非零向量商不超过 ‖A‖。`rayleigh_le_filterRayleigh` 先由 x∈F、x≠0 排除 F=0，然后向 `le_csSup` 供应集合的真正有上界性及当前商的真正成员资格。不存在对空集或无界集默认 sSup 值的依赖。对 F≠0，子空间本身含非零向量；最终非零终值分支还直接提供这个成员。F=0 的定义与原 `Λ_{0}=0` 完全一致，零终值分支已独立覆盖。

‖A‖只用于证明商集合有上界，不用于放大最终指数；最终实际使用 `ν(p^N)≤Λ_F` 和 T>0。精确 K_F 仅含 T、M、原 Λ_F，除了原 Λ_F 自身的算子依赖外，无新增 ‖A‖ 或空间维数依赖。子空间可任意变化；不需要特征基、谱投影、A 或势保持 F。常数的 T、M、Λ_F 表达式在定义中明确，因而对所有物理网格、维数及满足原数据的算子统一。

## 全部 19 项声明

以下逐项均已核对固定源码、实际 elaborated 类型、原文作用及递归公理；每项公理集合均恰为 `[propext, Classical.choice, Quot.sound]`。

| # | 声明 | 核查结果 |
|---|---|---|
| 1 | `Carleman.Physical.rayleigh` | PASS：原算子内积与真实范数平方的商。 |
| 2 | `Carleman.Physical.rayleigh_nonneg` | PASS：原 A 非负给商非负。 |
| 3 | `Carleman.Physical.rayleigh_step_normalized` | PASS：原正交分解、完成平方和 dt*M² 单步界。 |
| 4 | `Carleman.Physical.rayleigh_smul` | PASS：非零缩放下准确齐次性。 |
| 5 | `Carleman.Physical.rayleigh_step` | PASS：非零任意 z，实际证明输入与输出范数分母合法。 |
| 6 | `Carleman.Physical.positive_form_cauchy` | PASS：真实正对称形式二次判别式证明。 |
| 7 | `Carleman.Physical.positive_resolvent_lower` | PASS：正逆界使用 incoming x 的商。 |
| 8 | `Carleman.Physical.perturbed_resolvent_lower` | PASS：真实有限维逆和势范数给原双因子界。 |
| 9 | `Carleman.Physical.adjoint_nonzero` | PASS：非零终值推出全物理轨迹非零。 |
| 10 | `Carleman.Physical.exponential_recurrence` | PASS：有限步 exp 增量望远镜，覆盖 0 至 N。 |
| 11 | `Carleman.Physical.adjoint_rayleigh_bound` | PASS：原终值商加 (N−n)dt*M²。 |
| 12 | `Carleman.Physical.adjoint_reverse_rayleigh` | PASS：零终值单独覆盖，原完整精确指数。 |
| 13 | `Carleman.Physical.filterRayleigh` | PASS：原非零 F 向量商集合的真实 sSup，F=0 单独置零。 |
| 14 | `Carleman.Physical.rayleigh_le_opNorm` | PASS：仅供上确界存在性的有界性证明。 |
| 15 | `Carleman.Physical.filterRayleigh_bot` | PASS：原 Λ_{0}=0 约定。 |
| 16 | `Carleman.Physical.rayleigh_le_filterRayleigh` | PASS：实际有界集合与非零成员资格供应 le_csSup。 |
| 17 | `Carleman.Physical.filterConstant` | PASS：原 exp(TΛ+MT+M²T²/2) 无额外因子。 |
| 18 | `Carleman.Physical.filterConstant_pos` | PASS：所有实参数下严格正，零终值分支合法。 |
| 19 | `Carleman.Physical.filter_reverse` | PASS：真实 Hilbert 伴随方程、任意解与任意终端子空间，原完整 Lemma 7.4。 |

模块对应：1–5 为 [RayleighStep](../../Carleman/Control/RayleighStep.lean)，6–8 为 [PositiveResolvent](../../Carleman/Control/PositiveResolvent.lean)，9–12 为 [ReverseIteration](../../Carleman/Control/ReverseIteration.lean)，13–19 为 [FilterReverse](../../Carleman/Control/FilterReverse.lean)。

## 固定版本、构建与依赖

已读取根 AGENTS、PROJECT_OPERATIONS、state 证据协议及相关 MATH_SPEC。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。检查已验收基线至固定提交的 diff：旧数学模块和原稿未改；数学新增仅本次四模块及 root 导入。根 `Carleman.lean` 显式导入全部四模块。基线的完整原 Lemma 7.1 有 [T024 独立验收](T024-local-acceptance.md)；本次另外直接阅读并核对 `FiniteResolvent`、`PhysicalSolutions`、`PhysicalEquations`、`TimeGrid` 的实际接口和所用证明。

`/tmp/carleman-filter-full.log` 记录 `Build completed successfully (3471 jobs).` 及 `Axiom audit passed for all 3287 Carleman declarations.`。本次读取的 `.ci/axioms.txt` 为 934321 字节，SHA256 为 `881be53c03d27f95b2a111e6ab6eb0cd9c07f39dd1027ba4930964e96372dba2`。19/19 名称、顺序与固定 C041/T025 清单和 `/tmp/carleman-filter-declarations.json` 一致；每项均有实际类型与递归公理输出。`filterConstant` 两个纯实数声明没有隐式参数，因此实际 `#check @...` 输出无需显示 @；其类型已直接读过。

固定 `tools/CheckAxioms.lean` 同时显式登记这 19 项，并遍历包括私有常量在内的全部 Carleman 声明，递归 `collectAxioms`，拒绝三项标准基础公理之外的任何依赖。没有 `sorryAx` 或新增数学公理。主要证明依赖实际有限维线性代数、内积、实指数、条件完备上确界及二次判别式；不以 Carleman 目标估计或后续控制结论作输入。

正式证据已完成：实际读取 [main CI 39140648544 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39140648544/attempts/1) 的下载产物 `/tmp/carleman-filter-main-ci/result.json`，确认 `status=PASS`，`checked_sha=source_head_sha=12d18c9c6548cc70165ad9e4c01314f4438dc5f1`，target 为 `Carleman`，`finished_at=2026-10-18T15:31:48.168756+00:00`。工具链为 Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原始 result 文件 SHA256 为 `8d3e976bbcefd3546e08b90634570b7c95e37a3224fb609fc9f75d5394c6dab3`。

同次下载的 `/tmp/carleman-filter-main-axioms/axioms.txt` 为 934321 字节，SHA256 为 `881be53c03d27f95b2a111e6ab6eb0cd9c07f39dd1027ba4930964e96372dba2`，与本机锁定审查产物逐字节一致。已再次对正式产物逐名核验 19 项实际类型和全部递归公理集合，均仅三项标准基础公理，结尾确认 3287 项审计通过。正式结论绑定这些同 SHA 远端产物，不将本机日志或后续工作树状态冒充远端证据。

## 验收边界

原命题保真、19 项声明语义、递归公理及同 SHA 真实 main CI 均为 PASS，没有数学待修复项。可将 C041/P016 升为 REVIEWED/PAPER，`extra_hypotheses=[]`，绑定本次 19 项声明版本、构建证据与本报告。

本报告覆盖原算子层 Lemma 7.4；不宣称具体 FEM/FD 实例、Theorem 7.5 滤波观测、后续控制或收敛结果已经完成。只写本报告，未修改数学代码、root 导入、台账、覆盖表或论文，未 commit/push。
