# T024 — 原 Lemma 7.1 独立本机验收

- checked_sha: `1aa9b1f253dd759ccc18d92d151aa7c81646f51c`
- base_commit: `8706e95e3a24b09fe6e2675a0c72c827ba9a93f3`
- reviewed_at: `2026-10-18T15:23:21+00:00`（UTC）
- reviewer: 独立数学验收 Agent `/root/accept_spatial_lemma`
- targets: C040 / P013，原 Lemma 7.1 `lem:physicalduality`
- result: **PASS**
- axiom_check: **PASS**（31 项及同 SHA 远端 3265 项递归审计）
- extra_hypotheses: `[]`（相对于原 Section 7 的算子数据）

独立读取固定提交的六个 Control 模块，核对 31 项实际声明、证明体及关键 mathlib 定义；源码均以 `git show <checked_sha>:<path>` 获取。对照 `paper/main.tex:1713–1821`，包括原 Section 7 数据、`eq:forward`、`eq:adjoint`、原 Lemma 7.1 三条结论及证明；没有以执行者分析文档的结论替代检查。沿用并核查本次仍有效的根 AGENTS、PROJECT_OPERATIONS、MATH_SPEC 和状态证据协议。

## 原命题及语义结论

`Carleman.Physical.physical_duality_lemma` 的输出覆盖原引理完整内容：任意初值和任意 N 步控制的前向系统存在唯一解，任意终值的真实伴随系统存在唯一解；所有伴随解满足原 `exp(2M(t_ell−t_j))` 界；所有前向解满足统一 C(T,M) 控制 L² 能量界；所有解满足观察在 `p^(n−1)` 的精确物理对偶恒等式。没有发现数学缺口或额外前提。同 SHA 的 CI 和公理产物已核实，C040/P013 可提升为 `REVIEWED/PAPER`，由主任务把 31 项声明、声明版本、构建证据及本报告一并绑定本次 SHA。

本次仅验收原 Section 7 算子层的 Lemma 7.1。具体 FEM/FD 的 X_h、A_h、V_h、B_h 及其对原势系数的实现和范数性质，仍由对应 realization 任务负责；本报告不宣称这些实例、后续可观测性、控制结论或收敛结果已经完成。

## 原假设、物理节点和量词

最终前提是原有限维实 Hilbert 状态空间 X_h、实 Hilbert 控制空间 U_h、非负自伴刚度 A_h、逐步自伴势 V_h^n 且 `‖V_h^n‖≤M`、`‖B_h‖≤1`、`M≥0`、正步长及 `dt*M≤1/2`。这些正是 Section 7 的算子数据及原引理小性条件。U 不要求有限维；X 的完备性由有限维得到。A、V 被表示为连续线性算子不增加限制，因为 X 有限维；B 的原范数界本身已经给出有界性。没有要求 A 的严格正下界、统一算子范数、势非负、各步势交换、固定空间维数或额外网格条件。

`TimeGrid` 在这里只提供正整数 N、正 dt、`period=N*dt`；状态明确取 `Fin (N+1)→X`，控制与势明确取 `Fin N`。`i.castSucc` 表示物理 n−1，`i.succ` 表示物理 n，`Fin.last N` 是终端 N；本批证明没有调用周期 next/prev 或把首末状态识别。初值和终值分别由独立条件指定。N>0 的实现覆盖原 N≥2，同时允许 N=1，是加强适用范围。`g.period=T` 保证原 `dt=T/N`；对非正 T 不存在这样的正网格，未削弱原 T>0 情形。

最终首先固定 T、M 并选

\[
C(T,M)=e^{2MT}(1+\sqrt T)>0,
\]

然后才全称量化 X、U、网格、A、势族、B、初值、终值、所有控制和所有解。C 不依赖 h、dt、N、空间维数、A 的算子范数或具体状态。原文在本节明确允许依赖 T；不存在把此处 C(T,M) 冒作前文的 T 一致常数。前向结论写为对每个 n 的同一上界，与有限节点上的 max 上界等价。

## 证明链实查

### 单步可逆性和原指数

`stiffness_potential_lower` 从 A 非负与 `‖Vx‖≤M‖x‖`、真实内积 Cauchy–Schwarz 得到 `⟨(A+V)x,x⟩≥−M‖x‖²`；最终入口通过实际 V 的算子范数得到这个逐向量条件。没有输入一步逆界。`step_norm_lower` 用同一内积和范数推导
`(1−dt*M)‖x‖≤‖(Id+dt*L)x‖`，先分离 x=0 情形。`one_sub_mul_exp_ge_one` 从 `exp(2r)≥1+2r` 与 `0≤r≤1/2` 得到 `(1−r)exp(2r)≥1`；这给出准确的 `exp(2dt*M)` 单步逆控制。

`step_bijective` 用上述正下界证明核为零，再用有限维线性自映射的单射蕴含满射；无无限维满射推断。`existsUnique_forward` 通过 `Fin.induction` 逐步施加真实逆映射；`existsUnique_adjoint` 通过 `Fin.reverseInduction` 从终端施加同一逆映射，两者均证明任意竞争解等于构造解，包含所有 N+1 物理节点。

`adjoint_energy` 建立 `exp(2dt*M*n)‖p^n‖` 的单调性，对任意 `0≤j≤ell≤N` 应用，然后精确抵消指数，得到 `exp(2M(ell*dt−j*dt))`；未把它替换为较弱的仅终端 e^(2MT) 界。

### 前向控制 L² 能量

`forward_energy` 从真实前向方程与单步逆控制得到 `‖y^(i+1)‖≤exp(2dt*M)(‖y^i‖+dt‖u^(i+1)‖)`，其中 B 的原收缩性实际用于 `‖Bu‖≤‖u‖`。`forward_recurrence_bound` 使用带指数的反单调量和真实 partial sum 得到完整 `dt Σ‖u‖` 预算，并保留 e^(2MT) 的唯一总增长系数。

`controlNorm dt u = sqrt(dt Σ_{i:Fin N} ‖u_i‖²)` 是原 N 个控制步的 ℓ²_dt 范数。`time_l1_le_l2` 对 N 项有限和使用 Cauchy–Schwarz，随后在非负条件下平方/开方，得到准确的 `dt Σ‖u‖≤sqrt(Ndt) controlNorm`。最后才用非负性合并为上面的 C(T,M)。没有错计 N+1 个控制值、无额外 dt^(-1/2) 或维数因子，也未用假定的能量界替代递推证明。

### 真实伴随与精确对偶

中间 `Forward`、`Adjoint` 是乘以 dt 后的算子方程；其中 `Adjoint` 暂表示 `step(L_i)p^i=p^(i+1)`。最终 `AdjointEquation` 明确写真实 Hilbert 伴随 `(L i).adjoint`，不是用命名为 adjoint 的任意算子替代。`adjoint_equation_iff` 在实际 `L=A+V` 的对称性下调用 mathlib `IsSymmetric.clm_adjoint_eq`，严格识别 L*=L，再用 `dt≠0` 的 `step_equation_iff` 恢复原除以 dt 的方程；`forward_equation_iff` 同样保留原方程。最终存在唯一性和全部估计均回到这两个真实方程。

`duality_increment` 将实际前向方程与 `p i.castSucc` 配对，并用同一步 L_i 的对称性和实际反向方程，得到
`⟨y^(i+1),p^(i+1)⟩−⟨y^i,p^i⟩ = dt⟨f^(i+1),p^i⟩`。
`physical_duality` 只对这 N 个增量作普通有限望远镜求和，留下 0 与 N 的两个端点。`control_duality` 调用真实 `B.adjoint_inner_right`，转为 U 内积 `⟨u^(i+1),B* p^i⟩`。符号、物理时间位置、内积空间和 dt 因子均与 `eq:trueD` 完全一致；无周期边界消去或改用 p^n。

## 31 项声明逐项对应

下表声明均位于本批六模块，已逐名与名单及实际类型核对。本层纯算子/标量辅助前提只在相应辅助定理出现，最终入口由原数据内部供应。

| # | 显式声明 | 对应与结论 |
| --- | --- | --- |
| 1 | `Carleman.Physical.step` | 原 `Id+dt*L` 线性算子；PASS。 |
| 2 | `Carleman.Physical.step_apply` | 实际向量表达式；PASS。 |
| 3 | `Carleman.Physical.one_sub_mul_exp_ge_one` | 原小性区间上的倒数—指数比较；PASS。 |
| 4 | `Carleman.Physical.step_norm_lower` | 从真实二次型下界推导范数下界；PASS。 |
| 5 | `Carleman.Physical.step_inverse_bound` | 原 `exp(2dt*M)` 逐向量逆控制；PASS。 |
| 6 | `Carleman.Physical.step_bijective` | 正下界及有限维性推出真实单步双射；PASS。 |
| 7 | `Carleman.Physical.stiffness_potential_lower` | 原非负 A 与范数有界 V 供应 −M 下界；PASS。 |
| 8 | `Carleman.Physical.Forward` | N+1 节点、N 步的真实乘 dt 前向方程；PASS。 |
| 9 | `Carleman.Physical.Adjoint` | N+1 节点的反向 L 递推；最终由自伴性识别真实伴随；PASS。 |
| 10 | `Carleman.Physical.existsUnique_forward` | 任意初值/载荷的完整节点存在唯一性；PASS。 |
| 11 | `Carleman.Physical.existsUnique_adjoint` | 任意终值的完整节点存在唯一性；PASS。 |
| 12 | `Carleman.Physical.duality_increment` | 原逐步配对式，观察位置 i.castSucc；PASS。 |
| 13 | `Carleman.Physical.physical_duality` | 普通有限望远镜和保留实际首末端点；PASS。 |
| 14 | `Carleman.Physical.control_duality` | 实际 B 的 Hilbert 伴随转为控制空间配对；PASS。 |
| 15 | `Carleman.Physical.adjoint_energy` | 原每个 j≤ell 的准确反向指数界；PASS。 |
| 16 | `Carleman.Physical.partialSum` | N 个 forcing 值在物理时刻 n 之前的和；PASS。 |
| 17 | `Carleman.Physical.partialSum_zero` | 初端零 forcing 预算；PASS。 |
| 18 | `Carleman.Physical.partialSum_succ` | 准确增加当前控制步，不遗漏末步；PASS。 |
| 19 | `Carleman.Physical.partialSum_le_sum` | 非负 forcing 的完整预算上界；PASS。 |
| 20 | `Carleman.Physical.forward_recurrence_bound` | 从实际标量一步递推证明 e^(rN) 总预算；PASS。 |
| 21 | `Carleman.Physical.controlNorm` | 原 N 步的真实 ℓ²_dt 控制范数；PASS。 |
| 22 | `Carleman.Physical.time_l1_le_l2` | 原 sqrt(T) 的 ℓ¹—ℓ² 比较；PASS。 |
| 23 | `Carleman.Physical.energyConstant` | 明示 C(T,M)，不含离散化参数；PASS。 |
| 24 | `Carleman.Physical.energyConstant_pos` | 统一常数严格正；PASS。 |
| 25 | `Carleman.Physical.forward_energy` | 原前向所有节点控制 L² 能量估计；PASS。 |
| 26 | `Carleman.Physical.step_equation_iff` | dt≠0 时与原除以 dt 方程双向等价；PASS。 |
| 27 | `Carleman.Physical.ForwardEquation` | 原 `eq:forward`，全物理步；PASS。 |
| 28 | `Carleman.Physical.AdjointEquation` | 原 `eq:adjoint`，保留实际 `.adjoint`；PASS。 |
| 29 | `Carleman.Physical.forward_equation_iff` | 原前向方程与已证明递推适定性接口相连；PASS。 |
| 30 | `Carleman.Physical.adjoint_equation_iff` | 从原自伴性识别真实反向伴随递推；PASS。 |
| 31 | `Carleman.Physical.physical_duality_lemma` | 原三结论及两侧存在唯一性的完整统一组合；PASS。 |

## 版本、构建与公理证据

本机日志 `/tmp/carleman-physical-full.log` 包含 `Build completed successfully (3467 jobs).`，以及全部 31 项展开后的类型/公理输出。实际读取的 `.ci/axioms.txt` SHA-256 为 `0e519a9cfe5cc7b745f140f9a163e2ff3adc5ee6ea13f1ba8751cce913762e2c`，与本次固定产物一致。31/31 项均有 `#check @...` 类型和 `#print axioms`，各项仅依赖 `propext, Classical.choice, Quot.sound`；产物结尾为 `Axiom audit passed for all 3265 Carleman declarations.`。

固定提交的审计器遍历包含私有声明的全部 Carleman 常量，递归 `collectAxioms` 并拒绝除上述三项以外的公理；不是只扫描源码里的 sorry 字样。根 `Carleman.lean` 显式导入六模块。Lean 固定 4.35.0，mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`。本批主要依赖有限维线性代数、真实 Hilbert 伴随和有限求和；不把较早的 Carleman 误差或控制结论作为本引理的假设。

远端门槛已完成：独立通过 GitHub connector 读取 [main CI 39139922166 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39139922166/attempts/1)，确认 `event=push`、`head_branch=main`、`head_sha=1aa9b1f253dd759ccc18d92d151aa7c81646f51c`、`status=completed`、`conclusion=success`。`lean`（117712048414）、`state-check`（117712048701）、`dashboard / snapshot`（117712603965）三项均 success；实际 Lean 构建和两份证据上传步骤均成功。

独立查询该运行的 artifacts，`lean-ci-result` 为 12141068134，`lean-declaration-evidence` 为 12140938654，二者的 `workflow_run.head_sha` 均为本次 SHA。随后读取实际下载的 `/tmp/carleman-physical-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=1aa9b1f253dd759ccc18d92d151aa7c81646f51c`，target 为 Carleman，完成时间 `2026-10-18T15:20:32.980527+00:00`，Lean/mathlib pin 与固定源码一致。该原始 result 的 SHA-256 为 `f30193f4755a7c7c6e6d77a4048c1a6b1815c156cdf2268499352e7091dcb5f9`。

实际远端公理产物 `/tmp/carleman-physical-main-axioms/axioms.txt` 为 924943 字节，SHA-256 为 `0e519a9cfe5cc7b745f140f9a163e2ff3adc5ee6ea13f1ba8751cce913762e2c`，与上述本机锁定产物逐字节一致。再次逐名核查 31 项类型/公理输出，全部仅三项标准基础公理，结尾仍为 3265 声明审计通过。正式结论使用这些同 SHA 远端产物，不把后续开发的本机文件或新模块纳入本次验收。

本报告未修改数学代码、论文、根导入、台账或覆盖表，未 commit/push。
