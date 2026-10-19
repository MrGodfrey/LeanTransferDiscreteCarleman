# T104 / C120 独立本机验收

- `checked_sha`: `29ebd0b76cccb70d6da4499eaa09d35cab2895ff`
- `base_commit`: `23d19fb4276d47fb788d7040ae156f3e67e46ec8`
- `reviewed_at`: `2026-10-19T03:26:48+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全部 Cartesian 节点状态、原重构和原对角测试的完整弱 H¹ 超逼近，即 `eq:testsuper`。观察接口及完整 FD/P012 组装仍待，原文保持 **14/26**。

独立读取固定提交三模块全部证明、五项完整展开类型及关键依赖，对照固定 `paper/main.tex:419–464` 的数值量词、N4 和 `paper/main.tex:2878–2889` 的 Appendix B Step 3。另核对原允许权及 `eq:graphnorms`。执行者规格和 CI 没有替代数学核查；后续 T105 工作树及变化中的 `.ci/axioms.txt` 不属于本次证据。

## 全部五项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付 JSON、固定 C120 台账一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `allowed_prescribed_nodal_weak_norms` | `Weights/PrescribedNodalWeakResidual.lean:14` | PASS；用真实节点唯一性将既有弱残差中的存在代表替换为指定数据，保留实际零阶及完整弱梯度平方界。 |
| 2 | `WeakSobolevJet.weightedNorm_neg` | `Weights/PrescribedNodalSuperapproximation.lean:13` | PASS；全部阶次的线性字段在取负下变号，真实乘子半范数不变，故完整加权范数不变。 |
| 3 | `heat_nodal_residual_norm_bound` | `Weights/PrescribedNodalSuperapproximation.lean:23` | PASS；实际热 H¹ 范数平方身份及 Dq≤1 给 √(2C)Dq 倍原状态范数，无除以 D、q 或状态范数。 |
| 4 | `allowed_prescribed_nodal_superapproximation` | `Weights/PrescribedNodalSuperapproximation.lean:57` | PASS；显式取负恢复论文 I(σ²u)−σ²u 方向，并用 q(t)≤qmax 得原尺度。 |
| 5 | `allowed_weight_cartesian_test_superapproximation` | `Spatial/AllowedCartesianTestSuperapproximation.lean:16` | PASS；真实 Kuhn 形状、完整 H¹₀ 重构、指定节点数据及原 Tσ 身份全部内部清偿，统一 ε/C 先于全部网格、时间权和状态。 |

## 指定数据与真实弱残差的对齐

第1项调用的 `allowedSquaredWeight_full_weak_residual` 返回实际弱 H¹ jet e 和某个零边界节点代表 g，满足 u.value=nodalLp(g)，且 e.value 几乎处处等于 σ²I(g)−I(σ²g)。本批没有直接将 g 当作输入的指定数据 f。它使用输入的 u.value=nodalLp(f)，先得到 nodalLp(g)=nodalLp(f)，再调用 T103 的 `nodalLp_multiplier_congr`，严格得到 I(σ²g)=I(σ²f)。

该唯一性依赖的证明已经读取：从原域 L² 类相等经 `cell_measure_le_domain` 限制到真实单元；在单元上将 nodalFunction 识别为实际局部仿射函数；再由连续性及单纯形属于其内部闭包，将几乎处处相等提升到闭单元所有点，最后在全部顶点使用再现性。包括边界顶点，没有对任意 L² 等价类取点值，也没有假设指定 f 在域内与 g 处处相等。

`nodalProductResidual_lp` 使用实际有界乘子 map、原 nodalLp 的几乎处处身份以及 Lp.ext，将点函数残差转为真实 L² 类等式。`allowedSquaredWeight_multiplier_value` 严格识别平方权为 σ²；`allowed_weight_sq_integral` 和 `allowed_inverse_weight_sq_integral` 将已有积分界转换为真正乘子半范数。逆权为同时改变 (τ,η) 至 (−τ,−η)，其值确为 σ⁻¹，未只翻转其中一个参数。

因此第1项保留的是

\[
\|\sigma^{-1}e\|_2^2\le C D^4 E,
\qquad \|\sigma^{-1}\nabla e\|_2^2\le C D^2 E,
\qquad E=q^4\|\sigma u\|_2^2+q^2\|\sigma\nabla u\|_2^2.
\]

这里 D 是真实最大单元直径，所有字段为原 weak jet 的实际 L² 字段。底层 `FullWeakNodalResidual`、`NodalResidualSobolev` 和 `FullNodalResidual` 已直接读取：实际紧支 Lipschitz 残差给完整分布弱 H¹，完整梯度几乎处处等于真实 fderiv 的 `derivativeOneFiber`；全状态代表的梯度通过弱唯一性与原状态字段对齐。代表存在性所用状态相关 Lipschitz 界只用于成员证明，不进入上述统一估计常数。

`WeakSobolevJet` 的定义要求每个坐标方向的分布弱导数身份，`DerivativeFiber d 1` 含全部一阶坐标，范数为其 Euclidean 范数。故这里没有把任意形式字段、单个方向或逐单元跳跃导数冒充完整弱梯度。

## 原范数、吸收和残差符号

第3项直接使用已核对的真实身份

\[
\mathcal N_\sigma(u)^2=q^2\|\sigma u\|_2^2+\|\sigma\nabla u\|_2^2,
\qquad E=q^2\mathcal N_\sigma(u)^2.
\]

由 D,q≥0 和 Dq≤1，先用 (Dq)²≤1 控制零阶项额外的 q²，再与梯度平方界相加，得到 Nξ(e)²≤2C(Dq Nσ(u))²。取平方根时明确提供全部非负性，因而结论为 √(2C)Dq Nσ(u)。没有除以可能为零的量；D=0、q=0 或零状态的代数辅助结论均合法。应用于原 TimeWeight 时已有 q≥1。

T101 的既有 `nodalProductResidual` 方向为 σ²u−I(σ²u)，与论文相反。本批第4项明确返回 **−e**；value 的线性性和 `neg_sub` 给 I(σ²u)−σ²u，全部弱字段同时变号，再用第2项保留完整范数。此前记录的符号衔接要求已正确落实，不再遗留带符号 jet 被直接等同的问题。

随后只用 q(t)≤w.max，将 Dq(t) 换成 Dqmax。最终 e 是论文指定残差的实际弱 H¹ jet，不是另一个存在的测试函数；原域分布弱导数的唯一性使其梯度代表的选择不改变范数。

## 原 Cartesian 网格、原算子与常数量词

第5项固定 d、原物理域 S、ρ 及闭域 C² 正则性、步长可比常数 κ>0 后，先取得真实形状常数 K、再取得残差常数 C₀，选定

\[
\varepsilon=\frac1{d+1}>0,\qquad C=(d+1)C_0>0.
\]

此后才量化网格起点 o、全部正步长 δ、N、h>0、h/κ≤δⱼ≤h、任意 TimeWeight、τ、t、|η|=1，最后量化全部 `CartesianInteriorIndex N → ℝ` 状态 f。没有附加频谱、支撑、光滑节点值或目标误差前提，C 也不依赖节点数、单元数、状态、q、τ、符号或周期 T。

`hdom : openCoordinateBox o (o+Nδ)=S` 表达网格铺满同一个固定物理 Ω，符合原 Cartesian 实现；不是随网格缩域或新的物理限制。紧闭包的有界性内部给 volume(S)<∞，不要求调用者再提供有限测度证书。ρ 的原光滑性供应所需闭域 C² 正则性。结论对全部实 τ 成立，覆盖原 |τ|≤τ_*；|η|=1 保留两个原符号及其逆权。

T103 实际形状证明已直接读取：固定参考 Kuhn 单纯形的真实内接球半径 r₀>0，经实际仿射逆映射界 κ/h 得物理内接球半径 r₀h/κ；实际直径 D≤(d+1)h，形状常数 (d+1)κ/r₀ 先于网格。最终代码从这些定理取得各实际单元的球，未把形状估计留为额外前提。h q(t)≤ε 给 Dq(t)≤1；论文原 hqmax≤ε 由 q(t)≤qmax 自动蕴含该条件。ε≤1，无遗漏所需的小量约束。d+1 和 r₀ 始终正，证明不除以 d；空节点/空单元情形没有新增非空要求。

输入 u 是原 `cartesianKuhnReconstructionJet`，其 value 恰为同一个原重构 Lp 类。其真实 H¹₀ 图闭包成员及完整 `conformingSpace` 资格由既有实际 Kuhn 零边界重构内部证明。`hf` 使用原 `cartesianInteriorData`，而非另选一个任意节点参数化。最后 `cartesianInteriorData_multiplier` 的真实零延拓乘法身份及 `cartesianKuhnReconstructionLp_eq_nodal` 严格给

\[
I_h(\sigma^2 f^{\rm ext})=R_h(T_\sigma f),\qquad
(T_\sigma f)_a=\sigma(x_a)^2f_a.
\]

包括所有闭单元边界顶点。没有将节点插值 I_h(σ²R_hf) 与点态乘积 σ²R_hf 本身混同。onSubdomain 只沿 hdom 的域等式传输相同实际乘子。将 D≤(d+1)h 代入即可得到原结论

\[
\mathcal N_{\sigma^{-1},\Omega}(R_hT_\sigma f-\sigma^2R_hf)
\le C hq_{\max}\mathcal N_{\sigma,\Omega}(R_hf).
\]

这是 Appendix B Step 3 的空间估计，在每个固定时刻成立，不涉及时间方向的限制；两权符号完整保留。没有隐藏的 T、网格基数或任意有限维范数等价损失。它本身不声称完成观察接口及全部 FD 假设的最终组装。

## 固定版本、依赖及公理

三模块的 Carleman 导入闭包共335模块，332旧模块与 base 完全不变，新增恰为本批三模块。又逐模块比较关键已验收版本：C080 `FullNodalWeakNorms` 的180模块闭包相对 `7d5b98f23e305b99c69543c953bb545fefc42cb7` 不变；C081 `HeatNormSquare` 的31模块闭包相对 `9c354128a5ebd5e3eeb36f3e15e5fa9ae4a27158` 不变；C117 `AllowedCartesianDiagonalTest` 的306模块闭包相对 `88306d8177aee83bfc8c6011f9d964a273e042b9` 不变；C119 `CartesianKuhnShape` 和 `NodalMultiplierUniqueness` 的197、184模块闭包相对 base 不变。旧 declaration_version 没有被工作区或后续实现偷换。

原稿及既有治理协议未由本批改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。固定 Lean pin 为4.35.0，mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。root 显式导入三模块，`tools/CheckAxioms.lean` 包含五项完整类型及公理输出，并递归检查全部 Carleman 声明。

实际读取固定 `/tmp/carleman-fd-test-super-full.log`：`Build completed successfully (3815 jobs).`，末尾为 `Axiom audit passed for all 6299 Carleman declarations.`。固定本机产物 `/tmp/carleman-fd-test-super-local-axioms.txt` 为 **1,889,692 bytes**，SHA256 **`67c65a22255a76349ad9d77b9438f444bd5994a4224b7582d1309f8d08976989`**。五项完整类型已逐项核对；全部2125条显式公理记录中2117非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无 sorryAx。

## 实际同 SHA 远端证据

本验收 Agent 自行经 GitHub connector 查询 [main CI 39194196544 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39194196544/attempts/1)。run 为 main/push、completed/success，head SHA 精确等于本报告 fixed SHA。实际三项 job 均 completed/success：state-check **117873274151**、lean **117873274269**、dashboard / snapshot **117874186698**；实际步骤均成功。

独立读取同 run artifact 元数据：`lean-ci-result` **12161118069**，`lean-declaration-evidence` **12160978919**，两者 workflow_run.head_sha 均为固定 SHA。并自行通过 `gh run download 39194196544` 下载两份原始产物至约定目录。

实际 `/tmp/carleman-fd-test-super-main-ci/result.json` 为 PASS，`checked_sha=source_head_sha=29ebd0b76cccb70d6da4499eaa09d35cab2895ff`，targets为Carleman，`finished_at=2026-10-19T03:22:47.680464+00:00`，ci_url与上述 run/attempt 一致；Lean4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述固定pin。

独立逐字节比较 `/tmp/carleman-fd-test-super-main-axioms/axioms.txt` 与固定本机副本，完全一致：**1,889,692 bytes**，SHA256 **`67c65a22255a76349ad9d77b9438f444bd5994a4224b7582d1309f8d08976989`**。因此全部五项远端展开类型、公理记录及末行 **6299项全声明递归审计PASS** 与本机已审证据完全一致；未混用其他 SHA 或后续 `.ci` 文件。

## 验收决定

**C120：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 五项固定声明未发现需要修复的数学缺陷。原指定 Tσ/R_h 的身份、完整节点状态、真实弱残差及全部梯度、论文残差符号、逆权、原范数和统一常数量词均已独立核对；同 SHA 三项正式 CI 和自行下载的原始公理证据已核实。

本结论完成原 FD 的 `eq:testsuper`，不因此提升完整 FD/P012 或 PAPER 覆盖，原文保持 **14/26**。本次仅写此报告，没有修改实现、台账、原稿或root导入，没有commit/push。
