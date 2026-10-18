# T020 — Lemma 4.1 独立本机验收

- checked_sha: `a315bdc449c58a705a982f0d009f1dde24d6af66`
- reviewed_at: `2026-10-18T14:34:14+00:00`
- reviewer: 独立验收 Agent `/root/accept_spatial_lemma`
- targets: C008 / P009，完整原 Lemma 4.1
- result: **PASS**（36 个声明及其组合语义；下述独立依赖验收门槛已满足）
- axiom_check: **PASS**
- extra_hypotheses: `[]`（相对于 Lemma 4.1 的原假设；中间组合定理的参数已在原假设入口清偿）

本报告检查固定提交的源码、声明类型与证明体；源码均由 `git show <checked_sha>:<path>` 读取，不以正在开发的工作树或执行者自检说明代替。对照原稿 `paper/main.tex:1122–1283`，并回查 294–387、392–406、419–465 的空间、权族、A1–A3、质量接口及 N1/N3/N4。没有修改原稿、Lean 源码、根导入、状态台账或覆盖表。

## 验收结论与依赖门槛

八模块完整证明了原稿的两条结论：

\[
\mathcal N_{\sigma,\delta t}(u-R_hu_h)
\le K(a_E+\eta_A)\|\sigma g\|_{\ell^2_{\delta t}(H)},\qquad
\|\sigma(u-R_hu_h)\|_{\ell^2_{\delta t}(H)}
\le K(a_0+a_E^2+\eta_A)\|\sigma g\|_{\ell^2_{\delta t}(H)}.
\]

完整入口是 `Carleman.OriginalForm.spatial_uniform`；`EnergyEstimate` 还给出真实重构状态的统一稳定性。未发现本批声明的数学或接口缺陷。同一 SHA 的 Section 3 和 C038/C039 独立依赖验收也已通过，C008/P009 可以提升到 `REVIEWED/PAPER`；主任务须将本报告、36 项声明、同 SHA 构建及时间一并登记。验收中分别检查了以下依赖门槛：

| 依赖 | 本报告检查的实际使用 | 独立验收要求 |
| --- | --- | --- |
| T019 / C037（含其 C036 供应依赖），原 Lemmas 3.1、3.3、3.4、Theorem 3.5 | 原入口直接调用 `a.section3`；能量层使用 `H.euler`、`H.form_bound`、`H.form_coercive`；对偶再次使用 `H.euler` 的 opposite/inverse 实例 | 同 SHA 的 Section 3 独立报告确认 A1–A3 供应、完整原算子域、真实图范数及统一阈值；本引理并未将 `H` 留作原入口前提 |
| C038 | `spatial_error_equation`、`spatial_weighted_duality`、`spatial_continuous_test` 保留真实质量/刚度关系；有限维离散辅助问题存在唯一性仍由 `existsUnique_auxiliaryEuler` 负责 | 同 SHA 的辅助独立验收；存在唯一性是原稿引理前的背景，不以本引理中“对任意已解方程的解”取代该独立结果 |
| C039 | `spatial_cea`、两向 N4 时间下界、`squared_weight_test_uniform`、`nodal_approximation_bound` 及真实 N 范数半范数实现 | 同 SHA 的辅助独立验收；本报告另行核查这些结果的实参和阈值确由原假设构造 |

这些是证明依赖的验收条件，不是向数学定理新增的假设。Theorem 4.2、Section 5、原 Theorem 2.1 不在本次覆盖范围。

C038/C039 门槛已由 [T020 基础层独立报告](T020-foundations-local-acceptance.md) 在本次同 SHA 通过：52 项声明分别为 AUXILIARY PASS，公理检查 PASS，验收时间 `2026-10-18T14:30:45+00:00`。本报告已读取其实际结论并交叉核查调用关系。

Section 3 门槛已由 [T019 独立报告](T019-local-acceptance.md) 在本次同 SHA 通过：C037 的 61 项及 P004/P006/P007/P008 原文结论为 PASS，公理检查 PASS，验收时间 `2026-10-18T14:31:08Z`。本报告读取了其原域/原算子、a.e. 图代表、真实 N/R 和常数量词的独立核查结论，与本引理实际使用的接口一致。

## 原假设与实际对象

`OriginalForm` 用原闭、稠密 Sobolev 子空间和有界对称强制双线性型构造同一个关联算子；`hD` 与 `hell` 分别是 A1 的域嵌入和原椭圆正则性估计。`AllowedFamily` 的 `data` 是 A2 的乘法/逆乘法保域、交换子界及 A3 下界，`upper` 是 A3 上界。没有新图估计、插值估计、空间误差估计、离散稳定性或最终结论作为原入口假设。`a.operator_test` 实际供给连续变分测试等式，`bilinearForm_apply` 识别同一原形式。

`Reconstruction` 只有时间无关的 R、J 和质量伴随等式；Q 定义为 RJ，G 定义为 JR（含 V→H 嵌入）。实际离散方程始终是 `D_s z + A z + μ • r.G z = r.J f`，`μ=(Lq)^(2m)`。N1 的 `b` 为时间无关双线性形式，`hA` 保留完整刚度恒等式，`hdef` 保留 `ηA Nσ(Rz) Nσ⁻¹(Rv)`。误差方程保留两处缺陷项，对偶恒等式保留 `b(z,JY)`；未设置 ηA=0，也未使用 Q²=Q、G=Id、正交重构或节点测试算子交换。

估计对任意满足方程的全状态成立，因而不需要在估计接口再次要求 N1 的有限维、R 单射、A 自伴非负或重构范数等价。这是删除未用前提后的加强，不能误读为这些原假设的存在唯一性已被本批声明单独证明。上述条件在原离散适定性依赖中有其独立用途。Lemma 4.1 的载荷是任意 H 值 g，不使用 N2 的 lift、右逆或观测假设；省去它们没有改变目标估计。

`WeightedApproximation` 恰接收 N3 在 `[0,T]` 的两条逐时原域估计，没有把序列误差结论塞入字段。`WeightedTest` 接收时间无关 X 上的实际时变线性测试算子、端点相容、二次配对的实际导数、自伴、非负、N4 时间导数界及 `Csuper*h*qmax` 的原 superapproximation。原 N4 的可微正定算子族给出这些条件；仅用非负和二次配对导数是弱化未用条件。未要求额外的测试范数下界或稳定性结论。`superapprox` 对保域证明的全称量化只消除了证明参数选择，数学上仍是同一 σ²Rz。

能量范数 `energyNorm` 是实际 `δt Σ_n Nσ,n(v_n)²` 的平方根，空间 `N` 是 m 阶全部弱导数场的带 q 权平方和；`regularityNorm` 是实际 `Σ_{j=0}^{2m} ‖q^(2m-j)σ D^j u‖_{ℓ²δt}`，不是点态 R 的 ℓ²范数，也不是 H 诱导范数。N3 到序列 R 的提升实际调用 Minkowski 型 `nodal_approximation_bound`。域截断通过弱导数唯一性识别原 u 的 m 阶 jet；出现的 m+1、m+2 仅是固定阶数常数。L² 是同一真实 `Lp` 空间中乘权后 `g.l2Norm`。

本引理的 u、Y 是有限周期节点上的 D(A) 值序列，与原空间连续 Euler 问题一致；没有把连续时间 Sobolev 轨迹要求成处处 D(A) 值。被调用的 Section 3 连续图结果以 a.e. 域代表工作，`domainValue` 与原轨迹 a.e. 相等，弱导数和端点 H 迹由独立桥保留。本引理只取 Section 3 的 Euler 结论，不对 a.e. 轨迹增加新的点值/正规性要求。

## 能量、对偶与统一性检查

`energy_uniform_of_section3` 取 `B=18*Ctime+1`，由 `H.form_coercive B` 供应真实 qσ 质量余量，并调用两方向 N4 时间下界。`squared_weight_signed_uniform` 用两次原 σ/σ⁻¹ 共轭估计证明 σ² 测试稳定性，没有调用 |2τ| 范围的数值 N3/N4 或把新指数认作允许权。随后取 `ε=Csuper*mesh*w.max`，由 `spatial_smallness_thresholds` 证明 `ε≤1` 及 `Cf*ε+ηA*(ε+CM)≤c/2`，实际交给 `spatial_cea` 吸收。`energy_rates_of_cea` 再使用 N3、ηA≤1、aE≤1、`e=η-Re_h` 与 `Rz=Qu+Re_h`；`energy_estimate_of_cea` 用真实 Euler R 界换成源范数。

`l2_estimate_of_energy` 先令 `err=u-Rz`、`k=σ(σ err)`，从 `(hd k).1` 取得真实 D(A) 值唯一对偶解 Y。`hd` 由 `H.euler g s.opposite ... (-τ) (!e)` 供给，`signed_neg` 保证 profile 正确；|−τ|=|τ|，没有扩大允许指数区间。逆权作用于 k 后严格等于 σ err。`spatial_weighted_duality` 给实际 L² 平方左端和完整三项：

1. `(D_s u,Y-QY)` 用逆权 N3 L² 界及原向 Euler 时间差分界，系数为 a0。
2. `a_μ(e,Y-QY)` 用 A3 位移形式界、真实能量误差及逆权 N3，系数为 `aE*(aE+ηA)`。
3. `b(z,JY)` 用完整 N1 缺陷、真实重构状态稳定性及逆权 QY 界，系数为 ηA。

只有三项估计完成后才用 `aE≤1` 化简混合项，取得 `a0+aE²+ηA`；E=0 与 E>0 分开取消 L² 误差因子。未直接假设对偶图界、最终 L² 估计或误差方程。

最终量词为：固定原结构和假设常数后，先 `∃ Lmin δt`，再 `∀ L≥Lmin, ∃ δx ηstar K`，之后才量化 X、R、A、b、网格/周期、方向、q、τ、profile 符号、mesh、近似/缺陷率以及所有载荷和两个解。K、δx、ηstar 可依赖已固定的 L；不能依赖 T、N、δt、qmax、h、X、方向、符号、状态或载荷。`δx≤δnum` 明示；时间阈值缩入 Section 3 与 cell 范围。原 `δt≤1` 在原入口由 Section 3 的 δ≤1、qmax≥1 推得（估计本身实际上不需单列它）。全空间、两时间方向与两类允许权均保留。

## 36 项声明逐项对应

以下名称全部在同 SHA 的 `#check` 与递归公理输出中出现。每一行的“原假设”均指其本层参数；组合层参数最终按上文内部供应。字段声明属于原数据编码，不能按“已证明 N3/N4”计数。

| # | 显式声明 | 核查内容与结论 |
| --- | --- | --- |
| 1 | `Carleman.Section4.energyNorm` | 真实节点 Nm 能量定义；PASS。 |
| 2 | `Carleman.Section4.regularityNorm` | 真实 2m 阶导数场 ℓ² 范数之和；PASS。 |
| 3 | `Carleman.Section4.WeightedApproximation` | 原 N3 两条逐时估计，无序列/最终结论字段；PASS。 |
| 4 | `Carleman.Section4.WeightedApproximation.energy` | 原 `eq:approximation`，完整 D(A)、实际 Q；PASS。 |
| 5 | `Carleman.Section4.WeightedApproximation.l2` | 原 `eq:approximation-l2`，实际 u−RJ u；PASS。 |
| 6 | `Carleman.Section4.nodal_energy_le_regularity` | 从实际 jet 截断和 q≥1 得 Nm≤(m+1)R2m；无 N3 前提；PASS。 |
| 7 | `Carleman.Section4.WeightedApproximation.nodal_energy` | N3 由实际节点提升，系数 aE；PASS。 |
| 8 | `Carleman.Section4.WeightedApproximation.nodal_Q` | Qu=u−(u−Qu) 与三角不等式，系数 m+1+aE；无投影假设；PASS。 |
| 9 | `Carleman.Section4.WeightedApproximation.nodal_l2` | 原 N3 L² 经 Minkowski 提升到 R2m；PASS。 |
| 10 | `Carleman.Section4.regularityNorm_nonneg` | 实际有限和的非负性；PASS。 |
| 11 | `Carleman.Section4.energy_rates_of_cea` | 原 Step 1 的 e 和重构状态率；中间 Céa 参数随后清偿；PASS。 |
| 12 | `Carleman.Section4.WeightedTest` | 原 N4 所需数据，未含强制性或误差结论；PASS。 |
| 13 | `Carleman.Section4.WeightedTest.op` | 实际时变测试线性算子；PASS。 |
| 14 | `Carleman.Section4.WeightedTest.derivative` | 实际配对导数的线性算子数据；PASS。 |
| 15 | `Carleman.Section4.WeightedTest.endpoint` | 原周期端点相容；PASS。 |
| 16 | `Carleman.Section4.WeightedTest.hasDeriv` | 原可微族蕴含的闭区间内导数；PASS。 |
| 17 | `Carleman.Section4.WeightedTest.symmetric` | 原自伴条件，覆盖全部 X；PASS。 |
| 18 | `Carleman.Section4.WeightedTest.nonneg` | 原正定性的所需弱结论；PASS。 |
| 19 | `Carleman.Section4.WeightedTest.time_bound` | 原 `eq:testtime`、实际 qσRH；PASS。 |
| 20 | `Carleman.Section4.WeightedTest.superapprox` | 原 `eq:testsuper`、σ² 与 Csuper*h*qmax；PASS。 |
| 21 | `Carleman.Section4.spatial_smallness_thresholds` | 在数值数据之前选 δx≤δnum、ηstar≤1，证明 c/2 吸收；PASS。 |
| 22 | `Carleman.Section4.EnergyEstimate` | 原能量误差和重构稳定性的输出命题；任意真实解；PASS。 |
| 23 | `Carleman.Section4.energy_estimate_of_cea` | N3/Céa/Euler 实际合成；无替代源标量；PASS。 |
| 24 | `Carleman.Section4.squared_weight_signed_uniform` | 两 profile 符号共用 CM，σ²通过连续乘法而非扩大数值权族；PASS。 |
| 25 | `Carleman.Section4.spatial_time_threshold` | 先于时间/权选择共同正阈值，满足两个 cell 条件；PASS。 |
| 26 | `Carleman.Section4.EnergyUniform` | 统一量词顺序、δx≤δnum、所有 X/方向/符号/解；PASS。 |
| 27 | `Carleman.Section4.energy_uniform_of_section3` | 内部清偿 hform/hcoer/hmul/hsmall，真实 N4 时间控制；PASS。 |
| 28 | `Carleman.OriginalForm.spatial_energy_uniform` | 从 A1 原对象调用 `a.section3`，没有 H 外加参数；PASS。 |
| 29 | `Carleman.Section4.weighted_pairing_bound` | σ/σ⁻¹ 在真实 L² 配对抵消及 Cauchy–Schwarz；PASS。 |
| 30 | `Carleman.Section4.spatial_duality_bound` | 原 `eq:completeidentity` 三项全部保留，各用实际 N3/形式/缺陷界；PASS。 |
| 31 | `Carleman.Section4.L2Estimate` | 原 L² 误差率 a0+aE²+ηA，真实误差与载荷；PASS。 |
| 32 | `Carleman.Section4.duality_rate_coefficient` | 三项估计之后的纯标量率合并；并非独立 Lemma 4.1；PASS。 |
| 33 | `Carleman.Section4.l2_estimate_of_energy` | 构造 opposite Euler 对偶解，逆权图界、三项估计和合法消去；PASS。 |
| 34 | `Carleman.Section4.SpatialUniform` | 原能量及 L² 结论共用同一常数，全量词范围；PASS。 |
| 35 | `Carleman.Section4.spatial_uniform_of_section3` | 正/逆两个实际 Euler 实例与能量结果合成，max 常数统一；PASS。 |
| 36 | `Carleman.OriginalForm.spatial_uniform` | 完整原假设入口及 Lemma 4.1 双估计；所用 Section 3 结果内部取得；PASS。 |

## 固定版本构建与公理证据

独立通过 GitHub connector 读取 [run 39135593975, attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39135593975/attempts/1)：`event=push`、`head_branch=main`、`head_sha=a315bdc449c58a705a982f0d009f1dde24d6af66`，状态 completed/success。`state-check`（117699336129）、`lean`（117699336230）、`dashboard / snapshot`（117700001749）均 success。固定 SHA 的工作流明确 checkout `github.sha`；`tools/lean_ci.sh` 实际执行 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean`，并检查解析出的 mathlib 提交。

原始构建产物 `/tmp/carleman-spatial-main-ci/result.json` 中 checked/source SHA 均为本次 SHA，target 为 Carleman，finished_at 为 `2026-10-18T14:23:13.156876+00:00`。工具链为 Lean 4.35.0；mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定提交中的锁定文件一致。根 `Carleman.lean` 显式导入本批八模块。本次复核使用该精确 CI 构建，没有把新工作树的构建冒充固定提交构建。

`/tmp/carleman-spatial-main-axioms/axioms.txt` 的 SHA-256 为 `4cf5509f91b61e80901ab0f86484133c25cf95cd92f58849a473a01189a98278`。36 项声明的类型和 `#print axioms` 均逐名存在，全部只列出 `propext, Classical.choice, Quot.sound`。审计器遍历所有 private/public 的 Carleman 声明，递归使用 `collectAxioms`，允许名单恰为这三项基础公理；输出结尾为 `Axiom audit passed for all 3080 Carleman declarations.`。因此没有 sorryAx 或未经证明的数学公理依赖。本报告没有把正常基础公理误记为额外数学假设。
