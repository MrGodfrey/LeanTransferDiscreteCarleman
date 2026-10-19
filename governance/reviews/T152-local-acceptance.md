# T152 / C168 独立本机验收：光滑周期盒上的正向热观测估计

- checked_sha / source_sha: `86686ea4d106798727d898bf61abc238812a8cb8`
- mathematical_base: `8e740040ffe3ce75cb89b5868d5998b5ad8cd74c`
- reviewed_at: `2026-10-19T10:43:37+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 本报告覆盖固定八模块、十八项显式声明。C168 可以升级为 REVIEWED 并保持 AUXILIARY；P024 / `prop:continuousCE` 不提升，原文完整结果覆盖仍为 **17/26**。

## 原文与固定审查范围

直接读取固定 Git 源对象中的全部新证明、原始完整展开类型和相关依赖；对照原 `paper/main.tex:2672–2733` 的连续 CE 命题及证明，同时核对 `eq:qclass`（294–299 行）和 `eq:continuousabstract`（374–381 行）。原文先固定观测区，选内球和 Gaussian 权，再从 heatcross 吸收余项并返回原状态。本批完成这些步骤在全时空 C∞、周期、正坐标盒、正向热算子中的实际实现。没有把该范围等同于原命题要求的 C² 时间权、全部弱轨道、一般凸多面体或两种时间方向。

已读取固定 `governance/analysis/T152-smooth-heat-estimate.md`、`governance/MATH_SPEC.md` 的对应段、C168 登记，并依根 AGENTS 和规范执行固定版本独立审查。规格、执行者说明及 CI 均不是数学验收的替代。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。工作树中的 T153 时间反射草稿及动态 `.ci/axioms.txt` 完全排除；元数据提交不替换本报告的证明 SHA。

## 十八项声明逐项结论

路径及行号均指 checked_sha。以下清单与 C168 的 `lean_declarations` 以及固定 declarations.json 顺序一致；所有十八项完整类型均从固定 raw 读出并核对，八模块均由 `Carleman.lean` 导入，十八项均进入 `tools/CheckAxioms.lean`。

| # | 显式声明 | 固定源码位置 | 核对结论 |
|---|---|---|---|
| 1 | `Carleman.exists_heat_absorption_parameters` | `Carleman/Weights/HeatAbsorptionParameters.lean:9` | PASS。m、C 正时实际选 β=min(1,m/(8C))、qc=max(1,4C/m)，保留 β>0、β≤1、qc≥1，且统一控制所有 Q≥qc 的两项余量。 |
| 2 | `Carleman.interiorHeatPotential` | `Carleman/Weights/InteriorHeatPotential.lean:12` | PASS。定义为实际 λ³φ³‖∇ψ‖²(λ‖∇ψ‖²−6)，与同一 heatcross 的空间势精确一致。 |
| 3 | `Carleman.interiorHeatPotential_continuous` | `Carleman/Weights/InteriorHeatPotential.lean:16` | PASS。通过真实 Gaussian 和 ‖∇ψ‖²=4‖x−c‖² 证明连续性，供紧域统一界使用。 |
| 4 | `Carleman.interiorHeatPotential_positive_outside` | `Carleman/Weights/InteriorHeatPotential.lean:23` | PASS。球外真实梯度下界、φ≥κ>0、λ‖∇ψ‖²≥12 推出势≥24λ³κ³r²，所有乘法因子符号正确。 |
| 5 | `Carleman.exists_interior_heat_observation_coefficients` | `Carleman/Weights/InteriorHeatPotential.lean:37` | PASS。由固定有界 S、任意非空开 W⊆S 内部选中心、球和 λ，再供应 a、m、K>0，使 a≤λφ、m≤F+K·1_W 于全部 S 成立。 |
| 6 | `Carleman.interiorHeat_observation_absorption` | `Carleman/Weights/InteriorHeatAbsorption.lean:12` | PASS。空间下界及真实小量界乘以非负 Q³Z²，并加入梯度项，得到保留同一余项和实际 W 示性函数的点态吸收；最终调用内部清偿全部标量前提。 |
| 7 | `Carleman.continuous_box_observation_integrable` | `Carleman/Spatial/BoxObservationIntegral.lean:11` | PASS。连续函数在真实有限柱可积，再由 W 可测和 Integrable.indicator 得真实观测示性函数可积；未假定示性函数连续。 |
| 8 | `Carleman.boxTimeIntegral_observation` | `Carleman/Spatial/BoxObservationIntegral.lean:18` | PASS。真实 indicator 积分及两次限制测度相交，把观测项严格识别为 `[0,T] × (Ω∩W)` 的限制乘积积分。 |
| 9 | `Carleman.boxTimeIntegral_mono_on_integrable` | `Carleman/Spatial/BoxObservationIntegral.lean:32` | PASS。对实际可积函数，仅需原柱内逐点大小关系；适用于含不连续示性函数的吸收式。 |
| 10 | `Carleman.boxTimeIntegral_add_integrable` | `Carleman/Spatial/BoxObservationIntegral.lean:44` | PASS。用真实可积性实现加法，合法拆开观测项与连续主项。 |
| 11 | `Carleman.boxTimeIntegral_nonneg_on` | `Carleman/Spatial/BoxObservationIntegral.lean:51` | PASS。仅在实际柱内的非负性给积分非负；最终应用于真实平方及 q 非负加权项。 |
| 12 | `Carleman.box_smooth_gaussian_heat_observation` | `Carleman/Spatial/BoxGaussianHeatObservation.lean:15` | PASS。所有空间和吸收参数先于 T/q/u，真实单调积分后与同一 heatcross 的 C 余项消去，得到 A₁∫q‖∇z‖²+A₀∫q³z²≤¼∫真实残差²+K∫_Wq³z²。 |
| 13 | `Carleman.heat_gradient_return` | `Carleman/Spatial/HeatGradientReturn.lean:13` | PASS。实际指数及乘积微分给 θDᵢu=Dᵢz−DᵢL·z，逐方向平方和得到系数 2 的真实返回界。 |
| 14 | `Carleman.spatial_directionalEnergy_gradient` | `Carleman/Weights/InteriorHeatGradientReturn.lean:13` | PASS。Euclidean 基的全部方向平方和严格等于真实 Riesz gradient 范数平方，无额外维数系数。 |
| 15 | `Carleman.spaceTime_directionalEnergy_gradient` | `Carleman/Weights/InteriorHeatGradientReturn.lean:21` | PASS。真实空间切片链式法则把时空空间方向能量识别为同一 u(t,·) 的实际 gradient 范数平方。 |
| 16 | `Carleman.interiorGaussianHeatPhase_uniform_energy` | `Carleman/Weights/InteriorHeatGradientReturn.lean:31` | PASS。固定 S/c/λ 后由原空间 profile 梯度能量在紧闭包上的界选 J>0，再量化 q/t，证明实际相位能量≤Jq²。 |
| 17 | `Carleman.interiorGaussianHeat_return_bound` | `Carleman/Weights/InteriorHeatGradientReturn.lean:53` | PASS。内部取 H=3+2J，先于 q/u/t，得到原加权值与梯度两项由 H(q‖∇z‖²+q³z²) 控制。 |
| 18 | `Carleman.box_smooth_gaussian_heat_estimate` | `Carleman/Spatial/BoxSmoothHeatEstimate.lean:14` | PASS。原 u 的完整 (3,1;3) 积分估计、真实热残差及真实观测项，负权界、正参数和统一量词全部保留；没有外给目标估计或额外时间长度常数。 |

## 数学与量词审查

**实际观测球及空间势。** 在调用者给定的非空开 W 中选择 c。开集性质给球半径 ε，再取 r=ε/2，使真实闭球包含于 W；不要求 W 包含预先指定中心。依赖 `exists_interior_heat_weight` 以阈值 6 选 λ=max(1,3/r²)，于是球外 λg≥12，其中 g=‖∇ψ‖²=4‖x−c‖²。S 的有界性给真实 Gaussian 正下界 κ=exp(−λ(R+‖c‖)²)>0。由 g≥4r² 和 λg−6≥6，实际 F=λ³φ³g(λg−6) 在球外满足 F≥m=24λ³κ³r²>0。

F 在 closure S 上连续且有统一绝对值界 D。取 K=|D|+m，对 x∈W 使用 F≥−D，对 x∉W 使用闭球⊆W 推出 x 不在开球内，得到全部 S 上 `m≤F+K·1_W`。同时 a=λκ>0 给 `a≤λφ`。这些是从真实几何和真实系数推出的下界，没有输入“观测外势正”或目标观测估计。最终仅要求 W 开、非空、包含于 Ω；原文要求相对紧包含的观测开集当然在此范围内，没有增加观测几何限制。

**小量选择和同一余项。** Ccross 来自已验收的实际 `box_smooth_gaussian_heat_cross`，固定 a/b/c/λ 后选择，先于 T、q、β、u。m>0 和 Ccross>0 给 β=min(1,m/(8Ccross))、qc=max(1,4Ccross/m)。对 Q≥qc，实际证明 `Ccross Q²≤(m/4)Q³`；由 β≤1、β≤m/(8Ccross) 得 `Ccross(β+β²)Q³≤(m/4)Q³`，总和≤(m/2)Q³。没有把 qc 或 β 依赖于 T、qmax 或状态。

令 E=‖∇z‖²、Z=z，实际点态吸收保留左侧 `aQE+(m/2)Q³Z²+Ccross[Q²+(β+β²)Q³]Z²`。右侧正是同一个 heatcross 的 `QλφE+Q³FZ²` 加 `K·1_W Q³Z²`。可积单调积分和真实加法后，heatcross 右侧的同一 `Ccross∫[q²+(β+β²)q³]z²` 与左侧完全消去；不是使用另一个尺度或更强的余项假设。所得 A₁=a、A₀=m/2 均严格正，残差系数仍为 1/4。

**真实观测积分与可积性。** `boxTimeIntegral` 沿用实际 `(volume|[0,T])×(volume|Ω)`。W 开保证可测，时空观测集是 `Prod.snd ⁻¹' W`。`Integrable.indicator` 从连续加权状态的真实柱可积性推出观测项可积；`integral_indicator`、`Measure.prod_restrict` 和 `Measure.restrict_restrict` 给精确的 Ω∩W 限制乘积测度。因 W⊆Ω，Ω∩W=W，确为原观测柱而非另一个观测泛函。第 8 项一般 identity 对任意 f 成立；实际估计中所用 f 连续且有限柱可积，未利用非可积时 Bochner 积分默认值。

含观测示性函数的单调积分明确使用 `boxTimeIntegral_mono_on_integrable`；拆开该项使用可积加法，没有把示性函数误认为连续。其余实际加权值、梯度、余项和残差均由 q/u 的 C∞ 性及同一固定空间权的光滑性在有限柱上可积。q≥qc≥1 只须在 [0,T]；原柱外没有不必要的正性前提。T=0 的积分自然为零，原 T>0 完整包含。

**真实微分返回及梯度身份。** z 严格为 exp(L)u。逐方向实际 Fréchet 乘积和指数法则证明 `exp(L)Dᵢu=Dᵢz−DᵢL·z`；平方界用实数平方非负，求和得到 `θ²E(u)≤2E(z)+2E(L)z²`。固定 ρ=φ−2 的实际空间能量在 closure S 上连续有界；取 J=|D|+1 并使用分离相位的真实微分身份 `E(L)=q²E(ρ)`，在所有 q/t 前得到 E(L)≤Jq²。由此 H=3+2J 给 `q³θ²u²+qθ²E(u)≤H(qE(z)+q³z²)`，没有出现 qmax 或时间长度。

`spatial_directionalEnergy_gradient` 使用 mathlib 中 gradient 的真实定义 `(toDual).symm (fderiv f x)`、`inner_gradient_left` 和 Euclidean 全坐标范数平方公式。一般 f 的该身份是同一个总定义 fderiv 的身份；最终 u 光滑，故确为真实微分。时空版本进一步使用实际切片链式法则，输出 `‖gradient (fun y => u(t,y)) x‖²`，而不是抽象能量占位符。没有遗漏坐标、混入时间方向或引入维数损失。

**最终参数、规范化和原形式。** 最终先固定维数、正盒 a/b 与 W，然后输出 c、λ、β、qc、C，最后才量化 T≥0、全部 C∞ 周期 q 和全部 C∞ 周期 u。q′、q″ 分别是实际 `deriv q` 与 `deriv (deriv q)`，要求正是原 qclass 的 βq²、β²q³ 界。原 qmax 不是新的常数依赖；有限时间区间上连续 q 本来有上界，而本估计无需指定该上界。所有时刻原 frontier 上 u=0 的条件明确保留。

用 D=1/A₁+1/A₀>0，实际非负积分满足 `∫E+∫V≤D(A₁∫E+A₀∫V)`；取最终 C=HD(1+K)>0。残差和观测项均非负，故它控制 HD(¼∫R+K∫O)。`z²=θ²u²` 逐点代数身份同时用于值项和同一观测项，最终得到

`∫q³θ²u² + ∫qθ²‖∇u‖² ≤ C(∫|θ(∂t−Δ)u|² + ∫_W q³θ²u²)`。

指数确为 (c₀,c₁;o)=(3,1;3)。`spaceTimeHeat` 仍是原时间切片 deriv 减实际空间 Laplacian，因此为 Dirichlet 热算子的正向残差。ρ 全局 C∞ 且 −2<ρ≤−1；λ≥1 保证该严格负界，可取原负权阈值 ρ*=1。正空间维数由 d+1 编码，包含一维盒；一般辅助声明允许 d=0。最终没有缺失的状态选择、预设可积性、目标 Carleman 估计或隐藏的 T 因子。

**范围限制。** 此处确已得到陈述范围内完整的光滑正向盒观测估计，但全时空 C∞ / 全局周期 / 逐点零边界的输入仍比原弱轨道陈述窄。原 C² 时间权、`H¹_t L²_x ∩ L²_t D(A)` 的完整周期轨道、一般凸多面体，以及反向时间情形仍未由本批完成。不存在把本批十八项的 PASS 直接解释为 P024 完成的依据。

## 依赖版本、工具链与公理

递归读取八个新模块的 Carleman import 闭包，共 127 个文件，其中 119 个旧文件与 mathematical_base 逐文件内容完全相同。按固定台账既有 declaration_version 再作相关闭包比较：

| 依赖 | 已验收 declaration_version | 比较入口 / 文件数 | 结论 |
|---|---|---|---|
| C160 | `2cd92104c803b6a2e586be26a9685e4b2c7fc976` | `InteriorHeatMatrix` / 81 | 无变化 |
| C165 | `37d15b168e8c1ac3f313848be5a0c56594d2aad2` | `BoxIntegratedHeatIdentity` / 106 | 无变化 |
| C166 | `cc5e0b8ad589a03b86766a8c2c5dedc49449ced4` | `InteriorHeatB`、`InteriorHeatCoefficients` 并集 / 91 | 无变化 |
| C167 | `8e740040ffe3ce75cb89b5868d5998b5ad8cd74c` | `BoxGaussianHeatCross` / 119 | 无变化 |

特别实际读取了 `InteriorGaussianGeometry`、`InteriorHeatMatrix` 的选球/阈值/正界证明，`InteriorHeatCoefficients` 与 `SeparableHeatPhase` 的原相位和真实微分，以及 `InteriorHeatBLowerBound`、`InteriorHeatMixedTerm`、`InteriorHeatBulkLowerBound`、`BoxGaussianHeatCross` 的同一余项和量词。未用旧审查摘要替代新接口连接核对。

固定 Lean 4.35.0；实际 CI 的 Lean commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际依赖 HEAD 相同且工作树干净。核对其真实 gradient/Riesz 身份、Euclidean 基坐标恒等式和 indicator 积分声明。

固定 raw 共 2836 个显式公理记录，其中 2827 个含正常基础公理、9 个无公理；未知公理集合为空。全部十八项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。递归审计末行是 `Axiom audit passed for all 7571 Carleman declarations.`。2836 个显式输出记录与 7571 个递归声明不是同一种计数。未发现 sorryAx 或额外数学公理。

## 实际构建和独立 CI 证据

实际读取 `/tmp/carleman-t152-smooth-estimate-final-target.log`，包含最终 `Carleman.Spatial.BoxSmoothHeatEstimate`，3288 jobs 构建成功；`/tmp/carleman-t152-smooth-heat-estimate-build.log` 根目标 `Carleman` 完整构建成功，4028 jobs；同前缀 `-axioms.log` 的全部 7571 声明递归审计通过。这里记录的是固定已有日志核验，未声称审查者另行重跑本机构建。

审查者独立查询 GitHub 正式 run **39238936853** / attempt **1**，最终整体 `completed/success`，head SHA 精确匹配 checked_sha，updated_at 为 `2026-10-19T10:43:18Z`。实际三个 jobs 全部 `completed/success`：

| Job | ID | 结果 |
|---|---|---|
| lean | `118014760391` | success |
| state-check | `118014760467` | success |
| dashboard / snapshot | `118016405251` | success |

正式 CI：[run 39238936853 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39238936853/attempts/1)。独立查询并自行 `gh run download` 下载同次两个原始 artifact：

- `lean-ci-result`：artifact ID **12180267573**；实际文件 `/tmp/carleman-t152-smooth-heat-estimate-main-ci/result.json` 为 `status=PASS`，`checked_sha=source_head_sha=86686ea4d106798727d898bf61abc238812a8cb8`，`finished_at=2026-10-19T10:41:55.996544+00:00`，targets 为 `Carleman`，CI URL 属于同 run / attempt。
- `lean-declaration-evidence`：artifact ID **12180227715**；实际文件 `/tmp/carleman-t152-smooth-heat-estimate-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t152-smooth-heat-estimate-local-axioms.txt` **逐字节完全相同**，**2350438 bytes**，SHA256 **`75d2760a07a0568dd037a3c93c5c86185a1c12cdae2de5d1fc5eefa711cb3f5a`**；远端末行同为 7571 声明递归审计通过。

## 签发结论

十八项声明均 **PASS**，没有阻断 C168 AUXILIARY 验收的数学或证据缺陷。原观测几何、实际势正性和负项补偿、统一吸收、真实观测积分、同一残差与原梯度的完整连接均已核对；所有最终参数先于 T/q/u。仅签发并单独提交本报告，不改实现、root/audit、台账或原稿，不推送。签发后冻结 reviewed_at 和内容；P024 及原文 17/26 覆盖数保持。
