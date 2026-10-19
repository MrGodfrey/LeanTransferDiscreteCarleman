# T144 / C160 独立本机验收

- checked_sha / source_sha：`2cd92104c803b6a2e586be26a9685e4b2c7fc976`。
- base_commit：`90ca06c7cd42fae4b870fae9a67219fa729226f7`。
- reviewed_at：`2026-10-19T09:30:37+00:00`。
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批数学实现。
- result：**PASS**；axiom_check：**PASS**；32/32 项声明通过。
- scope：**AUXILIARY**。可将 C160 在本固定版本登记为 REVIEWED；P024 / `prop:continuousCE` 不提升，原文完成数保持 **17/26**。

本报告直接读取固定 Git 对象中的三模块全部定义、证明、实际产物的全部展开类型、原稿、T144 分析、MATH_SPEC、C160/T144 台账及关键依赖。独立访问实际 GitHub run/jobs/artifacts，并自行下载同 run 的原始 result/axioms。CI、执行者说明和既有依赖验收标签均未替代本次语义核查。仅新增并按授权单独提交本报告；不修改实现、台账、原稿或根导入，不推送。后续 T145 工作树文件及动态 `.ci/axioms.txt` 不属于本批证据。

## 原文对应与范围

固定 `paper/main.tex:2672–2730` 的 Proposition A.3 / `prop:continuousCE` 要求原完整时空状态、全部允许时间权、任意 T 及两个时间方向上的连续热 Carleman 估计。本批只对应其中 `2684–2690` 的空间权选择、`2698–2710` 的 Ψ 与矩阵计算、`2704` 所需法向符号，以及 `2724` 的球外梯度阈值选择。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。

已直接查看本地原书渲染 `/tmp/carleman-fu2019-cor31.png`，图中印刷页为 60：Fu–Lü–Zhang, *Carleman Estimates for Second Order Partial Differential Operators and Applications* (2019)，标准引用键 `fu2019carleman`，Corollary 3.1，式 (3.3)–(3.5)。取 p=Id、Φ=0 后，式 (3.5) 中的 c 确为 `2 Hess ℓ − (Δℓ+Ψ) Id`；式 (3.3) 在 c 二次型外另有一个系数 2。本批没有将该外部系数混入 c。原书完整时空不等式本身不在本批形式化范围。

原实际函数完全保留为 `ψ(x)=−‖x−c‖²`、`φ(x)=exp(lψ(x))`、`ρ(x)=φ(x)−2`。微分是 mathlib 的真实 Fréchet 导数，梯度是 Riesz 对偶定义的真实 `gradient`；既未把目标导数作为结构输入，也未在任意 L² 商空间代表上求点值。最终存在定理先选定 c、r、l、κ、K，再量化所有 q≥0、x、向量 u 及通量标量 a。

尚未完成点态热算子恒等式、真实面上的 Green 积分及通量识别、时间端点抵消、`eq:heatcross`、低阶吸收、密度传递和时间反射；本批也没有选择完整结论所需 β、q_c。故它是忠实的空间权辅助步骤，不能提升整个 P024。

## 全部 32 项声明

以下名单与 `/tmp/carleman-t144-interior-weight-declarations.json`、固定 C160/T144 的 `lean_declarations` 完全一致。位置均为 checked_sha 下 `Carleman/Weights/` 的源码位置。三模块均被固定 `Carleman.lean` 导入；32 项均有固定 `tools/CheckAxioms.lean` 中的 `#check @...` 与 `#print axioms ...`，并实际出现于原始产物。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.interiorQuadratic` | `InteriorGaussianWeight.lean:16` | PASS；真实负 Euclidean 距离平方。 |
| 2 | `Carleman.interiorGaussian` | `InteriorGaussianWeight.lean:18` | PASS；同一 ψ 的真实指数 exp(lψ)。 |
| 3 | `Carleman.interiorCarlemanProfile` | `InteriorGaussianWeight.lean:21` | PASS；同一 φ 减常数 2。 |
| 4 | `Carleman.interiorQuadratic_contDiff` | `InteriorGaussianWeight.lean:24` | PASS；实际范数平方和平移给全空间 C∞。 |
| 5 | `Carleman.interiorGaussian_contDiff` | `InteriorGaussianWeight.lean:28` | PASS；真实乘常数与指数链式法则给 C∞，任意 l。 |
| 6 | `Carleman.interiorCarlemanProfile_contDiff` | `InteriorGaussianWeight.lean:32` | PASS；减常数保持实际 C∞。 |
| 7 | `Carleman.interiorQuadratic_hasFDerivAt` | `InteriorGaussianWeight.lean:36` | PASS；真实 CLM 导数为 −2⟨x−c,·⟩。 |
| 8 | `Carleman.interiorGaussian_hasFDerivAt` | `InteriorGaussianWeight.lean:46` | PASS；真实指数链式法则给 −2lφ⟨x−c,·⟩。 |
| 9 | `Carleman.interiorCarlemanProfile_hasFDerivAt` | `InteriorGaussianWeight.lean:57` | PASS；ρ 的真实导数与 φ 相同。 |
| 10 | `Carleman.interiorGaussian_fderiv_apply` | `InteriorGaussianWeight.lean:63` | PASS；真实 Fréchet 导数对任意方向 u 的精确值。 |
| 11 | `Carleman.interiorCarlemanProfile_fderiv_apply` | `InteriorGaussianWeight.lean:70` | PASS；同一实际 ρ 的方向导数身份。 |
| 12 | `Carleman.interiorGaussian_pos` | `InteriorGaussianWeight.lean:77` | PASS；任意 l、x 的指数严格正。 |
| 13 | `Carleman.interiorGaussian_le_one` | `InteriorGaussianWeight.lean:80` | PASS；l≥0 时利用 ψ≤0 得全空间 φ≤1。 |
| 14 | `Carleman.interiorCarlemanProfile_bounds` | `InteriorGaussianWeight.lean:85` | PASS；l≥0 时全空间 −2<ρ≤−1，严格负性真实成立。 |
| 15 | `Carleman.interiorCarlemanProfile_hessian` | `InteriorGaussianWeight.lean:93` | PASS；对两独立方向的真实二阶导数，秩一项系数 4l²φ、单位项系数 −2lφ。 |
| 16 | `Carleman.interiorCarlemanProfile_smoothOnClosure` | `InteriorGaussianGeometry.lean:15` | PASS；以全空间实际 C∞ 构造任意 S 的原内禀闭包光滑性。 |
| 17 | `Carleman.interiorSpatialProfile` | `InteriorGaussianGeometry.lean:21` | PASS；任意测度上的实际同值 Profile，可测性和统一绝对值 bound=2 均内部供应。 |
| 18 | `Carleman.interiorSpatialProfile_value` | `InteriorGaussianGeometry.lean:31` | PASS；Profile 的点态值严格等于原 ρ，不只是 a.e. 替代对象。 |
| 19 | `Carleman.interiorQuadratic_gradient` | `InteriorGaussianGeometry.lean:35` | PASS；从真实 HasFDerivAt/Riesz 身份给 ∇ψ=−2(x−c)。 |
| 20 | `Carleman.interiorQuadratic_gradient_norm_sq` | `InteriorGaussianGeometry.lean:44` | PASS；精确 Euclidean 范数平方 4‖x−c‖²。 |
| 21 | `Carleman.interiorQuadratic_gradient_outside_ball` | `InteriorGaussianGeometry.lean:50` | PASS；r≥0、开球外（含球面）推出梯度平方≥4r²。 |
| 22 | `Carleman.exists_interiorGaussian_gradient_threshold` | `InteriorGaussianGeometry.lean:57` | PASS；r>0 时实际取 l=max(1,C/(2r²))，统一供应球外 l‖∇ψ‖²≥2C。 |
| 23 | `Carleman.interiorGaussian_lower_bound` | `InteriorGaussianGeometry.lean:69` | PASS；l,R≥0、真实距离界给 φ≥exp(−lR²)。 |
| 24 | `Carleman.interiorGaussian_supporting_normal` | `InteriorGaussianGeometry.lean:77` | PASS；真实支持方向条件与 l≥0 给实际 ∂nφ≤0，内积符号正确。 |
| 25 | `Carleman.interiorGaussian_face_flux_nonpos` | `InteriorGaussianGeometry.lean:89` | PASS；c∈S 和完整支持半空间条件给任意 a 的 2q∂nφ·a²≤0，q≥0。 |
| 26 | `Carleman.interiorHeatPsi` | `InteriorHeatMatrix.lean:13` | PASS；Ψ 定义为真实 −Δ(qρ)−8qlφ。 |
| 27 | `Carleman.interiorHeatMatrix` | `InteriorHeatMatrix.lean:17` | PASS；从真实两次 Fréchet 导数及实际 Laplacian 定义原 c 双方向值。 |
| 28 | `Carleman.interiorCarlemanProfile_scaled_hessian` | `InteriorHeatMatrix.lean:23` | PASS；冻结任意真实标量 q，真实二阶导数准确乘 q。 |
| 29 | `Carleman.interiorHeatMatrix_formula` | `InteriorHeatMatrix.lean:41` | PASS；完整双线性方向公式等于 4qlφ Id+2ql²φ∇ψ⊗∇ψ，原系数准确。 |
| 30 | `Carleman.interiorHeatMatrix_coercive` | `InteriorHeatMatrix.lean:52` | PASS；q≥0 时秩一平方项非负，给≥4qlφ‖u‖²；此基础不等式允许任意 l。 |
| 31 | `Carleman.interiorHeatMatrix_uniform_coercive` | `InteriorHeatMatrix.lean:61` | PASS；l>0、R≥0 时先取 K=4l exp(−lR²)>0，再对全部 q≥0、距离≤R 的 x 和任意 u 成立。 |
| 32 | `Carleman.exists_interior_heat_weight` | `InteriorHeatMatrix.lean:73` | PASS；从有界 S、非空开 W⊆S 和固定 C 内部选球及全部空间参数，一次取得负光滑权、正下界、阈值、矩阵界及支持面标量符号。 |

## 语义、量词与条件核查

**导数及真实负权。** ψ 的导数由实际 `norm_sq` 与平移导数取得，再对 exp(lψ) 应用真实链式法则。Hessian 证明先取得在所有 y 上的全函数恒等式 `Dρ(y)u=−2lφ(y)⟨y−c,u⟩`，再对该函数用乘积和内积导数求导；没有对只在单点成立的等式求导。所得二阶式为 `4l²φ⟨x−c,u⟩⟨x−c,v⟩−2lφ⟨v,u⟩`，保留两方向与次序，实内积下对称性正确。scaled Hessian 额外证明一阶导数路径光滑，再对外层乘 q 使用合法 Fréchet 法则，不假定目标二阶公式。

`SmoothOnClosure` 的实际定义包含闭包上的函数连续性、域内全阶光滑性以及每一阶真实导数的连续延拓。新权全空间 C∞，故用 U=univ 的既有 `of_neighborhood` 直接供应这些字段；不要求任意域外代表可微。`interiorSpatialProfile` 逐字段使用同一 ρ、实际连续性所给可测性及全空间 −2<ρ≤−1 推出的绝对值界。严格负性是独立已证点态定理，原 `SpatialProfile` 结构本身只记录有界可测数据，没有伪称该结构自动包含负性或光滑性。对每个实际测度 ν 均可使用，结论不留测度有限性或代表正则性前提。

**观测球与阈值选择。** 从 W 的非空性选 c∈W，再由 W 开性得到 ε>0 的开球包含；取 r=ε/2>0，利用实际闭球包含于 ε 开球，得 `closedBall c r⊆W`。不额外要求观测集是球，也不将中心置于边界。原观测区域非空、开且紧包含于 Ω，满足本批较弱前提。开球外条件是 x∉ball(c,r)，包括边界球面；真实梯度平方≥4r²。对任意已固定 C，取 l=max(1,C/(2r²))，正分母和 l≥0 合法推出目标阈值，即使 C≤0 亦无非法除法或符号翻转。

这里的 C 是一个**输入的吸收系数**，不是本批已证明存在的 `eq:heatcross` 常数。本批没有证明该时空估计，亦没有证明其常数独立于 l；将来的热恒等式/估计必须先给相应 C，才能按此阈值定理选择 l。该接口是原证明中一项正确的参数选择工具，不足以独自供应 β、q_c 或完成吸收。

**实际矩阵与统一正性。** 旧 `spatialLaplacian` 已直接核对，是固定 Euclidean 正交坐标上的实际两次 Fréchet 导数之迹，并非任意给定的 Δ 字段。新 `interiorHeatMatrix` 先按原导数定义 `2D²(qρ)(u,v)−(Δ(qρ)+Ψ)⟨v,u⟩`，再代入实际 Ψ 和 Hessian。因此 Δ 的抵消是对同一真实 Laplacian 的代数抵消，不能解释为通过另定矩阵跳过目标。单位项由 −4qlφ 与 +8qlφ 合成 +4qlφ；秩一项由 ∇ψ=−2(x−c) 得到精确系数 +2ql²φ。此处 c 对应原书式 (3.5)，未吸收原式 (3.3) 中外部 2 倍因子。

基础二次型下界仅要求 q≥0，利用 l²φ≥0 保证附加平方项非负；当 l<0 时它不宣称严格正性。统一强制性定理明确改用 l>0、R≥0，取 K=4l exp(−lR²)>0。最终定理由 S 的真实有界性取得 R>0、‖x‖≤R，利用 ‖x−c‖≤R+‖c‖，选择 `κ=exp(−l(R+‖c‖)²)>0` 和对应 K。这些量先于全部 q、x、u 选择；q=0 时等式退化为合法的零下界，原正 q 族当然包含在内。没有 qmax、T、时间网格、状态维数截断或额外状态界混入常数。

**支持方向与通量标量。** 条件 `∀y∈S, ⟨y−x,n⟩≤0` 是实际支持半空间条件；c∈S 内部给出 ⟨c−x,n⟩≤0，因此 ⟨x−c,n⟩≥0。由于 `Dφ(x)n=−2lφ(x)⟨x−c,n⟩`，l≥0 给非正；再乘 2q≥0 与 a²≥0 保持非正。法向方向没有反置，也不需要 n 归一化才能有符号结论。最终 c∈S 由 c∈W 和 W⊆S 内部供应。

本批定理对任意提供该支持条件的 x,n 成立；它没有构造真实多面体面或法向，没有证明实际 Green 边界向量恰等于该标量，没有为 Sobolev 状态构造法向迹，也没有通过“边界零测”省略边界积分。原凸域面几何及 Green 应用仍须在后续显式建立。本批准确完成的是需要的点态符号工具。

**量词边界。** 最终 `exists_interior_heat_weight` 仅用有界 S、非空开 W、W⊆S 和固定实数 C；S 的开性、凸性、边界光滑性、有限体积均不是该空间代数步骤的额外前提。C、S、W 可以影响所选空间参数，但所有 q、测试向量、通量标量均在这些选择之后。d 任意；d=0 时球外条件可为空量化，构造未选择不存在的坐标。任意实际正维数原域都在其范围内。完整时间方向、原全时空状态、周期端点和误差吸收不在声明中，不能从这些空间结论推称已经完成。

## 依赖闭包、公理与工具链

三新模块的 `Carleman` import 递归闭包共 **81** 模块；其中 **78** 个旧模块与固定基线逐文件内容相同。另将关键根的完整 import 闭包与其已验收 declaration_version 比较：

| 依赖 | 已验收版本 | 本次核查根及闭包数 | 结论 |
|---|---|---|---|
| C030，原闭包光滑/Profile 接口 | `bed432f9ab0eebd8a31163608ff72c422299e93d` | `Weights/ClosureProfile`，28 模块 | 全部内容相同；实际 `SmoothOnClosure`、`of_neighborhood` 与 Profile 结构已直接读取。 |
| C149，真实经典 Laplacian | `c3ea3c03352de258d944bf495695b31bcef3f3b0` | `Spatial/SmoothLaplacianProduct`，76 模块 | 全部内容相同；实际正交坐标二阶导数定义已直接读取。 |

固定 C030 台账的独立验收指向历史 [PR 16](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/pull/16)；C149 的固定独立报告 [T133-local-acceptance.md](T133-local-acceptance.md) 已读。新矩阵仅使用 C149 的实际 Laplacian 定义，没有借用未完成的连续 CE 作为输入；权函数资格直接证明，不依赖原 P024 的待证存在结论。

实际固定工具链为 Lean `4.35.0`、compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；本机版本与远端 result 相符。mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 checkout 同 SHA 且干净。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、lean-toolchain、lake-manifest 的固定哈希与本 Agent 此前已读适用版本相同，继续遵循其独立语义/同版本证据协议。

固定 raw 含 **2,661** 条显式公理打印记录：**2,652** 条只依赖 `propext`、`Classical.choice`、`Quot.sound` 的子集，另 **9** 条无公理。独立解析无异常公理，32 项本批声明全部存在，源模块无 `sorry`、`admit` 或新 `axiom`。末行实际为 `Axiom audit passed for all 7354 Carleman declarations.`；递归审计包含生成的辅助声明，不限于公开的 32 项。

## 构建、实际 CI 与独立下载证据

已读取固定 `/tmp/carleman-t144-matrix-target.log`：定向构建 **3,224 jobs** 成功；`/tmp/carleman-t144-interior-weight-build.log`：全库 **3,976 jobs** 成功；`/tmp/carleman-t144-interior-weight-axioms.log`：**7,354** 递归声明公理审计 PASS。本报告核对固定既有日志和正式远端产物，没有声称重跑新的全库构建。

本人独立查询实际 GitHub [run 39230125946 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39230125946/attempts/1)，确认 event=push、branch=main、head SHA 精确等于 checked_sha，最终 run 为 `completed/success`。没有在仅产物已上传但 lean 仍运行时提前签发；最终三个 jobs 均为成功：

| job | ID | 状态 | completed_at（UTC） |
|---|---|---|---|
| state-check | `117985798379` | completed / success | `2026-10-19T09:27:05Z` |
| lean | `117985798784` | completed / success | `2026-10-19T09:29:50Z` |
| dashboard / snapshot | `117987011172` | completed / success | `2026-10-19T09:30:02Z` |

实际 artifact API 确认两个证据均来自上述同 SHA run、未过期；本人分别执行 `gh run download` 成功下载：

| artifact | ID | API 压缩大小 | 本人下载位置 |
|---|---|---|---|
| lean-ci-result | `12176343556` | 492 bytes | `/tmp/carleman-t144-interior-weight-main-ci/result.json` |
| lean-declaration-evidence | `12176633422` | 208,788 bytes | `/tmp/carleman-t144-interior-weight-main-axioms/axioms.txt` |

原始 result 实际为 `PASS`、`checked_sha=source_head_sha=2cd92104c803b6a2e586be26a9685e4b2c7fc976`，目标 `Carleman`，`finished_at=2026-10-19T09:28:50.812630+00:00`；文件 **537 bytes**，SHA256 **`54ecb4a217e09ff8a8e025185497b4856cd2ef7d9166fc27689c24789d036dd4`**。远端 raw 与固定 `/tmp/carleman-t144-interior-weight-local-axioms.txt` 独立逐字节比较完全相同：均为 **2,247,598 bytes**、SHA256 **`3832de1c1b2e06c6ad536a02dcf6b0b6530d8dbac8b17997bab84a3925d2ac66`**。

API 压缩包 digest 分别为 result `sha256:67ea302e220b08214d6854a26fc5076039617b75f1a84bf900de5a33efc94052`、axioms `sha256:9959b28cbafeaf966c51b4ed41b1428cf5b33ea0fe1b45b7fc6f37b3e5e2e4f0`。这些是压缩包层面的证据，未与解压后原始文件大小/hash 混同。

## 签发结论

**T144 / C160：32/32 PASS，axiom_check PASS，未发现阻断性数学缺陷。** 原实际 Gaussian 负光滑权、真实一阶/Hessian/梯度公式、球外阈值、同一真实矩阵的精确原系数及统一正性、支持方向下的实际法向导数和通量标量符号均已证明。参数选择顺序正确；可登记 REVIEWED / AUXILIARY。

P024 整体仍待完整点态热恒等式、真实 Green 通量、时间端点、吸收、密度和两个方向的证明，不予提升；原文覆盖保持 17/26。本报告仅单独提交、不推送；通知主 Agent 后冻结上述签发时间与内容，不再修改。
