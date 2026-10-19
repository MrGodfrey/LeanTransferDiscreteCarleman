# T149 / C165 独立本机验收：光滑周期盒上的真实积分热不等式

- checked_sha / source_sha: `37d15b168e8c1ac3f313848be5a0c56594d2aad2`
- mathematical_base: `a3a39eadfe9f18fee3bdd0a60b07cd5856bd3dbb`
- reviewed_at: `2026-10-19T10:15:45+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 验收对象为本 SHA 的三个模块、十五个显式声明。可据此将 C165 升级为 REVIEWED，但保留 AUXILIARY；P024 / `prop:continuousCE` 不提升，完整原文覆盖仍为 **17/26**。

## 固定版本与原文范围

直接读取固定 Git 对象中的全部新源码、完整展开声明、公理输出和相关旧证明，并对照 `paper/main.tex:2672–2733` 的原连续 CE 命题及证明。原文先取光滑周期状态、令 z=exp(ℓ)u，消去时间通量，利用空间通量非正，再估计实际系数、吸收观测外余项，最后密度与时间反射。本批只完成其中真实时空积分与两种通量清偿，未达到原最终带观测项的 CE。

核对了固定 `governance/analysis/T149-integrated-smooth-heat.md`、`governance/MATH_SPEC.md` 的 T149 段、C165/T149 登记以及根 AGENTS 和治理协议；规格和 CI 均未替代数学检查。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有为本批改变原命题。未采用动态工作树中后续 Gaussian differential、separable phase、B 或 coefficient 模块，也未采用动态 `.ci/axioms.txt`。

## 十五项声明逐项核对

下列路径均相对于固定版本仓库，行号指声明起始行；每项均与固定 raw 中的完整类型核对。清单与 C165 的 `lean_declarations` 及固定 declarations.json 顺序完全相同，三个模块均由 `Carleman.lean` 导入，十五项均进入 `tools/CheckAxioms.lean`。

| # | 显式声明 | 固定源码位置 | 数学结论与审查结果 |
|---|---|---|---|
| 1 | `Carleman.boxTimeIntegral` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:13` | PASS。定义为真实 Lebesgue 限制测度 `(volume.restrict [0,T]).prod (volume.restrict Ω)` 上的积分；不是抽象积分泛函或外给线性接口。 |
| 2 | `Carleman.continuous_box_time_integrable` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:17` | PASS。由 `[0,T] × closure Ω` 紧、连续函数紧集可积和限制测度单调性，内部给原开盒柱可积性；任意 a/b/T 的一般辅助形式也允许空柱。 |
| 3 | `Carleman.boxTimeIntegral_eq_iterated` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:26` | PASS。使用第 2 项提供的实际可积性调用 Fubini，严格得到时间在外、空间在内的原积分。 |
| 4 | `Carleman.boxTimeIntegral_add` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:31` | PASS。两个实际连续函数各自可积后使用真实积分加法，无未证明的可积性字段。 |
| 5 | `Carleman.boxTimeIntegral_mono` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:36` | PASS。两个实际可积函数和逐点大小关系给积分单调性；最终应用中的所有连续性均内部供应。 |
| 6 | `Carleman.boxTimeIntegral_nonpos_of_spatial` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:41` | PASS。实际迭代积分及每个 t∈[0,T] 的空间积分非正推出全时空非正。此辅助引理明确保留空间积分符号前提；最终定理由真实盒散度定理清偿该前提。 |
| 7 | `Carleman.boxTimeIntegral_periodic_derivative` | `Carleman/Spatial/SmoothBoxTimeIntegral.lean:48` | PASS。实际时间 Fréchet 方向导数可积，交换积分、Icc/Ioc 端点 a.e. 转换及周期 FTC 得全柱积分为零；没有把逐 x 结论未经 Fubini 直接积分。 |
| 8 | `Carleman.directionalHessianForm_contDiff` | `Carleman/Spatial/HeatIdentityRegularity.lean:12` | PASS。任意有限方向族中完整双重和的真实二阶方向导数及两个一阶导数乘积为 C∞；未删去非对角项。 |
| 9 | `Carleman.pointwiseHeatMatrixEnergy_contDiff` | `Carleman/Spatial/HeatIdentityRegularity.lean:19` | PASS。真实 `2 Hess ℓ[∇z,∇z]−(Δℓ+p)|∇z|²` 的全部项经导数、和、乘积构造 C∞。 |
| 10 | `Carleman.pointwiseHeatB_contDiff` | `Carleman/Spatial/HeatIdentityRegularity.lean:25` | PASS。真实 `k_t+2 Σᵢ Dᵢ(k Dᵢℓ)+2kp` 全部保留并证 C∞，并非另给替身系数的正则性。 |
| 11 | `Carleman.heatCarlemanBulk` | `Carleman/Spatial/HeatIdentityRegularity.lean:33` | PASS。完整定义 `(Δz+kz)²+2c[∇z,∇z]−2(∇p·∇z)z+Bz²`；不预设其非负。 |
| 12 | `Carleman.heatCarlemanBulk_contDiff` | `Carleman/Spatial/HeatIdentityRegularity.lean:37` | PASS。对上述同一完整 bulk 逐项证明 C∞，从而其实际柱积分可积。 |
| 13 | `Carleman.pointwiseHeatDivergence_contDiff` | `Carleman/Spatial/HeatIdentityRegularity.lean:46` | PASS。对 T145 同一原热通量 V 的实际 `Σᵢ DᵢVᵢ` 证明 C∞，没有另换边界通量。 |
| 14 | `Carleman.spaceTimeHeat_contDiff` | `Carleman/Spatial/BoxIntegratedHeatIdentity.lean:15` | PASS。通过真实时间切片导数及空间 Laplacian 的方向导数身份，证明原 `(∂t−Δ)u` 为 C∞。 |
| 15 | `Carleman.box_smooth_heat_carleman_inequality` | `Carleman/Spatial/BoxIntegratedHeatIdentity.lean:22` | PASS。内部定义同一 z、k、M、V，实际单调积分、时间通量零和空间通量非正共同推出完整 bulk 的积分不超过真实共轭热残差平方积分。全部量词和明确的光滑周期盒范围见下。 |

## 实际数学检查

**测度、可积性和时间端点。** Ω 为实际 `openCoordinateBox a b`。其有界性给闭包紧；有限闭时间区间与它的乘积紧。`Measure.prod_restrict` 将真实限制乘积测度识别为乘积 Lebesgue 测度在柱上的限制，再从闭柱可积性限制到开空间柱。证明没有借用 Lean 非可积时积分默认值来制造等式。全部最终 integrands 由 C∞ 推连续，再由第 2 项给可积性。已核对 pinned mathlib 的 `ContinuousOn.integrableOn_compact`、`Measure.prod_restrict`、`integral_prod` 和 `integral_prod_symm` 的实际前提及结论。

对时间通量使用的是 `smoothD (1,0) (pointwiseHeatTimeFlux e k z)`。先以实际 Fubini 将时间积分置内，利用 Ioc 与 Icc 对 Lebesgue 测度 a.e. 相同及 T≥0 的有向积分身份，再调用原周期 FTC。T146 的周期性来自真实平移微分保持，k 由 L、p 构造，z 由 exp(L)u 构造，故所消去的正是同一 `M=kz²−|∇z|²`，并非一个无关周期原函数。时间端点没有新增项；T=0 也合法，原 T>0 被包含。无时间长度倍数或隐含 T 常数。

**空间散度与真实面符号。** 阅读了固定 `SmoothBoxDivergence`、`BoxHeatFluxIntegral`、`BoxHeatBoundary`、`HalfspaceHeatBoundary`、`CoordinateBoxHalfspaces` 和 `ClosedCoordinateFaces`。实际空间切片方向导数把同一 V 的时空空间方向散度识别为真实盒内散度。Euclidean 与函数坐标之间使用保体积映射，真实 Fréchet 链式法则供应导数，紧盒连续性供应散度可积性，再调用 mathlib 实际散度定理；开闭盒通过真实 a.e. 身份转换。没有省略 Jacobian 或改用离散求和代替体积分。

真实上下坐标半空间的单位外法向分别为 ±坐标基向量。原 u 在 frontier 逐点为零，z=exp(L)u 也在那里为零；半空间面结论给同一 V·n≤0。面中点见证由正边长内部构造，实际通量连续性把相对开面符号推广到闭面全部点，包括棱角。上面 Vᵢ≤0，下面 −Vᵢ≤0；散度公式中的“上面减下面”因此非正，方向和减号正确。这只是在实际光滑盒上完成 Green 积分，不是一般多面体或弱法向迹定理。

**完整 bulk 与实际热残差。** 对真实方向族 eᵢ=(0,basisᵢ)，固定证明内定义

`z=exp(L)u`, `k=L_t+|∇L|²−ΔL−p`, `M=kz²−|∇z|²`，

`Vᵢ=2z_t zᵢ+4(∇L·∇z)zᵢ−2|∇z|²Lᵢ−2pzzᵢ+2kz²Lᵢ`。

原点态等式右侧有两个真实平方；T145 的不等式只舍去已证非负的 `(z_t+2∇L·∇z−pz)²`。本批 bulk 仍完整保留首个 `(Δz+kz)²`、矩阵双重和、负混合项及 Bz²。`spaceTimeHeat` 明确定义为实际时间切片 `deriv` 减实际空间 `spatialLaplacian`；原共轭消去 exp(−L)exp(L) 后保留同一输入 u。最终先得 `∫bulk≤∫R+∫M_t+∫divV`，再用 ∫M_t=0 和 ∫divV≤0 得 `∫bulk≤∫R`，其中 R=`(exp(L)(∂t−Δ)u)²`。积分单调性、可积加法和最后不等式方向均正确。

**量词和未完成范围。** 最终定理接受任意正边长盒、任意内部中心 c、T≥0、λ≥0，任意全时空 C∞ 的 L、p、u 及同一 `(T,0)` 平移周期；要求实际 `L(t,x)=q(t)ρ(x)`、所有时刻原 frontier 上 u=0，以及 q 在 [0,T] 非负。ρ 是真实 `exp(−λ‖x−c‖²)−2`。z、k 及通量不可由调用者任意替换；没有新增积分值、可积性、Fubini、Green 等式或目标估计前提。空间维数 d+1 覆盖全部正维，一维时横向面为零维；一般积分辅助引理也允许 d=0。最终常数严格为 1，没有从状态相关有限维连续性中取出声称统一的常数。

p 仍是任意光滑周期函数；本批没有完成原指定 Ψ 的系数估计。全时空 C∞、全局周期与逐点零边界是本批明确的准备范围，不能当成原完整弱轨道已覆盖。原 `eq:heatcross` 的实际系数和 Young 界、λ/β/qc 的选择、观测吸收、原 C² 时间权、完整 `H¹_t L²_x ∩ L²_t D(A)` 状态、一般凸多面体 Green、密度及另一时间方向仍待后续完成。本报告不将这些剩余义务登记为本批缺陷，也不把本批结果升级为完整 P024。

## 固定依赖及公理

递归读取这三个模块的 Carleman import 闭包，共 106 个文件；其中 103 个旧文件与 mathematical_base 逐文件内容完全相同。另按固定台账的既有 declaration_version 核对相关依赖闭包：

| 依赖 | 已验收 declaration_version | 本次比较入口和闭包 | 结论 |
|---|---|---|---|
| C161 | `ccbd7a887ed37afbc4d4e530d06b885350e74b3a` | `SpacetimeHeatIdentity`，81 文件 | 无变化 |
| C162 | `c598090a2e592f2e2a5441e5d05eaec994e9b1b3` | `PeriodicHeatFlux` / `PlaneHeatFlux`，并集 88 文件 | 无变化 |
| C163 | `e3a9cd6fa7134bdb9d924c56686a14d0bb64029d` | `HalfspaceHeatBoundary`，95 文件 | 无变化 |
| C164 | `a3a39eadfe9f18fee3bdd0a60b07cd5856bd3dbb` | `BoxHeatFluxIntegral`，102 文件 | 无变化 |

固定工具链为 Lean 4.35.0；实际 CI 报告 Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际 HEAD 相同且工作树干净。特别核对上述 Fubini、限制乘积测度、紧集可积性和 `integral_divergence_of_hasFDerivAt_off_countable'` 的实际 mathlib 源码。

读取固定原始公理文件全部显式记录：2771 个声明记录，其中 2762 个列出基础公理、9 个无公理；未知公理集合为空。本批十五项均仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。原始文件末行是 `Axiom audit passed for all 7494 Carleman declarations.`；2771 个显式输出记录与 7494 个递归审计声明是不同计数，未混用。未发现 sorryAx、未授权数学公理或未清偿的形式化替身假设。

## 实际构建与独立远端证据

实际读取固定本机 `/tmp/carleman-t149-integrated-heat-target.log`，最终目标 `Carleman.Spatial.BoxIntegratedHeatIdentity` 构建成功，3267 jobs；`-build.log` 中根目标 `Carleman` 完整构建成功，4008 jobs；`-axioms.log` 中递归审计 7494 声明通过。这是已存在固定日志的核验，未声称审查者另行重跑了本机构建。

审查者独立通过 GitHub API 查询同 SHA run **39235457780**、attempt **1**：整体 `completed/success`，head SHA 精确等于 checked_sha，updated_at 为 `2026-10-19T10:13:11Z`。三个实际 job 均 `completed/success`：

| Job | ID | 结果 |
|---|---|---|
| state-check | `118003325557` | success |
| lean | `118003325860` | success |
| dashboard / snapshot | `118004583252` | success |

正式 CI：[run 39235457780 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39235457780/attempts/1)。独立查询并用 `gh run download` 实际下载了该 run 的两个原始 artifact：

- `lean-ci-result`：artifact ID **12179915248**，下载到 `/tmp/carleman-t149-integrated-heat-main-ci/result.json`。实际 `status=PASS`，`checked_sha=source_head_sha=37d15b168e8c1ac3f313848be5a0c56594d2aad2`，`finished_at=2026-10-19T10:11:55.969309+00:00`，targets 为 `Carleman`，CI URL 精确属于上述同 run / attempt。
- `lean-declaration-evidence`：artifact ID **12179105710**，下载到 `/tmp/carleman-t149-integrated-heat-main-axioms/axioms.txt`。与固定 `/tmp/carleman-t149-integrated-heat-local-axioms.txt` **逐字节相同**：**2305083 bytes**，SHA256 **`8b89e3e3aa7a89e98a42f2d2c011f0beb48d5f6454e542b2b84d3a54e75b4c86`**。远端末行同为全部 7494 声明递归审计通过。

## 签发结论

固定版本十五项声明全部 **PASS**，没有需阻断 C165 AUXILIARY 验收的数学或证据缺陷。真实可积性、Fubini、周期 FTC、盒散度积分、原残差及全部 bulk 项均已核对；完整连续 CE 所需系数估计、吸收与弱轨道扩展仍明确未完成。仅签发本报告并单独提交；不修改数学、根导入、公理检查程序、台账或原稿，不推送。签发后冻结 reviewed_at 和报告内容。
