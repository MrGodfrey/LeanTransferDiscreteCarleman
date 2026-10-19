# T125 / C141 独立本机验收

- checked_sha: `ed02ecc45e5edf8cb96085c4aff7e5da38397bcf`
- base_commit: `f3e3ddb8621286134d4560b73a682b495d0c0907`
- reviewed_at: `2026-10-19T06:17:02+00:00`
- reviewer: `/root/accept_spatial_foundations`，独立本机验收 Agent。
- result: **PASS**；axiom_check: **PASS**。
- scope: **AUXILIARY**。可将 C141 在上述固定版本登记为 REVIEWED；不提升 P011 / `prop:p1`，原文完成数保持 **14/26**。

本报告从固定 Git 对象读取全部三模块、原 `paper/main.tex`、T125 分析、MATH_SPEC、台账及关键依赖，逐条检查实际证明和展开类型；执行者说明与 CI 不替代语义验收。只写本报告，未改实现、台账、根导入或原稿，未提交或推送。后续工作树及变化中的 `.ci/axioms.txt` 不参与验收。

## 全部三项声明

下表路径及行号均属于 checked_sha。三项均在固定 `Carleman.lean` 中通过对应模块导入，并在 `tools/CheckAxioms.lean` 中同时列有 `#check @...` 和 `#print axioms ...`。独立下载的原始证据实际包含全部展开类型；与声明 JSON、C141 台账一致。

| # | 完整声明 | 固定源码位置 | 逐项结论 |
|---|---|---|---|
| 1 | `Carleman.SimplicialPartition.cellWeight_mesh_power_le` | `Carleman/Spatial/MaxDiameterWeight.lean:15` | PASS。对任意实际有限分割、任意 Hilbert 值 L² 输入及自然数 p，由真实上尺度 ℓᵢ≤B diam(Kᵢ) 推出 cellWeight 范数≤(B h)ᵖ 倍原权范数。 |
| 2 | `Carleman.weak_h2_allowed_projection_approximation` | `Carleman/Spatial/WeakH2ProjectionApproximation.lean:15` | PASS。对全部原弱 H²∩H¹₀ 输入，真实完整 P1 正交投影的同一误差 jet 先于权族选定；给出统一 Ch² 值误差和完整 Ch 能量误差。 |
| 3 | `Carleman.full_p1_weightedApproximation_interface` | `Carleman/Spatial/FullP1ApproximationInterface.lean:14` | PASS。对任意明确满足 D⊆H²、D⊆H¹₀ 的原域子空间及同一实际 conforming R/J/Q，证明原 `Section4.WeightedApproximation`，aE=Ch、a0=Ch²。 |

## 原命题、实际对象与量词

直接对照原稿 1469–1500 行的固定有界凸多面体、形状正则网格、真实最大单元直径、上下 ℓ 尺度及共享顶点分级；1532–1565 行的 P1 Step 2；304–313 行的完整 N/R 范数；419、445–451 行的全部允许权及 N3。形式化覆盖 d≤3，故包含原 d=2,3。域采用开、凸、紧闭包，C¹ profile 条件包含原光滑 profile。有限体积实例明确出现于类型；它由紧闭包和 Lebesgue 测度的紧集有限性保证，并非新增可积性假设。

`SimplicialPartition` 的单元为真实非退化 d 单纯形，位于 closure S、覆盖 S，内部两两不交；FaceMatching 和 BoundaryFitted 是实际网格条件。`conformingSpace (dirichletSubspace S)` 是全部原 H¹₀ 中逐单元 a.e. 仿射的 L² 子空间，非预先挑选的节点子空间。其真实有限维性提供闭性和 L² 正交投影存在；最终估计常数未从任意有限维范数等价或自动连续性提取。

第 2、3 项的量词均为：固定 d、S、profile、κ、c、B、γ 及其正性和 γ<Γd 后，先有 δ>0、δ≤1、C>0；再量化全部有限索引、网格、内球、局部尺度、原状态或 D、TimeWeight、TimeGrid、实幂、时刻和符号。共享顶点条件对所有有序 i,j 成立；配合邻接对称性与 ℓ>0，正是原双侧比例条件。Γd 是实际 `(sqrt(d+2)+1)/(sqrt(d+2)-1)`，没有以 mesh γ 代替有效权分级。

实际权为 `σ=(ρ.scaled η).multiplier w τ t`，即 q(t)^τ exp(η q(t)ρ)，|η|=1 覆盖两种符号，τ 任意实数因而包含原规定的有界幂族。逆权仍在此族中，由同时取 −τ、−η 得到。估计没有依赖时间方向；点态结论对所有实 t 成立，最终接口覆盖原整个闭周期，包含全部节点与两端点。

## 数学证明核查

**1. 真实上下尺度与网格幂。** `cellDiameter` 是 `Metric.diam (M.cell i)`，`maxDiameter` 是这些非负数的真实有限上确界，空索引取 0。`cellWeight` 通过实际分片乘子定义，且在各单元 a.e. 等于 ℓᵢᵖσ；既有 `cellWeight_sq_sum` / `cellWeight_seminorm_le` 使用真实积分的精确分割。第 1 项由 0≤ℓᵢ≤B diam(Kᵢ)≤B h，取自然幂并逐项比较积分。没有单元数量或体积常数，也没有除以 h；p=0 与零尺度情况遵循实际自然幂语义。主结论中的 ℓ>0、c,B>0 是原网格尺度条件，未额外假定 h>0。

主证明将下尺度 `c*diam(Kᵢ)≤ℓᵢ` 用 c>0 精确转换为 `diam(Kᵢ)≤c⁻¹*ℓᵢ`，输入既有节点插值定理。上尺度输入新的 mesh-power 界及真实逆估计。二者方向不同且均用到了；没有从单一上界偷推出双侧比较。

**2. 同一原状态、同一插值与投影误差。** `weak_h2_allowed_nodal_approximation` 从全部原弱 H²∩H¹₀ 输入内部供应同一 closure S 连续代表 f、全部边界点零值、真实 I_h f∈Vh，以及原 H¹₀ error jet e，value(e)=value(u)−I_h f。它及前一层 `exists_weak_h2_conforming_nodal_error` 的实际类型没有把连续代表、边界零、局部误差或可积性作为新增前提；弱 H²、原 H¹₀ 图闭包及网格条件足够。

设 X=完整 Vh，pe=Π_X(value e)。由 pe∈X⊆原 H¹₀ 的定义取得真实 H¹₀ jet p，value(p)=pe。令 E=p−e，原 H¹₀ jet 空间对差封闭。`projection_error_of_residual` 对实际 L² 正交投影用线性和 Π_X(I_h f)=I_h f，精确证明 value(E)=Π_X(value u)−value u。E 在全部 w、τ、t、η 之前存在，不随权族选择；不是只为某个权作出的替身。其梯度是原弱导数字段，未将标量范数数据当作 H¹ 误差。

**3. 权投影、逆估计及常数。** 既有完整空间投影界分别用于 σ 和 ℓ⁻¹σ，同一个 Cp 控制实际 Π_X(value e)。`allowed_weight_full_projection` 已在内部供应完整 Vh 的节点表示与边界数据，没有重新假设投影输出的节点表示。其常数先于网格，依赖有效权等级 θ=(γ+Γd)/2<Γd；具体构造为 `θ^3*(d+2)/p1MassMargin d θ`。CI 来自原完整 conforming 弱 H¹ 状态的真实加权逆估计；局部仿射梯度、精确单元积分及 ℓᵢ≤Bκrᵢ 给该界，没有额外状态限制。

令 H=‖σ field₂(u)‖、h=maxDiameter。既有节点估计及第 1 项分别给出

\[
\|\sigma e\|\le C_E B^2h^2H,\qquad
\|\sigma\nabla e\|+\|\ell^{-1}\sigma e\|\le C_E BhH.
\]

这里 C_E 取自固定 κ、c⁻¹、域/profile 和维数的节点定理。σ 与 ℓ⁻¹σ 投影稳定性、逆估计给 `weak_projected_residual_estimate` 的真实三个输入，故

\[
\mathcal N_\sigma(E)\le
\|\sigma\nabla e\|+C_I C_p\|\ell^{-1}\sigma e\|
+(1+C_p)q\|\sigma e\|.
\]

这是完整梯度和 q 加权值组成的原 N 范数，不是仅梯度半范数。`maxDiameter_mul_q_le` 只用实际 q(t)≤w.max 与 h≥0，推得 hq(t)≤δ≤1；因此 q‖σe‖≤C_E B²hH，无需除以 h。源码常数准确为

\[
C_0=(1+C_p)C_EB^2,\qquad
C_1=(1+C_IC_p)C_EB+(1+C_p)C_EB^2,\qquad C=1+C_0+C_1>0.
\]

C 同时支配两项误差，先于全部网格、状态、时间权与实幂选择。没有 T、节点数、单元数、最小网格尺度或状态相关常数进入最终 C。各项乘法比较明确使用非负性；零 Hessian 能量的情况直接包含，不作除法。

**4. 原 N3、真实 R/J 与符号。** `Physical.conformingReconstruction` 的 R 是 X→H¹₀ 的实际包含，J 是同一 L² 正交投影；RH 是 L² 包含，Q=RJ，故 RH(Jv)=Π_X v。第 3 项对每个 v:D 使用 `domainSobolevJet`，其 value 恰为原 L² 状态 v。经原开域上的 `WeakSobolevJet.value_injective`，−E 正好是 v−Qv 的 canonical H¹ jet；此步骤恢复全部弱字段，未仅对齐 zeroth field 后直接假定梯度相同。原 `weightedNorm_neg` 逐字段证明负号不改变 N，L² 乘子 seminorm 亦用实际偶性。论文方向是 v−Π_hv，与上一项的 E=Π_hv−v 在此显式转正。

原 `parameterNorm` 是所有 k=0,1,2 的 q^(2−k) 加权 L² 范数之和。其第 2 项系数为 q⁰=1，非负项比较给 H≤Rσ(v)，所以同一 C 给出 aE=Ch、a0=Ch²。实际 `WeightedApproximation` 两字段分别量化所有 t∈[0,g.period] 与 v:D；源码先证明任意实 t，再填这两个字段，未只验证节点、有限状态或某一时间方向。h≥0 与 C>0 保证两个误差尺度非负。

## 固定依赖版本与公理

递归读取三模块的全部 Carleman import 闭包，共 **498** 个模块；其中 **495** 个既有模块与 base 逐文件相同。另对关键已 REVIEWED 的 declaration_version 分别重新比对其当前递归闭包：C140 `WeakH2AllowedNodal` 222 个模块与 `f3e3ddb8621286134d4560b73a682b495d0c0907` 相同；C139 `WeakH2ConformingNodal` 207 个与 `e56df9d1895554e8cdfacc7e52c86bac51a08e6c` 相同；C074 `FullWeightedProjection` 161 个与 `9b4962ef9d03bb7bce6cc906a508857d57398c8c` 相同；C066 `ConformingAllowedInverse` 92 个与 `9ea552502177ccffb3f50593567578fc207c2568` 相同；C082 `WeakProjectionResidual` 166 个与 `1f04be4f79db9d40ac1af37271eb8e9dc58639a3` 相同。没有以旧审查结论覆盖已变化的数学依赖。

三项实际展开类型的公理均仅为 `propext`、`Classical.choice`、`Quot.sound`。对下载原始文件中全部 **2360** 条显式公理输出复查：2352 条仅使用该正常基础集合，8 条不依赖公理，无异常公理；其末行是 **6743** 项 Carleman 声明递归审计 PASS。显式打印条数与递归审计总数是不同统计。未发现 `sorryAx` 或未证明的数学公理。

固定 Lean toolchain 为 4.35.0；远端结果记录编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。固定 manifest 与本机干净 mathlib checkout 一致，提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿未改，其 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 实际构建、远端 CI 与原始证据

实际读取 `/tmp/carleman-p1-approx-target.log` 的 3711 jobs 成功和 `/tmp/carleman-p1-approx-full.log` 的 3887 jobs 成功及完整审计尾部。这是对已有固定日志的核验，本验收未声称重新运行全库构建。

独立通过 GitHub API 查询固定 main [run 39208420555 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39208420555/attempts/1)：head SHA 精确匹配 checked_sha，最终 run 为 completed/success，三个实际作业全部 completed/success：state-check `117916205431`，lean `117916205676`，dashboard / snapshot `117917378059`。不是仅凭 proof build 子步骤或执行者消息认定完成。

独立查询 artifact 元数据并使用 `gh run download` 下载该 run 的 `lean-ci-result`（artifact ID **12166394100**）至 `/tmp/carleman-p1-approx-main-ci/result.json`，以及 `lean-declaration-evidence`（artifact ID **12166876173**）至 `/tmp/carleman-p1-approx-main-axioms/axioms.txt`。实际 result 为 PASS，`checked_sha` 与 `source_head_sha` 均为本报告完整 SHA，`finished_at=2026-10-19T06:13:40.587931+00:00`，target 为 `Carleman`。

独立逐字节比较远端原始 axioms 与固定 `/tmp/carleman-p1-approx-local-axioms.txt`：完全相同，均为 **2,070,769 bytes**，原始文件 SHA256 均为 **`dc0904cf0618ed061e9f64ee2a0f8fc6109195e6b03eb858a85a87eb51a31d9d`**。该摘要针对实际 axioms 文本，不混同 artifact ZIP 的摘要。

## 结论与范围

三项声明均通过固定版本独立语义、依赖、公理和同 SHA 正式 CI 验收；未发现阻断缺陷。C141 可在 checked_sha 升级为 **REVIEWED / AUXILIARY**，认定原完整 P1 空间的 Step 2 投影 h²/h 误差及原 N3 接口已证明。

第 3 项明确保留 `hD : D ≤ sobolevSubspace d 2 ...` 与 `hDV : D ≤ dirichletSubspace S`。取真实算子域时必须供应原 A1 的 D(A)⊆H² 及 D(A)⊆H¹₀；本批没有证明具体 Dirichlet Laplacian 的 H² 正则性或其定量椭圆估计。完整 P1 命题还需与原控制空间及其余数值接口组合，本批也不证明连续 Carleman 估计。因此 P011 与 PAPER 完成数不变。报告签发后冻结内容及时间。
