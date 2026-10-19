# T146 / C162 独立本机验收

- checked_sha / source_sha：`c598090a2e592f2e2a5441e5d05eaec994e9b1b3`
- base_commit：`ccbd7a887ed37afbc4d4e530d06b885350e74b3a`
- reviewed_at：`2026-10-19T09:48:42+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_foundations`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；15/15 项声明通过。
- scope：**AUXILIARY — 光滑准备步骤**。C162 可登记 REVIEWED；P024 / `prop:continuousCE` 不提升，原文覆盖保持 **17/26**。

审查从固定 Git 对象读取三个新模块的全部实际定义与证明、原稿 `prop:continuousCE` 及其证明、T146 分析、MATH_SPEC 和固定台账；并逐项读取固定原始产物中的全部 15 项完整展开类型。相关旧通量、共轭、实际时空方向导数、高斯权与法向符号证明另从固定源码核查。执行者说明和 CI 没有代替数学审查。未来工作树增量和动态 `.ci/axioms.txt` 均排除；只新增并单独提交本报告，不改数学、台账、导入或原稿，不 push。

## 原稿对应和范围

原 `paper/main.tex` 的 `prop:continuousCE` 证明先取光滑周期状态，设置 `z=exp(ℓ)v`、`ℓ=qρ`，其中 `ρ=exp(−λ|x−c|²)−2`；随后使用总时间导数的周期抵消和每个面上 `2q∂νφ|∂νz|²≤0`，再通过 Green 积分、系数估计、吸收、密度和时间反射完成完整结论。

本批完成其中两个确切的光滑步骤：对同一实际 M 的时间切片证明积分零；在真实局部平面零值及单位法向条件下，将同一实际 V 的法向分量识别为 `2D_nℓ(D_nz)²`，再以实际 Gaussian 权和明确支持半空间条件证明非正。它不提供原多面体面几何、棱角在面测度下零测、面法向迹或 Green/散度积分，不将全时空 C∞ 周期函数换成原 C² 时间权或完整 Sobolev 轨道，也尚未提供系数吸收、密度或两方向最终 CE。

固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改稿。上述剩余义务限制的是本批验收范围，不是对原完整命题的完成认定。

## 全部 15 项声明

清单与固定 C162 `lean_declarations`、`/tmp/carleman-t146-heat-flux-declarations.json` 完全一致。三模块均被固定 `Carleman.lean` 导入；各项均有固定 `tools/CheckAxioms.lean` 中的 `#check @...` 和 `#print axioms ...`，并实际出现于独立下载的远端原始产物。下表位置前缀为 `Carleman/`，均指 checked_sha。

| # | 完整声明 | 固定源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `Carleman.smoothD_periodic` | `Spatial/PeriodicHeatFlux.lean:15` | PASS；真实平移复合的 fderiv 等式从 f 周期性推出全部固定方向导数周期性，不预设导数周期。 |
| 2 | `Carleman.directionalLap_periodic` | `Spatial/PeriodicHeatFlux.lean:22` | PASS；逐方向两次应用前项，再对实际二阶导数求和。 |
| 3 | `Carleman.directionalEnergy_periodic` | `Spatial/PeriodicHeatFlux.lean:27` | PASS；真实方向导数平方和保持同一周期。 |
| 4 | `Carleman.heatConjugationK_periodic` | `Spatial/PeriodicHeatFlux.lean:32` | PASS；实际 k=ℓ_t+|∇ℓ|²−Δℓ−p 由同一 ℓ、p 的周期性获得周期。 |
| 5 | `Carleman.pointwiseHeatTimeFlux_contDiff` | `Spatial/PeriodicHeatFlux.lean:39` | PASS；真实 M=kz²−|∇z|² 的光滑性由实际乘积和导数光滑性给出。 |
| 6 | `Carleman.pointwiseHeatTimeFlux_periodic` | `Spatial/PeriodicHeatFlux.lean:44` | PASS；同一 M 的真实周期性，没有替换通量。 |
| 7 | `Carleman.spacetime_periodic_derivative_integral` | `Spatial/PeriodicHeatFlux.lean:50` | PASS；实际时间切片链式法则与 FTC 给 ∫₀ᵀD_tf=f(T,x)−f(0,x)=0；导数可积性内部提供。 |
| 8 | `Carleman.spacetime_heat_time_flux_integral` | `Spatial/PeriodicHeatFlux.lean:62` | PASS；内部定义 z=exp(ℓ)u 和同一 k，供应 M 的光滑/周期资格，对每个 x 给实际 M_t 积分零。 |
| 9 | `Carleman.smooth_plane_tangent_derivative` | `Spatial/SmoothPlaneBoundary.lean:14` | PASS；局部平面内曲线 x+sv 的实际邻域零值与真实导数比较推出切向导数零。 |
| 10 | `Carleman.smooth_plane_normal_derivative` | `Spatial/SmoothPlaneBoundary.lean:37` | PASS；单位 n 下对 v−⟨v,n⟩n 使用切向结论，得到真实 Fréchet 导数法向表示。 |
| 11 | `Carleman.spacetime_plane_zero_derivatives` | `Spatial/SmoothPlaneBoundary.lean:49` | PASS；每个时间的局部平面零值给 z(t,x)=0、实际时间导数零及全部空间坐标导数法向身份。 |
| 12 | `Carleman.spacetime_directional_normal_sum` | `Spatial/PlaneHeatFlux.lean:13` | PASS；实际 Euclidean 基展开和 fderiv 的线性性识别坐标收缩为 D_(0,n)。 |
| 13 | `Carleman.pointwiseHeatFlux_normal_eq` | `Spatial/PlaneHeatFlux.lean:31` | PASS；对原 V 全部五项逐项代入，单位法向平方和为 1，准确保留系数 2。 |
| 14 | `Carleman.smooth_plane_heat_flux` | `Spatial/PlaneHeatFlux.lean:55` | PASS；切向/时间导数条件内部从真实局部零边值推出，最终 a 是实际空间切片法向导数。 |
| 15 | `Carleman.gaussian_plane_heat_flux_nonpos` | `Spatial/PlaneHeatFlux.lean:64` | PASS；实际 L(t,y)=q(t)ρ(y) 空间链式法则、真实 Gaussian 法向导数及支持半空间给同一 V·n≤0。 |

## 数学审查依据

**真实导数与周期抵消。** `smoothD e f x` 的定义就是 `fderiv ℝ f x e`。新周期证明使用真实函数恒等式 `f(·+a)=f` 与 mathlib `fderiv_comp_add_right`，而非把导数周期性另列假设。已读取 pinned mathlib 中该平移导数定理，其结论确实是完整 fderiv 的平移身份；它对 total fderiv 成立，后续 FTC 的实际使用则明确在 C∞ 函数上。二阶方向和、导数平方和、k、M 的周期性都由这条链内部推出。

`spacetime_periodic_derivative_integral` 将全时空光滑函数限制到实际曲线 t↦(t,x)，使用 `spaceTime_timeD` 识别 D_(1,0) 与一维 deriv。切片光滑性给导数连续，进而给任意有限区间的真实 interval integrability；mathlib `intervalIntegral.integral_deriv_eq_sub` 的可微和可积前提均内部供应。最后对 (0,x) 应用 `(T,0)` 平移周期性，端点顺序为 f(T,x)−f(0,x)，准确为零。声明允许任意实数 T，使用有向区间积分；原 T>0 被包含，T=0 也无除法问题。

最终时间通量引理的 `let z := exp(ℓ)u` 和 `let k := heatConjugationK ... ℓ p` 与 T145 的真实时空恒等式完全相同。z 周期性由 exp 复合与乘法推出，k 周期性和光滑性由同一 ℓ、p 推出；没有外给 M、M_t 或它们的可积性/周期性。但结论目前是每个固定 x 的时间积分，并未证明时空 Fubini 或整体空间可积性。输入是全时空 C∞ 的 ℓ、p、u 及全局平移周期性，不能据此声称原 C² q 和弱轨道的端点传递已完成。

**真实局部平面零值推出导数条件。** 切向引理假设实际半径 r>0 内、满足 ⟨y−x,n⟩=0 的每一点 f(y)=0。曲线 x+sv 在 s=0 邻域留在该球，且 ⟨v,n⟩=0 保证它始终位于平面。代码先证明曲线上的函数与常零函数在真实邻域 eventually equal，再用真实 HasDerivAt 链式法则和 deriv 的局部相等性得到 Df(x)v=0；没有从单点 f(x)=0 推出导数零。

单位法向给 ⟨n,n⟩=1，所以 v−⟨v,n⟩n 真正切向；fderiv 线性性于是给 Df(x)v=Df(x)n⟨v,n⟩。时空版本使用对所有 s 的平面零值，先得 z(s,x)=0 的真实恒等函数，再推出时间导数零；空间切片是同一光滑 z 的实际切片，逐基方向得到 D_i z=(∂_n z)n_i。半径和法向条件没有被省略，也未用弱迹、a.e. 边值或边界零测替代这些点态前提。

**同一 V 的五项与系数 2。** 已读取 T145 的实际 `PointwiseHeatIdentity`、`PointwiseHeatConjugation` 和 `SpacetimeHeatIdentity`。原通量的第 i 分量为

`V_i=2z_t z_i + 4(∇ℓ·∇z)z_i − 2|∇z|²ℓ_i − 2pzz_i + 2kz²ℓ_i`。

新引理没有替换 V 或把法向通量当成定义。以 a=∂_n z、z_i=a n_i 代入，真实 Euclidean 单位范数给 ∑n_i²=1、|∇z|²=a²；真实坐标展开给 ∑ℓ_i n_i=D_nℓ，因此 ∇ℓ·∇z=aD_nℓ。第一项由 z_t=0 消失，第四、第五项由 z=0 消失；第二项的法向和为 4a²D_nℓ，第三项为 −2a²D_nℓ，合成精确 `2D_nℓ·a²`。p、k 项确已实际消失，没有遗漏 Ψ 或 ℓ_t+A 的贡献。

坐标收缩引理本身只是实际 fderiv 连续线性映射对 Euclidean 基展开的线性恒等式，所以无须另假设 f 可微；最终高斯 L 与状态 z 明确光滑，法向导数均为真实经典导数。通量代数引理允许任意 k、p，这是由于其边界项含 z 而消失；它当然适用于 T145 的指定 `k=heatConjugationK` 和指定 Ψ，并非更换原共轭数据。平面引理对任意光滑 z 成立，因而可用于 T145 的 z=exp(ℓ)u；从原 u 的边界条件供应其平面零值仍属于后续几何/边界衔接。

**实际 Gaussian 权和法向方向。** `interiorQuadratic c x=−‖x−c‖²`、`interiorGaussian c λ x=exp(−λ‖x−c‖²)`、`interiorCarlemanProfile=interiorGaussian−2` 的实际导数已从固定旧源码核查。对固定 t，函数身份 L(t,y)=q(t)ρ(y) 与实际空间 fderiv 常数乘法给 `D_nL=q(t)D_nρ=q(t)D_nφ`。实际公式为 `D_nφ=−2λφ⟨x−c,n⟩`。

支持半空间条件是对所有 y∈S 有 ⟨y−x,n⟩≤0；由 c∈S 得 ⟨x−c,n⟩≥0。故 λ≥0、φ>0 给 D_nφ≤0，再以 q(t)≥0、法向导数平方非负得到 V·n≤0。法向方向与原外侧支持面一致，没有把符号反转。λ=0 或 q(t)=0 也合法给零通量，未除以这些量。本批不需要更强凸性输入，因为它明确要求所用支持半空间条件；该条件尚未从原每个面自动构造。

**量词与适用边界。** 时间结论对任意固定空间点、任意实 T 成立，恒等式没有隐藏常数或 T 因子。平面结论允许任意空间维数、平移、半径和单位法向；d=0 时不存在单位法向，带该前提的面结论为空适用情形，未虚构零维面。局部平面零值假设对应面的相对内部，不覆盖棱角或任意曲面。`gaussian_plane_heat_flux_nonpos` 明确保留 L、z 的全时空光滑性、实际乘积公式、局部零值和支持面条件；没有声称原 qclass 的 C² 权自动满足 C∞ 前提。原面几何、棱角面零测、Green 积分、完整弱轨道、吸收、密度与最终时间反射仍待证明，P024 不因此提升。

## 依赖版本、公理与构建

三新模块的 `Carleman` import 递归闭包共 **88** 模块，其中 **85** 个旧模块与固定 base 逐文件相同。基线至 proof 的数学增量仅这三模块及根导入/检查登记，原稿未变。关键依赖的完整 import 闭包另外与其已验收版本逐文件比较：

| 依赖 | declaration_version | 核查根 / 模块数 | 结论 |
|---|---|---|---|
| C161 | `ccbd7a887ed37afbc4d4e530d06b885350e74b3a` | `Spatial/SpacetimeHeatIdentity` / 81 | 全部相同 |
| C160 | `2cd92104c803b6a2e586be26a9685e4b2c7fc976` | `Weights/InteriorGaussianGeometry` / 30 | 全部相同 |

Lean 固定为 `leanprover/lean4:v4.35.0`，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；本机实际版本与远端 result 相符。mathlib 固定为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际 checkout 同 SHA 且无修改。新增依赖使用真实 interval FTC、平移导数、局部导数比较和 Euclidean 基展开，没有新增数学公理。

固定 raw 中独立解析到 **2,729** 条显式公理记录：**2,720** 条仅依赖正常基础公理子集，**9** 条无公理；未发现 `{propext, Classical.choice, Quot.sound}` 之外的公理。15 项本批声明均实际存在。末行是 `Axiom audit passed for all 7434 Carleman declarations.`，覆盖 **7,434** 项递归声明，没有 `sorryAx`。

已实际读取 `/tmp/carleman-t146-flux-target.log`（记录 `PlaneHeatFlux` 最终定向构建成功，**3,235 jobs**）、`/tmp/carleman-t146-heat-flux-build.log`（全库 **3,984 jobs** 成功）以及 `/tmp/carleman-t146-heat-flux-axioms.log`（7,434 项递归审计通过）。全部 15 项还由固定完整原始公理产物覆盖。这里核对的是已存在的固定日志，不声称另行重跑全库。

## 同 SHA 正式 CI 与独立下载

本人独立查询的 [run 39232361430 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39232361430/attempts/1) 为 main 的 push；head SHA 精确为 `c598090a2e592f2e2a5441e5d05eaec994e9b1b3`，run 已 `completed/success`，更新于 `2026-10-19T09:48:09Z`。三个实际 jobs 最终均成功：

| job | ID | 状态 |
|---|---|---|
| lean | `117993114221` | completed / success |
| state-check | `117993114698` | completed / success |
| dashboard / snapshot | `117994425090` | completed / success |

本人通过 `gh run download` 从该 run 独立下载两个原始 artifacts：

| artifact | ID | 独立下载位置 |
|---|---|---|
| lean-ci-result | `12177321706` | `/tmp/carleman-t146-heat-flux-main-ci/result.json` |
| lean-declaration-evidence | `12177162006` | `/tmp/carleman-t146-heat-flux-main-axioms/axioms.txt` |

实际 result 为 `status=PASS`，`checked_sha=source_head_sha=c598090a2e592f2e2a5441e5d05eaec994e9b1b3`，`finished_at=2026-10-19T09:46:53.259026+00:00`，target 为 `Carleman`。远端原始 axioms 与固定 `/tmp/carleman-t146-heat-flux-local-axioms.txt` 独立逐字节比较完全相同：均 **2,282,036 bytes**，SHA256 均为 **`5dce33f39402802d64ecc051d33d8afb07af31bac8c90f014c7a4432ab930018`**。

## 签发

T146/C162 在固定版本上通过实际数学、全部类型、依赖版本、公理及正式同 SHA CI 的独立验收，可登记 REVIEWED / AUXILIARY。未发现阻断性缺陷。结论严格限于上述光滑周期时间通量和平面边界通量步骤；P024 与原文完成数保持不变。仅单独提交本报告，通知主 Agent 后冻结内容和签发时间。
