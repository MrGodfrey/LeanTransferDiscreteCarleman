# T145 / C161 独立本机验收

- `checked_sha`: `ccbd7a887ed37afbc4d4e530d06b885350e74b3a`
- `base_commit`: `2cd92104c803b6a2e586be26a9685e4b2c7fc976`
- `reviewed_at`: `2026-10-19T09:41:30+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实全空间 C∞ 实函数的热算子点态恒等式、指数共轭及原 Fu–Lü–Zhang Corollary 3.1 在 p=Id、Φ=0 下的光滑特例。**不构成完整 P024 / prop:continuousCE，原文覆盖保持 17/26。**

本 Agent 直接读取固定 Git 对象中五模块全部定义、证明和 53 项完整展开类型，核对固定 MATH_SPEC、分析、台账清单、AGENTS、PROJECT_OPERATIONS 和 state/README。独立查阅原稿与本地原书，核对旧依赖版本，并自行查询、下载同一 main CI 的原始工件。执行者说明、旧报告和 CI 均未替代数学判断。后续 T146 工作树和动态 `.ci/axioms.txt` 不属于本次依据。

## 原文定位与范围

固定 `paper/main.tex:2672–2731` 的完整 `prop:continuousCE` 要求原允许 C² 时间权、任意 T>0、两时间方向、全部 H¹(0,T;H)∩L²(0,T;D(A)) 周期轨道，并含真实时空积分、观察项与统一常数。本阶段对应其 `2681–2703` 引用点态不等式的准备步骤。原稿 `2704` 的周期和边界积分、`2706–2727` 的具体权系数估计与吸收、`2730` 的密度与时间反射均未由本批供应。

已独立打开并渲染本地原书 [Fu–Lü–Zhang (2019)](</Users/wangyu/Documents/math/article/fu2019carleman-Carleman estimates for second order partial differential operators and applications.pdf>) 的 **PDF 第 69 页 / 印刷第 60 页**，目视核对 Corollary 3.1 的 (3.3)–(3.5)，并核对 PDF 第 17 页 (1.13) 的 θ=exp(ℓ)、v=θz。原书的未加权 z 对应本批 u，原书加权 v 对应本批 z；Lean 参数 `p` 对应原 Ψ，并不是扩散系数矩阵 p^{jk}。原页由本 Agent 另行渲染为 `/tmp/carleman-t145-review-fu69.png`，也与提供的 `/tmp/carleman-fu2019-cor31.png` 对照。

本批使用全空间 C∞ 假设，比原书及原稿最终正则性要求更强。该限制作为 AUXILIARY 阶段明确接受，不能从本报告推断原 C² 时间权或全部 Sobolev 轨道已经覆盖；原允许权 ℓ=qρ 及 Ψ=−Δℓ−8qλφ 的实例也尚未供应。没有加入目标点态恒等式作为假设，没有假定任意命名字段等于导数；所有微分都是实际 fderiv/deriv。

## 全部 53 项声明

声明名称省略 `Carleman.`；源文件均在 `Carleman/Spatial/`。表中源行以固定提交为准，完整类型行以本次独立下载且逐字节比对的 `axioms.txt` 为准。顺序与固定 C161/T145 台账和交付清单一致。

| # | 声明 | 固定源位置 / 完整类型行 | 独立结论 |
|---|---|---|---|
| 1 | `smoothD` | `SmoothDirectionalCalculus.lean:13` / 29322 | PASS；实际 fderiv 在常方向上的求值，无候选导数字段。 |
| 2 | `smoothD_contDiff` | `SmoothDirectionalCalculus.lean:15` / 29324 | PASS；由真实 fderiv 的光滑性和 CLM 求值得到同一方向导数 C∞。 |
| 3 | `smoothD_add` | `SmoothDirectionalCalculus.lean:19` / 29327 | PASS；两实际光滑函数的加法导数。 |
| 4 | `smoothD_sub` | `SmoothDirectionalCalculus.lean:25` / 29332 | PASS；两实际光滑函数的减法导数。 |
| 5 | `smoothD_neg` | `SmoothDirectionalCalculus.lean:31` / 29337 | PASS；实际 fderiv_neg；无需原函数可微的较广版本仍成立。 |
| 6 | `smoothD_mul` | `SmoothDirectionalCalculus.lean:37` / 29340 | PASS；实际乘积法则，两项均保留。 |
| 7 | `smoothD_const_mul` | `SmoothDirectionalCalculus.lean:45` / 29346 | PASS；实常数乘子可提出方向微分。 |
| 8 | `smoothD_sq` | `SmoothDirectionalCalculus.lean:49` / 29349 | PASS；实际平方导数为 2fDₑf。 |
| 9 | `smoothD_sum` | `SmoothDirectionalCalculus.lean:54` / 29352 | PASS；任意有限和逐项求导，光滑假设覆盖和内全部项。 |
| 10 | `smoothD_comm` | `SmoothDirectionalCalculus.lean:61` / 29357 | PASS；用实际二阶 Fréchet 导数对称性证明常方向交换。 |
| 11 | `directionalLap` | `SmoothDirectionalEnergy.lean:14` / 29361 | PASS；实际纯二阶方向导数的有限和。 |
| 12 | `directionalPair` | `SmoothDirectionalEnergy.lean:17` / 29364 | PASS；实际一阶方向导数乘积的有限和。 |
| 13 | `directionalEnergy` | `SmoothDirectionalEnergy.lean:20` / 29367 | PASS；实际方向导数平方和。 |
| 14 | `directionalHessianForm` | `SmoothDirectionalEnergy.lean:23` / 29370 | PASS；真实 Hessian 分量与同一 g 的两个方向导数收缩。 |
| 15 | `directionalLap_contDiff` | `SmoothDirectionalEnergy.lean:26` / 29373 | PASS；逐项二次求导及有限和保持 C∞。 |
| 16 | `directionalPair_contDiff` | `SmoothDirectionalEnergy.lean:30` / 29377 | PASS；两个真实一阶导数乘积的有限和保持 C∞。 |
| 17 | `directionalEnergy_contDiff` | `SmoothDirectionalEnergy.lean:35` / 29381 | PASS；真实一阶导数平方和保持 C∞。 |
| 18 | `smoothD_directionalPair` | `SmoothDirectionalEnergy.lean:39` / 29385 | PASS；对真实方向配对求导，两个乘积项均保留。 |
| 19 | `smoothD_directionalEnergy` | `SmoothDirectionalEnergy.lean:49` / 29395 | PASS；能量求导的系数 2 正确。 |
| 20 | `directional_transport_cancellation` | `SmoothDirectionalEnergy.lean:60` / 29402 | PASS；通过双和换序和 g 的混合导数交换，精确消去输运交叉项。 |
| 21 | `directionalPair_comm` | `SmoothDirectionalEnergy.lean:89` / 29411 | PASS；方向配对的实乘积交换性。 |
| 22 | `directionalPair_mul_left` | `SmoothDirectionalEnergy.lean:93` / 29415 | PASS；左因子乘积法则；未要求无需求导的第三输入额外光滑。 |
| 23 | `directionalPair_sq_left` | `SmoothDirectionalEnergy.lean:100` / 29423 | PASS；左因子平方产生准确 2f。 |
| 24 | `directionalPair_self` | `SmoothDirectionalEnergy.lean:106` / 29429 | PASS；自配对精确等于平方和能量。 |
| 25 | `directional_div_product` | `SmoothDirectionalEnergy.lean:110` / 29433 | PASS；真实逐方向散度乘积展开，无遗漏项。 |
| 26 | `smoothD_directionalEnergy_time` | `SmoothDirectionalEnergy.lean:117` / 29441 | PASS；真实时间方向微分与空间方向交换，给 2〈Dₜ∇f,∇f〉。 |
| 27 | `directionalLap_mul` | `SmoothDirectionalEnergy.lean:127` / 29447 | PASS；二阶乘积法则，交叉项准确为 2〈∇f,∇g〉。 |
| 28 | `pointwiseHeatFlux` | `PointwiseHeatIdentity.lean:14` / 29456 | PASS；真实五项通量：2zₜ∇z、4〈∇ℓ,∇z〉∇z、−2|∇z|²∇ℓ、−2Ψz∇z、2kz²∇ℓ。 |
| 29 | `pointwiseHeatTimeFlux` | `PointwiseHeatIdentity.lean:21` / 29460 | PASS；M=kz²−|∇z|²，符号准确。 |
| 30 | `pointwiseHeatB` | `PointwiseHeatIdentity.lean:24` / 29463 | PASS；B=Dₜk+2 div(k∇ℓ)+2kΨ，均为实际微分。 |
| 31 | `pointwiseHeatMatrixEnergy` | `PointwiseHeatIdentity.lean:28` / 29467 | PASS；原 c 二次型为 2 Hess ℓ[∇z,∇z]−(Δℓ+Ψ)|∇z|²；不含原式外层的另一个 2。 |
| 32 | `pointwiseHeatFlux_divergence` | `PointwiseHeatIdentity.lean:31` / 29471 | PASS；逐项实际微分，完整展开五项通量的散度。 |
| 33 | `pointwise_heat_identity` | `PointwiseHeatIdentity.lean:69` / 29494 | PASS；原残差平方加 Mₜ、div V 等于两平方、2c、负 Ψ 梯度项及 Bz²。 |
| 34 | `smoothD_exp` | `PointwiseHeatConjugation.lean:15` / 29512 | PASS；实际指数复合的方向链式法则。 |
| 35 | `smoothD_exp_neg` | `PointwiseHeatConjugation.lean:21` / 29516 | PASS；负指数复合的负号正确。 |
| 36 | `directionalLap_exp_neg` | `PointwiseHeatConjugation.lean:26` / 29520 | PASS；Δ exp(−f)=exp(−f)(|∇f|²−Δf)，真实二阶导数。 |
| 37 | `directionalPair_exp_neg` | `PointwiseHeatConjugation.lean:40` / 29527 | PASS；负指数与任意 g 配对的因子 −exp(−f) 正确。 |
| 38 | `heatConjugationK` | `PointwiseHeatConjugation.lean:47` / 29533 | PASS；k=ℓₜ+|∇ℓ|²−Δℓ−Ψ。 |
| 39 | `heatCarlemanA` | `PointwiseHeatConjugation.lean:50` / 29537 | PASS；A=|∇ℓ|²−Δℓ−Ψ，准确对应 Φ=0。 |
| 40 | `heatConjugationK_eq` | `PointwiseHeatConjugation.lean:53` / 29540 | PASS；精确 k=ℓₜ+A。 |
| 41 | `heatConjugationK_contDiff` | `PointwiseHeatConjugation.lean:58` / 29544 | PASS；k 的 C∞ 由原 ℓ、Ψ 内部推出。 |
| 42 | `pointwiseHeatB_original_formula` | `PointwiseHeatConjugation.lean:64` / 29548 | PASS；完整六项 B 展开与原 (3.5) 一致；未遗漏 Aₜ、ℓₜₜ 或时间混合通量。 |
| 43 | `pointwise_heat_conjugation` | `PointwiseHeatConjugation.lean:88` / 29564 | PASS；真实 exp(ℓ)(Dₜ−Δ)(exp(−ℓ)z) 共轭；任意 Ψ 在 k+Ψ 中严格抵消。 |
| 44 | `pointwise_heat_carleman_identity` | `PointwiseHeatConjugation.lean:102` / 29575 | PASS；将真实共轭及内部 k 光滑性代入完整点态恒等式。 |
| 45 | `pointwise_heat_carleman_inequality` | `PointwiseHeatConjugation.lean:116` / 29594 | PASS；仅丢弃第二个非负平方，保留 Mₜ、div V 和原完整右端。 |
| 46 | `spaceTimeSpatialDirection` | `SpacetimeHeatIdentity.lean:14` / 29611 | PASS；实际空间方向 (0,eᵢ)，eᵢ 为 Euclidean 标准正交基。 |
| 47 | `spaceTimeHeat` | `SpacetimeHeatIdentity.lean:17` / 29613 | PASS；原时间 deriv 减去真实 spatialLaplacian。 |
| 48 | `spaceTime_timeD` | `SpacetimeHeatIdentity.lean:21` / 29615 | PASS；通过真实时间嵌入的链式法则识别 D_(1,0) 与一元 deriv。 |
| 49 | `spaceTime_spatialD` | `SpacetimeHeatIdentity.lean:28` / 29619 | PASS；通过真实空间嵌入的链式法则识别 D_(0,v) 与空间 fderiv。 |
| 50 | `spaceTime_directionalLap` | `SpacetimeHeatIdentity.lean:35` / 29624 | PASS；两次实际空间方向身份给真实空间 Laplacian，相同时间切片。 |
| 51 | `spaceTime_heat_directional` | `SpacetimeHeatIdentity.lean:50` / 29630 | PASS；实际方向热算子与 spaceTimeHeat 精确相等。 |
| 52 | `spacetime_heat_carleman_identity` | `SpacetimeHeatIdentity.lean:56` / 29636 | PASS；对任意原 C∞ 实函数 u 内部设置 z=exp(ℓ)u，证明 exp(−ℓ)z=u 后得到完整恒等式。 |
| 53 | `spacetime_heat_carleman_inequality` | `SpacetimeHeatIdentity.lean:79` / 29654 | PASS；同一个实际原 u、z、k 的点态不等式，未加入积分或边界结论。 |

## 微分、通量与原书公式

一般层的 E 是任意实赋范空间，空间方向族只要求有限，时间方向也是固定向量；不需要先假定它们正交，因为这里先证明常方向微分的代数恒等式。`smoothD_comm` 先识别 Dᵤ(Dᵥf) 为实际二阶 Fréchet 导数求值，再调用二阶导数对称性，因而输运交叉项的消去不是形式上假定混合导数可交换。`directional_transport_cancellation` 在真实双和中换序并使用该交换，保留 Hessian 与能量导数两项。`smoothD_directionalEnergy_time` 同样使用真实时间/空间混合微分交换。

在标准空间方向下，独立展开得到

- M=kz²−|∇z|²；
- V=2zₜ∇z+4〈∇ℓ,∇z〉∇z−2|∇z|²∇ℓ−2Ψz∇z+2kz²∇ℓ；
- c[∇z,∇z]=2 Hess ℓ[∇z,∇z]−(Δℓ+Ψ)|∇z|²；
- B=kₜ+2 div(k∇ℓ)+2kΨ。

这里 div 是逐坐标真实方向微分的和。实际证明先展开所有五个通量项及 M 的真实时间导数，再使用已证输运抵消与实代数。所得等式为

R²+Mₜ+div V=(Δz+kz)²+(zₜ+2〈∇ℓ,∇z〉−Ψz)²+2c[∇z,∇z]−2〈∇Ψ,∇z〉z+Bz²，

其中 R=zₜ−Δz+2〈∇ℓ,∇z〉−(k+Ψ)z。特别核对：原 c 前的外层系数 **2** 没有吞入 c 的定义；Ψ 梯度项是 **负号**；Mₜ 和 div V 位于左端且没有被无依据删除；两个平方均在恒等式中保留。不等式只用第二个平方非负，与原 (3.3) 的 Φ=0 形式对应。

令 A=|∇ℓ|²−Δℓ−Ψ、k=ℓₜ+A 后，`pointwiseHeatB_original_formula` 真实展开为

B=2AΨ+2 div(A∇ℓ)+2 div(ℓₜ∇ℓ)+2Ψℓₜ+ℓₜₜ+Aₜ。

该六项恰与原 (3.5) 在 p=Id、Φ=0 下对应；p^{jk} 的时间导数为零，−Φ² 为零。没有丢失 Aₜ 或时间混合通量，也没有提前对 B 作正性或吸收断言。

## 指数共轭及真实时空算子

指数链式法则、实际 Laplacian 乘积法则和 Δexp(−ℓ)=exp(−ℓ)(|∇ℓ|²−Δℓ) 给出 R=exp(ℓ)(Dₜ−Δ)(exp(−ℓ)z)。`heatConjugationK` 内的 −Ψ 与 k+Ψ 精确抵消，所以此共轭定理允许任意 Ψ；这不是缺少 Ψ 可微性，因为该定理本身不对 Ψ 求导。后续 B、通量恒等式确实对 Ψ 要求 C∞。

时空层采用 ℝ×EuclideanSpace ℝ (Fin d)，时间方向 (1,0)，空间方向 (0,eᵢ)。`spaceTime_timeD` 用时间路径的真实链式法则得到一元 deriv；`spaceTime_spatialD` 用空间嵌入的真实链式法则得到空间 Fréchet 导数。第二次应用同一身份识别方向 Laplacian 为 C149 的实际 `spatialLaplacian`，因此不是把抽象方向和事后命名成原热算子。

最终输入是任意实际 C∞ 的原 u、ℓ、Ψ；内部构造同一 z=exp(ℓ)u，证明 exp(−ℓ)z=u 的函数恒等式后替换真实热算子。没有预设原 u 已经具有某种共轭表达，也没有缩小到特定状态。全 d:ℕ、任意时空点均覆盖，d=0 的空空间方向和亦合法。证明没有维数除法、非零梯度条件或隐含正维前提。

这些都是精确点态恒等式，数值系数固定，无网格、T、q、λ、β、q_c 或最终估计常数。它们不等于已经证明这些参数下的统一积分估计。一般方向层对正反时间方向均可代入，但最终时空入口明确是 ∂ₜ−Δ；原 ε=−1 的全轨道时间反射仍是后续工作。

## 依赖版本、公理与构建

五新模块真实声明数为 10+17+6+12+8=53；全部被固定 `Carleman.lean` 导入，全部在固定 `tools/CheckAxioms.lean` 中有完整类型和公理记录。固定台账两处声明清单与实际源码顺序完全一致。未发现 `sorry`、`admit`、新数学 `axiom` 或 `native_decide`。

本 Agent 递归遍历这五模块的 Carleman import 闭包，共 **81** 个模块；其中 **76** 个旧模块均与本次基线逐字节相同。这 76 个模块也是 `SmoothLaplacianProduct` 的完整项目依赖闭包，并且全部与 C149 的已验收固定版本 `c3ea3c03352de258d944bf495695b31bcef3f3b0` 相同。已直接重读 `SmoothLaplacianProduct` 的实际 Laplacian 定义与乘积证明。旧依赖的历史验收可追溯 [T133 报告](T133-local-acceptance.md)，但本批新证明和实例身份已另行核对。

固定 Lean 为 4.35.0；mathlib pin 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际依赖 HEAD 匹配且工作树干净。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

`CheckAxioms` 审计主体与基线相同：对 privateToUserName 属于 Carleman 的所有环境常量递归调用 collectAxioms，只容许 `propext`、`Classical.choice`、`Quot.sound`。原始产物末行实报 **7415** 项递归审计 PASS。打印的 2705 条非空公理记录及 9 条无公理记录与此全环境计数意义不同；未把打印条数冒充递归条数。53 项本批声明均有实际类型与公理记录，依赖仅含上述正常基础公理。

实际读取 `/tmp/carleman-t145-spacetime-target.log`：3224 jobs 成功；`/tmp/carleman-t145-pointwise-heat-build.log`：3981 jobs 成功；`/tmp/carleman-t145-pointwise-heat-axioms.log`：7415 项审计成功。CI 的固定脚本先校验实际 mathlib HEAD，再运行 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean`；未依赖变化中的本机 `.ci`。

## 独立远端证据

本 Agent 实际查询 [main CI run 39231368445 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39231368445/attempts/1)，核实 event=push、head_branch=main、head_sha=`ccbd7a887ed37afbc4d4e530d06b885350e74b3a`，顶层 completed/success（updated_at=2026-10-19T09:40:50Z）。三项 job 均 completed/success：

| job | 实际 ID | 最终结果 |
|---|---:|---|
| state-check | 117989851388 | success |
| lean | 117989851655 | success |
| dashboard / snapshot | 117991426179 | success |

两份原始工件均由本 Agent 以 `gh run download` 从该 run 独立下载，两个下载进程 exit 0。工件元数据的 workflow_run 均绑定上述 SHA：

| 工件 | 实际 artifact ID | 归档 bytes | 归档 SHA256 |
|---|---:|---:|---|
| lean-ci-result | 12177970333 | 493 | `fa463ec2dcca9289dc5468aff312022c66b74a4111a6d419f6a84f47f1aba342` |
| lean-declaration-evidence | 12176829955 | 210935 | `22a225f2fbad862550f13b54372927d1b08452933c805d28c3acc88196bf0ea1` |

实际读取 `/tmp/carleman-t145-pointwise-heat-main-ci/result.json`：status=PASS，checked_sha 与 source_head_sha 均等于本报告固定 SHA，ci_url 为同 run/attempt，finished_at=`2026-10-19T09:39:31.431355+00:00`；targets=[Carleman]；Linux Lean 4.35.0 编译器提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

实际下载的 `/tmp/carleman-t145-pointwise-heat-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t145-pointwise-heat-local-axioms.txt` **逐字节相同**：均 **2273504 bytes**，原始文件 SHA256 为 **`7d789d7cd19746bad3047299a20bef8db5b5d2f53d2b51eea385bfa28335eada`**。归档 hash 与原始文件 hash 分别记录，没有混用。远端原始文件包含全部 53 项完整类型及 7415 项递归审计 PASS。

## 签发结论

**T145 / C161 可在该固定版本升为 REVIEWED，scope 必须保持 AUXILIARY。** 全部 53 项在所声明 C∞ 范围内语义和公理检查 PASS，无需要修复的实现缺陷。原 C² 时间权、完整 Sobolev 轨道、真实域 Green 积分、周期端点、具体权代入、heatcross 系数界与吸收、密度和时间反射仍待；不得将本报告用于提升 P024 或宣称完整连续 Carleman 估计。原文覆盖保持 17/26。本报告定稿后冻结内容与 reviewed_at，仅提交此报告，不改实现、台账或原稿，不推送。
