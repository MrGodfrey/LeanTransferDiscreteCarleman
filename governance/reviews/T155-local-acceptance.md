# T155 / C171 独立本机验收：全局 C² 周期权的盒双方向估计

- checked_sha / source_sha: `069e313b5c03c66aec7c41e72055f95292515e58`
- mathematical_base: `abadce407f55be6c99212cbf92654e8fa44a7c2d`
- reviewed_at: `2026-10-19T11:09:29+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 两模块三声明通过固定版本验收。C171 可以升级为 REVIEWED 并保持 AUXILIARY；P024 / `prop:continuousCE` 不提升，原文完整结果覆盖仍为 **17/26**。

## 原文、对象和范围

直接读取固定源码、三个完整展开类型、实际证明与相关旧依赖，对照原 `paper/main.tex:291–299` 的 qclass 和 `2672–2733` 的连续 CE 命题及证明。原文要求 C²([0,T]) 时间权及 0、1、2 阶匹配端点，并对两时间方向和全部指定弱轨道成立。本批实际输入为全实线 C² 周期 q、全时空 C∞ 周期零边界 u，以及正坐标盒。它将此前 C∞ 时间权的双方向估计传递到上述全局 C² 周期权，尚不证明原闭区间权的周期延拓或完整弱轨道扩展。

读取固定 `governance/analysis/T155-c2-heat-estimate.md`、`governance/MATH_SPEC.md` 对应段和 C171 台账；依根 AGENTS 与既有治理协议进行语义、公理和真实 CI 核对。规格、执行者意见与 CI 没有代替数学检查。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。后续工作树的 PeriodicPrimitive、PeriodicC2Extension、BoxIntervalC2HeatEstimate、LocalOddConvolution 等模块及动态 `.ci/axioms.txt` 均不作为本批依据。

## 三项声明逐项验收

下表位置均指 checked_sha。清单与固定 declarations.json 及 C171 `lean_declarations` 顺序相同，两个模块均被 `Carleman.lean` 导入，三项均进入 `tools/CheckAxioms.lean`；已逐项读取固定 raw 的完整类型。

| # | 显式声明 | 固定源码位置 | 结论 |
|---|---|---|---|
| 1 | `Carleman.boxTimeIntegral_tendsto_parameter` | `Carleman/Spatial/BoxTimeIntegralLimit.lean:13` | PASS。实际有限盒柱、连续参数族 F、同一有界区间 [0,B] 内的连续 qₙ 及逐时刻 qₙ→q，内部构造可积常数支配，得到原乘积测度下的真实积分收敛。没有外给积分收敛、可积性或均匀收敛假设。 |
| 2 | `Carleman.boxTimeIntegral_observation_tendsto_parameter` | `Carleman/Spatial/BoxTimeIntegralLimit.lean:35` | PASS。仅要求 W 可测，真实 `Prod.snd ⁻¹' W` 示性函数在 W 内使用同一连续参数极限，在 W 外恒零；证明实际 a.e. 可测性、支配及积分极限，不要求示性函数连续。 |
| 3 | `Carleman.box_C2_gaussian_heat_both_signs` | `Carleman/Spatial/BoxC2HeatEstimate.lean:14` | PASS。先固定 c/λ/β₀/qc/C 并取 β=β₀/9，再量化 T>0、全局 C² 周期 q、ε=±1 与光滑周期零边界 u；实际光滑 qₙ 的四项积分极限给原 q 的同常数 (3,1;3) 估计。 |

## 真实积分极限

`boxTimeIntegral` 沿用 `(volume.restrict [0,T]).prod (volume.restrict Ω)` 上的实际 Lebesgue 积分，其中 Ω 为原开坐标盒。第 1 项取真实紧集 `[0,B] × ([0,T] × closure Ω)`。空间盒有界给闭包紧，F 的联合连续性给统一范数界 D；实际支配函数为常数 |D|，其在原柱上的可积性由 `continuous_box_time_integrable` 供应。界只需在实际限制测度下 a.e. 成立，证明通过 `Measure.prod_restrict` 和实际柱的可测性定位积分点，没有把闭盒积分替换为原开盒积分。

每个复合函数 `tx ↦ F(qₙ(tx.1),tx)` 连续，故 a.e. 强可测；全部 qₙ(t)∈[0,B] 提供共同支配。逐时刻参数收敛与 F 的连续性给每个 tx 的极限，再调用 pinned mathlib 的 `tendsto_integral_of_dominated_convergence`。没有对原 q 偷加连续性、强收敛或导数收敛要求；这个一般辅助结论只需所写的逐点极限。最终应用中的 q 本身为 C²，且所有目标 integrands 都是真实可积函数，并非利用非可积积分的默认值。

第 2 项对同一复合函数乘以真实观测示性函数。W 可测使 `Prod.snd ⁻¹' W` 可测；`AEStronglyMeasurable.indicator` 供应可测性。在观测集内沿用 |D| 支配和连续参数极限，在其外范数为零且序列恒零。整个证明没有声称观察集边界上的示性函数连续，也不需要该边界零测。结合已验收的 `boxTimeIntegral_observation`，该项是 `[0,T] × (Ω∩W)` 的真实限制乘积积分；最终 W⊆Ω，因而正是原观测柱。

已实际阅读 mathlib `MeasureTheory/Integral/DominatedConvergence.lean:58` 的所需前提：每个函数 a.e. 强可测、真实可积支配、逐项 a.e. 范数界和 a.e. 点态收敛。两个新辅助定理分别供应了全部前提。最终保持不等式使用 `le_of_tendsto_of_tendsto` 的实数序闭性，所用过滤器 atTop 非平凡，全部序列项的估计由同一光滑定理给出。

## C² 逼近接口及常数顺序

实际阅读了固定 `TemporalMollification`、`TemporalMollificationDerivative`、`TemporalMollificationBounds`、`PeriodicC2Mollification`。qₙ 来自真实非负单位质量紧支光滑核卷积；C² q 的一、二阶导数通过真实参数积分微分交换获得。周期性把原 [0,T] 上的 qclass 界传到全实线，卷积保留同一 qc 下界与一个共同有限上界 B，并逐点趋于原 q。

核支持足够小时，由实际均值估计和卷积误差界得到 `q(t−s)≤3qₙ(t)`；对一阶和二阶项分别产生 9β、27β²。第 3 项先取得光滑双方向估计的 β₀>0，再选择输出 β=β₀/9。输入 q 的界因此为 `(β₀/9)q²` 和 `(β₀/9)²q³`；C170 的 exact 接口给 qₙ 的界为 β₀qₙ² 和 β₀²qₙ³，其中二阶实际损失 `27(β₀/9)²=β₀²/3≤β₀²`。同一 qc 不被改变，也没有要求调用者提供卷积序列或核尺度。

最终参数选择顺序严格为：先固定维数、盒 a/b 和 W；再取 c、λ、β₀、qc、C 并输出 β₀/9；之后才引入 T、q、ε 和 u。序列的起始尺度、共同上界 B 及四个支配常数 D 可以依赖本次 T/q/u/ε；它们只用于证明四个极限，没有乘到估计上，也没有进入最终 C。实际极限步骤保留的是光滑估计原来的同一 C，而非一个随 qmax、T、u 或 n 变化的常数。

## 四项实际积分与原对象保持

固定同一 u 与 ε，令 Q 为实参数、ρ=interiorCarlemanProfile(c,λ)。四项连续参数函数和观测项准确为：

| 项 | 实际参数函数 | 核对 |
|---|---|---|
| 值项 F₀ | `Q³ exp(Qρ(x))² u(t,x)²` | qₙ→q 后恢复同一 q³θ²u²。 |
| 梯度项 F₁ | `Q exp(Qρ(x))² ‖gradient(u(t,·))(x)‖²` | 原全空间坐标梯度保持；其联合连续性由真实空间方向能量身份与 u 的光滑性证明。 |
| 残差项 R | `[exp(Qρ(x)) spaceTimeOrientedHeat ε u(t,x)]²` | `spaceTimeOrientedHeat` 明确定义为实际 ε∂tu−Δu；未改变符号、状态或空间 Laplacian。 |
| 观察项 O | `1_{Prod.snd⁻¹W} F₀(Q,(t,x))` | 与值项使用同一个 F₀、同一个 qₙ 和同一个 W，单独使用第 2 项证明积分收敛。 |

`hprofile` 证明 exp(Qρ(x)) 关于 Q/t/x 联合连续；`hgrad` 由真实 `spaceTime_directionalEnergy_gradient` 得到实际梯度范数平方连续；`hheat` 用真实时间切片导数和实际空间 Laplacian 的方向导数身份证明原 ε∂t−Δ 残差连续。q 的导数只参与逼近序列的资格证明，不出现在这些目标积分的参数函数中，因此逐点 qₙ→q 已足以配合内部支配完成极限。

对每个 n，已验收的同一 `box_smooth_gaussian_heat_both_signs` 适用于 qₙ、原 ε 和原 u，得到 `F₀ₙ+F₁ₙ≤C(Rₙ+Oₙ)`。四个真实积分收敛后，实数序闭性给

`∫q³θ²u² + ∫qθ²‖∇u‖² ≤ C(∫|θ(ε∂t−Δ)u|² + ∫_Wq³θ²u²)`。

指数为原 (3,1;3)。ρ 的定义未变，保留全局 −2<ρ≤−1；λ≥1、qc≥1、0<β≤1 和 C>0 全部输出。T>0 与原命题一致。空间 d+1 覆盖全部正维，包括一维盒；一般极限辅助定理也允许 d=0。两方向共用全部参数，C169 中实际时间反射的残差负号和保测积分身份在本批固定版本未变。

**明确剩余范围：** 此处只替换时间权的正则性，不降低 u 的 C∞ 输入，也未构造原闭区间 C² 匹配端点数据的全局周期延拓。完整 `H¹_t L²_x ∩ L²_t D(A)` 状态和一般凸多面体同样尚未由本批完成。因此不能将 C171 的 PASS 当成 P024 / 完整连续 CE 的完成。

## 固定依赖、公理和构建

两模块的递归 Carleman import 闭包共 135 个文件，其中 133 个旧文件与 mathematical_base 逐文件内容完全相同。对关键已接受版本另行比较相关闭包：

| 依赖 | declaration_version | 实际比较入口 / 文件数 | 结论 |
|---|---|---|---|
| C168 | `86686ea4d106798727d898bf61abc238812a8cb8` | `BoxSmoothHeatEstimate` / 127 | 无变化 |
| C169 | `7a2da98bcead43801f48dc03ecffbc70adc7585e` | `BoxSmoothHeatBothSigns` / 129 | 无变化 |
| C170 | `abadce407f55be6c99212cbf92654e8fa44a7c2d` | `PeriodicC2Mollification` / 86 | 无变化 |
| C165 | `37d15b168e8c1ac3f313848be5a0c56594d2aad2` | `SmoothBoxTimeIntegral` / 88 | 无变化 |

固定工具链 Lean 4.35.0，实际 CI Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机实际 HEAD 相同且依赖工作树干净。上述支配收敛和实数序闭性均检查了 pinned mathlib 的实际声明。

固定 raw 共 2872 个显式公理记录，2863 个只列正常基础公理、9 个无公理；未知公理集合为空。本批三项均只依赖 `propext`、`Classical.choice`、`Quot.sound`。原始文件末行是 `Axiom audit passed for all 7616 Carleman declarations.`；2872 个显式输出记录和 7616 个递归审计声明没有混为一谈。无 sorryAx 或额外数学公理。

实际读取 `/tmp/carleman-t155-c2-estimate-target3.log`，最终目标 `Carleman.Spatial.BoxC2HeatEstimate` 构建成功，3300 jobs；`/tmp/carleman-t155-c2-heat-estimate-build.log` 中根目标完整构建成功，4036 jobs。该前缀 `-axioms.log` 实际为 **0 bytes**，不作为 PASS 日志引用；递归审计证据来自已完整读取的固定 `-local-axioms.txt` 以及下述同 SHA 远端原始产物。未声称审查者重新执行过本机构建。

## 独立查询及下载的正式 CI

审查者独立查询正式 run **39242086203** / attempt **1**，最终整体 `completed/success`，head SHA 精确等于 checked_sha，updated_at 为 `2026-10-19T11:09:08Z`。实际三个 job 全部 `completed/success`：

| Job | ID | 结果 |
|---|---|---|
| lean | `118025084093` | success |
| state-check | `118025084698` | success |
| dashboard / snapshot | `118026536972` | success |

正式 CI：[run 39242086203 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39242086203/attempts/1)。独立查询并自行执行 `gh run download` 获取同次原始产物：

- `lean-ci-result`，artifact ID **12182161905**，实际文件 `/tmp/carleman-t155-c2-heat-estimate-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=069e313b5c03c66aec7c41e72055f95292515e58`，`finished_at=2026-10-19T11:07:59.500028+00:00`，targets 为 `Carleman`，CI URL 属于上述同 run / attempt。
- `lean-declaration-evidence`，artifact ID **12181982271**，实际文件 `/tmp/carleman-t155-c2-heat-estimate-main-axioms/axioms.txt`：与固定 `/tmp/carleman-t155-c2-heat-estimate-local-axioms.txt` **逐字节完全一致**，**2372024 bytes**，SHA256 **`632ad3ee3262086011324e4d66e1c6ba085b5c2f1572194a46fdc62e0a19ecfa`**，远端末行同为全部 7616 声明递归审计通过。

## 签发结论

固定三声明全部 **PASS**，没有阻断 C171 AUXILIARY 验收的数学或证据缺陷。实际有限柱支配收敛、观测 indicator、同一四积分、真实双方向热残差以及统一参数先后次序均已核对。只签发并单独提交本报告，不改实现、root/audit、台账或原稿，不推送；签发后冻结 reviewed_at 和正文。P024 不提升，原文覆盖保持 17/26。
