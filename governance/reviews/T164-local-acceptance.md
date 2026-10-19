# T164 / C180 独立本机验收：完整盒弱周期图的双方向 Carleman 估计

- checked_sha / source_sha: `3eef6d37a89f75f890de1a12aa8fe1f976217e04`
- mathematical_base: `61ddd47f394ef2a5c61e3ccc317ace118ab816b5`
- reviewed_at: `2026-10-19T12:36:41+00:00`
- reviewer: 独立本机 Agent `/root/accept_section3`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 四模块十二项声明通过。C180 可升级为 REVIEWED，并保持 AUXILIARY；本次清偿光滑 core CE 前提，得到完整盒 PeriodicGraph 上的同常数双方向估计。P024 不提升，原文完整覆盖保持 **17/26**。

## 原文与验收边界

逐项读取固定 Git 对象中的四模块全部实现、固定 raw 中十二项完整展开类型、关键实际依赖，并对照 `paper/main.tex:2672–2676` 的原连续 CE、`2696–2730` 的光滑状态估计与密度步骤，以及 `292–299` 的原 C² 时间权与 0、1、2 阶端点匹配要求。原指数为 `(c₀,c₁;o)=(3,1;3)`，残差为实际 `ε∂t−Δ`。本批完成这些量在盒域完整周期图上的估计；不把规格文字或 CI 成功代替数学核验。

已核对固定 AGENTS、PROJECT_OPERATIONS、state/README、MATH_SPEC 的 T164 段、`analysis/T164-box-weak-heat.md`、C180/T164 清单。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。后续 IntervalTimeWeight、IntervalHeatEnergies、BoxIntervalWeakHeat、WeakTrajectoryHeatEnergies、BoxOriginalWeakHeat 及动态 `.ci/axioms.txt` 全部排除。

最终域为任意正边长坐标盒，维数写成 `d+1`，覆盖任意正整数维。观察集 W 为非空开集且 W⊆Ω；此条件覆盖原紧包含的非空开观察区域，并允许更大的观察区域。空间相位确为 `ρ(x)=exp(−λ‖x−c‖²)−2`，c∈W、λ≥1，真实全空间范围 `−2<ρ≤−1`。未要求盒关于 c 对称，也未假设原弱状态有光滑代表。

**保留的接口范围：** 输入权仍是原框架 `TimeWeight`，它要求全实轴 `1≤q≤w.max`。新增 C²、端点匹配和导数预算只要求在 `[0,T]`，没有区间外连续、C² 或周期性假设。任意原闭区间 q 的有界承载代表构造，以及直接接收原 `PeriodicWeakTrajectory` 的最终包装接口，不在本固定版本。一般凸多面体也未覆盖。因此不能据本次通过宣称完整 P024 已完成。

## 十二项声明逐项验收

下列位置均指 checked_sha，Lean 路径相对于 `Carleman/`；raw 行为完整类型起始行。清单顺序与固定 `/tmp/carleman-t164-box-weak-heat-declarations.json`、C180 和 T164 完全一致。四模块均在固定根目标导入，十二项均有实际 `#check` 和 `#print axioms`。

| # | 声明 | 固定源码位置；raw 行 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.weighted_box_density_integrable` | `Spatial/BochnerBoxIntegral.lean:14`；32033 | PASS。闭时间区间乘盒闭包紧性与实际连续加权密度给真实产品测度可积性；仅需区间上 q 连续。 |
| 2 | `Carleman.timeSq_eq_boxTimeIntegral_of_norm_sq` | `Spatial/BochnerBoxIntegral.lean:31`；32044 | PASS。任意实指数、真实嵌套 Lp 范数平方身份、显式产品可积性，通过实际 Fubini 与 Ioo/Icc 限制测度相等得到精确柱积分。 |
| 3 | `Carleman.timeSq_eq_boxTimeIntegral_of_continuous` | `Spatial/BochnerBoxIntegral.lean:57`；32061 | PASS。任意自然指数内部调用第 1 项清偿可积性，实幂转自然幂准确。 |
| 4 | `Carleman.timeSq_eq_boxTimeIntegral_of_indicator` | `Spatial/BochnerBoxIntegral.lean:69`；32080 | PASS。W 仅需可测；由实际产品密度的可积性得到可测示性函数乘积可积性，再精确识别观察积分。 |
| 5 | `Carleman.periodicGraph_value_classical_ae` | `Spatial/PeriodicClassicalRepresentatives.lean:17`；32102 | PASS。同一 F 的闭区间迹身份，经实际 pathL2/clampPath 给时间 a.e. 内嵌空间 a.e. 的值身份。 |
| 6 | `Carleman.periodicGraph_residual_classical_ae` | `Spatial/PeriodicClassicalRepresentatives.lean:24`；32109 | PASS。两个 Lp 层次分别使用真实加法/数乘代表身份，得到 `ε·p.derivative+p.operator=ε∂tF−ΔF`；任意实 ε 均成立。 |
| 7 | `Carleman.periodicGraph_observation_classical_ae` | `Spatial/PeriodicClassicalRepresentatives.lean:42`；32122 | PASS。实际 cutoff CLM 的 Bochner 作用识别为同一 F 的 `1_W F`，未假设观察边界零测或示性函数连续。 |
| 8 | `Carleman.smooth_spatial_gradient_sq_continuous` | `Spatial/DirichletHeatIntegral.lean:15`；32132 | PASS。实际空间 gradient 范数平方通过完整方向能量恒等式及 Fréchet 导数连续性证明连续。 |
| 9 | `Carleman.smooth_oriented_heat_continuous` | `Spatial/DirichletHeatIntegral.lean:24`；32135 | PASS。真实时间导数与空间 Laplacian 的线性组合连续，符号和 ε 保留。 |
| 10 | `Carleman.dirichletHeatLeft_eq_boxIntegral` | `Spatial/DirichletHeatIntegral.lean:44`；32138 | PASS。同一 F 的 q³ 值项与 q 梯度项精确转为两项原柱积分；弱梯度与经典梯度由实际 H¹ jet 唯一性内部识别。 |
| 11 | `Carleman.dirichletHeatRight_eq_boxIntegral` | `Spatial/DirichletHeatIntegral.lean:66`；32154 | PASS。同一 F 的真实热残差平方和 q³ 观察项精确识别，无额外 q 次数、符号或系数损失。 |
| 12 | `Carleman.box_weak_C2_gaussian_heat_both_signs` | `Spatial/BoxWeakHeatEstimate.lean:15`；32177 | PASS。实际原闭区间 C² 光滑估计内部清偿 core 前提，完整图密度延拓保留同一 C，全部参数先于 g、w、ε、p。 |

## 产品积分、两层代表与四项实际身份

第 1 项使用的紧集是 `[0,T]×closure Ω`。q∘fst 只需在此集连续，ρ∘snd 与 F 连续；实际产品 Lebesgue 体积及 `Measure.prod_restrict` 把紧集可积性限制到 `[0,T]×Ω`。没有把任意不可积函数的 totalized integral 默认值用于 CE。第 2 项对一般实 s 保留真实产品可积性前提；第 3、4 项在实际应用中清偿它。`integral_prod` 使用该前提，时间端点由 Lebesgue 无原子性给 `restrict_Ioo_eq_restrict_Icc`，并非从周期性删除端点。

空间加权范数由 `BoundedMultiplier.seminorm_sq_integral` 精确变成 `∫|exp(qρ)|²‖u‖²`；指数为 0 的 multiplier 没有额外 q 因子，exp 的严格正性消去绝对值。观察项先对可积密度使用可测集 `Prod.snd ⁻¹' W` 的 indicator，再以 W 内外分支移动权因子。无需 W 的边界正则性或示性函数连续性。

`PeriodicGraph` 的值字段是实际连续 H 迹，两个 L² 字段分别满足完整弱时间测试关系和原 associated operator 的 a.e. 图关系，另有真实首尾迹相等条件。它不是仅给三个任意函数命名。值身份先在时间满测集上恢复真实 pathL2，再用同一 F 的每时刻空间 a.e. 迹身份；残差身份先处理外层 Bochner Lp 的加法/数乘，再处理内层空间 Lp。固定 `spaceTime_timeD` 和 `spaceTime_directionalLap` 将方向导数识别为真实时间 deriv 与空间 Laplacian，故原 A=−Δ 对应 `ε∂t−Δ`，没有变为 `ε∂t+Δ`。

梯度由原 `resolventEnergy(1)` 作用于 `Au+u` 给真实能量字段，再通过原 dirichletGradient 的 Bochner CLM 得到。其嵌回值正是原 u；同值的原弱 H¹ jet 与 F 的紧支截断 jet 由完整弱测试唯一性相等，全部一阶分量平方和精确等于真实 gradient 范数平方。这里没有将算子范数代替完整梯度范数，没有维数比较损失，也没有预设原状态的经典导数代表。

记 θ=exp(qρ)，同一个 F 同时给出四项：

| 原图能量 | 实际柱积分 |
|---|---|
| `timeSq 3`，原值字段 | `∫ q³ θ² F²` |
| `timeSq 1`，原弱梯度字段 | `∫ q θ² ‖∇ₓF‖²` |
| `timeSq 0`，`ε·weak_dtime+actual_A` | `∫ (θ(ε∂tF−ΔF))²` |
| `timeSq 3`，实际 cutoff(W) 值 | `∫ 1_W q³ θ² F²` |

四项使用同一 q、ρ、p、F，梯度在乘 θ 之前，且观察集合为原 W。最终 core 拆包一次得到 F 的 C∞、真实周期性、全时刻全边界零值、迹及两个字段身份；没有分别选择互不相关的四个代表。上述等式无估计损失，因而不会改变已有光滑 CE 的常数。

## 完整弱图范围、常数量词与条件清偿

最终先固定正边长盒和非空开观察集，内部从已验收 `box_interval_C2_gaussian_heat_both_signs` 取得 c、λ、β、qc、C，其中 λ≥1、0<β≤1、qc≥1、C>0。这些存在量词严格位于所有 `TimeGrid g`、`TimeWeight w`、两种 ε 和完整原 `PeriodicGraph g` 元素 p 之前。没有依赖 T、qmax、时间离散参数、谐波频率或 p 的新估计常数。

q 仅在 Icc 上 C²；0、1、2 阶使用 `derivWithin` 的原端点匹配，`q≥qc`、`|q′|≤βq²`、`|q″|≤β²q³` 原预算准确保留。由区间连续性内部推出 q 对实际时间测度的 a.e. 强可测性。C172 的区间延拓和光滑状态 CE 均在固定版本已接受且未变，本批没有重新要求全局 C² 或更小 β，也没有另加 q 的导数界。

固定参数下，两侧能量是完整图上的连续实函数。真实 `timeMap` 的 MemLp 与 CLM 范数证明了能量有限和连续；其辅助界可以依赖 w.max 或 T，这些界仅用于极限合法性，不进入 CE 常数 C。闭集 `{p | Left(p)≤C·Right(p)}` 包含整个 classical core 后，由其真实图拓扑稠密性覆盖全部 p，C 完全不变。

已读完整图稠密性的实际机制：有限谐波 L² 稠密经真实连续、满射的 constantSolve 映到完整 PeriodicGraph，覆盖连续 H 迹、弱时间导数及 Au 的图拓扑；真实空间算子图逼近再经 harmonicGraphCLM 生成同一光滑时空函数，具有全边界零值与正确的两个字段。因此稠密性不局限于值 L²、有限谐波或每时刻 D(A) 的原状态。最终定理没有保留 `hCE`、给定平滑序列、光滑代表、全时刻域资格或额外 PDE 前提。

辅助积分/连续性引理允许 d=0 或空盒的合法输入；最终 Dirichlet CE 明确只针对 `d+1` 正维正边长盒，不声称额外的零维 Dirichlet 模型。未发现本批所声明辅助目标的隐藏假设或实质弱化；上文 TimeWeight 承载和直接轨道包装的范围限制保持明确。

## 固定依赖与公理检查

四模块的 Carleman 递归 import 闭包为 **360** 文件，其中 **356** 个旧文件与 mathematical_base 逐文件完全相同。对以下关键已接受版本又比较完整相关闭包，均无变化：

| 依赖 | 接受的 declaration_version | 比较入口；闭包文件数 |
|---|---|---|
| C179 / [T163](T163-local-acceptance.md) | `61ddd47f394ef2a5c61e3ccc317ace118ab816b5` | Spatial/DirichletHeatContinuity；315 |
| C172 / [T156](T156-local-acceptance.md) | `b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50` | Spatial/BoxIntervalC2HeatEstimate；138 |
| C178 / [T162](T162-local-acceptance.md) | `5ec78c3027e714324439187119dfbfe4765a2af6` | Spatial/BoxClassicalTimeDensity；295 |
| C032 | `87363270f74e4955f5afbb8ecc20ae2990d449f5` | Weights/TimeL2Multiplier；38 |
| C056 / [T040](T040-local-acceptance.md) | `4f669626b3228adea39a16fbf6c1d22313763331` | Spatial/DirichletForm；49 |

实际 Dirichlet 形式仍为原全梯度 L² 内积，原 V 为 H¹₀，operator 为该形式的原完整变分域/action；没有零阶质量项。关键旧证明、实际图与弱 jet 结构已读取，不只依赖旧验收结论。新增模块 import 无循环，未见 sorry、admit、axiom 或 native_decide。

固定 Lean 为 `leanprover/lean4:v4.35.0`；CI 实际编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib pin 与本机实际干净 checkout HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、CI workflow、lean_ci.sh 与基线不变；实际 workflow 构建根 Carleman，并运行声明检查器。

固定 `-target2.log` 实际结束于 **3582 jobs** 成功，`-build.log` 结束于 **4076 jobs** 成功。`-axioms.log` 是空 stderr，未把它当作审计通过证据。完整固定 raw 有 **2995** 个依赖公理打印记录及 **9** 个无公理记录；全部只含 `propext`、`Classical.choice`、`Quot.sound`。十二项新声明均已逐项检查完整类型和递归公理集合。

固定检查器遍历环境中所有经 `privateToUserName` 还原为 Carleman 前缀的常量，逐项调用递归 `collectAxioms`，非白名单即报错。实际 raw 末行是 `Axiom audit passed for all 7926 Carleman declarations.`；显式打印记录数与包括自动生成对象的递归总数没有混淆。

## 独立正式 CI 与原始工件

验收者自行查询 [run 39252468748 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39252468748/attempts/1)，确认 main / push、`head_sha=3eef6d37a89f75f890de1a12aa8fe1f976217e04`，顶层最终 `completed / success`，最后更新 `2026-10-19T12:35:41Z`。三个作业均最终成功：

| 作业 | job ID | 结果 |
|---|---|---|
| state-check | `118059407768` | completed / success |
| lean | `118059408203` | completed / success |
| dashboard / snapshot | `118061993719` | completed / success |

自行执行 `gh run download` 下载同 run 两份原始工件，下载进程均退出 0，未用主执行者下载副本替代：

| 工件 | artifact ID；ZIP 字节数 | 独立下载位置 |
|---|---|---|
| lean-ci-result | `12186785009`；492 | `/tmp/carleman-t164-box-weak-heat-main-ci/result.json` |
| lean-declaration-evidence | `12185269672`；228719 | `/tmp/carleman-t164-box-weak-heat-main-axioms/axioms.txt` |

两工件 workflow_run 均绑定本次固定 SHA。API 给出的 ZIP digest 分别为 `sha256:94f6c170afc52c2c1ed523d37db6d232fa9068e6be36f45d673589ab504a8728` 与 `sha256:9e44105c09063fc1d47f53fc2d622d22230854c49a2c4cec6a383c0ff05e64ad`，与解压后的 raw 哈希区分记录。

实际 result.json：`status=PASS`，`checked_sha` 与 `source_head_sha` 均精确等于本报告首部的固定 SHA，目标 `Carleman`，`finished_at=2026-10-19T12:33:20.308081+00:00`；Lean/mathlib 与上述固定 pin 一致。远端 raw 与固定 `/tmp/carleman-t164-box-weak-heat-local-axioms.txt` 经独立逐字节比较完全相同，均为 **2458281 bytes**，SHA256 **`0e34ed37ddc7d0fa34d57823681e30b39e7e9975f70a1416327bd84a31fc25b2`**。

## 签发

**C180：PASS / AUXILIARY。** 十二项声明的实际对象、两层代表、可积性、导数符号、原指数、全状态范围、统一量词、固定依赖及公理均通过，未发现阻断缺陷。已内部清偿光滑 core CE 并传递至完整盒弱周期图；任意原区间权承载、直接原轨道接口与一般凸多面体仍不在本次完成范围。P024 不提升，完整原文覆盖保持 17/26。仅提交本报告，不改实现或台账，不推送；通知后正文和 reviewed_at 冻结。
