# T166 / C182 独立本机验收：真实热梯度与盒连续转移接口

- checked_sha / source_sha: `28789e8973368055acc0c17d5b395332e6ee7364`
- mathematical_base: `7e994b40b5fa75256961286178b81124fc9e1632`
- reviewed_at: `2026-10-19T12:54:20+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`，未参与本批实现。
- result: **PASS**；axiom_check: **PASS**；全部 **11/11** 显式声明通过。
- scope: **AUXILIARY**。真实盒连续估计已供应原转移接口的 continuous 前提；一般凸多面体与具体离散实例的完整组装不在本批，**P024 不提升，原文覆盖保持 17/26**。

本次从固定 Git 对象读取四模块全部源码、十一项实际展开类型及公理、原稿、分析、MATH_SPEC、台账和关键真实依赖。独立访问精确 SHA 的 GitHub run/jobs/artifacts，并自行下载 result/raw 与固定本机副本逐字节比较。执行者说明、既有验收报告和 CI 均未替代本批数学核查。动态 `.ci/axioms.txt` 及未来工作树草稿全部排除；仅新增并单独提交本报告，不改实现、台账、根导入或原稿，不 push。

## 原文对应与最终范围

固定 `paper/main.tex:292–299` 的 qclass 是原闭区间 C²、0/1/2 阶端点匹配、1≤qc≤q≤qmax、|q′|≤βq²、|q″|≤β²q³；qmax 可以取闭区间最大值。`374–381` 的 A4 对全部原弱周期状态和两个时间方向要求同一实际 ε∂t+A 残差及原观察区。`2672–2675` 对热方程指定 m=1、D₁=∇、指数 (3,1;3)，`2684–2690` 选择实际 Gaussian 相位，`2730` 用密度和时间反射得到完整弱状态与负方向。

本批最后声明采用任意正边长坐标盒，维数 d+1 覆盖所有正整数维。W 非空、开且包含在盒内，涵盖原非空紧包含观察开集的情形；不要求 W 的边界正则或零测。最终相位是实际 `interiorSpatialProfile`，ρ(x)=exp(−λ‖x−c‖²)−2，c∈W、λ≥1，且全空间 −2<ρ≤−1。常数由固定空间数据选择后，再量化全部数值空间、范数、时间网格、权、方向及原弱轨道。

**盒域的 continuous 前提已实际清偿，最终没有 hCE、给定梯度身份、给定逼近或光滑轨道前提。** 本批尚未将这个输入与具体 Cartesian 数值数据合并成新的完整离散结论，也未证明一般凸多面体上的连续 CE，因此仍为 AUXILIARY。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有通过修改原文缩小目标。

## 十一项声明逐项核对

清单和顺序与固定 C182/T166 及 `/tmp/carleman-t166-heat-transfer-geometry-declarations.json` 一致；行号指 checked_sha。每项完整展开类型及公理输出均已实际读取。

| # | 完整声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.heatGradientExpression` | `Carleman/Spatial/HeatGradientExpression.lean:15` | PASS。真实有界算子系数表达式，零阶为零 CLM，一阶为恒等 CLM，输出为完整 DerivativeFiber d 1。 |
| 2 | `Carleman.heatGradientExpression_apply` | `Carleman/Spatial/HeatGradientExpression.lean:23` | PASS。对任意两阶真实 Lp 输入，有限求和的实际输出精确等于 u 1；不是仅范数比较。 |
| 3 | `Carleman.heatDifferentialFamily` | `Carleman/Spatial/HeatGradientExpression.lean:39` | PASS。热指数 m=1 的唯一成员为第 1 项真实表达式，阶数 j+1 正确。 |
| 4 | `Carleman.conforming_heat_expression` | `Carleman/Spatial/HeatGradientExpression.lean:51` | PASS。对任意真实 H¹ conforming 子空间及其全部状态，表达式精确等于 canonical 一阶弱导数。 |
| 5 | `Carleman.dirichlet_conforming_gradient` | `Carleman/Spatial/HeatGradientExpression.lean:59` | PASS。原完整变分域 D(A) 的 inclusion 后 canonical 导数与同一 dirichletDomainJet 的 field₁ 定义相同。 |
| 6 | `Carleman.dirichletHeatGeometry_energy` | `Carleman/Transfer/DirichletHeatGeometry.lean:30` | PASS。原 continuousEnergy 精确成为原 value 的 q³ 项加原 domain jet 梯度的 q 项，domainValue 只用时间 a.e. 身份。 |
| 7 | `Carleman.dirichletHeatGeometry_residual` | `Carleman/Transfer/DirichletHeatGeometry.lean:53` | PASS。保留同一 ε·u.derivative+A(u.domainValue)，实际权 τ=0 恰为 exp(qρ)，残差指数为 0。 |
| 8 | `Carleman.dirichletHeatGeometry_observation` | `Carleman/Transfer/DirichletHeatGeometry.lean:60` | PASS。真实 cutoff(W) 作用于同一原 value，原观察指数为 3，区域与常数均不改变。 |
| 9 | `Carleman.IntervalQClass` | `Carleman/Weights/IntervalQClass.lean:11` | PASS。原 Icc C²、下界、两导数预算和三阶次端点匹配逐字段汇集，无区间外正则或周期假设。 |
| 10 | `Carleman.IntervalQClass.toRegularity` | `Carleman/Weights/IntervalQClass.lean:24` | PASS。由完整区间条件提取已有一阶 TimeWeightRegularity；没有声称反向蕴含。 |
| 11 | `Carleman.box_heat_continuous_data` | `Carleman/Transfer/BoxHeatContinuous.lean:16` | PASS。调用已证原盒弱双方向估计，并以第 6–8 项精确转换，完整供应原 transfer continuous 前提；同一参数和 C 在所有数值/时间/权/状态之前。 |

## 真实梯度、域及代表身份

`OperatorMultiplier.const` 的 value 是给定实际 CLM，强可测性由常值函数给出，bound 是其真实算子范数。`DifferentialExpression.apply` 是对 orders 中各实际 Lp map 的有限和。m=j=1 时 orders 包含 Fin 2 的两项；第 2 项经 apply_ae、Lp.ext 和 Fin.sum_univ_two，将该和实际化为 0+u₁。不存在命名为梯度的任意替代映射或预先假设的能量不等式。

`conformingDerivative` 是 `sobolevDerivative` 与真实子空间 inclusion 的复合；后者由 WeakSobolevJet.value 的单射线性等价恢复唯一弱 jet，再取 field。已重读 SobolevRealization 的唯一性证明：全部 Sym 分量和原弱导数测试逐阶决定整个 jet。因此第 4 项适用于全 conforming 空间，不限光滑、有限维或某个基底表示。

实际 `boundedDirichletOriginalForm` 取原 H¹₀ 子空间、真实 L² 梯度内积形式及由 Poincare 得到的 coercivity；`OriginalForm.model` 是该闭形式的原完整变分算子，其 domain_le 内部供应 H¹₀ 资格。`dirichletDomainJet` 与 conformingDerivative 使用同一个 sobolevJetEquiv、同一个域值和 inclusion，所以第 5 项确为 rfl；没有以 H² 子域重新定义算子域，也没有新增 H² 正则性前提。已有 dirichletDomainJet_graph 确认其弱负 Laplacian 恰为同一个 A 值。

DerivativeFiber d 1 的完整 Euclidean 坐标由 Sym(Fin d,1) 索引，与 Fin d 一一对应。第 1–5 项是字段精确相等，不能产生维数范数比较损失。通用表达式部分允许 d=0；实际 Dirichlet 几何要求 hd>0，最终以 d+1 明确实现，未误声称零维 PDE 结论。

原 PeriodicWeakTrajectory 的 value 是 Icc 上连续 H 迹且端点匹配，derivative 满足对所有紧支光滑时间测试的弱恒等式；value、derivative 和实际 A 字段均为 MemLp。domainValue 在不属于 D(A) 的例外时刻置零，并只通过 domainValue_ae 与原值相等。第 6、8 项分别在真实时间积分内使用这个 a.e. 身份，没有要求每时刻原 value∈D(A)，也没有把原连续迹替换为点态域轨道。

## 四项真实能量和可积性

已展开 `sobolevGeometry` 的 space、observation、derivative、gradient 字段及 `TransferGeometry.continuousEnergy` / trajectory：trajectory 就是原 domainValue 的 inclusion。heat 的 c₀=3、唯一 c₁=1、o=3。值项与唯一导数项分别处理，没有漏掉总和或误用完整 graphSq。

记 θ=exp(qρ)、G(u)=field₁(dirichletDomainJet(u.domainValue))，三项等式对应四个原量：

| 项 | 实际函数和指数 | 原能量 |
|---|---|---|
| 值 | u.value，s=3 | ∫₀ᵀ q³‖θu‖²L²(Ω) |
| 梯度 | G(u)，s=1 | ∫₀ᵀ q‖θ∇u‖²L²(Ω) |
| 残差 | ε·u.derivative+A(u.domainValue)，s=0 | ∫₀ᵀ‖θ(ε∂tu−Δu)‖²L²(Ω) |
| 观察 | cutoff(W)u.value，s=3 | ∫₀ᵀ q³‖θu‖²L²(W) |

`zero_multiplier_seminorm_eq_exp` 经两个实际 map_ae 和 Lp.ext 识别同一空间 Lp 元素；τ=0 的 q 因子为 1。`timeSq_eq_exp_of_eqOn` 在满测 Ioo 上逐点使用原 q。这里采用 w.q 与自身相等，故没有延拓差异。梯度是 θ∇u，不是 ∇(θu)；ε=−1 时仍是 −∂t+A，而不是将整个算子取负。

真实 cutoff 的 value 为 1_W、界为 1；observation 是空间乘子范数与该 Lp map 的复合。已读 observation_sq_integral，确认其平方就是 W 上积分。最终 W⊆Ω，因此实际观察区域恰为 W；不要求 indicator 连续，不扩张区域，也不增加倍数。残差的辅助等式甚至对任意实 ε 成立，最终才把 Orientation.sign 化为 ±1。

通用精确积分等式本身可对未给时间正则的 w 书写；最终 CE 使用 IntervalQClass 的 C² 连续性，实际 q 有限有界且强可测。原 value、derivative、A 字段具有 L² 资格；梯度由既有 dirichletTrajectory_gradient_memLp 从同一 periodicEnergy/jet 身份内部得到 L²；观察由有界 cutoff CLM 保持 L²。实际加权时间乘子及 norm-square 身份保证四项确为有限 L² 能量。已重读 BoxWeakHeatEstimate 中实际光滑柱积分等式与 core CE 的清偿调用，以及 WeakTrajectoryHeatEnergies 中原图/原轨道字段恢复，未通过不可积函数的 totalized integral 默认值制造结论。

## 区间权条件、量词和接口边界

IntervalQClass 的九个字段分别为 β>0、qc≥1、Icc 上 C²、qc 下界、一阶预算、二阶预算、值端点匹配、一阶端点匹配、二阶端点匹配。二阶始终是同一 Icc 内两次 derivWithin，不是任意域外延拓的环境导数。结构不单独要求 T>0 或指定 qmax：最终 T=g.period>0，qmax 由 TimeWeight.max 提供；原闭区间连续 q 的有限上界及合法 TimeWeight 包装已经由 T165 内部构造。

第 10 项只调用 ofContDiffOn，提取 derivative=derivWithin q Icc、HasDerivWithinAt、原一阶预算和零阶端点匹配。它没有删除第 11 项所需的二阶预算或两个导数端点条件，也没有证明仅一阶 TimeWeightRegularity 足以得到 CE。原 TimeWeight 的实际结构只有全实轴上下界，并无全局 C² 或周期字段；本批没有把注释里的“periodic extension”误当作额外定理。第 11 项保留现有数值转移使用的 w 载体；任意原区间 q 的不依赖载体结论由 T165 供应，本批不声称一个反向的权正则性蕴含。

第 11 项先从 box_original_weak_C2_heat_both_signs 取得 c、λ、β、qc、C，再引入 X/F/Y、三种数值 seminorm 及其 definiteness、g、w、IntervalQClass、s、U。β、qc、C 的正性和 β≤1 原样保留；同一 ρ 与 C 对全部方向和状态有效。X 无有限维输入，F/Y 无有限维输入，所有数值范数仅为原 TransferGeometry 字段，未用于确定连续常数。任意 T>0 可用 steps=1、dt=T 表示，网格步数和节点不进入 C。

证明逐项把 hq.smooth、三个端点、lower、first_bound、second_bound 传给实际原弱盒定理，最后仅以三个精确能量等式改写。不含再次吸收、放大 C、缩小 β、频率截断或状态限制。已直接对照 `Transfer/OriginalUniform.lean:46–50` 和 `Transfer/ScaleUniform.lean:46–49`：输出就是同一 sobolevGeometry、同一原 A 和 domain_le、两方向及全部 U 的 continuous 假设。后续调用仍需原其他解析/数值条件；本报告没有据此宣称完整具体差分估计或完整一般几何 P024 完成。

## 固定依赖、公理和本机证据

四模块 Carleman 导入闭包共 **386** 文件，除四个新增模块外的 **382** 文件与 mathematical_base 逐字节相同。关键旧接受版本的完整递归闭包另行比较，均无变化：

| 依赖 | 接受版本 | 比较入口及闭包文件数 |
|---|---|---|
| C181 / T165 | `7e994b40b5fa75256961286178b81124fc9e1632` | BoxOriginalWeakHeat；374 |
| C180 / T164 | `3eef6d37a89f75f890de1a12aa8fe1f976217e04` | BoxWeakHeatEstimate；360 |
| C179 / T163 | `61ddd47f394ef2a5c61e3ccc317ace118ab816b5` | DirichletHeatContinuity；315 |
| C085 / T069 | `d13e4bc8af28b91a2c2d65091a911baa174950c4` | DirichletCommutatorIdentity；83 |
| C056 | `4f669626b3228adea39a16fbf6c1d22313763331` | DirichletForm；49 |
| C011/C012 | `8706e95e3a24b09fe6e2675a0c72c827ba9a93f3` | ScaleExponents；16 |
| C023 | `e4b308fc21cd669906716aa9af53f1c2a263b1a7` | SobolevGeometry；37 |
| C022 | `a6c199412758d406be8c3f8d1e76587b9f820bc1` | DifferentialExpression；18；CellRegularity；16 |

已重读本批调用的上述实际证明及 OperatorMultiplier、SobolevRealization、OriginalForm、WeakSolution、SobolevGraph、WeightedNorm、Observation、IntervalHeatEnergies、WeakTrajectoryHeatEnergies 和 BoxIntervalWeakHeat；读取 T165 固定验收报告仅作依赖范围交叉核对。十一项实际 #check/#print axioms 均在固定检查器中，四模块均由根目标导入。新源码未出现 sorry、admit、新数学 axiom 或 native_decide。

检查器实际遍历 privateToUserName 下的所有 Carleman 常量并递归 collectAxioms，仅准许 propext、Classical.choice、Quot.sound。固定 raw 的 **3029** 条显式公理打印记录（**3025** 个不同名字）均为空或仅含这三项正常基础公理；这些打印数量与递归总数分开。末行实际为 `Axiom audit passed for all 8020 Carleman declarations.`。

实际读取 `/tmp/carleman-t166-box-transfer-target4.log`：最终 BoxHeatContinuous **3608 jobs** 成功；`/tmp/carleman-t166-heat-transfer-geometry-build.log`：根目标 **4085 jobs** 成功。`-axioms.log` 是零字节 stderr，不把空文件当作审计结论。固定 Lean pin 为 4.35.0，CI 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与实际干净本机 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 独立同 SHA CI 和工件

本 Agent 独立查询 [run 39255115603 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39255115603/attempts/1)，确认 main、精确 head SHA、最终 `completed/success`，run updated_at=`2026-10-19T12:53:30Z`。三个作业均实际最终成功：

| job | 实际 ID | 最终状态 |
|---|---|---|
| state-check | `118068343618` | completed / success |
| lean | `118068343176` | completed / success |
| dashboard / snapshot | `118069884276` | completed / success |

本 Agent 自行执行 gh run download 下载同 run 的 `lean-ci-result`（artifact **12187791937**，API 归档大小 492 bytes）和 `lean-declaration-evidence`（artifact **12187642207**，230675 bytes）；二者未过期，工件元数据 head_sha 精确匹配 checked_sha。没有使用主执行者的下载副本代替独立下载。

实际 `/tmp/carleman-t166-heat-transfer-geometry-main-ci/result.json`：537 bytes，SHA256 `c83a3aeae68bfdb450b899e43e63fbb0f7793dfb772b9d662459de0cf95af3e6`；status=PASS，checked_sha=source_head_sha=`28789e8973368055acc0c17d5b395332e6ee7364`，targets=[Carleman]，finished_at=`2026-10-19T12:52:20.739310+00:00`，ci_url 为同一 run/attempt，工具链与固定 pin 一致。

独立下载的 `/tmp/carleman-t166-heat-transfer-geometry-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t166-heat-transfer-geometry-local-axioms.txt` **逐字节相同**：各 **2482476 bytes**，SHA256 均为 **`822d024d0e5569897e8ee1d7ee56a1d7208f351fc996da09d7115d11263b9344`**；原始完整类型、公理输出和 8020 项递归 PASS 一致。压缩工件大小不与 raw 文件大小混同。

## 签发

**11/11 PASS，C182 可在 AUXILIARY 范围登记 REVIEWED。** 真实完整梯度、原域身份、四项能量、原区间权及先于全部数值/时间/方向/状态的同一常数均通过；未发现阻断性数学或量词缺陷。仅清偿盒域 continuous 接口，不提升 P024，覆盖保持 17/26。报告正文与 reviewed_at 冻结；只提交本报告，不 push。
