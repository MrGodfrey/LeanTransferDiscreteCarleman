# T165 / C181 独立本机验收：原闭区间权与原弱轨道的盒 Carleman 估计

- checked_sha / source_sha：`7e994b40b5fa75256961286178b81124fc9e1632`
- mathematical_base：`3eef6d37a89f75f890de1a12aa8fe1f976217e04`
- reviewed_at：`2026-10-19T12:45:52+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **14/14** 显式声明通过。
- scope：**AUXILIARY — 原连续 CE 在任意正坐标盒、全部原区间权和全部原弱周期轨道上的完整实例**。C181 可登记 REVIEWED；**一般凸多面体尚待，P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

本 Agent 从固定 Git 对象读取五模块全部源码、十四项实际展开类型、原稿、T165 分析、MATH_SPEC、台账及关键依赖；复核已读治理协议版本未变。独立查询实际同 SHA 三个 CI job，并自行下载同 run 的原始 result/raw、逐字节比较固定本机副本。执行者说明、既有验收与 CI 没有替代数学核查。动态 `.ci/axioms.txt` 及未来 HeatGradientExpression / DirichletHeatGeometry 等工作树增量均排除。仅新增并单独提交本报告，不改实现、台账、根导入、审计或原稿，不 push；签发后冻结正文及时间。

## 原文、最终对象与完成范围

固定 `paper/main.tex:292–299` 要求 q∈C²([0,T])，0、1、2 阶端点匹配，1≤qc≤q≤qmax、|q′|≤βq²、|q″|≤β²q³；qmax 可取闭区间最大值。`374–381` 要求原 Pε=ε∂t+A 的加权估计，`2672–2675` 对 Dirichlet Laplacian 取指数 (3,1;3)、原空间梯度和全部 `H¹_tH∩L²_tD(A)` 周期状态。本批最终定理直接量化原 q 和 `PeriodicWeakTrajectory`，不再要求调用者提供 TimeWeight、延拓或 PeriodicGraph 包装。

最终域为任意正边长坐标盒，维数写作 d+1，覆盖全部正整数维。W 只要求非空、开且 W⊆Ω，因而包含原非空紧包含观察开集的情形；不存在额外观察边界正则性或边界零测前提。空间相位真实为 `ρ(x)=exp(−λ‖x−c‖²)−2`，c∈W、λ≥1，并在全空间满足 −2<ρ≤−1。没有要求盒关于 c 对称。

**盒域实例已经覆盖原权和全部原弱轨道，且没有残留 hCE 或给定逼近前提。** 仍不能据此把 P024 的全部几何范围提升为 PAPER：一般凸多面体未证明。与后续通用转移几何及具体离散实例的包装亦不属于本批。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未改写原命题。

## 十四项声明逐项核对

下表路径前缀为 `Carleman/`，行号均指 checked_sha。清单及顺序与固定 C181 / T165、`/tmp/carleman-t165-original-box-weak-declarations.json` 完全一致。共十二项定理、两项实际能量定义；完整展开类型已逐项读取。

| # | 完整声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.exists_timeWeight_eqOn_interval` | `Weights/IntervalTimeWeight.lean:12` | PASS。原 Icc 连续且≥1的 q 经实际闭区间投影构造全实轴有界连续 w.q；整个 Icc 精确恢复 q，有限上界内部构造。 |
| 2 | `Carleman.eqOn_interval_within_derivatives` | `Weights/IntervalTimeWeight.lean:28` | PASS。同一集合上的 EqOn 经真实 derivWithin_congr 两次作用，精确保留值及一二阶区间导数，包括端点。 |
| 3 | `Carleman.SpatialProfile.zero_multiplier_seminorm_eq_exp` | `Spatial/IntervalHeatEnergies.lean:15` | PASS。两个真实空间乘子的 Lp map 由 a.e. 代表相等识别，τ=0 后恰为 exp(qρ)，没有额外 q 因子。 |
| 4 | `Carleman.SpatialProfile.timeSq_eq_exp_of_eqOn` | `Spatial/IntervalHeatEnergies.lean:24` | PASS。实际 timeMeasure 的满测 Ioo 内恢复原 q，再用 integral_congr_ae 给任意实指数的精确能量身份。 |
| 5 | `Carleman.dirichletIntervalHeatLeft` | `Spatial/IntervalHeatEnergies.lean:40` | PASS。定义原 q³ 值项与 q 弱梯度项，使用真实 expMultiplier 及原周期图字段。 |
| 6 | `Carleman.dirichletIntervalHeatRight` | `Spatial/IntervalHeatEnergies.lean:45` | PASS。定义原 ε·dtime+A 残差的 q⁰ 项和真实 cutoff 观察的 q³ 项。 |
| 7 | `Carleman.dirichletHeatLeft_eq_interval` | `Spatial/IntervalHeatEnergies.lean:51` | PASS。对同一 p 精确换回原 q 的两项左侧能量，不改变梯度或常数。 |
| 8 | `Carleman.dirichletHeatRight_eq_interval` | `Spatial/IntervalHeatEnergies.lean:57` | PASS。对同一 p、ε、W 精确换回两项右侧能量，不改变残差符号或观察集合。 |
| 9 | `Carleman.box_weak_interval_C2_gaussian_heat_both_signs` | `Spatial/BoxIntervalWeakHeat.lean:15` | PASS。内部构造 w，逐项传递原 C²、三端点匹配和两导数预算，调用已证完整弱盒估计，再以精确能量身份消去 w。 |
| 10 | `Carleman.dirichletTrajectory_gradient_ae` | `Spatial/WeakTrajectoryHeatEnergies.lean:18` | PASS。原能量字段与 domainValue 的真实 H¹ jet 由同值唯一性相等，继而其全部一阶字段在时间 a.e. 相等。 |
| 11 | `Carleman.dirichletTrajectory_gradient_memLp` | `Spatial/WeakTrajectoryHeatEnergies.lean:33` | PASS。由实际梯度 Bochner Lp 类及第 10 项 a.e. 身份内部得到原 domain jet 梯度的 MemLp，无新增可积性假设。 |
| 12 | `Carleman.dirichletIntervalHeatLeft_trajectory` | `Spatial/WeakTrajectoryHeatEnergies.lean:38` | PASS。恢复同一原轨道 value 和原 domain jet 的完整弱梯度，两项能量准确相等。 |
| 13 | `Carleman.dirichletIntervalHeatRight_trajectory` | `Spatial/WeakTrajectoryHeatEnergies.lean:48` | PASS。实际两层 Lp 代表规则恢复 ε·u.derivative+A(u.domainValue) 与 cutoff(W)u.value，保留同一残差。 |
| 14 | `Carleman.box_original_weak_C2_heat_both_signs` | `Spatial/BoxOriginalWeakHeat.lean:15` | PASS。对任意原 PeriodicWeakTrajectory 调用第 9 项后用第 12、13 项精确改写；所有空间参数和正 C 均先于 g/q/ε/u，双符号、原指数与原权预算完整保留。 |

## 原闭区间权及端点：没有域外假设

第 1 项取原连续函数的实际闭区间 `TracePath Q`，定义 `V=g.clampPath Q`，即以 `projIcc 0 T` 将所有实数投影回闭区间后求 q。V 是真正 boundedContinuousFunction；w.max 取 ‖V‖，全局下界来自投影点属于 Icc，全局上界来自实际 sup 范数。clampPath_on 在整个 Icc 上逐点恢复原 q，包含两端点。qmax 的存在因此内部清偿，没有要求原 q 在区间外有界、正、可测、连续或可微。

该 clamp 延拓一般**不是**全局 C² 或周期函数，源码也没有宣称这些性质。这里 TimeWeight 的实际结构只要求全局上下界；已直接读取其字段，未把注释中的周期措辞当作额外结构条件。后续估计要求的是 Icc 上 C² 和 0、1、2 阶端点匹配，真正周期 C² 延拓由既有 C172 内部完成。不会因为 clamp 在端点附近的域外导数为零而错误迫使原 q′ 的端点值为零。

第 2 项先由 EqOn 得 `derivWithin w.q Icc = derivWithin q Icc` 在同一 Icc 上逐点相等，再对这两个导数函数重复 derivWithin_congr。二阶是同一个 Icc 内的二次区间导数，没有替换为 clamp 的环境全导数。最终 T>0 内部保证闭区间的正常一侧端点导数含义；原 `ContDiffOn ℝ 2` 经 EqOn 转移给 w，值和两阶端点匹配以及两导数预算分别改写，无遗漏端点或缩小 β。

最终 q 的上界没有额外作为输入：原 C² 给闭区间连续和有限最大值，正性由 qc≥1 与 q≥qc 给出。原稿允许任意上界 qmax，取内部有限上界正符合原范围。构造只在给定 g/q 后进行，而 c、λ、β、qc、C 在它们之前已经选择，故延拓的界不能成为估计常数的新依赖。

## 四项实际能量及可积性

已展开 `timeDensity(q,s,p,u)=q(t)^s·p(t)(u(t))²`、`timeSq=∫timeDensity∂(volume|Ioo)` 和 `expMultiplier(r).value(x)=exp(ρ(x)r)`。第 3 项不是只比较乘子上界，而是用两个实际 map_ae、Lp.ext 证明加权 Lp 元素相等，再取同一范数。第 4 项在时间满测 Ioo 内使用 EqOn，因此原 q 的区间外任意行为不会进入时间积分。

记 θ=exp(qρ)、G(u)=field₁(dirichletDomainJet(u.domainValue))。最终四项准确对应：

| 项 | 实际原轨道输入和指数 | 原量 |
|---|---|---|
| 值 | u.value，s=3 | `∫₀ᵀ q³ ‖θu‖²L²(Ω)` |
| 梯度 | G(u)，s=1 | `∫₀ᵀ q ‖θ∇u‖²L²(Ω)` |
| 残差 | ε·u.derivative+A(u.domainValue)，s=0 | `∫₀ᵀ ‖θ(ε∂tu−Δu)‖²L²(Ω)` |
| 观察 | cutoff(W)u.value，s=3 | `∫₀ᵀ q³ ‖θu‖²L²(W)` |

梯度在乘 θ 之前，不是 ∇(θu)；残差是原 ε∂t+A，A=−Δ，ε=−1 时也未把整个算子取负。观察 map 的真实值为 1_W，界为 1，W⊆Ω 时就是原区域 W；没有扩大观察区域、要求示性函数连续或要求其边界零测。四个等式均不损失常数。

任意 q 的辅助能量定义本身不声称可积；最终合法 q 的四项均有实际有限性来源。u.value、u.derivative、A(u.domainValue) 是原 MemLp；观察为有界 CLM；梯度的 MemLp 由第 11 项内部证明。构造出的 w 连续有界，旧 `memLp_map` / timeMap 将这些字段真实地送到加权 Bochner L²，`timeSq_eq_weightedTimeCLM_norm_sq` 给实际有限范数平方。EqOn 和代表身份再把这些相同的密度换回原 q。**没有利用不可积函数 totalized integral 的默认值来制造估计。**

还直接核对 C180 的 BochnerBoxIntegral 和 DirichletHeatIntegral：光滑 core 上先以 `[0,T]×closure Ω` 紧性证明真实加权密度可积，观察项使用可测 indicator 保持可积；随后 integral_prod 与 Ioo/Icc 限制测度相等精确连接四项柱积分。真实弱梯度经 Sym.oneEquiv 的全部一阶坐标平方和对应经典 gradient，系数为 1。其光滑柱估计前提在 BoxWeakHeatEstimate 中用已有 C² 双符号估计实际清偿，未遗留给本批调用者。

## 原弱梯度、代表与全部状态

已直接读取原 `PeriodicWeakTrajectory`：value 在 Icc 上 H 连续且首尾迹相同，value 和 derivative 为真实 L²，弱导数对全部紧支光滑时间测试成立；域资格仅要求时间 a.e.，实际 A 字段为 L²。domainValue 在域资格失败的时间置零，且有真实 `domainValue_ae`。这不是新增每时刻 D(A) 条件，所有后续积分均对这种零测修改不变。

第 10 项同时取实际梯度 compLp 代表、periodicEnergy_embed_ae、tracePathL2_ae 和 domainValue_ae 的时间满测集。该时刻的能量元素给一个真正原 H¹ jet；它的 value 依次等于 pathL2、u.value、domainValue 的值，再由 dirichletDomainJet_value 等于原 domain jet 的 value。`WeakSobolevJet.value_injective` 使用开域上的完整弱导数唯一性证明**整个 H¹ jet 相等**，因此 field₁ 相等，不只是某个范数相等。已核对该唯一性通过全部 Sym 分量及原弱测试归纳，不含预给梯度或光滑代表前提。

这里 dirichletDomainJet 是原 D(A) 值的真实 Sobolev jet；domain_le 与原 H¹₀⊆H¹ 内部供应其资格，dirichletDomainJet_graph 也确认原弱负 Laplacian 为同一个 A 值。梯度 field₁ 是真实 DerivativeFiber 的完整 Hilbert 坐标，Sym.oneEquiv 与 Fin d 一一对应，所以没有维数范数比较损失或只取部分方向。

第 11 项由实际 `dirichletPeriodicGradient` 的 Lp.memLp 沿第 10 项 a.e. 等式转移，得到原函数 t↦G(u)(t) 的强可测性及 L² 资格。第 12 项使用值和梯度的时间 a.e. 身份精确恢复左侧。第 13 项先处理外层 Bochner Lp 的 add/smul/toLp 代表，恢复真正 ε·u.derivative+A(u.domainValue)；观察则用真实 cutoff CLM 的 coeFn_compLp 和原值身份。空间乘法本身由内层 Lp map 定义。没有将嵌套 Lp 代表升级为处处值，或非法交换不可数时间/空间零测例外。

最终 `u.toPeriodicGraph` 仅包装原完整状态，保留每个 Icc 时刻的连续 H 迹、原导数 L² 和实际 A 的 a.e. 字段；已重新核对该转换和逆向代表解释。原周期图的范数控制连续迹、弱导数 L² 和实际 A 的 L²。已验收 C180 通过真实 classical core 稠密性及两侧能量连续性得到全部原图的估计，本批只作无损身份转换，未缩回光滑轨道或有限谐波状态。

## 参数顺序与范围判定

两项最终估计的量词均为：固定 d、盒 Ω、非空开 W 后，先存在 c、λ、β、qc、C（λ≥1、0<β≤1、qc≥1、C>0），再对所有 g、原 q、ε∈{1,−1} 和全部原 p/u 成立。原 `q(0)=q(T)`、一阶和二阶 within 导数端点匹配、qc≤q、|q′|≤βq²、|q″|≤β²q³ 原样保留。不存在 TimeWeight、给定延拓、给定逼近、额外 CE、光滑 PDE 或逐时刻域资格前提。

任意 T>0 可用 steps=1、dt=T 表示，g 的其他离散参数不进入 C。实际 clamp 界以及旧加权 CLM 连续性界可依赖固定 T/qmax，仅用于合法极限和可积性；密度使用闭不等式集，保留同一个 C。最后两次左右能量改写都是相等，没有吸收、放大、频率截断或改变观察指数。两种 ε 使用同一 ρ、λ、β、qc、C。

因此本批完整清偿原连续 CE 的**盒域实例**；一般凸多面体不在声明范围，继续保持 AUXILIARY。没有发现该明确范围内的数学弱化、额外状态限制或尚未清偿的估计假设。

## 固定版本闭包、公理和本机证据

五模块的实际 Carleman 导入闭包共 **374** 文件，其中 **369** 个既有文件与 mathematical_base 逐字节相同。关键调用的已接受版本及其完整递归闭包又分别核对，均未改变：

| 依赖 | 固定接受版本 | 比较入口及闭包文件数 |
|---|---|---|
| C180 / T164 | `3eef6d37a89f75f890de1a12aa8fe1f976217e04` | BoxWeakHeatEstimate；360，真实完整盒弱估计及已清偿光滑 core CE。 |
| C179 / T163 | `61ddd47f394ef2a5c61e3ccc317ace118ab816b5` | DirichletPeriodicGradient；276，真实能量嵌回和 Bochner 弱梯度。 |
| C085 / T069 | `d13e4bc8af28b91a2c2d65091a911baa174950c4` | DirichletCommutatorIdentity；83，原 domain jet 与值/弱图身份。 |
| C025 | `58660cbe195e6af699e0b2edeec93153b1cd3f6d` | PeriodicGraphEquivalence；27，原完整弱轨道转换。 |
| C172 / T156 | `b65d78fa150ea0cc5c0cd7d7b3342e7498b1bc50` | BoxIntervalC2HeatEstimate；138，原区间 C² 预算、双方向光滑估计。 |

已读取 T163、T164 的固定独立报告，同时重读上述关键实际证明、WeakSolution、WeightedNorm、TimeWeight、MultiplierContinuity、TimeL2Multiplier、SobolevRealization、SmoothWeakGradientIdentity 及相关真实图字段；旧报告没有替代本批调用核查。治理协议、工具链、manifest 和 CI 脚本与已读固定版本不变。固定 MATH_SPEC SHA256 为 `825a573c62476fb1da646f95abe6c3e1ccf1d41ce110de10c6fec788fba74a01`。

五模块均在固定根目标导入，十四项均有实际 `#check @...` 与 `#print axioms ...`。新源码没有 sorry、admit、新数学 axiom 或 native_decide。实际检查器按 privateToUserName 遍历全部 Carleman 常量并递归 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。十四项完整类型及公理均已逐项读取；全文 **3009** 条非空公理打印和 **9** 条无公理打印未见其他公理，打印记录数不与递归总数混同。实际末行：`Axiom audit passed for all 7984 Carleman declarations.`。

实际读取 `/tmp/carleman-t165-box-original-weak-target.log` 的 **3596 jobs** 成功，及 `/tmp/carleman-t165-original-box-weak-build.log` 的根目标 **4081 jobs** 成功。`-axioms.log` 为零字节 stderr，不当作通过证据。Lean pin 4.35.0、CI 编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 与实际干净本机 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 独立同 SHA CI 与原始工件

本 Agent 独立通过 GitHub API 查询 [run 39253898566 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39253898566/attempts/1)，确认 main、精确 head SHA 为 checked_sha，最终 run `completed/success`，updated_at=`2026-10-19T12:45:24Z`。三项作业全部最终成功：

| job | 实际 ID | 最终状态 | completed_at UTC |
|---|---|---|---|
| state-check | `118064238148` | completed / success | `2026-10-19T12:40:42Z` |
| lean | `118064238807` | completed / success | `2026-10-19T12:45:11Z` |
| dashboard / snapshot | `118066281935` | completed / success | `2026-10-19T12:45:24Z` |

本 Agent 自行执行 gh run download 下载同 run 两份未过期原始工件：`lean-ci-result` ID **12187220935**（API 归档大小 493 bytes），`lean-declaration-evidence` ID **12186611865**（229578 bytes）。两工件元数据均绑定本次 proof SHA；未使用主执行者的 root 副本代替独立下载。

实际 `/tmp/carleman-t165-original-box-weak-main-ci/result.json` 为 **537 bytes**，SHA256 **`9bc9b0e94bfb3db02c6c981f58e640b967c7d49edf172bdea4d40525c9fd24b6`**；status=`PASS`，checked_sha 与 source_head_sha **均精确等于 `7e994b40b5fa75256961286178b81124fc9e1632`**，targets=`["Carleman"]`，finished_at=`2026-10-19T12:44:00.942643+00:00`，ci_url 指向同 run/attempt，实际 Lean/mathlib 与固定 pin 一致。

独立下载 `/tmp/carleman-t165-original-box-weak-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t165-original-box-weak-local-axioms.txt` **逐字节相同**，各 **2472185 bytes**，SHA256 均为 **`15cd685b2d61987101fa4319b4c0cea22f5b7e7b0ca4b0d97e0f0b96b05efda3`**。完整 raw 含十四项实际类型及 7984 项递归审计 PASS；压缩工件大小与原始文件大小分开记录。

## 签发

**14/14 PASS，C181 可在 AUXILIARY 范围登记 REVIEWED。** 任意原闭区间 C² 权、全部原弱周期轨道、真实四项能量、完整弱梯度、双符号及 T 统一常数均通过固定版本核查，未发现具体数学缺陷。完整盒域实例已清偿；一般凸多面体与后续转移几何/实例接口不在本批。P024 不提升，覆盖保持 17/26。报告正文和 reviewed_at 冻结，仅提交本报告，不 push。
