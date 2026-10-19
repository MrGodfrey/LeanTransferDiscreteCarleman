# T162 / C178 独立本机验收：经典微分字段与完整盒周期图逼近

- checked_sha / source_sha：`5ec78c3027e714324439187119dfbfe4765a2af6`
- mathematical_base：`edd51c0e410a3a6e21259fd156f719e60d965500`
- reviewed_at：`2026-10-19T12:12:29+00:00`
- reviewer：独立本机 Agent `/root/accept_spatial_lemma`，未参与本批实现。
- result：**PASS**；axiom_check：**PASS**；全部 **13/13** 显式声明通过。
- scope：**AUXILIARY — 带真实经典时间导数和负 Laplacian 字段的完整盒弱周期图密度**。C178 可登记 REVIEWED；**P024 / prop:continuousCE 不提升，原文覆盖保持 17/26**。

本 Agent 直接读取固定 Git 对象中五模块全部实际类型和证明、完整展开声明、原稿、T162 分析、MATH_SPEC、台账、治理协议及关键依赖；独立查询同 SHA 实际 CI 三个 job，自行下载同 run 原始 result/raw 并逐字节比较固定本机副本。执行者说明、旧验收和 CI 没有替代数学审查。动态 `.ci/axioms.txt` 及未来 WeightedTimeContinuity / PeriodicEnergyField / SmoothWeakGradientIdentity / DirichletPeriodicGradient 等工作树增量排除。仅新增并单独提交本报告，不改实现、台账、根导入、审计或原稿，不 push；签发后冻结正文及时间。

## 原文对应与完整状态范围

固定 `paper/main.tex:2672–2675` 的连续 CE 要求全部原 `H¹(0,T;H)∩L²(0,T;D(A))` 且端点匹配的状态；`2696` 先处理光滑周期状态，`2730` 使用密度。本批在任意正维正边长坐标盒上，证明更强的光滑子空间在**原完整 PeriodicGraph** 中稠密。对于任意原 p，输出同一对序列 Fₙ、Pₙ：Fₙ 全时空 C∞、全局严格 T 周期、每个实时间整个 frontier 上为零；每个闭时间区间时刻，Fₙ 是 Pₙ 迹的真实空间 Lp 代表；对几乎每个时间，原两个 Bochner 字段分别空间 a.e. 等于该 Fₙ 的实际 ∂tFₙ 和 −ΔFₙ；最后 Pₙ 在完整图拓扑收敛到 p。

最终输入没有光滑性、给定逼近序列、额外空间代表、每时刻 D(A) 归属或经典字段假设。只需 d>0、每个 aᵢ<bᵢ 和任意原 TimeGrid；后者的正周期可实现任意 T>0，例如 steps=1、dt=T，不产生时间尺度限制。一般开且有界域上的 core 定义和谐波成员引理不等于一般多面体密度；最终稠密性明确限盒域。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。

本批较 C177 增加的是**同一代表的经典微分字段身份**，不是只重复迹身份。尚未把这些字段与原空间梯度、实际加权柱积分逐项连接并传递完整弱 CE；一般凸多面体仍待。因此不提升 P024，也不将全时空光滑逼近本身计作完整 Carleman 命题。

## 全部十三项声明

下表路径前缀为 `Carleman/`，行号均指 checked_sha。清单及顺序与固定 C178 / T162、`/tmp/carleman-t162-classical-periodic-density-declarations.json` 精确一致。共十二项定理和一项带实际闭合性证明的 Submodule 定义；完整展开类型已逐项读取。

| # | 完整声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.directionalLap_add` | `Spatial/SmoothDifferentialLinearity.lean:13` | PASS。真实两次常方向 Fréchet 导数的有限和对两个 C∞ 函数相加线性，第二次求导的光滑性内部供应。 |
| 2 | `Carleman.directionalLap_const_mul` | `Spatial/SmoothDifferentialLinearity.lean:20` | PASS。实际两次方向微分与实常数相容；没有把空间变系数当常数。 |
| 3 | `Carleman.directionalLap_zero` | `Spatial/SmoothDifferentialLinearity.lean:27` | PASS。直接展开 fderiv 和有限和，零函数真实 Laplacian 为零。 |
| 4 | `Carleman.spatialLaplacian_add` | `Spatial/SmoothDifferentialLinearity.lean:35` | PASS。取真实 Euclidean 标准基，识别原 spatialLaplacian 的加法。 |
| 5 | `Carleman.spatialLaplacian_const_mul` | `Spatial/SmoothDifferentialLinearity.lean:40` | PASS。同一标准基下的实际空间 Laplacian 常数乘法。 |
| 6 | `Carleman.smooth_harmonic_time_derivative` | `Spatial/SmoothDifferentialLinearity.lean:45` | PASS。实际 HasDerivAt 链式法则给 −ωsin(ωt)φ+ωcos(ωt)ψ；空间函数仅在固定 x 求值，无不必要空间正则前提。 |
| 7 | `Carleman.smooth_harmonic_spatial_laplacian` | `Spatial/SmoothDifferentialLinearity.lean:55` | PASS。固定 t 的 cos/sin 为真实空间常系数，ΔF=cos(ωt)Δφ+sin(ωt)Δψ。 |
| 8 | `Carleman.CoerciveForm.harmonicGraph_derivative_ae` | `Continuous/HarmonicGraphFields.lean:13` | PASS。从同一 harmonicTrajectory 的实际 derivative_L2.toLp 读取原第二字段的时间 a.e. 身份。 |
| 9 | `Carleman.CoerciveForm.harmonicGraph_operator_ae` | `Continuous/HarmonicGraphFields.lean:18` | PASS。实际 operator_L2.toLp、domainRepresentative、线性 A 与 graphDomain_operator 共同给原第三字段，未另指定算子。 |
| 10 | `Carleman.classicalDirichletTimeCore` | `Spatial/ClassicalDirichletTimeCore.lean:16` | PASS。原完整周期图内同一个 F 同时满足光滑、周期、全边界零值、逐时刻迹和两个经典字段；零、加法、实乘均以两层真实 Lp 代表规则证明闭合。 |
| 11 | `Carleman.harmonicGraph_mem_classicalDirichletTimeCore` | `Spatial/ClassicalHarmonicTimeCore.lean:14` | PASS。用两个真正 SpatialTest univ 系数构造同一 cos/sin 代表，值与算子身份共同确定其实际 ∂t 和 −Δ 字段，负号全部一致。 |
| 12 | `Carleman.box_classicalDirichletTimeCore_dense` | `Spatial/BoxClassicalTimeDensity.lean:14` | PASS。对任意两个原空间图系数调用真实盒图逼近，内部供应 graphH、graphA 及边界三组身份，再经完整谐波密度得到强 core 稠密。 |
| 13 | `Carleman.exists_box_classical_periodic_graph_approximation` | `Spatial/BoxClassicalTimeDensity.lean:35` | PASS。任意原 p 得同一 Pₙ→p 和 Fₙ；两层 a.e. 的方向微分身份用真实时空链式法则改写为经典 ∂t/−Δ，保留每个 Icc 时刻迹与所有边界点。 |

## 实际导数、算子字段和负号

已展开旧定义：`smoothD e f x = fderiv ℝ f x e`；`directionalLap e f = Σᵢ smoothD(eᵢ)(smoothD(eᵢ)f)`；`spatialLaplacian` 是 Euclidean 标准基的真实纯二阶导数和。前三项使用已验证的 fderiv 加法/常数乘法和 smoothD 的 C∞ 保持性，继而有限求和；不是形式符号代数或人为赋予导数。

对频率 ω，时间公式由实际 cos/sin 的 HasDerivAt 组合得到，时间导数正是 `−ω sin(ωt) φ(x)+ω cos(ωt) ψ(x)`。空间公式在固定 t 下使用真正空间常数。`spaceTime_timeD` 通过路径 s↦(s,x) 的 Fréchet 链式法则得到 ∂t；`spaceTime_directionalLap` 对各路径 y↦(t,y) 连续求导两次再求和。后者只取 `(0,eᵢ)` 空间方向，不含时间二阶项，也没有缺少因子或符号。

第 8 项读取的是构造原图的那一个 harmonicTrajectory 的 derivative_L2.toLp，不是假设某个任意导数等于经典导数。第 9 项先由 operator_L2.coeFn_toLp 读取真实 A(domainRepresentative(...))；`harmonicDomain_representative` 用每时刻的线性域成员资格证明该代表就是实际 harmonicDomain，`harmonicDomain_operator` 和 `graphDomain_operator` 给 `cos(ωt)graphA(x)+sin(ωt)graphA(y)`。这些逐时刻域事实只用于光滑谐波生成元，不施加给任意原弱 p。

生成元选择同一 `F(t,x)=cos(ωt)φ(x)+sin(ωt)ψ(x)`。入口显式使用 graphH(x)=φ|S、graphH(y)=ψ|S、graphA(x)=−laplacianOnLp(φ)、graphA(y)=−laplacianOnLp(ψ)。空间 Lp 的 neg/smul/add 代表规则和 laplacianOnLp_ae 给算子代表 `−cos(ωt)Δφ−sin(ωt)Δψ=−ΔF`。因此最终字段是 **A=−Δ**，既没有错误取 +Δ，也没有把整个热算子的负号混入空间 A。

频率是实际 `k·2π/T`，k 遍历全部整数，包含零和负频率。`angularFrequency_period` 与三角函数的整数周期公式证明 F 在所有时空点严格满足 `F(t+T,x)=F(t,x)`，不只两个端点相同。系数在全部 frontier 上为零直接给每个实 t 的全部边界点零值，包括面交与角点。

## 两层 Lp 类和共同代表

core 的 carrier 是 `∃ F, ...`，这个存在量词在光滑、周期、边界、迹和两字段条件之前。迹条件是 `∀t:Icc 0 T` 的空间 a.e. 身份。字段条件则为 `∀ᵐt∂timeMeasure`，同时具有空间 a.e. 的 dtime 身份和 A 身份。不存在用不同 F 分别满足各条件的漏洞，也不把外层 Bochner 类的代表看成每时刻处处正确。

零元证明先用外层 `Lp.coeFn_zero` 确认时间代表值为零空间 Lp 类，再用内层 `Lp.coeFn_zero` 确认空间代表。加法与实数乘法同样先在外层取两个字段的 a.e. add/smul 身份，再在内层使用空间 add/smul 身份，并结合实际经典微分线性性。有限个时间零测例外可合并，内层空间例外可依赖该时间；证明没有非法把不可数时间或空间量词交换到统一零测集之外。

谐波成员证明以第 8、9 项在外层取同一个时间上的两个真实字段，再分别应用内层 Lp 代表规则。迹身份独立地对每个闭区间时刻证明，所以端点没有因时间 a.e. 身份被丢掉。最后从强 core 稠密性选一个 P 序列，再对每个 Pₙ 的共同存在见证选择 Fₙ；不是分别为迹、导数、算子挑选不同序列。第 13 项仅用实际时空微分恒等式改写两个字段，保留同一 Fₙ、Pₙ 和两层 a.e. 结构。

## 完整图拓扑、原弱状态及密度传递

已直接读取 `PeriodicGraphSpace`、`PeriodicGraphEquivalence`、`WeakTimeSpace` 和 `FormTimeGraph`。原 `PeriodicFields` 是 `C([0,T];H) × (L²_tH × L²_tH)`；图条件是全部实际时间测试及全部 H 方向的弱导数恒等式、真实 a.e. operatorGraph 和两个端点 H 迹相等。算子图以真实 resolvent 核刻画，并证明与 a.e. 原域资格及实际 A 等价。弱导数通过全部 SpatialTest 的积分恒等式和唯一性定义，没有把值、导数和载荷自由拼接。

该闭子空间继承乘积范数，实际图范数为 `max ‖trace‖∞ (max ‖dtime‖L² ‖A‖L²)`。所以 `Tendsto P atTop (𝓝 p)` 同时控制连续 H 迹的一致范数、真实时间导数 L²、真实算子 L²；`pathL2` 的实际 CLM 还给值的 Bochner L² 收敛。它不是仅值 L² 或弱拓扑收敛。原任意 PeriodicWeakTrajectory 经 toPeriodicGraph 保留全部 Icc 迹、实际导数和 a.e. 算子，不添加每时刻 D(A) 归属；反向图转换亦已核对。因此最终 ∀p 覆盖原完整状态空间。

重新核对 C177 的谐波传递：harmonicGraphCLM 的输入为两个实际 operatorGraph 系数，输出为完整 PeriodicGraph；其闭图证明利用连续迹评价、实际 graphH 连续性和原弱导数/算子唯一性得到整个图相等，故有真正完整图连续性。全部 L² 载荷的有限谐波稠密性经原连续满射逆解算子 constantSolve 进入完整周期图。该逆来自已证原 evolution 的单射和满射，未使用待证 CE，也没有留下载荷子空间限制。

第 12 项对任意 k,x,y，分别用已证 `exists_box_smooth_operator_graph_approximation` 得 Xₙ→x、Yₙ→y，以及同一空间测试的 graphH、graphA、全边界零值三组身份。它把全部身份交给第 11 项，清偿其明确前提；尤其没有只使用 graphH 后推测 graphA 正确。实际谐波 CLM 连续性把这些生成元送入强 core 闭包，再由子空间和有限谐波稠密性覆盖全部原周期图。第 13 项在实际度量子空间中用 `mem_closure_iff_seq_limit` 选取序列，合法且无额外可分性假设。

本批没有引入 q、权族或 CE 常数，也不声称逼近速率。近似序列和连续性常数可以依赖 T、频率、盒与目标状态；它们只用于密度，未被当作应独立于 T 的 Carleman 常数。缺失的空间梯度及加权柱积分识别明确仍是后续义务。

## 版本闭包和公理

实际五模块导入闭包共 **295** 个 Carleman 文件，其中 **290** 个既有文件与 mathematical_base 逐字节相同。直接调用的已验收依赖连同其整个递归闭包分别比对如下：

| 依赖 | 固定接受版本 | 完整闭包与使用情况 |
|---|---|---|
| C177 / T161 | `edd51c0e410a3a6e21259fd156f719e60d965500` | HarmonicStateDensity 起始 61 模块全部未改；实际图谐波连续性、全图稠密和真实字段构造。已读独立报告并重新检查关键证明。 |
| C176 / T160 | `d5a8ab859e4413c6eb950702df73990e356c3786` | BoxSmoothGraphDensity 起始 276 模块全部未改；对任意原图元素内部提供空间光滑图逼近、值和负 Laplacian 两投影身份。 |
| C161 / T145 | `ccbd7a887ed37afbc4d4e530d06b885350e74b3a` | SpacetimeHeatIdentity 起始 81 模块全部未改；实际时间方向与空间 Laplacian 的链式法则，不调用目标弱 CE。 |

五模块均在固定 Carleman.lean 导入，十三项均有固定 `#check @...` 和 `#print axioms ...`；没有漏列、sorry、admit、新数学 axiom 或 native_decide。实际审计脚本遍历全部环境常量，以 privateToUserName 保留私有声明，再递归 collectAxioms，仅允许 `propext`、`Classical.choice`、`Quot.sound`。

已逐项读完十三项 raw 完整类型及公理集合，均仅依赖上述三项正常基础公理。完整 raw 有 **2965** 条非空公理打印记录和 **9** 条无公理记录，无其他公理；此打印记录数不与全量递归审计数混同。实际末行是 `Axiom audit passed for all 7799 Carleman declarations.`。

本机实际定向日志 `/tmp/carleman-t162-box-classical-density-target.log` 为 **3502 jobs** 成功；`/tmp/carleman-t162-classical-periodic-density-build.log` 为根目标 **4067 jobs** 成功。`-axioms.log` 实际为零字节 stderr，不作为审计通过依据。Lean pin 为 4.35.0，CI 编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib pin 和本机实际 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机依赖工作树干净。固定 MATH_SPEC SHA256 为 `33ed3618d65fa2e7cb2848853701e684421da3a07ebf0910999344a7886a54bf`。

## 独立同 SHA CI 和原始产物

独立通过 GitHub API 查询 [run 39249556138 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39249556138/attempts/1)，确认 main、精确 head SHA 为 checked_sha，最终 run `completed/success`，updated_at=`2026-10-19T12:11:47Z`。最终三个 job 均成功：

| job | 实际 ID | 最终状态 | completed_at UTC |
|---|---|---|---|
| lean | `118049708907` | completed / success | `2026-10-19T12:11:29Z` |
| state-check | `118049709271` | completed / success | `2026-10-19T12:07:12Z` |
| dashboard / snapshot | `118051595368` | completed / success | `2026-10-19T12:11:46Z` |

本 Agent 自行执行 gh run download 下载同 run 两个原始 artifact：`lean-ci-result` ID **12184419105**（API 归档大小 493 bytes），`lean-declaration-evidence` ID **12184528849**（226283 bytes）；两者未过期，artifact 元数据的 head_sha 均匹配固定 proof SHA。未用执行者的 root 副本代替独立下载。

实际 `/tmp/carleman-t162-classical-periodic-density-main-ci/result.json` 为 **537 bytes**，SHA256 **`530e7bdcca00f9eaf70413888604edf9c6b3a938ddb70582d13509c97167bb86`**；status=`PASS`，checked_sha 与 source_head_sha **均精确等于 `5ec78c3027e714324439187119dfbfe4765a2af6`**，targets=`["Carleman"]`，finished_at=`2026-10-19T12:10:23.503425+00:00`，ci_url 指向上述同 run/attempt，Lean/mathlib 与固定 pin 一致。

独立下载 `/tmp/carleman-t162-classical-periodic-density-main-axioms/axioms.txt` 与固定 `/tmp/carleman-t162-classical-periodic-density-local-axioms.txt` **逐字节相同**，各 **2433363 bytes**，SHA256 均为 **`df4daf04c607a2ea591d71656fa19d93465458b8ac1c32564d232e51c850336e`**。完整 raw 包含上述十三项实际类型和 7799 项递归审计 PASS；压缩归档大小与原始 raw 大小分开记录。

## 签发结论

**13/13 PASS，C178 可在 AUXILIARY 范围登记 REVIEWED。** 未发现真实字段、负号、两层 Lp 代表、共同序列、完整图范数、原状态范围或依赖公理方面的缺陷。原盒全部弱周期轨道的经典字段图逼近已清偿；空间梯度和加权积分传递、完整弱 CE、一般凸多面体尚待。P024 不提升，覆盖保持 17/26。报告正文及 reviewed_at 签发后冻结，仅本报告单文件提交，不 push。
