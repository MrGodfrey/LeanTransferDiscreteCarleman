# T161 / C177 独立本机验收：完整盒弱周期图的光滑零边界密度

- checked_sha / source_sha: `edd51c0e410a3a6e21259fd156f719e60d965500`
- mathematical_base: `d5a8ab859e4413c6eb950702df73990e356c3786`
- reviewed_at: `2026-10-19T12:03:08+00:00`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- result: **PASS**；axiom_check: **PASS**；scope: **AUXILIARY**。
- 四模块十六项声明通过固定版本验收。C177 可以升级为 REVIEWED 并保持 AUXILIARY；P024 / 完整连续 CE 不提升，原文完整结果覆盖保持 **17/26**。

## 原文、实际对象及范围

逐项读取固定 Git 对象中的四模块、十六项完整展开类型、实际证明和关键旧依赖，对照原 `paper/main.tex:2672–2675` 的连续 CE 全弱状态量词、`2696–2704` 的光滑零边界计算及 `2730` 的密度步骤。原状态为 `H¹(0,T;H) ∩ L²(0,T;D(A))` 且两端迹匹配。本批在正边长坐标盒上，证明原完整 PeriodicGraph 中的实际光滑、严格周期、全边界零值代表稠密，并输出同一逼近序列；不直接给出弱 CE 的加权积分估计。

已读取固定 `governance/analysis/T161-box-periodic-density.md`、`governance/MATH_SPEC.md` 的对应段、声明清单及台账版本，遵循根 AGENTS 和适用治理协议。执行者说明与 CI 未代替语义审查。固定原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改。后续工作树中的 SmoothDifferentialLinearity、HarmonicGraphFields、ClassicalDirichletTimeCore、ClassicalHarmonicTimeCore、BoxClassicalTimeDensity 及动态 `.ci/axioms.txt` 不作为本次依据。

## 十六项声明逐项验收

下表位置均指 checked_sha，顺序与固定 `/tmp/carleman-t161-box-periodic-density-declarations.json` 一致。四模块均在固定 `Carleman.lean` 导入，十六项均在固定 `tools/CheckAxioms.lean` 审计，全部展开类型已实际读取。

| # | 显式声明 | 固定源码位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.CoerciveForm.harmonicGraph` | `Carleman/Continuous/HarmonicGraphContinuity.lean:16` | PASS。从两个实际 operatorGraph 系数，经原 harmonicTrajectory 构造原 PeriodicGraph；值、弱导数及实际算子字段随同构造。 |
| 2 | `Carleman.CoerciveForm.harmonicGraph_trace` | `Carleman/Continuous/HarmonicGraphContinuity.lean:19` | PASS。每个闭区间时刻的真实 H 迹精确为原 cos/sin 组合。 |
| 3 | `Carleman.CoerciveForm.harmonicGraphLinear` | `Carleman/Continuous/HarmonicGraphContinuity.lean:23` | PASS。系数加法/实数乘法通过真实迹公式及 PeriodicGraph.trace_injective 证明整个图元素线性。 |
| 4 | `Carleman.CoerciveForm.harmonicGraph_continuous` | `Carleman/Continuous/HarmonicGraphContinuity.lean:42` | PASS。输入与输出均为实际 Banach 图空间；逐点迹极限和迹单射性证明闭图，继而得到完整图拓扑连续性。 |
| 5 | `Carleman.CoerciveForm.harmonicGraphCLM` | `Carleman/Continuous/HarmonicGraphContinuity.lean:60` | PASS。将同一真实线性映射和第 4 项连续性包装为 CLM，没有更换范数或对象。 |
| 6 | `Carleman.CoerciveForm.harmonicGraph_mem_core` | `Carleman/Continuous/HarmonicStateDensity.lean:15` | PASS。显式图值 U(t)、dU(t) 的连续性与真实 HasDerivAt 给原 regularTimeCore 归属。 |
| 7 | `Carleman.CoerciveForm.harmonicStateSpan` | `Carleman/Continuous/HarmonicStateDensity.lean:32` | PASS。定义全部整数频率、任意两个实际图系数的谐波轨道之有限线性张成。 |
| 8 | `Carleman.CoerciveForm.harmonicStateSpan_le_core` | `Carleman/Continuous/HarmonicStateDensity.lean:35` | PASS。由原 core 的子空间结构和生成元归属推出全部有限组合归属。 |
| 9 | `Carleman.CoerciveForm.frequencyGraph_mem_harmonicStateSpan` | `Carleman/Continuous/HarmonicStateDensity.lean:40` | PASS。两方向、r≥0 的真实 frequencyCos/frequencySin 经 graphOfDomain 给同一个 frequencyGraph，未另选替身解。 |
| 10 | `Carleman.CoerciveForm.constantSolve_harmonic_mem` | `Carleman/Continuous/HarmonicStateDensity.lean:50` | PASS。原 evolution 单射性及两个真实方程确定 constantSolve 对每个谐波载荷的像；线性张成归纳覆盖全部有限载荷。 |
| 11 | `Carleman.CoerciveForm.harmonicStateSpan_dense` | `Carleman/Continuous/HarmonicStateDensity.lean:68` | PASS。完整 L² 载荷谐波稠密性经实际满射连续逆解算子传到完整 PeriodicGraph。 |
| 12 | `Carleman.CoerciveForm.dense_of_harmonic_approximation` | `Carleman/Continuous/HarmonicStateDensity.lean:80` | PASS。每一对图系数的实际收敛序列，通过同一 harmonicGraphCLM 进入目标子空间的闭包；有限谐波稠密性完成传递。 |
| 13 | `Carleman.smoothDirichletTimeCore` | `Carleman/Spatial/DirichletSmoothTimeCore.lean:15` | PASS。原 Dirichlet 周期图中具有全时空 C∞、全局严格周期、全实时间全 frontier 零值及每个闭区间时刻真实 Lp 迹代表的子空间。 |
| 14 | `Carleman.harmonicGraph_mem_smoothDirichletTimeCore` | `Carleman/Spatial/DirichletSmoothTimeCore.lean:49` | PASS。实际两个 SpatialTest 代表与原图系数的值身份，显式构造 cos/sin 乘积代表，完整保留所有时刻和边界点。 |
| 15 | `Carleman.box_smoothDirichletTimeCore_dense` | `Carleman/Spatial/BoxSmoothTimeDensity.lean:14` | PASS。对任意图系数调用已证真实盒算子图逼近，内部清偿第 12、14 项前提，得到完整弱周期图密度。 |
| 16 | `Carleman.exists_box_smooth_periodic_graph_approximation` | `Carleman/Spatial/BoxSmoothTimeDensity.lean:35` | PASS。任意原 p 获得同一序列 Pₙ→p 及逐项代表 Fₙ，输出全时空光滑、严格周期、全部时间全边界零值和每个闭区间时刻的实际迹身份。 |

## 完整图拓扑与闭图证明

固定 `operatorGraph` 是原 associated operator 的真实集合 `{(u,Au)}`，由 `domain.subtype.prod operator` 的 range 定义；其拓扑继承 H×H 的乘积范数。`FormOperator` 用真实 resolvent 等式 `resolventH(a+u)=u` 证明该图闭，故在 H 完备时图为 Banach。不是给 D(A) 随意赋予一个较弱范数。`graphH`、`graphA` 分别是两坐标的实际 CLM，`graphDomain_operator` 保证取回域元素后得到同一个 A。

固定 `PeriodicFields` 精确为 `C([0,T];H) × (L²(0,T;H) × L²(0,T;H))`。`periodicGraphSubmodule` 同时要求：全部真实弱时间测试的导数身份、值与第三字段属于实际 a.e. operatorGraph，以及真实两端 H 迹相同。其闭性分别来自真实弱测试配对的闭关系、resolvent 给出的 Bochner 图闭关系和端点差的 CLM 核。由此得到完整 PeriodicGraph 的完备性。实际范数为

`max (‖trace‖∞) (max ‖weak_dtime‖L² ‖actual_A‖L²)`。

`pathL2` 是闭区间连续迹的真实限制 Bochner 类，因而图范数收敛同时给值的 L² 收敛；没有将连续迹的一致收敛替换成仅 a.e. 时间值收敛。原 `PeriodicWeakTrajectory.toPeriodicGraph` 只用原连续 H 代表、弱导数和 a.e. D(A) 归属构造该图，保留闭区间全部迹以及实际导数和算子 L² 类，不添加所有时刻 D(A) 归属假设。

`PeriodicGraph.trace_injective` 并非把导数/算子字段忽略：相同连续迹给相同 pathL2；真实弱时间导数唯一性确定第二字段，实际 operatorGraph 对相同值的单值性确定第三字段，再由乘积/子类型外延性得到整个图元素相等。已复核 `WeakTimeSpace` 对全部 SpatialTest 和全部 H 方向的定义、与原向量弱导数接口的等价、测试唯一性，以及 `FormTimeGraph` 的实际 a.e. 图解释。

第 4 项对任意系数序列 Uₖ→x 和完整周期图极限 harmonicGraph(Uₖ)→p，先利用真实连续迹评价映射得到每个 t 的 p(t) 极限；另一方面，graphH 的连续性和真实 cos/sin 公式给 harmonicGraph(x)(t) 极限。H 中极限唯一性给全部 t 的相等，再用上述迹单射性得到整个图 p=harmonicGraph(x)。这满足 pinned mathlib `Analysis/Normed/Operator/Banach.lean:551` 的 `LinearMap.continuous_of_seq_closed_graph` 所有前提；该定理要求两端 Banach，已由原图空间内部证明。没有有限维假设，也没有预先假定导数或 A 字段连续。

## 从全部载荷到全部周期图

已读取固定 `HarmonicTrajectory`、`FiniteHarmonic`、`HarmonicDensity`、`ConstantPeriodicExistence` 和 `PeriodicSolutionOperator`。angularFrequency 为 `2πn/T`，真实谐波轨道的导数是 `−ω sin(ωt)x+ω cos(ωt)y`，原 A 通过线性域操作作用于两个系数。`frequencyGraph_equation` 是原有向 `s∂t+A+r` 方程，其真实载荷为同一 harmonicLp。第 10 项使用 evolution 的单射性比较该方程与 constantSolve_equation，严格识别同一个解，并以真实线性映射的零、加法、实数乘法扩展到有限张成。

原 constantEvolutionEquiv 是完整 PeriodicGraph 到全部 Bochner L² 载荷的连续线性等价，其满射性已由有限谐波解、实际闭范围估计及全部载荷谐波稠密性证明，不是在本批把解存在性作为新输入。HarmonicDensity 的真实 Fourier 完备性作用于原未归一化时间测度，并以全部 H 方向的弱测试唯一性处理一般 Hilbert H；不需 H 可分或有限维。

第 11 项固定 plus、r=0 的 inverse constantSolve 作为构造工具。其为连续满射，故全部载荷谐波稠密集的像稠密；第 10 项证明该像包含在 harmonicStateSpan 中。这一选择不会将待逼近状态限制为某个方向的解类：任意原 p 都是其原 evolution 载荷的逆像。原 0 频率也由 coercive form 的实际可逆常系数方程覆盖，不省略常数时间状态。

第 12 项明确以图系数的拓扑收敛为前提，应用同一 harmonicGraphCLM 得到周期图收敛；每个生成元进入 S 的闭包，该闭包是线性子空间，因而容纳全部 harmonicStateSpan，最终得到 S 稠密。最终盒包装对任意 n、x、y 各自调用真实空间图逼近，已内部供应该辅助前提，调用者无需给出谐波序列或空间光滑估计。

## 光滑代表、原 Dirichlet 对象与常数

`smoothDirichletTimeCore` 定义在同一个 `boundedDirichletOriginalForm(...).model.PeriodicGraph g` 中。子空间闭包运算使用实际 F+G 和 cF；每个时刻的代表等式通过 `Lp.coeFn_add`、`Lp.coeFn_smul` 处理 a.e. 代表，未假定不同 Lp 类的选定代表逐点满足代数身份。边界条件则是实际光滑函数在每个实数时间、每个原 frontier 点的严格零值，两种性质被正确区分。

第 14 项显式取 `F(t,z)=cos(ωt)φ(z)+sin(ωt)ψ(z)`。联合 C∞ 性来自真实乘积/复合微分；`ωT=2πn` 及整数周期恒等式证明整个实线上 `F(tx+(T,0))=F(tx)`。两个原空间代表在整个 frontier 零，故 F 对全部时间、全部边界点零。迹身份逐一量化 `t∈Icc(0,T)`，通过真实 toLp 的 a.e. 身份证明，包括两个端点；没有退化为仅 a.e. 时间的等式。

固定 `BoxSmoothGraphDensity.exists_box_smooth_operator_graph_approximation` 对任意原 operatorGraph 元素，内部用已证盒 Dirichlet H² 正则性、原 H¹₀ 归属及空间光滑逼近，产生真实 SpatialTest 序列 Uₖ 和同一图序列 Zₖ。其输出明确为 graphH(Zₖ)=toLp(Uₖ)、graphA(Zₖ)=−laplacianOnLp(Uₖ)，并在实际 operatorGraph 中收敛。第 15 项对两个任意系数分别应用该结论，再经第 14 项得到 smoothDirichletTimeCore 归属；本批没有另输入 H² 正则性、经典域近似、给定序列或有限频率限制。

第 16 项在实际可度量的完整周期图中使用闭包的序列刻画，先取得同一 Pₙ→p，随后从每一 Pₙ 的 core 归属选择相应 Fₙ。因此一条序列同时控制连续迹、弱时间导数及实际 A，Fₙ 是这条 Pₙ 的代表，不是另一个无关的光滑序列。最终输入为任意 hd>0、正边长 a/b、任意 TimeGrid g 及任意 p；没有要求原 p 光滑、有限频率或所有时刻属于 D(A)。正维限制明确写在实际 Dirichlet 模型接口中，本报告不声称 d=0 的盒结论。时间网格在本批只提供 T>0 和原时间测度；任意正 T 可由合法网格实现，未引入 T 的上、下界或节点数相关逼近限制。

闭图 CLM、constantSolve 的连续性及图逼近速率可以依赖固定的 T、频率和形式；这是存在逼近序列所需的连续性，不是 CE 统一常数。已核查原 `TimeGraphBound.regularTimeCore_norm_bound` 明确使用含 `sqrt(T)` 和 `1/sqrt(T)` 的迹控制，而本批只用其既有连续逆/稠密性结论，没有把该常数乘入任何 Carleman 不等式。本批未输出或改变 CE 的 ρ、β、qc、C，故未偷取 T 统一性。

**非阻断范围界限：** 已完成的是完整周期图的真实光滑代表密度。最终声明输出 Pₙ 的弱字段收敛及 Fₙ 的迹身份，但尚未显式将 Pₙ 的两个 Bochner 字段分别识别为 Fₙ 的经典 ∂t 和 −Δ，也尚未完成真实加权时空积分的弱 CE 极限。一般凸多面体同样不在本批范围。这些后续工作与固定规格一致，不妨碍十六项辅助声明通过，但禁止据此提升完整 P024。

## 依赖版本、公理及本机构建

四模块的递归 Carleman import 闭包为 286 个文件，其中 282 个旧文件与 mathematical_base 逐文件内容完全相同。另对以下已接受 declaration_version 的相关完整闭包逐文件比较，均无内容变化：

| 依赖 | declaration_version | 实际比较入口 / 闭包文件数 |
|---|---|---|
| C176 | `d5a8ab859e4413c6eb950702df73990e356c3786` | `Spatial/BoxSmoothGraphDensity` / 276 |
| C175 | `5923dbf398166a48ddf42f98585ff54a10545b0f` | `Spatial/BoxDirichletSmoothDensity` / 253 |
| C026 | `ec0848a447fb0a8a03e544ce453da43c90299ba0` | `Continuous/PeriodicSolutionOperator`、`HarmonicDensity`、`RegularTimeCore` 联合 / 59 |
| C025 | `58660cbe195e6af699e0b2edeec93153b1cd3f6d` | `Continuous/PeriodicGraphEquivalence`、`HarmonicTrajectory` 联合 / 31 |
| C024 | `64a8329f5b7b0b9cba01b8244ffd8170863e75f8` | `Continuous/FormOperator` / 3 |

固定 Lean 为 `leanprover/lean4:v4.35.0`，CI 版本 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`；本机 mathlib HEAD 同值且工作树干净。新显式导入的 Banach 闭图定理已实际读取其前提和证明接口，没有引入未钉住的库或数学公理。

实际读取 `/tmp/carleman-t161-box-smooth-time-density-target3.log`：定向 **3493 jobs** 成功，包含最终 BoxSmoothTimeDensity；读取 `/tmp/carleman-t161-box-periodic-density-build.log`：根目标 **4062 jobs** 成功。`/tmp/carleman-t161-box-periodic-density-axioms.log` 实际为空，不将空 stderr 视作独立审计结果。完整固定 raw 末行为 `Axiom audit passed for all 7765 Carleman declarations.`。

固定 raw 中有 2961 个显式公理打印记录、2957 个不同显式名称；递归检查覆盖 **7765** 项 Carleman 声明。全部打印记录仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理，未见 sorryAx 或新增非基础公理。新十六项的完整类型及公理集合已逐项核实，计数不与递归声明总数混同。

## 独立正式 CI 和原始产物

独立通过 GitHub API 查询 [run 39248518805 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39248518805/attempts/1)：`head_sha=edd51c0e410a3a6e21259fd156f719e60d965500`，最终 run 为 `completed / success`，最后更新 `2026-10-19T12:02:57Z`。实际三个作业全部最终成功：

| 作业 | job ID | 实际结论 |
|---|---|---|
| state-check | `118046285061` | completed / success |
| lean | `118046285608` | completed / success |
| dashboard / snapshot | `118047907506` | completed / success |

验收者自行用 `gh run download` 下载同 run 的两个原始产物，未用主执行者副本代替独立下载：

| 产物 | artifact ID | 独立本机位置 |
|---|---|---|
| lean-ci-result | `12184213607` | `/tmp/carleman-t161-box-periodic-density-main-ci/result.json` |
| lean-declaration-evidence | `12184153567` | `/tmp/carleman-t161-box-periodic-density-main-axioms/axioms.txt` |

实际 result.json 为 `status=PASS`，`checked_sha=source_head_sha=edd51c0e410a3a6e21259fd156f719e60d965500`，目标 `Carleman`，`finished_at=2026-10-19T12:01:38.353861+00:00`；Lean/mathlib 版本与固定 pin 一致。两个 artifact 元数据的 workflow head SHA 也精确同值。

独立读取并逐字节比较远端 raw 与固定 `/tmp/carleman-t161-box-periodic-density-local-axioms.txt`：**完全相同**，均为 **2425799 bytes**，SHA256 均为 `ca219b6e01966fbd28dd5b994025e8d9be6872d4445a996a0f2b78f03d6ca8fd`。未以未来阶段动态 `.ci/axioms.txt` 替代固定证据。

## 签发

**C177：PASS / AUXILIARY。** 十六项真实声明未发现阻断性数学、对象、量词、范数、依赖或公理问题。完整周期图密度、同一逼近序列和光滑代表的全时刻迹身份已通过；经典字段的显式识别、实际弱 CE 积分极限及一般凸多面体仍待。报告只签发上述固定 SHA；正文与 reviewed_at 随报告提交冻结，仅提交本报告，不修改实现或台账，不推送。
