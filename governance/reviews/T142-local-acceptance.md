# T142 / C158：完整原 Proposition 6.2 / P012 独立验收

- checked_sha: `13c8977bd4c50a11d6bed5fdab64b09aeee0203f`
- base_commit: `b818f314b275265490aa9b797779f7db0005ddb9`
- reviewed_at: `2026-10-19T09:06:20+00:00`
- reviewer: 独立数学验收 Agent `/root/accept_section3`
- result: **PAPER / PASS**；axiom_check: **PASS**。
- 原文：Proposition 6.2，`prop:fd`，覆盖项 **P012**。
- extra_hypotheses: **无（相对于原 Proposition 6.2 的设置）**。
- 结论：两项新增定理及本报告逐项核对的固定依赖共同完整覆盖原 N1–N5；C158 与 P012 可登记 REVIEWED / PAPER，原文完成数可由 **16/26 升为 17/26**。P023、P024/连续 CE 和随后离散 Carleman 推论不因此提升。

## 审查范围与全部新增声明

依固定 Git 对象的 AGENTS.md、PROJECT_OPERATIONS、state/README、MATH_SPEC、`governance/analysis/T142-cartesian-full-realization.md`，直接读取两模块全部证明和实际完整展开类型，逐条对照原稿并追溯真实依赖。未把 `Nonempty NumericalData` 当作完整原命题，未仅凭执行者说明、旧报告或 CI 给出结论。工作树后续实现与动态 `.ci/axioms.txt` 不属于本批。

| # | 完整声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `Carleman.cartesian_numericalData_of_box` | Spatial/CartesianBoxNumericalData.lean:15 | PASS。正边长固定盒的实际 Dirichlet 算子域 H² 包含在定理内部证明，随后构造同一实际 FD 对象上的 NumericalData；输出 hD，不把它留作输入。 |
| 2 | `Carleman.cartesian_full_weight_interface` | Spatial/CartesianFullWeightInterface.lean:15 | PASS。对全部允许权，联合给出原指定对角测试及真实导数等式、严格正定性、重构/测试双向比较、实际 lift 界和真实 Hilbert 伴随观察界；常数和阈值先于网格与时间数据。 |

两项名称与交付清单及固定 C158/T142 登记完全一致；两个模块均被固定根 `Carleman.lean` 导入。原稿定位：291–312 行的权族及 N/R 范数，392–410 行的真实数值空间、质量伴随和权同质性，419–469 行的完整 N1–N5，1634–1679 行的原 Cartesian 定义与 Proposition 6.2，1681–1702 行的精确刚度证明，以及 Appendix B 的质量、载荷、B.2 和测试/观察结论。原稿 1706 行借连续 CE 推出离散 Carleman 估计，是本命题之后的另一依赖步骤。

## 原对象与所有 N1–N5 的逐项对应

下表中辅助声明名称均省略 `Carleman.`。这些固定依赖的具体类型和实际使用已从源码核对；既有独立验收范围及版本比较另列于后文。

| 原要求 | 实际固定对象／声明 | 判断 |
|---|---|---|
| 完整物理状态、载荷、控制 Hilbert 空间 | `PhysicalFiniteSpace`、`CartesianPhysicalState`、`CartesianPhysicalControl`、`cartesianPhysicalState_inner`、`cartesianPhysicalControl_inner` | PASS。全部内部节点函数构成状态空间，物理质量为 `∏ δ_j`；载荷 F=X；控制索引为真实位于 ω 的节点子类型。 |
| 原实际 R、J、Q、G | `cartesianReconstruction`、`cartesianReconstruction_RH`、`cartesianReconstruction_J_values`、`cartesianReconstruction_QH`、`cartesianReconstruction_G_values` | PASS。R 是原 Kuhn 帽函数和且属于原 H¹₀；J 是原归一化帽函数矩及真实 Hilbert 伴随；Q=RJ、G=JR，没有改成正交投影或强行 G=Id。 |
| 原加权范数及同质性 | `cartesianPhysicalStateWeight_norm_sq`、`cartesianPhysicalControlWeight_norm_sq`、`cartesianStateSeminorm_definite`、`cartesianControlSeminorm_definite`、两项 `*_weight_scale` | PASS。恰为原物理节点平方和；允许权处处正，故实际为范数；正标量乘权具有原线性同质性。 |
| N1：R 单射及无权比较 | `cartesianReconstruction_injective`、`cartesianReconstruction_norm_sq_bounds` | PASS。真实单射；准确界 `(d+2)⁻¹‖z‖²≤‖Rz‖²≤‖z‖²`，其中 d 为物理维数。 |
| N1：A 自伴、非负、原模板 | `cartesianPhysicalLaplacian_values`、`cartesianPhysicalLaplacian_adjoint`、`cartesianPhysicalLaplacian_nonneg` | PASS。同一实际 `(2d+1)` 点算子，使用原零边界数据、原步长平方分母及原物理内积。 |
| N1：精确刚度和缺陷 | `cartesianPhysicalLaplacian_stiffness`，NumericalData 的 `stiffness`、`defect` | PASS。任意独立 z、v 有 `(Az,v)=a(Rz,Rv)`；b=0 是时间无关对称形式，ηA=0 对全部权和全部时刻成立。 |
| N1：全部允许权重构双向比较 | `cartesian_full_weight_interface` 的前两项 | PASS。两方向均以同一个统一 Cmass 控制实际加权重构与原节点范数平方，未局限于 τ=0 或离散时刻。 |
| N2：实际载荷兼容性 | `cartesianLoadInterface`、`cartesianLoadInterface_Γ`、`cartesianLoadInterface_lift`、`cartesianPhysicalMoment_load_right_inverse` | PASS。Γ=Id，lift 是真实 L² 类；精确 `J(lift f)=f=Γf`。 |
| N2：全部权 lift 稳定性 | `cartesian_full_weight_interface` 的第三项 | PASS。控制同一个真实 lift 的加权 L² 范数；对 F=X 中所有 f 成立。 |
| N2：原右逆和稳定性 | `cartesianLoadInterface_right_inverse`，F=X、I=Id 及相同 load/state 范数 | PASS。`ΓI=Id` 为真实恒等式，`‖Iz‖_{F,σ}=‖z‖_{X,σ}`，稳定常数可取 1。 |
| N3：全部原域状态的 N 误差 | `cartesian_numericalData_of_box` → `cartesian_weightedApproximation_interface` → `cartesian_heat_error_from_b2` | PASS。每个实际 v∈D(A)、每个允许权及闭时间区间内每个 t，原 `Nσ(v−Qv)≤Capp h Rσ(v)`。 |
| N3：同一 Q 的 L² 误差 | 同一 WeightedApproximation 的 `l2` 字段 | PASS。`‖σ(v−R(Jv))‖≤Capp h² Rσ(v)`，其中 `R∘J=Q`，不是另一个近似算子。 |
| N4：指定测试算子 | 新完整权接口的 `T.op` 等式、`cartesianPhysicalTest_values` | PASS。实际每节点严格为 `σ(x_i)² z_i`，全状态定义，不存在频率截断或另选测试。 |
| N4：真实可微与周期端点 | `cartesianPhysicalTest_hasDerivWithinAt`、`cartesianPhysicalTestDerivative_values`、`cartesianPhysicalTest_endpoint`，新接口 `T.derivative` 等式 | PASS。算子范数意义的真实导数，包含闭区间端点；不是仅一个任意命名导数或仅二次配对导数。 |
| N4：对称、严格正定与双向配对界 | `cartesianPhysicalTest_symmetric`、`cartesianPhysicalTest_positive`，新完整权接口 | PASS。每个非零 z 的配对严格正；同一配对与 `‖σRz‖²` 双向统一比较。 |
| N4：时间导数界 | `allowed_weight_cartesian_test_time`、WeightedTest 的 `time_bound` | PASS。准确为 `Ctime q(t)²‖σRz‖²`，实指数范围、两符号和时间统一。 |
| N4：完整弱超逼近 | `allowed_weight_cartesian_test_superapproximation`、`cartesian_weightedTest_interface`、原允许权 H¹₀ 保持定理 | PASS。原符号 `R(Tz)−σ²Rz` 的真实 H¹ 残差，以真实 σ⁻¹ 的 N 范数控制，右侧恰为 `Csuper h qmax Nσ(Rz)`。 |
| N5：真实观察与伴随 | 新完整权接口、`allowed_weight_cartesian_hilbert_observation`、`cartesianPhysicalControl_adjoint` | PASS。原 ω₀ 上真实重构 L² 观察≤Cobs 乘实际 B* 的原加权控制范数；B 为零延拓，Hilbert 伴随严格等于节点限制。 |

## 完整性审查中的关键连接

**同一原离散对象。** PhysicalFiniteSpace 的 inner core 直接定义为 `mass Σ f_i g_i`，再由它构造 norm、InnerProductSpace、有限维及 CompleteSpace 实例；没有用函数 sup 范数或网格相关范数等价替换物理范数。δ_j>0 给 `mass=∏δ_j>0`。实际 R 是 `Σ f_i φ_i`，其局部值等于同一 Kuhn 单元上的节点仿射插值；真实弱 H¹₀ 资格进入 R 的 codRestrict。J 既定义为连续重构的 Hilbert 伴随，又逐节点证明等于 `mass⁻¹∫u φ_i`，所以采用此接口没有改变原 Q/G。

实际 A 的节点值为 `Σ_r(2f_i−f_{i+e_r}−f_{i−e_r})/δ_r²`，外部/边界节点按原零延拓。精确刚度依赖原全部边差配对与真实梯度积分身份。质量、步长和每个边界项在该桥中保留；没有把一般 Galerkin 算子新定义为 A 再声称它等于原模板。`A.adjoint=A` 与非负性都有独立实际证明；NumericalData 中未保存这些性质，不影响它们在固定同一 A 上已经成立。

**载荷及权范数。** lift 的真实 L² 资格、归一化帽函数矩右逆和相同物理空间的类型均已核对。载荷与状态为同一个完整 Hilbert 空间，Γ/I 都是恒等映射，所以第二个 N2 稳定界没有留下需要另证的常数。全部权稳定定理直接控制 `cartesianKuhnLoadLiftLp`，新完整接口中的 lift 与它为同一定义。实际节点正指数权保证 state/control seminorm 的零核仅为零；同质性由实际乘子和 norm_smul 证明，载荷的同质性随 F=X 严格继承。

**全原 D(A)，没有隐藏 H² 输入。** 新第一个定理在固定正边长盒上调用 `box_dirichlet_domain_le_h2`，其源头是原梯度形式所关联的实际算子图。已重读 BoxDirichletRegularity 和 BoxPoissonRegularity：对任意真实域元素，以实际算子值取原 H¹₀ 弱 Poisson 解，经过已经独立验收的有限奇延拓和内部正则性得到同值 H² jet。不是把模型域定义成 H²，也没有要求调用者另给正则性、光滑代表或椭圆估计。既有精确域等式还给 `D(A)=H²∩H¹₀`；本次 N3 只需其已证明正向包含及原 `a.domain_le`。

N3 内部的 u 是原 v 的 canonical H² jet，误差 jet 通过 `cartesianReconstruction_QH` 和弱值唯一性识别为同一 `v−Qv`。已验收原 B.2 给

`‖σe‖ + h‖σ∇e‖ ≤ C h² ‖σD²u‖`。

使用 `hq≤1`，有 `h Nσ(e)≤‖σe‖+h‖σ∇e‖`；原 R 范数包含 Hessian 项，遂得 aE=Ch、a0=Ch²。N 为真实各阶加权 L² 平方和的平方根，R 为真实加权各阶 L² 范数之和，m=1 时 q 幂次分别准确为 (q,1) 与 (q²,q,1)。没有将 Hessian 改成上确界，也没有限于光滑状态或重构空间。

**N4 的较强结论没有被较小接口省略。** NumericalData 只保存部分权/时刻上的比较，WeightedTest 也只保存二次配对可微和非负性。因此本次另外直接核对完整权接口给出的算子/导数等式，并使用实际 `cartesianPhysicalTest_hasDerivWithinAt` 与 `cartesianPhysicalTest_positive`，从而得到原要求的算子可微和严格正定。物理有限维连续性只用于把指定线性映射打包为 CLM；定量比较来自真实质量/权估计，不来自任意有限维范数等价。

真实导数的每节点系数为

`2 σ_i² (τ q′/q + η ρ_i q′)`。

原 `|q′|≤βq²`、q≥1、固定 `|τ|≤τStar` 及固定轮廓界给统一 Ctime。周期端点由原 q(0)=q(T) 严格得到。超逼近输入和输出为同一实际指定对角测试；内部残差值身份、真实 H¹ 弱梯度和原重构 jet 均通过弱导数唯一性对齐。逆权是 `q^(−τ)exp(−ηqρ)=σ⁻¹`，没有扩大允许指数范围来估计 σ²。

WeightedTest.superapprox 的类型仍有权保持参数 `hw`。本次没有把该参数忽略：对原稿 `ρ∈C∞(closure Ω)`，固定 `allowed_weight_mem_dirichlet` 从原 SmoothOnClosure、域有界性、同一允许权内部证明 `σ·V⊆V`，连续乘两次给 `σ²Rz∈V`。它不要求域外光滑代表、节点资格或新的边界假设，且不向估计引入网格/时间相关常数。故原 Proposition 6.2 中这个参数可实际供应，不是未清偿前提。两项新定理仅需的 C²/C¹ 假设是较弱的数值正则性；本报告的完整 PAPER 结论按原稿光滑闭包权实例化，而非声称单凭任意 C² 输入已经获得所有外部光滑乘子定理。

**观察。** B 的真实 Hilbert 伴随已证明为节点限制；新接口使用这个 adjoint，而不是另设一个 Bstar 函数。原 ω₀ 紧包含于开放 ω 的间距给固定 h₀，真实帽函数支撑局部性给原观察界。新证明用 qmax≥1 将 `h qmax≤min(ε,h₀)` 转为 `h≤h₀`，所以没有在原小尺度条件之外再要求独立网格上界。完整权接口的结论量化所有实数 t；原命题只需要 [0,T]，时间可微和超逼近在该闭区间上成立。

## 原量词、统一性与没有新增限制

固定正边长盒 `openCoordinateBox lo hi=S` 指定原域；原文 (0,L_r) 是 lo=0、hi=L 的实例。正维数写为 d+1，覆盖任意原 d≥1。原设置 N_r≥2、δ_r=L_r/N_r、h=max δ_r 供应新定理的 h>0、δ_r≤h 和 h/κ≤δ_r；κ≥1 是原步长可比界。源定理允许更多 N 值，没有额外排除任何原网格或非零状态。开放、凸、闭包紧条件由同一个盒提供；hdom 是实际域相等，不是额外正则性。

所有 ε、Ctime、Csuper、Capp、Cnum、Cmass、Cobs 在任意网格原点 o、δ、N、h、时间权 w、TimeGrid、τ、η、t 和状态之前选择。常数仅依赖允许的固定域、维数、轮廓、β、τStar、控制几何及步长可比界；不依赖 T、Δt、qmax、离散空间维数或状态。新的两项定理可以先分别取得常数，再取共同 `δnum=min(ε₁,ε₂)>0`。双向平方比较合法开方得到原范数比较；有限个正常数取统一上界，Capp 可相应放大而仍有 aE=Ch、a0=Ch²。此有限合并不改变量词次序或引入新限制。

原 qclass 的全部函数均覆盖：TimeWeight 使用 q 的有界正实轴延拓；原周期延拓满足它。TimeWeightRegularity.ofContDiffOn 从原闭区间 C²、首导数界和端点相等构造实际数据；未用到的 q″ 界及一二阶端点匹配是省略非必要原假设，不是收紧 qclass。TimeGrid 的周期任意正，数值定理没有时间步长小性条件。η 满足 |η|=1，即原两种指数符号；τ 是任意实数且完整保留 |τ|≤τStar。原负轮廓条件没有被额外加强；数值估计本身甚至不使用其负性。

没有遗漏原 N1–N5 条款。完整结论来自两项新定理与本报告明确列出的同版本真实恒等式/范数/可微性依赖，而不是把较小 NumericalData 的字段集合等同于完整原命题。

## 依赖版本、公理及本机构建

两新模块 Carleman import 闭包为 **628** 模块，其中 **626** 个旧模块与固定 base 逐字节相同。又独立递归比较关键已验收版本：

| 关键根模块 | 已接受版本 | 闭包模块数 | 本次比较 |
|---|---|---:|---|
| CartesianNumericalData | `20523c258707a3864f45541d0eea83581360c86b`（T110/C126） | 569 | 全部不变 |
| BoxDirichletRegularity | `b818f314b275265490aa9b797779f7db0005ddb9`（T141/C157） | 224 | 全部不变 |
| DirichletAllowedWeight | `604328efce1cc28e4d6fe6cadcdaa039ee0e76a3`（T067/C083） | 51 | 全部不变 |

本次实际重读新定理、NumericalData/WeightedTest/WeightedApproximation 定义及关键 CartesianNumericalData、CartesianWeightedTestInterface、CartesianApproximationInterface、CartesianReconstructionInterface、CartesianMassAdjoint、CartesianPhysicalStiffness、CartesianPhysicalNorms、CartesianPhysicalStability、CartesianPhysicalTest、CartesianPhysicalSpaces、PhysicalFiniteSpace、CartesianHilbertObservation、AllowedCartesianKuhnError/Stability、AllowedCartesianTestTime/Superapproximation、CartesianKuhnLoadLift、CartesianKuhnReconstruction、CartesianFiniteDifference、BoxDirichletRegularity/PoissonRegularity，以及原 N/R 范数与权定义。真实局部权比较、有限重叠、几何和弱梯度桥属于这些已验收且不变的依赖，没有新外留假设。

既有独立范围参考：[T097 原 B.2](T097-local-acceptance.md)、[T104 超逼近](T104-local-acceptance.md)、[T105 观察](T105-local-acceptance.md)、[T106 物理空间](T106-local-acceptance.md)、[T107 质量/载荷](T107-local-acceptance.md)、[T108 指定测试](T108-local-acceptance.md)、[T109 物理刚度/范数](T109-local-acceptance.md)、[T110 数值组装](T110-local-acceptance.md)、[T141 盒正则性](T141-local-acceptance.md)。本次补的是完整原命题联合审查及 hD 清偿，未因这些辅助报告分别 PASS 就自动提升 PAPER。

两项新源码无 `sorry`、`admit`、新增 `axiom` 或 `native_decide`。独立解析原始公理文本，两项声明均仅依赖 `propext`、`Classical.choice`、`Quot.sound`；2609 个非空打印记录和 9 个无公理记录无越界项。CheckAxioms 的 `privateToUserName` / `collectAxioms` 检查体与 base 一致，最终递归审计覆盖 **7291** 个 Carleman 声明，包括生成声明。

实际读取本机定向日志：CartesianBoxNumericalData **3842 jobs** 成功，CartesianFullWeightInterface **3756 jobs** 成功；完整日志 `/tmp/carleman-t142-fd-realization-full.log` 为 **3967 jobs** 成功及全量审计通过。没有声称本报告另行重跑构建。Lean 固定 **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、治理协议和原稿与 base 不变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

## 自行核验的同 SHA 远端证据

独立查询 [main run 39226924106 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39226924106/attempts/1)：push/main，`head_sha=13c8977bd4c50a11d6bed5fdab64b09aeee0203f`，最终 `completed/success`，更新时间 `2026-10-19T09:04:28Z`。实际三任务均已最终成功：

| job | ID | 状态 |
|---|---|---|
| state-check | 117975340298 | completed/success |
| lean | 117975340847 | completed/success |
| dashboard / snapshot | 117976623769 | completed/success |

本验收者通过 `gh run download` 自行下载该 run 的两份原始 artifact，未以执行者的下载或转述代替：

| artifact | ID | 归档大小 | archive digest |
|---|---|---:|---|
| lean-ci-result | 12175490101 | 492 bytes | `sha256:d0df1bc32eb74747f13e2a902b949473d9f5737f76667514333710759a6afba8` |
| lean-declaration-evidence | 12175245217 | 206630 bytes | `sha256:fe3e6fecbfc8f0feb3bd73be845347650df902470a43a1b06ad833d2fad0dc3f` |

实际读取 [result.json](/tmp/carleman-t142-fd-realization-main-ci/result.json)：`status=PASS`，`checked_sha=source_head_sha` 均等于固定 proof SHA，目标为 `Carleman`，`finished_at=2026-10-19T09:03:16.065390+00:00`。该时间是证明结果时间，最终三任务成功另由上述查询确认。

独立下载的 [原始完整类型/公理产物](/tmp/carleman-t142-fd-realization-main-axioms/axioms.txt) 与 [固定本机副本](/tmp/carleman-t142-fd-realization-local-axioms.txt) 逐字节完全相同：均 **2229237 bytes**，SHA256 均为 `4559d5dce8c6e4cc1e14fd69cc84b7ab17838067a06dcd9a57c43342f562f1e9`；末行为 `Axiom audit passed for all 7291 Carleman declarations.`。两项新增声明完整类型和正常公理记录均实际存在。

## 签发

**完整原 Proposition 6.2 / P012：PAPER PASS，无待修复缺项或新增未清偿假设。** 原所有 N1–N5、m=1、aE=Ch、a0=Ch²、ηA=0 与指定节点平方权测试均由同一实际方案满足；可登记 C158/P012 REVIEWED / PAPER，完成数 17/26。一般凸多面体解析实现、完整 P023、连续 CE 以及原文随后借 CE 推导的结论仍单独处理。

依本轮明确授权，本报告单独提交，不推送；不包含实现、台账、根导入、原稿或未来工作树文件。通知主 Agent 后冻结报告内容及签发时间。
