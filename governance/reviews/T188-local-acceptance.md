# T188 / C204 独立本机验收：原受控状态的 L²_t H¹₀ 弱紧性

- checked_sha / source_sha: `32711e6669f223eba5851b43e9ec886a40c45b6e`
- mathematical_base: `69cee61bd440c386c2ac20af6104f72e98b3563c`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- reviewed_at: `2026-10-20T00:53:09+00:00`（UTC；签发后正文与时间冻结）
- 最终状态：**PASS，23/23 显式声明通过独立数学验收；同 SHA 三项正式 CI 成功，独立下载的原始证据逐字节一致。**
- scope: **AUXILIARY，17/26**；仅原差分受控状态的完整空间能量弱子列及 E_h 极限识别，不提升整个 P021 / Corollary 7.9。

## 固定版本与原文

直接读取固定 Git 对象四模块全部实现、固定 raw 中23项完整展开类型、T188 分析、MATH_SPEC 和 C204/C203/C145 台账。AGENTS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读 T186 版本相同；PROJECT_OPERATIONS 与已读治理提交 `dab075a80599541c0ecafdbdce7a3b2fa2f0d609` 相同，包含 API 迟滞时完整精确作业日志交叉核验规则。动态工作树、后续数学增量及动态 .ci 输出不作为本批证据。

实际对照原 `paper/main.tex:2330–2390`，尤其2368–2381：以 dt·yⁿ 测试原隐式方程，利用前向能量与精确刚度，得到 Y_h,dt 在 L²(0,T;V) 的一致界，抽取弱子列，再由 E_h−R_h 一致性得到修改状态的同一 L²_tH 弱极限。原文 V=H¹₀，后续仍需识别极限方程、V′时间导数与初终值。本批准确完成这里的状态弱紧性步骤。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有改变原文。

已完整读取 [T187 冻结报告](T187-local-acceptance.md)，报告提交 `74280d45d211f473b5f4273caedc64ec1678606b`，checked 正是本批 mathematical_base，reviewed_at=`2026-10-19T16:13:11+00:00`，20/20 PASS。报告不能替代源码：实际前向能量、刚度预算、平均势与控制零延拓、原 Kuhn H¹₀ jet、固定盒与真实时间重构及 E_h/R_h 一致性在本次重新读取。

## 全部23项声明

顺序与固定 manifest 一致。源码相对 `Carleman/Control/`；raw 行为完整类型起始行。6项定义、3项实例分别核对其真实构造，其余14项为已证明定理。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.timeCellReconstruction_map` | `DirichletTimeWeakCompactness.lean:17` | 35607 | 真实 Bochner 时间重构与任意 CLM 交换；PASS。 |
| 2 | `Carleman.fixedTimeCellReconstruction_map` | `DirichletTimeWeakCompactness.lean:31` | 35614 | 固定同一时间域的精确交换身份；PASS。 |
| 3 | `Carleman.DirichletEnergyState` | `DirichletTimeWeakCompactness.lean:42` | 35621 | 原 DirichletEnergy 的同一载体；PASS。 |
| 4 | `Carleman.dirichletEnergyStateNormedAddCommGroup` | `DirichletTimeWeakCompactness.lean:44` | 35623 | 完整继承原能量范数；PASS。 |
| 5 | `Carleman.dirichletEnergyStateInnerProductSpace` | `DirichletTimeWeakCompactness.lean:47` | 35626 | 完整继承原实内积；PASS。 |
| 6 | `Carleman.dirichletEnergyStateEquiv` | `DirichletTimeWeakCompactness.lean:50` | 35629 | 身份映射的线性等距满射；PASS。 |
| 7 | `Carleman.dirichletStateValue` | `DirichletTimeWeakCompactness.lean:53` | 35632 | 原真实零阶嵌入 CLM；PASS。 |
| 8 | `Carleman.dirichletStateGradient` | `DirichletTimeWeakCompactness.lean:57` | 35636 | 原全部一阶弱梯度 CLM；PASS。 |
| 9 | `Carleman.dirichletEnergyState_norm_sq` | `DirichletTimeWeakCompactness.lean:61` | 35641 | 能量范数平方恰为值与完整梯度平方之和；PASS。 |
| 10 | `Carleman.dirichletEnergyState_complete` | `DirichletTimeWeakCompactness.lean:65` | 35645 | 开域原 H¹₀ 图闭包给真实完备性；PASS。 |
| 11 | `Carleman.dirichletEnergyStateSecondCountable` | `DirichletTimeWeakCompactness.lean:68` | 35648 | 实际有限阶 L² 字段空间及子空间的第二可数性；PASS。 |
| 12 | `Carleman.dirichlet_time_norm_sq` | `DirichletTimeWeakCompactness.lean:73` | 35651 | 实际时间 H¹₀ 范数的精确两项分解；PASS。 |
| 13 | `Carleman.exists_dirichlet_time_weak_subsequence` | `DirichletTimeWeakCompactness.lean:97` | 35658 | 原 Hilbert 弱紧性给同一严格子列及值、梯度弱极限；PASS。 |
| 14 | `Carleman.cartesianBoxDirichletState` | `CartesianDirichletReconstruction.lean:16` | 35711 | 同一完整 Kuhn 重构确属原固定盒 H¹₀；PASS。 |
| 15 | `Carleman.cartesianBoxDirichletState_value` | `CartesianDirichletReconstruction.lean:27` | 35718 | 与原固定盒 jet 的值严格相等；PASS。 |
| 16 | `Carleman.cartesianBoxDirichletState_gradient` | `CartesianDirichletReconstruction.lean:33` | 35724 | 与原固定盒 jet 的完整梯度严格相等；PASS。 |
| 17 | `Carleman.cartesianBoxDirichletState_value_norm_le` | `CartesianDirichletReconstruction.lean:39` | 35730 | 实际重构 L² 范数≤原物理节点范数，常数1；PASS。 |
| 18 | `Carleman.timeCellReconstruction_norm_sq_le` | `CartesianDirichletReconstruction.lean:52` | 35736 | 实际 dt 加权平方和≤period·B²；PASS。 |
| 19 | `Carleman.fixedTimeCellReconstruction_norm_sq_le` | `CartesianDirichletReconstruction.lean:64` | 35740 | 同一原固定 T 下的真实平方界；PASS。 |
| 20 | `Carleman.cartesian_state_node_uniform` | `CartesianStateTimeEnergy.lean:15` | 35744 | 原物理方程内部供给全部 N+1 状态节点界；PASS。 |
| 21 | `Carleman.stateTimeEnergyBound` | `CartesianStateTimeEnergy.lean:55` | 35767 | 仅依 T、M、Y、U 的完整能量预算定义；PASS。 |
| 22 | `Carleman.cartesian_state_dirichlet_time_uniform` | `CartesianStateTimeEnergy.lean:59` | 35769 | 原方程供给真实 L²_tH¹₀ 统一界；PASS。 |
| 23 | `Carleman.cartesian_controlled_states_weak_subsequence` | `CartesianStateWeakCompactness.lean:15` | 35795 | 不输入 R_h 弱极限，构造同一子列的四组全测试极限；PASS。 |

## 原 H¹₀ 载体、范数、完备性与可分性

DirichletEnergyState 的定义体就是原 DirichletEnergy S；两个代数/范数实例直接继承其结构，dirichletEnergyStateEquiv 是 LinearIsometryEquiv.refl。它不是另一份带自定义弱梯度或缩小成员的空间。实际 DirichletEnergy 是 SobolevHilbert 中零阶值属于 dirichletSubspace 的子空间；后者来自真实 SpatialTest 的 Sobolev jets 之线性张成在原弱 H¹ 图拓扑中的闭包，再经 value 映射。开域上真实弱导数唯一性保证相同 value 的 jet 相同，因此这个描述没有增加不正确的梯度成员。

SobolevHilbert 使用各阶 L² 字段的 PiLp 2 范数；原 DirichletForm 的 norm_sq 通过两个阶数的真实平方和和零阶标量范数身份得到 **‖u‖²=‖value u‖²+‖gradient u‖²**。gradient 是 EuclideanSpace ℝ (Sym (Fin d) 1) 的全部一阶坐标，未丢掉方向、重复计数或换成网格差分范数。这里继承的是完整 H¹ 能量范数，没有混淆 H¹ 闭合与 L² 闭合。

第10项只要求 S 开：原 dirichletSubspace_closed 给 Sobolev 图中的闭子空间，conformingHilbert_completeSpace 内部从真实 Hilbert 完备性得结论，不要求调用者另给闭合或 Poincaré。第11项通过 HilbertJetFields 的第二可数性和子空间继承给结论。已读取固定 mathlib 的 Measure.SeparableMeasure：可数生成 Borel 空间上的 s-finite 测度可分；有限 p 的 Lp 在值域可分时第二可数，证明使用实际有限指示函数和 Lp 稠密性。空间限制 Lebesgue 测度与时间限制 Lebesgue 测度均满足该条件，p=2≠∞，坐标纤维有限维。没有新增可分性、有限维 H¹₀ 或紧嵌入假设。

第13项因此可对真正无限维 **Lp (DirichletEnergyState S) 2 (volume|(0,T])** 调用 C145。其真实证明先用 Hilbert Riesz 线性等距将有界序列放入弱对偶闭球，再用可分情形的顺序 Banach–Alaoglu 提取 StrictMono φ，以 Riesz 逆映射得到仍属于原 H¹₀ 值 L² 空间的 v，且保留同一个范数预算 C。已读 mathlib 的实际顺序紧性路径：弱对偶紧集的可度量性来自可数稠密测试，随后获得序列紧性；这不是仅由一般紧性错误地断言存在子列。

原 helper 的结论测试覆盖全部 Hilbert 元素。值和梯度极限由各自 compLpL 的真实 Hilbert 伴随把目标测试拉回源空间，保留同一个 φ 与 v；未分别抽取两条不一致子列，也未以稠密测试子集的结论冒称全测试收敛。预算 C 不另假设非负是合法的，已有 ∀n,‖u_n‖≤C 已强制 C≥0。

## 真实 Bochner 重构与固定域身份

timeCellReconstruction 是原物理时间单元 **(t_i,t_(i+1)]** 上 indicatorConstLp 的有限和，单元真实体积为 dt，两两不交。第1项同时使用 CLM.compLpL 的实际 a.e. 复合代表和时间重构的有限指示和代表，利用 CLM 保零与保和证明严格 Lp 身份。已读 mathlib compLpL：其连续性来自真实 ‖L∘u‖Lp≤‖L‖‖u‖Lp，且输出确实 a.e. 为 L(u(t))。没有把值域改变只当作数字范数比较。

第2项仅沿 g.period=T 运输到字面相同的限制时间测度。第12项把原空间平方恒等式在时间单元求和，用真实 **‖reconstruct u‖²=dt Σ‖u_i‖²** 得精确两项分解。第18–19项则由每个节点的 B 界得到 **dt·steps·B²=T B²**；没有丢失 dt 或多出步数因子。

第14项取原 cartesianBoxKuhnReconstructionJet，并以其实际 Dirichlet 成员证明包装为同一能量状态。hbox:lo_j+N_jδ_j=hi_j 只是固定物理盒的精确等式运输；value 与 gradient 的第15–16项均为真实定义相等。旧 jet 是由已证明的原 Kuhn Lp 重构在原 H¹₀ 闭包中的成员资格取得，value 严格等于原 R_h，全弱梯度由分布唯一性确定。没有输入额外边界迹、光滑性、H² 或待证零边界资格。

第17项调用原重构的真实积分质量界上侧 **‖R_h f‖²≤‖f‖²_Xh**。物理有限空间范数中的质量 ∏δ 与原 L² 重构完全对应，取非负平方根保留常数1。只使用该上侧，不引入下侧 d+2 的范数等价常数，更没有使用随网格的有限维自动连续性。

## 原物理方程内部供给完整能量预算

第20项覆盖全部 k:Fin(steps+1)，包括初态与终态。输入是原 **dt⁻¹(y_(i+1)−y_i)+(A_h+V_i)y_(i+1)=B_hu_i**，真实 ForwardEquation 与 step 方程在 dt>0 下等价。原 A_h 是实际 Cartesian 物理有限差分 Laplacian，V_i 是原 b 在时间—对偶单元上的实际平均乘法；不是自由选取的正算子或有界节点势。

实际平均系数为 **(dt·∏δ)⁻¹∫timecell∫D_a b**，由真实有限柱体积分保留同一 b.bound≤M。实际 PhysicalFiniteSpace 乘子范数≤M，原 A_h 的非负性给 A_h+V_i 下界−M‖v‖²。原 Cartesian 控制按活动节点零延拓，真实物理质量内积中保范数，故 ‖B_h‖≤1；允许任意活动集及空活动集，不需要控制支持的额外假设。

代码调用实际 Physical.forward_energy，保留 **dt M≤1/2**，得到所有节点 **‖y^k‖≤E:=energyConstant(T,M)(Y+U)**。既有 energyConstant 的定义为 **exp(2MT)(1+sqrt T)**，来自实际步递推和 dt 加权控制 L¹→L²，独立于 ‖A_h‖、空间节点数和时间步数。第20项不单列 Y、U 非负亦无漏洞：原初态/控制范数上界已强制它们非负；完整平方预算第22项明确保留 hY、hU。

原真实刚度身份 **⟨A_h f,f⟩Xh=‖field₁(R_h f)‖²L²** 与完整物理能量望远镜和在 T187 给梯度预算。已重新读取其证明：时间末态平方与每步跳跃平方仅在非负性成立后丢弃，势项符号和 Young 不等式给系数1+2M；真实控制平方和为 dt Σ‖u_i‖²，没有把初态算作控制时间步。

第22项使用第17项与全部节点界，先得时间值范数平方≤**T E²**；再使用 T187 的实际梯度范数平方≤**Y²+U²+(1+2M)T E²**。第12项精确相加并取合法平方根，所得第21项定义为

**stateTimeEnergyBound(T,M,Y,U)=sqrt(T E²+Y²+U²+(1+2M)T E²)**。

T≥0 从实际 TimeGrid 的 period=T 内部推出，根号内非负；实际合法网格更强制 T>0。预算在所有网格、原点、边长、势、活动集及状态/控制之前由 T、M、Y、U 固定，不含 h、dt、N、空间维数或刚度范数。出现的 T 恰为时间积分长度；没有要求对变化 T 保持同一个常数。整个构造不要求 Poincaré、H²、长宽比、网格嵌套或 h/dt 关系。

## 最终同一子列、全部测试与范围

第23项先对每层原方程内部证明上述统一预算，再对原 H¹₀ 值时间重构 r_n 应用第13项得到 v、StrictMono φ 和预算。通过真实 compLpL 交换及第15–16项，把已得弱极限重写为**同一原 R_h 的值与梯度**，不是另外选择同范数字段。

最终四组结论分别为：原 H¹₀ 值重构对全部 L²_tH¹₀ 测试收敛到 v；原 R_h 值对全部 L²_tL²_x 测试收敛到 value(v)；原完整梯度对全部 L²_tL²_x(ℝ^d) 测试收敛到 gradient(v)；原 E_h 值对全部 L²_tL²_x 测试收敛到同一个 value(v)。这里全部都沿**同一个严格递增 φ**，v 的成员类型自身保证真实弱梯度与零边界图成员资格。输出不是只逐个空间坐标或固定有限测试的收敛。

最后一组实际调用 T187 的 cartesian_controlled_states_same_weak_limit，并将全部原数据与方程按 φ 重索引。StrictMono φ 给 φ→∞，因此 h_(φ n)→0；T187 用真实 E_h−R_h 误差和内部梯度预算传递该弱极限。**最终输入没有 R_h 弱收敛、任意梯度预算或目标 E_h 极限。** 用于 T187 的 R_h 弱收敛是本批刚证明的结论。

原固定盒 lo、hi 和固定 T 保留；每层势 b_n 允许变化但同受 M 控制，包含原固定 b 的合法平均实例。这一较一般的预算/紧性结论不声称变化势的极限仍为指定原 b。显式初值预算、真实控制成本预算、原全部方程及 dt_n M≤1/2 均保留。这里只要求 **h_n→0** 来识别 E_h，不需要 dt_n→0；原 Corollary 中 dt_n→0 足以在后续提供时间一致性，并没有被本批用一个耦合条件替代。

允许 d=0、空盒、空内部节点/活动控制及粗层 N_j≤1：没有选取不存在的方向或除以 d，Lp 零空间、空和与原重构均合法。通用弱紧性 helper 甚至允许任意 T 的空时间区间；最终真实 TimeGrid 则内部保证正周期。所有状态时间重构均取 y i.succ，准确对应后向 Euler，初态只进入预算。

本批可应用于既有控制子列再取子列，原控制弱收敛会被严格子列保留；但本声明没有把控制选择、极限 PDE、V′时间导数、连续端点、零终态或完整 P021 作为已证明输出。一般 P1 实例也没有在本批接入。维持 AUXILIARY 是准确的范围。

## 固定闭包、公理与实际构建

四入口实际 Carleman 导入闭包共 **361** 模块，除四新增模块外 **357** 个与 mathematical_base 逐字节相同。关键已接受版本的完整闭包另行比较，全部无变化：

| 入口 | 固定依赖版本 | 闭包模块数 |
| --- | --- | --- |
| CartesianEquationWeakConsistency / T187 | `69cee61bd440c386c2ac20af6104f72e98b3563c` | 355 |
| HilbertWeakSubsequence / C145 | `bee8a93d0856f84c9280d10a19f50da7da2a362f` | 1 |
| TimeCellReconstruction / T177 | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 23 |
| CartesianPhysicalStability / 已验 T110 闭包 | `20523c258707a3864f45541d0eea83581360c86b` | 323 |
| DirichletForm / 已验 T041 闭包 | `3d5aa9cec281974bef7da9d37ffa11a8f9f75670` | 49 |

固定根模块导入四入口，23项在固定 CheckAxioms 中均实际 #check @ 与 #print axioms。新源码无 sorry、admit、新 axiom、native_decide。23项仅依赖正常 **propext、Classical.choice、Quot.sound**；独立解析 raw 全部 **3314** 条显式公理记录（**3310** 个不同名字、**9** 条无公理），白名单外依赖为零。实际递归 auditor 末行确认 **8496 项 Carleman 声明 PASS**。

实际读取 `/tmp/carleman-t188-weak-build11.log`，最终相关目标 **3562 jobs** 成功；`/tmp/carleman-t188-state-weak-compactness-build.log`，根构建 **4162 jobs** 成功。`-axioms.log` 为零字节 stderr，成功取自 raw 的真实末行，不从空输出推断。

固定 `/tmp/carleman-t188-state-weak-compactness-local-axioms.txt` 实测 **2741909 bytes**，SHA256 **`159923657328ca21cb77a705b82348ca66305ba1181a176556b3c97a09aafbb4`**。Lean pin v4.35.0；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、workflow、lean_ci.sh 与已验 T186 未变。此次新增使用的 mathlib Lp 可分性/第二可数性、compLpL 实际复合及顺序 Banach–Alaoglu 类型与证明路径已直接读取。

## 正式 CI 与签发

本 Agent 独立查询 [main CI run 39349472901 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39349472901/attempts/1)，实际 `event=push`、`head_branch=main`、`head_sha=32711e6669f223eba5851b43e9ec886a40c45b6e`。最终 API 已明确返回 **completed / success**，updated_at=`2026-10-20T00:49:02Z`；本次不需要采用 API 迟滞的完整日志替代路径。

| 作业 | 实际 job ID | 最终状态 | completed_at（UTC） |
| --- | --- | --- | --- |
| lean | `118389993141` | completed / success | `2026-10-20T00:48:53Z` |
| state-check | `118389993326` | completed / success | `2026-10-20T00:45:06Z` |
| dashboard / snapshot | `118391238885` | completed / success | `2026-10-20T00:49:01Z` |

三条 job 的 head_sha 均逐一匹配固定证明。独立查询结果保存为 `/tmp/carleman-t188-state-weak-compactness-review-run.json`、`-review-jobs.json` 和 `-review-artifacts.json`。同 run 的两个实际工件如下；表中 digest 为 GitHub 提供的 ZIP 摘要，区别于解压后原始文件摘要。

| 工件 | artifact ID | ZIP bytes | GitHub ZIP SHA256 |
| --- | --- | --- | --- |
| lean-ci-result | `12232198077` | 492 | `b0e23e8d06476528db426d49113fd735fcfd3f2fa4d55d48e5ce7de318432016` |
| lean-declaration-evidence | `12233035132` | 252970 | `6213b5078ab3c86e60145c0bd7433ddf19bb29076836e8c67168b6811cb8d13c` |

两个工件的 workflow_run 均绑定 run `39349472901`、main 与精确 proof SHA。本 Agent 自行执行两次 `gh run download`，均退出0，分别下载至 `-main-ci` 与 `-main-axioms`，没有使用 root 的下载副本。

实际读取 `/tmp/carleman-t188-state-weak-compactness-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=32711e6669f223eba5851b43e9ec886a40c45b6e`，`targets=[Carleman]`，ci_url 指向该 run/attempt，finished_at=`2026-10-20T00:47:43.690892+00:00`；Lean 4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib pin 均匹配。该原始 JSON **537 bytes**，SHA256=`f35265b65ecae11d26a7b1d63f0193ed50fb358b21e03df60cf5dcb4927d6962`。

实际读取 `/tmp/carleman-t188-state-weak-compactness-main-axioms/axioms.txt`，与本批固定 `-local-axioms.txt` **逐字节完全相同**：均 **2741909 bytes**，SHA256=`159923657328ca21cb77a705b82348ca66305ba1181a176556b3c97a09aafbb4`。远端原始末行同样确认 **8496 项 Carleman 声明递归公理检查 PASS**，23项完整类型及其正常基础公理证据随字节一致性一起核实。

## 最终结论

**T188 / C204 在固定 proof SHA 上 PASS，无阻断或非阻断数学缺陷。** 实际原 H¹₀ 能量载体、全部物理状态的内部预算、真实 Bochner 时间重构及同一严格子列的全空间测试极限均忠实于原文对应步骤，最终没有预设 R_h 弱极限。仅验收本辅助阶段；保持 **AUXILIARY、17/26**，不据此提升 P021、极限 PDE 或完整控制收敛。此报告为本 Agent 唯一仓库写入，单文件提交，不修改数学、原稿、台账或 root/audit，不推送。
