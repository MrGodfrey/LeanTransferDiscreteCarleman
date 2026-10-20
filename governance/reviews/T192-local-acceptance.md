# T192 / C208 独立本机验收：原 P1 节点测试的 H¹₀ 强一致性

- checked_sha: `560e3aa8d23c22943b51dd7744da8174944b27ef`
- mathematical_base: `ec7ddbfba0b338f3ba97039442ed5c2108ac99aa`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- reviewed_at: `2026-10-20T01:48:19+00:00`（UTC；签发后时间与正文冻结）
- 最终状态：**PASS，16/16 显式声明通过独立数学验收；同 SHA 三项 CI 最终成功，独立下载原始公理工件与固定本机证据逐字节一致。**
- scope: **AUXILIARY，17/26**；不提升整个 P021。

## 固定版本与原文

直接读取固定 Git 对象三个新模块的全部证明、固定 raw 中16项完整展开类型、T192 分析/MATH_SPEC 及唯一台账的 T192/C208 和关键旧依赖记录。三个模块均位于 `Carleman/Control/`。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES 与 PAPER_COVERAGE 和已读 T190 版本逐字节相同，沿用真实固定版本语义验收与同 SHA 证据要求；动态工作树、后续草稿与动态 `.ci` 不属于本批。

实际对照原 `paper/main.tex:2926–2956`：固定有限和 φ(t,x)=Σηₗ(t)ψₗ(x)，原 P1 节点插值 I_h，前一时间层取样，整个和的后向时间差商，以及 τ=0、T 两端空间一致性。另参照原控制极限步骤使用这些测试的范围。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，未修改原文。

已完整读取 [T191 冻结报告](T191-local-acceptance.md)，报告提交 `9ce5a486fc1b5d6645eb6555cbb28146f4a00c8e`，checked SHA 为本批 mathematical_base，reviewed_at=`2026-10-20T01:32:24+00:00`，18/18 公开声明及 private 辅助通过。实际重读该批 TensorTimeTests 的全部证明、时间差商 FTC/真实平均投影及闭区间 C¹ 接口；没有以报告替代被调用代码。T191 中明确保留的空间强收敛输入，在 T192 的最终接口中由真正节点插值误差内部清偿。

## 全部16项声明

顺序与 `/tmp/carleman-t192-p1-tests-declarations.json` 一致；源码相对 `Carleman/Control/`，raw 行是完整类型起始行。共 **2 个 def、14 个 theorem**。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.SimplicialPartition.nodal_lipschitz_derivative_error` | `P1TestInterpolation.lean:19` | 36366 | 实际仿射节点导数的 (1+4κ)L·maxDiameter 点态界；PASS。 |
| 2 | `Carleman.SimplicialPartition.test_nodal_derivative_L2_error` | `P1TestInterpolation.lean:32` | 36382 | 真实算子值 L² 导数误差及准确有限体积因子；PASS。 |
| 3 | `Carleman.SimplicialPartition.test_nodal_zero_boundary` | `P1TestInterpolation.lean:51` | 36398 | 原紧支撑测试在全部边界节点真实为零；PASS。 |
| 4 | `Carleman.SimplicialPartition.testDirichletState` | `P1TestInterpolation.lean:58` | 36404 | 实际节点弱 jet 进入原 H¹₀ 能量载体；PASS。 |
| 5 | `Carleman.SimplicialPartition.testDirichletState_value` | `P1TestInterpolation.lean:65` | 36413 | 零阶值严格为原 nodalLp；PASS。 |
| 6 | `Carleman.SimplicialPartition.testDirichletState_gradient` | `P1TestInterpolation.lean:70` | 36419 | 完整弱梯度严格为实际节点导数字段的坐标映射；PASS。 |
| 7 | `Carleman.SpatialTest.dirichletState` | `P1TestInterpolation.lean:79` | 36426 | 同一原测试的真实 H¹₀ 状态；PASS。 |
| 8 | `Carleman.SpatialTest.dirichletState_value` | `P1TestInterpolation.lean:86` | 36429 | 值恰为原测试的真实 L² 类；PASS。 |
| 9 | `Carleman.SpatialTest.dirichletState_gradient` | `P1TestInterpolation.lean:90` | 36433 | 原 fderiv 的全部方向弱梯度身份；PASS。 |
| 10 | `Carleman.test_nodal_value_strong_convergence` | `P1TestStrongConvergence.lean:13` | 36438 | 从真实值误差内部推出全节点插值强收敛；PASS。 |
| 11 | `Carleman.test_nodal_derivative_strong_convergence` | `P1TestStrongConvergence.lean:25` | 36446 | 固定形状常数下的真实导数 L² 强收敛；PASS。 |
| 12 | `Carleman.dirichletEnergyState_tendsto_of_fields` | `P1TestStrongConvergence.lean:42` | 36460 | 由原完整范数平方身份合并值与梯度强极限；PASS。 |
| 13 | `Carleman.full_p1_test_H1_strong_convergence` | `P1TestStrongConvergence.lean:62` | 36468 | 无目标收敛前提的原节点 H¹₀ 强一致性；PASS。 |
| 14 | `Carleman.SimplicialPartition.testDirichletState_finite_value` | `P1TensorTestConsistency.lean:17` | 36481 | 整个有限和的同一原 I_h 身份；PASS。 |
| 15 | `Carleman.full_p1_finite_time_test_consistency` | `P1TensorTestConsistency.lean:36` | 36490 | 前层取样与整和差商在真实 H¹₀ 值 Bochner 空间强收敛；PASS。 |
| 16 | `Carleman.full_p1_finite_test_endpoint_consistency` | `P1TensorTestConsistency.lean:59` | 36527 | 任意固定 τ 的同一插值强极限，包含原两端；PASS。 |

## 真正原节点插值与 H¹₀ 成员

SimplicialPartition 记录实际非退化 d 单纯形、胞元包含 closure S、覆盖 S 及内部不交。已重读 FaceMatching 的共同顶点凸包条件、BoundaryFitted 的边界顶点凸包条件和 nodalFunction 的构造。局部仿射函数恰由原 f 的顶点值唯一确定；FaceMatching 给共同面一致性，闭覆盖拼接成真实连续分片仿射函数。nodalLp 是该点态函数的实际 L² 类。这里求值的是原光滑测试的函数 φ.value，而非任意 L² 商类的节点值。

第3项利用 tsupport φ⊆S 和 S 开：边界点不在 interior S=S，故不在 tsupport，原函数值为零。这是逐个真实边界节点结论，不是用边界零测推点值。BoundaryFitted 再把节点零值传到完整边界，各相邻胞元一致；原零延拓函数连续且 Lipschitz。

第4项使用 `nodalSobolevJet` 的实际弱导数证明，并调用 `nodalLp_mem_dirichletSubspace`。该依赖的 H¹₀ 资格并非“零边界”命名：已直接读取其内缩、紧支光滑卷积及原 H¹ 图闭包路径。对非空开凸 S，原节点函数的真实内缩支撑严格落在 S，光滑卷积给 SpatialTest 逼近，内缩再强 H¹ 返回原函数；对空域另用零 Lp 类处理。没有新增待证迹、H² 或 H¹₀ 成员前提。

原 `nodalLp_mem_dirichletConformingSpace` 同时给值属于**全部分片仿射且在 H¹₀ 的 conformingSpace**；该空间由真实 a.e. 胞元仿射身份与原 Dirichlet 子空间定义，未换成只含少数测试的子空间。第4项的最终载体是原 DirichletEnergyState，值由第5项精确识别为同一 I_hφ；这个包装没有改变原空间函数或能量范数。

第7项用原 SpatialTest.sobolevJet 和 test_mem_dirichletSubspace 构造原测试的 H¹₀ 状态。展开类型确认该 def 本身没有继承不必要的有限体积假设。第8–9项表明其值和完整弱梯度就是原测试的真实 L² 类及 fderiv 字段，而非任意相同范数的代表。

## Taylor 导数误差、真实弱梯度及统一常数

第1项调用已接受并本次重读的 `simplexNodal_gradient_error_of_lipschitz_derivative`。实际一阶 Taylor 仿射多项式 p 满足值余项≤L D²、导数余项≤L D；节点插值精确再现 p。对仿射 I_hf−p，内球半径 r 上的幅度界给实际 CLM 导数范数≤4L D²/r，原形状条件 D≤κr 将其控制为4κL D，因此总误差为 **(1+4κ)L D**。该4来自内球中心与半径 r/2 方向点的真实差值，未假设逆估计或导数误差作为输入。

M.cellDiameter 是实际 Metric.diam，胞元紧性供应任意两点距离≤该直径；maxDiameter 是有限集上的 NNReal supremum，含空网格约定。以非负系数放大 D 到 maxDiameter 合法。κ 在所有 n、单元、内球参数之前固定；a、r 可以逐网格/胞元变化，但唯一进入误差的形状量为同一个 κ。没有节点数、最小单元尺寸或网格局部导数范数混入常数。

实际 nodalDerivativeFunction 是在胞元内部取 localNodalDerivative 的有限指标和，骨架上取零。已读取其 HasFDerivAt、MemLp 与 a.e. 代表证明：内部局部一致给真实经典导数；每个单纯形边界零测，有限合并后真实域内 a.e. 落在某个胞元内部。第2项据此与原 φ.fderivLp、Lp 减法代表合并，应用真实 a.e. 范数界，保留 **|S|^(1/2)(1+4κ)L·maxDiameter**。类型中的体积因子写为 `(measureUnivNNReal (volume.restrict S):ℝ)^((2:ENNReal).toReal⁻¹)`，正是该平方根，不是体积本身。

它首先是算子值 L² 的导数误差；第6项所用 firstOrderJet 再把同一导数 CLM 作用于每个标准坐标方向，经 Sym.oneEquiv 组装全部一阶 DerivativeFiber。已重读 nodalLp_weakDerivative：从全空间 Lipschitz 零延拓和 a.e. 实际导数，经真实分部积分证明所有方向、所有 SpatialTest 的弱身份。并非只把经典导数字段命名成弱梯度，也没有漏掉骨架分布跳跃；连续拼接与实际弱导数引理清偿该问题。

`derivativeOneFiber` 是固定维数下的真实 CLM；最终仅使用其在 L² 上的连续线性映射保强收敛，未把算子范数误当完整 Euclidean 纤维范数的等距。可能的维数常数只依固定 d，与网格/测试序列无关。成员资格证明中出现的网格与节点值相关 Lipschitz 常数仅用于弱导数和 H¹₀ 资格，未用于本批统一误差上界。

第10项从原值误差 **2C·maxDiameter·|S|^(1/2)** 夹逼；第11项从上面的真实导数误差夹逼。C 和 L 都由固定 φ 的全局光滑紧支撑内部供应：对 φ.value 和 fderiv φ.value 分别调用 mathlib `ContDiff.lipschitzWith_of_hasCompactSupport`。已读取其真实证明：紧支撑导数的连续性给全局界，随后均值定理给 Lipschitz；φ.compact.fderiv 及 φ.smooth.fderiv_right 满足第二次调用。没有给原初值、控制或势增加光滑性；正则性仅属于原文已有的测试。

## 完整 H¹ 范数与真实有限张量测试

DirichletEnergyState 仍是原 DirichletEnergy；第12项对差 u_n−u₀ 使用准确恒等式 **‖u_n−u₀‖²=‖value差‖²+‖gradient差‖²**，由两个非负范数推出总范数≤二者之和并夹逼。没有混淆仅 L² 强收敛与 H¹ 强收敛，也没有依赖 Poincaré 来补漏零阶项。第13项把已内部证明的两个强极限通过第5–9项身份接入，得到真正原 H¹₀ 图范数强收敛；输入无目标空间收敛或任意弱梯度假设。

第14项通过 value CLM 保有限和/数乘和原 nodalLpLinearMap 的实际线性，证明和状态的值恰为 **I_h(Σcₗψₗ)**。该线性映射定义在点态函数域，已有真实节点身份，因此没有在 Lp 商类上非法插值。所得和属于原 H¹₀，弱梯度由其真实 jet 的线性运算确定；在开域上同值的弱梯度唯一，和状态代表的正是原整个插值。

第15项直接实例化 T191 的有限张量定理，但空间因子 `vₗ,n=(M n).testDirichletState(ψₗ)` 的强收敛全部由第13项供应，最终不再要求调用者输入。极限 `timeTensor T ψₗ.dirichletState (...)` 是真实标量乘法的 Bochner 连续双线性映射，代表为 ηₗ(t)ψₗ 或 fₗ(t)ψₗ；值/梯度均是同一原测试。收敛发生在 **Lp (DirichletEnergyState S) 2 (volume|(0,T])** 中，因而包含原 V=H¹₀ 的全部能量，而不仅零阶值。

时间网格 period=T 保留同一固定原时间域。取样为 nodeTime i=i·dt，实际重构胞元是 (i·dt,(i+1)·dt]，故正是论文前一时间层。第二个结论明确是 **dt⁻¹·((Σηₗ(tᵢ₊₁)I_hψₗ)−Σηₗ(tᵢ)I_hψₗ)** 的整个和差商；T191 证明先精确分配有限和差/数乘，再用同一空间因子与真实标量差商组合。原标量差商已由胞元内 FTC 等于导数平均，并由同一实际平均投影的全 L² 收敛推出，非预设极限。

ηₗ、fₗ 只需在 [0,T] 连续，且所有区间点满足真实 HasDerivWithinAt ηₗ (fₗ t)；原 C∞ 时间测试满足这些更弱条件。端点只用 within 正则性，未要求全实轴延拓、周期 η(0)=η(T) 或区间外可微。T≥0 是原正周期的弱条件，并由合法 TimeGrid 与 period=T 自动满足。

空间 maxDiameter→0 与 dt→0 沿同一 n 独立要求；双线性连续性处理两个各自收敛因子，未将空间误差除以 dt，因此没有 h/dt 耦合或网格嵌套。固定有限和索引可任意有限并允许空和。第16项对每个固定 τ 只用常数数乘与有限和强收敛，特别给 τ=0、T；结论甚至在原 H¹₀ 范数成立，通过连续值嵌入包含原 H 的端点测试结论。它不是状态 y 的时间连续迹结论，也没有声称任意变化 τ_n 的一致收敛。

## 量词与范围

实际前提为固定开凸 S、有限限制体积，有限 conforming 且 BoundaryFitted 的网格序列，真实正内球与统一 κ 形状界、真实最大直径趋零，以及上述固定 T 和独立时间细化。原 bounded convex 多面体及其形状正则 P1 网格满足这些接口；没有 grading、小权、h 下界或 H² 数据限制。没有在本批构造某个具体网格族，但也没有以任意替代插值取代原 I_h。

允许 d=0、空域、空网格及空张量和：导数方向为空时真实导数为零，maxDiameter 的空 supremum 为0，H¹₀/Lp 零空间与有限和均合法；旧 H¹₀ 成员证明已明确分支处理空域，未偷偷选择域内点。内球 r>0 仅对实际存在的胞元量化。

本批清偿原 P1 节点测试的 H¹₀ 空间/时间强一致性、整和差商及固定端点。原稿相邻的产品 L∞ 测试误差、差分 R_h/E_h 测试识别、势乘积最终极限、完整弱方程极限和状态端点并非本批结论。保持 AUXILIARY、17/26，不因辅助一致性自动提升整个 P021。

## 依赖闭包、构建与公理

三入口实际导入闭包共 **155** 个 Carleman 模块，其中 **152** 个旧模块与 mathematical_base 逐字节相同；从基线到 proof 的数学改动恰为三个新模块。关键已接受版本完整闭包另核对，无变化：

| 入口 | 已接受版本 | 闭包模块数 |
| --- | --- | --- |
| Control/TensorTimeTests / T191 | `ec7ddbfba0b338f3ba97039442ed5c2108ac99aa` | 69 |
| Spatial/P1InitialDataApproximation / C197 | `7a2f33cfe125a118ee1792410345603891957e6c` | 123 |
| Spatial/SimplexTaylorInterpolation / C075 | `daf0c9e455f04bf5d7eff4e4ecde1729e01f6a92` | 74 |
| Control/DirichletTimeWeakCompactness / T188 | `32711e6669f223eba5851b43e9ec886a40c45b6e` | 59 |

固定根模块实际导入全部三个入口，16项均有固定 `#check @` 和 `#print axioms`。新模块无 sorry、admit、native_decide 或新 axiom。固定原始类型逐项核验：16项仅依赖正常 **propext、Classical.choice、Quot.sound**。全 raw 独立解析 **3381** 条显式公理记录（**3377** 个不同名字、**9** 条无公理），白名单外依赖为零；实际末行确认 **8631 项 Carleman 声明递归审计 PASS**。显式打印记录数与全环境递归数不混用。

实际读取 `/tmp/carleman-t192-target1.log`：三个新模块定向 **3340 jobs** 成功；`/tmp/carleman-t192-build.log` 根构建 **4176 jobs** 成功；`/tmp/carleman-t192-axioms.log` 为零字节 stderr。成功依据包含真实 raw 审计末行，不由空输出推断；未使用开发 probe 或变化中的工作树重跑结果替代固定版本证据。

固定 `/tmp/carleman-t192-p1-tests-local-axioms.txt` 实测 **2791191 bytes**、SHA256=`0c0e6ba3b612b60ca008710a1c3ef30d896ac308ea7df7d8e862d4186a288938`。Lean pin **4.35.0**，mathlib pin 与实际本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、lean_ci.sh 及两个 workflow 与数学基线逐字节相同。

## 正式 CI 与签发

本 Agent 按精确 SHA 独立发现 [main run 39354880337 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39354880337/attempts/1)。实际 `event=push`、`head_branch=main`、`head_sha=560e3aa8d23c22943b51dd7744da8174944b27ef`；最终 API 为 **completed / success**，updated_at=`2026-10-20T01:46:57Z`。三项实际 job 的 head_sha 均逐一匹配固定证明：

| 作业 | job ID | 最终状态 | completed_at（UTC） |
| --- | --- | --- | --- |
| lean | `118407281387` | completed / success | `2026-10-20T01:46:44Z` |
| state-check | `118407281518` | completed / success | `2026-10-20T01:42:11Z` |
| dashboard / snapshot | `118408609223` | completed / success | `2026-10-20T01:46:56Z` |

本次摘要 API 已真正终结成功，无需使用状态迟滞的完整日志替代路径。独立原始查询保存于 `/tmp/carleman-t192-p1-tests-review-runs.json`、`-review-run.json`、`-review-jobs.json` 与 `-review-artifacts.json`。

本 Agent 自行执行两次 `gh run download 39354880337`，实际均 exit 0，分别下载 `lean-ci-result` 到 `/tmp/carleman-t192-p1-tests-main-ci`，`lean-declaration-evidence` 到 `-main-axioms`，没有使用 root 副本。同 run 的两个工件 workflow_run 均精确绑定上述 SHA/main/run：

| 工件 | artifact ID | ZIP bytes | GitHub ZIP SHA256 |
| --- | --- | --- | --- |
| lean-ci-result | `12235165405` | 491 | `5ca303e0732be6ce30ceef82cefba92d3024faf07c7b755f0186835bbf7569dd` |
| lean-declaration-evidence | `12234519973` | 257843 | `c42dbaa8c2cb469cc0ac75578c6ccffe9353f658b04011e106653db9427d0647` |

实际 `-main-ci/result.json` 为 **537 bytes**，SHA256=`ae1d48b3c53d245ca22d20767b65c9fdae67e88296363984b2e7bf69a9593483`；`status=PASS`，`checked_sha=source_head_sha=560e3aa8d23c22943b51dd7744da8174944b27ef`，`targets=[Carleman]`，ci_url 精确指向本 run/attempt，finished_at=`2026-10-20T01:45:03.857724+00:00`。Lean 4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 和 mathlib pin 匹配。

实际 `-main-axioms/axioms.txt` 与固定 `-local-axioms.txt` **逐字节完全一致**，均 **2791191 bytes**、SHA256=`0c0e6ba3b612b60ca008710a1c3ef30d896ac308ea7df7d8e862d4186a288938`；16项完整类型/公理记录及末行 **8631 项递归审计 PASS** 均在同一原始文件中核实。ZIP 摘要和展开文件摘要分别记录，没有混用。

## 正式判定与冻结

**T192 / C208：PASS，16/16；axiom_check PASS，无阻断或非阻断数学缺陷。** 原节点插值、真实 H¹₀ 成员、值及完整弱梯度、统一 κ、固定 T、独立时空细化、有限整和差商与测试端点均符合对应原文步骤，目标空间强收敛已内部清偿。

保持 **AUXILIARY、17/26**，不提升整个 P021，也不把测试端点一致性当状态初终迹或把本批当产品 L∞/势乘积/极限 PDE 的完成。此报告为本 Agent 唯一仓库写入，只单文件提交，不推送、不修改实现或台账。签发时间与正文现冻结。
