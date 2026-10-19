# T186 / C202 独立本机验收：原 E_h 与 Kuhn R_h 的完整空间一致性

- checked_sha / source_sha: `2f52ae6bafebec9c18313da458507026064a7542`
- mathematical_base: `fe308a7e6958dc8a2caa9f9dec3c331ae5678a03`
- reviewed_at: `2026-10-19T16:06:52+00:00`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS，10/10**；无数学修复项。三项实际作业由自行下载的完整日志核实成功结束，API 摘要迟滞如实单列。
- scope: **AUXILIARY**，原文覆盖保持 **17/26**。本批只清偿原差分 E_h−R_h 空间重构误差，不等于完整状态或控制收敛。

## 固定版本、原文及真实量词

直接读取固定 Git 对象四个新模块全部证明、固定 raw 的十项完整展开类型、T186 分析、MATH_SPEC 和 C202 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与本 Agent 已读 T183 版本相同，沿用其规则。后续 FixedBoxKuhnConsistency、CartesianStateWeakConsistency、时间能量/方程一致性等工作树增量，以及动态根导入和 .ci 输出均排除。

验收过程中另完整读取治理提交 `dab075a80599541c0ecafdbdce7a3b2fa2f0d609` 的 PROJECT_OPERATIONS 及其唯一新增段：摘要迟滞时须独立下载同 run 精确 job 的完整日志，核对源码、实际成功及最终清理，再比较原始工件，不能将未读到的 API 终态冒写为成功。本批按此规则处理，不把该治理提交当成数学证明版本。已完整读取 T185 冻结报告，报告提交 `5b3612e6e77084ba69726720c748e54dc83fe796`，checked 正是本批 mathematical_base，reviewed_at=`2026-10-19T16:01:12+00:00`，7/7 PASS；其报告没有替代本批实际源码与依赖审查。

实际对照原 `paper/main.tex:2893–2905`：eq:conv-consistency 要求 **‖E_h z−R_h z‖₂≤C h‖R_h z‖H¹**；原差分证明必须包括未覆盖边界条带，有限元则 E_h=R_h。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，与已验版本一致。

本批实际结论更强：对每个固定 d，**先存在 C>0，再量化全部原点 o、各坐标正步长 δ、任意自然数节点数 N、h≥0、δ_j≤h，以及全部 CartesianPhysicalState δ hδ N 中的原状态 f**，有 **‖cartesianCellIsometry f−cartesianKuhnReconstructionLp f‖₂≤C h‖field 1 (cartesianKuhnReconstructionJet f)‖₂**。右端是同一原重构的全部弱梯度纤维，非另给估计字段。实际 SobolevJet 中一阶纤维为 EuclideanSpace ℝ (Sym (Fin d) 1)，每个坐标恰出现一次；其 L² 范数由原完整 H¹ 范数控制。故这条加强的梯度半范数估计保留原式；未另声称本批已命名一个 H¹ 右端包装定理。

## 全部十项声明

顺序与固定 manifest 一致。源码相对 `Carleman/`，raw 行为固定完整类型起始行；十项均为实际定理。

| 序号 | 完整声明 | 固定源码 | raw 行 | 判定 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.antitone_threshold_cut` | `Geometry/KuhnNearestVertex.lean:12` | 35205 | 单调坐标阈值集确为初始段，含空段及全段；PASS。 |
| 2 | `Carleman.kuhnOrderedCube_nearest_vertex` | `Geometry/KuhnNearestVertex.lean:44` | 35208 | 参考有序单纯形中真实最近 0/1 顶点；PASS。 |
| 3 | `Carleman.cartesianKuhnSimplex_nearest_vertex` | `Geometry/KuhnNearestVertex.lean:58` | 35213 | 真实仿射图及排列运回同一物理单纯形；PASS。 |
| 4 | `Carleman.coordinate_hyperplane_volume_zero` | `Geometry/CoordinateHyperplaneNull.lean:12` | 35219 | 实际坐标超平面为适当仿射子空间，真实体积为零；PASS。 |
| 5 | `Carleman.coordinate_ne_ae` | `Geometry/CoordinateHyperplaneNull.lean:28` | 35221 | 上述真实零测集合的 a.e. 补集；PASS。 |
| 6 | `Carleman.cartesianKuhnSimplex_nearest_vertex_ae` | `Geometry/CoordinateHyperplaneNull.lean:32` | 35223 | 每个真实单元 a.e. 点存在同单元严格最近顶点；PASS。 |
| 7 | `Carleman.cartesian_lattice_unique_nearest` | `Spatial/CartesianCellNearestValue.lean:13` | 35230 | 严格半步长邻域不能含两个不同整数格点；PASS。 |
| 8 | `Carleman.cartesianCellFunction_nearest_value` | `Spatial/CartesianCellNearestValue.lean:31` | 35236 | 原指示重构等于原最近节点值，包含非内部节点零值；PASS。 |
| 9 | `Carleman.cartesianCell_kuhn_pointwise_consistency` | `Spatial/CartesianCellKuhnConsistency.lean:17` | 35243 | 原全域 a.e. 误差受 C h 乘真实全部弱梯度控制；PASS。 |
| 10 | `Carleman.cartesianCell_kuhn_L2_consistency` | `Spatial/CartesianCellKuhnConsistency.lean:69` | 35256 | 同一 E_h、R_h 的真实 L² 范数估计，C 仅依赖 d；PASS。 |

## 同一单纯形最近顶点与零测例外

第 1 项对 s={j:c<a_j} 取 k=card s。Antitone 使该集合确为初始段：两侧分别用 Iic j 的包含与基数反证，得到 j<k 当且仅当 c<a_j。k 属于 Fin(d+1)，因此阈值前无元素及全部元素均被覆盖，未遗漏端点。

第 2 项在真实 kuhnOrderedCube 中取 c=1/2。坐标均在 [0,1] 且按规定次序单调，所得前 k 个坐标为1、其余为0的向量正是 kuhnReferenceSimplex 的第 k 个顶点。排除坐标恰为1/2后，各坐标误差严格小于1/2；边界坐标0、1仍合法。使用的是已证明与实际凸包相同的有序区域，不是另定义的较小单元。

第 3 项通过原 cartesianKuhnSimplex 的正对角仿射图与原排列传输该顶点。每个坐标严格距离为 δ_j/2；正性用于合法除法。没有反映射算子范数、min δ 或单元纵横比损失。

第 4 项将 {x:x_j=c} 写成实际坐标投影对单点仿射子空间的原像；取 (c+1)e_j 证明它不是全空间，再调用 mathlib 对有限维 Haar 测度的适当仿射子空间零测定理。已读取该定理真实证明：通过非全方向子空间的平移不交性和 Haar 平移不变性得到零测，不假设目标超平面本身零测。

第 5–6 项有限合并所有坐标中间平面的零测例外，然后限制到真实闭单元；单元可测性保证 a.e. 点确属该单元。删除的仅为中间平面，**没有删除正测度边界条带**，也未把闭单元面上的点态身份冒称所有点均严格最近。

## 原 E_h 节点身份与完整边界条带

第 7 项若两个整数格点均与 x 每坐标相距严格小于 δ_j/2，则两格点相差严格小于 δ_j；但不同整数坐标的物理距离至少 δ_j。逐坐标矛盾后得到整格点相等。严格不等号与中间平面零测处理配合准确，未误处理等距点。

第 8 项直接使用原 finiteCellFunction(cartesianDualCell) 和 cartesianInteriorData。若最近格点是实际内部节点 a，则 x 属于原开对偶单元 D_a，真实指示和的值为 f a，原节点数据在该点也严格等于 f a。

若该格点不是内部节点，则任何内部 D_a 对 x 的覆盖都会给另一个严格最近格点，与第 7 项冲突。因此 x 不属于任何内部对偶单元，原 finiteCellFunction 在 x 确为零；原 cartesianInteriorData 的有限节点指示和也确为零。这个分支包括原边界顶点附近的未覆盖条带。它没有新增调用者提供的边界条件，也没有修改 E_h：零边界节点数据本来就是原完整内部节点状态的延拓。

这里采样的是原有限节点数组及其明确点函数延拓，未对任意 Lp 等价类取点值。E_h 的 L² 输出最终由既有实际 cartesianCellIsometry_ae 与该点函数相连。

## 实际弱梯度、全域拼合与统一常数

第 9 项在每个实际有限 Kuhn 单纯形 S 上，令 p 为**原节点值的实际 simplexNodalInterpolant**。第 6、8 项与真实顶点插值身份给 E_h f(x)=p(v)，原 cartesianKuhnReconstruction_on_cell 给 R_h f(x)=p(x)，其中 v 属于同一 S。不是使用任意拟合仿射函数替代原重构。

两点都在以 v 为中心、各边长 δ_j 的实际闭坐标盒中，既有真实 Euclidean 距离估计给 dist(v,x)≤d h。仿射 p 的真实 Fréchet 导数 A=affineScalarDerivative p 给 **|p(v)−p(x)|≤‖A‖ dist(v,x)**，而同一原弱 jet 的单元身份给 field 1(R_h f)(x)=derivativeOneFiber A。

重新读取 CartesianKuhnReconstructionJet、SimplicialLocalGradient、AffineWeakGradient、FirstOrderSobolevJet：原 R_h 的实际 Lp 类属于原 H¹₀ 图闭包，所选 jet 的 value 严格等于该类；全部一阶字段由分布测试连接。单元内仿射身份通过真实弱导数唯一性识别所有坐标导数，使用开凸域内的单元内部包含和真实零测单元边界传回闭单元。未以任意梯度见证或单一方向替代原弱梯度。

DerivativeFiberNorm 的逆向界由真实 derivativeOneFiber 单射导出：对每个坐标基向量恢复 A 的值，故两个 CLM 相同。有限维反 Lipschitz 比较应用于**固定 d 的全部线性泛函空间与完整坐标纤维**，不是随网格变化的状态空间。因而先选 R=R(d)>0，再选 **C=R d+1>0**，即可在所有 o、δ、N、h、f 之前固定常数。此处没有用有限维自动连续性偷取依赖 N 或网格的“统一”常数；p 自身的导数范数由同一真实梯度精确控制。

原 cartesianKuhnPartition.ae_of_cells 以真实有限分割、单元测度限制转换及 a.e. 覆盖，将上述单元结论拼回原整个开盒。此步骤不求和估计常数，不引入单元数或 d!。第 10 项再同时使用 Lp 差的 a.e. 代表、原 E_h 与原 R_h 的实际代表身份，应用真实 Lp 范数单调性。无需额外可积性输入：差与完整梯度本来均为相应原 L² 元素。

所有 N_j∈ℕ 均允许：正维数中 N_j=0 时原盒空，a.e./Lp 结论退化正确；N_j=1 可没有内部节点，原状态空间及重构零值仍有效。d=0 时无坐标超平面可选，全部 Fin d 条件真空，固定泛函空间的单射/反 Lipschitz 引理有 subsingleton 分支，C=1；两重构在零维点空间一致，未除以 d 或选取不存在的方向。原点任意平移及任意正各向异性步长均保留。无时间参数、T 因子、节点数因子或网格分级前提。

## 固定闭包、公理和已读构建

递归解析四入口的实际 Carleman 导入共 **339** 模块，除四新增模块外 **335** 个与 mathematical_base 逐字节相同。关键旧接受版本的完整依赖闭包另行比较，全部无变化：

| 入口 / 阶段 | 固定接受版本 | 闭包模块数 |
| --- | --- | --- |
| KuhnOrderedCell / T086 | `e753eb065d87695d33e31c141cfe15c7cea4b5de` | 103 |
| CartesianKuhnReconstructionJet / T095 | `116908340801d3f1cd9f7e940304807f70bdb1ba` | 183 |
| DerivativeFiberNorm / T046 | `0c632f37eadbcece6459555fef22a2bb4b3ca688` | 34 |
| CartesianCellReconstruction / T175 | `7c2ceacf62d42b168879106b8c6d6fc246c45794` | 326 |
| FiniteCellMultiplier / T182 | `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` | 46 |

固定根模块导入全部四入口，十项均在固定 CheckAxioms 中实际 #check @ 与 #print axioms。新增源码无 sorry、admit、新 axiom 或 native_decide。十项公理仅正常 `propext, Classical.choice, Quot.sound`；独立解析固定 raw 全部 **3271** 条显式公理记录（**3267** 个不同名字，**9** 条无公理记录），规范化换行空白后无白名单外依赖。递归 auditor 实际末行为 **8422 项 Carleman 声明全部 PASS**。

已实际读取 `/tmp/carleman-t186-cell-kuhn-consistency-target2.log`：最终 CartesianCellKuhnConsistency 目标 **3530 jobs** 成功；`-build.log`：根构建 **4149 jobs** 成功。`-axioms.log` 为零字节 stderr，递归成功来自上述固定 raw 末行。未把较早的 target.log 作为最终目标证据。

固定 raw `/tmp/carleman-t186-cell-kuhn-consistency-local-axioms.txt` 实测 **2696533 bytes**，SHA256 **`0b020f5ec7659c5db4b0d3690cbbb54fa9cfa51cc27ba385be74f92b8c14c5de`**。Lean pin v4.35.0；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、workflow、lean_ci.sh 与已审 T183 版本未变。mathlib 的实际 `Measure.addHaar_affineSubspace`、`LinearMap.injective_iff_antilipschitz` 和 `ZeroHomClass.bound_of_antilipschitz` 的类型和证明本次重新读取。

## 同 SHA 原始工件与独立下载

本 Agent 自行查询 GitHub run/jobs/artifacts，并分别执行两次 gh run download，均 exit 0；没有采用执行者的 root 下载副本。

- run: [39282223997 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39282223997/attempts/1)，event=push、branch=main、head_sha 精确为本报告 proof SHA。
- 实际三个 job：lean **118158604163**、state-check **118158604470**、dashboard / snapshot **118159926270**；三个 job 元数据均绑定同 run、attempt 和精确 SHA。
- `lean-ci-result` artifact **12201551388**，ZIP **492 bytes**，API digest=`sha256:71ed70358b896f2d937e8af42644fcf85f149367820ca989f02cd02711c1da63`。
- `lean-declaration-evidence` artifact **12201596493**，ZIP **249401 bytes**，API digest=`sha256:e71b7613506694f33aaed273190183d49b88dd038176df780386a969163bf27d`。
- 两个工件 workflow_run 均精确绑定本 run、main 和 checked SHA；ZIP digest 与解包文件 hash 分别记录。

独立 `/tmp/carleman-t186-cell-kuhn-consistency-main-ci/result.json` 为 **537 bytes**，SHA256=`455e52edc049b20c2316e3c3867d13df1c41dad690f3d4fb956ee4bae3c6f8de`；实际 status=PASS、checked_sha=source_head_sha=`2f52ae6bafebec9c18313da458507026064a7542`、targets=[Carleman]、finished_at=`2026-10-19T16:03:53.720371+00:00`。ci_url 精确指向上述 attempt；Lean compiler commit=`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib 与上述 pin 一致。

独立 `/tmp/carleman-t186-cell-kuhn-consistency-main-axioms/axioms.txt` 与固定本机 raw **逐字节完全一致**，均为 **2696533 bytes**，SHA256 **`0b020f5ec7659c5db4b0d3690cbbb54fa9cfa51cc27ba385be74f92b8c14c5de`**。十项完整类型、公理及末行8422项审计成功核对通过。

## API 迟滞与三个精确作业的完整结束记录

独立保存 `/tmp/carleman-t186-review-run.json`：run 的实际 API 字段仍为 **queued / conclusion=null**，updated_at=`2026-10-19T16:01:08Z`；`/tmp/carleman-t186-review-jobs.json` 中三个 job 均仍为 **queued / conclusion=null / completed_at=null**。本报告**没有读到 API completed/success，不作这种陈述**。这与原始工件及完整日志中的实际执行时间明显不一致。

本 Agent 从三个精确 `/actions/jobs/{id}/logs` 端点分别自行下载完整日志，三命令均 exit 0。逐份检查真实 checkout SHA、作业名、成功输出、上传及 Post job cleanup / Cleaning up orphan processes；全部无 `##[error]`、非零 process exit、取消或中断记录。固定 lean-ci.yml 和 dashboard.yml 已直接重读，实际构建、审计、测试、上传均无 continue-on-error；runner 的 Node.js 兼容性/弃用告警不是失败。

| job / 自行下载日志 | 实际成功依据 | 末行 UTC | bytes / SHA256 |
| --- | --- | --- | --- |
| lean / `/tmp/carleman-t186-lean-review.log` | 4149 jobs构建成功、8422声明审计PASS；BUILD_OUTCOME/SETUP_OUTCOME=success；Recorded PASS精确SHA；两个工件上传完成；2046353341 bytes缓存上传100%、Cache saved及最终清理。 | `2026-10-19T16:05:08.6547575Z` | 3747183 / `3c3451334ff0f654fb144a7db5a22437fa7b42ac1b6e60c8e157efe8198f55ad` |
| state-check / `/tmp/carleman-t186-state-check-review.log` | 21个Python测试OK、10个Node测试pass/fail0，State/coverage consistent、display projection matches，最终清理。 | `2026-10-19T16:01:16.6620613Z` | 20358 / `29c1977ae87085911c2f2ac3bd51ddec4cec4b7d2938567a5fa08def924d9a12` |
| dashboard / snapshot / `/tmp/carleman-t186-dashboard-review.log` | 同run下载同ID/digest的lean-ci-result；EXPECTED_SHA/CI_URL精确匹配；State/coverage consistent、display projection generated；progress-dashboard上传完成及最终清理。 | `2026-10-19T16:05:20.5797603Z` | 16741 / `83d73d908cc5c2fe04cca6ffb7a7e41d9c9df532033c2115b94fe562a1487432` |

三份日志的末行均为清理之后的非失败兼容性告警。dashboard 上传工件 **12201346798**，**92867 bytes**，ZIP SHA256=`aee4874c12bf65818900f3f8486ed7581d2cc43469bd50a733ace29a9cc344aa`；其日志明确引用本 run、attempt 1 和固定 proof SHA。由上述完整执行记录确认三项**实际成功结束**，不是单凭工件存在、PASS 文件或执行者口述推定。保存的 API 摘要差异保留供复核，不因其迟滞改写实际字段。

## 最终签发

**T186 / C202 独立验收 PASS，全部 10/10 声明通过，无需修复。** 原 E_h 与同一节点数据的 R_h 在完整原域（含边界条带）满足更强的 C h 乘真实弱梯度半范数估计，C 仅依赖维数。所有原物理状态、平移和正各向异性步长均保留，无额外纵横比或非空内部节点条件。

C202 可登记 **AUXILIARY / REVIEWED**，原文仍 **17/26**。本批不供应状态时间能量界、Bochner弱子列、极限PDE、初终值或完整控制收敛。只提交本报告文件，不 push、不改数学/台账/原稿；签发后正文与 reviewed_at 冻结。
