# T111 / C127 独立本机验收

- `checked_sha`: `0d91a94335bd491366597b81f45de26b4559b7ad`
- `base_commit`: `20523c258707a3864f45541d0eea83581360c86b`
- `reviewed_at`: `2026-10-19T04:21:05+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**；原完整 P1 空间上实际 Π_h(σ²z) 的完整 `Section4.WeightedTest` 接口。一般 H² 逼近及完整 P1/P011 不在本次完成范围，原文保持 **14/26**。

独立从固定 Git 对象读取新模块全部源码和证明、实际展开类型、`governance/analysis/T111-p1-weighted-test.md`、对应 MATH_SPEC 和关键依赖，对照原 `paper/main.tex` N4（453–464）、原 P1 空间及分级条件（1469–1485）、`prop:p1`（1499–1500）和 Step 3（1569–1607）。执行者说明和 CI 没有代替语义检查。自行查询同 SHA main CI、自行下载并逐字节比对原始产物；工作树后续的 `SmoothAveragedTaylor`、`SmoothH2NodalError` 等 T112 增量均排除。

## 固定声明

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `full_p1_weightedTest_interface` | `Carleman/Control/FullP1WeightedTest.lean:13` | PASS；完整名称 `Carleman.full_p1_weightedTest_interface`。内部供应原全空间超逼近与真实时间字段，先选正统一阈值和常数，结论明确同一实际 op/derivative 身份，没有待证测试估计前提。 |

交付 `/tmp/carleman-p1-weighted-test-declarations.json`、固定 C127/T111 台账及固定公理产物中的声明名称一致。实际类型除原域、轮廓、网格及时间权假设之外，没有外部 `IsFiniteMeasure`、额外空间完备性、节点表示、光滑状态或超逼近假设。

## 完整原 P1 空间和真实投影

最终 X 明确为 `M.conformingSpace (dirichletSubspace S)`。已直接读取 `SimplicialPartition` 及其成员刻画：M 使用真实非退化 d 单纯形、覆盖 S、位于 closure S、不同单元内部不交；X 中成员恰为原 `dirichletSubspace S` 成员且在每个真实单元上 a.e. 等于仿射多项式。它是完整 H¹₀∩分片 P1 空间，没有换成预选节点表示的像或某个较小子空间。X 的有限维性来自实际有限单元构造，随之供应 L² 完备性和正交投影；没有将 H¹₀ 本身误认为 L² 闭子空间。

`Physical.conformingReconstruction` 的 R 是 X 到原 V 的实际包含，J 是 X 的 L² 正交投影。它的质量伴随身份由真实正交投影证明；新结果明确使用这个 Reconstruction。X 的内积继承原 L²(Ω)，对应一致质量 P1 内积，未换成节点 Euclidean 内积或 FD 对角质量。

已直接读取 `galerkinWeightedTest` 的定义及作用证明。令 F 为真实 σ 乘法与 X→L² 包含的复合，则测试为 F*F，且实际作用严格等于 `X.orthogonalProjectionOnto (σ.map (σ.map z))`，也就是原 Π_h(σ²z)。它不是仅满足某个估计的任意测试算子。最终结论分别给出 `T.op` 和 `T.derivative` 与这些具体构造的函数等式；构造中对 T₀ 仅扩大时间常数，op 和 derivative 均原样保留。

## 真实时间导数、配对与端点

实际导数构造是 `F′*F+F*F′`，其中 F′ 来自真实允许权乘法算子的导数再复合包含。已直接读取 `TemporalMultiplier.hasDerivWithinAt_weightCLM`：它在 L² 连续算子空间的算子范数中证明 σ 乘法的真实相对导数，使用原 q 的 HasDerivWithinAt、q>0、对数与指数求导，绝非自命名的候选系数。

`galerkinWeightedTest_hasDeriv` 通过该真实导数作用于固定 z，再对实际内积微分，正式给出闭区间 [0,T] 上二次配对的 HasDerivWithinAt，导数是同一个 `galerkinWeightedTestDerivative` 的配对。其公式是两项真实内积之和，正对应原 `(z,T′z)=∫(σ²)′z²`，因而保留平方权的因子 2。`galerkinWeightedTestData` 将此结论填入 WeightedTest.hasDeriv。本批没有新增一条针对整个 Galerkin 测试路径的算子范数 HasDerivWithinAt 声明；正式微分字段是接口原本要求的真实二次配对导数，其依据是已经证明的权乘法算子范数导数。

端点字段由原 q(0)=q(T) 经真实权乘法算子得到，两个端点均在相对导数范围内；未把一般 TimeWeight 的上/下界当成周期性。原 q 的 C² 和端点匹配供应 `TimeWeightRegularity` 所需较弱的一阶数据，没有增加状态轨迹的时间正则性。

实际 F*F 配对恒等式给对称性、非负性及精确能量 `(z,Tz)=‖σz‖²`。允许权非零和原 multiplier 的 definite 性保证原非零状态的正定性，能量比较的常数为 1。WeightedTest 只存储 Section 4 需要的非负字段，不将其误称为另有 test-norm 或严格正定字段；同一实际测试的既有精确身份保持不变。

时间估计使用实际对数导数作用，给 `2β(τStar+(ρ.scaled η).bound) (q‖σz‖)²`，不使用投影稳定性或网格相关等价常数。由 abs η=1，缩放 profile 的 bound 精确等于原 ρ.bound。新证明取 `Ctime=2β(τStar+ρ.bound)+1`，利用非负平方扩大系数，使 Ctime 严格为正；即使 τStar=0 或 ρ.bound=0 也合法。该常数不依赖周期、网格、qmax、时刻、符号或状态。

## 实际空间超逼近内部供应

新声明调用 `full_p1_galerkin_superapproximation` 取得 ε、Csuper 和对全部满足原几何条件网格的超逼近，再以当前 M、r、ℓ、w、g、τ、η 实例化得到 hs，传入 `galerkinWeightedTestData`。因此 C049 旧接口中显式保留的 hs 在这里已由 C082 的实际定理清偿，不是换名后仍作为最终调用者前提。

已读取实际调用链：`allowed_full_projected_superapproximation` 使用完整 X 的两种逆权投影界、真实加权逆估计及同一全状态节点残差，构造真实弱 H¹ jet，值类为 `Π_h(σ²u)−σ²u`；它不要求 u 是额外光滑代表。`full_p1_galerkin_superapproximation` 再取 X 的任意状态的 canonical Sobolev jet，使用真实投影作用公式、两次乘法身份和完整弱导数唯一性，把所得残差识别为接口中同一 V 值误差的整个弱 jet。符号和 σ⁻¹ 均正确：profile 缩放符号与幂同时反转，`scaled_neg` 给完整结构身份。

接口中的 `conformingWeightedNorm` 是原实际 H¹ 弱 jet 范数，平方为 `q²‖σu‖²+‖σ∇u‖²`；该字段没有被零阶 L² 估计代替。最终系数为 `Csuper*M.maxDiameter*w.max`，准确保留原 hqmax。所有状态均为 X 的任意成员；不存在节点数据资格、梯度代表或目标估计的额外输入。

superapprox 字段仍按原 WeightedTest 定义量化每一份 A2 乘法保持性证明 hw，以便在原 V 内写两次 `conformingWeight`。这不是新增到最终 `∃T` 外层的假设，也不把一般 H¹ jet 自动视为 H¹₀。新结果对同一原接口的全部字段给出了证明，但不据此宣称完整 A2 或原连续算子正则性已完成。

## 原几何条件、有限测度与统一性

几何条件准确保留：实际有限非退化单纯形分区、真实 FaceMatching 和 BoundaryFitted、正内球半径 r_K 及 ball(a_K,r_K)⊆K、真实直径 h_K≤κr_K、正局部尺度 ℓ_K、c h_K≤ℓ_K≤B h_K，以及共享顶点单元的 ℓ_j≤γℓ_i。FaceMatching 表达公共部分由公共顶点生成，BoundaryFitted 表达边界部分由实际边界节点生成，均属于原 conforming、贴合边界的单纯形网格条件，未添加锐角、Delaunay 或准均匀条件。

`VertexNeighbors` 是实际共享顶点关系且对称；在正 ℓ 上，全称单侧不等式同时给出原双侧比值界。`p1GradingLimit d=(√(d+2)+1)/(√(d+2)−1)`，与原 Γ_d 完全一致；保留原严格条件 `1≤γ<Γ_d`。辅助定理对更多维数成立，包含原 d∈{2,3}，没有凭此宣称这些维数之外的一般 H² 插值已完成。

原 S 开、凸且闭包紧；原有界凸多面体满足它。新类型在结论内部使用 `letI : IsFiniteMeasure (volume.restrict S)`，证明来自 closure S 紧⇒有界、S⊆closure S 及 Lebesgue 测度的有界集有限性；证明体中提供同一局部实例。实际展开类型没有外部有限测度参数。有限维 X、其完备性及真实 Sobolev 包含也由已有构造供应，无需调用者另给。

ε∈(0,1]、Ctime>0、Csuper>0 均在固定 d、S、ρ、κ、c、B、γ、β、τStar 之后、全部网格索引类型/剖分/内球/局部尺度/TimeWeight/TimeGrid/周期/两符号/状态之前选择。唯一网格小条件是 `M.maxDiameter*w.max≤ε`。C082 的阈值先于全部网格选择，并使实际四类允许权的有效分级严格低于 Γ_d；不能把原 γ 直接误作带权后的分级值。abs τ≤τStar 和 abs η=1 保留完整原允许权族。Csuper 未随当前网格或 q 重新选择；Ctime 的 +1 只作固定正数扩大。

空域、空索引或零状态不触发除以网格数、状态范数或域测度的步骤。没有把旧全局有限测度实例作为外部前提，也没有通过有限维性偷引入用于统一估计的网格常数。

## 依赖版本和证据

新模块的 Carleman 导入闭包共 **402** 文件，其中 **401** 个既有文件相对基线逐字节不变。进一步逐文件比较：`FullP1Superapproximation` 的 **401** 文件闭包与 [T066/C082 验收](T066-local-acceptance.md) 的 `1f04be4f79db9d40ac1af37271eb8e9dc58639a3` 完全相同；`GalerkinTestData` 的 **287** 文件闭包与 [T033/C049 验收](T033-local-acceptance.md) 的 `d999e5b3779aa82efee2da8e162b86148dc1f715` 完全相同。本次仍直接核对调用的实际字段和关键证明，不仅引用旧报告的结论。

固定 root 已导入新模块。原稿、已读治理协议、工具链和 manifest 未改；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。

独立读取 `/tmp/carleman-p1-weighted-test-target.log`：定向 **3614 jobs** 成功；`/tmp/carleman-p1-weighted-test-full.log`：全库 **3833 jobs** 成功，实际 **6556** 项递归公理审计通过。

独立查询 [main CI run 39198725994 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39198725994/attempts/1)，head 精确为固定 SHA，分支 main，最终 `completed/success`，更新于 `2026-10-19T04:20:32Z`。等待三作业实际全部结束后才签发：

| Job | ID | 最终结论 | 完成时间 UTC |
|---|---|---|---|
| state-check | 117887017645 | success | 2026-10-19T04:17:40Z |
| lean | 117887017976 | success | 2026-10-19T04:20:22Z |
| dashboard / snapshot | 117887739990 | success | 2026-10-19T04:20:31Z |

自行下载的 `lean-ci-result` artifact ID **12162648718**；原始 `/tmp/carleman-p1-weighted-test-main-ci/result.json` 为 PASS，`checked_sha=source_head_sha=0d91a94335bd491366597b81f45de26b4559b7ad`，目标 Carleman，`finished_at=2026-10-19T04:19:20.655122+00:00`，CI URL 与上述 run/attempt 精确一致。

自行下载的 `lean-declaration-evidence` artifact ID **12163077273**；原始 `/tmp/carleman-p1-weighted-test-main-axioms/axioms.txt` 与固定 `/tmp/carleman-p1-weighted-test-local-axioms.txt` **逐字节相同**：**1,946,527 bytes**，SHA256 **`be77fb7bbc510990a10f718941a1290c5a15652c6b2c4f4cb104fa94684c6466`**。两 artifact 的 workflow_run 元数据均对应本次 main/head/run，未使用后续 `.ci`。

该声明恰有一份实际类型打印，公理仅 `propext`、`Classical.choice`、`Quot.sound`。全产物有 2212 条非空公理打印和 8 条无公理打印，合计 2216 个不同显式名称；包含生成声明的实际递归审计为 **6556** 项，两者不混称。已核对固定检查器的全 Carleman 常量遍历及 `collectAxioms`，只允许上述三项基础公理；检查逻辑相对基线不变，仅增加本声明的类型/公理打印。未见 sorryAx 或其他数学公理。

原始结果记录 Lean **4.35.0**、mathlib **`56a005855ea17e0b0958f73ec801ae140b0a1679`**，与固定 pin 一致。此验收只新增本报告，未修改实现、台账、原稿、root 或提交。

## 验收决定

**C127 可升为 REVIEWED / AUXILIARY。** 单项声明的真实投影测试、明确导数身份、完整原空间与几何条件、实际超逼近/时间字段供应、有限测度来源及统一量词均通过，未发现需要修复的数学缺陷。原全 H² 逼近及完整 P1/P011 仍待，不提升完整论文结果，原文保持 **14/26**。报告定稿后冻结内容和 reviewed_at。
