# T050 / C066 独立本机验收

- `checked_sha`: `9ea552502177ccffb3f50593567578fc207c2568`
- `base_commit`: `99694c20834ac8d3b712f5e2d071a4e4ccfc308b`
- `semantic_checked_at`: `2026-10-18T19:57:10+00:00`
- `reviewed_at`: `2026-10-18T19:59:54+00:00`
- `result`: **PASS**；C066 可升 REVIEWED，范围保持 AUXILIARY
- `axiom_check`: **PASS**；同次远端原始产物与固定本机副本逐字节一致
- `scope`: **AUXILIARY**
- 范围：原实际 allowed 权的单元比较，以及以真实单元直径、内球形状界和原 ℓ_K 尺度实现的完整一致 P1 状态全域加权逆界。接受 `eq:element-weight-comparison` 和 `eq:p1-weighted-inverse` 这两个证明步骤；不提升整个 Proposition 6.1 或其他具名结果，原文计数仍为 12/26。

本次独立读取固定四模块全部源码、20 项展开类型、真实关键依赖与原论文。规格只用于定位，没有把执行者自检或编译通过等同于数学验收。后续 SimplicialNeighbors、GradingThreshold 等工作区草稿不属于本次范围。

## 全部 20 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。与固定 C066、T050 及交付 JSON 清单逐项一致，以下为语义结论。

| # | 声明 | 位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `uniqueDiffOn_closure_open_convex` | `Weights/SpatialComparison.lean:14` | PASS；开集非空时其闭包内部非空，真实凸性给 UniqueDiffOn；空域另行处理。 |
| 2 | `smooth_profile_lipschitz` | `Weights/SpatialComparison.lean:22` | PASS；固定 C¹ 剖面的真实闭域导数在紧集上有统一界，再用凸域均值定理得到 L≥1。 |
| 3 | `allowedWeight_spatial_ratio` | `Weights/SpatialComparison.lean:37` | PASS；q>0 保证 q^τ 非零，空间比值精确为 exp(η(a−b)q)，τ 因子完全消去。 |
| 4 | `allowedWeight_spatial_comparison` | `Weights/SpatialComparison.lean:43` | PASS；|η|=1 和 |a−b|≤D 给两侧 exp(±Dq)，符号、指数及正 q 方向正确。 |
| 5 | `SpatialProfile.scaled` | `Weights/SpatialComparison.lean:58` | PASS；真实函数 ηρ 及其 a.e. 可测、有界乘子数据，界为 |η|ρ.bound。 |
| 6 | `SpatialProfile.scaled_multiplier_value` | `Weights/SpatialComparison.lean:67` | PASS；实际乘子点态公式就是 q(t)^τ exp(ηρ(x)q(t))。 |
| 7 | `SpatialProfile.scaled_one` | `Weights/SpatialComparison.lean:70` | PASS；η=1 恰回到同一 SpatialProfile ρ。 |
| 8 | `SpatialProfile.scaled_neg_one` | `Weights/SpatialComparison.lean:74` | PASS；η=−1 恰为已有 ρ.neg，保持原 θ⁻¹ 的接口。 |
| 9 | `SpatialProfile.scaled_multiplier_pos` | `Weights/SpatialComparison.lean:78` | PASS；全部实 τ、η、t 下实际乘子严格正，含边界点。 |
| 10 | `SpatialProfile.scaled_multiplier_spatial_le` | `Weights/SpatialComparison.lean:82` | PASS；除法比较通过真实正分母还原为乘子值比较。 |
| 11 | `SimplicialPartition.cellDiameter` | `Spatial/SimplicialDiameter.lean:12` | PASS；实际 Metric.diam(M.cell i)，不是外加尺度标签。 |
| 12 | `SimplicialPartition.cellDiameter_nonneg` | `Spatial/SimplicialDiameter.lean:14` | PASS；真实直径非负。 |
| 13 | `SimplicialPartition.dist_le_cellDiameter` | `Spatial/SimplicialDiameter.lean:16` | PASS；单元紧性供应有界性，同单元两点距离≤其真实直径。 |
| 14 | `SimplicialPartition.maxDiameter` | `Spatial/SimplicialDiameter.lean:22` | PASS；有限 NNReal supremum 后转实数，空索引时值为 0。 |
| 15 | `SimplicialPartition.maxDiameter_nonneg` | `Spatial/SimplicialDiameter.lean:24` | PASS；包括空网格在内的非负性。 |
| 16 | `SimplicialPartition.cellDiameter_le_max` | `Spatial/SimplicialDiameter.lean:26` | PASS；每个真实单元直径≤同一有限最大直径。 |
| 17 | `SimplicialPartition.cellScale_le_inball` | `Spatial/SimplicialDiameter.lean:31` | PASS；ℓ≤B diam、diam≤κr 和 B≥0 精确组合为 ℓ≤Bκr，无逆向尺度错误。 |
| 18 | `SimplicialPartition.maxDiameter_mul_q_le` | `Spatial/SimplicialAllowedComparison.lean:13` | PASS；q(t)≤qmax 与实际最大直径非负给所有 t 的 hq(t)≤δ。 |
| 19 | `SimplicialPartition.allowedWeight_cell_comparison` | `Spatial/SimplicialAllowedComparison.lean:17` | PASS；真实闭单元包含 closure S，导数导出的剖面 Lipschitz 界、diam 及 hq≤1 给同一 exp L 双边比较。 |
| 20 | `conforming_allowed_weight_inverse` | `Spatial/ConformingAllowedInverse.lean:12` | PASS；内部供应权比较和 ℓ/内球尺度，对完整原 H¹ 一致分片仿射状态给实际 ‖σ∇u‖≤C‖ℓ⁻¹σu‖。 |

## 原文映射及假设边界

原 `paper/main.tex:291–302` 固定光滑 ρ、q≥1 及 qmax 上界，并定义 σ=q^τθ 或 q^τθ⁻¹，θ=exp(qρ)、|τ|≤τ_*。原 Section 6.1（1469–1485）使用有界凸多面体、形状正则单纯形网格、h_K=diam K、h=max h_K 和正 ℓ_K，且 ℓ_K 与 h_K 双边可比。Step 2（1523–1551）中的两项目标分别是单元上 exp(±Chq) 的权比界，以及全部 V_h=H¹₀∩P1 状态的全域加权逆界。

本批将最终逆界的权具体化为同一原公式，尺寸具体化为真实 Metric.diam 和有限最大值，并将 ℓ_K 上比较接到真实内球形状界，清偿 T049 中保留的这两类输入。最终仍公开要求真实几何数据 a_K,r_K：r_K>0、ball(a_K,r_K)⊆K、diam K≤κr_K；这是本批所用形状正则性的几何形式，不是额外的目标估计假设。对原形状正则单纯形网格，取其内球数据即可应用，未声称自动构造任意网格及其形状证据。

这个逆估计只需要 ℓ_K>0、ℓ_K≤B diam K，而不需要原 ℓ 的下比较和相邻 grading 条件。省去这些未使用条件扩大了适用范围，没有缩小原目标。邻接权比较和 DST 投影稳定性仍需原 grading 信息，尚未由本批证明。

空间估计实际只使用固定剖面的 C¹、闭域紧性/凸性及正 q；ρ 的负性、q 的时间导数/周期条件和 |τ|≤τ_* 不参与这一步。公开声明允许全部实 τ，不意味着改变原 allowed 权族或已完成更广时间分析；它对原族的每一项均成立，且常数不依赖 τ_*。ρ 可由已有 ofContinuousOn 在紧闭域上构成真实 SpatialProfile，未增加域外可测、光滑或有界要求。最终类型保留 `IsFiniteMeasure(volume.restrict S)`，原有界域供应此实例，不构成新的数学限制。

## 从实际 C¹ 导数到空间比较

UniqueDiffOn 不是新增未证明前提。若开凸 S 非空，S=interior S 且 S⊆closure S 给 interior(closure S) 非空，closure S 又凸，故固定 mathlib 的 `uniqueDiffOn_convex` 适用。若 S=∅，其闭包为空，UniqueDiffOn 直接为空集命题。没有从空域选择点，也没有隐含正维条件。

已读取固定 mathlib 的真实凸域均值定理与唯一微分定理。`exists_profile_derivative_bound` 对各阶实际 iteratedFDerivWithin 使用 ContDiffOn 的导数连续性和紧集有界性，再以有限和选出 L≥1；本次 n=1。UniqueDiffOn 使一阶 iteratedFDerivWithin 范数准确识别为 fderivWithin 范数，而不是任意候选导数。`ContDiffOn ℝ 1` 给 DifferentiableOn；凸域均值定理在闭包内线段上产生 |ρ(x)−ρ(y)|≤L dist(x,y)。调用端点 hy、hx 的次序得到所需 x−y 方向，实数绝对值和距离转换准确。

这一 L 只由固定 S、ρ 及其真实 C¹ 数据选择；没有输入 σ 的 Lipschitz 界或目标权比较，没有依赖 q、τ、网格或时刻。边界点使用的就是 hρ 所规定的真实闭域 C¹ 代表；SpatialProfile 虽然只要求域内 a.e. 数据，最终 hρ 额外明确约束其同一 value 函数在整个 closure S 上的正则性，没有把任意 Lp 代表当成连续代表。

对于 q>0，q^τ>0，故实际比值精确为 exp(η(a−b)q)。|η|=1 给 −D≤η(a−b)≤D，乘以正 q 再用 exp 单调性得两个指数界。第 3–4 项没有 τ 的估计损失，也没有用随 q 增长的粗乘子范数替代空间比较。

scaled 的函数恰为 ηρ；η=1、−1 的两个结构等式和实际 multiplier 公式分别识别 θ、θ⁻¹。原 σ 的逆也在相同族中，对应指数 −τ 和相反 η，故没有遗漏反权方向。严格正性适用于所有点，归一化点位于边界也不需要从 a.e. 正性非法推出点态正性。

## 真实直径、原指数形式与 hqmax

cellDiameter 是实际单元凸包的 Metric.diam。证明距离受直径控制时实际调用单纯形紧性给有界性，因此没有误用 Metric.diam 在无界集合上的约定。maxDiameter 是非负实数直径的有限 supremum；每个单元的直径都在其中，空索引的 supremum 为 NNReal 的底元 0，正确对应空网格扩展。

对 x,y∈K，inside 仅给它们属于 closure S，代码正是在 closure S 上使用剖面比较，没有把闭单元顶点错误放入开域 S。随后得到 |ρ(x)−ρ(y)|≤L diam K。将此代入第 4 项，得到真实比值上下界 exp(±L diam(K) q)，再由 diam K≤h 和 q≥0 得原文 exp(±Lhq) 形式。该精确指数界由已证通用比值定理与直径/Lipschitz 结论组合；专门的第 19 项则在 hq≤1 下把它收敛为用于逆估计的统一常数 exp L。

第 19 项对任意单元内 x,y 都成立，不只是预选中心或几乎处处内点；其下比较也通过交换 x,y 的同一上比较得到，保留相同常数。D=L diam K 非负；h q≤1 通过正 q 与直径上界给 diam K·q≤1，再乘 L≥0，指数比较方向正确。

第 18 项以 TimeWeight.upper 的实际 q(t)≤w.max 和 h≥0 给 hq(t)≤δ，对所有实 t 成立。最终主定理显式输入的是固定时刻的 hq(t)≤1；若原条件为 hqmax≤δ_num≤1，先用第 18 项，再与 δ_num≤1 传递，即可在全部时刻用同一个 C 应用主定理。这里并未把 qmax 偷换成精确最大值，原文也仅要求它是上界。q 的周期延拓、节点 t_n 或时间区间长度都不会改变 C，故具有所需 T 统一性。

## 原 ℓ 尺度与真实全域范数

原形状假设 diam K≤κr_K 与原上比较 ℓ_K≤B diam K 给 ℓ_K≤(Bκ)r_K。B>0 使不等式可乘，κ>0 使传给已证全域定理的形状参数 Bκ 正；实际内球包含和 r_K、ℓ_K 正性原封不动传入。这里选择依赖中的尺度参数为 ℓ_K，直接得到右侧 ℓ_K⁻¹，而非先错误地把最大 h 代替局部 ℓ_K。

已直接读取 CellwiseInverseWeight 的实际构造：inverseScale ℓ 的 value 是有限和 Σ_K1_Kℓ_K⁻¹，inverseWeight 是它与 σ 的实际点态乘积。共享面上可能有多重值，但真实分区定理在域测度下给 a.e. 唯一单元，故 a.e. 值正是 ℓ_K⁻¹σ。用于有界乘子合法性的粗界 Σ_K|ℓ_K⁻¹| 不进入最终 C，因此没有单元数或最小尺寸依赖。

第 20 项取实际第零顶点 x_K∈K，s_K=σ(x_K)>0；第 19 项对完整单元点态成立，经真实 cell 可测性和 ae_restrict_mem 转成单元测度下的双边比较。无须节点位于 S 内部，无须状态具有点值。这个节点值只属于已定义的正光滑权，不属于任意 L² 状态。

传入 `conforming_weighted_inverse` 的 W=exp L，形状参数为 Bκ。这两个数在网格、权和状态之前已经固定。该依赖逐单元将实际全梯度积分控制为 (C/ℓ_K)² 倍真实状态积分，使用精确 a.e. 分区积分求和，再以 inverseWeight_sq_sum 恢复实际右范数。两侧非负才从平方界返回范数界。没有漏掉平方、体积或单元 multiplicity，也没有通过三角不等式引入网格数量因子。

## 完整 H¹ 一致 P1 状态及真实梯度

已直接检查 T048/T049 的本次调用链，而非仅继承其验收标签。conformingSpace 的双向成员刻画是实际 V 与逐单元 a.e. 仿射多项式空间的交；它不是节点插值像的子空间。最终量化任意 V 和任意真实 WeakSobolevJet d 1，只要求其 value 属于这个完整空间。

局部多项式由空间成员取出实际坐标系数后构造 AffineMap。同一全局 jet 通过真正 subdomainLp 限制到单元内部，原全部 SpatialTest 的弱身份保留；仿射函数的真实 CLM 导数由 Lipschitz 积分分部成为弱导数，完整测试族唯一性识别已有弱梯度，再利用单元边界零测扩回整个闭单元。derivativeOneFiber 遍历全部正交坐标且各出现一次，故 field 1 是实际 Euclidean 全梯度 L² 字段。没有另行输入目标局部梯度、光滑状态或有限元测试范围内的弱身份。

对原 V=dirichletSubspace，H¹₀ 定义为真实紧支光滑测试在 H¹ 图范数中的闭包之 value 像；dirichletSubspace_sobolev 给每个成员的真实 jet 见证，开域上的 value_injective 给唯一梯度。因此 jet 形式覆盖原完整 V_h，既不遗漏状态，也不允许为同一标量状态自由选择梯度。没有 H²、节点表示、谱滤波、FaceMatching 或额外边界正则性前提。

全域积分依赖实际单元内部属于开凸 S、闭单元与其内部测度相同，因此闭单元限制测度≤域测度且二重限制精确等于单元测度。乘子密度实际可积，有限和积分合法；未使用不可积 Bochner 积分默认值。空索引时 cover 强制 S=∅，最大直径为零且积分和为空，最终结论仍成立。各辅助定理允许 d=0；但非空零维网格的 diam=0 与最终 ℓ_K>0、ℓ_K≤B diam K 不兼容，所以不将该分支误称为正尺度的非空零维网格实例。

## 常数量词及剩余义务

最终实际展开类型先固定 d、S、开凸/紧闭域数据、有限测度实例、固定 ρ 及 C¹ 数据、κ,B>0，随后存在 C>0；之后才量化索引类型/Fintype、M、全部内球/尺度数据、TimeWeight、τ、t、η、V 和 u。证明中先取得 L，再调用已证 `conforming_weighted_inverse d (Bκ) (exp L)` 选 C。C 因而只依赖固定域/ρ、维数和形状/尺度比较常数；不依赖网格、节点数、ℓ_min、qmax、τ、符号、时刻、时间长度或状态。它也不使用 SpatialProfile/BoundedMultiplier 的随 q 增长的粗有界常数。

本阶段可以接受原单元比较与完整 allowed 加权逆界这两个证明步骤已完成。尚未完成相邻单元的四类权 grading 比较及 DST 加权 L² 投影稳定性、H² 节点代表与局部 h/h² 插值误差、超逼近、原 Proposition 6.1 的全部 N3/N4 等数值条件、椭圆正则性或连续热 CE。故 C066 保持 AUXILIARY，P011/P012/P014/P015 等完整原文结果不因此提升，原文计数保持 12/26。

## 固定版本、构建与递归公理

四新模块的 Carleman 导入闭包共 92 模块，88 个旧模块相对 base 逐字节不变；固定 Carleman.lean 显式导入全部四模块。20 项与固定 C066/T050、源码及交付 JSON 清单一致。已读取 [T048 完整局部弱梯度验收](T048-local-acceptance.md)、[T049 全域逆界验收](T049-local-acceptance.md)，并直接检查上述实际依赖的使用。

原稿、治理协议、阶段/覆盖文件、工具链 pin 和两 CI 工作流相对 base 未变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本机 mathlib HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，工作树干净，Lean pin 为 4.35.0。已读取固定 mathlib 的凸域真实微分与均值定理、有限 supremum 的空集/上界约定。

固定 CheckAxioms 对 20 项逐一 `#check @...` 和 `#print axioms ...`，然后用 privateToUserName 遍历所有 Carleman 公开/私有声明并递归 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。实际完整类型已逐项阅读，无隐藏目标权比较、局部逆估计或完整状态限制；20 项递归公理集合均恰为这三项正常基础公理。

固定本机 `/tmp/carleman-allowed-inverse-local-axioms.txt` 为 1,326,820 bytes，SHA256 `52fc8b474e148cff082d91556b5a09fb1e4fe588216373a532b9ec25815d2a73`，末行 `Axiom audit passed for all 4757 Carleman declarations.`。实际 `/tmp/carleman-allowed-inverse-full.log` 包含 `Build completed successfully (3596 jobs).` 和同一全局审计 PASS，没有 sorryAx 或未批准数学公理。

已独立通过 GitHub connector 核实 [main CI 39160957782 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39160957782/attempts/1)：head_sha 为 `9ea552502177ccffb3f50593567578fc207c2568`，main/push，顶层 completed/success。`lean`（117773970202）、`state-check`（117773970374）、`dashboard / snapshot`（117774840082）三个 jobs 均 completed/success；Lean pin、证明构建、记录 checked source 及上传两份原始证据步骤均成功，最终缓存收尾亦已完成。

同 run 的 `lean-ci-result` artifact 12148812397 和 `lean-declaration-evidence` artifact 12149061420 元数据均绑定同一固定 SHA。实际读取 `/tmp/carleman-allowed-inverse-main-ci/result.json`：status PASS，checked_sha=source_head_sha=`9ea552502177ccffb3f50593567578fc207c2568`，ci_url 精确对应上述 run/attempt，finished_at=`2026-10-18T19:58:04.716584+00:00`，target 为 Carleman，Lean 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）与 mathlib pin 均与固定源码一致。

实际 `/tmp/carleman-allowed-inverse-main-axioms/axioms.txt` 与固定本机副本独立逐字节比较，完全相同：1,326,820 bytes，SHA256 `52fc8b474e148cff082d91556b5a09fb1e4fe588216373a532b9ec25815d2a73`。逐名复核远端全部 20 项实际展开类型及公理集合，均恰为上述三项标准基础公理，末行确认全部 4757 项审计 PASS。没有混用后续工作树、其他 SHA 或其他 run 的证据。

## 验收决定

**C066：PASS，可升级为 REVIEWED，scope 保持 AUXILIARY。** 20 项未发现需修复的数学、实际类型、边界代表、权族、尺度、完整状态或常数量词缺陷；固定版本语义、展开类型、公理和同 SHA 三项 CI 均已独立核实。接受范围仅为上述两个已完成的证明步骤，原完整 Proposition 6.1 及其他原文覆盖仍未完成，计数保持 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
