# T043 / C059 独立本机验收

- `checked_sha`: `28e1f4df08f31b4337f32bd20b61dbe566762f15`
- `base_commit`: `0df65a77f4a13fdab4641c30a3843f02bd8b1af8`
- `semantic_checked_at`: `2026-10-18T19:01:36+00:00`
- `reviewed_at`: `2026-10-18T19:06:13+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 范围：**AUXILIARY**。只接受实际节点函数内缩序列在完整 H¹ 图拓扑中的强收敛；不接受尚未证明的光滑卷积 H¹ 逼近或最终 H₀¹ 成员资格。原文完成计数保持 12/26，不提升 P011/P012 或任何其他完整原文覆盖。

独立读取固定提交四个新模块、18 项实际完整类型、公理产物、相关既有依赖及原 `paper/main.tex` Section 6。执行者分析用于定位范围，没有替代实际数学核查；后续未提交模块不作为本次证据。

## 全部 18 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。表中 PASS 是逐项语义结论。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `lp_two_norm_sub_sq_integral` | `LpDominatedLimit.lean:16` | PASS；任意 NormedAddCommGroup 值的真实 Lp 差范数平方等于代表差模平方的积分，无内积假设。 |
| 2 | `lp_two_tendsto_of_dominated_norm_sq` | `LpDominatedLimit.lean:28` | PASS；实际平方差的可积支配与 a.e. 点态极限推出 Lp 范数强收敛，正确通过平方根回到差范数。 |
| 3 | `lp_two_tendsto_of_bounded_support` | `LpDominatedLimit.lean:50` | PASS；共同有限测度支撑与统一 B 界供应可积支配 `1_K(2B)²`。 |
| 4 | `firstOrderFields_tendsto` | `CompactLipschitzLimit.lean:14` | PASS；真实标量和 CLM 导数场的两个强 L2 极限经实际连续字段映射进入全部一阶 jet 字段。 |
| 5 | `compactLipschitzSobolevJet_tendsto` | `CompactLipschitzLimit.lean:27` | PASS；共同紧支、统一函数/Lipschitz 界及实际 fderiv 的 a.e. 极限供应完整 H¹ jet 极限。 |
| 6 | `inwardRatio` | `ContractionSequence.lean:14` | PASS；实际序列 `(1+n)/(2+n)`，从 n=0 起定义。 |
| 7 | `inwardRatio_pos` | `ContractionSequence.lean:16` | PASS；每项严格为正，所有逆映射合法。 |
| 8 | `inwardRatio_lt_one` | `ContractionSequence.lean:20` | PASS；每项严格小于 1，确为支撑向内收缩。 |
| 9 | `inwardRatio_half_le` | `ContractionSequence.lean:25` | PASS；所有 n 均≥1/2，含首项等号。 |
| 10 | `inwardRatio_inv_le_two` | `ContractionSequence.lean:31` | PASS；所有 n 的正倒数≤2，无最终才成立的遗漏。 |
| 11 | `inwardRatio_tendsto` | `ContractionSequence.lean:35` | PASS；真实有理式序列趋于 1。 |
| 12 | `inverse_inward_tendsto` | `ContractionSequence.lean:40` | PASS；实际逆像点 `a+r_n⁻¹(x−a)` 对每个 a,x 趋于 x。 |
| 13 | `inwardFunction_tendsto` | `ContractionSequence.lean:49` | PASS；连续 f 与真实逆映射复合的逐点极限为 f(x)。 |
| 14 | `inward_fderiv_tendsto_of_local_affine` | `ContractionSequence.lean:54` | PASS；邻域上同一个真实导数 A 的条件给最终精确链式公式 `r_n⁻¹ • A`，再趋于原 fderiv。 |
| 15 | `SimplicialPartition.nodal_inward_fderiv_tendsto_ae` | `ContractionSequence.lean:76` | PASS；有限零测骨架外，单元内部局部仿射或闭包外局部为零覆盖 volume-a.e. 点。 |
| 16 | `SimplicialPartition.closure_isCompact` | `NodalContractionLimit.lean:15` | PASS；真实有限紧单元覆盖闭包，未额外假定未知支撑集合紧。 |
| 17 | `SimplicialPartition.nodalCompactJet_eq` | `NodalContractionLimit.lean:19` | PASS；同一实际 L2 值及完整弱 jet 唯一性识别两个构造出的全空间节点 H¹ jet。 |
| 18 | `SimplicialPartition.nodal_inward_tendsto_H1` | `NodalContractionLimit.lean:29` | PASS；内部供应共同紧支、函数 B 界、2C 导数界和两类点态极限，结论为实际原 nodalGlobalSobolevJet 的完整图拓扑极限。 |

## 原文映射与范围

原 `paper/main.tex:1469–1485` 对有界凸多面体上的一致 P1 空间取 `V_h={v∈H₀¹(Ω):v|K∈P₁}`；`1634–1658` 对盒子上的 FD 实现使用零边界节点和 Kuhn 分片仿射重构。本阶段服务于这些真实节点函数进入 H₀¹ 闭包的证明路线，清偿其中“先向内收缩，再令收缩比趋于 1”的 H¹ 极限步骤。它不是原 Proposition 6.1/6.2 的完整形式化，也未完成该路线的全部 H₀¹ 证明。

最终声明仍显式要求开凸 S、实际有限 SimplicialPartition、FaceMatching、BoundaryFitted、边界顶点值为零和中心 a∈S。这些是当前内缩路线的几何输入，符合原凸多面体/盒子的目标范围；代码没有从形状正则性或 grading 自动构造这些输入。a∈S 排除了本入口的空域情形；空域零函数应在最终 H₀¹ 总命题中单独处理，当前结论没有声称覆盖它。

## 一般范数值 Lp 的平方积分与主导收敛

已逐项核对实际类型：第 1–3 项只要求目标 E 为 NormedAddCommGroup，不要求实向量结构、内积空间或 Hilbert 结构。这一点使它们可直接用于真实导数所在的连续线性映射空间及其算子范数。μ 是一般测度；没有要求总测度有限。

第 1 项展开实际 Lp.norm_def、eLpNorm 的实值和 p=2 的积分公式，得到 `‖u−v‖=sqrt(∫‖(u−v)(x)‖²)`。u−v 本身属于 Lp；不存在把不可积表达的默认积分值当成范数的情况。非负平方积分允许 `sq_sqrt`，再以 `Lp.coeFn_sub` 的 a.e. 身份将 Lp 差的代表换成两个代表之差。整个论证没有误用 L2 内积的平方范数公式。

第 2 项的实际支配假设为 `∀n,∀ᵐx,‖u_n(x)−v(x)‖²≤b(x)`，另有 b 可积及共同 a.e. 点态极限。被积函数强可测性来自真实 Lp 代表之差、模与平方；平方非负使其绝对值支配与给定上界一致。主导收敛首先给平方差积分趋于 0，继而使用连续平方根和非负范数将其变为差范数趋于 0，最后得到 Lp 的范数拓扑收敛，没有只得到弱收敛或逐点收敛。

第 3 项中 K 可测且 μK<∞，B≥0。K 内的三角不等式给差模≤2B，平方后由 `1_K(2B)²` 支配；K 外两个代表都为零。该 indicator 常数函数通过真实有限测度支撑的 MemLp/Integrable 定理证明可积。没有要求整个空间有限测度，也没有遗漏极限 v 的同一支撑和 B 界。

## 实际导数场、共同 a.e. 代表与 H¹ 图拓扑

已直接追查 `CompactLipschitzSobolev`：标量 Lp 类来自真实紧支 Lipschitz 函数，导数 Lp 类来自 `fderiv ℝ f` 本身。其可测性由 measurable_fderiv 给出，范数由真实 Lipschitz 常数控制，支撑外导数为零；没有输入自由命名的梯度。Rademacher 的 a.e. 可微性将这个实际 fderiv 识别为 HasFDerivAt，再由已证全测试族的 Lipschitz 积分分部构造真正的弱 H¹ jet。

通用极限定理分别调用第 3 项处理标量值与 CLM 值导数场。紧 K 给可测性和有限 Lebesgue 测度；函数由 B 支配，fderiv 的算子范数由统一 Lipschitz 上界 L 支配，K 外两者均为零。对每类 Lp 代表，代码以 `ae_all_iff` 将全部自然数 n 的 a.e. 身份汇合到同一个 a.e. 集，再与极限代表和导数极限条件相交。因而没有在各 n 不同异常集上直接非法推导点态序列极限。

`firstOrderFields_tendsto` 使用 scalarZeroFiber 和 derivativeOneFiber 的实际连续 Lp 映射。前者是真实零阶值，后者在 `Sym (Fin d) 1` 的每个指标读取真实 CLM 在对应坐标单位向量上的值。随后在 Fin 2 的完整乘积拓扑逐项证明收敛，最后由 subtype 拓扑得到 WeakSobolevJet 的收敛。既有 `SobolevHilbert.jetEquiv` 将该有限 L2 图拓扑与平方和 H¹ Hilbert 拓扑双向连续识别。因此结论包含值和全部一阶弱导数的强 L2 收敛，没有用单独标量 L2 极限冒充 H¹。

CLM 算子范数到完整坐标 fiber 的连续映射只在固定有限维 d 上使用；本阶段没有据此声称维数统一的估计或数值误差常数。H¹ 强极限所需的连续性足够，未遗漏这一转换。

## 收缩方向、导数链式公式与零测骨架

实际同胚为 `H_r(x)=a+r(x−a)`，函数收缩定义为 `f∘H_r⁻¹`；其支撑是 H_r 作用于原支撑的像，因此 r∈(0,1) 确实收缩支撑。逆像点为 `a+r⁻¹(x−a)`，没有把内缩和外扩写反。序列 r_n=(n+1)/(n+2) 对全部 n 满足 1/2≤r_n<1、r_n>0 和 r_n⁻¹≤2，并趋于 1。

第 14 项的公开前提是在 x 的一个邻域内，每个点 y 都有同一个实际 Fréchet 导数 A。逆像点趋于 x，因此最终落在此邻域；链式导数准确为 `A.comp(r_n⁻¹ • id)=r_n⁻¹ • A`。同时该邻域条件在 x 自身成立，故 `fderiv f x=A`，而 r_n⁻¹→1 给算子范数中的导数极限。这里没有从一般 Lipschitz 函数 a.e. 可微误推导数连续。

对节点函数，有限个真实凸单元的 frontier 均通过已有凸集 Lebesgue 边界零测定理证明为零测。将其共同排除后：若 x∈closure S，由真实 `cells_union` 覆盖选到某个单元，且 x 非该单元 frontier，故位于其内部，函数在整个内部邻域就是同一仿射局部函数；若 x∉closure S，闭包补集是开集，节点零延拓在该邻域恒为零。两种情形覆盖全空间的共同 a.e. 集，直接供应第 14 项前提。

不需要另行证明每个收缩骨架的并集零测：对于所选 x，其逆像点最终留在原同一内部/外部邻域，便足以保证从某项起的链式公式。有限个早期项不影响极限。这个导数 a.e. 引理本身无需边界零值或全局连续性，因为它只讨论骨架外实际导数；最终 H¹ 入口另外显式供应边界匹配、零值和全局 Lipschitz 性，未因此跨越跳跃函数的弱导数障碍。

## 最终组合、状态范围与常数

已直接追查 SimplicialPartition：单元为真实非退化 d-simplex 的凸包，有限族覆盖 S、包含在 closure S 内且内部两两不交；由有限闭单元覆盖得到其并集恰为 closure S。因此 closure_isCompact 内部证明了共同支撑紧性。FaceMatching 将公共部分限制在公共顶点凸包中，BoundaryFitted 将单元边界部分限制在边界顶点凸包中；给定的真实节点值 f 在边界顶点为零，既有构造保证零延拓的全局连续和 Lipschitz 性。

原节点函数的 Lipschitz 常数是实际有限和 `C=Σ_i‖localNodalDerivative_i‖`。它可依赖网格和节点值，本阶段只用它证明固定函数的成员与收敛，没有将其作为原数值条件中的网格统一逆估计。内缩函数的 Lipschitz 常数为 C|r_n⁻¹|≤2C；原函数也被 2C 控制，C=0 时仍合法。对原紧支连续函数选出的全局 B 界，全部复合函数自动保留；B 非负由一个真实函数值的非负范数推出，没有正 B 或除以 B 的隐含要求。

开凸性与 a∈S 保证每个内缩支撑紧含于 S，因而所有支撑共同位于固定 closure S 中。这里的共同紧集不随 n 改变；既有每个内缩的边界 buffer 可以随 n 缩小，证明没有假设一个对全部 n 统一的正 buffer。

`nodalCompactJet_eq` 将通用紧支 Lipschitz 构造的 jet 与原 `nodalGlobalSobolevJet` 以实际 L2 值身份和完整弱导数唯一性严格相等，未仅在零阶值上作命名替换。最终定理逐项内部供应通用极限定理的所有前提，真实输出位于 `WeakSobolevJet d 1 volume Set.univ`，即原节点零延拓的全空间 H¹ 图拓扑。函数 f 的非节点值不会被当作额外正则输入：实际 nodalFunction 只由顶点值与真实局部仿射插值决定。

本阶段没有 T、时间方向、权或数值误差参数；B、C、K 固定于当前域、网格和节点状态，统一于序列 n。这不等同于原网格族或所有状态之间的统一误差/控制常数。所有 n 从 0 起覆盖，未丢掉首项；最终 a∈S 是明确非空域限制，不可隐去后宣称空域也已由此入口处理。

## 未清偿项

每个紧含于 S 的内缩函数仍须以真正 C_c∞(S) 在 H¹ 中逼近，然后借 H₀¹ 闭性传回原节点函数。当前报告不把已有支撑 buffer、全空间 H¹ 成员或本次 H¹ 极限等同于这一步。最终节点 H₀¹ 成员资格、空域分支、H² 正则性及点值代表、具体网格误差和连续热 CE 均不由本阶段自动完成；原文完整覆盖保持 12/26。

## 固定依赖、构建和递归公理

四个新模块的 Carleman 导入闭包共 54 个模块，50 个既有模块相对 base 逐字节未变。全部新模块在固定 `Carleman.lean` 中显式导入。原稿、工具链 pin 和两个 CI 工作流相对 base 未变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

18 项清单与固定 C059/T043、源码及显式审计声明逐项一致，实际完整类型没有新增目标 H¹ 收敛、H₀¹ 成员或梯度识别前提。固定 `/tmp/carleman-contraction-limit-local-axioms.txt` 为 1,263,477 bytes，SHA256 为 `8573cbb048a860b2ca6d566ec9e74761386748e02ca858972d1007e3db45a220`；18/18 的递归依赖仅为正常基础公理 `propext`、`Classical.choice`、`Quot.sound`，末行为 `Axiom audit passed for all 4527 Carleman declarations.`。

审计脚本遍历所有经 privateToUserName 归属 Carleman 的公开/私有声明，用 collectAxioms 递归收集依赖，仅允许上述三项基础公理。没有 sorryAx 或新数学公理。实际 `/tmp/carleman-contraction-limit-full.log` 记录 `Build completed successfully (3570 jobs).` 及随后完整公理审计 PASS；固定工具链 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

已独立通过 GitHub connector 核对 [main CI 39156717401 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39156717401/attempts/1)：main/push，`head_sha=28e1f4df08f31b4337f32bd20b61dbe566762f15`，completed/success。实际三个 jobs 全部 success：lean（117761351058）、state-check（117761351250）、dashboard / snapshot（117762112681）。Lean 的证明目标构建、checked-source 记录和声明公理上传步骤亦 success。

同次 artifact 元数据确认 `lean-ci-result`（12147695513）和 `lean-declaration-evidence`（12147242592）均绑定该 run 和本次固定 head SHA。实际读取 `/tmp/carleman-contraction-limit-main-ci/result.json`：status=PASS，`checked_sha=source_head_sha=28e1f4df08f31b4337f32bd20b61dbe566762f15`，target=Carleman，`finished_at=2026-10-18T19:02:24.575002+00:00`，CI URL 对应上述 attempt 1。Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 与固定源码一致。

正式 `/tmp/carleman-contraction-limit-main-axioms/axioms.txt` 为 1,263,477 bytes，SHA256 为 `8573cbb048a860b2ca6d566ec9e74761386748e02ca858972d1007e3db45a220`，与固定本机副本逐字节相同。另行检查远端 18/18 项完整类型及递归公理列表，均只有上述三项正常基础公理，实际末行确认全部 4527 项审计 PASS。未使用后续源码、另一 SHA 或执行者概述替代这些实际证据。

## 验收决定

**C059：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 18 项未发现需修复的数学、代表、类型、量词、常数或范围缺陷；同 SHA 实际 CI、完整类型和递归公理证据已齐备。仅接受本报告所述内缩 H¹ 极限；光滑逼近与最终 H₀¹ 成员仍待，不得提升任何完整原文覆盖，完成计数保持 12/26。

本次仅写本报告，未修改数学源码、台账、root 导入、原稿或覆盖表，未 commit/push。
