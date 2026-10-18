# T055 / C071 独立本机验收

- `checked_sha`: `7815f431a2674c214a51368d1383b7deeb9eed40`
- `base_commit`: `cbea02af04b947ec6f1b1c6e3cfb0da5bd65e5a7`
- `semantic_checked_at`: `2026-10-18T20:35:33+00:00`
- `reviewed_at`: `2026-10-18T20:38:43+00:00`
- `result`: **PASS**。
- `axiom_check`: **PASS**。
- 范围：**AUXILIARY**。完成实际共享节点权、原四类权的统一节点比较、零边界节点测试成员关系及节点状态的全域质量下界。完整 V_h 节点表示、加权状态/测试范数比较及最终投影稳定性仍待，不提升完整原文覆盖，完成计数保持 12/26。

本报告直接读取固定 Git 源码、全部 16 项实际完整类型、相关依赖及递归公理产物，并对照原 `paper/main.tex` 和 `governance/analysis/T055-uniform-nodal-weights.md`。执行者说明及先前报告没有替代实际证明检查；后续工作树草稿不参与本次验收。

## 全部 16 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `SimplicialPartition.incidentCells` | `NodalWeightMinimum.lean:13` | PASS；按真实几何顶点相等定义有限相邻单元集合。 |
| 2 | `SimplicialPartition.mem_incidentCells` | `NodalWeightMinimum.lean:17` | PASS；成员准确等价于该点是单元某个顶点。 |
| 3 | `SimplicialPartition.nodalWeightMinimum` | `NodalWeightMinimum.lean:22` | PASS；非空相邻集合取真正有限最小值，其余点取 1；同一几何点只有一个值。 |
| 4 | `SimplicialPartition.nodalWeightMinimum_pos` | `NodalWeightMinimum.lean:26` | PASS；正单元权给所有点上严格正的节点权，包括非顶点分支。 |
| 5 | `SimplicialPartition.nodalWeightMinimum_vertex_bounds` | `NodalWeightMinimum.lean:35` | PASS；真实共享顶点和正 θ 给 aᵢ/θ≤ω≤aᵢ。 |
| 6 | `SimplicialPartition.nodalWeightMinimum_local_ratio` | `NodalWeightMinimum.lean:50` | PASS；同单元任意两顶点之比至多 θ，没有扩大到 θ²。 |
| 7 | `SimplicialPartition.gradedCellWeight` | `AllowedCellWeight.lean:13` | PASS；实际光滑权在本单元 0 号顶点的值乘明确因子 1 或 ℓᵢ⁻¹。 |
| 8 | `SimplicialPartition.gradedCellWeight_pos` | `AllowedCellWeight.lean:18` | PASS；真实 q 正性、实幂和指数正性、ℓᵢ>0 给样本严格正。 |
| 9 | `SimplicialPartition.allowedWeight_scaled_neighbor_le` | `AllowedCellWeight.lean:24` | PASS；真实邻接点距离、profile Lipschitz 界与正因子分级给 γ exp(2Lhq) 比较。 |
| 10 | `SimplicialPartition.sizeWeightFactor_grading` | `AllowedCellWeight.lean:43` | PASS；正尺度除法方向正确，原 ℓⱼ≤γℓᵢ 给 ℓᵢ⁻¹≤γℓⱼ⁻¹；无逆尺度时用 1≤γ。 |
| 11 | `SimplicialPartition.gradedCellWeight_neighbor_le` | `AllowedCellWeight.lean:54` | PASS；将真实两个样本顶点代入邻接比较，保持同一 γ exp(2Lhq)。 |
| 12 | `SimplicialPartition.gradedCellWeight_compare` | `AllowedCellWeight.lean:70` | PASS；真实分片权仅按单元 a.e. 身份替换为单元因子，得到与样本的双向比较。 |
| 13 | `allowed_weights_uniform_nodal_weights` | `UniformNodalWeight.lean:10` | PASS；固定 profile 与原 γ<Γ_d 内部选统一 δ，准确输出 θ=(γ+Γ_d)/2、正节点权及两组实际比较。 |
| 14 | `SimplicialPartition.nodal_squared_weight_test_mem` | `NodalWeightedTest.lean:16` | PASS；ω²f 保持零边界节点，真实 nodalLp 测试属于 H¹₀ 一致 P1 空间。 |
| 15 | `SimplicialPartition.nodal_weighted_mass_coercive` | `NodalWeightedTest.lean:25` | PASS；真实局部质量下界以精确体积因子求和为全域 nodalFunction 乘积积分。 |
| 16 | `SimplicialPartition.nodal_weighted_pairing_coercive` | `NodalWeightedTest.lean:61` | PASS；真实可积节点函数的乘积积分精确识别为两个 nodalLp 的 L² 内积。 |

## 原文映射及当前状态范围

原 `paper/main.tex:1465–1485` 的 Section 6.1 给定真实一致质量空间、共享顶点的尺度分级及原 `Γ_d=(sqrt(d+2)+1)/(sqrt(d+2)−1)`。`paper/main.tex:1506–1521` 的 Step 1 处理 σ、σ⁻¹、ℓ⁻¹σ、ℓ⁻¹σ⁻¹ 四类权，并以 hq_max≤δ_num 把有效邻接分级压到 `(γ+Γ_d)/2<Γ_d`，再得到 `eq:p1-weighted-projection`。

本批是朝该投影稳定性目标的构造步骤。它提供由真实 allowed 权生成的共享节点权、实际 H¹₀ 节点测试，以及节点状态和测试之间的全域质量下界。最后两个声明的状态明确是 `M.nodalLp … f`，没有改写成任意完整 `M.conformingSpace (dirichletSubspace S)` 成员；本批也没有证明这两个空间相等。因此不得据此声称已经覆盖完整 V_h 上的投影估计。

零边界测试成员声明要求真实 FaceMatching、BoundaryFitted 和边界节点 f=0，符合原 conforming boundary-fitted 网格的节点构造。质量下界本身只需要 FaceMatching，不要求边界条件；这是适用范围的扩大。它们没有预设待证的加权投影估计、节点表示逆命题或状态/测试范数比较。原 H² 插值、超逼近及其他 P1/连续分析义务仍不在本批结论中。

## 几何顶点最小值与精确局部比值

`incidentCells x` 检查 `(M.simplex i).points k=x` 的真实点相等；它不是仅按局部编号聚合，也不是对全部几何邻域取样。同一个几何顶点出现在不同单元时，传入同一个 x，故得到同一个有限集合和同一个 ω(x)。空集合分支设为 1 只处理非顶点及空网格，不改变实际节点值；有限非空集合上的真正最小值保留严格正性。

对 Kᵢ 的任意顶点 x，i 本身属于 incidentCells x，故 ω(x)≤aᵢ。对集合内每个 j，x 同时是 Kᵢ、Kⱼ 的顶点，实际 `VertexNeighbors i j` 给 aᵢ≤θaⱼ；正 θ 可除，所有候选都不小于 aᵢ/θ，故最小值也不小于该数。同单元的两个顶点因此满足 ω(x)≤aᵢ≤θω(y)。没有先对两个顶点各使用一次邻接比值造成 θ²。

局部强制性使用归一化 aᵢ/γ>0，节点上界恰为 aᵢ=γ(aᵢ/γ)。用于原 allowed 权时须将此参数 γ 实例化为有效 θ；相应下界系数是 μ(d,θ)，不是 μ(d,原 mesh γ)。节点与实际空间权之间经样本传递可能出现额外比较因子，但该因子不会被误用为节点间分级阈值；本批尚未断言最终加权范数比较。

## 四类实际权与边界样本

`gradedCellWeight` 定义 `aᵢ=bᵢ σ(vᵢ₀)`，bᵢ 为 1 或 ℓᵢ⁻¹，σ 的真实函数为 `q(t)^τ exp(ηρ(x)q(t))`。样本使用明确单元 i 的 bᵢ，没有求值全域 `inverseScale` 在共享顶点的 indicator 和。因此即使共享边界处分片乘子有多个单元贡献，也不影响样本定义。有限函数的实际点值可合法用于此处；没有对 L² 等价类作节点点值。

q(t)>0 保证任意实 τ 的 q(t)^τ 正，指数也始终正；ℓᵢ>0 给逆尺度正。η 的 |η|=1 覆盖两符号。已核对依赖中的 `scaled_multiplier_inverse_value`：倒数同时改变 τ→−τ、η→−η，所以该族准确包括 σ⁻¹，结合 Bool 因子覆盖原四类权。τ 在空间比较中精确消去，未新增指数区间限制。

真实共享顶点给 dist(x,y)≤diam(Kᵢ)+diam(Kⱼ)≤2h；所有单元包含于 closure S，故 profile 的实际闭域 Lipschitz 界可在两个样本顶点和所有单元点使用。正单元因子的邻接界乘上指数比较得到 γ exp(2Lhq)，其中尺度倒数方向已核对。`gradedCellWeight_compare` 在同单元用两个方向的点态比较，再通过 `gradedWeight_on_cell` 的正确单元限制测度 a.e. 身份得到真实 |ζ(x)| 与 aᵢ 的双向界。没有把单元 a.e. 身份提升为共享顶点处的点态身份。

## 统一 δ、有效 θ 与所有量词

`allowed_weights_uniform_nodal_weights` 的完整类型先固定 d、开凸域 S 及紧 closure、真实 profile ρ 和其闭域 C¹ 性、原 1≤γ<Γ_d，然后才存在 δ>0、δ≤1。δ 之后依次量化索引类型、Fintype、实际网格 M、正尺度 ℓ、其邻接 grading、任意 TimeWeight、τ、时刻 t、η 和 inverseSize。故 δ 不依赖网格大小、单元数、ℓ、q_max、时刻、τ、符号、分片因子选择或 T。

闭域 C¹、紧性和凸性由真实导数界/均值估计内部供应 L≥1。实际阈值依赖使用 `δ=min(1,log((γ+Γ_d)/(2γ))/(2L))`，原严格间隙保证它为正。h q_max≤δ 与 q(t)≤q_max 对所有 t 给 γ exp(2Lh q(t))≤(γ+Γ_d)/2。θ 的定义精确为该中点，且 1≤θ<Γ_d；没有收紧原 γ 范围或另加 T 依赖阈值。输出节点范围和 ζ 与 aᵢ 比较均使用同一 θ。

## 真正的零边界测试与全域质量下界

任意实函数 ω、f 只在有限真实节点上取值，因此本阶段不需要假定 ω 全局连续或可测。f 在边界节点为零则 ω²f 同样为零。`nodal_squared_weight_test_mem` 调用的实际成员定理由真实全局 Lipschitz 节点函数、内缩 H¹ 极限和紧支光滑卷积逼近证明属于 `dirichletJetSpace` 的 H¹ 图范数闭包，再取其 value 为 `dirichletSubspace`；不是以“零边界”命名一个未经证明的空间。FaceMatching 保证公共面局部插值一致，BoundaryFitted 保证边界部分由零值边界节点生成。

质量下界使用既有真正单元积分身份 `∫K p_c p_e=vol(K)/((d+1)(d+2))·[Σcᵢeᵢ+(Σcᵢ)(Σeᵢ)]`。已直接核对该调用、二阶重心坐标矩与置换换元依赖：对角系数为 2、非对角为 1，体积因子是实际 `volume.real K` 且严格正。将 T052 的允许混合符号系数强制性应用于每个单元，节点范围正好满足 γ 与 aᵢ/γ 的归一化条件，未出现 θ² 或额外单元依赖。

`nodalFunction` 在每个闭单元点态等于真实 localNodal 多项式。两节点函数的实际 MemLp 给乘积可积，随后使用真实有限 a.e. 分区的积分等式逐单元求和；共享面零测，未重复计数。全域左边保留每个单元的实际体积因子及加权节点平方和，没有把它预先认定为原加权 L² 范数。最后通过两个实际 MemLp.toLp 的 a.e. 代表身份和真实 L² 内积积分公式得到 `nodal_weighted_pairing_coercive`。

最后两个下界声明只要求 γ≥1，因此在 γ≥Γ_d 时 μ 可能非正，仍是正确不等式。将它称为正强制性时必须接入有效 θ<Γ_d，并有非零节点系数能量；本批没有错误声称任意非零点值函数 f 都给严格正值，因为 f 可以仅在非节点处非零。空域/空索引及零状态未被不当排除，d=0 也被实际类型覆盖。

## 声明版本、构建与递归公理

四个新模块的 Carleman 导入闭包共 146 个模块，其中 142 个既有模块相对 base 逐字节不变；root 明确导入全部四模块。AGENTS、流程规则、原论文、Lean/mathlib pin 和 CI 流程没有在该差异中改变。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-nodal-weights-full.log` 实际包含 `Build completed successfully (3617 jobs).`。固定 `/tmp/carleman-nodal-weights-local-axioms.txt` 中全部 16 项完整类型与源码相符；每项递归公理集合仅包含正常基础公理 `propext`、`Classical.choice`、`Quot.sound`。已核对实际审计程序对全部 Carleman（含内部生成）声明使用递归 `collectAxioms` 并拒绝白名单外项；末行确认全部 4835 项通过。显式打印的 1306 项不同声明的集合扫描也无未许可公理，没有 sorry 或未证明数学公理。

固定本机产物为 1,364,575 bytes，SHA256 `d617867d312929ffa3a5bd51f9bbf121461f743f634d37a2f0835ba13a06efc1`。工具链为 Lean 4.35.0，mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

## 远端证据及最终结论

已独立读取真实 [main/push run 39163863586](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39163863586/attempts/1)、attempt 1，head SHA 精确匹配本次 checked SHA，顶层 completed/success。三项 jobs 均 completed/success：state-check `117782623050`、lean `117782623247`、dashboard / snapshot `117783436575`。Lean job 的实际构建、记录 checked source、上传两项证据及缓存收尾步骤全都 success。

独立核对同次产物元数据：`lean-ci-result` id `12150345520`，`lean-declaration-evidence` id `12150057140`，两者均绑定该 run 和同一 head SHA。已实际读取 `/tmp/carleman-nodal-weights-main-ci/result.json`：status=PASS，checked_sha/source_head_sha 均为 `7815f431a2674c214a51368d1383b7deeb9eed40`，ci_url 精确对应该 run/attempt，finished_at=`2026-10-18T20:36:16.148408+00:00`，target 为 `Carleman`；Lean 4.35.0（commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）及 mathlib pin 均吻合。

已实际读取 `/tmp/carleman-nodal-weights-main-axioms/axioms.txt` 并与固定本机副本逐字节比较：完全相同，1,364,575 bytes，SHA256 `d617867d312929ffa3a5bd51f9bbf121461f743f634d37a2f0835ba13a06efc1`。在远端产物中再次核对全部 16 项完整类型和递归公理集合，均通过，且末行确认全部 4835 项审计通过。

最终结论：**T055 / C071 PASS，可以将 C071 升为 REVIEWED，保留 AUXILIARY。** 本批 16 项声明及所声称范围通过，未发现数学缺陷。完整 V_h 节点表示、加权范数比较和最终投影稳定性仍待，不提升完整原文覆盖，完成计数保持 12/26。本 Agent 仅写本验收报告，未修改证明、台账、root 导入或原稿，未 commit/push。
