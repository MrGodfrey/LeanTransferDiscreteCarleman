# T056 / C072 独立本机验收

- checked_sha: `14bdf0cb11fcc8ac2c51297c2307fb5745ee49b5`
- base_commit: `7815f431a2674c214a51368d1383b7deeb9eed40`
- reviewer: 独立本机数学验收 Agent `/root/accept_spatial_lemma`
- result: `PASS`
- axiom_check: `PASS`
- reviewed_at: `2026-10-18T20:49:09+00:00`
- scope: `AUXILIARY`；保留节点表示及边界节点零值前提的统一加权投影估计。不是原完整 `eq:p1-weighted-projection` / `prop:p1`，原文完成数保持 **12/26**。

## 审查方法与版本

按照仓库 `AGENTS.md`、`governance/PROJECT_OPERATIONS.md` 和 `state/README.md`，直接读取上述固定提交的六个新模块、实际调用的数学依赖、完整声明输出、原论文 Section 6（`paper/main.tex:1468–1520`）及 `governance/analysis/T056-nodal-projection-estimate.md`。没有以执行者说明或 CI 成功替代语义核验。工作树中后续阶段的内容不在本次范围内。

六模块为 `WeightedSimplexMassBound`（4 项）、`NodalWeightedNorm`（6 项）、`WeightedMassAbsorption`（2 项）、`NodalProjectionEstimate`（1 项）、`AllowedReciprocalWeight`（4 项）、`UniformNodalProjection`（1 项），均在 `Carleman/Spatial/` 下。18 项精确匹配固定提交 C072 的 `lean_declarations` 与 `/tmp/carleman-nodal-norms-declarations.json`，均由固定 `Carleman.lean` 导入。递归检查项目 import 闭包，共 152 个源文件；除六个新模块外，既有依赖相对基线没有变化。

固定论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定 `leanprover/lean4:v4.35.0`，mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`；本机实际 mathlib HEAD 与该 pin 相同且工作树干净。

## 全部声明的实际结论

下表名称均为完整 Lean 声明名。逐项核对实际展开类型、证明和递归公理；所有行的数学结论均 PASS，范围按表保留。

| 声明 | 实际数学内容与假设检查 |
| --- | --- |
| `Carleman.weighted_simplexNodal_integrable` | 非退化真实单纯形上的有界乘子平方密度可积。使用实际 `simplexNodalLp` 的 a.e. 代表和乘子密度可积性，没有假设待证积分有限。 |
| `Carleman.weighted_simplexNodal_coefficient_bound` | 若 `B ≥ 0` 且单元 a.e. `|w| ≤ B`，实际加权平方积分至多 `B²(d+2)m_K Σ c_i²`。其中 `m_K = vol(K)/((d+1)(d+2))`，来自真实质量积分上界；积分单调性两侧可积。 |
| `Carleman.weighted_simplex_state_bound` | `θ,a > 0`、`a/θ ≤ ω_i`、`|w| ≤ θa` 推出实际状态平方积分界 `θ⁴(d+2)m_K Σ(ω_i c_i)²`。逐系数平方时先证明相应量非负；不要求系数 `c_i` 非负。 |
| `Carleman.weighted_simplex_test_bound` | `θ,a > 0`、`0 ≤ ω_i ≤ a`、`|w| ≤ θ/a` 推出实际节点测试 `p_(ω²c)` 的平方积分界 `θ²(d+2)m_K Σ(ω_i c_i)²`。严格正 `a` 保证消去 `a²` 合法。 |
| `Carleman.SimplicialPartition.nodalCoefficientEnergy` | 定义真实有限网格能量 `E = Σ_K m_K Σ_i(ω(x_Ki)f(x_Ki))²`；取样对象是实际点值函数 `f`，并非任意 L² 等价类。 |
| `Carleman.SimplicialPartition.nodalCoefficientEnergy_nonneg` | `E ≥ 0`，通过正单元体积因子和平方和；没有不当地断言非零函数必使 E 严格正。 |
| `Carleman.SimplicialPartition.ae_of_cells` | 开凸域中，所有单元上的 a.e. 命题提升为域上 a.e. 命题。使用真实受限测度恒等式、有限 a.e. 合取及真实 a.e. 分区；不是点态边界断言。 |
| `Carleman.SimplicialPartition.nodal_weighted_norm_sq_sum` | `FaceMatching` 下实际 `nodalLp` 的加权 L² 范数平方精确等于单元加权仿射多项式积分之和。明确使用 a.e. 代表、单元测度不超过域测度、单元上节点函数恒等式及分片积分公式。 |
| `Carleman.SimplicialPartition.nodal_weighted_state_bound` | 正单元样本 `a_K`、邻接比较 `a_K ≤ θ a_K'` 和乘子单元上界内部给节点最小权的状态界 `θ⁴(d+2)E`。是全域真实范数，不带单元数因子。 |
| `Carleman.SimplicialPartition.nodal_weighted_test_bound` | 同样的节点最小权，加上乘子上界 `θ/a_K`，内部给真实 `nodalLp(ω²f)` 的测试范数界 `θ²(d+2)E`。没有把节点插值测试换成一般乘积 `ω(x)² z(x)`。 |
| `Carleman.BoundedMultiplier.inner_le_weighted_pair` | 任意测度上的真实有界乘子满足 `wξ=1` a.e. 时，实际 L² 配对等于乘子后的配对，继而 `⟨u,v⟩ ≤ ‖wu‖₂‖ξv‖₂`。对任意真实 L² 状态成立；不需要另加虚构的对偶配对公理。 |
| `Carleman.weighted_mass_norm_absorption` | 在所有范数/能量非负、`μ,θ,D > 0` 和三条明确标量界下推出 `Z ≤ θ³D U/μ`。`E=0` 与 `E>0` 分开，所有平方、消去及除法均有符号依据。此项是辅助吸收而非独立的原文投影结论。 |
| `Carleman.SimplicialPartition.weighted_projection_bound_of_nodal_representation` | 作用于完整 `M.conformingSpace (dirichletSubspace S)` 的真实正交投影。节点测试内部证明属于该完整空间；显式保留投影等于 `nodalLp f` 以及边界节点 `f=0`。在实际互逆权、局部界和 `1≤θ<Γ_d` 下得到 `θ³(d+2)/μ(d,θ)` 的真实投影界。 |
| `Carleman.SimplicialPartition.gradedReciprocalWeight` | 定义真实有界倒数乘子：时间幂 `τ`、空间符号 `η` 同时反号，网格尺度 `ℓ` 取逆；没有将倒数性质放入结构字段。 |
| `Carleman.SimplicialPartition.gradedReciprocalWeight_product_cell` | 在正 `ℓ` 下，原实际权和所构造乘子的乘积在每个单元 a.e. 为 1。使用真实指数/实幂的倒数身份及两个单元代表身份；没有在共享骨架上强求点态选片一致。 |
| `Carleman.SimplicialPartition.gradedReciprocalWeight_product` | 通过 `ae_of_cells` 将上述实际乘积 1 提升为整个域的 a.e. 恒等式。 |
| `Carleman.SimplicialPartition.gradedReciprocalWeight_cell_bound` | 正样本 `a`、真实权下界 `a ≤ θ|ζ|` 和实际互逆身份推出 `|ξ| ≤ θ/a`。乘绝对值及除法符号正确，不是假设最终测试范数。 |
| `Carleman.allowed_weight_projection_of_nodal_representation` | 固定域/profile/原分级常数后先选 `δ,C>0`，再量化全部网格、尺度、时间权、幂、时刻、符号、四类权开关、L² 状态及节点数据。内部供应样本、节点权、比较、互逆乘子和两项范数界；节点表示和零边界节点数据仍显式保留。 |

## 原文对应与实质数学核对

原 Section 6 定义 `V_h = H¹₀(Ω) ∩ {逐单元 P₁}`，使用一致 L² 内积及其正交投影，并在 Step 1 要求四类真实权的统一稳定性。本阶段将真实质量积分、已有节点强制性与正交投影身份连接起来，是这一目标的有效辅助推进；当前还不是对原完整 `V_h` 无额外前提的投影定理。

**真实质量、节点测试和全域范数。** 使用 `SimplexMassIntegral` 中已经证明的实际 Lebesgue 质量积分公式及平方上界，而不是把系数矩阵当作 L² 内积的定义。单元质量因子始终是 `vol(K)/((d+1)(d+2))`；状态界用 `a²Σc² ≤ θ²Σ(ωc)²`，测试界用 `Σ(ω²c)² ≤ a²Σ(ωc)²`，配合两个乘子的 `θa`、`θ/a` 上界，分别得到 θ⁴ 和 θ²。全域证明使用真实积分分片与 a.e. 代表，故不存在人为丢失体积因子、质量集中替代、重叠单元重复计数或网格单元数进入常数的问题。

**强制性和消去。** 实际 `nodal_weighted_pairing_coercive` 给出 `μE ≤ ⟨z,q⟩`，其中 `q = nodalLp(ω²f)`、`μ = p1MassMargin d θ = 1-(d+1)(θ-1)²/(4θ)`。`1≤θ<Γ_d` 内部推出 `μ>0`。通过真实正交投影身份和真实互逆权 Cauchy–Schwarz 得到 `μE≤UT`，而 `Z²≤θ⁴(d+2)E`、`T²≤θ²(d+2)E` 已由前述范数引理内部供应。当 E 为 0 时直接得 Z 为 0；E 正时才消去 E，再利用非负平方比较、除以正 μ。最终常数确为 `θ³(d+2)/μ`，没有非法除以可能为零的状态或测试范数。

**完整投影空间没有被替换。** 展开 `SimplicialPartition.conformingSpace` 和 `mem_conformingSpace_iff`，其成员恰为属于给定 `dirichletSubspace S` 且每个单元 a.e. 等于某仿射多项式的 L² 状态。该空间有限维，因而具有实际 Hilbert 正交投影。证明使用 mathlib 的 `inner_orthogonalProjectionOnto_eq_of_mem_right`，右侧测试由 `nodal_squared_weight_test_mem` 内部证明属于该完整空间。没有投影到较小节点像空间，也没有把最终投影界作前提。

然而 `hproj : Π_X u = nodalLp f` 和 `hf : f 在 frontier S 上的所有网格顶点取零` 确实是额外显式前提。特别是前者是 L² 等价类相等，并不自动给后者的点值边界事实；本阶段没有忽略这一差别。为完成原文无条件投影结论，仍须从完整 H¹₀ 分片仿射空间推出可兼容的全局节点表示及零边界节点值。当前估计对任意满足这些前提的 u、f 成立，而不是只估计某个特选状态。

**实际权倒数。** 对 `ζ=σ`，构造的 ξ 是真实 `σ⁻¹`；对 `ζ=ℓ⁻¹σ`，ξ 是真实 `ℓσ⁻¹`，相反空间符号同理。后者作为测试时的辅助互逆乘子使用，并未宣称它属于论文四类待估权，也没有要求它自动满足原四类权的分级。实际下界 `a_K≤θ|ζ|` 加上乘积 1 直接给所需测试上界。单元到全域的提升仅断言 a.e.；骨架代表的任意选片不影响真实 L² 结论。`TimeWeight` 的正值和正 ℓ 保证倒数存在；本阶段不向零权作无条件推广。

**量词与统一性。** 最终先固定 d、域 S、实际 C¹ profile ρ、`1≤γ<Γ_d`，并选择 `θ=(γ+Γ_d)/2`、`C=θ³(d+2)/μ(d,θ)`。δ 来自真实 profile 导数/Lipschitz 界和严格分级余量；两者均先于索引型、单元集合、所有几何/ℓ 数据、`TimeWeight`、τ、t、η、`inverseSize`、u、f。利用 `maxDiameter*w.max≤δ` 控制所有时刻的 `hq(t)`，没有 qmax、τ、T 或网格进入 C。`|η|=1` 对实数即两个空间符号；τ 全实数允许取负实现原 σ 的倒数，因此论文四类权全部包含。时间幂因子在空间比较中精确抵消。利用共同顶点节点权下/上界恢复 `a_K≤θa_K'`，没有把 θ 再平方而破坏严格阈值。

开凸、紧闭包和 C¹ profile 是从原固定有界凸多面体及允许权取出的数据；FaceMatching、BoundaryFitted 和正尺度/邻接分级仍明确要求。当前这个辅助界无需额外假定形状正则或 `ℓ≈diam`；原网格的这些较强条件可兼容，而不是在此被冒充已证明。有限测度实例显式保留，与有界域相容。d 没有被强行限制为 2 或 3，原维数是其特例；证明没有在 d=0 使用空间单点零测。空网格/空域的有限和与 a.e. 论证也不要求选择一个不存在的单元，且零能量分支覆盖其范数结论。

## 依赖验收条件

实际使用了 [T054 质量积分验收](T054-local-acceptance.md) 和 [T055 节点权/真实测试验收](T055-local-acceptance.md) 所覆盖的结果；T055 的 checked SHA 正是本阶段基线。上述依赖相对本次固定提交未改变。除此之外，本次直接检查了 `SimplexMassIntegral` 的实际质量积分/正体积因子/强制性调用，`NodalWeightedTest` 的真实测试成员、全域配对及分片证明，`NodalWeightMinimum`、`AllowedCellWeight`、`UniformNodalWeight`、`UniformNeighborGrading`、`NeighborWeightComparison` 的实际定义与比较链，以及真实完整 `conformingSpace` 和 mathlib 正交投影身份。

节点测试的 H¹₀ 成员资格沿既有实际节点 H¹₀ 构造供应；不是把“节点测试属于空间”或“最终估计成立”新增为本次最终定理的不可见前提。既有节点空间到完整一致空间的单向成员证明并不提供反向表示，本报告明确保留该后续义务。尚未清偿的 H² 点值/正则性、统一插值与超逼近误差、完整 P1 N3/N4 及连续热方程 CE 均不能由本阶段推出。

## 构建、公理与远端证据

已独立读取 `/tmp/carleman-nodal-norms-full.log`，实际记录 `Build completed successfully (3623 jobs)` 和 `Axiom audit passed for all 4859 Carleman declarations`。固定本机公理产物 `/tmp/carleman-nodal-norms-local-axioms.txt` 的实测大小是 1,381,579 bytes，SHA256 为 `4018f2af5f5c7e71c5b912a2798df40c534555382b28ea7b8b1765558f4c9755`。逐一解析 18 项递归公理输出，每项都仅依赖 `propext`、`Classical.choice`、`Quot.sound`，未见 `sorryAx` 或额外数学公理。

已独立访问 [main CI run 39164593895](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39164593895/attempts/1) 的 GitHub API：三个 job 的 head SHA 均为本次 checked SHA，且实际为 completed/success：`state-check` 于 `2026-10-18T20:43:27Z`，`lean` 于 `2026-10-18T20:46:42Z`，`dashboard / snapshot` 于 `2026-10-18T20:46:51Z`。固定工作流实际检出 github.sha、构建 `Carleman` 并输出声明公理证据；dashboard 是该运行依赖的第三项检查。

又独立读取 run API，确认本次运行整体 `completed/success`、attempt 1。真实 artifact API 将 `lean-ci-result`（ID `12149908775`）和 `lean-declaration-evidence`（ID `12150217599`）都关联到同一个 run 和同一个 checked SHA，且均未过期。

已直接读取 `/tmp/carleman-nodal-norms-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha=14bdf0cb11fcc8ac2c51297c2307fb5745ee49b5`，`finished_at=2026-10-18T20:45:45.584892+00:00`，CI URL 精确匹配上述 run/attempt，目标 `Carleman`，Lean 4.35.0 与 mathlib pin 正确。此时间是结果生成时间，早于 job 上传证据/收尾完成，不混作三个 job 的最终完成时间。

已独立逐字节比较 `/tmp/carleman-nodal-norms-main-axioms/axioms.txt` 与上述固定本机副本：完全相同，均为 1,381,579 bytes、上述 SHA256。远端末行同样确认全部 4859 声明递归审计 PASS；再从远端文本逐一解析 18 项公理列表，均精确为三项标准基础公理。

最终结论：**PASS；C072 全部 18 声明可升 `REVIEWED / AUXILIARY`。** 未发现需要修正本次声明的数学缺陷。`hproj` 节点表示与 `hf` 零边界节点数据仍是明确、实质的待清偿前提，不能据此将原完整加权投影结论、`prop:p1` 或下游完整命题标为完成；原文覆盖数保持 12/26。本审核仅写此报告，没有修改源码、论文、总台账或提交/推送。
