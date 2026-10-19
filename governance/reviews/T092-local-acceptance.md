# T092 / C108 独立本机验收

- `checked_sha`: `1c3da9ffc54b5624f27760db5368aa05cbdfc0a5`
- `base_commit`: `c5ac12749281c37710ade58c454fe9945273c7ec`
- `reviewed_at`: `2026-10-19T01:48:00+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原完整内部节点空间上，实际重构的全允许权族范数等价，以及同一实际L²载荷右逆的加权稳定性。局部Q_h稳定性、刚度身份、B.2及完整FD仍待；原文保持 **13/26**。

独立从固定提交导出八模块，读取全部证明、18项完整展开类型及关键依赖，对照固定 `paper/main.tex` 的原允许权定义、Section 6物理节点质量／重构，以及Appendix B Step 1载荷公式和 `eq:fd-local-stability`。没有以执行者规格、既有验收文字或CI代替本次数学核对；后续工作树新增局部投影模块不属于本报告。

## 全部18项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON及固定C108台账一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `simplex_continuous_memLp` | `Spatial/WeightedCompactCell.lean:12` | PASS；真实紧单元上的连续函数经有限测度和实际有界性得到MemLp 2。 |
| 2 | `simplex_continuous_weighted_integrable` | `Spatial/WeightedCompactCell.lean:21` | PASS；真实乘子密度与toLp代表身份给加权平方真正可积。 |
| 3 | `simplex_weighted_sq_anchor` | `Spatial/WeightedCompactCell.lean:30` | PASS；正锚点及双向a.e.比较推出两个真实积分界，先证明可积性。 |
| 4 | `weighted_coefficient_sq_anchor` | `Spatial/SimplexWeightedStability.lean:13` | PASS；非负节点权与正锚点逐项平方求和，保留全部系数。 |
| 5 | `simplexNodal_sq_lumped_bounds` | `Spatial/SimplexWeightedStability.lean:34` | PASS；真实质量积分给mΣc²≤(d+2)∫p²及∫p²≤mΣc²。 |
| 6 | `simplex_weighted_reconstruction_bounds` | `Spatial/SimplexWeightedStability.lean:50` | PASS；实际积分和节点锚点界组合给W⁴(d+2)、W⁴双向界，锚点和体积不进入常数。 |
| 7 | `simplex_weighted_load_bound` | `Spatial/SimplexWeightedStability.lean:81` | PASS；同一真实载荷多项式的平方积分上界给W⁴(d+2)加权界。 |
| 8 | `closedCoordinateBox_diameter_bound` | `Geometry/KuhnAllowedWeightComparison.lean:13` | PASS；开盒真实直径界用闭包和连续性延伸至全部闭盒点。 |
| 9 | `cartesianKuhnSimplex_dist_le` | `Geometry/KuhnAllowedWeightComparison.lean:27` | PASS；实际闭单元包含在格点闭盒内，各轴δⱼ≤h给dist≤dh。 |
| 10 | `cartesianKuhn_allowedWeight_comparison` | `Geometry/KuhnAllowedWeightComparison.lean:38` | PASS；实际指数权、闭域轮廓Lipschitz及hq≤1给全部闭单元点双向比较。 |
| 11 | `cartesianInteriorData_weight` | `Spatial/CartesianKuhnWeightedMass.lean:12` | PASS；真实节点单射和有限指示延拓使节点数据与任意物理权乘法交换。 |
| 12 | `cartesianKuhn_weighted_mass_assembly` | `Spatial/CartesianKuhnWeightedMass.lean:24` | PASS；真实加权节点数据代入精确质量组装，给原物理加权对角质量。 |
| 13 | `BoundedMultiplier.integrable_scalar_density_ae` | `Spatial/WeightedScalarRepresentative.lean:11` | PASS；任意实际L²代表替换保持加权平方密度可积。 |
| 14 | `BoundedMultiplier.seminorm_sq_scalar_ae` | `Spatial/WeightedScalarRepresentative.lean:17` | PASS；真实乘子半范数平方等于该代表的实际加权积分。 |
| 15 | `cartesianKuhn_weighted_reconstruction_cell_bounds` | `Spatial/CartesianKuhnWeightedCell.lean:15` | PASS；实际重构闭单元公式、真实限制乘子及节点权给局部双向界。 |
| 16 | `cartesianKuhn_weighted_load_cell_bound` | `Spatial/CartesianKuhnWeightedCell.lean:43` | PASS；同一LoadLift的实际逐单元a.e.公式给局部加权上界。 |
| 17 | `cartesianKuhn_weighted_norm_bounds` | `Spatial/CartesianKuhnWeightedNorm.lean:15` | PASS；真实分割积分、Lp代表身份及精确加权质量组装给全域三项界。 |
| 18 | `allowed_weight_cartesianKuhn_stability` | `Spatial/AllowedCartesianKuhnStability.lean:16` | PASS；固定域／轮廓后先选统一C，再内部清偿所有网格、时间权和状态的比较前提。 |

## 真实局部积分与常数

输入T是真实满维 `Affine.Simplex ℝ (SpatialCoordinates d) d`，K是其顶点的实际闭凸包。连续函数在K上的真实有界性和有限Lebesgue测度先给MemLp 2，再通过真实有界乘子及toLp的a.e.代表身份证明加权平方可积。第3项使用积分单调性时两侧的可积性均已供应，没有利用总化积分在不可积时取零。

写m_K=|K|/(d+1)、p_c=Σc_kλ_k及原载荷L_c=Σc_k((d+2)λ_k−1)。已直接核对所调用的实际质量矩阵积分及载荷平方身份；后者为

\[
\int_K L_c^2=m_K\left((d+2)\sum_k c_k^2-\left(\sum_k c_k\right)^2\right).
\]

因此m_KΣc²≤(d+2)∫p_c²、∫p_c²≤m_KΣc²、∫L_c²≤(d+2)m_KΣc²均为真实多项式积分结论。d+1和d+2严格正，相关代数消去合法。

局部比较的前提分别是节点权ω_k非负且ω_k≤Ws、s≤Wω_k，以及真实乘子在单元上a.e.满足|σ|≤Ws、s≤W|σ|，其中W,s>0。两次平方比较把节点能量和积分能量经过同一s²连接，得到

\[
m_K\sum_k(\omega_kc_k)^2\le W^4(d+2)\int_K|\sigma|^2p_c^2,
\quad \int_K|\sigma|^2p_c^2\le W^4m_K\sum_k(\omega_kc_k)^2,
\quad \int_K|\sigma|^2L_c^2\le W^4(d+2)m_K\sum_k(\omega_kc_k)^2.
\]

证明没有引入参考单元的任意有限维范数等价常数，也没有残留s、|K|的倒数或网格数量因子。节点权和a.e.乘子比较在辅助接口中明确分开，最终定理分别证明它们，未从a.e.信息推断边界点值。

## 闭单元、边界顶点与原允许权族

第8项从真实开盒直径上界出发，逐个变量利用距离函数连续及闭不等式集合，将界延伸到闭盒。正轴步长保证开盒闭包等于对应闭盒。真实Kuhn单元整体位于该闭盒中，故任意x,y∈K都有dist(x,y)≤dh。这一界允许各轴δⱼ不同，不需要长宽比；d而非√d只是合法的较松上界。

最终先固定原有界开凸域S、实际SpatialProfile ρ及其闭域C¹正则性。已读取 `smooth_profile_lipschitz` 的完整证明：开凸域闭包的UniqueDiff、紧性和实际一阶导数有界性给L≥1，再由闭凸集上的均值估计给全部闭域点的L-Lipschitz界；空域也被原证明覆盖。原光滑ρ满足这一较弱正则性要求。

实际网格域Ω_g包含于S，闭单元K包含于closure Ω_g，再由closure的单调性得到K⊆closure S。因此该Lipschitz界覆盖所有边界顶点。对原允许乘子

\[
\sigma(x)=q(t)^\tau\exp(\eta\rho(x)q(t)),\qquad |\eta|=1,
\]

q(t)>0，实际q(t)^τ严格正，两个点的比值中它精确消去。两种η符号都满足指数差的绝对值上界Ldhq(t)，hq(t)≤1使比较常数为W=exp(Ld)。这给全部闭单元点的真实双向比较，不限于内部或a.e.点。

每个单元以实际零号顶点的正σ值为s_K；各顶点属于凸包，故节点比较成立；同一逐点结论再给所需a.e.单元比较。ρ的负性并非该比值估计所需，未附加原允许权族之外的限制。证明对全部实τ成立，因而包含原|τ|≤τ_*的所有权，也包含同时(τ,η)变为(−τ,−η)的逆权。原hq_max≤1蕴含本项的固定时刻hq(t)≤1。

## 同一完整状态、重构和L²载荷右逆

实际状态类型为全部 `CartesianInteriorIndex N → ℝ`，其中 `CartesianInteriorIndex N = ∀ j, Fin (N j−1)`；物理节点坐标是oⱼ+((aⱼ).val+1)δⱼ。正步长给真实节点单射及全部内部节点身份。没有预设状态属于特殊有限支持子空间、节点边界之外的较小集合或满足某个误差结论。

重构严格沿用原帽函数有限和 `cartesianKuhnReconstruction` 及其真实Lp类。已直接读取逐闭单元的实际节点插值身份。载荷严格沿用原 `cartesianKuhnLoadLiftLp`：仅内部顶点系数活动，真实每单元多项式是上述L_c；共享面上的指示和通过实际分割的a.e.唯一归属处理。原完整右逆定理 `cartesianKuhnLoadLiftLp_right_inverse` 的实际输入、输出及证明已读取，仍是归一化真实帽积分算子J_h满足J_h L_h f=f的同一L²对象。本批没有依权或状态另选一个右逆。

第11项只证明实际节点数据延拓的乘法身份；将其用于原精确节点质量组装得到

\[
\sum_K\frac{|K|}{d+1}\sum_{k=0}^d\bigl(\sigma(x_{K,k})c_{K,k}\bigr)^2
=\left(\prod_j\delta_j\right)\sum_a\bigl(\sigma(x_a)f_a\bigr)^2=:E_\sigma(f).
\]

边界顶点的延拓系数严格为零，首末层内部节点仍用原完整关联质量计数。这里没有声称加权节点插值多项式p_(σc)等于点态σp_c；节点身份只用于质量组装。右侧正是原物理节点质量ω_a=∏δⱼ及其加权平方和，没有改用任意等价范数。

真实全域分割沿用 `cartesianKuhnPartition`：闭单元仅在零测共享边界上重叠。单元限制测度≤原域限制测度，来自开凸域中单元内部包含及真实单纯形边界零测性，并非把闭单元误认为包含在开域内。实际R_h和L_h的Lp代表、加权密度可积性和积分平方身份均在求和前供应。精确积分分割与上式节点质量给全域三项界，完全没有重叠常数、节点数、单元数或时间长度损失。

## 最终量词与范围

最终实际展开类型在固定d、S和ρ后给∃C>0，再量化任意o、正δ、N、Ω_g⊆S、h>0及δⱼ≤h，之后才量化任意TimeWeight、τ、t、|η|=1及hq(t)≤1，最后量化完整离散状态f。证明一次选择

\[
C=W^4(d+2)=\exp(4Ld)(d+2)>0.
\]

该C先于所有网格、h、时间权及其周期T、τ、η和状态；不使用ρ的乘子有界性证书中的数值作为最终常数。C可以依赖固定维数、域／轮廓所给L，这是原结论允许的依赖。用同一C得到E_σ≤C‖σR_hf‖²、‖σR_hf‖²≤CE_σ、‖σL_hf‖²≤CE_σ。所有量均非负且C>0，开平方即为原重构范数等价和载荷稳定性，范数常数为√C。

原矩形域等于S的情形被Ω_g⊆S覆盖；没有收缩原完整网格状态或原允许权族。d=0、空内部节点集合及退化网格域也由原有限索引、空乘积及测度定义保留，不影响原d≥1、正网格的结论。本阶段完成上述Step 1辅助稳定性，未证明局部Q_h稳定性、刚度身份、B.2或完整FD/P012，原文仍13/26。

## 固定依赖、构建与公理证据

最终模块Carleman导入闭包共252模块，244旧模块与base完全不变，新增恰为本批八模块。关键已验收依赖亦已比较：C106 CartesianKuhnLoadLift的177模块闭包相对 `340cab6232ac4c81515d19b523fec6e7a031df75` 不变；C107 CartesianKuhnLpNorm的182模块闭包相对base不变；C065 SimplicialIntegrals的85模块闭包相对 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b` 不变。关键数学依赖已直接读取，包括实际载荷、重构、单元质量、节点质量组装、权比较和限制测度接口。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入八模块，`tools/CheckAxioms.lean` 包含18项完整类型和公理输出，并通过privateToUserName遍历全部Carleman声明、递归collectAxioms，只允许三个正常基础公理。

18项完整展开类型逐项核对通过。固定本机1976条显式公理记录中1970非空、6无公理，未发现 `propext`、`Classical.choice`、`Quot.sound` 之外的公理或sorryAx。`/tmp/carleman-kuhn-allowed-stability-full.log` 实际含 `Build completed successfully (3776 jobs).` 及 `Axiom audit passed for all 6076 Carleman declarations.`。固定本机 `/tmp/carleman-kuhn-allowed-stability-local-axioms.txt` 为 **1,786,032 bytes**，SHA256 **`66be7da1cfaa72a5d22768840bf97ad8e9d0fbd354370c4f61fa26c401faf42f`**。

已独立通过GitHub connector读取 [main CI 39186541670 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39186541670/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117850053804）、state-check（117850053568）、dashboard / snapshot（117850923983）三项jobs全部completed/success，其实际步骤均success。同run的lean-ci-result（12157984421）和lean-declaration-evidence（12158710920）artifact元数据均绑定固定SHA。

已实际读取 `/tmp/carleman-kuhn-allowed-stability-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=1c3da9ffc54b5624f27760db5368aa05cbdfc0a5`，targets为Carleman，`finished_at=2026-10-19T01:44:41.440500+00:00`，ci_url精确对应上述run/attempt。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-kuhn-allowed-stability-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,786,032 bytes**，SHA256 **`66be7da1cfaa72a5d22768840bf97ad8e9d0fbd354370c4f61fa26c401faf42f`**。另逐名核对远端18/18完整展开类型及公理，1976条显式记录均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 6076 Carleman declarations.`**。未混用后续工作区产物。

## 验收决定

**C108：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定18项未发现闭单元／边界节点、真实积分、加权质量、同一载荷右逆、完整状态或常数量词方面需要修复的缺陷；同SHA正式三项CI及原始公理产物已独立核实。本报告不提升完整FD/P012、B.2/P026或其他原文命题，原文保持 **13/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
