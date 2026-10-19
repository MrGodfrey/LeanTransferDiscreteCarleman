# T101 / C117 独立本机验收

- `checked_sha`: `88306d8177aee83bfc8c6011f9d964a273e042b9`
- `base_commit`: `d8a513e72a1c480b4ecab1e2dcf3fe583ffc5527`
- `reviewed_at`: `2026-10-19T02:56:31+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全部节点空间上σ²对角测试的精确线性、自伴、正定和能量结构，真实节点重构身份，以及全允许权的 `eq:test-norm`。时间导数、周期性、完整超逼近和观察仍待；完整FD/P012不提升，原文保持 **14/26**。

独立从固定提交导出两模块，读取全部证明、15项完整展开类型及关键依赖，对照固定 `paper/main.tex` 的 `eq:test-norm`、Ptest接口及Appendix B Step 3原对角测试。执行者规格及CI没有代替数学核对；后续工作树不纳入本报告。下面单列残差与论文相反的符号约定，它不阻断本批正确身份及范数比较的验收。

## 全部15项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON及固定C117台账一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `cartesianNodalMultiplier` | `Spatial/CartesianDiagonalTest.lean:14` | PASS；全部原内部节点上真实ω(x_a)乘法，逐点证明加法及实数齐次性。 |
| 2 | `cartesianSquaredWeightTest` | `Spatial/CartesianDiagonalTest.lean:21` | PASS；严格将同一节点线性乘子取ω=σ²，得到原测试。 |
| 3 | `cartesianWeightedNodeEnergy` | `Spatial/CartesianDiagonalTest.lean:26` | PASS；真实物理质量∏δⱼ乘全部节点(σ(x_a)f_a)²之和。 |
| 4 | `cartesianNodalMultiplier_selfadjoint` | `Spatial/CartesianDiagonalTest.lean:30` | PASS；在同一原物理配对中逐项实乘法结合律给自伴性。 |
| 5 | `cartesianSquaredWeightTest_pairing` | `Spatial/CartesianDiagonalTest.lean:41` | PASS；(f,Tσf)恰等于原σ节点能量，无比较损失。 |
| 6 | `cartesianWeightedNodeEnergy_nonneg` | `Spatial/CartesianDiagonalTest.lean:52` | PASS；正步长物理质量与平方和给非负性。 |
| 7 | `cartesianWeightedNodeEnergy_eq_zero_iff` | `Spatial/CartesianDiagonalTest.lean:57` | PASS；正质量及全部节点权非零，逐项推出能量零当且仅当完整f=0。 |
| 8 | `cartesianSquaredWeightTest_positive` | `Spatial/CartesianDiagonalTest.lean:72` | PASS；对任意非零完整状态得严格正二次配对，适用于全部正允许权。 |
| 9 | `cartesianSquaredWeightTest_inverse_energy` | `Spatial/CartesianDiagonalTest.lean:81` | PASS；逐节点合法消去非零σ，逆权下测试后能量精确等于原σ能量。 |
| 10 | `cartesianInteriorData_multiplier` | `Spatial/CartesianDiagonalTest.lean:95` | PASS；真实有限节点指示延拓与任意物理点函数ω乘法严格交换。 |
| 11 | `cartesianKuhnReconstruction_multiplier_nodal` | `Spatial/CartesianDiagonalTest.lean:110` | PASS；全部单元顶点再现和真实nodalFunction给全空间点函数身份。 |
| 12 | `cartesianKuhnReconstructionLp_multiplier_nodal` | `Spatial/CartesianDiagonalTest.lean:120` | PASS；同一真实节点插值身份在实际Lp类中成立，无Lp点值算子。 |
| 13 | `cartesianSquaredWeightTest_reconstruction` | `Spatial/AllowedCartesianDiagonalTest.lean:14` | PASS；原R_hTσf严格等于真实I_h(σ²R_hf)。 |
| 14 | `cartesianSquaredWeightTest_residual` | `Spatial/AllowedCartesianDiagonalTest.lean:21` | PASS；准确识别已有残差为σ²R_hf−R_hTσf，方向说明见下。 |
| 15 | `allowed_weight_cartesian_test_norm` | `Spatial/AllowedCartesianDiagonalTest.lean:33` | PASS；真实允许权质量稳定性与精确配对组合，统一C在全部网格、周期、幂、符号和状态之前。 |

## 原物理配对、完整节点空间与严格正定性

状态类型是全部 `CartesianInteriorIndex N → ℝ`，每个坐标索引为Fin(Nⱼ−1)，物理节点为oⱼ+((aⱼ).val+1)δⱼ。没有缩小状态空间或对状态附加支撑、均值、频谱条件。实际 `cartesianPhysicalInner` 的定义已经读取，严格为

\[
(f,g)_{X_h}=m_h\sum_a f_ag_a,\qquad m_h=\prod_j\delta_j,
\]

与前阶段原有限差分刚度接口使用同一个配对。正δⱼ给m_h>0，这是原物理内积，未换成无权系数配对或任意有限维等价内积。

节点乘子定义为M_ωf(a)=ω(x_a)f_a，线性性由实际逐点乘法给出。对任意实ω，逐项实数交换／结合律严格给(M_ωf,g)=(f,M_ωg)。取ω=σ²得到原Tσ；同一配对的二次值恰为

\[
(f,T_\sigma f)_{X_h}=E_\sigma(f)
=m_h\sum_a\bigl(\sigma(x_a)f_a\bigr)^2.
\]

在m_h>0和每个σ(x_a)≠0下，有限非负平方和为零迫使每项为零，继而每个f_a为零。反向也直接成立。因此对全部非零f严格正定，而非只证明半正定。辅助定理明确保留节点权非零前提，没有对任意可能消失的权误称正定。

对实际允许权，已直接读取 `scaled_multiplier_pos`：q(t)>0保证实幂q(t)^τ>0，指数函数严格正；onSubdomain保留相同点值，所以每个节点的非零前提都内部可由原允许权定义清偿，不是新增数学假设。d=0的空轴乘积为1，空内部节点集合时只有零状态，原非零状态结论合法；原d≥1、Nⱼ≥2的全部情形均覆盖。

逆权身份在每个真实节点使用σ⁻¹σ²f=σf，非零σ明确保证消去合法，得到E_(σ⁻¹)(Tσf)=E_σ(f)。这是精确身份，没有二次权幂数错误或节点数因子；该代数辅助身份本身不需要步长正性，而作为物理能量使用时仍在原正步长范围内。

## 真实零延拓、节点插值与Lp对象

第10项展开原 `cartesianInteriorData` 的有限指示和，逐节点区分x_a=x与否；相等时使用真实物理点相等替换ω(x_a)=ω(x)，不相等时两边项均为零。因此它对任意点函数ω成立，并包含全部边界／域外零延拓数据。

原重构R_hf严格等于同一实际Kuhn分割对内部数据延拓的nodalFunction。第11、12项在每个真实单元的全部顶点使用已证顶点再现性，再通过nodalFunction_congr／nodalLp_congr，得到

\[
R_h(M_\omega f)=I_h(\omega R_hf).
\]

这里I_h是实际分片仿射节点函数：在闭单元上用真实重心坐标插值，共有面一致，覆盖外按原定义为零。边界顶点的原数据及R_hf顶点值都为零，未遗漏边界单元。第11项是全空间点函数等式，第12项是原域实际Lp类等式；取ω=σ²给论文所需R_hTσf=I_h(σ²R_hf)。

该结论没有声称I_h(ωR_hf)=ωR_hf在单元内逐点相等。ω的输入是实际点函数、R_hf是实际连续重构，故不存在对任意L²类取节点值的问题。即使一般ω没有连续性，插值只用有限真实节点值，已有真实nodalLp构造保证结果属于L²；其有限节点粗界只用于成员证明，不进入最终统一常数。

## 残差方向：非阻断接口说明

固定第14项展开类型准确为

\[
\operatorname{nodalProductResidual}(\sigma^2,f^{\rm ext})
=\sigma^2R_hf-R_hT_\sigma f.
\]

这与既有 `nodalProductResidual w f = w I_hf-I_h(wf)` 的定义严格一致，证明没有符号错误。但论文 `eq:testsuper` 写的是R_hTσf−σ²R_hf，故论文残差是本接口残差的负值。不能把两个带符号的点函数或弱jet直接等同。

这个差异不阻断本批验收：当前定理忠实证明了其实际声明，且后续值范数、弱梯度范数及N_σ在整体取负下不变。衔接论文方向时应显式取负，或分别使用值／梯度范数的负号不变性；当前身份本身尚未证明相应完整弱残差估计或超逼近。本验收已将此注意点告知后续执行者，未改动实现或原稿。

## 全允许权质量比较及常数量词

第15项从已验收T092的实际允许权重构稳定性取得同一C，再用上述精确二次配对替换E_σ，直接得到

\[
(f,T_\sigma f)_{X_h}\le C\|\sigma R_hf\|_{L^2(\Omega_g)}^2,
\qquad
\|\sigma R_hf\|_{L^2(\Omega_g)}^2\le C(f,T_\sigma f)_{X_h}.
\]

这正是原 `eq:test-norm` 的双向比较；半范数为同一实际有界乘子作用于原重构Lp类后的真实L²范数，不是另造的节点能量定义。底层真实单元积分及精确加权节点质量组装再次读取，没有将目标质量比较作为前提，也没有节点／单元总数损失。

完整展开类型在固定d、有界开凸环境S、实际ρ及其闭域C¹正则性后给∃C>0，然后才量化全部o、正δ、N、网格域Ω_g⊆S、h>0及δⱼ≤h；再量化任意TimeWeight、τ、t、|η|=1和hq(t)≤1，最后量化全部f。原固定物理域对应Ω_g=S，故没有收缩原范围。ρ原光滑性供应C¹条件，原hq_max≤1供应固定时刻条件。

所复用常数由固定轮廓的L-Lipschitz界给W=exp(Ld)、C=W⁴(d+2)。实际闭单元直径≤dh和hq≤1清偿全部闭单元（含边界顶点）权比较，q^τ在比值中精确消去。C先于网格、h、TimeWeight及其周期T、幂τ、时刻、符号和状态，不依赖任意节点有界性证书的数值或网格基数。结论对全部实τ成立，包含原|τ|≤τ_*及同时(τ,η)变负的逆权；两种η符号均保留。

本批只完成上述结构及质量比较；原Ptest的算子时间可微性、端点周期身份、`eq:testtime`、完整 `eq:testsuper` 和观察接口仍待，完整FD/P012不因这些辅助结论提升。原文保持14/26。

## 固定依赖、构建与公理证据

两模块Carleman导入闭包共306模块，304旧模块与base完全不变，新增恰为本批两模块。关键已验收版本亦已逐模块比较：C108 AllowedCartesianKuhnStability的252模块闭包相对 `1c3da9ffc54b5624f27760db5368aa05cbdfc0a5` 不变；C116 CartesianFiniteDifference的228模块闭包相对base不变；C079 SimplicialProductResidual的116模块闭包相对 `36278e60193f3453a60bcdf33ef089ace1398350` 不变；C053 SimplicialNodalOperator的31模块闭包相对 `6923ae3b24d9590bd0afb4e66830b30fe49165d3` 不变。关键数学依赖已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入两模块，`tools/CheckAxioms.lean` 包含15项完整类型和公理输出，并通过privateToUserName遍历全部Carleman声明、递归collectAxioms。

15项完整展开类型已逐项核对。固定本机2100条显式公理记录中2092非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理或sorryAx。实际定向日志为3497 jobs；`/tmp/carleman-fd-diagonal-test-full.log` 包含 `Build completed successfully (3806 jobs).` 和 `Axiom audit passed for all 6248 Carleman declarations.`。固定本机 `/tmp/carleman-fd-diagonal-test-local-axioms.txt` 为 **1,868,402 bytes**，SHA256 **`9d3dc33c7a99a4f9bdacf17ebee3b0e68154d82215439d755091daa5efadcaf1`**。

已独立通过GitHub connector读取 [main CI 39192013906 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39192013906/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117866683760）、state-check（117866683989）、dashboard / snapshot（117867329983）三项jobs全部completed/success，其实际步骤均success。同run的lean-ci-result（12160820434）和lean-declaration-evidence（12160820438）artifact元数据均绑定固定SHA。

本验收Agent已自行通过 `gh run download 39192013906` 下载同run两份原始artifact。实际读取 `/tmp/carleman-fd-diagonal-test-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=88306d8177aee83bfc8c6011f9d964a273e042b9`，targets为Carleman，`finished_at=2026-10-19T02:54:33.602854+00:00`，ci_url精确对应上述run/attempt。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-fd-diagonal-test-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,868,402 bytes**，SHA256 **`9d3dc33c7a99a4f9bdacf17ebee3b0e68154d82215439d755091daa5efadcaf1`**。另逐名核对远端15/15完整展开类型及公理，2100条显式记录均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 6248 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C117：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定15项未发现线性测试、原物理配对、自伴／正定、精确能量、节点／Lp身份或允许权常数量词方面需要修复的缺陷；残差方向的非阻断接口注意点已明确记录。同SHA正式三项CI及自行下载的原始公理证据已独立核实。Ptest其余义务、观察及完整FD/P012仍待，原文保持 **14/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
