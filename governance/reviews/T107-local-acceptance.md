# T107 / C123 独立本机验收

- `checked_sha`: `513b40027762c901232372629409f0001dea82ab`
- `base_commit`: `337d9c1b8c5fadce4e638a2c96311e230ee94bb1`
- `reviewed_at`: `2026-10-19T03:49:32+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原物理 Hilbert 空间上的真实 R、质量伴随 J、Q=RJ、G=JR 及原 F=X、Γ=Id、实际 L² lift 的载荷兼容性和 I=Id 右逆。完整 FD/P012 数值接口组装不因此提升，原文保持 **14/26**。

独立从 git 对象读取固定三模块全部证明、十九项完整展开类型及关键依赖，对照原 `paper/main.tex` 的 `eq:massinterface`、`eq:transfer-compositions`、Section 6 Cartesian 定义和 Appendix B Step 1 的真实载荷公式。另读取固定 T107 分析和 MATH_SPEC；执行者说明及 CI 未代替数学核查。后续工作区 `PhysicalFiniteDiagonal` 等增量和变化中的 `.ci` 产物完全排除。

## 全部十九项声明

名称省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根，顺序与交付 JSON、固定 C123 台账一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `cartesianKuhnReconstructionLp_eq_sum` | `Spatial/CartesianReconstructionLinear.lean:14` | PASS；原实际重构 Lp 类严格等于全部内部节点系数乘实际帽函数 Lp 类之和。 |
| 2 | `cartesianPhysicalReconstructionLp` | `Spatial/CartesianReconstructionLinear.lean:32` | PASS；同一 R 的真实线性性由帽和证明，有限维连续性仅构造 CLM。 |
| 3 | `cartesianPhysicalReconstructionLp_apply` | `Spatial/CartesianReconstructionLinear.lean:50` | PASS；新 CLM 的实际值定义性等于既有重构，未另选重构。 |
| 4 | `cartesianPhysicalReconstructionLp_injective` | `Spatial/CartesianReconstructionLinear.lean:54` | PASS；原物理范数平方及严格正的 1/(d+2) 下界作用于 f−g，给完整状态单射性。 |
| 5 | `cartesianKuhnMoment_eq_inner` | `Spatial/CartesianMassAdjoint.lean:13` | PASS；真实归一化积分等于 (∏δ)⁻¹ 乘原 L² 内积，代表替换合法。 |
| 6 | `cartesianKuhnMoment_pairing` | `Spatial/CartesianMassAdjoint.lean:27` | PASS；在原物理内积展开有限和并精确消去正质量，得到原质量伴随配对。 |
| 7 | `cartesianPhysicalMoment` | `Spatial/CartesianMassAdjoint.lean:40` | PASS；定义为同一个重构 CLM 的实际 Hilbert adjoint。 |
| 8 | `cartesianPhysicalMoment_values` | `Spatial/CartesianMassAdjoint.lean:44` | PASS；实际伴随配对和内积非退化性识别其全部节点值为原矩公式。 |
| 9 | `cartesianPhysicalMoment_load_right_inverse` | `Spatial/CartesianMassAdjoint.lean:56` | PASS；值等价单射及既有真实 L² lift 的矩右逆给 J L=Id。 |
| 10 | `cartesianReconstruction` | `Spatial/CartesianReconstructionInterface.lean:14` | PASS；R 限值到原 H¹₀ 图闭包的 L² 实现，J 为真实伴随，mass_adjoint 由 Hilbert 伴随定理证明。 |
| 11 | `cartesianReconstruction_RH` | `Spatial/CartesianReconstructionInterface.lean:22` | PASS；接口 RH 与同一原重构 Lp 类严格相同。 |
| 12 | `cartesianReconstruction_J_values` | `Spatial/CartesianReconstructionInterface.lean:26` | PASS；接口 J 全部节点分量等于原归一化帽函数矩。 |
| 13 | `cartesianReconstruction_QH` | `Spatial/CartesianReconstructionInterface.lean:32` | PASS；接口 QH 严格等于既有 `cartesianKuhnProjectionLp`，此前 B.2 使用的 Q_h 没有被替换。 |
| 14 | `cartesianReconstruction_G_values` | `Spatial/CartesianReconstructionInterface.lean:38` | PASS；接口 G 节点分量严格为 J(Rf)，即原一致质量矩作用。 |
| 15 | `cartesianReconstruction_injective` | `Spatial/CartesianReconstructionInterface.lean:44` | PASS；经真实子空间包含映射把 R 相等送入已证原 L² 重构单射性。 |
| 16 | `cartesianLoadInterface` | `Spatial/CartesianReconstructionInterface.lean:50` | PASS；原 F=X、Γ=Id 和同一实际分片多项式 L² lift，兼容性由第9项提供。 |
| 17 | `cartesianLoadInterface_Γ` | `Spatial/CartesianReconstructionInterface.lean:56` | PASS；原 Γ 在全部物理状态上严格为恒等。 |
| 18 | `cartesianLoadInterface_lift` | `Spatial/CartesianReconstructionInterface.lean:60` | PASS；接口 lift 定义性等于此前证明稳定性的同一实际 lift。 |
| 19 | `cartesianLoadInterface_right_inverse` | `Spatial/CartesianReconstructionInterface.lean:64` | PASS；原 I=Id 是 Γ 的右逆，即 Γ(I f)=f；未将其与 J 或 G 混同。 |

## 真实物理空间与重构单射性

已直接读取 T106 的 `PhysicalFiniteSpace` 和 `CartesianPhysicalSpaces`。物理状态类型包含全部 `CartesianInteriorIndex N → ℝ`，值线性等价为完整双射；没有频谱、均值、支撑或其他状态限制。它有单独的实际范数和内积实例：

\[
m_h=\prod_j\delta_j>0,\qquad
\langle f,g\rangle_{X_h}=m_h\sum_a f_ag_a,\qquad
\|f\|_{X_h}^2=m_h\sum_a f_a^2.
\]

正质量与非负平方和证明内积正定；有限维性给完备性，故用于 adjoint 的确为原物理 Hilbert 空间，而非普通函数类型的上确界范数或未加质量的系数内积。

第1项以 Lp.ext、有限和及实数倍的几乎处处公式、每个实际帽函数的 Lp 代表身份，严格证明原 R_hf=Σ_a f_aφ_a。所有和均有限；没有在任意 L² 类上评价节点。第2项从这一实际等式证明加法和齐次性，然后调用 `LinearMap.toContinuousLinearMap`。此处有限维自动连续性只供应每个固定网格上的连续映射资格，没有将其未知的算子范数当作统一常数。

第4项使用此前实际质量积分给出的

\[
\frac1{d+2}\|f\|_{X_h}^2\le\|R_hf\|_{L^2(\Omega)}^2\le\|f\|_{X_h}^2.
\]

若 R_hf=R_hg，则真实线性性给 R_h(f−g)=0；正的 1/(d+2) 与物理范数正定推出 f=g。没有从任意有限维范数等价取得这一下界，也没有节点总数因子。本批所有身份对任意正 δ、任意 N 和平移 o 成立，包含原 d≥1、Nⱼ≥2、δⱼ=Lⱼ/Nⱼ 的全范围；不需要新增可比性或网格小量条件。空节点空间等退化辅助情形也不需要分母非空假设，空轴乘积为1，d+2始终正。

## 归一化帽函数矩确为同一 Hilbert 伴随

`cartesianKuhnMoment` 的实际定义已读取，为

\[
(J_hu)_a=m_h^{-1}\int_\Omega u\phi_a\,dx.
\]

原 u 是任意真实 L² 类，φ_a 是同一实际 Kuhn 帽函数；`cartesianKuhnMoment_integrable` 由两项 L² 的乘积可积性给出真正积分。第5项通过帽函数的几乎处处身份及 L² 内积公式识别该积分，不依赖对 L² 代表的点值选择，也没有利用不可积积分的默认值。

第6项在原物理内积展开，再使用第1项和有限和的内积线性性：

\[
\langle J_hu,f\rangle_{X_h}
=m_h\sum_a\bigl(m_h^{-1}\langle u,\phi_a\rangle_H\bigr)f_a
=\left\langle u,\sum_a f_a\phi_a\right\rangle_H
=\langle u,R_hf\rangle_H.
\]

所有 δⱼ>0 明确供应 m_h≠0，因此消去归一化合法，没有遗漏质量或平方根质量。第7项将 J 定义为实际 R 的 Hilbert adjoint，第8项则对所有物理 f 比较内积，以 `ext_inner_right` 的非退化性证明它的值等于原积分矩。并非仅给一个未识别的抽象伴随，也没有以目标矩身份作为假设。

## 同一 R/J/Q/G 及同一实际载荷

`cartesianReconstruction` 的 R 是上述实际重构经 `codRestrict` 落入 `dirichletSubspace`；成员证明复用同一真实 Kuhn 零边界重构的原 H¹₀ 图闭包资格。这里只构造原线性 R:X_h→V 及其到 H 的连续实现，没有把 H¹₀ 的闭合性误称为 L² 闭合性，也没有从该资格声称统一 H¹ 算子范数。

已读取底层 `Reconstruction`：RH 是真实包含后的 R，Q=RJ、QH 是其包含到 H，G=JRH；mass_adjoint 正是论文的质量配对。第11–14项分别把这些接口值与既有实际对象对齐。由第14项和帽和展开，原质量矩严格为

\[
(G_hf)_a=m_h^{-1}\sum_b\langle\phi_b,\phi_a\rangle_H f_b.
\]

没有断言 G=Id，也没有断言 Q²=Q。第13项对任意完整 L² 输入严格证明 QH=`cartesianKuhnProjectionLp`，故此前局部/全域 Q_h 逼近结论确实对应这一接口，而非一个同名替代投影。

实际 lift 的构造及右逆依赖已经读取：每个单元上，它几乎处处等于 Σ_k c_k((d+2)λ_k−1)，c_k 是原内部节点数据，边界顶点系数为零。真实有限单元指示和给全域 L² 类；共享面重叠由零测边界处理。单元对偶重心坐标积分和原节点星质量精确给 ∫L_hf φ_a=m_h f_a，正质量归一化后得到原矩右逆。所有内节点包括邻近物理边界的节点均保留。

第9项通过物理值等价的单射性把这一实际右逆转为真实 Hilbert J_hL_h=Id。第16项取 F 为同一物理 X_h，Γ 为恒等，lift 定义性等于上述已验收 L² 载荷；其 `LoadInterface.compatible` 是真实 J_hL_h=Γ。第19项的 I=Id 只表示 ΓI=Id，不误称 lift 是 R 或 G 的逆。

这些算子只依赖空间网格，独立于时间、周期、允许权和数据；实际等式没有隐藏常数。此前量化的加权稳定性可以沿本批对象身份使用，但本批 `LoadInterface` 本身只包含代数兼容性，没有声称已经将全部加权估计及数值假设装配完成。完整 FD/P012 保持待完成，原文14/26。

## 固定依赖及本机构建、公理证据

三模块的 Carleman 导入闭包共315模块，312旧模块与 base 完全相同，新增恰为本批三模块。另逐模块比较关键已验收版本：C122 `CartesianPhysicalSpaces` 的310模块闭包相对 base 不变；C106 `CartesianKuhnLoadLift` 的177模块闭包相对 `340cab6232ac4c81515d19b523fec6e7a031df75` 不变；C107 `CartesianKuhnLpNorm` 的182模块闭包相对 `c5ac12749281c37710ade58c454fe9945273c7ec` 不变；C109 `CartesianKuhnProjection` 的184模块闭包相对 `ba9aa5d2a3caf655bba037695fe733a3f292d952` 不变；C111 `CartesianKuhnReconstructionJet` 的183模块闭包相对 `116908340801d3f1cd9f7e940304807f70bdb1ba` 不变。没有把旧 declaration_version 的验收默默用于已改变的数学依赖。

原稿、既有治理协议、工具链 pin 和 CI 工作流自上一已审阶段未改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。固定 Lean 为4.35.0；mathlib pin和本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。root 显式导入全部三模块，`tools/CheckAxioms.lean` 包含十九项完整类型及公理输出，并递归检查全部 Carleman 声明。

实际读取 `/tmp/carleman-fd-mass-interface-full.log`：`Build completed successfully (3824 jobs).`，末行为 `Axiom audit passed for all 6476 Carleman declarations.`。约定的 `-target.log` 不存在，本报告不声称读取定向构建日志，也不以交付说明中的定向 job 数作为独立证据。

固定 `/tmp/carleman-fd-mass-interface-local-axioms.txt` 为 **1,916,697 bytes**，SHA256 **`e1df70e557ce51b7452586cfd03d20fdceda824dab52e64bd764844c4212efe3`**。十九项完整展开类型均逐项核对；全部2182条显式公理记录中2174非空、8无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无 sorryAx。

## 实际同 SHA CI 与原始远端产物

本验收 Agent 自行经 GitHub connector 查询 [main CI 39196236578 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39196236578/attempts/1)。实际 run 为 main/push、completed/success，head SHA 精确为固定提交。三个 job 均 completed/success：state-check **117879504127**、lean **117879504365**、dashboard / snapshot **117880180801**；最终读取的全部实际步骤均success。

同 run 原始 artifact 元数据：`lean-ci-result` **12161768745**，`lean-declaration-evidence` **12161634296**，两者 workflow_run.head_sha 均为固定 SHA。本 Agent 自行通过 `gh run download 39196236578` 下载两份原始产物至约定目录。

实际 `/tmp/carleman-fd-mass-interface-main-ci/result.json` 为 PASS，`checked_sha=source_head_sha=513b40027762c901232372629409f0001dea82ab`，targets为Carleman，`finished_at=2026-10-19T03:47:54.181377+00:00`，ci_url精确对应上述run/attempt；Lean4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

独立逐字节比较 `/tmp/carleman-fd-mass-interface-main-axioms/axioms.txt` 与固定本机副本，完全一致：**1,916,697 bytes**，SHA256 **`e1df70e557ce51b7452586cfd03d20fdceda824dab52e64bd764844c4212efe3`**。另逐名确认远端19/19完整类型及基础公理记录；实际末行为 **6476项全声明递归审计PASS**。没有混用后续工作区 `.ci/axioms.txt`。

## 验收决定

**C123：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定十九项未发现需要修复的数学缺陷：真实物理 Hilbert 范数和完整状态、原 R 的单射性、真实归一化矩与 Hilbert adjoint 身份、同一 Q_h/G_h、原 F=X 与实际载荷兼容性全部独立核对通过；未使用有限维自动连续性冒充统一估计。同 SHA 三项正式 CI 和自行下载的原始公理证据已核实。

本批不提升完整 FD/P012 或 PAPER 覆盖，原文保持 **14/26**。本次仅新建本报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发 UTC 固定，通知主 Agent 后不再变更。
