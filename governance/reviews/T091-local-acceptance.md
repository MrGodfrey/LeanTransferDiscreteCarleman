# T091 / C107 独立本机验收

- `checked_sha`: `c5ac12749281c37710ade58c454fe9945273c7ec`
- `base_commit`: `340cab6232ac4c81515d19b523fec6e7a031df75`
- `semantic_checked_at`: `2026-10-19T01:28:24+00:00`
- `reviewed_at`: `2026-10-19T01:32:38+00:00`
- `result`: **PASS**；固定版本语义与同 SHA 远端证据均通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节一致，6057 项递归审计通过。
- `scope`: **AUXILIARY**；真实有限网格重构的无权 L² 质量等价，以及同一真实载荷右逆的无权 L² 稳定性。原文保持 **13/26**。

本报告直接核对固定提交五模块全部 24 项声明、证明和完整实际类型，并读取实际节点、帽质量、载荷右逆、单元质量及分割积分等关键依赖。对照原 `paper/main.tex:1634–1666` 的完整内部向量/物理对角质量/原重构定义，以及 Appendix B Step 1（2745–2789）的载荷和重构稳定性；同时核对 `governance/analysis/T091-kuhn-norm.md`。不以规格、执行者报告或 CI 替代数学验收，后续工作树增量不在范围内。

## 全部 24 项声明

名称均加前缀 `Carleman.`，源码位置相对于固定提交 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `cartesianKuhnReconstruction` | `CartesianKuhnReconstruction.lean:13` | PASS；直接定义原全部内部帽函数的有限线性组合 Rf=Σf_aφ_a。 |
| 2 | `cartesianKuhnReconstruction_on_cell` | `CartesianKuhnReconstruction.lean:17` | PASS；真实闭单元上逐点等于原节点数据零延拓形成的实际 P1 插值。 |
| 3 | `cartesianKuhnReconstruction_continuous` | `CartesianKuhnReconstruction.lean:35` | PASS；每个真实内部帽的全空间连续性给有限和连续性。 |
| 4 | `cartesianKuhnReconstruction_compact` | `CartesianKuhnReconstruction.lean:42` | PASS；真实有限帽支撑给全空间重构紧支撑。 |
| 5 | `cartesianKuhnReconstruction_memLp` | `CartesianKuhnReconstruction.lean:54` | PASS；连续紧支撑供应真实全空间 L² 可积性。 |
| 6 | `cartesianKuhnReconstruction_sq_integrable` | `CartesianKuhnReconstruction.lean:60` | PASS；同一实际重构的平方真正可积。 |
| 7 | `integral_simplexLoadPolynomial` | `SimplexLoadNorm.lean:12` | PASS；实际单元载荷积分为 mΣc_i，m=|K|/(d+1)。 |
| 8 | `integral_simplexLoadPolynomial_sq` | `SimplexLoadNorm.lean:35` | PASS；真实平方积分精确为 m((d+2)Σc_i²−(Σc_i)²)。 |
| 9 | `integral_simplexLoadPolynomial_sq_le` | `SimplexLoadNorm.lean:76` | PASS；仅舍弃非负平方项，得到 (d+2)mΣc_i²，无系数同号条件。 |
| 10 | `cartesianInteriorData_sq` | `CartesianKuhnMassAssembly.lean:13` | PASS；实际内部点单射，故零延拓值的平方恰为平方数据的零延拓，未丢交叉项。 |
| 11 | `cartesianInteriorData_zero_compl` | `CartesianKuhnMassAssembly.lean:23` | PASS；原域外不可能等于任何内部节点，所有对应指标项为零。 |
| 12 | `cartesianKuhnLoadCoefficients_interiorData` | `CartesianKuhnMassAssembly.lean:34` | PASS；原载荷活动顶点指示与数据域外零值精确兼容。 |
| 13 | `cartesianKuhn_vertex_mass` | `CartesianKuhnMassAssembly.lean:43` | PASS；真实帽积分和真实单元积分精确给每个内部节点总质量 ∏δ_j。 |
| 14 | `cartesianKuhn_vertex_mass_assembly` | `CartesianKuhnMassAssembly.lean:60` | PASS；有限三重求和重排，完整节点质量精确组装，无基数估计。 |
| 15 | `cartesianKuhn_vertex_mass_sq_assembly` | `CartesianKuhnMassAssembly.lean:85` | PASS；对平方数据使用同一组装身份，给原物理对角能量 E。 |
| 16 | `cartesianKuhnReconstruction_cell_sq_bounds` | `CartesianKuhnNormBounds.lean:14` | PASS；真实 P1 积分界改写为单元节点质量的 1/(d+2) 与 1。 |
| 17 | `cartesianKuhnReconstruction_sq_bounds` | `CartesianKuhnNormBounds.lean:47` | PASS；真实可积分割与精确质量组装给原域上下界 E/(d+2)≤∫(Rf)²≤E。 |
| 18 | `cartesianKuhnLoadLift_cell_sq_bound` | `CartesianKuhnNormBounds.lean:64` | PASS；同一实际载荷的 a.e. 单元身份给 (d+2) 倍单元节点质量上界。 |
| 19 | `cartesianKuhnLoadLift_sq_bound` | `CartesianKuhnNormBounds.lean:80` | PASS；实际可积性、精确分割与质量组装给 ∫(Lf)²≤(d+2)E。 |
| 20 | `cartesianKuhnReconstructionLp` | `CartesianKuhnLpNorm.lean:14` | PASS；用原重构函数的真实 MemLp 构造原物理域 L² 类。 |
| 21 | `cartesianKuhnReconstructionLp_ae` | `CartesianKuhnLpNorm.lean:20` | PASS；L² 类代表在同一原域 a.e. 等于实际帽函数有限和。 |
| 22 | `cartesianKuhnReconstructionLp_norm_sq` | `CartesianKuhnLpNorm.lean:27` | PASS；真实 L² 范数平方等于前述实际重构平方积分。 |
| 23 | `cartesianKuhnReconstructionLp_norm_sq_bounds` | `CartesianKuhnLpNorm.lean:36` | PASS；最终原对角质量与真实重构 L² 范数平方上下界，常数仅 d。 |
| 24 | `cartesianKuhnLoadLiftLp_norm_sq_bound` | `CartesianKuhnLpNorm.lean:43` | PASS；对 T090 同一实际矩右逆 L² 类给出 (d+2)E 上界，没有换载荷。 |

## 原对象、完整状态和范围

原论文取内部索引 ∏j{1,…,N_j−1}，物理节点质量 ω_a=∏jδ_j，对角平方范数为 `Σ_a ω_a f_a²`，重构为 `Σ_a f_aφ_a`。这里 `CartesianInteriorIndex N=∀j,Fin(N_j−1)`，实际整数坐标为每个索引值加一。与原内部索引是精确的一一对应，所有原 N_j≥2 的内部数据向量都包括在内，不取低频子空间、平均零子空间或特殊符号向量。

物理点为 `o_j+(a_j+1)δ_j`，原域为 `openCoordinateBox o (o+Nδ)`；o=0、δ_j=L_j/N_j 即原 Ω。输入任意平移、任意正 δ 和任意 f，结论给精确

`E(f)=(∏jδ_j)Σ_a f_a²`，

`E(f)/(d+2) ≤ ‖R_hf‖L²(Ω)² ≤ E(f)`，

`‖L_hf‖L²(Ω)² ≤ (d+2)E(f)`。

这些是原对角物理质量，不是未加质量的欧氏系数和、平均质量或一致质量矩阵本身。常数直接在类型中写为 d+2、其倒数和 1，因此仅依赖维数，并在所有 o、δ、N、f 上统一；无节点数、单元数、δ 比值或网格总尺寸依赖。

原 Appendix B Step 1 的载荷和重构结论含实际允许权 σ。本批只完成其无权基础，未证明允许权族下的比较，也未证明局部 Q_h 稳定性或完整离散算子身份。不能由这些无权界自动完成 `eq:fd-local-stability` 的全加权版本、原全部 numerical assumptions、FD/P012 或 B.2/P026。C107 仅 **AUXILIARY**，原文保持 **13/26**。

## 实际重构及节点平方身份

`cartesianKuhnReconstruction` 直接使用实际有限网格的内部帽函数有限和。已核对相关定义：真实帽在关联闭单元上为重心坐标，在非关联单元上为零；公共面一致性确保它是原连续 P1 基函数，而非闭单元指示的重复求和。新单元公式展开两个有限和后换序，严格得到同一个单元上的实际 `simplexNodalInterpolant`。

`cartesianInteriorData` 是把有限节点向量按实际节点注入空间点的零延拓，只有在系数取样时使用。它不是拿来积分的重构场，也没有将一般 L² 类在节点取值。正 δ 使实际内部点单射，故任意空间点最多对应一个节点；节点处数据恰为 f_a，其它点为零。这证明 `data(f,x)²=data(f²,x)`，避免错误地把一般和的平方当作平方之和。

内部点确实在原开盒，故物理域外数据为零。原载荷系数的“顶点在 Ω 内才取值”指示，在输入这份零延拓数据后精确等于同一个 data 顶点值；边界节点既不会加入重构，也不会在载荷中保留非零系数。

重构的全空间连续性与紧支撑由有限个真实内部帽供应，进而得到真正 MemLp 2 和平方可积性。无需任意给 f 的延拓函数的可测性，也没有对离散向量附加稳定性条件。

## 真实单元质量与载荷平方积分

直接核对 `SimplexMassIntegral` 的真实 Lebesgue 积分身份。若 c 是一个真实 d 维单纯形 K 上全部 d+1 个顶点系数，则

`∫K (Σc_iλ_i)² = |K|/((d+1)(d+2)) [Σc_i²+(Σc_i)²]`。

其输入是实际重心坐标积分，并非独立定义的系数范数。有限 Cauchy–Schwarz 给 `(Σc_i)²≤(d+1)Σc_i²`，非负平方给下界；令 `E_K=|K|/(d+1)Σc_i²`，恰得到 `E_K/(d+2)≤∫K(Rf)²≤E_K`。d+1、d+2 均严格正，所有除数改写合法。系数可任意混合正负，未使用加权系数强制性中的任何 γ 或网格分级条件。

载荷单元函数与原文逐项相同：`L_K(x)=Σc_i((d+2)λ_i(x)−1)`，边界顶点对应 c_i=0。实际重心坐标均值给 `∫K L_K=mΣc_i`，m=|K|/(d+1)。已证明的真实双对偶矩为 `∫K L_Kλ_i=mc_i`。新证明把同一 L_K² 写成 `Σc_i((d+2)L_Kλ_i−L_K)`，逐项积分后得到精确

`∫K L_K² = m[(d+2)Σc_i²−(Σc_i)²]`。

代码在交换有限和、积分常数倍及积分相减之前，分别供应 L_K、L_Kλ_i 和所组合各项在紧闭单元上的真正可积性。没有以不可积时默认积分为零完成等式。m≥0，故舍弃最后非负项恰得 `∫K L_K²≤(d+2)E_K`。未漏掉平方和项、未把 (Σc_i)² 的负号改错。

## 节点质量精确组装

新 `cartesianKuhn_vertex_mass` 不是假定每个星有固定质量：它对原实际 φ_a 使用已证明的分割积分恒等式及单元帽积分，结合真实零阶矩 `∫Ωφ_a=∏δ_j`，得

`Σ_{K,k:vertex(K,k)=x_a} |K|/(d+1)=∏δ_j`。

已直接读取其零阶矩依赖 `CartesianKuhnMass`、`KuhnNodeIncidence`、`KuhnCellVolume`：每个坐标排列 π 和顶点位置 k 唯一确定含 x_a 的实际有限单元，原点是 a−该位置的前缀指示；T088 的内部节点完整性保证这个单元实际位于有限网格。固定 π,k 的节点映射单射保证唯一性。有限关联求和因此精确成为 `Σπ(d+1)m_π`，并非粗略上界。

单元真实体积对格点平移不变，由 Lebesgue 平移换元证明；一个真实 Cartesian 盒上的全部排列单元体积和，通过精确分割积分等于盒体积 ∏δ_j。两个因子 d+1 正好相消，产生上述真实帽质量。这个论证也覆盖第一层和最后一层内部节点，不使用不完整边界星的假质量。

`cartesianKuhn_vertex_mass_assembly` 展开 data 后，将单元、顶点、内部节点三个有限和重排，再逐内部节点使用已证明的真实质量身份，得到对任意实数据 g 的

`Σ_K |K|/(d+1) Σ_k data(g,vertex(K,k)) = (∏δ_j)Σ_a g_a`。

取 g=f² 并使用实际点单射带来的平方延拓身份，精确得到 `Σ_KE_K=E(f)`。没有用有限集基数乘最大值，没有单元数、星度上界或形状常数损失。

## 全域积分、真实 L² 类与同一右逆

直接核对 `SimplicialIntegrals.integral_eq_sum_cells`。该结果先使用同一分割的真实 a.e. 唯一单元覆盖，以指示函数和表示可积场，再交换有限和与积分；闭单元边界零测且单元内部属于原开凸域，使 `(volume.restrict Ω).restrict K=volume.restrict K`。共享边界不会在积分中重复贡献。

重构使用前述同一平方函数的全空间可积性限制到 Ω，再精确求和单元上下界，最后用 `Σ_KE_K=E(f)` 得全域积分两侧界。载荷一般不跨单元连续，其定义是实际闭单元指示的有限和；已有 `cartesianKuhnLoad_on_cell` 仅在单元上 a.e. 等于局部载荷多项式，这个精度恰适用于平方积分，不曾把共享面上的多重值当作逐点单元公式。

已有载荷 MemLp 由有限个紧单元上的真实有界连续局部多项式供应；不需要任意空间数据函数本身可测，因为仅使用有限顶点样本。新全域平方界先从同一载荷 MemLp 用 L²×L² 得真正平方可积，再应用精确分割，故各积分和与不等式都对应实际函数。

最终 `cartesianKuhnReconstructionLp` 用原帽有限和的 MemLp 限制构造真正 `Lp ℝ 2 (volume.restrict Ω)`。代表 a.e. 恒等式和 `lp_two_norm_sq_integral` 给其真实范数平方精确等于前述积分；实数范数平方通过 `|r|²=r²` 改写，未将系数范数定义为“重构范数”。

载荷最终入口直接接受 `cartesianKuhnLoadLiftLp o δ hδ N f`。已逐行核对 T090 的 `CartesianKuhnLoadLift` 与 `CartesianKuhnLoadMoment`：其真实归一化矩算子为 `(∏δ_j)⁻¹∫uφ_a`，且此同一 L² 类的矩恰返回 f。归一化因子非零由全部 δ_j>0 证明；代表配对可积性由实际 L² 场供应。本批没有改定义或选另一份较方便的载荷，范数界与既有右逆结论针对完全相同的对象。

## 量词与边界情形

结论的系数是显式维数函数，适用于全部 o、正 δ、N 和原完整有限实向量 f。无需正系数、均值条件、特殊方向、低频过滤、预给节点质量、H¹ 正则或抽象稳定性假设。原各方向步长可比条件在这些无权精确质量公式中不必使用；省略它加强结论，没有收紧原网格。

所有原 d≥1、N_j≥2 均覆盖；N_j=2 的唯一内部层及边界附近内部节点包含在真实索引和精确质量组装中。额外允许无内部节点的退化索引情况时有限和为空，结论正常成为零界；d=0 也不除以 d，d+1 和 d+2 仍为正。零向量无需单独除范数。输出是平方界，与原无权范数稳定性取非负平方根等价。

本批没有可供覆盖表提升的完整原文命题；只清偿无权重构/载荷质量界。允许权族、局部 Q_h、刚度、具体 numerical data 和完整 FD/B.2 仍须继续供应及验收。

## 固定版本、本机构建与递归公理

五模块 Carleman 导入闭包共 182 个模块，其中 177 个既有模块相对 base 逐字节未变，root 明确导入全部五模块。AGENTS、治理和 state 协议与已读版本一致；原论文、Lean/mathlib pin、两个 CI workflows 相对 base 未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-kuhn-norm-target.log` 实际显示定向构建 3359 jobs 成功；`/tmp/carleman-kuhn-norm-full.log` 实际显示全库 3768 jobs 成功并完成 6057 声明递归审计。固定 `/tmp/carleman-kuhn-norm-local-axioms.txt` 为 1,768,650 bytes，SHA256 `252c68da3a4ff05471dddb5ae125493135a7cfd2e8c26373d207ae80f9b498f9`。

24 项实际完整类型与固定源码逐项核对，每项恰有一条类型和一条公理检查，均只用 `propext`、`Classical.choice`、`Quot.sound`。全产物 1952 条带公理打印（1948 个不同声明）及 6 条无公理打印已扫描，无白名单外公理；末行实际为 `Axiom audit passed for all 6057 Carleman declarations.`。审计程序相对 base 未改，仍递归检查全部 Carleman 声明，本批只增显式打印。五新模块无 sorry/admit 或新增数学公理。

## 远端证据与签发

已独立查询 [main CI run 39185414279 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39185414279/attempts/1)，确认事件为 `push`、分支为 `main`、head SHA 为本次固定 `c5ac12749281c37710ade58c454fe9945273c7ec`。run 最终为 `completed/success`，最后更新时间为 `2026-10-19T01:30:21Z`；三个实际 jobs 均最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `state-check` | `117846703156` | `completed/success` |
| `lean` | `117846703258` | `completed/success` |
| `dashboard / snapshot` | `117847392785` | `completed/success` |

独立读取同次原始 `/tmp/carleman-kuhn-norm-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha` 精确为上述固定 SHA，`finished_at=2026-10-19T01:29:09.148118+00:00`，target 为 `Carleman`。Lean 4.35.0 Linux commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

独立查询远端 artifact 元数据，`lean-ci-result`（ID `12157308661`）和 `lean-declaration-evidence`（ID `12158180370`）均未过期，且各自绑定上述同 run、main 分支和固定 SHA。下载的原始 `/tmp/carleman-kuhn-norm-main-axioms/axioms.txt` 与固定本机副本逐字节完全一致：1,768,650 bytes，SHA256 `252c68da3a4ff05471dddb5ae125493135a7cfd2e8c26373d207ae80f9b498f9`。远端 24 项完整类型和公理结果再次逐项核对，全部 1952 条带公理打印仅含三项正常基础公理，另有 6 条无公理打印，末行确认全库 6057 声明递归审计通过。没有混入后续工作树增量。

最终 **AUXILIARY / PASS**，未发现本批声称范围内的数学缺陷。可将 C107 按 **AUXILIARY / REVIEWED** 记录，原文保持 **13/26**。允许权族、局部 Q_h、FD 和 B.2 不随本报告提升。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
