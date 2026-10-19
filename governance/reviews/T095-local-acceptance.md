# T095 / C111 独立本机验收

- `checked_sha`: `116908340801d3f1cd9f7e940304807f70bdb1ba`
- `base_commit`: `fc89f7ab4516bb6dd97a43a2e5224e722b0b7a56`
- `reviewed_at`: `2026-10-19T02:12:18+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际Kuhn重构的原H¹₀图闭包成员、真实弱梯度、网格统一局部逆估计，以及原Q_h对全部L²输入的局部梯度稳定性。完整B.2、刚度身份和完整FD仍待；原文保持 **13/26**。

独立从固定提交导出四模块，读取全部证明、17项完整展开类型及关键依赖，对照固定 `paper/main.tex` Appendix B Step 2中B.2证明所用的有限元逆估计和局部Q_h稳定性，以及Step 1的原R_h、J_h、Q_h定义。执行者规格及CI没有代替数学核对；后续工作区增量不属于本报告。

## 全部17项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON及固定C111台账一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `coordinatePermutation_symm_norm` | `Geometry/KuhnInverseMap.lean:13` | PASS；实际欧氏范数平方按全坐标置换重排，逆置换严格等距。 |
| 2 | `cartesianKuhn_inverse_map_bound` | `Geometry/KuhnInverseMap.lean:21` | PASS；真实逆映射为先逆对角缩放再逆置换，h/κ≤δⱼ给算子范数≤κ/h。 |
| 3 | `cartesianKuhn_uniform_inverse` | `Spatial/CartesianKuhnInverse.lean:13` | PASS；固定前缀参考单纯形的实际逆界经真实仿射换元，C先于全部物理网格、排列和系数。 |
| 4 | `cartesianFiniteSimplex_uniform_inverse` | `Spatial/CartesianKuhnInverse.lean:26` | PASS；真实有限格点索引代入同一无限格网单元结论，无附加几何前提。 |
| 5 | `cartesianKuhnReconstruction_eq_nodal` | `Spatial/CartesianKuhnReconstructionJet.lean:14` | PASS；原帽函数有限和在每个闭单元及覆盖外均与实际nodalFunction逐点相等。 |
| 6 | `cartesianKuhnReconstructionLp_eq_nodal` | `Spatial/CartesianKuhnReconstructionJet.lean:35` | PASS；真实代表a.e.身份给原重构Lp类与nodalLp严格相等。 |
| 7 | `cartesianKuhnReconstructionLp_mem_dirichlet` | `Spatial/CartesianKuhnReconstructionJet.lean:46` | PASS；真实边界节点数据为零，实际公共面和边界贴合性质供应原H¹₀成员。 |
| 8 | `cartesianKuhnReconstructionJet` | `Spatial/CartesianKuhnReconstructionJet.lean:58` | PASS；从已证明的Dirichlet像空间成员中选择真正WeakSobolevJet。 |
| 9 | `cartesianKuhnReconstructionJet_value` | `Spatial/CartesianKuhnReconstructionJet.lean:64` | PASS；选择出的jet值严格等于原重构Lp类。 |
| 10 | `cartesianKuhnReconstructionJet_mem_dirichlet` | `Spatial/CartesianKuhnReconstructionJet.lean:69` | PASS；同一个jet属于原紧支光滑测试的H¹图范数闭包。 |
| 11 | `cartesianKuhnReconstructionJet_gradient_on_cell` | `Spatial/CartesianKuhnReconstructionJet.lean:75` | PASS；局部弱导数唯一性识别完整第一阶字段，闭单元边界通过零测性处理。 |
| 12 | `cartesianKuhnReconstruction_cell_norm` | `Spatial/CartesianKuhnWeakInverse.lean:16` | PASS；实际单元重构范数精确等于真实节点多项式Lp范数。 |
| 13 | `cartesianKuhnReconstructionJet_cell_gradient_norm` | `Spatial/CartesianKuhnWeakInverse.lean:28` | PASS；真实弱梯度a.e.身份精确给单元完整梯度Lp范数。 |
| 14 | `cartesianKuhnReconstruction_weak_inverse` | `Spatial/CartesianKuhnWeakInverse.lean:39` | PASS；前两项实际范数身份与物理单元逆界组合，覆盖原全部离散状态。 |
| 15 | `cartesianKuhnProjectionJet` | `Spatial/CartesianKuhnWeakInverse.lean:53` | PASS；同一重构jet作用于原J_hu，输入是原全部L²空间。 |
| 16 | `cartesianKuhnProjectionJet_value` | `Spatial/CartesianKuhnWeakInverse.lean:59` | PASS；jet值严格等于原Q_h=R_hJ_h的Lp类。 |
| 17 | `cartesianKuhnProjection_local_gradient_bound` | `Spatial/CartesianKuhnWeakInverse.lean:64` | PASS；真实弱逆界与实际局部Q_h范数界组合，给C/h乘裁剪块上的原输入L²范数。 |

## 物理逆映射及网格统一常数

实际Kuhn单元定义为固定前缀参考单纯形在A=D_δP_π和物理平移b=(oⱼ+zⱼδⱼ)ⱼ下的仿射像。这里P_π的坐标是x_(π⁻¹j)，D_δ逐坐标乘正δⱼ；两者是真正连续线性同构。新证明对P_π⁻¹逐坐标平方求和，用置换的求和等式及范数非负性得到严格等距，未采用依赖排列的任意有限维连续化范数界。

已经读取正对角缩放逆界的实际证明：δⱼ≥h/κ>0推出δⱼ⁻¹≤κ/h，再在欧氏平方和中逐项比较。因此

\[
\|A^{-1}x\|=\|P_\pi^{-1}D_\delta^{-1}x\|\le(\kappa/h)\|x\|,
\qquad \|A^{-1}\|\le\kappa/h.
\]

顺序与原单元定义一致；平移不进入导数。原δⱼ≤h的上步长界在本批逆估计中无需使用，所以保留h/κ≤δⱼ的接口覆盖原可比网格。κ和h严格正，倒数与除法没有零分母问题。

第3项调用的 `affineSimplex_inverse_uniform` 已直接读取。其参考逆界在固定真实单纯形上，先证明实际节点多项式到L²的线性映射单射，再由有限维反Lipschitz界控制全部系数；单射证明使用连续多项式的a.e.相等提升及单元内部稠密性，未评价任意L²代表的节点值。完整梯度系数映射给固定参考逆常数R。

真正仿射换元给值范数平方的J倍缩放和梯度的L∘A⁻¹公式。`derivativeOneFiber_comp_bound` 控制完整欧氏坐标梯度，其常数D只依赖d；使用了真实导数到全部坐标的单射性。J是真实正Jacobian，值和梯度两侧同一J通过准确平方范数身份抵消，没有留下单元体积、排列或平移因子。最终C=DRκ一类常数只依赖固定前缀参考单纯形（因而d）和κ。

完整展开类型为先固定d、κ>0，再∃C>0，之后量化o、δ、hδ、格点／有限N、排列／单元、h>0和步长下界，最后才量化全部系数c或全部离散状态f。C不依赖网格大小、单元数、h、状态或单元选择。

## 原重构的真实H¹₀身份

实际 `cartesianKuhnReconstruction` 是原内部帽函数有限和，内部数据采用全部 `CartesianInteriorIndex N → ℝ`，即每轴1至Nⱼ−1的完整节点数据，物理点外零延拓。第5项在任意实际闭单元上分别使用原重构和nodalFunction的真实单元多项式公式；公共面匹配已经内部证明。没有单元包含x时，真实有限覆盖等于closure Ω给x不在闭包，原每个帽函数与nodalFunction都逐点为零。因此身份在全空间逐点成立，不只是形式系数相同或只在开单元内部成立。

第6项经两侧实际Lp代表得到严格Lp类等式。第7项对每个物理边界顶点，利用开域frontier点不在原域内及真实内部数据零延拓，供应原节点Dirichlet成员定理所要求的零数据。实际Kuhn分割的FaceMatching、BoundaryFitted和原开凸矩形域条件全部由已经构造的几何定理供应。

已直接核对 `dirichletJetSpace` 和 `dirichletSubspace`：前者是全部真实紧支光滑SpatialTest的Sobolev jet线性张成在完整弱H¹图空间中的闭包；后者是该空间在value映射下的像。该图空间由值和完整第一阶Lp字段组成，具有实际分布弱导数身份；拓扑是完整乘积图范数，非仅标量L²拓扑。没有把L²稠密性误用为H¹₀成员。

所复用 `nodalLp_mem_dirichletSubspace` 的证明链也已读取：真实全空间零延拓节点函数为紧支Lipschitz函数；凸域内缩把支撑送入有正缓冲的原域内部，真实卷积近似在H¹中收敛，内缩节点jet又在H¹中趋于原全空间节点jet。限制到原域后，闭包稳定性给所需成员。空域分支单独由真实Lp零类处理，不额外要求非空。

新jet只是从这一已证明存在命题选择见证；其值等式和同一jet的dirichletJetSpace成员都由choose_spec直接获得。它不是新公理化的梯度，也没有要求输入f先满足额外弱正则性或边界条件。

## 全部弱测试、真实单元梯度和Lp范数

第11项使用原 `SimplicialPartition.gradient_on_cell`，其完整证明已读取：闭单元K仅包含在closure Ω；开凸域的正则开性质先给interior K⊆Ω，原jet因而可限制到该开单元内部。原弱限制接口保留全部SpatialTest和分布身份。实际值在此开集a.e.等于局部仿射多项式p。

对每个坐标，真实仿射导数对应CLM并具有实际Lipschitz分部积分公式；弱导数唯一性将限制jet的坐标弱导数识别为fderiv p在该坐标基上的值。有限全部坐标合并给完整 `DerivativeFiber d 1`，其范数是这些真实一阶偏导的欧氏范数。最后真实满维单纯形边界零测，使该身份从interior K延伸为K限制测度下的a.e.身份。没有将相邻单元的经典导数直接宣称为全局弱导数，也没有遗漏物理边界单元。

第12、13项将上述真实代表身份与 `simplexNodalLp_ae`、`simplexNodalGradientLp_ae` 串接，再使用bochnerL2Norm的a.e.不变性和实际Lp范数身份。所有局部字段都真正平方可积：重构是连续紧支函数；原jet第一阶字段属于原域Lp，真实单元限制测度≤原域限制测度；比较的仿射多项式及常梯度分别有真实有限测度Lp构造。因此这些范数没有利用eLpNorm在无穷值处toReal的总化行为。

将这两个精确范数身份代入物理单元逆界，得到原全部离散状态的真实弱逆估计

\[
\|\nabla R_hf\|_{L^2(K)}\le (C/h)\|R_hf\|_{L^2(K)}.
\]

## 同一Q_h及原全部L²输入

`cartesianKuhnProjectionJet` 严格定义为上述同一重构jet作用于原归一化帽矩 `cartesianKuhnMoment u`；其value严格等于原 `cartesianKuhnProjectionLp u`，后者就是R_hJ_hu。J_h输入为任意原域L²类，其每个真实积分的可积性已在旧接口证明；没有对u取节点值或附加H¹、H²、光滑、零迹等假设。

已直接读取所调用局部稳定性和矩估计：真实帽函数的0≤φ≤1、真实质量ω=∏δⱼ和Cauchy–Schwarz给ω(J_hu)_a²≤∫_B u²；原单元质量上界、|K|≤ω及全部顶点求和给常数1的实际局部Q_h范数界。重构及u在相应限制测度下的MemLp均明确供应，开平方合法。

最终右侧使用已验收的实际加宽裁剪块

\[
B_K^+=\Omega\cap\prod_j\bigl(o_j+(z_j-2)\delta_j,\ o_j+(z_j+3)\delta_j\bigr),
\]

它包含活动帽函数的非零支撑，宽度在δⱼ与5δⱼ之间，且具有已证统一有限重叠界。它是明确的加宽块，没有冒充原文最小B_K；这正是前阶段采用并已验收的等价局部证明路线。本阶段仅组合实际逆界和该真实局部L²界，得到

\[
\|\nabla Q_hu\|_{L^2(K)}\le(C/h)\|u\|_{L^2(B_K^+)}
\]

且C仍在全部网格、单元、h和u之前选定，没有新增块数量或全局状态因子。d=0和不存在有限单元的退化索引情形均由原类型保留；原d≥1、正可比网格全部包含。

本批完成B.2所需的真实弱逆估计和局部梯度稳定性。原全部H²∩H¹₀状态的误差分解、允许权局部比较及全域有限重叠组合仍不是本批结论；没有把上述辅助界提升为完整B.2或完整FD。

## 固定依赖、构建与公理证据

四模块Carleman导入闭包共207模块，203旧模块与base完全不变，新增恰为本批四模块。关键已验收版本也已逐模块比较：C061 SimplexReferenceInverse的33模块闭包相对 `6cbca2eb3813801b491d54b7f442834ded59d83c` 不变；C062 AffineSimplexInverse的43模块闭包相对 `0c632f37eadbcece6459555fef22a2bb4b3ca688` 不变；C060 NodalDirichletMembership的113模块闭包相对 `50ea3111057c5d7b796cca799c10a9a900d14caf` 不变；C064 SimplicialLocalGradient的83模块闭包相对 `2ccd0e5f1ae783f69c70d18593e09c79dfe7d7bd` 不变；C103 CartesianKuhnNodal的139模块闭包相对 `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a` 不变；C109 CartesianKuhnPatchProjection的186模块闭包相对 `ba9aa5d2a3caf655bba037695fe733a3f292d952` 不变。关键数学依赖已直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入四模块，`tools/CheckAxioms.lean` 包含17项完整类型和公理输出，并通过privateToUserName遍历全部Carleman声明、递归collectAxioms。

17项完整展开类型已逐项核对。固定本机2029条显式公理记录中2023非空、6无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理或sorryAx。实际定向日志为3385 jobs；`/tmp/carleman-kuhn-weak-inverse-full.log` 包含 `Build completed successfully (3788 jobs).` 和 `Axiom audit passed for all 6146 Carleman declarations.`。固定本机 `/tmp/carleman-kuhn-weak-inverse-local-axioms.txt` 为 **1,819,578 bytes**，SHA256 **`d516348a2bc0c01141a73e02d3fe5327e1e7b9dd58370ba905eaf072986bdda4`**。

已独立通过GitHub connector读取 [main CI 39188529418 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39188529418/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117855989329）、state-check（117855989560）、dashboard / snapshot（117856681454）三项jobs全部completed/success，其实际步骤均success。同run的lean-ci-result（12158579661）和lean-declaration-evidence（12158579663）artifact元数据均绑定固定SHA。

本验收Agent已自行通过 `gh run download 39188529418` 下载同run的两份原始artifact。实际读取 `/tmp/carleman-kuhn-weak-inverse-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=116908340801d3f1cd9f7e940304807f70bdb1ba`，targets为Carleman，`finished_at=2026-10-19T02:10:04.625176+00:00`，ci_url精确对应上述run/attempt。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-kuhn-weak-inverse-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,819,578 bytes**，SHA256 **`d516348a2bc0c01141a73e02d3fe5327e1e7b9dd58370ba905eaf072986bdda4`**。另逐名核对远端17/17完整展开类型及公理，2029条显式记录均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 6146 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C111：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定17项未发现物理逆映射、常数量词、原H¹₀图闭包、实际弱梯度、单元范数或全部L²输入的Q_h局部稳定性方面需要修复的缺陷；同SHA正式三项CI及自行下载的原始公理证据已独立核实。完整B.2/P026、FD/P012及其他原文命题不因本批提升，原文保持 **13/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
