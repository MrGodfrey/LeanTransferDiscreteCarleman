# T087 / C103 独立本机验收

- `checked_sha`: `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a`
- `base_commit`: `e753eb065d87695d33e31c141cfe15c7cea4b5de`
- `reviewed_at`: `2026-10-19T00:54:46+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**（固定本机与同次远端原始产物逐字节一致）
- `scope`: **AUXILIARY**
- 范围：真实 Kuhn 公共面匹配、矩形边界贴合、实际有限单纯形分区、连续内部节点帽函数与原 H¹₀ 成员，以及真实函数支撑／拓扑支撑的有限节点星包含。节点矩、载荷、Q_h 和完整 FD/B.2 仍待；原文保持 **13/26**。

独立以 `git show` 读取固定六模块全部源码、43项完整展开类型和关键依赖，对照原 `paper/main.tex` Section 6（TeX 1634–1658、1688）及 Appendix B（TeX 2747–2789、2854–2869）。规格与执行者说明只用于定位，未代替实际数学核对；后续工作树不属本次验收。

## 全部43项声明

下表省略名称公共前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付清单一致。

| # | 声明 | 固定位置 | 独立结论 |
|---|---|---|---|
| 1 | `integer_weighted_le_of_pos` | `Spatial/SimplexPositiveSupport.lean:12` | PASS；整数宽度、非负权和为1及严格正权，真实推出整数上界；严格矛盾由单个正项供应。 |
| 2 | `simplexBarycentric_reconstruct` | `Spatial/SimplexPositiveSupport.lean:35` | PASS；实际 AffineBasis 重心坐标的向量加权和精确重构任意空间点。 |
| 3 | `simplex_mem_convexHull_positive_support` | `Spatial/SimplexPositiveSupport.lean:42` | PASS；零权项真正消去；正权有限支撑的和仍为1，得到真实凸包成员。 |
| 4 | `simplex_integer_affine_le_of_pos` | `Spatial/SimplexPositiveSupport.lean:62` | PASS；任意仿射泛函通过真实节点再现身份，准确化归整数加权引理。 |
| 5 | `cartesianGridPoint` | `Geometry/KuhnLatticeCoordinates.lean:13` | PASS；实际格点为 o+zδ，以欧氏空间坐标包装。 |
| 6 | `cartesianGridCoordinate` | `Geometry/KuhnLatticeCoordinates.lean:16` | PASS；实际归一化坐标仿射泛函，线性部分为 δ_j⁻¹ 投影，常数为 −o_j/δ_j。 |
| 7 | `cartesianGridCoordinate_apply` | `Geometry/KuhnLatticeCoordinates.lean:21` | PASS；精确求值得到 (x_j−o_j)/δ_j。 |
| 8 | `cartesianGridCoordinate_point` | `Geometry/KuhnLatticeCoordinates.lean:26` | PASS；正步长保证除法合法，真实格点求值还原整数 z_j。 |
| 9 | `kuhnVertexIndex` | `Geometry/KuhnLatticeCoordinates.lean:34` | PASS；真实顶点整数索引为 z_j+1_(π⁻¹j<k)。 |
| 10 | `cartesianKuhnSimplex_points_eq_gridPoint` | `Geometry/KuhnLatticeCoordinates.lean:37` | PASS；原物理 Kuhn 顶点确为上述真实格点。 |
| 11 | `cartesianGridCoordinate_vertex` | `Geometry/KuhnLatticeCoordinates.lean:46` | PASS；归一化泛函在每个真实顶点的值精确等于对应整数。 |
| 12 | `kuhnVertexIndex_width` | `Geometry/KuhnLatticeCoordinates.lean:52` | PASS；同一坐标在全部顶点之间整数宽度至多1。 |
| 13 | `kuhnVertexIndex_difference_width` | `Geometry/KuhnLatticeCoordinates.lean:58` | PASS；利用同一前缀阈值的嵌套次序，坐标差整数宽度也至多1，非错误宽度2。 |
| 14 | `cartesianKuhn_positive_vertex_upper` | `Geometry/KuhnLatticeCoordinates.lean:65` | PASS；整数坐标上半空间约束传给所有正重心系数顶点。 |
| 15 | `cartesianKuhn_positive_vertex_lower` | `Geometry/KuhnLatticeCoordinates.lean:75` | PASS；取负仿射泛函并反转宽度指标，得到对应下半空间约束。 |
| 16 | `cartesianKuhn_positive_vertex_difference` | `Geometry/KuhnLatticeCoordinates.lean:88` | PASS；实际两个归一化坐标之差的约束，传给所有正重心系数顶点。 |
| 17 | `cartesianKuhn_gridPoint_is_vertex` | `Geometry/KuhnFaceMatching.lean:14` | PASS；真实闭单元中的任意格点必等于一个实际顶点，未额外假设节点枚举。 |
| 18 | `cartesianKuhn_positive_vertex_mem_other` | `Geometry/KuhnFaceMatching.lean:36` | PASS；另一单元的全部坐标和排序半空间传给正系数顶点，得到真实成员资格。 |
| 19 | `cartesianKuhn_cells_common_face` | `Geometry/KuhnFaceMatching.lean:71` | PASS；整个闭单元交集位于公共顶点真实凸包，包含所有低维公共面。 |
| 20 | `cartesianKuhnPartition` | `Geometry/KuhnFaceMatching.lean:85` | PASS；实际有限网格构造完整 SimplicialPartition；闭包内含、开域覆盖与内部不交均内部供应。 |
| 21 | `cartesianKuhnPartition_faceMatching` | `Geometry/KuhnFaceMatching.lean:110` | PASS；把无限网格实际公共面定理用于每对有限单元，内部清偿 FaceMatching。 |
| 22 | `simplex_affine_min_eq_of_pos` | `Spatial/SimplexCoordinateBoundary.lean:14` | PASS；非负差值加权和为零，严格正权项的仿射值精确达到最小值。 |
| 23 | `simplex_coordinateBox_boundary_support` | `Spatial/SimplexCoordinateBoundary.lean:30` | PASS；边界点落某实际坐标面；正系数顶点同样落在该面及真实 frontier。 |
| 24 | `cartesianKuhnPartition_boundaryFitted` | `Spatial/CartesianKuhnNodal.lean:16` | PASS；原有限矩形网格的 BoundaryFitted 由真实正重心边界支撑内部供应。 |
| 25 | `cartesianKuhnHat` | `Spatial/CartesianKuhnNodal.lean:30` | PASS；真实格点 Kronecker 数据经实际局部仿射插值及全局选单元定义帽函数。 |
| 26 | `cartesianKuhnHat_on_cell` | `Spatial/CartesianKuhnNodal.lean:35` | PASS；每个整个闭单元上精确等于 Kronecker 系数乘实际重心坐标的和。 |
| 27 | `cartesianKuhnHat_vertex` | `Spatial/CartesianKuhnNodal.lean:47` | PASS；每个实际网格顶点的帽函数值精确为 Kronecker 值。 |
| 28 | `cartesianKuhnHat_data_boundary` | `Spatial/CartesianKuhnNodal.lean:54` | PASS；节点在原开域内时，与任何真实边界点不同，数据自动为零。 |
| 29 | `cartesianKuhnHat_continuous` | `Spatial/CartesianKuhnNodal.lean:63` | PASS；仅对内部节点声称全空间连续；公共面和边界贴合均由本批内部供应。 |
| 30 | `cartesianKuhnHat_zero_compl` | `Spatial/CartesianKuhnNodal.lean:72` | PASS；内部节点帽函数在整个域补集为零，包括物理边界。 |
| 31 | `cartesianKuhnHat_compact` | `Spatial/CartesianKuhnNodal.lean:82` | PASS；对任意格点数据，有限闭单元并给真实紧支撑。 |
| 32 | `cartesianKuhnHat_nonneg` | `Spatial/CartesianKuhnNodal.lean:86` | PASS；真实重心坐标非负与域外零给全空间点态非负。 |
| 33 | `cartesianKuhnHat_le_one` | `Spatial/CartesianKuhnNodal.lean:99` | PASS；实际插值稳定常数1与域外零给全空间点态上界1。 |
| 34 | `cartesianKuhnHatLp` | `Spatial/CartesianKuhnNodal.lean:114` | PASS；以真实有限测度上的 nodalFunction.toLp 构造原域 L² 等价类。 |
| 35 | `cartesianKuhnHatLp_ae` | `Spatial/CartesianKuhnNodal.lean:121` | PASS；该真实 L² 类几乎处处等于所构造的帽函数。 |
| 36 | `cartesianKuhnHatLp_mem_dirichlet` | `Spatial/CartesianKuhnNodal.lean:128` | PASS；内部节点的原 H¹₀ 图闭包成员资格，非另定义的点态零边界空间。 |
| 37 | `cartesianKuhnHat_on_incidentCell` | `Spatial/CartesianKuhnHatSupport.lean:13` | PASS；单纯形顶点单射性消去其余项，含节点单元上精确等于对应重心坐标。 |
| 38 | `cartesianKuhnHat_zero_on_nonincidentCell` | `Spatial/CartesianKuhnHatSupport.lean:22` | PASS；不含该节点的整个闭单元上帽函数恒零。 |
| 39 | `cartesianFiniteNodeStar` | `Spatial/CartesianKuhnHatSupport.lean:32` | PASS；真实有限节点星为所有确实含该节点的闭单元之并。 |
| 40 | `cartesianFiniteNodeStar_compact` | `Spatial/CartesianKuhnHatSupport.lean:38` | PASS；有限条件单元并紧，未把无限并或一般有界性当作紧性。 |
| 41 | `cartesianKuhnHat_support_subset` | `Spatial/CartesianKuhnHatSupport.lean:46` | PASS；真实非零函数支撑包含于节点星，使用整个闭域覆盖及非相邻单元零。 |
| 42 | `cartesianKuhnHat_tsupport_subset` | `Spatial/CartesianKuhnHatSupport.lean:61` | PASS；节点星闭，由支撑包含取闭包给真实拓扑支撑包含。 |
| 43 | `cartesianKuhnHat_tsupport_subset_cellStar` | `Spatial/CartesianKuhnHatSupport.lean:67` | PASS；任一关联单元与节点星中单元共享该实际顶点，拓扑支撑因此进入 T085 完整单元星。 |

## 整数宽度与真正公共面

`integer_weighted_le_of_pos` 的假设是整数 g_i、非负权 w_i、总和1、所有两两整数差上界1，以及真实平均不超过整数 c。若某个正权项 g_k>c，整性给 g_k≥c+1；宽度给所有 g_i≥c。于是所有 w_i(g_i−c) 非负，第 k 项严格正，总和严格正，却又等于平均减 c≤0，矛盾。这里严格正权不可省略；代码只向正重心系数顶点传递半空间限制，没有错误控制零系数顶点。

真实 `simplexBarycentric` 是完整 AffineBasis 的坐标。向量重构来自实际 affineCombination 身份，和为1用于转换成向量线性组合。对凸包点，重心坐标非负；过滤正项后，其余项确为零，实际有限和仍为1，向量重构不变。因此“只用正系数顶点”的凸包结论对任意目标顶点集合成立，没有把支撑本身作为额外输入。

真实归一化坐标为 a_j(x)=(x_j−o_j)/δ_j；原物理顶点 v_k 的值为整数 z_j+1_(π⁻¹j<k)。每个坐标值的宽度显然至多1，但公共面证明还需要坐标差的宽度。代码对同一前缀阈值的全部分支用整数次序证明该事实：若 π⁻¹i<π⁻¹j，则两个指示值之差只取0或1；反次序只取0或−1，相等时恒为0。因此同一单元不同顶点之间的差宽度仍为1，而非把两个独立0/1增量误算成此结论。真实排列、共同阈值和完整分支条件均保留。

对真实单元内格点 x=o+aδ，重心和为1保证存在正系数顶点。该格点的每个归一化坐标精确为整数 a_j，将上下半空间约束传到这个正顶点，得到其全部整数坐标等于 a；真实顶点公式遂证明 x 正是该顶点。这不是对“格点就是顶点”的先验假设。

若 x 同时属于两个闭 Kuhn 单元，直接使用已验收、此次又读取的 `cartesianKuhnSimplex_mem_iff`：第二单元的全部归一化坐标在其整数格点的[0,1]区间，沿其排列递减。对第一单元每个正系数顶点，坐标上下界通过整数宽度引理传递，沿第二排列的每个坐标差约束也通过差宽度传递；其阈值为第二格点坐标的真实整数差。故该顶点满足第二单元的完整充分必要半空间刻画，真正属于它。再由上面的“格点即顶点”证明其是第二单元顶点。

因此 x 是公共顶点的真实凸组合，得到整个闭交集包含于公共顶点凸包。被供应的 `FaceMatching` 定义恰是这个包含；反向包含由两单元凸性立即成立，但本批没有将一个未声明的相交集合等式列为额外成果。证明适用于不同格点、不同排列、相同单元及仅共享低维面的情形，没有忽略单元边界或用 a.e. 结论代替公共面匹配。

## 实际有限分区和矩形边界

有限索引仍为 `(∀j, Fin(N_j)) × Perm(Fin d)`，单元仍为原 `cartesianFiniteSimplex`。新结构的 `inside` 用实际单元闭格点盒包含，及每个合法有限索引 0≤i_j、i_j+1≤N_j，将整个闭单元放入原矩形闭包。证明只在实际索引存在时从 Fin(N_j) 推出 N_j>0，之后使用真实开盒闭包公式；没有无条件假设原空盒等于退化闭盒。`cover` 和 `disjoint` 直接调用 T086 的实际全开域覆盖和有限族内部不交。由有限闭单元并可得其并恰为域闭包，此旧接口亦已读取。

`simplex_affine_min_eq_of_pos` 对一般真实仿射泛函 p 证明支撑面性质：若所有顶点值≥c，而某凸包点 p(x)=c，则 Σ(p(v_i)−c)λ_i(x)=0。所有项非负；任何正 λ_k 强制 p(v_k)=c。矩形边界点由闭盒成员且不在开盒内，必有至少一个坐标等于下端点或上端点；分别对坐标投影或其负值应用该引理。所有正系数顶点落在同一个实际坐标面，且已在整个闭盒内，故属于真实 frontier。棱角无需单独光滑性或唯一法向。

该边界支撑与正系数凸包重构精确供应 `BoundaryFitted` 的定义，即单元与 frontier 的交集包含于其边界顶点的凸包。它来自原矩形和实际网格，不是要求调用者提供 BoundaryFitted、几何面一致或任何 Sobolev 零迹假设。

全部新网格声明允许任意 N_j∈ℕ。若 d>0 且某 N_j=0，有限索引为空、原开域为空，分区及帽函数结论相应退化；包含条件下不产生非法 Fin 0 元素。d=0时欧氏空间、格点函数及排列各只有一个元素，唯一单元覆盖全空间唯一点，边界为空，所有坐标及边界论证正确退化。原论文 d≥1、N_j≥2、步长互相可比是这些几何构造的特例；这里无需可比性，但也没有据此声称原数值误差常数与可比性无关。

## 实际帽函数、原 L² 类与 H¹₀ 闭包

帽函数的数据是实际点函数 `if x=cartesianGridPoint o δ a then 1 else 0`，没有对任意 L² 或 H² 等价类取节点值。`nodalFunction` 在一个包含 x 的真实单元上选用实际重心仿射插值，域闭包外取零。此次已直接读取拼接证明：两个局部仿射插值在公共顶点取同一数据，因而在公共顶点仿射张成、继而整个实际公共面相等，消除选单元的不确定性；有限闭覆盖拼接给闭域上的连续性。

每个闭单元上的帽函数严格等于 Kronecker 数据乘实际重心坐标的和。原单纯形的仿射独立保证顶点单射；若指定格点为该单元第 k 顶点，只有 k 项非零，故帽函数精确为 λ_k。若节点不在该单元顶点集合中，所有项为零。这两结论均包括单元面和边，不仅单元内部。每个实际顶点的 Kronecker 值也直接核实。任意内部格点确有实际关联顶点，可由原开域覆盖及本批格点即顶点定理组合，不需要额外节点枚举前提。

全空间非负性来自重心坐标非负和域外零；上界1来自真实局部插值稳定常数1及域外零。任意格点的帽函数均有紧支撑，因有限闭单元并紧。全空间连续、在域补集恒零及 H¹₀ 成员资格则仅对实际内部格点声称；本报告没有将这些推广到边界节点。所需 `ha` 是格点在原开矩形内，正步长下等价于原内部整数指标条件0<a_j<N_j，是原内部节点选择而非额外零迹假设。其 Kronecker 数据在任何实际边界点自动为零，已由开域与 frontier 不交内部证明。

`cartesianKuhnHatLp` 是原开域限制 Lebesgue 测度下真实 `Lp ℝ 2` 对象，由局部连续、有限测度和有界性证明 MemLp 后构造；`cartesianKuhnHatLp_ae` 正确把该类的 a.e. 代表识别为实际帽函数。没有把点值相等误作等价类处处相等，也没有自由假设可积性。

H¹₀ 使用旧定义 `dirichletJetSpace = closure(span{φ.sobolevJet | φ : SpatialTest S})` 在完整弱 H¹ 图空间中的闭包，再取其 value 像 `dirichletSubspace`。`SpatialTest` 是全部全空间 C∞、紧支撑且拓扑支撑包含于 S 的真实测试函数，弱导数要求对全部这些测试的真实积分分部身份。此次读取这些定义及 `NodalDirichletMembership` 的实际调用链：几何拼接和边界数据给全空间紧支 Lipschitz 节点函数；向内部收缩后支撑严格在开凸域内；真实光滑卷积强 H¹ 逼近给收缩函数的原图闭包成员，再用收缩 H¹ 极限与闭性得到原节点函数；限制真实全空间弱 jet 后以 L² a.e. 身份识别原帽函数类。最后代码还包含原空域分支。

新入口内部供应开性、凸性、FaceMatching、BoundaryFitted 和边界数据零，未遗留弱导数存在、额外正则代表、光滑逼近或零迹输入。已有 Lipschitz／H¹ 成员资格证明中的网格相关有限常数仅用于存在性，不是本批声称的统一误差常数；本批唯一新帽函数大小常数为真实点态0和1，先于任意网格、节点和空间点。

## 真实支撑而非预设支撑区域

`cartesianFiniteNodeStar` 直接遍历原全部有限单元，仅在其真实顶点集合含指定格点时取该整个闭单元，否则取空集。它是实际有限节点星，而不是较大的方便格点窗口。每个单元为有限顶点的真实凸包，紧；有限条件并紧，因而闭。

对函数非零点，帽函数定义的域外零先给该点在域闭包内；真实闭单元覆盖选出一个单元。若此单元不含该节点，则本批精确非关联单元零定理矛盾。因此非零点属于真实节点星。对该包含取闭包，并用节点星闭性得到整个 `tsupport` 包含。这里保留了拓扑支撑可能含函数零值点的差异，也不要求先假设帽函数连续才能使用闭包最小性。

最后对任意确实含该节点的单元 i，节点星中的单元 j 也含同一实际点；两次 range 见证给真实顶点等式 v_i(k)=v_j(l)。这正好构成 T085 `cartesianKuhnStarPatch` 的共享顶点见证。目标是以 i 为中心、遍历完整无限同向格网的单元星并集，而非将其与有限单节点星混为一谈。因此得到实际帽函数拓扑支撑的所需包含，可接到 T085/T086 已证格点块和重数界。

本批没有证明支撑与节点星相等、内部节点有限星等于完整无限节点星、中心对称、分片基的整体单位分解、零阶／一阶矩或质量积分。尤其拓扑支撑包含本身不能推出原 Appendix B 的中心对称和矩身份。

## 原文映射和依赖边界

原 Section 6 TeX1656–1658 的同向 Kuhn 划分与内部节点基 φ_i，现在具有真实有限分区、跨面匹配、连续零延拓、原 H¹₀ 成员与实际支撑基础。TeX1688 的原顶点步进公式沿用已验收的真实单纯形。Appendix B TeX2789 所需活跃节点支撑进入局部块，本批提供真实支撑到共享顶点星的连接；尚未据此构造完整 R_h、J_h、G_h、Q_h 或证明其稳定性。

原 TeX2747–2774 的完整内部星、中心对称、节点矩、载荷右逆与稳定性，以及 TeX2854–2869 的矩再现、Q_h 局部与全域加权逼近仍待。本批不提升 FD/P012、B.2/P026 或其他原文命题；固定覆盖表中13项 REVIEWED/PAPER 保持不变，P012、P026仍为 PLANNED。

六新模块 Carleman 导入闭包共140模块，其中134旧模块与基线逐字相同。关键已验收版本另行递归比较：NodalDirichletMembership 的113模块闭包相对 T044 固定 `50ea3111057c5d7b796cca799c10a9a900d14caf` 完全不变；KuhnCellInterior 的106模块闭包相对 T086 固定基线完全不变；KuhnVertexStars 的102模块闭包相对 T085 固定 `e52ffb4aed1df34fbcb1839e9472abafa927abfd` 完全不变。依赖验收分别见 [T044](T044-local-acceptance.md)、[T085](T085-local-acceptance.md)、[T086](T086-local-acceptance.md)。本次另读取真实重心插值、半空间刻画、有限覆盖和内部不交、FaceMatching／BoundaryFitted 定义、nodalFunction 选择一致性、L²构造、原 H¹₀ 定义及内缩／光滑闭包调用，确认新实例确实满足全部依赖条件。

## 构建、公理和同 SHA 远端证据

固定定向 `/tmp/carleman-kuhn-conforming-target.log` 实际为3310 jobs成功；全库 `/tmp/carleman-kuhn-conforming-full.log` 实际为3750 jobs成功，并含 `Axiom audit passed for all 5951 Carleman declarations.`。固定 `/tmp/carleman-kuhn-conforming-local-axioms.txt` 为 **1,727,744 bytes**，SHA256 **`f61421119edd8f102da8a34bff7c326effc8cace06b0f19a27e7323e151bd0a8`**。

43/43项完整展开类型逐项核对，每项各有一条显式公理记录，均仅依赖正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 的子集。全文件1875条显式记录中1872条列出非空基础公理、3条无公理，共1871个不同声明；没有白名单外依赖或 sorryAx。递归审计包含生成辅助声明。六新模块无 sorry/admit/axiom/unsafe，root 明确导入全部六模块；CheckAxioms 增量仅增加43项 #check/#print，原全局递归审计未削弱。

原稿、治理协议、工具链 pin 和 CI 工作流未由本批改变；原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean pin 为4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。

已独立通过 GitHub API 读取 [main CI 39182503383 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39182503383/attempts/1)：main/push，head SHA 精确为固定证明版本，run 为 completed/success。state-check `117838057304`（00:49:41Z）、lean `117838057484`（00:52:13Z）、dashboard / snapshot `117838670432`（00:52:26Z）三项 job 均绑定同 SHA，全部 completed/success。

实际 artifact 元数据将 `lean-ci-result`（`12157325115`）与 `lean-declaration-evidence`（`12157145727`）绑定到同 run、main 分支及本报告 SHA，均未过期。已独立读取 `/tmp/carleman-kuhn-conforming-main-ci/result.json`：status=PASS，checked_sha=source_head_sha=`7b2627620e04ad9b44e6bee31fab8a241d4f4d1a`，targets 为 Carleman，finished_at=`2026-10-19T00:51:17.700483+00:00`，ci_url 精确对应上述 run/attempt。实际 Lean 4.35.0 和 mathlib commit 与固定 pin 一致。

实际远端 `/tmp/carleman-kuhn-conforming-main-axioms/axioms.txt` 与上述固定本机副本逐字节相同：**1,727,744 bytes**，SHA256 **`f61421119edd8f102da8a34bff7c326effc8cace06b0f19a27e7323e151bd0a8`**。另逐名核对远端43/43完整类型及各自公理记录，重新扫描全部1875条显式记录，无非基础公理；末行确认全部 **5951** 声明递归审计 PASS。交付 JSON、固定 C103/T087 台账以及报告表格的43项名单也精确一致。未使用其他 SHA 或后续工作树产物替代这些证据。

## 验收决定

**C103：PASS，可按 AUXILIARY 升为 REVIEWED。** 43项语义核对未发现整数宽度、公共面、真实分区、边界贴合、内部节点数据、全空间连续性、原 H¹₀ 资格、a.e. 类或实际拓扑支撑方面的缺陷。同 SHA 三项最终 CI 与原始远端公理证据已独立核实；本阶段不提升 P012/P026 或其他尚未完成的原文命题，原文仍为 **13/26**。

本次仅写本报告，未修改实现、台账、原稿或 root 导入，未 commit/push。范围保持 AUXILIARY，原文保持13/26。
