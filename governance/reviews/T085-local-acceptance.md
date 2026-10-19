# T085 / C101 独立本机验收

- `checked_sha`: `e52ffb4aed1df34fbcb1839e9472abafa927abfd`
- `base_commit`: `d8ccc85628961e226550d9fea095eac9710ed969`
- `reviewed_at`: `2026-10-19T00:32:39+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**（固定本机与同次远端产物逐字节相同）
- `scope`: **AUXILIARY**
- 范围：真实标准／前缀／物理 Kuhn 单纯形及其顶点公式；固定单元各顶点星的完整并集、有限紧并表示、可测性和对有限无重复索引族的实际 `5^d d!` 重数界。未完成单元覆盖、内部不交、帽函数、矩或 Q_h；原文保持 **13/26**。

直接以 `git show` 读取固定三模块全部证明、24项实际展开类型及关键依赖，对照原 `paper/main.tex` Section 6 的 Cartesian/Kuhn 设置（TeX 1634–1658）及 Appendix B 的局部支撑块／有界重叠（TeX 2783–2789、2854–2869）。未以执行者规格、已有验收或 CI 代替数学核对；后续工作树增量不属范围。

## 全部24项声明

名称省略共同前缀 `Carleman.`；固定位置以 `Carleman/` 为根，顺序与交付 JSON、C101/T085 名单一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `coordinateStandardSimplex` | `Geometry/KuhnReferenceSimplex.lean:14` | PASS；实际顶点为0与标准欧氏基，仿射无关性由去零顶点后的真实基线性无关性证明。 |
| 2 | `kuhnPrefixMatrix` | `Geometry/KuhnReferenceSimplex.lean:29` | PASS；真实矩阵为 M_ij=1 当 i≤j，否则0。 |
| 3 | `kuhnPrefixMatrix_det` | `Geometry/KuhnReferenceSimplex.lean:32` | PASS；下三角严格位置为零、对角均1，实际行列式等于1，含空矩阵。 |
| 4 | `kuhnPrefixEquiv` | `Geometry/KuhnReferenceSimplex.lean:40` | PASS；由实际 det 为单位构造真正线性等价，有限维保证连续线性等价。 |
| 5 | `kuhnPrefixEquiv_basis` | `Geometry/KuhnReferenceSimplex.lean:44` | PASS；对第 i 个标准基，实际第 j 坐标为1_(j≤i)，矩阵行列方向正确。 |
| 6 | `kuhnReferenceSimplex` | `Geometry/KuhnReferenceSimplex.lean:56` | PASS；标准单纯形通过真实可逆前缀映射的仿射像，保留仿射无关性。 |
| 7 | `kuhnReferenceSimplex_points` | `Geometry/KuhnReferenceSimplex.lean:59` | PASS；实际第 k 顶点第 j 坐标为1_(j<k)，包括首尾顶点。 |
| 8 | `coordinatePermutation` | `Geometry/CartesianKuhnSimplex.lean:14` | PASS；真实坐标排列 x_j↦x_(π⁻¹j)，逆为 x_j↦x_(πj)，两边逆身份及线性均证明。 |
| 9 | `coordinatePermutation_apply` | `Geometry/CartesianKuhnSimplex.lean:24` | PASS；明确实际坐标公式，未交换 π 与 π⁻¹。 |
| 10 | `cartesianKuhnSimplex` | `Geometry/CartesianKuhnSimplex.lean:27` | PASS；前缀单纯形依次经坐标排列、正步长对角缩放及 o+zδ 平移构成真实物理单纯形。 |
| 11 | `cartesianKuhnSimplex_points` | `Geometry/CartesianKuhnSimplex.lean:32` | PASS；顶点精确为 o_j+(z_j+1_(π⁻¹j<k))δ_j。 |
| 12 | `cartesianKuhnSimplex_points_step` | `Geometry/CartesianKuhnSimplex.lean:42` | PASS；相邻两顶点差为 δ_(πk)e_(πk)，其他坐标严格消去。 |
| 13 | `closedCoordinateBox_convex` | `Geometry/CartesianKuhnSimplex.lean:64` | PASS；真实闭盒是坐标线性投影的闭区间原像之交，凸性内部证明。 |
| 14 | `cartesianKuhnSimplex_cell_subset_box` | `Geometry/CartesianKuhnSimplex.lean:72` | PASS；所有实际顶点在其格点闭盒内，凸包最小性覆盖整个闭单元。 |
| 15 | `cartesianKuhnSimplex_cell_subset_patch` | `Geometry/CartesianKuhnSimplex.lean:81` | PASS；正步长把闭格点盒严格放入半径1实际开扩张块，包含单元边界。 |
| 16 | `cartesianKuhn_shared_vertex_index_bound` | `Geometry/KuhnVertexStars.lean:12` | PASS；真实共享顶点等式按坐标约去非零步长，0/1 顶点增量给整数 z_j−1≤z′_j≤z_j+1。 |
| 17 | `cartesianKuhn_shared_vertex_cell_subset` | `Geometry/KuhnVertexStars.lean:26` | PASS；邻格点界与该单元真实闭盒包含组合，整个邻单元在 [o+(z−1)δ,o+(z+2)δ] 内。 |
| 18 | `cartesianKuhnStarPatch` | `Geometry/KuhnVertexStars.lean:42` | PASS；遍历全部整数格点、全部排列与双方全部顶点，仅纳入确实共享顶点的真实闭单元。 |
| 19 | `cartesianKuhnStarPatch_subset_patch` | `Geometry/KuhnVertexStars.lean:49` | PASS；完整无限格网星并集严格包含于半径2实际开扩张块。 |
| 20 | `cartesianKuhnStarPatch_multiplicity_le` | `Geometry/KuhnVertexStars.lean:57` | PASS；对任意有限注入格点／排列族，以实际星包含供应 T084 前提，真实重数≤5^d d!。 |
| 21 | `cartesianKuhn_cell_subset_starPatch` | `Geometry/KuhnVertexStars.lean:67` | PASS；取同一单元及其第0顶点，原整个单元属于星并集。 |
| 22 | `cartesianKuhnStarPatch_eq_finite_union` | `Geometry/KuhnVertexStars.lean:72` | PASS；与实际邻近整数窗口、所有排列及共享顶点条件上的有限并严格双向相等。 |
| 23 | `cartesianKuhnStarPatch_compact` | `Geometry/KuhnVertexStars.lean:99` | PASS；每个真实有限顶点凸包紧，条件未满足时为空，两个有限并保持紧性。 |
| 24 | `cartesianKuhnStarPatch_measurable` | `Geometry/KuhnVertexStars.lean:112` | PASS；实际 Euclidean 空间中紧集闭，再由 Borel 可测性得到可测集合。 |

## 标准与前缀单纯形的真实构造

`coordinateStandardSimplex d` 的类型是实际 `Affine.Simplex ℝ (SpatialCoordinates d) d`，不是任意顶点数组配一个尚未证明的仿射无关前提。顶点为 `Fin.cons 0 basisFun`。以0号顶点为基点，去掉它后通过 Fin.pred 把剩余索引单射映到 Fin d；相对位移恰为原欧氏坐标基。证明调用该真实基的线性无关性与单射重索引，逐项识别后得到完整仿射无关性。

真实前缀矩阵 M 的第 i 行第 j 列为1_(i≤j)。严格下三角元素为零，真实上三角行列式定理给 det M 等于对角乘积1。`Matrix.toLinearEquiv` 在实际欧氏基下使用这个 det 单位证明构造可逆线性映射，再由有限维变为连续线性等价；并未用未证明逆矩阵或添加可逆性公理。

`kuhnPrefixEquiv_basis` 展开真实矩阵对应线性映射，把其第 i 列在基上求和，再用第 j 坐标投影计算，得到1_(j≤i)。标准单纯形第0顶点映到0，第 k+1 顶点映到 e₀+⋯+e_k。故参考单纯形确为 `0,e₀,e₀+e₁,…,e₀+⋯+e_(d−1)`，其第 k 顶点坐标是1_(j<k)。`affineSimplex` 依赖通过实际仿射等价的单射性映射原 Affine.Simplex，因此这些新顶点真正仿射无关，而不是只命名为单纯形。

所有基础声明允许 d=0：此时单纯形有唯一顶点，排除0后的索引为空、矩阵为空且行列式为空积1；最终参考点公式按空坐标真，未选择不存在的坐标。原论文 d≥1 是其特例，不构成范围收缩。

## 物理顶点、排列方向与整个闭单元

坐标排列实际为 `(P_πx)_j=x_(π⁻¹j)`，逆为 x_(πj)。正步长对角映射 D_δ 的逆逐坐标用 δ_j⁻¹，δ_j>0 保证非零；它也是实际连续线性等价。物理单纯形采用 `D_δ∘P_π`，再平移 o+zδ，故实际顶点公式为

`v_k(j)=o_j+(z_j+1_((π⁻¹j).val<k.val))δ_j`。

计算 v_(k+1)−v_k 时，j=π(k) 的指示值由0变1，产生 δ_(πk)；其他 j 有 π⁻¹j≠k，前后严格不等式条件等价，差为零。因此真实步进为 δ_(πk)e_(πk)，与原文每盒采用相同方向的 Kuhn 排列构造吻合。原点可任意，格点是全部整数向量，步长可各向异性；代码不要求固定有限网格或额外比例界。

`simplicialCell` 已直接核对为 `convexHull ℝ (range points)`。每个真实顶点各坐标取闭格点盒的一个端点；闭盒本身凸，凸包最小性给整个单元包含，而非仅顶点或内部点。闭格点盒位于开扩张块 `(o+(z−1)δ,o+(z+2)δ)` 中，严格余量由每个 δ_j>0 供应。因此包含单元所有面、棱和顶点，不存在闭／开边界漏项。

这里构造的是原 Kuhn 公式所指定的全部单元及各自非退化性。尚未证明不同排列单元内部不交或它们的并覆盖格点盒，不能将真实 Affine.Simplex 类型本身当成已经完成的三角剖分定理。

## 全无限格网共享顶点星与有限并

若两个实际物理单纯形有共同顶点，则对每个坐标，顶点公式给

`o_j+(z_j+ε_j)δ_j=o_j+(z′_j+ε′_j)δ_j`，其中 ε_j、ε′_j∈{0,1}。

先消去 o_j，再由 δ_j≠0 约去乘子，得到 z_j−z′_j 为两个0/1增量之差。证明分支处理这四种实际指示值，并把实数整数嵌入不等式准确转回 ℤ，得 z_j−1≤z′_j≤z_j+1。该条件是由真正共享顶点等式推出，不是用空间靠近代替共享顶点，也没有把“每个坐标相近”反向当成必共享顶点。

邻单元整个凸包位于其自身闭格点盒，正步长保持上述整数不等式方向，因此该整个单元位于 `[o+(z−1)δ,o+(z+2)δ]`。再由正步长的严格余量将这个闭盒置于半径2开扩张块 `(o+(z−2)δ,o+(z+3)δ)`。没有假定邻单元形状或只估计交点。

`cartesianKuhnStarPatch` 是固定单元所有顶点星的并集：存在任意 z′∈ℤ^d、任意 π′ 和双方顶点 k,l，实际顶点相等且 x 属于该邻单元。定义没有先把 z′ 限于有限窗口，也没有只纳入某几个“典型邻居”。取原 z、π 和0号顶点证明原整个单元包含于该星。

有限并定理的正向使用上面已证整数邻域，把每个确实共享顶点的 z′ 放入各坐标 `[z_j−1,z_j+1]` 的真实有限函数积；反向仍保留“存在共享顶点”条件，只对条件成立的单元取回星定义。条件不成立时为空，不错误地将整个邻近窗口都当作实际星。因而与有限并是精确相等，不只是一个方便的上界。

候选窗口有3^d个整数向量、排列有限；紧性只需要这些真实有限集合，无需给实际邻单元个数等式。每个 simplicialCell 为有限点集的真实凸包，其紧性由有限维 Euclidean 凸包定理供应；空分支也紧，故整体紧且 Borel 可测。无限并的紧性由已证明的精确有限表示得出，未从“一致有界”或“每个成员紧”直接推断。

## 实际点态重数、常数和前提边界

第20项实际量词是任意 Fintype ι、任意原点和逐坐标正步长，以及注入 `index : ι→ℤ^d×Perm(Fin d)`；被计数集合正是这些标签对应的上述完整星并集。`finiteCoverMultiplicity` 是实际包含该点 x 的指标集之基数，不是另给的上界函数。注入性只排除重复标签，是明确的组合前提，不能忽略为“任意重复单元列表”也有相同界。

已直接复核 T084 计数依赖：星的实际半径2包含关系给正步长归一化坐标 y_j=(x_j−o_j)/δ_j。若星含 x，则块含 x，floor 双侧界和整数性把其中心 z_j 放入 `[⌊y_j⌋−2,⌊y_j⌋+2]`。该整数闭区间恰有5项，坐标函数积恰有5^d项；全部真实排列的基数为 d!。包含 x 的指标集经注入 index 进入这个窗口×排列全集，所以

`finiteCoverMultiplicity(star family,x)≤5^d d!`。

边界上仍是点态结论，不必删除零测单元边界。5^d来自半径2的开块中心计数，与单个星的3^d候选邻格点窗口不是同一个计数；两者不能混用。该界独立于原点、网格步长、各向异性比、有限网格范围、总单元数及点 x。d=0时空坐标函数空间与排列空间均只有一个元素，5^0·0!=1，所有声明正常成立。

每个星的定义遍历无限格网；重数定理本身作用于任意有限无重复标签子族，没有将有限重数定义冒称为另一个已经形式化的无限求和定理。真实物理域内的单元或支撑裁剪只会减少集合，未来可用包含关系接入；本批并未构造帽函数或证明其支撑就是这些星，亦未证明具体有限域网格的完整索引方案及覆盖。

## 原文定位和未完成范围

原 Section 6 在正方向步长的 Cartesian 网格每盒取 d! 个同方向 Kuhn 单元，再以内部节点帽函数定义 R_h、J_h、Q_h。Appendix B 的局部矩、稳定性及最终 B.2 求和用到活跃节点支撑位于有限局部块，以及这些块的有界重叠。本阶段提供原具体单元与共享顶点邻域的实际几何基础，已把 T084 原本显式要求的“集合包含于固定半径格点块”用于这些真正星集合内部证明。

单元覆盖及内部不交、全局连续 P1 帽函数及其实际支撑、完整内部节点星的中心对称、节点矩条件、Q_h 仿射再现和局部稳定性仍未证明；也没有将星的有限并等式当成整个网格覆盖。原物理域边界的帽函数处理和全域加权误差仍待。故不提升 FD/P012、B.2/P026 或其他原文命题；固定覆盖表的13项 REVIEWED/PAPER 不变，P012/P026仍为 PLANNED。

## 固定依赖、构建与公理

三个新模块的 Carleman 导入闭包共102模块，其中99旧模块与基线逐字相同，新增恰为本批三模块。实际计数依赖 T084/C100 在同一基线已通过 [独立验收](T084-local-acceptance.md)；本次另直接读取 CartesianPatchOverlap 的 floor／窗口／注入计数、真实 simplicialCell 凸包与紧性、affineSimplex 的真实仿射等价像、正对角映射及所用 mathlib 矩阵等价和上三角行列式接口，核对适用条件与实际使用。

原稿、已读治理协议、工具链 pin 及 CI 工作流未被本批改变。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean 为4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root 显式导入三模块，CheckAxioms 增量只增加24项完整类型及公理输出，原递归审计未削弱。

固定 `/tmp/carleman-kuhn-stars-target.log` 实际含定向3254 jobs成功；`/tmp/carleman-kuhn-stars-full.log` 实际含 `Build completed successfully (3740 jobs).` 与 `Axiom audit passed for all 5856 Carleman declarations.`。固定 `/tmp/carleman-kuhn-stars-local-axioms.txt` 为 **1,696,436 bytes**，SHA256 **`4aa7f26e53a9357b51e340c56cd216897fe214031ba50235da4da572fb2dc966`**。

24/24项完整展开类型逐项核对且各有一条公理记录，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全部1797条显式公理记录（1793个不同声明）也无白名单外公理；递归审计含生成辅助声明，无 sorryAx 或无依据数学公理。三新模块无 sorry/admit/axiom/unsafe。

## 同 SHA 正式远端证据

独立通过 GitHub API 查询 [main/push run 39180881178](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39180881178/attempts/1)，确认 attempt 1、head SHA 为本报告固定 SHA，run 已 completed/success。三项 job 均绑定相同 SHA 且 completed/success：state-check `117833166830`（00:28:00Z）、lean `117833167062`（00:30:55Z）、dashboard / snapshot `117833869766`（00:31:08Z）。

实际 artifact 元数据把 `lean-ci-result`（`12156421118`）及 `lean-declaration-evidence`（`12155894196`）均绑定到该 run、main 分支与同一 head SHA，且未过期。已独立读取 `/tmp/carleman-kuhn-stars-main-ci/result.json`：status=PASS，checked_sha=source_head_sha=`e52ffb4aed1df34fbcb1839e9472abafa927abfd`，finished_at=`2026-10-19T00:29:51.393425+00:00`，target 为 Carleman；Lean 4.35.0、mathlib commit 与固定本机 pin 一致。

已对 `/tmp/carleman-kuhn-stars-main-axioms/axioms.txt` 与上述固定本机副本作实际逐字节比较，完全相同：1,696,436 bytes，SHA256 为 `4aa7f26e53a9357b51e340c56cd216897fe214031ba50235da4da572fb2dc966`。远端末行确认全部5856项递归审计通过；重新扫描其1797条显式公理记录，无三项标准基础公理之外的依赖。本报告未使用后续工作树构建替代固定远端证据。

## 验收决定

语义核对未发现仿射无关性、矩阵方向、物理坐标／步进、闭凸包包含、无限星定义、有限并、紧性、重数或量词方面需要修复的缺陷。同 SHA 三项 CI 及原始产物核实完成，T085/C101 全部24项声明正式 **PASS**，可按辅助结果升至 REVIEWED；不得据此提升 P012/P026 或其他尚未完成的原文命题。

本次只写本报告，没有修改数学实现、台账、原稿或 root 导入，没有 commit/push。范围保持 AUXILIARY，原文计数保持13/26。
