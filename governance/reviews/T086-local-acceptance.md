# T086 / C102 独立本机验收

- `checked_sha`: `e753eb065d87695d33e31c141cfe15c7cea4b5de`
- `base_commit`: `e52ffb4aed1df34fbcb1839e9472abafa927abfd`
- `reviewed_at`: `2026-10-19T00:44:32+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：实际Kuhn闭单元的有序坐标刻画、真实有限Cartesian网格覆盖、无限／有限网格内部不交、有限网格a.e.唯一分割及实际单元星族重叠界。帽函数、矩、Qh及其稳定性仍待；原文保持 **13/26**。

独立从固定提交导出源码，读取四模块全部证明、34项完整展开类型及关键依赖，对照固定 `paper/main.tex` Section 6的Cartesian/Kuhn网格定义和顶点步进公式（TeX 1630–1697），以及Appendix B的节点基、完整星和矩要求（TeX 2741–2785）。执行者规格和CI没有代替数学核对，后续工作区修改不属于本报告。

## 全部34项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `kuhnExtendedCoordinate` | `Geometry/KuhnBarycentricCoordinates.lean:15` | PASS；真实扩充序列为(1,x₀,…,x_{d−1},0)。 |
| 2 | `kuhnExtendedCoordinate_zero` | `Geometry/KuhnBarycentricCoordinates.lean:18` | PASS；首值精确为1。 |
| 3 | `kuhnExtendedCoordinate_last` | `Geometry/KuhnBarycentricCoordinates.lean:20` | PASS；末值精确为0。 |
| 4 | `kuhnExtendedCoordinate_inner` | `Geometry/KuhnBarycentricCoordinates.lean:24` | PASS；中间索引严格还原原欧氏坐标。 |
| 5 | `kuhnBarycentricWeight` | `Geometry/KuhnBarycentricCoordinates.lean:28` | PASS；第k权为实际相邻两项之差。 |
| 6 | `kuhnBarycentricWeight_sum` | `Geometry/KuhnBarycentricCoordinates.lean:31` | PASS；有限望远镜和给全部d+1权总和1。 |
| 7 | `kuhnBarycentricWeight_reconstruct` | `Geometry/KuhnBarycentricCoordinates.lean:40` | PASS；逐坐标尾和精确重构真实前缀顶点线性组合。 |
| 8 | `kuhnBarycentricWeight_nonneg` | `Geometry/KuhnBarycentricCoordinates.lean:64` | PASS；首末界和递减坐标分别保证所有权非负，含d=0。 |
| 9 | `kuhnReferenceSimplex_mem_of_ordered` | `Geometry/KuhnBarycentricCoordinates.lean:95` | PASS；实际非负权、总和与重构供应真实凸包成员。 |
| 10 | `kuhnOrderedCube` | `Geometry/KuhnOrderedCell.lean:13` | PASS；原欧氏点满足全部坐标[0,1]界及递减次序。 |
| 11 | `kuhnOrderedCube_convex` | `Geometry/KuhnOrderedCell.lean:16` | PASS；坐标区间与非负线性组合保留递减次序。 |
| 12 | `kuhnReferenceSimplex_cell_eq_ordered` | `Geometry/KuhnOrderedCell.lean:24` | PASS；顶点凸包与有序坐标集合双向精确相等。 |
| 13 | `cartesianKuhnChart` | `Geometry/KuhnOrderedCell.lean:42` | PASS；真实坐标置换、正对角缩放和平移组成仿射等价。 |
| 14 | `cartesianKuhnChart_apply` | `Geometry/KuhnOrderedCell.lean:48` | PASS；第j坐标为oⱼ+(zⱼ+x_{π⁻¹j})δⱼ。 |
| 15 | `cartesianKuhnChart_symm_apply` | `Geometry/KuhnOrderedCell.lean:55` | PASS；真实逆坐标为(x_{πj}−o_{πj})/δ_{πj}−z_{πj}。 |
| 16 | `cartesianKuhnSimplex_cell_eq_chart` | `Geometry/KuhnOrderedCell.lean:66` | PASS；原实际顶点凸包恰为有序单位扇区的仿射像。 |
| 17 | `cartesianKuhnSimplex_mem_iff` | `Geometry/KuhnOrderedCell.lean:75` | PASS；所有归一化坐标在[0,1]及沿π递减是充分必要条件。 |
| 18 | `cartesianKuhnSimplex_cover_box` | `Geometry/KuhnOrderedCell.lean:100` | PASS；真实OrderDual排序构造排列，全部闭格点盒均被d!单元覆盖。 |
| 19 | `CartesianCellIndex` | `Geometry/FiniteCartesianKuhnCover.lean:14` | PASS；实际有限格点坐标函数×全部排列。 |
| 20 | `cartesianCellLatticeIndex` | `Geometry/FiniteCartesianKuhnCover.lean:16` | PASS；取各Fin值并转为整数，保留排列。 |
| 21 | `cartesianCellLatticeIndex_injective` | `Geometry/FiniteCartesianKuhnCover.lean:19` | PASS；整数坐标相等恢复各Fin项，排列相等恢复整个指标。 |
| 22 | `cartesianCellIndex_card` | `Geometry/FiniteCartesianKuhnCover.lean:30` | PASS；真实有限函数空间与排列基数给(∏Nⱼ)d!。 |
| 23 | `cartesianFiniteSimplex` | `Geometry/FiniteCartesianKuhnCover.lean:34` | PASS；实际有限索引实例化原物理Kuhn单纯形。 |
| 24 | `cartesianFiniteSimplex_cover` | `Geometry/FiniteCartesianKuhnCover.lean:38` | PASS；实际floor给合法有限格点，排序给单元，覆盖整个原开域。 |
| 25 | `cartesianFiniteSimplex_ae_cover` | `Geometry/FiniteCartesianKuhnCover.lean:59` | PASS；真实点态覆盖与开域可测性给原限制体积a.e.覆盖。 |
| 26 | `cartesianFiniteStar_multiplicity_le` | `Geometry/FiniteCartesianKuhnCover.lean:66` | PASS；内部供应有限索引注入，实际完整单元星族重数≤5^d d!。 |
| 27 | `linear_strict_of_mem_interior_le` | `Geometry/KuhnCellInterior.lean:11` | PASS；内点球中显式正方向扰动给严格半空间不等式。 |
| 28 | `cartesianKuhnSimplex_interior_box` | `Geometry/KuhnCellInterior.lean:33` | PASS；实际正负坐标投影给全部严格格点盒界。 |
| 29 | `cartesianKuhnSimplex_interior_strictAnti` | `Geometry/KuhnCellInterior.lean:51` | PASS；不同坐标归一化差的真实线性泛函给严格递减次序。 |
| 30 | `cartesianKuhnSimplex_common_interior_origin` | `Geometry/KuhnCellInterior.lean:79` | PASS；共同内点不可能属于两个不同整数格点开盒。 |
| 31 | `strictAnti_permutation_unique` | `Geometry/KuhnCellInterior.lean:99` | PASS；两种严格排序的相对排列严格单调，有限线性序迫使其为恒等。 |
| 32 | `cartesianKuhnSimplex_interiors_disjoint` | `Geometry/KuhnCellInterior.lean:113` | PASS；格点及排列同时唯一，得到整个无限整数网格的内部不交。 |
| 33 | `cartesianFiniteSimplex_interiors_disjoint` | `Geometry/KuhnCellInterior.lean:129` | PASS；真实有限标签注入保留不等指标，内部不交被实际继承。 |
| 34 | `cartesianFiniteSimplex_ae_partition` | `Geometry/KuhnCellInterior.lean:138` | PASS；覆盖、内部不交和有限个真实零测边界给a.e.唯一闭单元。 |

## 真实参考单纯形与相邻差重构

已读取T085的实际参考对象：从0及真实标准基构成的仿射独立单纯形出发，用对角全1、行列式为1的真实上三角前缀矩阵作线性同构。所得第k顶点的第j坐标是1_{j<k}，恰为0、e₀、e₀+e₁等前缀顶点。新证明使用的是这些实际顶点的凸包，没有另设抽象“参考域”替代它。

对d≥1，相邻差权具体为1−x₀、x₀−x₁、…、x_{d−2}−x_{d−1}、x_{d−1}。总和由两种Fin全集分解望远镜相消；第j坐标只接收k>j的顶点贡献，该真实尾和精确等于xⱼ。重构身份对全部欧氏x成立，不预先假设凸包成员。坐标在[0,1]且递减时，首末权及全部中间权分别非负，于是凸组合定理给真正凸包成员。

反方向由有序坐标集合的凸性及每个实际顶点均在其中证明。因此精确等式同时具有充分性和必要性，而非仅凭坐标必要界宣称覆盖。d=0单独处理非负性：唯一权为1，重构是零维空间唯一点；其他有限和、凸包与排序步骤也保留该情形。

## 同向物理图、排序和有限floor覆盖

物理图为原坐标置换后接逐轴正缩放及格点平移；其实际公式为Φ(y)ⱼ=oⱼ+(zⱼ+y_{π⁻¹j})δⱼ。逆公式在排列后的第j位置为(x_{πj}−o_{πj})/δ_{πj}−z_{πj}。全部除法由δⱼ>0保证，排列方向和归一化次序相互吻合。原 `affineSimplex_cell` 的真实凸包仿射像身份把该图接到原物理顶点，不是独立指定单元区域。

于是单元成员资格恰为归一化坐标yⱼ=(xⱼ−oⱼ)/δⱼ−zⱼ全部属于[0,1]，并且y∘π递减。闭格点盒中的每个点先满足坐标界，再对实际y调用 `Tuple.sort`，值域取OrderDual ℝ，因此得到所需非严格递减排列。已直接读取所用mathlib定义和证明：它以有限图上的真实序同构构造排列，monotone_sort确实给值的排序。相等坐标、全部盒面和边角都允许，未要求坐标互异或删去边界来证明覆盖。

有限索引是(∀j,Fin(Nⱼ))×Perm(Fin d)，真实基数为(∏Nⱼ)d!，到无限整数格点／排列标签的映射内部证明注入。对原开域oⱼ<xⱼ<oⱼ+Nⱼδⱼ，qⱼ=(xⱼ−oⱼ)/δⱼ满足0≤qⱼ<Nⱼ；取Nat.floor(qⱼ)因此确实落在Fin(Nⱼ)。floor≤q<floor+1又把x放入对应真实闭格点盒，随后排序覆盖选出单元。

内部格面上的整数q可选右侧格点，所得闭单元仍包含该点；原上边界不在开域中，故不会产生floor=Nⱼ的非法索引。若某Nⱼ=0则开域为空，覆盖命题合法且未构造虚假的Fin 0元素；d=0时没有坐标约束、空格点函数和空排列均唯一。原稿d≥1、Nⱼ≥2、o=0、δⱼ=Lⱼ/Nⱼ是本批量词的特例。原稿的步长可比性不需要用于这些纯覆盖／分割结论，未被替换成更强假设。

所有格点使用同一前缀顶点和坐标排列规则，原实际顶点步进为δ_{πk}e_{πk}，对应原文同向Kuhn剖分。这里尚未额外证明全部公共面的顶点匹配或全局帽函数跨面一致；覆盖和内部不交本身不充当这些后续结论。

## 内点严格性、两层唯一性与a.e.分割

一般半空间引理在任意实际赋范实向量空间中成立。若内点x有半径ε>0的球包含于S，取a=ε/(‖v‖+1)>0，则a‖v‖<ε，故x+av∈S。真实线性性和f(v)>0给f(x)+af(v)≤c，从而f(x)<c。没有预设结论、严格分离假设或除以可能为零的‖v‖。

对每个实际坐标投影及其负泛函，用相应±标准基作正方向，得到单元内点严格位于所属格点开盒。对k<l，采用f=δ_{πl}^{−1}proj_{πl}−δ_{πk}^{−1}proj_{πk}，对应常数包含正确的原点及格点平移项。πk≠πl使f(e_{πl})=δ_{πl}^{−1}>0；原单元的非严格次序给f≤c，内点引理遂给归一化坐标严格递减。所有坐标都被处理，未仅检查相邻或特定一个方向后擅自推全结论。

若两个单元共享内点，先逐坐标使用整数格点间至少相差1及正δ，排除不同格点开盒，得到z=z′。随后两种排列都严格排序同一归一化坐标函数。相对排列π⁻¹∘π′因此严格单调；所用 `StrictMono.apply_eq` 的实际mathlib证明表明有限线性序上的严格单调自映射只能是恒等，于是π=π′。这证明无限整数网格任意不同标签的内部不交，不依赖有限网格范围。

有限版本通过刚证明的实际标签注入继承内部不交。最终调用的 `simplicialCells_ae_partition` 已直接读取：真实有限凸包是紧／可测／凸集，凸集的实际Lebesgue边界测度为0；有限指标的ae_all_iff给一个共同零测例外集。在其补集上，属于闭单元就属于其内部，点态覆盖给存在性，内部不交给指标唯一性。因此输出在原开域限制体积下a.e.存在唯一闭单元；并未声称所有点有唯一单元，也未把共享面上的闭单元交集消掉。

该共同零测集论证只应用于实际有限索引族。无限网格版本本批只声称内部两两不交，未不加说明地对任意无限边界族取a.e.交集。零维单元的边界为空，原依赖也未借正维数假设略过该情形。

## 星族重叠对象及仍待完成的原文义务

`cartesianKuhnStarPatch`的实际定义是：固定一个单元，取无限同向Kuhn网格中与它任一顶点共享的所有闭单元之并。它是以单元为指标的完整星块，可能伸出物理矩形域，并非已经构造的单一节点帽函数支撑。已直接核对旧证明：共享顶点强制相邻格点坐标差在[−1,1]，故该并包含于格点周围固定半径2的开Cartesian块；其有限并表示也真实给出紧性和可测性。

新有限族定理将真实 `cartesianCellLatticeIndex` 的注入内部提供给T085，再接T084的floor窗口计数，因此对所有欧氏点给重数≤5^d d!。这个系数与N、δ、o、总单元数和时间周期无关；无需额外再乘顶点数d+1。有限物理邻居星或域内裁剪是该完整星的子集，但本批未据此宣称节点星中心对称、内部节点星完整性或帽函数的零迹。

本批已消去实际有限Kuhn网格覆盖、内部不交以及该单元星族注入的相应外留前提。帽函数显式构造、局部重心坐标匹配、跨面连续、支撑、原内部节点星中心对称、零阶／一阶矩、载荷提升、Qh及其局部稳定性仍未在新声明中证明。原FD/P012、B.2/P026不提升，scope保持AUXILIARY，原文仍13/26。

## 固定依赖、构建与公理

四模块Carleman导入闭包共106模块，102旧模块与base完全不变，新增恰为本批四模块。关键已验收版本亦已比较：C052 SimplicialCells的26模块闭包相对 `885add73e59dd08e5609597cac3c2ddd7fd395bd` 不变，C100 CartesianPatchOverlap的87模块闭包相对 `d8ccc85628961e226550d9fea095eac9710ed969` 不变，C101 KuhnVertexStars的102模块闭包相对base不变。参考顶点、实际物理单纯形、星并定义、边界零测及a.e.唯一分割依赖均直接读取。

原稿、已读治理协议、工具链pin及CI工作流未由本批改变。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入四模块，CheckAxioms包含34项完整类型及公理输出。

固定本机34项完整展开类型均已逐项核对；CartesianCellIndex与cartesianCellLatticeIndex两项不依赖任何公理，其余只用正常基础公理的子集。全部1832条显式记录中1829条具有非空公理列表、3条无公理，未发现 `propext`、`Classical.choice`、`Quot.sound` 之外的公理，无sorryAx。检查器通过privateToUserName遍历所有Carleman声明并递归collectAxioms。

实际定向日志为3258 jobs；`/tmp/carleman-kuhn-partition-full.log` 包含 `Build completed successfully (3744 jobs).` 和 `Axiom audit passed for all 5896 Carleman declarations.`。固定 `/tmp/carleman-kuhn-partition-local-axioms.txt` 为 **1,708,366 bytes**，SHA256 **`825970205618c934210de9591f2b30921a426e9fd1ae4450cae7a45bb587f748`**。

已独立通过GitHub connector读取 [main CI 39181779883 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39181779883/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。state-check（117835873129）、lean（117835873332）、dashboard / snapshot（117836502121）三项jobs全部completed/success；工具链准备、完整构建、checked source记录、原始证据上传及同次快照步骤均success。同run的lean-ci-result（12156437677）和lean-declaration-evidence（12156467576）实际artifact元数据均绑定固定SHA。

已实际读取 `/tmp/carleman-kuhn-partition-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=e753eb065d87695d33e31c141cfe15c7cea4b5de`，targets为Carleman，`finished_at=2026-10-19T00:41:36.685248+00:00`，ci_url与上述run/attempt一致。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-kuhn-partition-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,708,366 bytes**，SHA256 **`825970205618c934210de9591f2b30921a426e9fd1ae4450cae7a45bb587f748`**。另逐名核对远端34/34完整展开类型及公理，1832条显式记录（1829非空、3无公理）均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 5896 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C102：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定34项未发现相邻差方向、实际凸包、排序／逆图、floor有限索引、内部严格性、排列唯一性、零测边界或星重叠常数方面需要修复的缺陷；同SHA正式三项CI及原始远端公理证据已独立核实。帽函数、矩和Qh等后续义务如上，本批不提升FD/P012、B.2/P026或其他原文命题，原文仍 **13/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
