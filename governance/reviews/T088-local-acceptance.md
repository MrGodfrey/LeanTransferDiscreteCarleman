# T088 / C104 独立本机验收

- `checked_sha`: `b54a0a22a2352ab389a1cb109f1d60386ca2261a`
- `base_commit`: `7b2627620e04ad9b44e6bee31fab8a241d4f4d1a`
- `semantic_checked_at`: `2026-10-19T01:02:10+00:00`
- `reviewed_at`: `2026-10-19T01:03:46+00:00`
- `result`: **PASS**；固定版本语义与同 SHA 远端证据均通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节一致，5968 项递归审计通过。
- `scope`: **AUXILIARY**；实际有限 Cartesian Kuhn 网格内部节点帽函数的中心对称和真实零向量一阶矩。原文保持 **13/26**。

直接核对固定提交四模块全部 16 项声明的源码、证明、完整类型与关键依赖，对照原 `paper/main.tex:1634–1658` 的有限网格/重构定义、Appendix B Step 1 的 `eq:fdmoments`（2745–2754）以及 `governance/analysis/T088-kuhn-first-moment.md`。数学核查不以规格、执行者报告或 CI 代替；后续工作树增量不属于本次范围。

## 全部 16 项声明

名称均加前缀 `Carleman.`；文件相对于固定提交的 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `simplex_cell_affine_relabel` | `Spatial/SimplexAffineRelabel.lean:12` | PASS；实际仿射等价的顶点对应，经凸包像恒等式给整个闭单元的精确对应。 |
| 2 | `simplexBarycentric_affine_relabel` | `Spatial/SimplexAffineRelabel.lean:29` | PASS；同一顶点排列下重心坐标实际仿射拉回，全空间成立，不只单元内部。 |
| 3 | `kuhnReflectedOrigin` | `Geometry/KuhnReflection.lean:14` | PASS；真实整数格点原点为逐坐标 2a−z−1。 |
| 4 | `kuhnReflectedPermutation` | `Geometry/KuhnReflection.lean:16` | PASS；`Fin.revPerm.trans π` 的实际复合方向为 π∘rev。 |
| 5 | `kuhnVertexIndex_reflection` | `Geometry/KuhnReflection.lean:19` | PASS；正确区分 Fin d 的排列反序与 Fin(d+1) 的顶点反序，实际整数坐标等于 2a−旧顶点。 |
| 6 | `cartesianKuhnSimplex_reflection_vertex` | `Geometry/KuhnReflection.lean:33` | PASS；在同一物理 o、正 δ 下，关于 x_a=o+aδ 的真实反射等于反射单元第 rev(k) 个顶点。 |
| 7 | `cartesianKuhnSimplex_reflection_cell` | `Geometry/KuhnReflection.lean:48` | PASS；真实闭 Kuhn 单元反射像恰为同向构造网格中的反序单元。 |
| 8 | `cartesianKuhn_incident_finite_index` | `Geometry/KuhnReflection.lean:57` | PASS；内部整数节点及真实顶点关联内部推出 0≤z_j<N_j，实际 toNat 构造有限索引并证明标签相等。 |
| 9 | `cartesianFiniteSimplex_of_latticeIndex` | `Geometry/KuhnReflection.lean:88` | PASS；实际有限标签与无限格标签相等时，得到真实单纯形本身相等。 |
| 10 | `cartesianFiniteSimplex_reflected_incident` | `Geometry/KuhnReflection.lean:96` | PASS；反射固定节点仍是反射单元顶点，内部供应有限索引及全部顶点对应，不增远离边界条件。 |
| 11 | `cartesianKuhnHat_reflection_of_nonzero` | `Spatial/CartesianKuhnHatSymmetry.lean:12` | PASS；非零支撑选出真实关联有限单元，以同一重心坐标对应证明实际帽值相等。 |
| 12 | `cartesianKuhnHat_reflection` | `Spatial/CartesianKuhnHatSymmetry.lean:36` | PASS；用反射自反性处理零值点，取得整个欧氏空间上的真实零延拓帽函数对称性。 |
| 13 | `cartesianKuhnHat_integrable` | `Spatial/CartesianKuhnFirstMoment.lean:13` | PASS；实际全空间连续帽函数及紧支撑给真正 Lebesgue 可积性。 |
| 14 | `cartesianKuhnHat_firstMoment_integrable` | `Spatial/CartesianKuhnFirstMoment.lean:20` | PASS；同一向量函数 φ_a(x)(x−x_a) 连续且支撑包含帽支撑，真正 Bochner 可积。 |
| 15 | `cartesianKuhnHat_firstMoment_zero` | `Spatial/CartesianKuhnFirstMoment.lean:28` | PASS；全空间平移/取负换元与反射反对称性给向量积分等于其负，逐实坐标消去为零。 |
| 16 | `cartesianKuhnHat_firstMoment_domain` | `Spatial/CartesianKuhnFirstMoment.lean:53` | PASS；物理开域外帽函数逐点恒零，使原 Ω 上积分精确等于已证明为零的全空间积分。 |

## 与原矩条件的对应及范围

原 Appendix B Step 1 先说明内部节点星完整并中心对称，包括紧邻边界的内部节点，再写两条矩条件：`∫Ω φ_i=ω_i` 与 `∫Ω (x−x_i)φ_i=0`。本批最终声明精确证明第二条，其 φ_i 是实际有限网格的节点基函数；不是自由给定的偶函数、抽象重构函数或无限网格的替代积分。

实际参数为任意维数 d、平移 o、逐坐标正步长 δ、各方向有限盒数 N，以及整数节点 a。物理域恰为 `openCoordinateBox o (o+Nδ)`，节点恰为 `cartesianGridPoint o δ a`。原 Ω=∏(0,L_j)、δ_j=L_j/N_j、内部 a_j∈{1,…,N_j−1} 是 o=0 的直接实例。原所有内部节点均覆盖；无网格步长可比性、特定长宽比或维数上界的额外条件，说明这些在本精确一阶矩身份中不需要。

尚未证明 `∫Ω φ_i=∏δ_j`。因此不能由本批单独声称完整矩条件、`J_hp=p(x_i)` 的仿射再现、载荷右逆、Q_h、FD 数值假设或完整 B.2 已完成。C104 只可按 **AUXILIARY** 记录，P012、P026 及其它原文覆盖均不提升，原文保持 **13/26**。

## 实际网格、帽函数与仿射重标号

直接复核 `KuhnReferenceSimplex`、`CartesianKuhnSimplex`、`KuhnLatticeCoordinates`、`FiniteCartesianKuhnCover` 和 `KuhnFaceMatching` 的实际定义。参考单纯形由真实单位上三角等价从标准单纯形构造，顶点依次为 0、e₀、e₀+e₁、…；非退化性不是假设。物理单纯形以坐标排列、正对角缩放及平移构造，顶点逐坐标为

`o_j + (z_j + 1[(π⁻¹j)<k]) δ_j`。

有限索引为 `(∏j Fin(N_j)) × Perm(Fin d)`，包含每个实际 Cartesian 盒内全部 d! 个 Kuhn 单元，排列构造在全部盒相同。已有实际闭单元覆盖和公共面证明供应 `cartesianKuhnPartition`；并未给每个盒另选会破坏反射一致性的任意剖分。

`cartesianKuhnHat` 是该具体有限 partition 的真实 `nodalFunction`，节点数据为在 x_a 取 1、所有其它几何点取 0。`nodalFunction` 在闭覆盖内取实际局部仿射插值，在覆盖外取零；其公共面一致性由实际单元公共顶点凸包和仿射再现证明。因此共享面/边/顶点上不会累加多个局部帽值，也没有 a.e. 任意选代表导致的边界点歧义。

已直接核对 `CartesianKuhnNodal`、`CartesianKuhnHatSupport`、`SimplexNodalInterpolation`、`SimplicialNodalGluing`、`SimplicialNodalBoundary`：关联单元上帽函数恰为该节点的真实重心坐标，非关联单元上恒零，非零支撑包含真实有限闭节点星。内部节点数据在物理边界节点为零；实际 boundary-fitted 证明和公共面一致性给整个边界零值，故全空间零延拓连续。紧支撑来自有限紧闭单元覆盖，不依赖尚未证明的矩条件。

新闭凸包重标号直接使用实际仿射映射的凸包像性质，再以顶点排列的双射性证明范围相等。重心坐标重标号把 `λ^U_{e(k)}∘A` 视为实际全空间仿射函数；其在 T 的全部顶点上由 Kronecker 值与 e 的单射性等于 `λ^T_k`，再由真实仿射插值再现推出两个仿射函数相等。没有将仅在单元内部成立的公式错误推广到全空间。

## 反射公式与完整有限节点星

设 R(x)=2x_a−x。代码的 `Fin.revPerm.trans π` 为先 rev 后 π，即 π∘rev；其逆为 rev∘π⁻¹。若 r=(π⁻¹j).val，则 r 属于 Fin d，反序为 d−1−r；原顶点 k 属于 Fin(d+1)，反序为 d−k。代码明确证明

`d−1−r < d−k ↔ ¬(r<k)`，

所以反射单元原点 `z'_j=2a_j−z_j−1` 加上反序顶点的指示值，恰为 `2a_j−(z_j+1[r<k])`。这些不同长度的反序没有混用。代入实际物理 o、δ 后得到所有 k 的精确向量顶点身份；真实仿射凸包像由此给整个闭单元反射身份。

对任意无限格单元，若 x_a 是其真实顶点，应用已证明的网格坐标仿射函数 `(x_j−o_j)/δ_j`，得到整数 `a_j=z_j` 或 `z_j+1`。原 ha 与 δ_j>0 给 `0<a_j<N_j`；整数性于是保证 `0≤z_j<N_j`。代码用 `(z_j).toNat` 形成真正 `Fin(N_j)`，并证明转回整数的标签与 z 精确相等，排列也保持 π。不是把存在有限索引作为前提。

对关联有限单元反射时，x_a 被 R 固定，故仍是反射无限格单元中的第 rev(k) 个顶点；上述内部节点结论立刻提供其有限索引。由标签等式转回真正单纯形，再证明全部顶点对应。

这里只用 `0<a_j<N_j`，允许 a_j=1、a_j=N_j−1，亦允许 N_j=2；没有要求节点距边界至少两个网格宽度。只要求单元关联于该节点，没有证明或使用 R(Ω)=Ω。这个局部星完整性正是原紧邻边界内部节点所需的内容。

## 全空间帽函数对称与真正一阶矩

当 φ_a(x)≠0，真实支撑定理给某个关联有限单元 i 包含 x。反射构造给另一个实际有限单元 j，且 R(x)∈j；两个帽值分别等于 i 的 λ_k(x) 和 j 的 λ_rev(k)(R(x))。新仿射重标号定理使二者严格相等，包括共享面上的点。

当 φ_a(x)=0，若 φ_a(Rx)≠0，则对 Rx 应用非零情形，再用 R(Rx)=x，得到非零值等于零的矛盾。因此全空间每一点均满足 φ_a(Rx)=φ_a(x)。没有为零值点强求单元存在，也没有把反射域外点当作仍在 Ω 内。

同一函数 φ_a 已证明全空间连续且紧支，故对 Lebesgue volume 可积；向量函数 `F(x)=φ_a(x)•(x−x_a)` 是连续函数与连续位移的标量乘积，支撑包含 φ_a 的紧支撑，因此真正 Bochner 可积。`firstMoment_integrable` 的参数和 ha 与后续积分声明完全相同，没有隐藏积分前提。

`firstMoment_zero` 的代数证明使用标准积分换元，其本身不需要显式传入可积性证明；但本批已独立证明同一 F 的可积性，所以这里的零值确为真实积分抵消，不能归因于不可积时的默认积分值。全空间换元定理 `integral_sub_left_eq_self F volume (x_a+x_a)` 来自固定 mathlib 的取负不变与平移不变积分身份，实际作用于 Euclidean Lebesgue 测度；不是对 Ω 的限制测度声称反射不变。

实际反射身份使 `F(2x_a−x)=−F(x)`，因为帽值保持而位移取负。换元给 `−∫F=∫F`，实向量每个坐标由线性算术得到零；PiLp.ext 还原向量零。没有忽略向量方向或用标量积分替代向量矩。

最后使用已证明的 `cartesianKuhnHat_zero_compl`：在整个物理开域外，包括其边界，帽函数逐点为零。因此 F 也逐点为零，`setIntegral_eq_integral_of_forall_compl_eq_zero` 将原 Ω 上的积分精确等于全空间积分。这个末步没有将整个 Ω 反射，也没有使用零测边界或对称域的未证假设。

## 量词、维数和未清偿项

全部主结论统一量化任意 o、正 δ、N、整数 a，只假定 x_a 为原域内部节点；没有另给中心对称、节点星完整性、可积性、保测度或目标一阶矩。实际 ha 与正步长在正维时已推出每个 N_j≥2。任意 anisotropic 正步长也成立，本精确等式无需网格尺度统一常数。

d=0 在辅助声明中也合法：没有坐标比较义务，空间为单点，位移向量恒零；未因 d−1 的自然数截断产生实质漏洞，涉及 r:Fin d 的分支在此为空。原所有 d≥1 均完整覆盖。边界节点不在目标范围，恰与原只对内部节点写矩条件一致。

本批已完成的仅是实际帽函数的对称性和向量一阶矩。零阶质量、具体节点载荷、全部矩条件以及后续重构/FD/B.2 依赖仍须单独证明和验收，不能从本批辅助 PASS 自动提升。

## 固定版本、本机构建与公理

四新模块的 Carleman 导入闭包共 144 个模块，140 个既有模块相对 base 逐字节未变，root 明确导入四模块。AGENTS、治理协议和 state 协议与前次已读版本相同；原论文、工具链、mathlib pin、两个 CI workflows 相对 base 未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本地核查的 mathlib checkout HEAD 实际为固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，已阅读积分换元的真实源证明（乘法形式经 `to_additive` 生成此处使用的加法定理）。

`/tmp/carleman-kuhn-first-moment-target.log` 实际显示定向构建 3314 jobs 成功；`/tmp/carleman-kuhn-first-moment-full.log` 实际显示全库 3754 jobs 成功、5968 声明递归审计通过。固定本机 `/tmp/carleman-kuhn-first-moment-local-axioms.txt` 为 1,735,922 bytes，SHA256 `9165c623617c3d8b29b106e915a29b44663d6a24eec600b36edcd8ae442056ab`。

全部 16 项各有恰一条实际完整类型与恰一条公理检查结果，均已核对。`kuhnReflectedOrigin` 不依赖公理；`kuhnReflectedPermutation` 只用 `propext`、`Quot.sound`；其余 14 项只用正常三公理 `propext`、`Classical.choice`、`Quot.sound`。全产物共有 1887 条带公理打印（1883 个不同声明）和 4 条无公理打印，无白名单外公理；末行实际为 `Axiom audit passed for all 5968 Carleman declarations.`。

递归审计程序相对 base 未改，本批只新增显式打印；仍遍历全部 Carleman 声明并递归检查依赖。四新模块无 sorry/admit 或新增数学公理。

## 远端证据与签发

已独立查询 [main CI run 39183200183 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39183200183/attempts/1)，确认事件为 `push`、分支为 `main`、head SHA 精确为本次固定 `b54a0a22a2352ab389a1cb109f1d60386ca2261a`。run 最终为 `completed/success`，最后更新时间为 `2026-10-19T01:02:24Z`；三个实际 jobs 均成功：

| Job | ID | 最终状态 |
|---|---|---|
| `lean` | `117840148422` | `completed/success` |
| `state-check` | `117840148606` | `completed/success` |
| `dashboard / snapshot` | `117840915411` | `completed/success` |

独立读取同次原始 `/tmp/carleman-kuhn-first-moment-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha` 为上述固定 SHA，`finished_at=2026-10-19T01:01:16.324009+00:00`，target 为 `Carleman`。Lean 4.35.0 Linux commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

独立查询远端 artifact 元数据，`lean-ci-result`（ID `12156803754`）和 `lean-declaration-evidence`（ID `12157510668`）均未过期，且各自绑定上述同 run、main 分支与固定 SHA。下载的原始 `/tmp/carleman-kuhn-first-moment-main-axioms/axioms.txt` 与固定本机副本逐字节完全相同：1,735,922 bytes，SHA256 `9165c623617c3d8b29b106e915a29b44663d6a24eec600b36edcd8ae442056ab`。远端全部 16 项实际类型和公理打印再次逐项核对，全部 1887 条带公理结果仅含正常三公理，另有 4 条无公理结果；末行确认全库 5968 声明递归审计通过。没有混入后续工作树的产物。

最终结论 **AUXILIARY / PASS**，未发现本批声称范围内的数学缺陷。可将 C104 按 **AUXILIARY / REVIEWED** 记录，保持原文 **13/26**。零阶矩、完整矩条件、载荷/Q_h、FD 和 B.2 不随本报告提升。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
