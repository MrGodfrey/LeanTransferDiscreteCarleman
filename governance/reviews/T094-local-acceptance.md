# T094 / C110 独立本机验收

- `checked_sha`: `fc89f7ab4516bb6dd97a43a2e5224e722b0b7a56`
- `base_commit`: `ba9aa5d2a3caf655bba037695fe733a3f292d952`
- `semantic_checked_at`: `2026-10-19T02:01:06+00:00`
- `reviewed_at`: `2026-10-19T02:03:55+00:00`
- `result`: **PASS**；固定版本语义及同 SHA 远端证据均通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节一致，6122 项递归审计通过。
- `scope`: **AUXILIARY**；原完整弱 H²∩H¹₀ 状态的实际局部边界相容仿射逼近，以及同一实际 Q_h 的闭单元仿射再现。原文保持 **13/26**。

本报告直接读取固定提交四个新模块的全部 14 项源码、证明、完整实际类型及关键依赖，对照原 `paper/main.tex:2783–2870`，尤其是 B.1 的物理边界仿射逼近和 B.2 证明开始的矩再现、相减分解。另核对 `governance/analysis/T094-kuhn-local-affine.md`。执行者说明及 CI 不代替语义核查，后续工作树中的新数学模块不在本报告范围内。

## 全部 14 项声明

名称均加前缀 `Carleman.`；源码位置相对于固定提交 `Carleman/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `cartesianGridPoint_interior_index` | `Geometry/CartesianInteriorVertex.lean:12` | PASS；由实际整数格点位于原开域，构造原完整有限内部节点索引，覆盖首末内部层。 |
| 2 | `cartesianFiniteSimplex_interior_vertex` | `Geometry/CartesianInteriorVertex.lean:29` | PASS；实际 Kuhn 顶点的整数坐标身份给出每个内部顶点的真实索引。 |
| 3 | `cartesianKuhnMoment_affine` | `Spatial/CartesianKuhnAffineProjection.lean:16` | PASS；原全域仿射 L² 类的实际归一化矩等于仿射函数在对应内部节点的值。 |
| 4 | `cartesianKuhnProjection_affine_on_cell` | `Spatial/CartesianKuhnAffineProjection.lean:28` | PASS；内部矩身份和边界顶点零值补齐全部单元节点，得到整个闭单元逐点再现。 |
| 5 | `cartesianKuhnMoment_sub` | `Spatial/CartesianKuhnAffineProjection.lean:51` | PASS；原 L² 差的 a.e. 代表身份、真实配对可积性给 J_h 的减法线性性。 |
| 6 | `cartesianKuhnProjection_sub` | `Spatial/CartesianKuhnAffineProjection.lean:64` | PASS；同一实际帽函数有限和给 Q_h 的全空间逐点减法身份。 |
| 7 | `cartesianFiniteSimplex_subset_closedPatch` | `Geometry/CartesianClippedBoundary.lean:13` | PASS；整个中心闭单元包含于实际加宽裁剪块的闭盒。 |
| 8 | `cartesianClosedPatch_subset_closedDomain` | `Geometry/CartesianClippedBoundary.lean:26` | PASS；max/min 端点直接给裁剪闭盒包含于原物理闭盒。 |
| 9 | `cartesianClippedPhysicalFaces` | `Geometry/CartesianClippedBoundary.lean:33` | PASS；从全部有限坐标面中按裁剪端点等于原域端点筛选真实物理面。 |
| 10 | `cartesianClippedPhysicalFaces_frontier` | `Geometry/CartesianClippedBoundary.lean:40` | PASS；每个所选完整闭面均属于原开域 frontier，包含面边缘。 |
| 11 | `cartesianCell_boundary_in_physicalFace` | `Geometry/CartesianClippedBoundary.lean:69` | PASS；中心闭单元的每个非内部点均属于某个所选物理闭面，覆盖角点与多面交线。 |
| 12 | `cartesianPhysicalFace_zero_on_boundaryCell` | `Geometry/CartesianClippedBoundary.lean:97` | PASS；物理闭面上的零值蕴含中心单元所有边界点的零值，无人工面零值要求。 |
| 13 | `cartesianKuhnProjection_physical_affine` | `Spatial/CartesianKuhnLocalAffine.lean:14` | PASS；真实物理面零值内部供应全部边界顶点条件，同一 Q_h 精确再现实际仿射 L² 类。 |
| 14 | `cartesianKuhn_h2_local_reproduced_affine` | `Spatial/CartesianKuhnLocalAffine.lean:26` | PASS；原全部弱 H²∩H¹₀ 状态产生同一 p、真实局部弱 H¹ 残差和 h² 局部 Hessian 界，C 先于全部网格和状态。 |

## 原文映射和本批边界

原 Appendix B Step 2 先由 B.1 选取在物理边界面上为零的仿射 p_K，再利用实际零阶/一阶矩在内部顶点再现 p_K；边界顶点由 p_K 的零值补齐，所以 Q_hp_K=p_K。随后才能把误差写成 `(u−p_K)−Q_h(u−p_K)`，应用局部稳定性、逆估计及 B.1，最后加权求和得到完整 B.2。

本批精确完成其中的内部顶点枚举、真实仿射矩、物理边界顶点处理、Q_h 仿射再现、J_h/Q_h 减法线性性，以及把已验收 B.1 和真实 Dirichlet 局部迹供应给同一 p 的局部 h² 逼近。这里没有把待证 Q_h 误差稳定性放进前提，也没有将一般弱 H² 类取节点值。

本批使用 T093 的一致加宽裁剪块 B，而原文把 B_K 定义为最小轴向块。代码和规格均未声称两者相等。加宽块保有原分析路线需要的 h 尺度边长、活动帽支撑和统一重叠控制；本批右端明确为较大实际 B 上的 Hessian 范数，不能把它改称原最小 B_K 上的更强局部界。该选择与本批明确的辅助范围一致。

目前没有输出 `‖u−Q_hu‖+h‖∇(u−Q_hu)‖` 的完整局部界，没有完成允许权、全域重叠组装、完整 B.2/P026 或 FD/P012。保留 **AUXILIARY** 与原文 **13/26**，不因辅助再现与逼近通过而提升完整论文覆盖。

## 真实内部节点与同一矩重构

原内部索引逐轴为 `{1,…,N_j−1}`。实际 `CartesianInteriorIndex N` 为 `∀j,Fin(N_j−1)`，其物理整数坐标是索引值加一。若实际整数格点 `o_j+z_jδ_j` 位于原开盒，δ_j>0 严格给出 `0<z_j<N_j`。证明逐轴取 `(z_j−1).toNat`，证明其落在 `Fin(N_j−1)` 中，再恢复整数坐标等式。没有把存在索引作为假设，没有遗漏靠边界的第一或最后一层内部节点。

实际 Kuhn 顶点的 `kuhnVertexIndex` 身份将上一结论应用到单元全部内部顶点。它并不假设所有顶点都内部；边界顶点由另一分支处理。原 N_j≥2 的完整有限网格全部覆盖，N_j=2 的单内部层也包括在内。

`boundedAffineLp` 用真实仿射函数在有界原域的可积性构造 `Lp ℝ 2 (volume.restrict Ω)`，其代表 a.e. 等于实际 p。新矩身份使用的是原

`(J_hv)_a=(∏jδ_j)⁻¹ ∫Ω v(x)φ_a(x)`，

而非另行定义的采样算子。已直接核对 `CartesianKuhnAffineMoment`：实际帽的零阶矩为 ∏δ_j，一阶矩为零；将仿射函数拆成节点值与连续线性部分，通过实际可积性和线性映射交换积分，得到 p 的真实仿射矩。新定理只把仿射 L² 类的 a.e. 身份代入同一积分。正 δ 给归一化质量非零。

`cartesianKuhnProjection` 是同一实际重构 `R_h(J_hv)`。闭单元公式使用实际节点数据零延拓和真实单纯形重心坐标。对每个单元顶点：内部情形由完整枚举、节点数据身份和上述仿射矩得到 p 值；非内部情形由真实零延拓为零及 p 的边界顶点零值得到相同 p 值。全部系数因此等于 p 在单元顶点的取值，实际 P1 插值的仿射再现给整个闭单元上的逐点等式，包含公共面和角点。

这里允许取点值的对象只有真实仿射 p、实际连续帽和重构函数。一般输入 u 只通过其真实 L² 类、弱导数和 a.e. 身份出现，未要求它存在点态连续或光滑代表。p 使用全域仿射 L² 类，并非裁剪块上的零延拓；也未错误要求 p 本身属于全域 H¹₀。

## 相减身份及代表精度

`cartesianKuhnMoment_sub` 使用真正 `Lp.coeFn_sub` 的 a.e. 身份，将 L² 类相减转成积分中的代表相减。两个帽配对的可积性均由实际 `cartesianKuhnMoment_integrable` 供应，随后合法使用积分相减及归一化标量分配。没有把 L² 的代表逐点相等当作前提，也没有利用不可积积分的默认值。

`cartesianKuhnProjection_sub` 在同一原有限帽函数和中使用各节点矩的相减身份，经有限和分配得到全空间逐点身份。它与仿射再现使用完全相同的 J_h、R_h、Q_h；没有换投影、换局部系数或引入额外的矩算子。

## 实际裁剪块与物理闭面

设中心单元的 Cartesian 整数原点为 c，各方向原域上端点为 `o_j+N_jδ_j`。本批沿用的实际裁剪端点为

`a_j=max(o_j,o_j+(c_j−2)δ_j)`，

`b_j=min(o_j+N_jδ_j,o_j+(c_j+3)δ_j)`。

已直接核对 `CartesianClippedPatch` 和 `CartesianKuhnPatchProjection`：此 B 精确等于相应开坐标盒，也等于原域与实际加宽邻域的交；其边长满足 `δ_j≤b_j−a_j≤5δ_j`。原活动帽的 `Function.support`（非零点集合）位于这份 B 中；此处不把包括物理边界的闭支撑误称为开域的子集。已有实际 Q_h 局部性和有限重叠证明使用的也是同一份块，并未只以几何直觉替代定义。

新证明先由实际 Kuhn 单元的坐标界将整个闭 K 放入 `[o+cδ,o+(c+1)δ]`，再用 c≥0、c+1≤N 和 max/min 端点放入 `[a,b]`。后者逐坐标包含于原物理闭盒。

物理面集合遍历有限 `Fin(n)×Bool`，只保留下端点等于 o_j 或上端点等于 `o_j+N_jδ_j` 的对应面。由于实际中心单元索引存在，逐轴 N_j>0；δ_j>0 使原盒非退化，真实开盒闭包就是原闭盒。所选面已在该闭包内，且其相应坐标严格等于原边界端点，故不属于原开域；开域的 interior 等于自身，由此得到整个所选闭面属于原 frontier。

反向覆盖从任意 `x∈K` 且 `x∉Ω` 出发。已知 x 位于原闭盒，所以某个失败的严格坐标只能等于原下端点或上端点。又因 x 位于裁剪闭盒，其对应裁剪端点必须等于同一个原物理端点，故该面确实属于所选集合，且 x 位于该完整闭面。证明针对所有这样的 x，不只针对面内部或单元顶点；角点与多重面交线没有被排除。

因此，p 在所选物理闭面上为零就供应中心单元所有边界点及边界顶点的零值。没有强迫 p 在人工邻域面上消失，没有要求整个域关于节点对称，也没有额外边界光滑性要求。

## 原全部弱状态、同一仿射函数与统一常数

最终类型先固定 d 与 κ≥1，再给 `∃C>0`，其后才量化全部 o、δ、正步长证明、N、实际单元 i、h>0、`h/κ≤δ_j≤h` 和原全局弱 H² 状态 u。唯一边界状态要求是其真实 L² 值属于原 `dirichletSubspace Ω`，即实际 H¹₀ 空间。没有额外光滑性、节点值、已知零迹、单元内 H² 代表、特殊状态子空间或目标估计前提。

最终定理对实际维数 n=d+1 使用已验收 `dirichlet_h2_local_boundary_affine d (5κ)`。κ≥1 给 5κ≥1；实际块的边长内部满足

`h/(5κ)≤h/κ≤δ_j≤b_j−a_j≤5δ_j≤5h≤5κh`。

因此调用 B.1 的比较参数只扩大为 5κ，常数仍仅依赖维数和原 κ，并且选择在全部网格、位置、h、单元及 u 之前。固定 n 的数值因子 5 不引入网格数量、总尺度或状态依赖。所有除数均由 κ≥1 和 h>0 处理，未除以 u 的范数或 Hessian。

直接核对实际 `DirichletLocalAffine`、`DirichletBoxFace`、`SubdomainRestriction`、`DirichletSpace`、`BoundaryAffineLemma`、`PhysicalBoxBoundaryAffine`。这些关键文件与已经独立审查的 T083 固定版本逐字节相同：原 H¹₀ 是全空间测试函数在真实 H¹ 图拓扑中的闭包；限制算子和真实物理面迹的连续性使全局 Dirichlet 条件传到局部物理面零迹。再由原弱 H² 的实际限制和 B.1，得到 p 与局部弱 H¹ 残差 r。没有把“全局零边界”直接当作光滑函数处处零，也没有另加迹资格。

输出同一个 p 同时满足物理闭面点态零值、实际 Q_h 的闭单元再现和局部逼近。r 是真实 `WeakSobolevJet n 1`，其值在局部盒上 a.e. 等于原 u−p，且

`‖value r‖ + h‖field 1 r‖ ≤ C h² bochnerL2Norm(volume.restrict B)(field 2 u)`。

左端为真实局部 L² 值和全梯度范数，不是系数型或人为定义的能量。右端由 `subdomainLp_norm_eq_bochner` 将实际限制 L² 范数精确改写为同一个原 Hessian 场在 B 上的 Bochner L² 范数；B⊆Ω 供应真正局部可积性，不引入体积归一化、补零 Hessian 或域外代表替代。

最终正维接口 n=d+1 覆盖原所有 n≥1；辅助顶点和仿射再现声明还允许零维。κ=1、零状态、零 Hessian 均无需额外排除，h=0 明确不属于原正网格尺度。局部 r 不被假称为整个 B 的 H¹₀ 函数，其所需结论仅为真实 H¹ 残差和物理面兼容性。

## 固定版本、构建和递归公理

四模块的 Carleman 导入闭包共 255 个模块，其中 251 个既有模块相对 base 逐字节未变；root 明确导入四个新模块。AGENTS、治理和 state 协议与已读版本一致；原论文、Lean/mathlib pin 和两个 CI workflows 相对 base 未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

实际读取固定 `/tmp/carleman-kuhn-local-affine-target.log`，定向构建 3445 jobs 成功；`/tmp/carleman-kuhn-local-affine-full.log` 显示全库 3784 jobs 成功并完成 6122 声明递归审计。固定 `/tmp/carleman-kuhn-local-affine-local-axioms.txt` 为 1,809,006 bytes，SHA256 `bb6037b6999944c694170ebcfd15c7479d9312b1f80fcb4ade5bf8d0cf1d31fc`。

全部 14 项实际完整类型逐项与源码对照，各有恰一条类型及恰一条显式公理检查，均只使用 `propext`、`Classical.choice`、`Quot.sound`。全产物 2006 条带公理打印、2002 个不同带公理声明及 6 条无公理打印已经扫描，无白名单外公理；末行实际为 `Axiom audit passed for all 6122 Carleman declarations.`。递归审计程序相对 base 未改，仍检查整个 Carleman 声明环境，本批只增加显式类型及公理打印。四新模块无 sorry、admit 或新增数学公理。

## 远端证据与签发

已独立查询 [main CI run 39187677676 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39187677676/attempts/1)，确认事件为 `push`、分支为 `main`、head SHA 为本次固定 `fc89f7ab4516bb6dd97a43a2e5224e722b0b7a56`。run 最终为 `completed/success`，最后更新时间 `2026-10-19T02:02:21Z`；三个实际 jobs 均最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `state-check` | `117853442216` | `completed/success` |
| `lean` | `117853442295` | `completed/success` |
| `dashboard / snapshot` | `117854558409` | `completed/success` |

独立读取同次原始 `/tmp/carleman-kuhn-local-affine-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha` 精确为上述固定 SHA，`finished_at=2026-10-19T02:00:16.465988+00:00`，target 为 `Carleman`。Lean 4.35.0 Linux commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，均与固定源码 pin 一致。

独立查询远端 artifact 元数据，`lean-ci-result`（ID `12157849575`）及 `lean-declaration-evidence`（ID `12158513783`）均未过期，各自绑定本次同 run、main 分支及固定 SHA。下载的原始 `/tmp/carleman-kuhn-local-affine-main-axioms/axioms.txt` 与固定本机副本逐字节完全一致：1,809,006 bytes，SHA256 `bb6037b6999944c694170ebcfd15c7479d9312b1f80fcb4ade5bf8d0cf1d31fc`。

对远端原始产物再次核对 14 项完整类型和每项公理依赖，全部匹配；2006 条带公理打印仅含三项正常基础公理，另有 6 条无公理打印，末行确认全库 6122 声明递归审计通过。没有采用后续工作树 `.ci/axioms.txt`，也没有混入后续数学模块。

最终 **AUXILIARY / PASS**，未发现本批声称范围内的数学缺陷。可将 C110 按 **AUXILIARY / REVIEWED** 记录。原文保持 **13/26**；完整梯度误差、允许权、全域组装、B.2/P026 和 FD/P012 不随本报告提升。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
