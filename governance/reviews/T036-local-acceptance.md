# T036 / C052 — 单纯形分区与局部节点插值独立验收

- checked_sha: `885add73e59dd08e5609597cac3c2ddd7fd395bd`
- base_commit: `f919944fb3755af8f9ab8cb92ea7a0970ae69d67`
- reviewed_at: `2026-10-18T17:43:20+00:00`（UTC）
- reviewer: 独立数学验收 Agent `/root/accept_spatial_lemma`，非本阶段执行者
- target: 三个 Spatial 模块、全部 30 项显式声明
- result: **PASS**；独立数学语义核对及同 SHA 正式构建门槛通过
- axiom_check: **PASS**；同 SHA 远端 4069 声明递归审计及本批 30 项检查
- scope: **AUXILIARY**
- extra_hypotheses: `[]`（所述辅助命题的几何与测度输入均公开；完整网格义务见下文）

本次直接用 `git show <checked_sha>:<path>` 读取全部三个模块、全部实际展开类型和相关依赖，对照原 `paper/main.tex` Section 6.1 的 P1 网格与空间定义（1469–1500）、节点插值与超逼近使用（1523–1544、1569–1593），以及 Section 6.2 的 Cartesian/Kuhn 重构（1634–1667）。另读固定 MATH_SPEC、T036 分析文档、C052/T036 清单及上游 T035 验收。根 AGENTS、治理/证据协议与此前已读版本相同；不审核后续工作树草稿。

## 验收结论与原文映射

本批建立真实有限顶点凸包的基础几何、由覆盖和内部不交推出的 a.e. 分区、该分区上的有限维 L² 分片仿射交空间，以及单个非退化单纯形上的真实重心节点插值。未发现数学、类型、边界、代表或量词缺陷。同 SHA 构建门槛已通过，C052 可升为 `REVIEWED/AUXILIARY`。

它为原 P1 定义 `V_h={v∈H₀¹: v|K∈P₁}` 和原节点插值提供局部几何/代数基础，也可用于未来 Kuhn 单纯形重构。它不证明任何完整具名原文结论，P011/P012 及其他论文覆盖不得因此提升。原 FD 的质量是节点对角质量，不能把这里的 L² 子空间自动识别为原 FD 状态内积或标准差分算子。

## 凸包、边界零测与显式半径

`simplicialCell v` 精确定义为 `convexHull ℝ (range v)`，其中 v 是实际 Euclidean d 空间的 d+1 个顶点。凸性由 convexHull 获得，有限顶点集在有限维空间中的凸包紧性给紧、闭、可测。此处不假设顶点仿射独立；退化、重复顶点也在前三类几何结论中覆盖。

`simplicialCell_frontier_null` 使用 mathlib 的真实 `Convex.addHaar_frontier volume`。已直接检查固定 mathlib 依赖的类型和证明：它适用于有限维实空间的 Haar 测度与任意凸集，不额外要求非空内部；退化情形由真仿射子空间的 Haar 零测处理，满仿射包情形由内部及伸缩论证处理。因此没有对退化单元错误套用“有内部”的版本，也没有把任意测度下的边界都当作零测。本次结论具体使用 Euclidean Lebesgue volume，符合原文几何。

内部非空是单独的 `simplicialCell_interior_nonempty`：输入 `Affine.Simplex ℝ (SpatialCoordinates d) d`，其 fields 提供 d+1 个仿射独立顶点。真实坐标空间 finrank=d，故 `Affine.Simplex.affineSpan_eq_top` 给满仿射包；凸集内部非空等价式与 `affineSpan_convexHull` 才给结论。没有从任意 d+1 顶点数组推断非退化。

对有限族 v，`simplicialRadius v=∑i∑k‖v_i,k‖` 非负。每个顶点范数小于等于此和，包含它们的闭球凸，因此整个凸包都在同一闭球内。该界不除以半径，不需要严格正，也没有漏掉常数坐标项——后续 L² 生成元使用 `max 1 R`。半径可能随单元数、平移位置和顶点而变化；它仅作可积性构造见证，不被当成网格大小、形状正则性、插值误差或任何网格统一常数。

## 从几何覆盖到真实 a.e. 分区

`simplicialCells_ae_partition` 的输入为有限顶点族、可测 S、S 的实际逐点覆盖以及任意两个不同单元内部不交。对每个 i，先把已证 volume(frontier K_i)=0 限制到 S；再以有限索引的 `ae_all_iff` 合并边界异常集。对 S 中避开全部边界的点，覆盖提供某个 K_i；若也在 K_j，则“在集合内且不在 frontier”给两个内部成员，内部不交迫使 j=i。输出实际类型包含 a.e. **存在和唯一归属两者**，不只是两两 a.e. 不交。

共享面和非匹配边界交叠被允许，因为本层只要求体积意义的唯一归属。原网格的完整面匹配条件没有被推断出来。没有对边界上的代表指定唯一单元，也没有用边界面积零代替体积零。该引理连退化单元也可处理；真非退化 simplex 只在后续结构与节点基中要求。

`SimplicialPartition` 记录真实 simplex、每个闭单元包含于 closure S、覆盖 S 和内部两两不交。其结构本身不携带 Fintype 字段；需要有限性的 `cells_union`、a.e. 分区和空间构造均在实际类型中显式要求 `[Fintype ι]`。顶点属于 closure S 则不需要有限性。有限闭单元并为闭集，结合覆盖和 inside 精确证明 `⋃i K_i=closure S`；没有额外假设 S 本身闭。

这些结果允许 d=0、空索引和空 S。d=0 的真 0-simplex 在零维全空间有非空内部，边界仍为空；空索引时覆盖强制 S 为空，所以 a.e. 存在唯一单元的结论在零测度下成立，不产生错误的非空单元。没有隐式假定 d≥1 或 ι 非空。

## 真实分片空间与公开的有限测度条件

`M.conformingSpace V` 调用已验收的真实 piecewiseAffineSpace 构造，自动供应实际凸包可测性、上述显式半径和逐点有界性，再与给定 V 相交。`IsFiniteMeasure(volume.restrict S)` 仍是公开实例要求，适合原有界区域；本批没有额外把它声明为已从几何结构得到的实例。V 也是输入的真实 L² 子空间，不是已在这里识别的 H₀¹。

已直接复核 `PiecewiseAffineLp` 和 `PiecewiseAffinePartition` 的本次调用：生成元是真实 `1_K` 乘常数/坐标，通过 MemLp.toLp 形成 a.e. 类；空间是有限系数数组线性映射的 range。有限维由有限维系数域的像得到，与 V 的交保留有限维；既不假设目标空间有限维，也不要求 V 有限维或生成元线性无关。半径选择不改变实际空间，既有 bound_independent 定理覆盖此点。

`mem_conformingSpace_iff` 将已构造的真实 a.e. 分区传给上游双向刻画，输出准确为

`u∈V ∧ ∀i, ∃c_i, u(x)=c_i,0+∑j c_i,j+1 x_j for a.e. x∈K_i`。

a.e. 是相对于 volume.restrict S，不能据此给共享顶点或区域边界赋值。正向由唯一归属消去其它 indicator 项；反向合并有限个异常集并利用覆盖构造全域系数表达。V 成员条件没有被删去。交空间本身不会自动证明跨面连续、H¹、零迹、非平凡性、节点自由度或逼近密度；这些仍需具体 V 和网格实现。

## 重心节点插值的真实内容

`simplexAffineBasis` 使用同一 simplex 的 points、原 affine independence 以及 finrank=d 导出的满仿射包。基点等于原顶点是 rfl；没有另选不相关仿射基。重心坐标是该 AffineBasis 的实际 AffineMap coord。顶点值为准确 Kronecker δ，坐标和在**整个空间**等于 1；单元内非负由已核查的 `AffineBasis.convexHull_eq_nonneg_coord` 给出。非负性只在 convex hull 内声称，并未错误延拓到全空间。

`simplexNodalInterpolant T c=∑i c_i λ_i` 是实际全空间仿射多项式，输入明确为 `Fin(d+1)→ℝ`。apply 定理逐项展开仿射映射的有限和与标量乘法。顶点保持使用 δ 值，保留每个节点；再现定理使用仿射基的真实坐标仿射组合与仿射映射保持组合，输出 AffineMap 相等，所以对任意仿射 p 在全空间成立，而非仅在顶点或单元上。

稳定定理的正式类型是：若每个 `|c_i|≤C`，则每个 x∈K 有 `|I_Tc(x)|≤C`。证明以三角不等式、λ_i≥0、∑λ_i=1 得到常数 1，完全不含单元直径、形状、维数或半径。没有额外 C≥0 前提，因为非空 Fin(d+1) 上的节点假设已经蕴含它；证明也不作非法除法。这是原局部 L∞ 稳定性的点态形式，本批没有另定义一个 L∞ Banach 空间算子或给出导数/L² 误差估计。

本层仅给定实际点值数组，或对真实 AffineMap p 取其顶点值。没有接受 `Lp`/H¹/H² 等价类再在顶点求值，没有假设尚未建立的连续代表。原文 1532 行所需 d=2,3 的 H²→C⁰ 供应仍待。不同单元的局部插值也没有通过共同节点表或面匹配组装；不能把局部顶点保持和全空间仿射再现自动提升为全局连续、H₀¹ 或保持边界的插值算子。

## 全部 30 项声明

下表顺序与交付名单及固定 C052/T036 台账相同；逐项检查实际类型、证明与递归公理。

| # | 完整声明 | 独立结论 |
| --- | --- | --- |
| 1 | `Carleman.simplicialCell` | PASS；真实有限顶点凸包。 |
| 2 | `Carleman.simplicialCell_convex` | PASS；凸包凸性，无非退化假设。 |
| 3 | `Carleman.simplicialCell_compact` | PASS；有限维有限点凸包紧。 |
| 4 | `Carleman.simplicialCell_measurable` | PASS；紧闭集的 Borel 可测性。 |
| 5 | `Carleman.simplicialCell_frontier_null` | PASS；真实 Haar/Lebesgue 边界零测，含退化情形。 |
| 6 | `Carleman.simplicialCell_interior_nonempty` | PASS；真 d-simplex 的满仿射包给非空内部。 |
| 7 | `Carleman.simplicialRadius` | PASS；显式全部顶点范数的有限和。 |
| 8 | `Carleman.simplicialRadius_nonneg` | PASS；各项非负。 |
| 9 | `Carleman.simplicialCell_norm_le` | PASS；顶点闭球界经凸包传到全单元。 |
| 10 | `Carleman.simplicialCells_ae_partition` | PASS；真实覆盖加内部不交和已证零边界给 a.e. 唯一归属。 |
| 11 | `Carleman.SimplicialPartition` | PASS；真实非退化 simplex 与 inside/cover/disjoint，未包含面匹配。 |
| 12 | `Carleman.SimplicialPartition.cell` | PASS；取真实 simplex 顶点凸包。 |
| 13 | `Carleman.SimplicialPartition.vertex_mem_closure` | PASS；顶点在本单元并由 inside 落入 closure S。 |
| 14 | `Carleman.SimplicialPartition.cells_union` | PASS；有限闭单元并准确等于 closure S。 |
| 15 | `Carleman.SimplicialPartition.ae_partition` | PASS；实例化已证几何 a.e. 分区。 |
| 16 | `Carleman.SimplicialPartition.conformingSpace` | PASS；实际 L² 分片仿射 range 与 V 的交。 |
| 17 | `Carleman.SimplicialPartition.conformingSpace_finiteDimensional` | PASS；有限维性内部供应，V 无此额外前提。 |
| 18 | `Carleman.SimplicialPartition.conformingSpace_le` | PASS；真实交空间包含 V。 |
| 19 | `Carleman.SimplicialPartition.mem_conformingSpace_iff` | PASS；所有 L² 类的准确 V 成员及逐单元 a.e. 仿射刻画。 |
| 20 | `Carleman.simplexAffineBasis` | PASS；真实 simplex 的顶点、独立性和满仿射包。 |
| 21 | `Carleman.simplexAffineBasis_apply` | PASS；基点就是原顶点。 |
| 22 | `Carleman.simplexBarycentric` | PASS；真实 AffineBasis 坐标 AffineMap。 |
| 23 | `Carleman.simplexBarycentric_vertex` | PASS；全部顶点的 Kronecker 值。 |
| 24 | `Carleman.simplexBarycentric_sum` | PASS；全空间坐标和为 1。 |
| 25 | `Carleman.simplexBarycentric_nonneg` | PASS；仅在真实单元内要求非负。 |
| 26 | `Carleman.simplexNodalInterpolant` | PASS；真实节点数组的仿射插值多项式。 |
| 27 | `Carleman.simplexNodalInterpolant_apply` | PASS；精确 sum(c_i λ_i) 展开。 |
| 28 | `Carleman.simplexNodalInterpolant_vertex` | PASS；所有输入节点值精确保持。 |
| 29 | `Carleman.simplexNodalInterpolant_reproduces` | PASS；任意真实仿射函数在全空间再现。 |
| 30 | `Carleman.simplexNodalInterpolant_abs_le` | PASS；真实单元上点态 L∞ 稳定，常数 1。 |

## 依赖、剩余义务与构建证据

已读取 [T035 / C051 独立验收](T035-local-acceptance.md)，其固定 SHA 即本批基线；本次另直接检查 PiecewiseAffineLp/Partition 的生成元、有限维证明和成员刻画实参。基线至本次提交没有修改既有 Carleman 数学文件，新增数学模块恰为这三个，均由固定 `Carleman.lean` 显式导入。原稿、Lean/mathlib pin、治理协议与 CI 工作流未变。实际检查的 mathlib HEAD 为固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，相关 Convex/AffineSpace 源码无本地修改。

未清偿的原文义务包括：具体 conforming 面匹配网格、统一形状正则与原分级条件、Cartesian/Kuhn 的具体数据和全局节点基、Sobolev 连续代表和零边界点值、全局连续/H₀¹ 插值、局部 h/h² 误差、梯度逆界、加权投影稳定性和超逼近，以及具体热连续 CE。局部稳定常数 1 与上述估计不是同一结论。本报告没有把此辅助阶段当作 P011/P012、完整 N3/N4 或物理控制完成。

固定 `/tmp/carleman-simplicial-nodal-full.log` 记录 `Build completed successfully (3535 jobs).`。固定本机公理副本 `/tmp/carleman-simplicial-nodal-local-axioms.txt` 为 1180191 字节，SHA-256 为 `befea58600e469f44043dbba22d7ba4cfc81518ad85b7e14e6dd13785b90177c`。30/30 项均有实际完整类型与逐项公理输出，各项仅有 `propext`、`Classical.choice`、`Quot.sound`；全局末行是 `Axiom audit passed for all 4069 Carleman declarations.`。固定审计器递归检查全部公开/私有 Carleman 声明，仅允许上述三项基础公理，无 sorryAx 或新增数学公理。

已通过 GitHub connector 独立读取 [main CI 39150398479 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39150398479/attempts/1)，确认 head SHA 为本次固定 SHA、head_branch=main、event=push、status=completed、conclusion=success。三个实际 jobs 均完成且成功：state-check（117742862872）、lean（117742863088）、dashboard / snapshot（117743575256）。同次 artifact 元数据中 `lean-ci-result`（12144218870）和 `lean-declaration-evidence`（12145200832）均绑定上述 run 和固定 head SHA。

已独立读取原始 `/tmp/carleman-simplicial-nodal-main-ci/result.json`，537 字节，SHA-256 为 `98756ee430e81c6df9fc0d26e8275fd269d7bce0fea2d97e98a95d1e2c733431`。实际内容为 PASS，checked_sha=source_head_sha=`885add73e59dd08e5609597cac3c2ddd7fd395bd`，目标 Carleman，finished_at=`2026-10-18T17:39:42.379331+00:00`，Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

正式远端 `/tmp/carleman-simplicial-nodal-main-axioms/axioms.txt` 为 1180191 字节，SHA-256 为 `befea58600e469f44043dbba22d7ba4cfc81518ad85b7e14e6dd13785b90177c`。已实际逐字节比较确认与固定本机副本相同，再次针对远端文件逐名核对 30/30 项完整类型及三项标准基础公理集合，并确认全局 4069 声明审计 PASS。没有用其它提交或后续数学草稿替代本次正式证据。

本次只写本报告，未修改代码、台账、根导入、原稿或覆盖表，未 commit/push。
