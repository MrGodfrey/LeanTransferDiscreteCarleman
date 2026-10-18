# T035 / C051 独立本机验收

- `checked_sha`: `f919944fb3755af8f9ab8cb92ea7a0970ae69d67`
- `base_commit`: `27c5e0e5a60b860f08e4c74c5d7de81f7498781f`
- `semantic_checked_at`: `2026-10-18T17:31:53+00:00`
- `reviewed_at`: `2026-10-18T17:34:33+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- 范围：**AUXILIARY**。验收真实分片仿射 L2 类、a.e. 分区刻画、内部有限维性及原形式的 Galerkin 刚度构造；不提升 P011 / Proposition 6.1、P012 / Proposition 6.2 或其他完整原文覆盖。

本报告直接读取固定 Git 提交中的三个新模块、全部 24 项展开类型与递归公理结果、相关既有依赖，以及原 `paper/main.tex`。执行者分析和旧报告只用于定位范围，没有代替源码、证明或原文核对；后续未提交的网格草稿不参与验收。

## 全部 24 项声明

除第 19–24 项使用前缀 `Carleman.Physical.` 外，其余均使用 `Carleman.`。位置为固定提交下的文件和行号；表中 PASS 为逐项数学语义结论。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `affineCoordinate` | `Spatial/PiecewiseAffineLp.lean:15` | PASS；Fin(d+1) 的首项为真实常数 1，其余为 Euclidean 坐标 x_j。 |
| 2 | `affineCoordinate_continuous` | `Spatial/PiecewiseAffineLp.lean:18` | PASS；分别使用常数和坐标投影连续性，不是假定抽象生成元连续。 |
| 3 | `affineCoordinate_bound` | `Spatial/PiecewiseAffineLp.lean:23` | PASS；真实界 `|coordinate|≤max 1 ‖x‖`，坐标界无 d 因子。 |
| 4 | `affineCellGenerator` | `Spatial/PiecewiseAffineLp.lean:30` | PASS；实际 indicator 乘常数/坐标，经 MemLp.toLp 构造真实 Lp 类，有限测度与 a.e. 有界性显式。 |
| 5 | `affineCellGenerator_ae` | `Spatial/PiecewiseAffineLp.lean:41` | PASS；代表与原 indicator 函数 a.e. 相等，未声称点值相等。 |
| 6 | `piecewiseAffineMap` | `Spatial/PiecewiseAffineLp.lean:51` | PASS；有限系数阵列的真实有限线性组合，并证明加法、标量乘法相容。 |
| 7 | `piecewiseAffineMap_ae` | `Spatial/PiecewiseAffineLp.lean:57` | PASS；Lp 有限和与标量乘法的 a.e. 代表公式逐层组合。 |
| 8 | `piecewiseAffineSpace` | `Spatial/PiecewiseAffineLp.lean:74` | PASS；定义为上述实际线性映射的 range。 |
| 9 | `mem_piecewiseAffineSpace_iff` | `Spatial/PiecewiseAffineLp.lean:76` | PASS；range 成员与全域 a.e. 指示函数表达双向等价，反向使用 Lp.ext。 |
| 10 | `piecewiseAffineSpace_bound_independent` | `Spatial/PiecewiseAffineLp.lean:88` | PASS；任意两个合法 R/hR 给同一子空间，消去构造性可积性见证的影响。 |
| 11 | `piecewiseAffineSpace_finiteDimensional` | `Spatial/PiecewiseAffineLp.lean:94` | PASS；有限索引系数空间的线性像有限维，未把待证空间有限维列为前提。 |
| 12 | `conformingPiecewiseAffineSpace` | `Spatial/PiecewiseAffineLp.lean:101` | PASS；定义为实际 range 与给定 V 的交。 |
| 13 | `conformingPiecewiseAffineSpace_finiteDimensional` | `Spatial/PiecewiseAffineLp.lean:104` | PASS；交空间包含于已证有限维的 range，无须 V 有限维。 |
| 14 | `conformingPiecewiseAffineSpace_le` | `Spatial/PiecewiseAffineLp.lean:108` | PASS；真实子空间包含关系 X≤V。 |
| 15 | `affineCoordinate_sum` | `Spatial/PiecewiseAffinePartition.lean:15` | PASS；常数项和 Fin d 的一次项索引完全正确，Fin.succ 未漏项或重计。 |
| 16 | `piecewiseAffine_formula_on_cell` | `Spatial/PiecewiseAffinePartition.lean:20` | PASS；单个点唯一归属某单元时，其他 indicator 为零，恰得到该单元的仿射多项式。 |
| 17 | `mem_piecewiseAffineSpace_iff_on_cells` | `Spatial/PiecewiseAffinePartition.lean:42` | PASS；a.e. 分区上全域 range 与每个单元上 a.e. 仿射的双向等价，覆盖条件在反向实质使用。 |
| 18 | `mem_conformingPiecewiseAffineSpace_iff` | `Spatial/PiecewiseAffinePartition.lean:67` | PASS；精确为 `u∈V ∧ 每单元 a.e. 仿射`，没有删去 V 成员条件。 |
| 19 | `affineGalerkinSpace` | `Control/PiecewiseAffineGalerkin.lean:22` | PASS；V 取原 `a.V`，不是额外指定的任意有限维状态空间。 |
| 20 | `affineGalerkinStiffness` | `Control/PiecewiseAffineGalerkin.lean:24` | PASS；内部有限维实例及 X≤a.V 供应真实 L2 Riesz Galerkin 构造。 |
| 21 | `affineGalerkinStiffness_pairing` | `Control/PiecewiseAffineGalerkin.lean:28` | PASS；对所有 x,y∈X，L2 内积精确等于原 a.scalarForm 在真实包含上的值。 |
| 22 | `affineGalerkinStiffness_symmetric` | `Control/PiecewiseAffineGalerkin.lean:34` | PASS；由原形式对称及真实配对得到算子对称性。 |
| 23 | `affineGalerkinStiffness_nonneg` | `Control/PiecewiseAffineGalerkin.lean:38` | PASS；由原形式 coercive 字段推出每个状态的非负二次型。 |
| 24 | `affineGalerkinSpace_membership` | `Control/PiecewiseAffineGalerkin.lean:43` | PASS；a.e. 分区下的原 V 交空间完整成员刻画，没有假定额外节点值。 |

## 原文映射与范围

原稿 Section 6.1，`paper/main.tex:1469–1485`，固定有界凸多面体 Ω、d∈{2,3}、V=H₀¹(Ω)、梯度形式及一致单纯形网格，继而定义

`X_h=V_h={v∈H₀¹(Ω):v|K∈P₁}`，`(A_h z,w)_{L²}=a(z,w)`。

第 1–18 项构造该空间定义的 L2 等价类版本所需的代数与测度论部分；第 19–24 项在给定原形式上给出相应的一致质量 Galerkin 刚度。这里逐单元仿射性按 a.e. 理解，符合 Sobolev/L2 等价类的层次；具体网格上的连续代表、零迹和节点表示仍须额外识别。

原稿 Section 6.2，`paper/main.tex:1656–1658`，通过 Kuhn 单纯形和节点基函数构造 `R_h z=Σz_i φ_i`。本阶段的有限仿射空间是可供该重构落入的辅助空间，尚没有给出 Kuhn 网格或节点基函数，也没有证明这个 range 等于具体重构的像。`paper/main.tex:1640–1654` 的 FD 内积是对角质量，算子是标准 (2d+1) 点差分；本阶段 Galerkin 算子使用 L2 一致质量，**不能直接认作原 FD 算子**。原 `eq:fdstiffness` 在 `1683–1703` 的边计数和精确刚度恒等式仍待建立。该区别不影响本次明确 AUXILIARY 的结论。

## 真实生成元、可积性与量词

`SpatialCoordinates d` 为真实 Euclidean 坐标空间。`Fin.cases` 定义常数坐标与 d 个线性坐标；`Fin.sum_univ_succ` 给出的多项式正是 `c₀+Σc_{j+1}x_j`。生成元定义使用连续坐标的强可测性和可测单元 indicator，实际函数模被 `max 1 R` a.e. 控制。已核对 mathlib 的 `MemLp.of_bound`：它在有限测度下从该真实函数有界性推出 MemLp，随后 `toLp` 形成等价类；这里没有自由指定的“L2 范数”或任意形式替身。

`IsFiniteMeasure ν`、有限单元索引、每个 K_i 可测，以及共同 a.e. 坐标范数界 R 均是公开前提。它们适合后续在有界 Ω 上使用受限 Lebesgue 测度；本阶段并未构造这个具体测度/网格实例。一般无限总测度的版本不在当前声明范围。R 不要求严格正：空单元、零测度单元和负 R 强迫的 a.e. 空情形仍由实际 indicator 界正确处理，没有除以 R。空间对合法 R 的选择已证明独立，未把 R 当成统一误差常数。

代表公式逐一使用 `Lp.coeFn_finsetSum`、`Lp.coeFn_smul` 和 `MemLp.coeFn_toLp`。从函数 a.e. 等式回到空间成员时使用 `Lp.ext`，所以不同等价代表不会改变空间。维数来自有限系数域 `ι→Fin(d+1)→ℝ` 的 range；不要求生成元线性无关、不要求非退化单元，也未声称维数恰等于单元数乘 (d+1)。重复/零测度单元可降低维数；证明仍成立。

所有公式对任意 d、任意有限单元族及相应全部 L2 状态成立，包括 d=0 和空索引类型。空索引时 range 是零空间；a.e. 分区前提若成立则 ν 必为零测度，因此逐单元刻画的空量词与零 L2 空间相容，没有空真导致错误推广。阶段没有时间、T、方向、Carleman 权或 h 误差参数；它也不输出任何随网格统一的稳定性/逼近常数。

## 分区、交界与一致性

分区前提的实际类型是

`∀ᵐ x∂ν, ∃i, x∈K_i ∧ ∀j, x∈K_j → j=i`。

它同时要求 a.e. 覆盖和唯一归属，不只是两两 a.e. 不交。原有界域上体积零的公共面可被忽略，因而闭单纯形的零测度交界与此条件相容；代码并未证明具体公共面零测度。如果 ν 对交界赋正质量，或存在正测度未覆盖区，则不能套用该刻画。未提供分区时 range 仍有定义且有限维，只有全域 indicator 和表达成立；不能无条件声称它就是任意重叠单元上的逐片多项式空间。

正向逐单元证明将全域 a.e. 代表等式与分区结合，利用唯一归属消去其他项。反向从每个单元独立存在的系数使用 choice 选取有限系数族，借 `ae_all_iff` 合并有限个异常集，再用 a.e. 覆盖选取当前单元。没有要求同一点可属于多个正测度重叠单元，也没有在异常集上强行匹配多项式。

交空间定义只保证 X≤V；它不会仅凭分片仿射性推出 H¹ 正则性、跨面连续性或零 Dirichlet 迹。对于将来的具体 V=H₀¹ 实例，V 成员条件会强制这些 Sobolev/边界限制；目前该识别仍未完成。特别是空间可能为零，本阶段没有证明非平凡性、节点自由度、逼近密度或某个节点基为基，未用这些未证结论支撑后续刚度。

## 原形式和真实 L2 刚度

已直接追查 `OriginalForm`、`valueEquiv`、`scalarForm` 和 `Control/GalerkinStiffness.lean`。原 V 是 L2 子空间，嵌于实际弱 Sobolev 空间，并带相应闭性、稠密性和真实 Sobolev Hilbert 范数下有界、对称、coercive 的形式。`valueEquiv` 由弱 jet 的值嵌入及其已证双射构成；`scalarForm` 是这一等价下原形式在 V 上的真实表达。

对新 X=range∩a.V，`conformingEnergyLift` 是 X 包含入 V 后经 `valueEquiv.symm` 回到原能量空间。其连续性来自已证明的 X 有限维，而非假定原 V 的 Sobolev 范数由全空间 L2 范数控制。`galerkinStiffness` 将拉回形式经 X 的 L2 Riesz 逆映射到 X；有限维性也供应 X 的完备性。新实际类型没有 `FiniteDimensional ℝ X` 或 `CompleteSpace X` 的外部前提，所需实例均内部得到。

配对式对每个 x,y∈X 成立，且使用 X 从 L2 继承的内积。对称性由原形式对称性和实内积交换性推出；非负性由正 coercivity 常数乘能量范数平方的非负性推出。这里没有引入人为正定矩阵、独立于 a 的算子或把目标配对式/非负性作为新输入。有限维连续性可能具有随 X 改变的算子界，但本阶段不从该存在性导出网格统一估计，因而没有把这种界偷渡到数值常数。

保留的局部有限测度/紧集有限测度实例用于既有真实 Sobolev 与形式接口；它们不改变本阶段由有限测度与实际状态生成的数学结论。成员刻画不需要局部有限实例，实际类型中已省去该未使用前提。

## 尚未清偿的原文义务

本阶段没有供应具体一致、形状正则单纯形网格及原 grading 条件；没有供应 Cartesian/Kuhn 网格、节点基、零边界节点和单元/边计数；没有实例化 `V=H₀¹`、梯度形式和 Dirichlet Laplacian。加权投影稳定性、局部逆界、实际插值、h/h² 逼近、超逼近、具体原 N1–N5 及连续热 CE 都不能因本次定义和刚度成立而视为完成。P011/P012 与任何下游完整物理覆盖保持原状态。

## 固定依赖、构建与公理

三模块的 Carleman 导入闭包为 286 个模块，其中 283 个既有模块相对于 base 逐字节未变，新增恰为本次三模块；三个新模块均在固定 `Carleman.lean` 中显式导入。原稿、Lean/mathlib pin 和两个 CI 工作流相对 base 未变。原稿 SHA256：`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

24 项清单与固定 C051/T035 清单、源码声明、审计脚本的显式 `#check`/`#print axioms` 逐项一致。已阅读实际完整类型，均无额外隐藏的有限维、节点值、网格正则或目标局部估计前提。固定 `/tmp/carleman-piecewise-affine-local-axioms.txt` 为 1,169,665 bytes，SHA256 为 `ebd4fe62f8bb6b9d1d8dd61ffc8c677c001ea9bd09864b572181a2f5b1bd869a`；24/24 仅递归依赖 `propext`、`Classical.choice`、`Quot.sound`。末行为 `Axiom audit passed for all 4006 Carleman declarations.`。

固定审计工具枚举所有经 `privateToUserName` 归属 Carleman 的公开/私有声明，逐个以 `collectAxioms` 递归检查，白名单仅有上述三项正常基础公理。没有 sorryAx 或未证明的新数学公理。实际 `/tmp/carleman-piecewise-affine-full.log` 记录 `Build completed successfully (3527 jobs).`，随后同一完整审计通过。工具链固定为 Lean 4.35.0、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。

已独立通过 GitHub connector 读取 [main CI 39149740857 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39149740857/attempts/1)：`head_sha=f919944fb3755af8f9ab8cb92ea7a0970ae69d67`，main/push、completed/success。三个实际 jobs 均成功：lean（117740927130）、state-check（117740927256）、dashboard / snapshot（117741550200）。Lean job 的固定工具链、根目标构建、版本/结果记录、公理产物上传步骤均 success。

同次 artifact 元数据确认 `lean-ci-result`（12144169842）和 `lean-declaration-evidence`（12144264517）均绑定 run 39149740857 及本次 head SHA。已实际读取 `/tmp/carleman-piecewise-affine-main-ci/result.json`：status=PASS，`checked_sha=source_head_sha=f919944fb3755af8f9ab8cb92ea7a0970ae69d67`，target=Carleman，`finished_at=2026-10-18T17:30:52.711429+00:00`，CI URL 为上述 attempt 1。记录的 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 mathlib pin 与固定源码一致。

正式远端 `/tmp/carleman-piecewise-affine-main-axioms/axioms.txt` 为 1,169,665 bytes，SHA256 为 `ebd4fe62f8bb6b9d1d8dd61ffc8c677c001ea9bd09864b572181a2f5b1bd869a`；已与固定本机副本逐字节比较，相同。另行检查远端文件内 24/24 项完整类型与递归公理列表，均仅含上述三项正常基础公理；实际末行确认全部 4006 项审计 PASS。没有使用后续草稿、另一 SHA 或仅凭执行者陈述替代此证据。

## 验收决定

**C051：PASS，可升级为 REVIEWED，scope 保留 AUXILIARY。** 本次 24 项未发现数学证明、类型、代表、量词或范围缺陷；同 SHA 实际 CI、类型和递归公理证据已齐备。该结论只验收本报告所列空间和原形式刚度构造，不得提升 P011/P012 或其他完整原论文覆盖。

本次仅写本报告，未修改证明、台账、原稿、root 导入或覆盖表，未 commit/push。
