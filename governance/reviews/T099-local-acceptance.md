# T099 / C115 独立本机验收

- `checked_sha`: `e6f194345f2f7b9822f8d8654a003aee071382a2`
- `base_commit`: `36d8ee7de732f00be2146ad4ef293ccf9c53c53f`
- `semantic_checked_at`: `2026-10-19T02:43:12+00:00`
- `reviewed_at`: `2026-10-19T02:45:01+00:00`
- `result`: **PASS**；语义、同 SHA 三项最终 CI 和原始产物均已独立核实。
- `axiom_check`: **PASS**；固定本机和同 run 远端原始公理文件逐字节一致。
- `scope`: **AUXILIARY**；原 Kuhn 弱刚度的精确坐标边组装，尚未完成原标准 Laplacian 的离散分部求和与最终 FD 刚度身份。原文保持 **14/26**。

独立直接读取固定提交三模块全部源码与证明、13 项实际完整展开类型、规格 `governance/analysis/T099-kuhn-stiffness-edges.md` 和关键依赖，对照原 `paper/main.tex:1634–1703` 的原物理网格、R_h、Dirichlet 梯度形式及刚度证明。执行者说明与 CI 不代替语义核查，后续工作树中的分部求和模块不属于本次范围。本验收自行查询固定 SHA 的 main CI 并下载两份同 run 原始产物。

## 全部 13 项声明

名称均省略公共前缀 `Carleman.`；源码位置相对于固定提交的 `Carleman/`。名单与交付 JSON、固定 C115 和 T099 台账完全一致。

| # | 声明 | 固定位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `finRotate_val_step` | `Geometry/FiniteCartesianShift.lean:13` | PASS；实际 Fin 循环旋转准确给非末点加一、末点归零，n=0 用空索引消去。 |
| 2 | `cartesian_sum_face_zero_shift` | `Geometry/FiniteCartesianShift.lean:24` | PASS；实际各坐标旋转组合成 Pi 等价，回绕两侧由 0/N 面零值消去，无回绕时整数点严格相等。 |
| 3 | `cartesianLatticeData` | `Spatial/CartesianLatticeDifferences.lean:13` | PASS；在真实物理格点上评价原完整内部节点数据的零延拓。 |
| 4 | `cartesianLatticeData_zero_face` | `Spatial/CartesianLatticeDifferences.lean:17` | PASS；实际整数坐标为 0 或 N_j 时物理点不在原开域，原数据延拓确为零。 |
| 5 | `cartesianLatticeSuccessor` | `Spatial/CartesianLatticeDifferences.lean:29` | PASS；仅所选坐标增加整数 1；该定义不依赖任何公理。 |
| 6 | `cartesianAxisDifference` | `Spatial/CartesianLatticeDifferences.lean:32` | PASS；原数据在真实相邻坐标格点上的前向差商，分母为该方向的真实 δ_r。 |
| 7 | `cartesianAxisDifference_zero_transverse` | `Spatial/CartesianLatticeDifferences.lean:36` | PASS；横向边界坐标不被后继改变，两个端点都在同一物理面，故差商为零。 |
| 8 | `kuhnVertexIndex_succ_eq_axis` | `Spatial/CartesianLatticeDifferences.lean:44` | PASS；实际 Kuhn 前缀索引从 k 到 k+1 精确只增加坐标 πk。 |
| 9 | `cartesianKuhnCellDifference_eq_axis` | `Spatial/CartesianLatticeDifferences.lean:56` | PASS；原单元相邻物理顶点差商严格等于该前缀起点上的同一坐标前向差商。 |
| 10 | `cartesianKuhn_step_sum` | `Spatial/CartesianKuhnEdgeAssembly.lean:15` | PASS；固定 π、k 的前缀只移动横向坐标，全部平移面零值内部供应，得到完整有限格网边和身份。 |
| 11 | `cartesianKuhn_permutation_step_sum` | `Spatial/CartesianKuhnEdgeAssembly.lean:42` | PASS；真实有限和交换及 π 等价重排使完整边和与 π 无关，f/g 保持独立。 |
| 12 | `cartesianKuhnReconstruction_weakGradientPairing_edges` | `Spatial/CartesianKuhnEdgeAssembly.lean:56` | PASS；真实单元体积平移不变、所有排列体积之和为 ∏δ_j，给精确原弱梯度配对边和。 |
| 13 | `cartesianKuhnReconstruction_scalarForm_edges` | `Spatial/CartesianKuhnEdgeAssembly.lean:69` | PASS；原真实 H¹₀ 重构成员和值身份把同一边和精确识别为原 Dirichlet scalarForm。 |

## 原文映射和实际状态

原 Section 6 固定正维数、正 Cartesian 网格步长、全部内部节点状态及物理零边界；同方向 Kuhn 三角剖分使每个单元坐标导数等于相邻前缀顶点差商。原稿通过坐标边关联数和单元体积计算出每条非零坐标边的总系数 ω=∏δ_j，再通过标准 Laplacian 的分部求和得到最终刚度身份。

本批准确完成其中从真实单元梯度配对到坐标边和的步骤。采用等价的有限和路线：对每个固定排列，消去横向前缀平移后边和与排列无关，再乘实际所有排列单元的总体积。没有将“每边 d! 次”或“每个排列体积 ω/d!”当作新增假设，也没有为了回绕而将物理零边界改成周期边界。原标准 Laplacian 尚未在本批出现，因此不能将本辅助身份宣称为已完成 `(A_hf,g)_(X_h)=a(R_hf,R_hg)` 或完整 FD/P012。

实际 `CartesianInteriorIndex N` 是每轴 `Fin(N_j−1)`，物理整数坐标为索引加一，因而对应全部原内部节点 1 至 N_j−1。f、g 是这整个有限空间中任意两组独立实数数据。`cartesianInteriorData` 是按真实物理节点求和定义的零延拓：正步长保证物理节点映射单射，节点上准确返回原 f 值，其他点为零。新 `cartesianLatticeData` 只是把这个同一对象拉回真实物理格点 `o_j+z_jδ_j`，没有另造一组周期数据，也没有限制状态支持、均值、频率或特殊子空间。

已直接读取原节点单射、节点数据值、`cartesianInteriorData_zero_compl` 的证明。若 z_j=0 或 N_j，物理坐标等于原开盒端点，严格域内条件失败，因此数据为零；这个结论对其他坐标任意取值成立。对 r 方向差分和 j≠r，后继点的第 j 坐标不变，两个端点都在同一零边界面，故 D_rf(z)=0。轴向端点的差分并未被错误设为零：z_r=0 的边与 z_r=N_r−1 的边连接内部节点和物理边界，通常有非零贡献，最终求和保留它们。

## 真实有限旋转与边界消去

一般平移引理的辅助假设是：对每个被移动坐标 j∈J，F 在整个整数超平面 z_j=0 或 N_j 上为零。该假设是明示的泛化接口，最终调用中已由真实横向边界差商清偿，没有遗留为最终刚度命题的额外前提。

证明把每个 j∈J 上的实际 `finRotate(N_j)` 与其他坐标上的恒等等价组合为整个有限乘积索引的等价 e。对任意 z 分两种情况：

- 若某个被移动坐标为末点，则直接平移点该坐标为 N_j，而旋转点为 0。虽然其他坐标未必相同，但 hF 对任意其余坐标成立，所以两项均严格为零。
- 若无被移动坐标为末点，则每个被移动坐标满足 z_j+1<N_j。实际 finRotate 值公式给普通整数加一，其余坐标不变，故两个完整整数向量严格相同。

因此两个有限和逐项相等，再通过 e 的真实有限等价重排回原和。这里没有忽略回绕项，没有把边界项近似为零，也没有用未经证明的无限和换元。J 为空时等价就是恒等；出现 N_j=0 时相应正维乘积索引为空，证明和结论仍合法；`Fin 0` 的无元素分支在旋转值引理中被明确消去。

## Kuhn 前缀只沿横向移动

已直接读取实际 Kuhn 整数顶点定义 `z_j + 1_{(π⁻¹j)<k}` 及其与真实物理单纯形顶点的等式。第 8 项逐坐标证明 k+1 与 k 前缀之差：j=πk 时恰增加 1；j≠πk 时，逆排列坐标与 k 不等，严格次序 `(π⁻¹j)<k+1` 与 `(π⁻¹j)<k` 等价，因此其他坐标不变。方向是后顶点减前顶点，与原连续导数公式一致。

第 9 项将上述真实顶点身份代入原 T098 `cartesianKuhnCellDifference`，分子和分母均准确对应，得到同一 D_(πk)f 在 k 前缀起点的差商。没有取任意 L² 类的节点值；所评价的是原有限节点数据，连续重构梯度已由真实弱 jet 单独证明。

固定 π、k 后，取 J 为所有 `(π⁻¹j)<k` 的坐标。由严格不等式立即得到 πk∉J，所以所有被移动坐标都横向于 r=πk。F(z)=D_rf(z)D_rg(z) 在这些坐标面上为零；证明只需第一个因子为零，未使用 f=g。一般平移引理因此适用于实际全部原数据，清除前缀移位。再交换两个有限和，并用 π 对 k 的等价换元，完整坐标和每个方向恰出现一次。

最终 z 遍历每轴 0 至 N_j−1。对固定方向 r，横向坐标为 0 的项为零；横向 N_j 面上的边同样为零，所以没有遗漏任何非零物理坐标边。剩余横向指标正是 1 至 N_j−1，轴向指标完整保留 0 至 N_r−1。这与原刚度证明所需的内部横向边及两端轴向边界边完全一致，角点和多重横向面也由相同零值逻辑覆盖。

## 真实体积、弱梯度及原 scalarForm

已直接读取 T098 的实际单元刚度展开。原重构的第一阶字段是完整真实弱梯度；其单元公式来自开单元上的完整弱测试和导数唯一性，再经真实单纯形边界零测扩展到闭单元 a.e.。对两组独立状态，真实欧氏配对按 `Sym.oneEquiv` 和 π 精确重排为全部坐标差商乘积和，没有重复坐标或额外维数因子。

弱梯度属于原域 L²，配对由 `L2.integrable_inner` 明确可积。真实有限分割通过 a.e. 唯一单元归属将原域积分分成闭单元积分；闭单元仅在零测物理边界外，限制测度转换已合法证明，不把开域外的闭面当作有额外体积的区域。每个单元实际紧且有限测度，`volume.real` 不利用无穷测度 toReal 的总化行为。

新组装从该原单元式出发。`cartesianKuhnSimplex_volume_translation` 的证明使用真实顶点平移、真实单纯形像集合相等和 Lebesgue 平移保测，故对固定 π，体积与格点 z 无关，可以提出有限格点和。前述边和身份对每个 π 都给同一标量。随后使用 `cartesianKuhnSimplex_sum_permutation_volume`：在真实单个 Cartesian 盒的 Kuhn 分割上积分常数 1，再以实际盒测度乘积公式得到所有排列的总体积恰为 ∏δ_j。该证明已直接读取；没有假设各排列体积相同，也没有引入归一化体积或隐藏阶乘。

因此得到精确双线性身份：原完整弱梯度配对等于 `ω Σ_z Σ_r D_rf(z) D_rg(z)`，其中 ω=∏δ_j。全部 δ_j 严格正，真实差商没有零分母；等式不需要步长可比、h 小、时间参数或允许权前提。

最后直接核对 `GradientPairing`、`DirichletForm`、`DirichletScalarForm` 和真实重构 jet：`boundedDirichletOriginalForm.form` 按定义就是实际梯度 L² 配对，原 scalarForm 通过准确值同构取回此配对，没有额外零阶质量项、Poincaré 倍数或等价范数替代。两个输入是原重构 L² 类和已经证明的原 H¹₀ 成员，传入的两个真实 jet 各有严格 value 等式，清偿 `dirichlet_scalarForm_eq` 的全部要求。H¹₀ 仍是全部紧支光滑测试在实际 H¹ 图拓扑的闭包，而非被改写的节点零空间。

raw 配对版本对所有 d 有效；d=0 时坐标和为空、梯度为零。scalarForm 版本明确要求 0<d，正好覆盖原正维数。原 N_j≥2 的全部网格均包括在内；N_j=1 没有相应内部节点、数据零延拓给正确零贡献，N_j=0 的空单元情形也由原类型处理。无新增数学假设，无数值近似或只对二次型成立的限制。

## 依赖、固定版本与本机证据

已读取 [T098 独立验收报告](T098-local-acceptance.md)，并直接核查本批使用的单元式、体积、零延拓、真实分割及原形式身份。三新模块的 Carleman 导入闭包共 225 模块，222 个旧模块相对 base 全部不变。关键已验收依赖的整个闭包亦逐字节比较：

- `CartesianKuhnCellStiffness`：222 模块，与 T098 SHA `36d8ee7de732f00be2146ad4ef293ccf9c53c53f` 相同。
- `KuhnCellVolume`：153 模块，与 T089 SHA `f2e5416279274e334edf8df2d2e43ce3a4d23c39` 相同。
- `CartesianKuhnReconstructionJet`：183 模块，与 T095 SHA `116908340801d3f1cd9f7e940304807f70bdb1ba` 相同。
- `DirichletScalarForm`：86 模块，与 T070 SHA `c5e99b4f0aa241a24dcf27262fced6bc147a60d8` 相同。

root 明确导入全部三模块。AGENTS、治理及 state 协议已读取；原文、这些协议、Lean/mathlib pin 与两个 CI workflows 相对 base 未变。原文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；Lean pin 为 4.35.0，本机 mathlib 实际 HEAD 为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。固定覆盖表实际为 14 个 PAPER/REVIEWED，总计 26 项；本批 C115 仍是 AUXILIARY。

实际 `/tmp/carleman-kuhn-stiffness-edges-target.log` 为定向 **3403 jobs** 成功；`/tmp/carleman-kuhn-stiffness-edges-full.log` 为全库 **3801 jobs** 成功及 **6213** 声明递归公理审计通过。三个新模块无 sorry、admit、新数学公理或 unsafe 证明。`tools/CheckAxioms.lean` 只添加本批 13 项显式类型、公理打印，原全 Carleman 环境的 `privateToUserName` 和递归 `collectAxioms` 审计程序未改。

全部 13 项实际完整类型均逐名读取并与源码核对，各有恰一条类型和一条公理记录。`cartesianLatticeSuccessor` 不依赖公理，其余 12 项仅依赖 `propext`、`Classical.choice`、`Quot.sound`。全产物 2064 条带公理记录、7 条无公理记录，共 2071 条打印、2067 个不同声明名；扫描没有白名单外公理。末行实际为 `Axiom audit passed for all 6213 Carleman declarations.`，该递归环境计数没有与显式打印数混淆。

## 远端原始证据

已独立查询 [main CI run 39191074485 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39191074485/attempts/1)。同 run 的 `lean-ci-result`（ID `12159694065`）和 `lean-declaration-evidence`（ID `12159604383`）artifact 元数据均未过期，均绑定 main 与固定 SHA。本验收已自行通过 `gh run download 39191074485` 成功下载两份原始 artifact。

实际读取 `/tmp/carleman-kuhn-stiffness-edges-main-ci/result.json`：status 为 PASS，checked_sha 与 source_head_sha 均精确为 `e6f194345f2f7b9822f8d8654a003aee071382a2`；ci_url 指向上述 run/attempt；targets 为 Carleman；finished_at 为 `2026-10-19T02:42:27.014618+00:00`。Linux Lean 4.35.0 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib commit 与固定 pin 相同。

远端 `/tmp/carleman-kuhn-stiffness-edges-main-axioms/axioms.txt` 与固定本机 `/tmp/carleman-kuhn-stiffness-edges-local-axioms.txt` 已独立逐字节比较，**完全相同**：**1,853,413 bytes**，SHA256 **`b936095ebaa2da7ed1ddf5ec87da01c296f168f087d3e87de806b3ccb656962e`**。另逐名重新核对远端 13 项类型、公理记录和末行 6213 审计，均通过。没有使用后续工作树 `.ci/axioms.txt` 或其他 SHA 的产物。

已再次独立查询真实 run 和 jobs：event 为 push、branch 为 main、head SHA 精确匹配固定版本、attempt 为 1；run 最终为 `completed/success`，updated_at 为 `2026-10-19T02:43:42Z`。三个 jobs 及其实际步骤均最终成功：

| Job | ID | 最终状态与完成时间 |
|---|---|---|
| `state-check` | `117863797003` | `completed/success`，2026-10-19T02:40:43Z |
| `lean` | `117863797207` | `completed/success`，2026-10-19T02:43:30Z |
| `dashboard / snapshot` | `117864503458` | `completed/success`，2026-10-19T02:43:42Z |

## 验收决定

**C115：PASS，可记录为 REVIEWED，scope 保持 AUXILIARY。** 固定 13 项未发现真实节点数据、物理零延拓、循环回绕消去、横向前缀重排、独立 f/g、真实单元体积、弱梯度或原 Dirichlet scalarForm 方面需要修复的缺陷。同 SHA 三项 CI 及自行下载的原始 result、公理证据已全部核实。

本批仅完成原弱刚度的精确坐标边组装。原标准 Laplacian 的分部求和、最终完整刚度身份及完整 FD/P012 不随本报告提升；原文保持 **14/26**。本 Agent 仅写本报告，未修改实现、台账、原稿、root，未 commit/push。
