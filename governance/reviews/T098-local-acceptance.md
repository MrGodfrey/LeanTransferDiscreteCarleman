# T098 / C114 独立本机验收

- `checked_sha`: `36d8ee7de732f00be2146ad4ef293ccf9c53c53f`
- `base_commit`: `a9ca6fccf19cc677a4a60b07f373eb533df9d502`
- `reviewed_at`: `2026-10-19T02:36:46+00:00`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全部节点状态的真实Kuhn重构弱梯度及原Dirichlet形式的精确单元差商展开。坐标边重排、差分分部求和及完整FD刚度终式仍待；原文保持 **14/26**。

独立从固定提交导出两模块，读取全部证明、9项完整展开类型及关键依赖，对照固定 `paper/main.tex` Section 6的刚度证明（TeX 1680–1703）及原R_h和Dirichlet梯度形式定义。执行者规格及CI没有代替数学核对。原B.2已在基线完成PAPER验收；本报告不重新扩张其范围，也不纳入后续工作树坐标边重排草稿。

## 全部9项声明

名称均省略公共前缀 `Carleman.`，位置以 `Carleman/` 为根；顺序与交付JSON及固定C114台账一致。

| # | 声明 | 固定位置 | 独立数学核对 |
|---|---|---|---|
| 1 | `cartesianKuhnNodalDerivative_basis` | `Spatial/KuhnNodalGradient.lean:16` | PASS；真实仿射线性部分作用于实际相邻顶点差，结合HasFDerivAt给原坐标差商。 |
| 2 | `derivativeOneFiber_inner` | `Spatial/KuhnNodalGradient.lean:33` | PASS；实际Euclidean内积经Sym.oneEquiv精确化为全部坐标导数乘积之和。 |
| 3 | `cartesianKuhnNodalGradient_inner` | `Spatial/KuhnNodalGradient.lean:44` | PASS；按真实排列重排完整坐标和，得到两组独立系数的差商配对。 |
| 4 | `cartesianKuhnNodalGradientLp_inner` | `Spatial/KuhnNodalGradient.lean:55` | PASS；真实Lp梯度代表和L²内积积分给实际体积乘常值差商配对。 |
| 5 | `cartesianKuhnCellDifference` | `Spatial/CartesianKuhnCellStiffness.lean:16` | PASS；原完整内部数据的物理零延拓在实际相邻顶点上的正向差商。 |
| 6 | `cartesianKuhnReconstructionJet_coordinate_on_cell` | `Spatial/CartesianKuhnCellStiffness.lean:21` | PASS；同一真实重构jet的弱梯度坐标在闭单元a.e.等于该实际差商。 |
| 7 | `cartesianKuhnReconstructionJet_cell_energy` | `Spatial/CartesianKuhnCellStiffness.lean:34` | PASS；两原状态的完整弱梯度单元配对等于真实单元体积乘差商乘积和。 |
| 8 | `cartesianKuhnReconstruction_weakGradientPairing_cells` | `Spatial/CartesianKuhnCellStiffness.lean:51` | PASS；真正可积的弱梯度内积经真实有限分割精确求和，无公共面重计。 |
| 9 | `cartesianKuhnReconstruction_scalarForm_cells` | `Spatial/CartesianKuhnCellStiffness.lean:61` | PASS；原H¹₀成员和值身份将同一弱配对精确接入原Dirichlet scalarForm。 |

## 真实fderiv差商与完整梯度内积

实际Kuhn单元是固定前缀参考单纯形经坐标排列、正对角网格缩放和平移所得的真实仿射像。已直接读取其物理顶点公式和相邻顶点差定理：对k∈Fin d，v_(k+1)−v_k=δ_(πk)e_(πk)。这给全部d个实际坐标方向，每个恰出现一次。

对真实节点仿射插值p_c，证明先由仿射映射恒等式得到

\[
p_c^{\rm linear}(v_{k+1}-v_k)=p_c(v_{k+1})-p_c(v_k)=c_{k+1}-c_k.
\]

随后使用实际顶点差和真实线性映射的齐次性，得到δ_(πk)Dp_c(e_(πk))=c_(k+1)−c_k。`affineScalar_hasFDerivAt` 把该连续线性部分识别成实际fderiv；δ_(πk)>0保证除法合法，因此

\[
\partial_{\pi k}p_c(x)=\frac{c_{k+1}-c_k}{\delta_{\pi k}}.
\]

方向是后一顶点减前一顶点，与原文相同。p_c是全空间真实仿射函数，故公式对任意x成立；没有把另行定义的离散梯度赋予连续重构，也没有只在形式系数层面计算。

`derivativeOneFiber` 的实际定义把连续线性导数作用于所有标准正交坐标基，并以 `Sym (Fin d) 1` 标记这些真实分量。第2项展开PiLp欧氏内积并使用 `Sym.oneEquiv` 重排有限和，严格得到Σ_j A(e_j)B(e_j)，没有维数、阶乘或多重指标重复计数因子。第3项再用π重排全部坐标并代入上述真实差商，给两组任意独立系数c、b的双线性恒等式；不是仅验证c=b的能量上界。

## 真正Lp配对与原H¹₀重构

第4项使用的 `simplexNodalGradientLp` 是真实常梯度在真实有限测度单元上的Lp类。已读取其MemLp构造、真实HasFDerivAt及a.e.代表身份。L²内积确为实际积分，两个Lp字段配对真正可积；a.e.替换后被积函数为常值差商和，因此积分是实际Lebesgue体积|K|乘该常数。紧单元测度有限，volume.real没有隐藏无穷体积或总化积分问题。

原状态f、g均量化于完整 `CartesianInteriorIndex N → ℝ`，没有特殊支持、均值、频谱或额外边界条件。`cartesianInteriorData` 将原全部内部节点数据按物理节点单射延拓到全空间，其他物理点取零。第5项在实际单元连续顶点上评价这个真实节点数据；它不会对任意L²代表取点值。

所复用的 `cartesianKuhnReconstructionJet` 和原Lp重构是T095验收的同一对象，相关固定证明再次读取：实际重构等于真实nodalLp，边界节点数据零、公共面匹配和边界贴合供应原H¹₀图闭包成员；从该已经证明的成员中选择真实弱H¹ jet，并保留精确value身份。这里的H¹₀是紧支光滑测试在完整弱H¹图范数中的闭包，没有将其改成L²闭包或缩小为H²状态。

第6、7项使用原重构jet在闭单元上的真实完整梯度身份。该身份来自开单元内部上的全部弱测试和局部弱导数唯一性；单元内部包含于原开凸域，闭边界零测再给整个闭单元上的a.e.身份。因此物理边界单元同样被覆盖，未将只在每单元计算的经典导数未经弱拼接证明就宣称为全局弱导数。

定义D_(K,k)f为实际第k条前缀边上的上述差商，得到精确局部公式

\[
\int_K\langle\nabla R_hf,\nabla R_hg\rangle
=|K|\sum_{k=0}^{d-1}D_{K,k}f\,D_{K,k}g.
\]

两状态弱梯度都是真实原域L²字段。单元限制测度≤原域限制测度，所以其局部乘积也真正可积；没有通过总化积分的不可积零值得到该公式。

## 原域组装与原scalarForm的精确身份

第8项先展开真实 `weakGradientPairing`：它按定义就是两个jet第一阶字段的实际L²内积，故被积内积由 `L2.integrable_inner` 明确可积。原 `integral_eq_sum_cells` 使用实际Kuhn分割的a.e.唯一归属和有限指示函数积分，得到原域积分等于全部闭单元积分之和。该依赖的证明已直接读取；闭单元限制测度的转换来自开凸域内点包含和真实零测边界，未把闭单元错误视为包含在开域内，也无共享面重复计数。

第9项调用的 `dirichlet_scalarForm_eq`、原 `OriginalForm.scalarForm`、`boundedDirichletOriginalForm` 和 `dirichletJetEnergy` 均已读取。原form是实际弱梯度的L²配对；scalarForm通过精确value线性同构将它放在原H¹₀标量域上。选择的能量代表由弱jet的value单射性识别，`scalarForm_value` 精确还原同一梯度形式，未加入零阶质量项、Poincaré系数或其他等价能量。

新定理供应的两个scalarForm输入正是原 `cartesianKuhnReconstructionLp` 及其真实Dirichlet成员证明；同一jet的value等式清偿接口。因此最终结论是原文形式的精确单元展开

\[
a(R_hf,R_hg)=\sum_{K\in\mathcal T_h}|K|\sum_{k=0}^{d-1}D_{K,k}f\,D_{K,k}g.
\]

raw弱梯度版本允许任意d，d=0时完整坐标和为空、梯度为零，身份一致。scalarForm版本保留原正维数0<d前提，正是原文d≥1的范围。所有正轴步长、平移、有限网格N以及全部f、g均保留；精确身份不要求网格可比、h小、权比较或时间参数。

本批始终保留真实|K|，没有假定每个排列单元体积为∏δ/d!，也没有使用尚未证明的全局坐标边关联数。原边界坐标边贡献、各边总质量、有限差分分部求和及最终(A_hf,g)_(X_h)=a(R_hf,R_hg)仍须后续证明；本批不能据此宣称缺陷η_A已全部清偿或完整FD/P012完成。已验收B.2及原文14/26状态保持。

## 固定依赖、构建与公理证据

两模块Carleman导入闭包共222模块，220旧模块与base完全不变，新增恰为本批两模块。关键已验收版本亦已逐模块比较：C111 CartesianKuhnReconstructionJet的183模块闭包相对 `116908340801d3f1cd9f7e940304807f70bdb1ba` 不变；C086 DirichletScalarForm的86模块闭包相对 `c5e99b4f0aa241a24dcf27262fced6bc147a60d8` 不变；C065 SimplicialIntegrals的85模块闭包相对 `99694c20834ac8d3b712f5e2d071a4e4ccfc308b` 不变。关键数学依赖已直接读取。

本批相对base未改变原稿、已读治理协议、工具链pin或CI工作流；此前P026映射更新已属基线。原稿SHA256为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean为4.35.0，本机mathlib实际HEAD为 `56a005855ea17e0b0958f73ec801ae140b0a1679` 且工作树干净。root显式导入两模块，`tools/CheckAxioms.lean` 包含9项完整类型和公理输出，并通过privateToUserName遍历全部Carleman声明、递归collectAxioms。

9项完整展开类型已逐项核对。固定本机2058条显式公理记录中2052非空、6无公理，均无 `propext`、`Classical.choice`、`Quot.sound` 之外的公理或sorryAx。实际定向日志为3400 jobs；`/tmp/carleman-kuhn-stiffness-cells-full.log` 包含 `Build completed successfully (3798 jobs).` 和 `Axiom audit passed for all 6198 Carleman declarations.`。固定本机 `/tmp/carleman-kuhn-stiffness-cells-local-axioms.txt` 为 **1,847,608 bytes**，SHA256 **`b414f1573fbb4971ec929b68e89588a5863ce4fcae17d4075eee1b6bcd932cda`**。

已独立通过GitHub connector读取 [main CI 39190404769 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39190404769/attempts/1)：main/push、head SHA精确匹配固定版本，run为completed/success。lean（117861730518）、state-check（117861730250）、dashboard / snapshot（117862467337）三项jobs全部completed/success，其实际步骤均success。同run的lean-ci-result（12159393814）和lean-declaration-evidence（12159862366）artifact元数据均绑定固定SHA。

本验收Agent已自行通过 `gh run download 39190404769` 下载同run的两份原始artifact。实际读取 `/tmp/carleman-kuhn-stiffness-cells-main-ci/result.json`：status PASS，`checked_sha=source_head_sha=36d8ee7de732f00be2146ad4ef293ccf9c53c53f`，targets为Carleman，`finished_at=2026-10-19T02:33:58.494252+00:00`，ci_url精确对应上述run/attempt。实际Lean 4.35.0提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

原始远端 `/tmp/carleman-kuhn-stiffness-cells-main-axioms/axioms.txt` 与固定本机副本已独立逐字节比较，完全相同：**1,847,608 bytes**，SHA256 **`b414f1573fbb4971ec929b68e89588a5863ce4fcae17d4075eee1b6bcd932cda`**。另逐名核对远端9/9完整展开类型及公理，2058条显式记录均无非基础公理、无sorryAx；实际末行为 **`Axiom audit passed for all 6198 Carleman declarations.`**。未混用其他SHA或后续工作区产物。

## 验收决定

**C114：PASS，可升级为REVIEWED，scope保持AUXILIARY。** 固定9项未发现真实导数、差商符号、完整梯度、原H¹₀重构、可积性、单元体积、原域分割或原scalarForm方面需要修复的缺陷；同SHA正式三项CI及自行下载的原始公理证据已独立核实。坐标边重排、差分分部求和及完整FD刚度终式仍待，FD/P012不由本批提升，原文保持 **14/26**。

本次仅写本报告，没有修改数学实现、台账、原稿或root导入，没有commit/push。
