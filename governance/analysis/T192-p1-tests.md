# T192 — 完整 P1 节点测试的 H¹₀ 强一致性

数学基线为已独立验收的 T191：`ec7ddbfba0b338f3ba97039442ed5c2108ac99aa`。原稿 `sec:control-consistency`（`paper/main.tex:2926–2956`）对原有限张量测试使用完整 P1 节点插值 I_h，要求空间和时间同时细化时的强一致性。本批清偿 T191 中对这个实际空间插值的强收敛输入。

`nodal_lipschitz_derivative_error` 对真实单纯形节点插值给出点态导数误差 `(1+4κ)L·maxDiameter`。κ 是在整个网格序列之前固定的形状常数；每个实际单纯形有正半径内球，实际胞元直径不超过 κ 倍内球半径。证明使用真实 Taylor 余项和仿射插值导数，不输入梯度误差或一致性。随后通过实际导数 Lp 代表、几乎处处避开网格骨架以及真实分片导数，得到 L² 算子值导数误差；有限体积因子准确保留。

原 `SpatialTest` 的光滑性和紧支撑在内部供应函数与真实 fderiv 的全局 Lipschitz 常数。它们只依赖固定测试函数，与网格无关。因此当实际最大直径趋于零时，节点插值的值与真实导数同时强收敛。这里对光滑测试证明一致性，没有给原初值或控制添加正则性条件，也不需要网格嵌套或 grading。

`testDirichletState` 是实际节点 Sobolev jet 在原 H¹₀ 能量载体中的元素。原测试在边界顶点为零，由紧支撑在开集内证明；真实 conforming 网格的 FaceMatching、BoundaryFitted 和凸域条件供应 H¹₀ 成员资格。值严格为 `M.nodalLp φ.value`，弱梯度严格为实际节点导数字段经 `derivativeOneFiber` 的原映射。已有 `nodalLp_mem_dirichletConformingSpace` 同时确保这是完整 P1 空间的元素。原测试的 `dirichletState` 则取实际紧支撑光滑 Sobolev jet，不是任意同构选出的状态。

`dirichletEnergyState_tendsto_of_fields` 用原能量范数平方等于值与梯度范数平方之和，把两个真实强极限合并为 H¹₀ 强极限。`full_p1_test_H1_strong_convergence` 在内部供应两个极限和梯度映射的连续性，最终输入只有实际网格的统一形状正则性、最大直径趋零和原紧支撑光滑测试。

`testDirichletState_finite_value` 精确识别有限个节点测试的线性组合为整个原有限和的节点插值。`full_p1_finite_time_test_consistency` 再连接 T191，直接证明同一个实际 I_h 的前一时间层重构及整个有限和差商在真正 H¹₀ 值 Bochner 空间中强收敛。时间测试仅需闭区间 C¹、区间内的真实导数关系；没有区间外延拓要求。空间 h 和时间 dt 独立趋零，没有 h/dt 耦合。固定端点定理使用同一节点插值，包含原 0 和 T。

三个模块、16 项声明。范围保持 AUXILIARY、原文17/26。本批给出一般 conforming、边界拟合、统一形状正则 P1 网格上的原光滑测试一致性；不声称完整 P1 Carleman 实例或整个 P021。差分节点取样与其实际 R_h/E_h 的识别、产品 L∞ 测试误差、势项最终极限、弱方程极限和状态端点仍待继续。
