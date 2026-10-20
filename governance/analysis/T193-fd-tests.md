# T193 — 原差分节点取样及实际重构的测试一致性

固定数学基线为 T192 `560e3aa8d23c22943b51dd7744da8174944b27ef`。原稿 `sec:control-consistency`（`paper/main.tex:2926–2956`）的差分 I_h 是完整内节点上的点值取样，R_h 为实际 Kuhn 重构，E_h 为原对偶胞元上的分片常数重构。本批证明这些原对象对紧支撑光滑测试的一致性，没有以任意逼近替代原取样。

`cartesianNodalSample` 在全部原内节点取函数值，载体为原带物理质量的 `CartesianPhysicalState`；这不是对任意 L² 等价类做点值求值。`cartesianInteriorData_test_vertex` 对每个实际单纯形顶点证明零延拓取样值等于原测试值：在域内用实际格点的完整内点索引表示，域外用紧支撑在开域内给出的零值。因此实际 R_h 的 L² 值严格等于完整节点插值，边界条带没有被忽略。

`cartesianBoxKuhnPartition` 仅沿真实盒端点等式运输同一个网格。FaceMatching、BoundaryFitted、最大直径界和统一正内球均来自原实际 Kuhn 几何。给定在整个序列前固定的 κ>0，原 h/κ≤δ_j≤h 条件内部供应同一个形状常数；最大直径≤(d+1)h。没有额外的插值误差、形状极限或网格嵌套输入。

`cartesianBoxDirichletState_test_eq_nodal` 先证明实际值相等，再使用开域上的真实弱导数唯一性，将原 chosen Kuhn jet 与节点 jet 识别为同一个 H¹₀ 状态。这确保 T192 强一致性直接适用于原差分 R_h，而不仅是某个同值、未核实梯度的对象。`cartesian_test_H1_strong_convergence` 在内部供应全部几何条件和最大直径极限，得到实际 R_h I_h ψ→ψ。

`cartesian_test_cell_L2_strong_convergence` 利用已接受的原 E_h−R_h 误差≤C h‖∇R_h‖。H¹₀ 强收敛使真实梯度范数收敛，h→0 使该乘积趋零；与值强收敛相加，得到实际 E_h I_h ψ→ψ。没有输入统一梯度预算或 E_h 一致性，也没有丢掉边界区域。

`cartesianBoxDirichletLinearMap` 用实际值映射的线性及弱导数唯一性证明原 R_h 在 H¹₀ 中线性；它没有新选取状态。`cartesianNodalSample_finite` 逐点识别整个原有限张量的取样与其有限和。最终两条时空定理直接对原 I_hφ(t_i)、原整个和的物理差商 dt⁻¹(I_hφ(t_{i+1})−I_hφ(t_i)) 给出真实 R_h 的 H¹₀ 值 Bochner 强极限和 E_h 的 L² 值 Bochner 强极限。这里空间因子强收敛全部由上述定理内部供应，时间部分使用 T191 的闭区间 C¹ 接口。固定端点定理是同一原 E_h I_h 的 L² 极限，包含 0 和 T。

三个模块、18 项声明。原网格步长比条件、固定 T、全部内节点和有限张量测试保留；h 和 dt 独立趋零。范围保持 AUXILIARY、17/26。原 E_h 测试的产品 L∞ 误差、最终势项、极限弱方程和连续状态端点仍待，未声称整个 P021。
