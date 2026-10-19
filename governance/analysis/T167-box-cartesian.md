# T167 / C183：全 Cartesian 状态的真实盒热差分 Carleman 估计

三模块七项显式声明。CartesianHeatGeometry 使用原 CartesianPhysicalState 的实际对角质量内积、原状态/载荷节点权范数、原控制节点范数以及 T166 的真实弱梯度表达式；权正性内部证明所有数值范数的确定性。固定域上的 reconstruction/load 由真实域相等运输，载荷 Γ 精确保持恒等。CartesianTransportedData 仅正规化这个依赖运输，直接使用已证完整 N1–N5，不改变任何算子、测试族、误差阶或常数。

BoxCartesianHeatEstimate 先对固定正坐标盒和观察区域选择 c、λ、β、qc、连续CE常数；实际 box_analytic_data_uniform 供应原 D(A)⊆H² 的完整域、图范数估计及所有权的 AllowedFamily。真实 cartesian_numericalData_on 供应原 Cartesian Laplacian、Kuhn reconstruction、Γ=id 载荷、原 control extension 的实际 Hilbert adjoint，以及所有允许权的 N1–N5；误差为 aE=Capp*h、a0=Capp*h²、ηA=0。T166 的实际同符号连续估计随后直接供应完整 transfer 所需输入。

原 heat_scale_uniform 给 h^(-4/5)、dt^(-2/5) 的参数范围。最终κ缩小为min(原κ,数值阈值ε)；由 h≤1 和真实实幂预算内部证明h*w.max≤ε，因而最终不保留原数值小量条件。取实际残差作为载荷、Γ=id 给所有离散状态的估计，无频率过滤、无额外 PDE 解条件或逆载荷常数。两个 Orientation 共用同一相位、β、qc、κ、h0、Δ0、C，全部量在数值网格、h、g、w和z之前选择。

最终左侧 nodeEnergy 包含真实对角质量 q³ 状态项及实际 Kuhn 重构的 q 弱梯度项；右侧为原物理范数中真实 s.difference+Cartesian Laplacian 残差和实际 control adjoint 的 q³ 观察项。W 是非空开且包含于盒，closure W⊆ω；其紧性由盒有界内部供应。网格仅要求正各向步长、真实固定盒相等和统一ratio≥1，所有内部节点状态都覆盖。时间权是原 IntervalQClass 的 C²/端点/导数预算，数值载体TimeWeight的max为原上界。

这完成原文 Section6 盒Cartesian实例与 cor:scales 的实际端到端结合。仍为该几何/离散化实例，不提升一般P024或P1/一般解析实现；AUXILIARY，覆盖17/26。接续原物理权、节点势及真实非周期观测/控制后果，并继续其余原文目标。

定向3976 jobs、根目标4088 jobs通过；Axiom audit passed for all 8035 Carleman declarations. 固定raw 2494005 bytes，SHA256 0e239b6fe52e852dbd6c02a769a3cfff3db06740ee934cf8820d76978a21f307。同SHA正式CI和独立验收另行登记。
