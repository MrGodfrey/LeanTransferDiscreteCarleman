# T109：原物理刚度、实际加权范数与统一稳定性

本阶段补齐实际物理 Hilbert 算子的性质，并把原质量、载荷和测试范数估计接入同一数值对象。

`cartesianPhysicalLaplacian` 是原完整节点空间上的真实连续线性算子。节点零延拓的加法/齐次性先证明，再逐值实现原 `(2d+1)` 点 Dirichlet 差分公式。它与 T100 已验收原差分算子逐节点完全相同；原精确刚度恒等式因此成为同一实际 R_h 和原 Dirichlet scalarForm 的内积身份。真实坐标边配对的对称性给算子对称性，进而证明实际 Hilbert adjoint(A_h)=A_h；自身配对为非负坐标边平方和，证明 A_h 非负。所有完整节点状态和零边界项保留。

状态与控制的 `cartesianStateSeminorm`、`cartesianControlSeminorm` 是实际物理权乘法后的范数，通过连续线性映射复合范数得到真实 seminorm。每个权节点非零时它们正定；允许权严格为正，故确为原加权范数。对任意非负 r，均严格满足把权替换为 rσ 后范数乘 r 的原同质性。载荷取 F=X，故使用同一状态范数，I=Id 的状态至载荷界常数为1。原实际平方权测试对全部非零状态的严格正性也由精确节点能量和严格正权证明。

`cartesianReconstruction_norm_sq_bounds` 给真实 RH 与物理状态范数的精确无权界 `(d+2)⁻¹‖f‖²≤‖RH f‖²≤‖f‖²`。`allowed_weight_cartesian_physical_stability` 在固定域/轮廓后、全部网格/周期/权/两符号/状态之前选择同一个正 C，组合原加权重构双向界、同一真实 LoadInterface 的 lift 界，以及同一物理测试配对与加权重构的双向界。只使用已证精确节点能量身份；没有使用网格相关范数等价常数。

三模块19项显式声明，定向3515 jobs、全库3830 jobs通过，6545项递归公理审计通过。固定产物 `/tmp/carleman-fd-physical-numerics-local-axioms.txt` 为1935658 bytes，SHA256 `b02354e8474428f9e08778bd69bb0742d2b7fa7f6b8f6874d049884bdc2a34e4`。

范围 AUXILIARY，原文保持14/26。本阶段提供 N1 的真实自伴/非负、原范数和刚度，N2 的相同载荷范数及稳定性，以及 N4 的严格正性与范数比较；仍不把各项的完整统一装配或 N3 逼近接口视为已完成，完整 FD/P012 不提升。固定提交独立验收另记台账。
