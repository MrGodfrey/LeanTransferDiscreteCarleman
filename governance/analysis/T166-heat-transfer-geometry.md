# T166 / C182：实际弱梯度及盒连续 CE 接入原转移几何

四模块十一项显式声明。HeatGradientExpression 构造真正的有界算子系数微分表达式：零阶系数为零，一阶系数为恒等连续线性映射。实际有限表达式精确等于输入一阶 Lp 字段；唯一热微分族因此等于原 conformingDerivative。对实际 Dirichlet 域状态，后者精确等于原 dirichletDomainJet 的一阶弱字段，未命名任意线性映射替代梯度。

DirichletHeatGeometry 对任意数值空间及其规定范数，证明原 sobolevGeometry 的 continuousEnergy 正好是原轨道 q³ 值项加 q 弱梯度项；实际 domainValue 只需 a.e. 等于原 value。残差为实际 ε∂t+A，观察为实际 cutoff；两者精确等于原 exp(qρ) timeSq，没有额外常数或更换观察区域。区间权的二阶预算、三重端点匹配和下界以 IntervalQClass 原样汇集，并导出已用的 TimeWeightRegularity；没有增加区间外光滑或周期条件。

BoxHeatContinuous 将 T165 原弱 CE 和这三个精确身份合并，清偿原 ScaleUniform/TransferUniform 接口中的整个 continuous 假设。c、λ、β、qc、C 在数值空间、时间网格、TimeWeight、两个 Orientation 及全部原弱状态之前选择；数值范数不进入连续常数。最终不保留 CE、梯度识别、图密度或原轨道代表前提。TimeWeight 是现有数值转移的权载体，任意原区间 q 的版本仍由 T165 提供；本次没有声称所有数值权只靠一阶预算便满足连续 CE。

区域仍为正坐标盒，AUXILIARY，P024 不提升，覆盖17/26。下一阶段将真实盒 A1/允许权族及 Cartesian N1–N5 与该连续结论一起用于完整离散估计；一般凸多面体及其它原文目标继续。

定向3608 jobs、根目标4085 jobs通过；Axiom audit passed for all 8020 Carleman declarations. 固定 raw 2482476 bytes，SHA256 822d024d0e5569897e8ee1d7ee56a1d7208f351fc996da09d7115d11263b9344。同SHA正式CI及独立验收另行登记。
