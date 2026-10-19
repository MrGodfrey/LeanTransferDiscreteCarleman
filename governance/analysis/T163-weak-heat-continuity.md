# T163 / C179：完整弱周期图上的真实梯度与加权热能量连续性

五模块十八声明。PeriodicEnergyField 将原 resolventEnergy(1) 作用于真实 A 字段与值字段之和，得到完整周期图到实际 L²_t V 的连续线性映射。原时间算子图身份内部证明其嵌入恰是原轨道 L² 值；不是附加能量代表假设。

SmoothWeakGradientIdentity 对任意有界开域上的原弱 H¹ jet 和同值的全局 C∞ 函数，用紧支截断、原弱 jet 值唯一性和真实局部坐标微分身份，识别每个弱一阶字段。实际有限维 Hilbert 范数给全部梯度平方和等于经典 gradient 的平方范数。

DirichletPeriodicGradient 将真实能量字段与原 dirichletGradient 的 Bochner 连续线性映射复合。若同一个光滑 F 代表闭区间上的轨道迹，则对时间 a.e.、空间 a.e.，输出的真实弱梯度平方等于 F 的经典空间梯度平方。只使用实际能量嵌入、pathL2 代表和弱导数唯一性；不把全时间域资格加到原状态上。局部关闭 backward.isDefEq.respectTransparency 是 Lean 旧有嵌套 Hilbert/Lp 类型的展开设置，不改变声明或逻辑公理。

WeightedTimeContinuity 复用已存在的 timeMap 和其真实范数界，包装为 CLM，证明原 timeSq 恰等于指数平移后的实际加权 Bochner 范数平方，因而连续。界可依赖本次 w.max、ρ.bound 等数据；这里只用于固定权的拓扑连续性，不成为原 CE 常数。

DirichletHeatContinuity 定义原 q³ 值项、q 梯度项之和，以及实际 ε∂t+A 残差和真实观察集 cutoff 项之和。四项均沿实际完整周期图连续。box_dirichletHeat_le_of_classical 保留光滑 core 上的 CE 为显式前提，利用已证完整 core 密度及闭不等式集，以完全相同的 ε、权和 C 延拓至全部原弱轨道；不要求 C 正或改变它。这是一条清楚列出平滑估计前提的辅助传递引理，尚未用实际柱积分估计清偿该前提。

仍需将这些 Bochner 加权能量与已有实际 boxTimeIntegral 四项逐一识别，并实例化已证原 C² 时间权双方向光滑 CE。一般凸多面体也仍待。保持 AUXILIARY、P024 不提升、原文覆盖17/26，原稿不改。

定向3523 jobs、根目标4072 jobs通过；7913项递归公理审计通过。固定 raw 2444719 bytes，SHA256 65ab097409a6076273393439769492a7f538cc41933722dc994ea7e30d7dfdf0。同 SHA 正式 CI 与独立验收另行登记。
