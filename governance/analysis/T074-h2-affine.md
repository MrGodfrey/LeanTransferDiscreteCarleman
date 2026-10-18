# T074：原凸域全部弱 H² 状态的齐次仿射逼近

五模块34声明，AUXILIARY。原有界开凸域 S，正体积，D≥0 控制其全部两点距离。对每个真实 `WeakSobolevJet d 2 (volume.restrict S) S` 状态 u，构造实际仿射 p 和实际弱 H¹ 残差 r，使 r 的零阶值 a.e. 等于 u−p，并证明

`||r|| + D ||∇r|| ≤ d (2^d+1) D² ||field₂ u||`。

这里右侧是真实二阶对称导数字段的 L² 范数，不是完整 H² 范数或另定义的“误差能量”。不需要光滑代表、点态可微、全空间弱延拓或零迹。d 任意自然数；d=0 或 D=0 不被除法排除。常数仅依赖 d，先于域、直径、状态和任何网格/权参数。

`BoundedAffineSobolev` 将有界域上的实际仿射函数及其常导数实现为真正 L² 类。仿射 L² 成员资格来自闭包上的连续平方积分；完整弱导数来自实际 Lipschitz 积分分部。常函数、残差平方积分与 L² 范数平方的身份均在 a.e. 代表层面证明。弱导数的减法使用原全部 SpatialTest 身份。

`CoordinateFirstJet` 从已证明的完整弱坐标身份组装真实 H¹ jet。零阶类精确等于给定标量类，完整一阶字段的 L² 范数平方精确等于各坐标 L² 范数平方之和。

`MeanAffinePolynomial` 从给定斜率 A 构造 `p(x)=c+A(x)`，其中 c=((∫u)−(∫A))/volume(S)。`coordinateFunctional` 用原 Euclidean 坐标给出实际连续线性泛函；其对标准基的作用确为指定斜率坐标。实际 L² 残差 a.e. 等于 u−p，且精确积分为零；除法仅用原正体积前提。

`H2MeanGradient` 取原一阶弱导数各坐标的积分均值 g_i。对这些坐标应用 T073 的弱 Poincaré，原二阶 jet 的完整弱身份给出其弱导数。每个 Hessian 坐标范数≤原完整二阶字段范数，两次有限求和给 d² 的宽松维数因子。因此真实梯度残差能量≤P D² d²||field₂u||²，P=2^d/2。没有将对称 Hessian 的混合分量误计成精确双重和；显式 d² 上界已容纳全部坐标。

`ConvexH2AffineApproximation` 取 A=coordinateFunctional g、p=meanAffinePolynomial u A，并用实际原弱导数减实际仿射弱导数构造 r。除零阶 a.e. 身份外，逐坐标证明 r 的梯度是原梯度减 p 的实际导数。再对零均值 r 应用第二次 Poincaré，得到值误差平方≤P²D⁴d²||field₂u||²。由所有范数和 D 非负，平方界分别给值误差≤P d D²||field₂u||、梯度误差≤(P+1)d D||field₂u||，相加给所述维数常数。最后存在量词包装仍是原任意弱 H² 状态及实际仿射/残差对象。

原文 Appendix B `lem:fd-boundary-affine`（B1）的第一步正是此类未校正仿射逼近。其要求的物理面零迹保持尚未完成：仍须真实弱迹估计和有限维面限制核校正。B2 还须实际局部矩重构、网格组合和权估计；P1 的节点 H² 插值也未由本阶段自动得到。因此原完整命题数保持12/26，不提升 B1/B2/P1。
