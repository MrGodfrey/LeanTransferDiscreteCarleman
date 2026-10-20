# T200 — 原控制极限的实际对偶时间弱导数

基线 `c8020ad62e0ebb26a1c9144edc50d2ac2458a6d9`；原稿 `paper/main.tex:2403–2415`，`9.26-eq16`。4 模块 15 声明，AUXILIARY，17/26。

记 V 为此前真实 H¹₀ 能量空间，H 为原空间 L²，E:V→H 为实际值映射，G 为真实弱梯度。`timeTensor_eq_scalarTensor` 和 `inner_timeTensor_integral` 将已使用张量与真实 Bochner 积分配对相接；`compLpL_adjoint` 通过实际代表元和 L² 积分证明有界算子伴随与逐时间 L² 映射交换。`HasWeakTimeDerivative.map_integral` 使用真实可积性将弱导数积分恒等式通过任意有界线性映射传到 Banach 空间。

`dirichletTimeMass` 实际构造 M=E*E。`dirichletTimeLoad` 在 Bochner 空间中实际构造 D=E_t*U−G_t*(G_tY)−E_t*J*(b.map(J(E_tY)))，其中下标 t 表示 compLpL，J 是已构造的真实 Bochner→产品 L² 等距映射。所有伴随都有真实完备 Hilbert 空间实例；D 的类型就是 L²(0,T;V)，没有输入待证导数或右端存在性。`dirichletTimeMass_pairing` 以实际代表元证明质量配对，`dirichletTimeLoad_pairing` 对任意 w∈V、任意标量时间 L² 类证明 D 的配对精确等于原控制、真实梯度和原产品势的三个配对。

`mass_test_identity` 将 T199 原全 V 恒等式写成 −⟨MY,η′⊗w⟩=⟨y0,η(0)Ew⟩+⟨D,η⊗w⟩。`mass_weak_time_derivative` 取内部 C∞ 时间测试，原支撑给 η(0)=0；由任意 w 的积分配对和 Hilbert 分离性得到真正 V 值分布关系 ∂t(MY)=D。Ioo 与 Ioc 时间测度用 Lebesgue 端点零测的实际等式连接。时间网格 g 只为接入旧 HasWeakTimeDerivative 接口，最终对偶定理内部取一个辅助一步网格，结论只涉及原 T。

`dirichletPivotDual` 是真实 StrongDual ℝ V 值的 pivot 嵌入，`dirichletPivotDual_apply` 证明 (pivot v)(w)=(Ev,Ew)_H。`dirichletDualTimeLoad` 将 D 经实际 Riesz 映射 innerSL 送到 L²(0,T;StrongDual ℝ V)。`dirichletDualTimeLoad_pairing` 对任意时间 L² 标量测试和任意 w，证明其积分作用精确是原 U−Ay−by 的弱作用；势项直接使用原 b.map(J(E_tY)) 与 J(η⊗Ew)，没有换成任意势或假设 J 满射。

最终 `FiniteDirichletControlIdentity.dual_weak_time_derivative` 对任意原内部光滑时间测试，证明实际 StrongDual Bochner 积分等式 ∫η′ pivot(Y)=−∫η dirichletDualTimeLoad。因此原 Y 的时间导数确在 L²(0,T;V′)，并由上一配对定理识别为原控制减梯度形式和原有界势的分布右端；同一 Y、U、b、y0 保持不变。原开有界盒自动满足当前 S 开、测度有限和 T>0 的明确接口条件。

本批没有证明 Y 的 H 连续代表元或 y(0)=y0/y(T)=0，也没有把 MY 的 V 弱 H¹ 正则性直接当成 Y 的 H 时间迹。Lions–Magenes 型连续性和端点仍待；一般多面体/P1 极限分支仍待。原稿未修改。
