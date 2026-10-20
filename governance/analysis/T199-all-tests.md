# T199 — 原有限弱方程扩展到全部 H¹₀ 测试

基线 `714954acb8b017b09da56c71d4bd91b7d0ccffe2`，原稿 `paper/main.tex:2395–2421`，`eq:conv-limit-identity` 到 `9.26-eq16` 的空间测试扩展。本批 3 模块 5 声明，AUXILIARY，17/26。

`exists_refining_time_grids` 实际构造 N=n+1、dt=T/(n+1) 的辅助时间网格。它只用于识别两个固定测试表示，没有替换原控制网格或给原 h/dt 增加关系。

`finiteTensorTestMultiplier_eq_product` 对任意有限项原 C¹ 时间函数和光滑空间测试，证明 J(Σ η⊗ψ) 等于原有限产品测试乘子的实际 L² 类。沿辅助时间网格，一边用真实 Bochner 张量强收敛及 J 连续性，另一边用原产品测试的时间一致误差、有限测度 L∞→L² 和极限唯一性。J 是之前构造的真实等距嵌入；没有假设其满射，也没有假设待证产品恒等式。

`exists_dirichlet_test_sequence` 对任意开 S 的真实 DirichletEnergyState，使用其真实 Sobolev jet 在原光滑测试 span 闭包中的定义、每个 span 元素仍为一个真实光滑测试，以及实际 jet 连续线性等价，将闭包序列还原成 H¹₀ 能量范数收敛的原测试序列。没有输入稠密性前提或改用 L² 范数。

`FiniteDirichletControlIdentity.spatial_test` 从原全部有限恒等式取一项，结合上述产品身份得到原单张量弱恒等式。`all_energy_tests` 再利用实际值映射、真实弱梯度映射、张量映射和 J 的连续性，把该恒等式沿能量稠密序列推广到任意 w∈H¹₀。Y、U、原 b 和 y0 均保持不变；势项是原 b.map(J Yv) 与 J(η⊗w) 的实际产品 L² 配对。η 在两个端点都不受限，保留原 η(0)y0 初值项以及终端项消失后的原形式。T>0、S 开且测度有限是明确的当前接口前提，原有界盒自动满足。

本批没有把这个恒等式冒充完整连续零控制定理。实际 V′ 时间导数、H 连续时间迹及 y(0)=y0/y(T)=0 仍待；一般多面体/P1 控制极限分支也仍待。原稿未修改。

实现中采用固定维度/区域的稠密性命题和显式 Hilbert 类型，使 Lean 避免在消去存在量词时展开整个 Sobolev/Lp 实现；未改变任何数学前提或结论。
