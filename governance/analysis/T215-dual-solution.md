# T215 — 原强对偶方程及唯一能量解

基线 `9662adfb01356f17d6bdb85ea93c7e47046373b0`，三模块、七定理及一个原能量解定义。对应 `paper/main.tex:2338–2415`，AUXILIARY、17/26。

对任意实际注入连续线性映射 L，两个 L² 函数的映像满足分布时间积分方程，则原函数也满足该方程。测试加权函数真实可积，由 L 与 Bochner 积分交换及注入性反推，未假设逆映射有界或满射。

在原 Dirichlet 空间上取真实 Riesz 映射 `innerSL ℝ`，使用其等距注入性。原 pivotDual 就是该映射复合质量算子，原 dualTimeLoad 是同一映射作用于原载荷；两个 a.e. Lp 代表身份与积分交换给出 StrongDual 弱方程和质量弱方程的双向等价。另直接证明原 pivotDual 状态及原载荷均为真实 V′ 值 L² 函数。因此此处的分布身份确实给原 H¹(0,T;V′) 时间正则，而非形式符号。

`DirichletEnergySolution` 只要求原 Y∈L²H¹₀、同一 b/U 的真实 V′ 方程以及 H 连续代表 q 的原初迹 q(0)=y0，定义不限制终态。已有原零控制状态是该一般能量解。两个该定义下的解转为质量弱方程后，T214 给 Y=Z；不假设任何一方为原离散极限或已有零终迹。

`FiniteDirichletControlIdentity.unique_energy_solution` 从真实有限测试身份内部给该能量解，并对任意同数据能量解 Z 证明 Y=Z 及 `DirichletNullControlState`，其中终态零由已构造解的真实连续迹传递。一般多面体解析与 Carleman 实现仍需清偿；此辅助阶段不提升整条 P021。
