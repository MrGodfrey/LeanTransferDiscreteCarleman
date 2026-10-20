# T204 — 原控制状态的真实 H 连续时间代表

基线 `d6634423766eaa11b670fb643578e3a62ff1a71e`。原文 `paper/main.tex:2415` 的 y∈C([0,T];H)；2 模块 4 声明。AUXILIARY、17/26，P021 整体仍不提升。

`pivot_path_limit` 对实际闭区间 V 连续、弱 H¹ 近似 u_n，输入其真实状态 L² 类收敛到 Y、质量加权导数 E*E du_n 的真实 L² 类收敛到 D。通过真实弱导数相减，将 T202 迹界应用于 u_n-u_m，给每个时刻

‖E(u_n-u_m)(t)‖² ≤ T⁻¹‖E_t(U_n-U_m)‖²+2‖U_n-U_m‖‖D_n-D_m‖。

逐点估计经实际 ContinuousMap 上确界范数转为 C([0,T];H) 的平方根上界。两个索引在真正乘积 atTop 滤子中同时趋于无穷时，右侧趋零；因此整个路径序列 Cauchy。路径空间的完备性产生真实连续极限 p。实际 pathL2 和 E.compLpL 都连续，且近似的 pathL2 身份由几乎处处代表逐点核对，极限唯一性给 pathL2 p=E_tY。

`exists_pivot_time_representative` 只输入任意完整实 Hilbert V/H、有界单射 E、原 Y,D∈L² 和实际 (E*E Y)'=D。E*E 非负性及稠密值域由真实伴随和单射性内部证明。取明确 ε_n=1/(n+1)，调用 T203 构造实际连续正则化族，再应用路径极限定理，返回 q 在原闭区间 H 连续且 q=EY 几乎处处。未把 MY 的 V 连续性直接视为 Y 的 H 连续性，未要求 E 的有界逆或 E(V)=H，也未假设原 Y 连续。

`FiniteDirichletControlIdentity.continuous_H_representative` 接到同一原 Y、U、b、y0。真实完整 Dirichlet 能量空间的值嵌入 E 单射，原质量导数由 T200 供应，最终返回原时间 [0,T] 的 H 连续 q 和实际 EY 的 a.e. 身份。内部一步 TimeGrid 仅编码正 T；没有引入周期条件、新空间正则性、额外解或替换控制序列。

原稿该句的 H 连续代表部分已证明，两个端点是该连续函数的真实点值；q(0)=y0、q(T)=0 尚须用原不限端点的弱恒等式识别。T⁻¹ 只用于固定 T 的连续代表构造，不是论文控制成本的额外 T 依赖；原控制范数结论保持不动。本批未修改原稿，仍需端点与完整定理组合后才能评估 P021。
