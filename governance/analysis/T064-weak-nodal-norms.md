# T064：真实弱残差与原允许乘子范数

六模块9声明，AUXILIARY，原文12/26不变。清偿T063残差梯度仅用实际fderiv积分表述的义务，将全域估计接到真正H¹弱jet及项目原L²乘子。

一般支持集K上有界Lipschitz系数w乘全局有界Lipschitz函数u，若u在K外为零，则wu全局Lipschitz。证明分两点均在K/跨K/均在外三类；跨界仅用u的真实全局Lipschitz性和零值，不要求w在K外光滑或有界。常数B L+P D准确。原σ²在闭域由真实C²与紧性供应Lipschitz/有界数据，零边界节点函数供应全局Lipschitz及有限节点界。因此σ²N(f)及其节点残差是实际紧支撑全局Lipschitz函数。这些成员资格常数允许依赖网格、状态和权；它们不进入T063的统一误差常数。

真实紧支撑Lipschitz弱导数定理及限制到S构造完整H¹ jet，标量值a.e.等于实际残差，弱梯度a.e.等于实际fderiv的Euclidean fiber。这里使用真实Rademacher/积分分部依赖，无拼接未知弱导数或忽略单元边界项。T063全域估计由a.e.身份转为真正弱jet的标量/一阶字段积分。

实际Lp代表恒等式证明e=w.map u−I，其中I为同一实际加权节点测试类。对原SpatialProfile/TimeWeight乘子σ及τ/η翻转所得倒数ξ，平方seminorm准确等于∫σ²|u|²及∫|u|²/σ²；标量和完整Euclidean fiber均在真实内积空间L²接口内。最终allowed_full_nodal_weak_norms选统一C在全部网格、TimeWeight、τ、时刻、η和原状态之前，任意完整V_h状态内部产生I∈原完整H¹₀一致空间及真实弱jet e，满足

value(e)=(σ.mul σ).map(value(u))−I，
||ξ value(e)||²≤C h⁴[(q⁴||σ value(u)||²)+(q²||σ field₁(u)||²)]，
||ξ field₁(e)||²≤C h²[同一能量]。

成员资格构造没有加入域外光滑或节点表示前提；q≥1、hq≤1、内球形状及原完整V_h条件保留。残差已是弱H¹，但未单独登记其H¹₀闭包成员资格。ℓ⁻¹加权残差项、投影/逆估计组合和最终原eq:testsuper尚待；一般H²插值仍待，不升级完整prop:p1。
