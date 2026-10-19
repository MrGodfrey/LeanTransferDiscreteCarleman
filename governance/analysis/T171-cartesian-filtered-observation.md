# T171 / C187：原终端滤波条件与完整 Cartesian 物理观测

两模块三声明。filter_condition_budget 从原 TΛ≤θdS 与 D+log(4C0)/2≤(1−θ)dS 直接证明 4C0 exp(-2dS) K²≤1，其中 K 是原 exp(TΛ+MT+M²T²/2)，C0≥1。真实指数和对数运算给预算，没有替换原滤波条件。

filtered_observation_of_relaxed 在原真实物理时间方程下调用已证 filter_reverse；真实 Rayleigh 上确界属于给定终端子空间 F，仅要求 pN∈F，完全不要求 A 或任意时间势保持 F。反向范数平方界代入实际松弛观测余项，预算给≤四分之一初始平方范数，吸收得到原 2C0 成本。该通用中间声明明确保留实际松弛观测前提。

box_cartesian_filtered_observability 内部以 T170 原完整 Cartesian 观测清偿前提，并在 T/M 固定后取 C0=max(1,C)，先于所有网格、节点势、θ、F和轨道选择。完整原物理节点空间、Laplace、势、Hilbert控制伴随及 S=κmin(h^(-4/5),dt^(-2/5)) 不变；原网格两侧条件及两个滤波条件准确保留。结论使用原控制范数并去除全部终态余项。接口事实上对所有满足所列条件的实 θ 成立，故覆盖原 0<θ<1 而不增限制。

这是原滤波观测定理的完整盒 Cartesian 实例，不将通用条件性吸收当作一般几何的结论；仍 AUXILIARY，原文17/26。

定向3992 jobs、根目标4099 jobs通过。Axiom audit passed for all 8099 Carleman declarations. 固定raw2540654 bytes，SHA256 cacb14043c6cb78528a83b3938b32d2327273ed23f495219622b6fa834b78a8e。同SHACI与独立验收另行登记。
