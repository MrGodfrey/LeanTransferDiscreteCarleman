# T207 — 实际有限元状态的完整 Dirichlet 时间能量界

固定基线 `7b47cb8efa47015a5e2e62f6e2573204bd5c7418`。原文 `paper/main.tex:2366–2385`，控制收敛证明的状态能量紧性步骤。两模块六项声明，AUXILIARY；17/26 与 P021 均不提升。

令 S 为正维有界开域、X 为真实 L²(S) 的任意有限维子空间，且 X≤H¹₀(S) 的原值子空间。`dirichletGalerkinState` 使用原 `conformingEnergyLift (boundedDirichletOriginalForm ...)`，把同一 X 元素提升到真正 DirichletEnergyState；不是另加梯度变量或假设重构。其值恰为原 X 元素的 L² 函数；原 consistent-mass Galerkin 刚度配对恰为两真实弱梯度的内积。因此完整 H¹₀ 范数平方等于原 L² 范数平方加原刚度能量。

`conforming_state_node_uniform` 从真实 ForwardEquation 推导每个物理节点的 L² 预算。势为原 L² 乘子经 X 的正交投影，区域控制为实际零延拓后投影，二者的真实算子范数界及刚度非负性都在内部使用；只需要各步势界≤M、dt M≤1/2、原初值和控制费用上界。

`conforming_state_dirichlet_time_uniform` 从同一个方程推导真正分片常数 H¹₀ 值 Bochner 重构的统一预算 `stateTimeEnergyBound T M Y U`。离散能量恒等式给两倍累积刚度能量≤Y²+U²+(1+2M)T B²，B=energyConstant T M (Y+U)。逐节点界给 L² 时间值范数平方≤T B²；真实时间重构内积公式及提升范数恒等式给完整时间能量之和。非负刚度允许用同一较宽但统一的预算。没有另加状态能量界、逆估计、网格尺度或时空耦合。

X 可直接取原 full P1 Dirichlet conforming space，包含所有自由度；本批接口不以盒域、单纯形形状、网格分级或观测不等式为前提。仅借用已有 CartesianStateTimeEnergy 文件中的通用数值预算定义，数学声明没有 Cartesian 网格限制。费用可依赖固定 T/M 与数据预算；未声称 T 独立能量界。

尚未在本批声称 P1 控制族的弱极限方程或整体原文控制收敛结果。下一阶段将该真实状态界接到原 H¹₀ Bochner 弱紧性，并建立实际 Galerkin 六项测试恒等式。
