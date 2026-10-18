# T050：原允许权族的完整一致P1逆估计

四模块20声明，AUXILIARY。把原具体σ=q^τ exp(±qρ)、实际单元直径及ℓ_K尺度接入已验收的全域逆界，完成原eq:p1-weighted-inverse这一证明步骤；整个prop:p1尚未完成，原文12/26不变。

SpatialComparison 从开凸S推出closure S的UniqueDiffOn，空域单独处理。固定ρ在紧closure S上C1，既有真实Fréchet导数的紧性界及凸域均值定理供应L≥1，使|ρ(x)−ρ(y)|≤L dist(x,y)。没有把σ本身的比较或随q变化的Lipschitz界作为前提。实际允许权的比值精确为exp(η(ρ(x)−ρ(y))q)，q^τ完全消去；|η|=1给两侧指数界。实际scaled profile的η=1和−1分别精确等于ρ与ρ.neg，正性及乘子比较均证明。

SimplicialDiameter 定义每个真实单纯形的Metric.diam和有限NNReal最大值，空网格最大值为零；同单元两点距离≤该直径，直径≤最大值。原尺度正且ℓ_K≤B diam(K)、形状条件diam(K)≤κr_K组合为ℓ_K≤Bκr_K。r_K是真实内球半径，主定理另显式要求ball(a_K,r_K)包含于实际单元；这就是所用形状正则性的几何内容。此逆界不需要原ℓ的下比较或邻接分级，是在原条件下成立的更广情形。

SimplicialAllowedComparison 用真实空间Lipschitz界和实际直径推出单元比较，在maxDiameter*q≤1时常数为exp L。任意单元点均可作归一化点；闭单元中的点按inside进入closure S，没有错误地声称进入开S。另从maxDiameter*qmax≤δ及实际q(t)≤qmax给所有时刻的相同网格条件。

ConformingAllowedInverse 将固定L给出的exp L及Bκ传给T049统一全域逆界。归一化点取实际单元第零顶点，原乘子的实际正值作为s_K；逐点比较转为真正单元受限测度的a.e.比较。最终正常数C在全部索引类型／网格、内球／尺度、TimeWeight、τ、t、η及状态之前；仅依赖固定域／ρ、维数、κ、B。对完整M.conformingSpace V中的任意H1 jet给 ‖σ∇u‖≤C‖ℓ⁻¹σu‖，使用的右乘子正是已证的实际分片逆尺度乘积。V可取H01，不限制为节点像，也没有τ、T、qmax、网格数量或最小尺寸依赖。

本阶段完成具体allowed权与几何尺度对应，不声称完成加权L2投影稳定性、H2节点插值／超逼近、椭圆正则性或连续CE。原邻接权分级及DST投影稳定性仍待独立构造证明。
