# T134：原弱 Poisson 解的真实内部 H² 正则性

本阶段完成任意开域上原 H¹ 弱 Poisson 解的内部二阶正则性，包含实际截断构造、同一梯度的强极限和同一右端项。未预设原解 H²，未把内部正则性冒充边界正则性。

`InteriorSmoothCutoff` 从开 S 和紧 K⊆S，先选闭增厚仍包含于 S 的正距离缓冲，再使用实际光滑 Urysohn 构造 η。其真实拓扑支持紧且包含于 S，在 K 上严格等于1；不要求调用者提供截断函数。

`CutoffMollifierGradient` 先在 η=1 的开内域 T 上用真实邻域函数相等证明 D(ηU)=DU。固定 η 的紧支持给缩小核最终合法；原一阶弱链识别局部卷积梯度，实际零延拓/限制 a.e. 身份及卷积 L² 强收敛给完整原梯度各分量的强 L² 极限。没有假定二阶字段或全空间跨边界弱链。

`WeakPoissonRestriction` 将 T 的同一紧支测试合法延拓到 S，精确使用弱梯度配对和载荷限制的伴随关系，证明原弱 Poisson 方程限制后仍具有同一 f|T。此处仅测试 jet 的零延拓使用 H¹₀；原解 u 无 H¹₀ 前提，也没有删除内域边界通量。

`InteriorPoissonRegularity` 从 T133 截断常数构造实际紧支平滑 φₙ=η(u⁰*κₙ)。Gₙ 是其真实梯度的限制，Aₙ 是真实二阶导数的限制；所有原测试分部积分身份严格成立，梯度强收敛和最终统一二阶分量界供应 T128 的完整测试界构造。因此恢复同一原 u|T 的真实 H² jet，完整一阶截断严格相等。

最终 `exists_interior_H2_bound` 的前提仅是 S、T 开，closure T 紧且包含于 S。先选 M≥0，再量化全部原 u∈H¹(S)、f∈L²(S) 与原弱 −Δu=f；输出 v∈H²(T)，truncate₁v=u|T，negativeLaplacian v=f|T，且

‖field₂v‖² ≤ card(Sym(Fin d),2)·[M(‖f‖+2∑ᵢ‖Dᵢu‖+‖u‖)]²。

常数依赖固定域对，先于解与载荷，不保留平滑核、收敛、二阶候选或截断资格输入。同一右端项由真实弱方程限制和原全部测试唯一性识别。任意维数；空内域及零维情况无非法正性除法。

四模块6声明，定向3349 jobs、全库3929 jobs通过，6975声明递归公理审计PASS。固定 `/tmp/carleman-t134-interior-local-axioms.txt` 为2140355 bytes，SHA256 `90e74c2d73c431eb5cf9bace13b50934dcdbffa79fdb46a4a728842a0edf44bf`。

AUXILIARY，14/26，P023不提升。全局 Dirichlet 边界正则性、凸域统一 Hessian 界和实际光滑凸穷竭仍待。下一阶段同时推进独立的原文粗网格 P1 Rayleigh 界，使用已经接受的真实逆估计与一致质量刚度身份。
