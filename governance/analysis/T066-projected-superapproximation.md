# T066：原完整P1投影测试超逼近

三模块6声明，AUXILIARY，原文12/26保持。完成Section 6 Step3的实际投影组合以及原eq:testsuper，并接入已存在的GalerkinSuperapprox接口；完整prop:p1尚需一般H²逼近等义务。

真实m=1弱Sobolev范数由其平方恒等式得N≤q‖ξe‖+‖ξ∇e‖。真实L²正交投影固定I∈X给Πv−v=Π(v−I)−(v−I)。取T065同一实际节点残差e及I，Πe∈完整V_h⊂H¹₀，因此内部选出真实弱H¹ jet p，其value恰为Πvalue(e)。不假设e本身已证明H¹₀成员资格。

T058的原四允许权投影定理分别实例化ξ和ℓ⁻¹ξ；T050的真实加权逆估计实例化ξ和p。弱范数三角式给N_ξ(p−e)≤‖ξ∇e‖+CI Cp‖ℓ⁻¹ξe‖+(1+Cp)q‖ξe‖。原h q_max≤δ≤1将最后h²q_max²项吸收到h q_max。选择C=(2+Cp+CI Cp)CE，δ沿用原γ<Γ_d的投影阈值。δ/C先于全部网格、尺度、TimeWeight、τ、t、符号和状态；原形状正则、尺度双边比较及邻接分级条件准确保留。

allowed_full_projected_superapproximation产生真实弱H¹ jet，其值准确等于Π_h(σ²u)−σ²u，且原N范数≤C h q_max N_sigma(u)。输入覆盖完整原V_h，无自由节点表示或空间超逼近前提。通过真实弱梯度唯一性，该jet与任何相同L²值的弱H¹表示一致，不可任意选择有利梯度。

full_p1_galerkin_superapproximation把该结论转入原GalerkinSuperapprox：测试算子确为已有F*F=Π_h(σ²z)，并使用原canonical domainSobolevJet的相同弱导数。此接口按其原定义对权保持hw作蕴含；hw使误差可作为V元素书写，而前一实际投影jet定理不需要这个前提。本批不声称已经证明对所有H¹₀状态的A2保持性。空间C对所有τ和η=±1同时统一，时间区间/周期未进入常数。

一般H²状态的N3逼近、连续Dirichlet算子H²正则性、具体A2/A3及连续Carleman等义务仍按原台账继续。原eq:testsuper只是prop:p1的一项义务，不能据此升级整个具名命题。
