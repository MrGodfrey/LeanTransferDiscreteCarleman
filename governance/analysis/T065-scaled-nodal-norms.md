# T065：原尺度残差和节点超逼近

五模块7声明，AUXILIARY，原文12/26不变。完成原Section 6 Step 3式9.26-eq10和9.26-eq11的节点残差估计，未完成投影测试算子的eq:testsuper。

原局部尺度下界c h_K≤ℓ_K给ℓ_K⁻²h_K⁴≤c⁻²h²；不要求准均匀、不除以h_K或h。使用真实inverseWeight平方积分恒等式及实际残差a.e.身份，有限单元求和恰为全域积分。局部非负能量与已证明的可积性供应积分不等式；常数不随单元数增长。

allowed_full_nodal_scaled_norms对任意完整V_h状态内部选择同一节点测试I∈V_h和同一真实弱H¹残差e，使value(e)=σ²u−I，三个原允许范数的平方界依次为C h⁴E、C h²E、C h²E，其中E=q⁴‖σu‖²+q²‖σ∇u‖²。新ℓ⁻¹项使用原ℓ_K正值和尺度下界；所有原始空间和形状条件保持。

heat_weightedNorm_sq将项目原m=1弱Sobolev范数准确展开为q²‖σu‖²+‖σ∇u‖²。因此E=q²N_sigma(u)²，并非换成一个未经比较的范数。非负平方根引理不除以状态或残差范数；同一C的平方根给三个实际范数界。

allowed_full_nodal_superapproximation选2√C在全部网格、TimeWeight、τ、t、η、尺度和完整状态之前，给同一I/e：

‖σ⁻¹∇e‖+‖ℓ⁻¹σ⁻¹e‖≤C h q_max N_sigma(u)，
q‖σ⁻¹e‖≤C h² q_max² N_sigma(u)。

q≤q_max只用于非负量的单调放大；h q≤1未强化为新的参数约束。完整V_h的内部节点表示及I的H¹₀资格沿用已验收真实构造。e为真实H¹弱jet；本批不声称e的H¹₀成员资格。投影/逆估计组合、一般H²插值和完整prop:p1仍待。所引用的9.26-eq10/11是证明中间公式，不改变26个具名结果的完成计数。
