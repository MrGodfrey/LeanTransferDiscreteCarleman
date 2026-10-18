# T034：插值误差到原投影近似和超逼近

范围 CONDITIONAL，不提升 P011 / Proposition 6.1 或物理观测控制覆盖。原文 `paper/main.tex` Section 6 P1 Step 2–3（约1533–1600行），原稿未改。

本阶段以真实 L2 子空间的正交投影、实际 Sobolev 弱导数和已经构造的 Pi(sigma²z) 为对象。证明 v-Pv=(v-Iv)-P(v-Iv)，由加权投影稳定性得 L2 误差常数 1+Cp；由辅助权 ζ 的投影稳定性与真实能量逆估计得 N(v-Pv)≤N(v-Iv)+CI Cp ‖ζ(v-Iv)‖。两条估计接入原 N3；不把原投影误差当作输入。

对 σ²z 的真实 V 内双乘法重复上述推导，准确识别 P(σ²z)=inclusion(galerkinWeightedTest z)，逆权下的投影误差用 seminorm 对差的对称性翻转符号。原 N4 空间误差常数为 CE+CI Cp Cζ，尺度为 h*qmax。

热 m=1 的梯度定义是唯一弱导数 jet 的一阶 L2 场。原 Nσ≤q‖σv‖+‖σ∇v‖ 由实际 Sobolev 范数证明。逐点 q|σ|≤|ζ| 推出 q‖σv‖≤‖ζv‖；当 ζ=ell⁻¹σ 时这正由 q ell≤1给出（本阶段未构造 ell）。因此梯度逆常数 CI 给完整能量逆常数 1+CI；原梯度插值加辅助 L2 的联合界给能量及辅助误差两条界。

`HeatInterpolationData.approximation` 的常数精确为 aE=(CE+(1+CI)Cp CE)h，a0=(1+Cp)C0 h²。`HeatSuperapproxData.superapprox` 的 Csuper=CS+(1+CI)Cp CS。`heatInterpolationErrors` 取真实 ηA=0，`heatInterpolationErrors_orders` 用 Cap=max(CE+(1+CI)Cp CE,(1+Cp)C0) 同时给两条原误差阶，Cap 不依赖 mesh/q/T/X。

`interpolatedHeatNumericalData` 对完整两符号/全部|τ|≤τStar的局部数据实际构造原 N1–N5；时间测试及 Ctime=2β(τStar+ρ.bound) 内部供应，质量、载荷、观测比较常数1。插值器 I:D→X 和 J:V→X 为实际函数（可以取同一插值器在相应集合上的限制/延拓），此投影推导无需它们线性。没有声称任意 H1 函数已有点值或已存在节点插值器。

仍待的具体内容：P1 网格/ell、分级条件下四个权的投影稳定性、节点插值及局部梯度/辅助L2误差、梯度逆估计和加权双乘法的局部超逼近；连续 Dirichlet 热实现和 A4 也未清偿。这里 ζ/ξ 是显式有界乘子，没有仅凭名称认定其已是 ell⁻¹σ。所有这些输入均显示于结构和最终函数类型中，不能据此声称整个 Proposition 6.1 完成。

独立验收需核对六模块全部25显式声明、真实范数/投影/导数身份、量词与常数、不隐藏网格实例、根导入和同SHA公理审计。
