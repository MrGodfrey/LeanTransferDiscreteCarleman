# T070：原Dirichlet形式的两条A3加权估计

三模块10声明，AUXILIARY。对原完整H¹₀空间与原Dirichlet scalarForm证明两条A3：|a(u,v)|≤Nσ(u)Nσ⁻¹(v)，以及a(u,σ²u)≥(1/2)Nσ(u)²−C||qσu||²。C先于全部时间权、指数、时刻、符号和状态；没有H²正则、节点或网格条件。原文完整计数仍12/26。

WeakWeightedForm先用实际H¹值的唯一性，将构造的弱乘积公式传递给任意具有准确乘积值的真实jet。两次应用真实一阶弱乘积，使用有界乘子在Lp上的交换性、实际标量配对自伴身份和完整Euclidean坐标平方和，得到
a(u,σ²u)=||σ∇u||²+2Σ_i〈σ D_i u,(D_iσ)u〉。
平方权由连续两次同一允许乘子作用产生，不假定其指数仍属于单次允许族。

逐坐标Cauchy–Schwarz和Young不等式给交叉项下界。若真实一阶乘子满足|D_iσ|≤Bq|σ|，则原平方和N范数给c=1/2和C=1/2+2dB²。上界使用真实互逆乘子在L²内积中的精确抵消及Cauchy–Schwarz；两边梯度范数由实际N范数中的一阶项控制，常数为1。

DirichletScalarForm通过原OriginalForm.valueEquiv和真实H¹₀能量状态，把项目原scalarForm识别为同一弱梯度配对；没有重新定义形式或替换状态空间。DirichletAllowedForm由原SmoothOnClosure和有界开域内部供应真实intrinsicWordMultiplier [i]与统一相对导数界。原H¹₀允许权保持定理供应σu、σ²u的成员资格，再用各自canonical jet的准确值调用底层下界。

最终下界直接对全部原dirichletSubspace状态及实际conformingWeight复合成立，所有权保持资格内部清偿；上界直接使用原σ和取反指数/符号的实际倒数ξ，逐点验证σξ=1。上界事实上对任意η有效；下界保留原|η|=1。结合T067–T069已完成该Dirichlet模型m=1的A2与A3，但A1的H²椭圆正则、一般m及完整Appendix A仍待。
