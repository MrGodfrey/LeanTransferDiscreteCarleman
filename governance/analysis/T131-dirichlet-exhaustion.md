# T131：真实内域解、统一 H¹ 界及 Dirichlet 穷竭极限

本阶段把已经验收的抽象逼近极限用于实际内域 Dirichlet 解。给定递增开域穷竭、每个内域的真实 H² 解及统一 Hessian 界后，原区域的 H¹₀ 逼近族、统一 H¹ 界、逐测试最终 Poisson 与二阶分部积分身份都由代码内部构造，最终得到同一右端项的真实 H²∩H¹₀ 解。

`SubdomainZeroExtension` 对真实标量或向量 L² 类定义先全空间零延拓、再限制到目标 S 的操作；当 T⊆S 时，限制回 T 严格恢复原类，范数严格相等，与实际子域限制满足精确内积恒等式。测度运算实际使用 indicator、限制测度交集和 a.e. 类，未使用形式上的域替换。

`DirichletExtensionPairing` 给原 H¹₀ 延拓的各阶字段等式、精确范数与梯度配对身份。同一紧支光滑函数从 T 视为 S 的测试，限制回 T 严格恢复原 jet；由内域的真实 Poisson 弱身份得到原区域针对该测试的同一右端项配对，绝不声称方程对所有 S 测试立即成立。

`DirichletExtensionHessianTest` 对每个实际 H² 内域状态，将二阶导数分量单独零延拓。测试支持仍在 T 时，原 H¹ 零延拓的梯度与测试导数的配对，严格等于负的延拓 Hessian 分量与测试的配对。由内域真实弱导数链得此结论；没有 H² 零延拓、边界通量消失或全域二阶弱身份假设。

`DirichletWeakSolve` 从真实 coercive Dirichlet form 的零移位 resolvent 内部构造任意有界开域的 H¹₀ 弱解。以解自身作为原 H¹₀ 变分测试，再用原 slab Poincare 与 Cauchy–Schwarz，证明 ‖∇u‖≤2R‖f‖ 和一阶能量≤(((2R)²+2R)‖f‖)²。`DirichletSubdomainSolve` 用外域同一 slab 界和限制载荷范数不增，得到所有内域解在 S 上的统一 H¹ 界；常数在任意内域 T 之前选定。

`SpatialTest.eventually_support_subset` 由真实紧性和递增开覆盖，证明每个原测试的紧支持最终位于内域。阈值可依赖测试。`exists_dirichlet_H2_of_exhaustion` 直接构造 H¹₀ 延拓族及单独 Hessian 延拓字段，供应已经验收的 H² 逼近极限定理的全部逐测试条件。输出实际 H² jet，其 value 在原 H¹₀，negativeLaplacian 等于同一 f，Hessian 平方≤card(Sym(Fin d),2)C²。

数学范围为 AUXILIARY，P023 不提升，14/26 不变。H¹ 弱解存在性和统一 H¹ 界已经内部证明；光滑内域解的 H² 正则性、统一 Hessian 界与符合光滑几何要求的凸域穷竭构造仍是明确未完成的分析义务。本阶段的穷竭极限保留真实 H² 内域解及二阶界输入，不把它们隐藏为已完成结论。

七模块21声明，定向3285 jobs、全库3919 jobs通过；6934声明递归公理审计PASS。固定 `/tmp/carleman-t131-exhaustion-local-axioms.txt` 为2120125 bytes，SHA256 `dcd04a59278984515610a0139ce55b7ee5779b1bf115cc06e96d502f3d18abb1`。
