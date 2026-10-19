# T128：混合弱导数交换、原对称 Hessian 与 H² 极限

这是原附录凸域正则性证明所需的实际 H² 组装和极限工具，仍为 AUXILIARY。继 T127 从有界测试泛函构造单个实际 L² 弱导数，本批将所有二阶分布导数组装为原 WeakSobolevJet d 2，并保留同一原 H¹ jet。

`SpatialTestDerivative` 直接对全部紧支 C∞ 测试作方向微分；真实支持包含保证它仍是同一域的合法测试。实际 toLp 等于原 derivativeLp；C²经典导数的对称性给两次测试方向微分在 L² 中相等。`WeakMixedDerivative.mixed_commute` 对原状态的两个完整弱导数链，将以上真实测试代入四个分部积分身份，通过测试密度证明两个混合 L² 弱导数相等。状态无需经典光滑性。

`DerivativeFieldAssembly` 在任意阶原 DerivativeFiber 中作实际有限坐标注入和求和。每个 derivativeComponent 精确恢复给定 L² 类，完整字段的范数平方恰为每个无序多重指标分量平方和。没有重复计算交换后的混合指标，也没有用任意候选场替代原弱导数字段。

`SecondOrderJetAssembly` 将原 H¹ jet 与满足每个真实坐标弱导数身份的二阶字段装配为 H² jet；其一阶截断严格等于原 jet，二阶字段严格等于输入字段。`exists_weakH2_of_gradient_test_bounds` 不把二阶字段及身份作为前提：对原每个梯度分量的测试泛函界 C，内部调用 T127 构造 D_ij，证明 D_ij=D_ji，经 Sym2 与 Sym(_,2) 的真实等价存入同一个无序指标字段，得到原 H² jet。定量结论为 ‖field₂U‖²≤card(Sym(Fin d),2) C²，常数是明确的维数因子，C允许0，任意开域和维数均覆盖。

`WeakH2BoundedLimit` 的一般版本只要求每个 i/j/测试上的配对收敛、最终成立的分部积分身份和候选 Hessian 分量最终≤C；不预设候选场弱收敛、对称性或它们是全域弱导数。极限的对称性由真实弱导数链内部证明，因此适用于将内域 Hessian 逐分量延拓后的场，未断言 H² 零延拓。强 H¹ 收敛的真实 H² 序列及统一完整 Hessian 范数界是直接推论，所有二阶字段仍属于同一个极限原 H¹ 状态。

六模块16声明，定向3197 jobs、全库3900 jobs通过，6880声明递归公理审计PASS。固定 `/tmp/carleman-h2-bounded-local-axioms.txt` 为2096243 bytes，SHA256 `0d2734ed7fd8407595f8b3b0bc43ba3a0b4d88ccbdad2d072d51a658fbd882ef`。原稿未改。

P023不提升，原文14/26。实际 Dirichlet 解的 Hessian 先验界、光滑内域解正则性和凸域穷竭仍需清偿；本批没有将这些义务藏入最终论文结论。
