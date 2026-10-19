# T129：真实 H¹₀ 弱紧性与 Dirichlet H² 逼近极限

本阶段完成 Grisvard 凸域正则性路线的极限组装步骤：由已给定的 H¹₀ 逼近族、统一 H¹ 界、候选 Hessian 的统一 L² 界和逐测试最终身份，构造真实 H²∩H¹₀ 解，并保留原 Poisson 方程。具体逼近族和先验界的构造仍未完成，因此不提升 P023。

`HilbertWeakSubsequence` 使用固定 mathlib 的可分空间弱对偶闭球序列紧性与真实 Riesz 等距同构，从任意有界实 Hilbert 序列内部选择同一严格递增子列及弱极限，保留范数界C。闭线性子空间版本在子空间中提取，通过真实正交投影将测试扩展到全空间，故极限仍在原闭子空间。弱收敛经过真实连续线性映射，用实际 Hilbert 伴随传递。

`DirichletWeakSubsequence` 在真实 SobolevHilbert 平方和范数上应用该工具。Lebesgue 限制测度的可分性、有限维导数字段的第二可数性以及 Hilbert jet 子空间的完备性均由实际实例和旧证明供应。原 H¹₀ 测试闭包经原 toJet 连续线性映射拉回为闭子空间，未用逐点边界零代替原边界条件。输出同一u∈原H¹₀、同一严格递增子列，并对每阶k=0,1和每个真正L²测试字段给弱收敛。原H¹能量界 field₀²+field₁²≤C²被原样保留。

`WeakLaplacianLimit` 由全部原测试证明真实分布负Laplacian的L²右侧唯一；若全梯度弱收敛且Poisson测试身份逐测试最终成立，则同一真实弱方程传到极限，没有假设强H¹收敛。

`exists_dirichlet_H2_of_bounded_approximants` 内部提取H¹₀弱子列，将其全梯度弱收敛经真实坐标连续映射转为T128所需配对极限。每个候选二阶字段的最终界及每个测试的最终身份沿同一严格递增子列传递，T128因此给同一极限u的真实H² jet v。原方程弱身份另行传极限，已有真实H²负Laplacian测试恒等式及右侧唯一性给严格等式negativeLaplacian v=f。v的值属于原H¹₀，完整一阶字段仍保留C₁²能量界，Hessian平方≤card(Sym(Fin d),2)C₂²。

输入候选A_n仅为真实L²类，不要求它们全域为弱Hessian、对称或收敛；原u_n仅H¹₀，不要求H²。因而后续可由光滑内域的解和逐分量延拓字段供应输入，不会把H²零延拓错误地作为前提。最终构造既非预设的解也非任意替身，而是所有原测试下满足同一f的真实Dirichlet H²状态。

四模块7声明，定向3235 jobs、全库3910 jobs通过，6887声明递归公理审计PASS。固定 `/tmp/carleman-dirichlet-limit-local-axioms.txt` 为2102943 bytes，SHA256 `d3b1972e9ec476855a15f14dc1c37859133470d2b1b002fea9757157cfdc1ec4`。

AUXILIARY，14/26；光滑内域解的H²正则性、Miranda–Talenti统一Hessian界及实际凸域穷竭构造仍须证明。原稿未改，没有用本阶段的逼近输入取代原论文最终假设。
