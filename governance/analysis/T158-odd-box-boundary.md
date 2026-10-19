# T158 / C174：实际盒奇延拓及保持全部零边界的卷积

本批把T157明确输入的局部奇性真正接到原弱Dirichlet Poisson解上。七模块25声明，AUXILIARY，原文覆盖仍17/26；完整弱轨道的Carleman估计未完成。

EvenLocalMollification 证明全偶核的拓扑支集包含在原核的闭球支集中，复用真实局部弱微分交换，得到任意紧内子集上实际一、二阶导数的L²强收敛；全空间L²状态的受限范数收敛也内部证明。

CoordinateOddPart 定义实际全空间Lp差 u−u∘R，证明其a.e.代表及同面奇性；不同坐标的仿射反射交换，故新坐标奇部分保持旧坐标平面附近的局部奇性。DoubleOddSlab 从原状态在区间(a,b)外为零，证明下端奇延拓支持在(2a−b,b)，继而两次真实反射 (I−R_b)(I−R_a) 后，在 |x_r−a|<b−a 内仍关于a奇，且关于b全局奇。上端反射项在下端局部带内的两个采样点均为零，由实际坐标不等式证明；没有假设双端全局奇性。

OddPoissonExtensionValue 和 BoxPoissonExtensionValue 重用已验收的真实H¹零边界奇延拓及弱Poisson方程，同时保留新域状态的零延拓等于原域零延拓实际奇部分的精确Lp等式。该等式依靠反射支集包含和域外a.e.零值，不能从任意存在性接口猜测。

FiniteOddBoxExtension 按有限坐标迭代，同步保留原 IsPoissonExtension 的Dirichlet归属、弱方程、精确原域恢复和统一4^card范数界，以及每个已处理原面、宽度b_r−a_r的局部奇性。每次新坐标尚未扩大，所以原盒零延拓在该坐标原区间外为零；两面引理处理新坐标，反射交换处理旧坐标。全部盒几何与常数在状态之前固定。

OddSlabSmoothing 将局部带条件转成卷积所见球的局部奇条件。由逐坐标范数受欧氏距离控制，半径≤带宽时原面卷积严格为零。有限个正带宽给一个统一的足够大n，对整个frontier同时零值，包含棱边、角点；原面存在性从真实盒闭包及frontier刻画证明。最终 exists_box_poisson_extension_smooth_boundary 对原H¹₀弱Poisson解内部构造同一扩展及实际C∞卷积序列、最终严格零边界。

本批最终定理没有声称这些卷积已在原盒H²图范数收敛。局部H²收敛工具已就绪，但还需把实际扩展的H²正则性与原域全部弱字段恢复接起来，再处理完整周期轨道。原稿不改，P024不提升。

定向3378 jobs、根目标4051 jobs、7690声明递归公理审计通过；固定raw2404009 bytes，SHA256 2075233434715e3046f2ff8127f5b1ef60912ac516c4be6d56bf01efbbcdada2。固定SHA、同SHA真实三项CI及独立Agent语义验收另行登记。
