# T160 / C176：盒 Dirichlet 算子图的严格零边界光滑密度

本批把已证明的完整空间 H²∩H¹₀ 逼近接入真实 Dirichlet 算子图。四模块十声明，范围 AUXILIARY；完整周期时空图密度与弱 CE、一般凸多面体仍未完成，P024 不提升，原文覆盖保持 17/26。

BoxCompactSmoothDensity 用固定紧支光滑截断（在原盒闭包上恒为一）乘 T159 的全局光滑逼近。开盒上函数严格相等，经局部 Fréchet 导数唯一性保持全部一、二阶实际坐标导数。因此输出为真正 SpatialTest univ 序列，仍逐项在整个原 frontier 为零，值、梯度和全部 Hessian 分量在原域 L² 中强收敛。

SmoothLaplacianL2Limit 证明代表函数的 L² 误差极限确实给实际 Lp 范数收敛，并把真实二次坐标导数与空间 Laplacian 对齐。由有限项真实 Lp 求和，所有二阶分量收敛给负 Laplacian 的实际 Lp 强收敛；没有以新符号替代原算子。

SmoothDirichletGraph 对任意正维有界非空凸开域，将全局紧支光滑且全 frontier 零值的函数放入真实 Dirichlet 域。原 H¹₀ 归属由已证边界零值定理供应，实际弱 Poisson 方程通过空间限制继承，并用原形式算子图等价证明其算子值恰为负 Laplacian。这一接口不假设域归属或 Green 恒等式。

最终 exists_box_smooth_operator_graph_approximation 对实际盒 Dirichlet 算子图任意 z，内部使用已证全盒 H² 正则性及原 H¹₀ 归属，取得同一原状态的 H² jet。构造 SpatialTest U_n 及实际算子图 Z_n，逐项满足原边界零值、graphH Z_n 等于 U_n 的原域 Lp 类、graphA Z_n 等于负 Laplacian Lp 类，并在实际算子图拓扑中收敛到 z。结论保留所有原域元素，而非仅在预先光滑子空间中声明稠密。

定向 3464 jobs、根目标 4058 jobs、7713 项递归公理审计通过。公理产物 2416329 字节，SHA256 c94678abd8b1aafea6f4d9a21cd3c4bb5ffc571a083007306ef45f40153d6c3f。固定 SHA 及远端三项 CI、独立语义验收另行登记。下一步将实际空间图逼近接入周期谐波及全部弱周期图轨道；本阶段没有宣称完成该时间方向步骤或完整连续 CE。
