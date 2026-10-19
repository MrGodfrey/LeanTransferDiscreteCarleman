# T113：光滑状态的真实 L² Hessian 节点梯度误差

本阶段补齐上一阶段光滑类节点插值的梯度估计；仍不冒充原全弱 H² 状态、边界节点资格或全局加权逼近。

`derivativeOneFiber_norm_sq` 精确识别项目真实 Euclidean 梯度纤维的范数平方为所有坐标方向值的平方和。`smooth_directional_gradient_bound` 将 D(Df·e) 的真实算子范数控制为 ‖D²f‖‖e‖，使用实际 Fréchet 导数、双线性翻转和 iteratedFDeriv 的等距柯里化身份，没有仅按形式把二阶导数写成候选矩阵。

`averagedTaylorPolynomial_derivative` 证明同一实际平均 Taylor 仿射多项式的梯度恰为平均 Df。逐坐标应用已验收凸域均值 Poincare，随后使用真实坐标导数界及有限积分求和，得到同一 f−p 的完整梯度 L² 界：`d·2^(d−1) D² ∫K‖D²f‖²`。此步骤对一般维数成立；随后的节点值部分保持 d≤3。

`simplexNodal_smooth_h2_gradient_integral` 使用原实际闭单纯形内接球 ball(a,r)⊆K、D≤κr 和真实直径界。节点插值再现平均 Taylor 仿射多项式，由上一阶段的 L² Hessian 点态余项控制所有真实顶点；实际仿射差 I_Kf−p 在内球上有界，因此其真实梯度范数≤4R/r。纤维连续线性映射的范数仅依赖固定维数，未引入随网格变化的范数等价常数。

证明将实际 `Df−D(I_K f)` 分为 `Df−Dp` 和 `Dp−D(I_K f)`，使用真实范数平方三角界、积分与正体积消去。由 D²/r²≤κ² 得最终结论

`∫K ‖derivativeOneFiber(Df−D(I_K f))‖² ≤ (2^d d+128 κ²‖derivativeOneFiber‖²) D² ∫K ‖D²f‖²`。

梯度左端是项目采用的完整 Euclidean 梯度纤维；右端仍为实际二阶多线性算子范数的 L² 积分。后续需要将其与弱 jet 的 Hessian 分量范数连接，不能把本批视为已经完成该识别。与 T112 的值误差合用，已在光滑类上获得原局部 h² 值误差和 h 梯度误差，常数只依赖 d、κ。

单模块5项显式声明，定向3273 jobs、全库3837 jobs通过；6582项递归公理审计通过。固定产物 `/tmp/carleman-p1-h2-gradient-local-axioms.txt` 为1959277 bytes，SHA256 `8973a261982beccfa39184d4fcf3d420b594ab5c9e1a1a184fcbcb913e8aff35`。AUXILIARY，原文14/26；原全弱 H² 状态、节点连续代表、边界适配和全局允许权逼近仍待，P011不提升。原文未修改。
