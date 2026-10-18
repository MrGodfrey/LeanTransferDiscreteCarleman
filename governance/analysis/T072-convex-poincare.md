# T072：凸单元光滑函数的均值 Poincaré

四模块11声明，AUXILIARY。为原 Appendix B 的一般 H² 逼近建立均值 Poincaré 基础。本阶段针对真实全空间 C¹ 函数在任意紧凸单元 K 上的限制，结论为

∫K |f−meanK f|² ≤ (2^d/2) D² ∫K ||Df||²。

K 必须具有正的实际 Lebesgue 体积，D≥0 是真实两点距离的上界。Df 是实际 Fréchet 导数，右侧是其算子范数平方的真实积分，不是自由提供的梯度、Lipschitz 上界或 Hessian 上确界。常数仅依赖维数，允许任意形状的紧凸 K。

MeanSquareDifference 在任意有限测度的真实 L² 函数上展开平方并证明 2m·variance 等于两点差平方的双积分。所有拆分积分先证明可积性；最终除以 m 需要 m>0。

ConvexSegmentIntegral 以真实可逆标量线性映射及仿射换元识别雅可比 r^d，凸性确保像仍在 K。r∈[1/2,1] 给逆雅可比≤2^d。SmoothSegmentSquare 使用真实 C¹ 导数沿线段的微积分基本定理，再用实际 L² Cauchy–Schwarz 得到差平方的导数积分界，未代入上确界。

ConvexSmoothPoincare 对参数 [0,1/2] 的半线段使用上述雅可比界与 Fubini；所有二重积分由连续性和紧性证明可积。两端到同一中点的平方差各自受控，交换积分后得到双差界 2^d·volume(K)·D²·∫K||Df||²，再由精确均值恒等式消去 2·volume(K)。没有遗漏半区间长度或两次平方三角因子。

这里只完成光滑函数的真实 L² 估计，尚未通过局部卷积和域内穷竭传到原弱 H¹/H² 状态，也未完成节点插值、边界校正、B1/B2 或 N3。没有把全空间 C¹ 前提冒充原一般 H²；原文仍12/26。
