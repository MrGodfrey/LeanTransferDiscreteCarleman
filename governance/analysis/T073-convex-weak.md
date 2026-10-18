# T073：原凸域的真实弱 H¹ 均值 Poincaré

五模块21声明，AUXILIARY。将 T072 的光滑均值估计真正传到原域所有弱 H¹ 状态，得到

∫S |u−meanS u|² ≤ (2^d/2) D² ||∇u||²。

S 是原有界开凸域，正体积；D≥0 是真实两点距离上界，u 是 WeakSobolevJet d 1 (volume.restrict S) S 的任意状态。没有零边界条件、全空间 H¹ 延拓、光滑性或代表的逐点可微性前提。右侧是原一阶完整 Euclidean 导数字段的真实 L² 范数。

PairwiseL2Limit 先从实际 L² Fatou 得到平方积分的最终一致上界传递，继而证明真实双差函数的 L² 成员资格、代表不变性与双差极限；穷竭版用可测指示函数及最终包含传递能量，不要求单调序列或积分极限存在。

MollifiedGradientEnergy 用真实正交基的 dual norm 平方和精确识别 Frechet 导数能量。每个坐标通过原弱测试与局部卷积交换识别为对应真实弱导数的卷积，再由单位非负核的 L² 收缩得到原梯度能量上界。没有加入维数范数比较损失；积分拆有限和与空间限制均有 L² 可积性。

InteriorWeakPoincare 为任意紧凸 K⊆S 从紧性取得正的域内缓冲半径，证明 shrinkingBump 半径趋零后所有反射核测试留在原域。原标量与弱坐标导数仅以 L² 零延拓用于卷积，原完整弱身份仅在 S 内使用；没有断言零延拓具有全空间弱导数。卷积的实际 a.e. 收敛通过双差 Fatou 给 K 的均值估计，右侧仍是原域梯度能量。

ConvexCompactExhaustion 给出显式 K_n=a+r_n(closure S−a)，r_n=(n+1)/(n+2)。实际 K_n 紧、凸、严格包含于开 S，所有 x∈S 最终属于 K_n（由逆收缩点趋 x）。没有假设边界正则性或边界测度结论。

ConvexWeakPoincare 在原限制测度的乘积上对 K_n×K_n 作真实指示穷竭，使用 volume(K_n)≤volume(S) 得统一双差界，再由精确均值恒等式消去 2 volume(S)。最终 wrapper 从原 jet 的完整弱坐标身份取得各 v_i，通过 Sym.oneEquiv 将坐标平方和精确识别为原 field 1 的平方范数。空域双差分支显式处理；均值结论要求正体积。

本阶段证明一般弱 H¹ 的均值估计，是一般 H² 仿射逼近的基础。尚未完成二阶仿射构造、边界校正、节点 H² 插值、B1/B2 或 N3；不提升原文完整命题，原文仍12/26。
