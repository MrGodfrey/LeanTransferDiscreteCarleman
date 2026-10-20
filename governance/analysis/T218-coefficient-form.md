# T218 — 任意阶原系数形式及统一加权上界

固定基线 `79151186853d57b5e937851b51ace47c05a4e7ff`。原稿 `paper/main.tex:2615–2652` 的 coefficientform 及 unshiftedformbound。两模块17项显式声明（含2个缩写），AUXILIARY、17/26，不提升完整 Proposition A.1。

在 Σ k:Fin(m+1), Sym(Fin d) k 的全部无序多重指标上，使用实际弱射流分量 CLM、原有界乘子的 L² 作用及实际内积，构造连续双线性有限和。积分公式证明其恰为 ∑αβ∫aαβ Dβu Dαv，每个多重指标出现一次；未限制为对角系数或最高阶系数。a.e. 对称系数经真实乘子相等与内积交换得到形式对称。

对任意有界互逆乘子 w、ξ 和任意 q≥1，每个原导数分量的 w-L² 范数由原 Nq,w 范数控制。配对中插入实际 wξ=1，再用系数与标量乘子交换和 L² Cauchy–Schwarz，得到 |a(u,v)|≤(∑αβ bound(aαβ)) Nq,w(u) Nq,ξ(v)。常数在 q、权、符号、时间长度及状态之前固定，仅取决于既定系数界；无权导数或权自身 sup 界进入最终常数，也不要求系数光滑。上界甚至只需 bounded measurable 系数；原 W^{2m,∞} 系数是其子类。

将同一有限和限制到真实 H₀ᵐ 的 conformingHilbert 实现，明确证明能量范数平方正好等于所有 Dαu 的 L² 范数平方之和，并给出原积分公式、对称性和加权上界。由已证明真实 H₀ᵐ 在 Hᵐ 中闭、在 L² 中稠密，及原文给定的同一形式 Hᵐ coercivity，构造 OriginalForm；没有假定目标加权上界或额外正则性。此处 coercivity 是原命题的原始输入，尚未断言该关联算子的 H^{2m} 域身份或图界。

局部 ContinuousAdd 实例只是显式选择 mathlib 已有强对偶 IsTopologicalAddGroup 的投影，解决推断歧义；不修改弱射流的图拓扑、范数或任何数学条件。一般系数的 W^{2m,∞} 弱乘法、交换子和加权下界仍待。
