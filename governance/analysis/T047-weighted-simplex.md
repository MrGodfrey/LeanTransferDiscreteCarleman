# T047：所有物理单纯形的统一局部加权逆估计

两模块11声明，AUXILIARY，继续原 Section6 加权逆估计的局部步骤。新结果不再输入某个固定参考 T 及其物理仿射像表示；内部为每个维数选择一次参考单纯形，构造任意物理单纯形与它的真实仿射等价。最终常数只依赖维数 n、形状比 κ 和单元内权比较 W，先于所有物理单元、内球、尺度、权函数及多项式。

SimplexReferenceMap 从任意 T,U 的真实仿射基中选同一个第0顶点，以其余顶点差构造两组线性基。基之间的实际 LinearEquiv 经有限维连续性成为 ContinuousLinearEquiv；平移量 U0−A(T0) 使每个真实顶点准确映射。以单纯形顶点外延性证明 affineSimplex T A b=U，维数0的空线性基分支同样成立。referenceSimplex n 从有限维 AffineBasis 存在定理选取，仅依赖 n。于是已证形状逆界成为 ∃C(n,κ)>0，对所有U及实际内球 ball(a,r)⊆cell U、h>0、r>0、h≤κr和全部节点系数统一成立。

SimplexWeightedInverse 在每个真实单元的受限 Lebesgue L² 上取实际 BoundedMultiplier w。明确局部比较为 |w|≤Ws、s≤W|w| a.e.，其中 W>0 先置、局部归一化 s>0 可随单元及权变化。原有实际乘子范数比较给 ‖w∇p‖≤Ws‖∇p‖ 和 ‖p‖≤(W/s)‖wp‖；与无权逆估计组合后 s 精确消去，最终常数为 W²C(n,κ)。不把 w.bound 当统一常数，不要求权函数在任意 Lp 代表上取点值。

最终给三种等价适用形式：全部节点系数；任意真实 AffineMap p 及 a.e. 与p/其实际全坐标Fréchet导数相等的实际 L² 类u/g；以及真实积分 ∫cell |w|²‖∇p‖²≤(C/h)²∫cell |w|²|p|²。它们均由同一真实局部多项式和梯度识别，不输入目标逆估计。Lp 身份使用仿射再现和完整 toLp a.e. 公式，从不对任意 L² 代表求节点值。

尚未清偿原具体 allowed 权族从 hq≤δ 到上述比较的统一推导，也未在本阶段证明任意完整 V_h 状态的全局弱梯度限制等于局部仿射导数、全网格求和或 ℓ/h 比较。因此原 eq:p1-weighted-inverse 的全域结论及 Proposition6.1 仍未完成，原文12/26不提升。H2点值/插值误差、加权投影、椭圆正则性及连续热CE仍待。
