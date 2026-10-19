# T122：原 H¹₀ 连续代表的真实边界零值

本阶段清偿原 P1 Step 2 中节点插值保持齐次 Dirichlet 条件的边界义务。对任意开凸域 S、原全部 H¹₀ jet u，以及任意在 closure S 连续且在 S 上 a.e. 等于原 value 的 f，证明每个 frontier S 上的点都满足 f=0。主结论无需预设边界迹定理、光滑边界或原状态点态导数。

`SmoothGapCutoff` 对任意 δ>0 构造真实 ContDiffBump 的补函数 η=1−b。取内外半径 δ/4、δ/2，得到全局光滑 Lipschitz 的 η，η(0)=η′(0)=0，而 |t|≥δ 时 η(t)=1、η′(t)=0。这些导数零值由实际邻域恒等式或支撑外性质证明。

`WeakZeroGradientConstant` 对原真实 L² 状态使用已证全弱凸域 Poincaré，全部弱梯度为零使均值平方误差积分为零，再由实际可积非负函数的零积分得到 a.e. 常数。空域单独覆盖。

`WeakScalarGap` 对全空间原弱 H¹ 数据应用 T121 的真实标量链式法则。若在一个有界开凸集合上 u 的值 a.e. 只能为零或绝对值至少 δ，则 η′(u) 的每一个真实弱导数乘子在该集合 a.e. 为零。限制后的 η(u) 因此由 Poincaré 成为一个 a.e. 常数。η 的实际两种取值表明：该集合上要么 u a.e. 为零，要么 |u| a.e. 至少 δ，不能跨越该正间隙。不存在把任意 L² 代表当连续函数的步骤。

`DirichletContinuousBoundary` 反设某边界点 f(x)≠0。闭包连续性给一个真实开球 B 及 δ>0，使 closure S∩B 上 |f|≥δ。原 H¹₀ 的全空间零延拓 w 具有全部真实弱 H¹ 导数，且其值在 B 上满足上述二值间隙条件。若 w 在 B a.e. 为零，利用 S∩B 为非空开集和实际连续代表 a.e. 唯一性，推出其中 f=0，与下界矛盾。若 |w|在 B a.e. 至少 δ，开凸域的 interior(closure S)=S 保证闭包外开集与 B 相交；该集合具有正测度，实际零延拓又在那里为零，矛盾。

这一证明对每个边界点成立，不从边界零测推断节点取值，不新增几何延拓算子或点容量假设。主定理只要求原 H¹₀ 与现有闭包连续代表，甚至无需 S 有界或 d≤3；后两条件仅用于最终弱 H² 入口内部构造代表。`exists_dirichlet_closure_representative` 对原全部有界开凸域 d≤3 的弱 H² 且 value∈dirichletSubspace 状态自动给同一闭包连续代表、原 a.e. 身份和全部边界点零值。

四模块5显式声明，定向3350 jobs、全库3876 jobs通过；6702声明递归公理审计PASS。固定产物 `/tmp/carleman-dirichlet-continuous-local-axioms.txt` 为2037306 bytes，SHA256 `d3a489fa8a703d6acf48fcb8b25afd045dd97db9534202d15419834fff90ed9b`。

AUXILIARY，原文14/26。原全部弱 H²∩H¹₀ 的边界零值现在已证明；全弱局部节点值/梯度界由前阶段完成。随后仍须将同一代表接入实际全网格 conforming 节点插值、其真实误差 jet 和全域允许权及投影组合，P011不提升。原稿未修改。
