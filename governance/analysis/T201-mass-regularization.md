# T201 — 能量空间质量算子的实际正则化

基线 `a081c61839658c2869ef6a01e7bcd387a81b9af4`；原稿 `paper/main.tex:2420–2421`，原控制极限 H 连续时间迹的辅助证明。3 模块 19 声明，AUXILIARY，17/26。

本批选用质量正则化证明时间迹，属于原结论不变的证明路线。一般 Hilbert 空间 V 上，M 为实际有界线性算子，明确要求 (Mv,v)≥0。`positiveMassForm` 构造 Bε(v,w)=(Mv,w)+ε(v,w)，对每个 ε>0 的实际强制性由原非负性直接证明；`positiveMassInverse` 通过真实 Lax–Milgram/variationalSolve 构造 Rε=(M+εI)⁻¹，不将逆存在性作为输入。

`positiveMassInverse_equation`、`positiveMassInverse_left` 给出实际左右逆恒等式，`positiveMassInverse_commute` 推导 RεM=MRε。`positiveMassRegularizer` 是 Qε=MRε。原内积方程分别测试 MRεx 和 Rεx 得到 ‖Qεx‖≤‖x‖ 及 ‖x−Qεx‖≤‖x‖；随后证明对真实 range 元素 ‖Mx−QεMx‖≤ε‖x‖。这些一般结论不要求有限维、紧性或自伴，只有已经明确的非负性。

`positiveMassRegularizer_strong` 在明确的 M 稠密值域假设下，以残差收缩及 range 误差证明任意正序列 εn→0 时 Qεn x→x。`adjoint_mass_denseRange` 则对任意单射有界 E:V→H，实际证明 E*E 的值域稠密：伴随算子正交核/闭包身份、ker(E*E)=ker(E)=0 及其自伴性给结论，不输入原质量的稠密性。

`compLpL_strong_of_contractions` 对实际强收敛至恒等映射的收缩族，使用平方范数的支配收敛定理（支配函数 4‖Y(t)‖²）证明逐时间 compLpL 在原 Bochner L² 范数下强收敛。全过程核对真实 a.e. 代表元、Lp 差以及积分范数身份，不把逐点强收敛直接当作算子范数收敛。

最后六项将以上构造接到 T200 的真实 `dirichletTimeMass=E*E`。非负性由实际值内积证明；E 的单射性由真实 Sobolev 值注入给出，因此原质量的稠密值域得到清偿。`dirichletMassRegularizer` 是实际构造；其收缩性、对每个完整 H¹₀ 元素的能量强收敛，以及对每个真实 H¹₀ 值 Bochner 状态的 L² 强收敛全部无额外正则化前提。仅要求原 S 开，未要求光滑状态、有限维截断、h/dt 耦合或空间边界额外光滑。

ε 为证明中独立引入的辅助正参数，不改变原控制或网格。尚未证明时间正则化状态的 H 一致收敛、原 H 连续代表元或初终端识别；不能从 MY 在 V 中连续直接推出 Y 在 H 连续。本批不提升 P021，原稿未修改。
