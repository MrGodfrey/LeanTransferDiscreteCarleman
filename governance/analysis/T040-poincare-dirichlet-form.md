# T040：实际 H¹₀ 的 Poincaré 与 Dirichlet 梯度形式

四模块27声明，AUXILIARY；对应原 Section3 A1 与 Section6 的 `V=H₀¹(Ω)`、`a(u,v)=∫∇u·∇v`。本批实际供应这个形式，不再将其连续、对称、强制或 Poincaré 作为输入。原稿和完整命题覆盖保持不变，12/26。

## 完整光滑测试与 Poincaré

`SpatialTestOperations` 给零、加法和实数倍的真实 SpatialTest 构造：C∞、紧支及 tsupport 包含于 S 全部由函数实际性质证明。开集上利用真实 value 单射和 Lp a.e. 运算证明对应 jet 的线性身份。span_induction 因此证明每个测试 jet 线性张成中的元素本身就等于某个测试 jet，没有把估计错误地按三角不等式传到任意抵消的线性组合。

`TestPoincare` 对真实 CLM L 构造 `ψ(x)=L(x)φ(x)`，证明准确乘法导数。由已证全局 Lipschitz 积分分部得到 φ 的任意方向完整弱身份。若 `L(e)=1` 且 S 位于 `|L(x)|≤R` 的 slab（R≥0），则 ψ 的 L² 范数≤R‖φ‖。将 ψ 作为实际测试代入弱身份，利用准确乘法导数及可积的 L² 配对得到

`‖φ‖² = -2⟨D_e φ,ψ⟩`。

Cauchy–Schwarz 与前述 ψ 范数界给 `‖φ‖≤2R‖D_e φ‖`；φ=0 的分支单独处理，没有除以可能为零的范数。全程使用限制 Lebesgue 测度中的真实 Lp 类及 a.e. 公式，未缩小弱测试族，也未预设目标估计。

## 传到 H¹₀ 闭包

`DirichletPoincare` 首先精确识别 φ.sobolevJet 的每个一阶分量为实际 φ.derivativeLp。Euclidean 分量范数≤完整 fiber 范数逐点成立，经 Lp 的 a.e. 范数比较给真实导数分量的 L² 控制。

选 L 为坐标投影、e 为同一单位坐标方向，前述 slab 估计给所有测试 jet 的 `‖value‖≤2R‖field 1‖`。两个字段均为实际连续线性映射，所以该不等式的满足集合在 H¹ 图范数中闭合。每个 span 元素由已证明的线性闭合可表示为单个测试，于是闭包最小性将估计传递到完整 dirichletJetSpace。这里未假设 Poincaré、节点 H¹₀ 成员或任意边界刻画。

## 实际梯度形式与 A1

`DirichletForm` 使用既有 conformingHilbert 对真实 dirichletSubspace 的实现。dirichletGradient 是 subtype、SobolevHilbert.toJet 和实际 field 1 连续线性映射的复合；形式就是该 L² 梯度的内积。精确积分公式是所有一阶 Sym 分量的乘积和，恰含每个坐标一次。对称性由实内积证明。

零阶只有空多重指标，点态 Euclidean 范数与实际 scalar value 的绝对值相等；a.e. 范数比较给其 L² 范数严格相等。因此 Hilbert 能量范数准确为 `‖u‖H1²=‖value u‖L2²+‖grad u‖L2²`。Poincaré 推出 `‖u‖H1²≤((2R)²+1)‖grad u‖L2²`，从而得到正强制常数 `((2R)²+1)⁻¹`。不是通过给形式添加零阶项来取得强制性。

dirichletOriginalForm 内部供应实际空间、Sobolev包含、H¹闭合、L²稠密、连续双线性形式、对称和强制全部字段。进一步在任意正维、有界开集上，由真实 Bornology.IsBounded 得固定正范数半径，选一个坐标方向，内部供应 slab 条件，构造 boundedDirichletOriginalForm。常数只由固定空间域选取，不依赖时间、网格、权或状态。原 d=2,3 的有界凸多面体包含在该范围；不要求非空域。

## 剩余原文义务

本批完成真实 Dirichlet A1 形式的构造；尚未证明其全变分算子域等于 `H²∩H¹₀`、凸多面体 H² 椭圆正则性或原连续热 CE。节点零延拓进入紧支光滑 H¹ 闭包、H² 点值代表、具体网格条件及原局部误差/加权投影/逆估计仍需继续。完整 P1 Proposition 6.1 和热观测控制命题均不升级。
