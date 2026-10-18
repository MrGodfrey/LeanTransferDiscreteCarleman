# T044：真实光滑逼近与节点 H¹₀ 成员

五模块30声明，AUXILIARY，对应原 Section6 一致 P1 空间的真实零边界节点成员。本阶段完成实际节点函数进入以 C_c∞(S) 的 H¹ 闭包定义的 Dirichlet 空间，并进入实际一致分片仿射空间；原 Proposition6.1 的定量近似、加权投影稳定性等仍待，原文12/26。

## 实际卷积与导数

`CompactConvolution` 对非负、积分为1的原 SpatialTest univ 核，证明真实卷积保持原函数的全局范数界及 Lipschitz 常数。积分支配由紧支核可积性证明，Lipschitz 身份使用两个实际可积卷积之差，非形式代换。卷积闭支撑包含于原函数 tsupport 的 r 闭邻域，只要核闭支撑在半径 r 的闭球中；实际 support 的 Minkowski 和先给点态包含，再由闭厚化的闭性覆盖整个 tsupport。真实光滑性和紧支也构造。

`CompactConvolutionDerivative` 对任意方向 e 从真实全局 Lipschitz 积分分部证明弱导数身份，导数 Lp 类就是实际 fderiv 的连续线性求值。随后以该身份、已证卷积交换及连续线性求值与 Bochner 积分交换，证明

`fderiv (κ⋆f)(x) = (κ⋆fderiv f)(x)`。

这是实际 CLM 值等式，不是选取任意候选梯度；a.e. Lp 代表经卷积同余处理，得到对每个 x 的准确等式。

## 真实光滑化的 H¹ 极限

`CompactMollificationLimit` 使用既有归一化 C∞ bump，半径 2/(n+1) 趋于0且不超过2，内外半径比例始终为2。定义原函数与该核的实际卷积，证明光滑、紧支、Lipschitz 常数不变、精确半径厚化支撑。

连续原函数给每点函数值极限；实际 fderiv 由既有全空间 MemLp 推出局部可积，固定 mathlib 的 Lebesgue 微分／bump 卷积定理给 CLM 值 a.e. 极限。结合上述准确导数交换，得到实际光滑函数 fderiv 的 a.e. 极限。共同支撑位于紧集 cthickening 2(tsupport f)，函数统一界及 Lipschitz 常数由前述卷积估计内部供应。T043 的真实两个 L² 字段支配收敛于是给完整 H¹ 图拓扑极限。没有把之前仅 a.e. 的卷积极限直接当作 H¹ 极限。

## 实际 Sobolev 限制

`SobolevRestriction` 把原 SpatialTest S 视作 univ 上同一个光滑紧支函数。任意全空间弱导数身份可对该测试使用；真实 Lp 限制的 a.e. 身份，以及测试值和导数在 S 外为零，把全空间积分精确变为受限体积积分。因此每个原弱身份在域内仍成立，而非假设一个限制后的 jet。

全部真实 L² 字段逐项限制，分量求值与限制准确交换，构造任意阶实际 WeakSobolevJet.restrictDomain。标量 value 保持真实限制，且每个字段的 L² 限制连续，故完整图拓扑极限保持。开域上，若全空间 jet 的真实标量值是某个 SpatialTest S，则限制后与该测试已有的 domain sobolevJet 严格相等，由完整弱导数唯一性证明。

## H¹₀ 闭包成员及实际一致空间

任意紧支 Lipschitz f，只要 tsupport f⊆开S，紧性给正卷积 buffer δ。核半径趋于0，因此所有充分大的光滑卷积都具有紧含于 S 的支撑，实际构成原 SpatialTest S。其限制 jet 就是该测试的真实 sobolevJet，因而属于原 dirichletJetSpace。完整 H¹ 极限及这个拓扑闭包的闭性证明原 f 的限制 jet 也属于该空间。

对真实边界零节点函数，T042 的凸域内缩保证每个固定 r_n 的闭支撑紧含于 S，故上段给每个内缩的 H¹₀ 成员；T043 的真实内缩 H¹ 极限经连续限制传到原域，再由 H¹₀ 闭性得到原节点函数的成员。最后精确识别实际 nodalLp 值，从而证明 nodalLp∈dirichletSubspace，再和已有真实逐片仿射成员组合，得到 nodalLp∈M.conformingSpace(dirichletSubspace S)。

公开条件为开凸 S、有限真实单纯形分区、FaceMatching、BoundaryFitted 和所有边界顶点值零。最终标量结论不要求非空中心：S=∅ 分支直接用零受限测度证明实际 Lp 类为零；S≠∅ 才取中心并使用内缩。保留原 nodalLp 已有的有限受限测度类型实例；有限分区本身已证明 closure S 紧，这一实例不是额外几何限制。任意维数均成立。

没有声称所有 H¹₀ 函数都具节点值，也没有在任意 Lp 等价类上取点值；输入仍为真正点态节点数组。H² 连续代表/椭圆正则性、具体网格和形状正则统一常数、加权投影及 h/h² 误差、连续热 CE 仍待，不提升完整原文覆盖。
