# T039：全空间零延拓 H¹ 与真实 Dirichlet 闭包

五模块27声明，AUXILIARY，服务于原 Section3 的 Dirichlet 形式及 Section6 的 conforming P1 空间。原稿及完整原文覆盖不变，仍12/26。

## 全空间实际函数和导数

`SimplicialGlobalDerivative` 沿用同一个实际 nodalFunction 和逐片 CLM 导数字段。有限单元 frontier 在全空间 volume 下零测；其余点若在 closure S 内，则位于某单元内部，若在外则有恒零邻域。由此证明全空间 a.e. HasFDerivAt。这里不需要边界节点零，因为仅断言经典 a.e. 导数，未推出弱导数。

各导数 indicator 的支撑包含实际紧单元，直接由 compact 的有限体积证明 MemLp，不假设全空间体积有限。边界节点零、BoundaryFitted、FaceMatching 和 S 开给原函数全空间连续，有限紧单元给紧支，再构造实际全空间标量 Lp 类。所有代表身份均为 a.e.，没有把任意 Lp 代表当连续函数。

`LipschitzGlobalSobolev` 对全空间真实 Lipschitz 函数、实际标量及导数 Lp 类证明完整弱导数与 H¹ jet。积分分部直接使用固定 mathlib 的实际 lineDeriv 定理，再以光滑测试的实际 fderiv 识别正确负号。全部 SpatialTest univ 都参与测试；hA 是真实 HasFDerivAt a.e.，不是目标分布积分式。`SimplicialGlobalSobolev` 用已证全局 Lipschitz、实际 Lp 代表及上述 a.e. 导数供应该接口，value 精确等于 nodalGlobalLp。因此零延拓确属全空间 H¹，而非仅在 S 内 H¹。

## 光滑测试的真实 H¹ 与闭包

`SpatialTestSobolev` 对原完整 SpatialTest S，使用真实 C∞ 导数的连续性、导数紧支和紧集有限测度构造 fderivLp。所有坐标弱导数由实际 Lipschitz 积分分部证明，组装 firstOrderJet；value 精确为 φ.toLp(volume.restrict S)。无需事先给定 jet 或弱导数身份。

`DirichletSpace` 以所有这些真实光滑 jet 的线性张成在 WeakSobolevJet 的 H¹ 图范数中的闭包定义 dirichletJetSpace，再经真实 value 映射到标量 L² 定义 dirichletSubspace。每个测试函数都属于其中，整个空间包含于既有 sobolevSubspace。S 开时既有弱导数唯一性使 value 单射，所以 scalar 成员等价于 jet 成员，闭包本身闭合推出原 H¹ 拓扑意义的闭合。此结论不声称在 L² 中闭合。

L² 稠密性由正交补刻画：若 u 与这个 scalar 子空间正交，则它与所有原 SpatialTest 的真实 L² 类正交；已证的完整空间测试分离性使 u=0。因此闭包是全部 L²。此证明没有把 H¹ 稠密性或零迹识别放进输入。

## 未完成义务

两项构造之间仍有实质桥梁：节点零延拓属于全空间 H¹，并不自动使其在任意开集 S 上属于这里的紧支光滑 H¹ 闭包。必须继续证明适合原凸多面体的支撑内缩与光滑逼近。Poincare/梯度能量强制性、实际 Dirichlet OriginalForm、H² 连续代表、网格形状/分级、局部误差、加权稳定与连续热 CE 均未完成。本批不能提升 P011 或其他完整命题。
