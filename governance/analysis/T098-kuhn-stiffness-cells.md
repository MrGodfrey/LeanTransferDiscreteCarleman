# T098：实际 Kuhn 弱刚度的精确单元差分展开

两模块9声明，AUXILIARY。对原全部内部节点状态f、g，严格证明原实际Dirichlet scalarForm(R_h f,R_h g)等于所有实际有限Kuhn单元上“真实单元体积×相邻顶点差商乘积之和”。这是Section6有限差分刚度证明的真实导数和单元组装步骤；全局坐标边重排、有限差分分部求和以及完整FD刚度身份仍待。

`KuhnNodalGradient` 使用已接受的真实物理顶点差 v_(k+1)-v_k=δ_(πk)e_(πk)，对实际节点仿射插值p应用真实仿射线性部分，得到 ∂_(πk)p=(c_(k+1)-c_k)/δ_(πk)。导数是实际fderiv，由仿射HasFDerivAt严格识别；没有另外赋予形式离散梯度。完整DerivativeFiber的欧氏内积经Sym.oneEquiv精确化为各坐标导数乘积之和，再经π重排。真实simplexNodalGradientLp配对因此精确等于单元体积乘相邻差商内积，无比较常数或误差。

`CartesianKuhnCellStiffness` 定义实际单元相邻差商，节点数据为此前原cartesianInteriorData（全部原内部状态、物理边界零延拓）。已接受R_h真实H¹₀ jet的弱梯度在每个闭单元上a.e.等于真实仿射梯度，所以坐标差商和整个局部能量均是原弱场的恒等式。原有限分割的积分恒等式给实际全域weakGradientPairing的单元体积加权和。最后用已接受dirichlet_scalarForm_eq把该恒等式接入同一boundedDirichletOriginalForm.scalarForm，严格使用相同R_h的原Dirichlet成员及精确值身份。

声明对全部正步长、原有限网格、任意维数的真实梯度配对成立；原scalarForm版本保留其原正维数前提。没有网格可比或小参数限制，未将单元体积替换成未证均匀值。下一阶段可利用已证单元平移不变性与排列体积总和，对每个坐标边汇总全部排列；不必先证明每个排列体积相等。完整2d+1点Laplacian及FD/P012不由本批提升。原稿和工具链未改。
