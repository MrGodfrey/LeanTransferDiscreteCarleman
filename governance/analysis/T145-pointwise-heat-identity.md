# T145：真实时空热算子的点态 Carleman 恒等式

本阶段对应原稿 `prop:continuousCE` 证明引用 Fu–Lü–Zhang, *Carleman Estimates for Second Order Partial Differential Operators and Applications* (2019), Corollary 3.1，印刷第60页 / PDF第69页的点态恒等式步骤。准确范围是 p=Id、Φ=0、实数未知函数，在全空间光滑状态/权/辅助函数上的等式及不等式。原稿及书本原页已实际阅读。本批不声称完整 Proposition A.3：实际面 Green 积分、时间端点抵消、系数估计与吸收、原时间权和原 Sobolev 状态的极限传递及时间反射仍待，P024 不提升。

`smoothD e f(x)` 定义为真实 `fderiv ℝ f x e`。加减乘、有限和、平方、指数及二阶混合导数交换均从真实微分法则证明，没有自由的导数字段或未证明 Leibniz/交换公理。`directionalLap`、`directionalPair`、`directionalEnergy`、`directionalHessianForm` 分别是固定有限空间方向的二阶迹、梯度配对、梯度平方和及 Hessian 二次型。通量中的 Hessian(z) 交叉项由实际二阶导数交换和两重有限和交换抵消。

通用恒等式允许任意固定时间方向 t、空间方向 e，以及实际光滑 ℓ、k、Ψ、z，定义

- M=kz²−|∇z|²；
- V=2z_t∇z+4(∇ℓ·∇z)∇z−2|∇z|²∇ℓ−2Ψz∇z+2kz²∇ℓ；
- c[∇z,∇z]=2 Hess(ℓ)[∇z,∇z]−(Δℓ+Ψ)|∇z|²；
- B=k_t+2 div(k∇ℓ)+2kΨ。

恒等式完整保留真实 M_t、真实 div V 及两个平方项：

R²+M_t+div V=(Δz+kz)²+(z_t+2∇ℓ·∇z−Ψz)²+2c[∇z,∇z]−2(∇Ψ·∇z)z+Bz²，

其中 R=z_t−Δz+2∇ℓ·∇z−(k+Ψ)z。它首先由实际通量的逐项微分证明，而非把最终等式假设为接口。

随后定义原 A=|∇ℓ|²−Δℓ−Ψ 与 k=ℓ_t+A，并证明其真实展开。`pointwiseHeatB_original_formula` 将 B 精确展开为原书的 2AΨ+2 div(A∇ℓ)+2 div(ℓ_t∇ℓ)+2Ψℓ_t+ℓ_tt+A_t。指数一、二阶真实微分与乘积法则给 R=exp(ℓ)(∂t−Δ)(exp(−ℓ)z)，从而得到完整点态等式，去掉第二个非负平方得到原不等式。原 c 外的系数 2、Ψ 梯度项的负号、B 的全部时空项均保留。

最终在实际 `ℝ × SpatialCoordinates d` 上选 t=(1,0)、e_i=(0,EuclideanSpace.basisFun i)。链式法则明确证明该时间方向导数就是固定 x 的真实 `deriv`，空间方向就是固定 t 的真实 `fderiv`，方向 Laplacian 就是同一真实 `spatialLaplacian`。`spaceTimeHeat` 因而是原 ∂t−Δ，而非任意的残差算子。最终 `spacetime_heat_carleman_identity/inequality` 的未知量从原任意 u 内部定义为 z=exp(ℓ)u，逐点证明 exp(−ℓ)z=u；左侧是同一原 u 的真实热残差。

正则性边界明确：本批声明要求全时空 ℓ、Ψ、u 为 C∞，是平滑情形的点态准备步骤。原 q 只有 C²、空间状态属于原 H²∩H¹₀，原最终轨道是 H¹_tH∩L²_tD(A)；这些更弱类别尚未通过本批恢复，不能忽略此差别或把 C∞ 条件加入原最终命题。后续需要证明有限方向正则性的推广或保持所需时间权界的逼近，并建立实际域上的积分、端点及 Sobolev 密度传递。空间域、T、周期、网格及状态谱截断不进入本批点态等式，亦没有选择最终 β、q_c 或断言 heatcross 的 λ 一致常数。

五模块53显式声明；既有实际 Laplacian 来自 C149（T133，版本 c3ea3c03352de258d944bf495695b31bcef3f3b0），其余为固定 mathlib 的真实微分定理。新增文件不改既有已验收对象或原稿。申请 AUXILIARY 验收，原文覆盖保持17/26。
