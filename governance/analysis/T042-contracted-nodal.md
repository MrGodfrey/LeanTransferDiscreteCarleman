# T042：凸域内缩、正支撑缓冲与实际 H¹

三模块24声明，AUXILIARY，对应原 Section6 conforming 节点函数进入 H¹₀ 光滑闭包的准备工作。本阶段只构造内缩函数、实际 H¹ 成员及支撑缓冲；尚未证明逼近收敛或节点 H¹₀ 成员。原文仍12/26。

## 实际内缩与几何支撑

`ConvexSupportContraction` 定义真正的 centeredDilation 同胚 `x↦a+r(x-a)`，逆函数为 `x↦a+r⁻¹(x-a)`，两向互逆和连续性均证明。若 S 开且凸、a∈S、0<r<1，则 closure S 中每点的像都在 S 内；由凸集内部与闭包的严格凸组合性质证明。

contractedFunction 是原 f 与该逆同胚的真实复合，因而其 tsupport 精确等于原 tsupport 的正向像，紧支也保持。若原 tsupport⊆closure S，则内缩后支撑紧含于 S；实际紧集和开集包含关系给一个正 δ，使支撑的整个闭 δ 邻域仍位于 S。这个 δ 可以依赖 f、a、r，仅用于随后合法卷积；不宣称网格统一几何常数。

全局连续性在复合下保持，真实 Fréchet 导数用链式法则给出 `A∘(r⁻¹ Id)`；实际支持函数和导数没有作为任意候选输入。

## 紧支 Lipschitz 的完整 H¹

`CompactLipschitzSobolev` 对任意实际全空间 Lipschitz、紧支实函数，直接证明其真实 fderiv 的 CLM 值 L² 存在：fderiv Borel 可测，逐点范数受 Lipschitz 常数界控制，在原 tsupport 外为零；以有限体积紧集的常数 indicator 控制，避免假设全空间测度有限。

实际标量与 fderiv 的 toLp 类均有 a.e. 身份。固定 mathlib 的真正 Rademacher 定理给 a.e. DifferentiableAt；与 fderivLp 的 a.e. 身份结合供应已证 Lipschitz 积分分部构造，从而得到原完整 WeakSobolevJet d 1 volume univ。value 精确恢复原 f 的实际 L² 类。没有将 a.e. 经典可微直接当作分布可微，也没有外加目标弱导数恒等式。

## 实际节点函数实例

`ContractedNodalSobolev` 证明 dilation 的 Lipschitz 常数为 |r|，其逆的常数为 |r⁻¹|，所以内缩复合的常数为 C|r⁻¹|。由真实紧支 Lipschitz 构造为该具体内缩函数供应完整 H¹ jet，并以 a.e. 身份识别 value。

节点函数的 tsupport⊆closure S 由原定义在 closure S 外为零直接证明；有限单元给紧支。凸域内缩的缓冲定理因此直接适用。边界节点零、FaceMatching、BoundaryFitted、开集条件给已经证明的实际全局 Lipschitz；据此构造 nodalContractedSobolevJet，其 value 就是对同一个原 nodalFunction 的真实内缩，不是任意重构或近似占位。

支撑缓冲的几何部分不要求 f 边界节点零；只有 H¹ 构造使用这些边界条件来供应全局 Lipschitz。a∈S 明确排除了空域的中心选择，未声称总能从空域选中心；后续完整节点 H¹₀ 证明应单独处理空域零函数。

## 尚待完成

还需证明 r→1 时内缩函数在 H¹ 中回到原节点函数，并在上述正缓冲内用光滑卷积证明 H¹ 收敛。只有这两项真正完成后，才能把 nodalLp 放入此前定义的 H¹₀ 闭包。当前构造不能直接充当闭包成员证明；H² 正则性/点值代表、具体网格和数值误差、原连续热 CE 也仍待。
