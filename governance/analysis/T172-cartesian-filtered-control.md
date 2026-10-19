# T172 / C188：互补终端惩罚、实际 HUM 与完整 Cartesian 滤波控制

六模块二十项显式声明。此阶段沿原文 `cor:filtered-control` 及附录互补惩罚证明，构造实际控制和完整正向轨道，不以抽象最优性替代控制结论。

`ComplementaryHUM` 构造真实算子 O*O+η²P(F⊥)，证明其精确配对身份。互补观测及 R 的单射性给零核，有限维性给满射，故真实 Euler 方程有唯一解 z。取 u=−Oz；精确身份 R*y+O*u=η²P(F⊥)z 给 PF 终态为零，能量配对给控制和完整残差范数界。这里 R/O 均为真正连续线性映射和 Hilbert 伴随。

`ComplementaryObservation` 使用正交 Pythagoras、R 的算子范数界 L 和仅在 F 上的反向界 K，证明 ‖z‖²≤2K²‖Rz‖²+(1+2L²K²)‖P(F⊥)z‖²。原松弛观测与 4C0ε²K²≤1 预算给系数 2C0 的互补观测，惩罚精确为 η=εsqrt(1+2L²K²)。不要求 R、A 或时间势保持 F。

`PhysicalComplementaryHUM` 把实际物理时间的 initialMap/observationMap、sqrt(dt) 控制向量、正向解存在和终态对偶身份接起来，得到原 ForwardEquation、初态身份、真实 controlNorm、PF yN=0 及完整终态界。`FilteredControl` 内部调用实际 forward/backward 流、initialMap_bound 和 filter_reverse；其通用版本明确保留松弛观测前提，F 任意。

`FilterPenaltyBound` 证明实际非负 A 的 Rayleigh 上确界非负（包括 F=⊥），原反向常数 K≥1，并用 TΛ≤θdS 给互补惩罚指数 exp(-(1−θ)dS)。额外因子是仅依赖 T/M 的

`factor(T,M)=sqrt(1+2exp(2MT)^2) exp(MT+M²T²/2)`。

为使原终态 prefactor 与同一个观察常数一致，完整 Cartesian 定理在 T/M 之后、全部网格/势/θ/F 之前选择 `C0=max(1,max(C,2factor²))`。松弛观测常数可以单调增大到此 C0；sqrt(2C0)factor≤C0 精确清偿因子。因此原两个滤波条件使用的就是这个同一 C0，最终成本 sqrt(2C0)‖y0‖，PF yN=0，完整终态≤C0 exp(-(1−θ)d0S)‖y0‖；没有额外网格依赖常数或额外滤波条件。

`BoxCartesianFilteredControl` 内部调用 T170 真实物理观测，原完整物理节点空间、原 Laplacian、任意有界节点势、原控制零延拓、实际物理时间递推均保持。原 S=κmin(h^(-4/5),dt^(-2/5)) 与原两侧物理网格条件不变。qc/κ/h0/Δ0/Cb/d0 在 T/M 之前，C0(T,M) 在全部网格和 F 之前。结论事实上对满足列出预算的任意实 θ 成立，包含原 0<θ<1。

仍为完整盒 Cartesian 辅助实例，未完成一般几何/P1；AUXILIARY，原文17/26。六模块均已根导入，二十项声明均显式检查类型和公理；定向最终3998 jobs，根目标4105 jobs，全部8135项Carleman声明递归公理审计PASS。固定raw2562137 bytes，SHA256 76e24372f62d67b3ac0cd66e5afd4501cd9b07913ec58f0939fad41d1080109f。同SHA正式CI及独立验收另行登记。
