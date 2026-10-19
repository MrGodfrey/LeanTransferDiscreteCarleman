# T126：原 L²(ω) 控制的完整 P1 数值数据

本阶段将已清偿的全 P1 加权投影误差 N3 和真实 Π_h(σ²z) 加权测试 N4，与原 conforming 一致质量 Galerkin 数据组合。控制空间保持实际 L²(ω)，B_h* 是原状态在 ω 的真实限制，观测仍为 ω₀⊆ω；未把控制改为全域 L² 或任意有限维代理。

`ConformingRegionWeightedData` 证明真实受限权乘子和限制 Lp 的平方范数等于 ∫ω σ²|u|²。非负真实可积密度在 ω₀⊆ω 下的积分单调性给观测界，常数恰为1。组装函数使用实际 inclusion 重构、正交投影负载、Galerkin 刚度和零缺陷，原 N1/N2/N5 精确成立；此通用组装层的 N3/N4 由下一个具体定理供应。原控制算子的伴随及配对已由 ConformingRegionControl 真实证明，未重新假设。

`FullP1NumericalData` 的常数 δ>0、Ctime>0、Csuper>0、Capp>0 在全部网格、状态、TimeWeight、时间网格之前统一选取。δ 是实际 N3/N4 阈值的最小值，δ≤1。全部原形状正则、尺度上下比较、相邻顶点 grading γ<Γ_d 的网格，所有允许 time weights 和 |τ|≤τStar、两种空间权符号同时成立。原完整 conforming P1 空间、原 boundedDirichletOriginalForm 和实际弱 Sobolev jets 均保留。误差为 a_E=Capp h、a₀=Capp h²、η_A=0，h 为实际最大单元直径。

原算子域到 H² 的包含 hD 仍显式保留为原 A1 输入，尚未宣称具体凸多面体上的 Dirichlet H² 正则性已证。连续 Carleman 估计也不属于本定理。因此这是原空间数值接口 N1–N5 的 AUXILIARY 组装，不提升 P011 或其他原文计数，覆盖仍为14/26。

两模块5显式声明，定向3724 jobs、全库3889 jobs通过；6782声明递归公理审计PASS。固定产物 `/tmp/carleman-p1-numerical-local-axioms.txt` 为2081313 bytes，SHA256 `58f0f1235c93292ca05aa2a345b4fa18aaf03178401c7a6428dc5902431d7e12`。原稿未改。
