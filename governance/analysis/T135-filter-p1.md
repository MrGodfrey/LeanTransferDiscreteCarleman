# T135：原 Proposition 7.7 的 P1 粗网格 Rayleigh 界

本阶段目标是原文 `prop:filter-p1`（P019），不是连续 H² 正则性的替代命题。该结果仅依赖真实粗空间逆估计、一致 L² 质量与 Dirichlet Galerkin 刚度，独立于尚待完成的连续 CE 和具体 H² 算子域正则性。

`ConformingUniformInverse` 从非空域的实际单纯形覆盖及正维非退化顶点证明真正最大粗单元直径 Hc>0。实际逐单元逆网格乘子在 a.e. 唯一所属单元上等于 Hc⁻¹，故其真实 L² 乘法范数≤Hc⁻¹‖u‖。将已证明的全 conforming P1 加权逆估计用于权1、局部尺度Hc，形状界 diam(K)≤κrK 与准一致界 Hc≤Q diam(K) 内部供应 Hc≤QκrK，得到全部粗状态的真实梯度界 ‖∇u‖≤(C/Hc)‖u‖。C 仅由 d、κ、Q 决定，先于域、网格和状态。

`FilterRayleighBound` 操作已经用于 Lemma 7.4 的原 `filterRayleigh` 定义，即非零保留子空间上实际 Rayleigh 商的实数 supremum，零空间明定为0。给定实际能量界，其 supremum 上界内部证明；非零子空间提供非空性，非零向量范数平方严格正，零空间分支单独处理。

`ConformingFilterRayleigh` 定义实际粗空间包含映射的 range 作为细状态空间内 F。它不是新的候选保留空间，嵌套前提正是原 V_H⊆V_h。`dirichlet_galerkin_energy` 用原 Galerkin form 身份和实际 Dirichlet scalarForm 识别得到 (A_hv,v)=‖∇v‖²，质量范数是原 L² 子空间继承范数。任意 F 中向量均恢复真实粗状态，通过同一个原 H¹ jet 值单射识别其实际梯度；全粗空间逆估计平方并取 supremum，给 Λ_F≤C/Hc²。

最终 `p1_coarse_filter_rayleigh` 直接量化两个实际完整 conforming P1 空间，细刚度是 `galerkinStiffness (boundedDirichletOriginalForm ...)`，F 为粗空间包含映射实际像，Hc 为粗网格实际 maxDiameter。C 在所有粗/细网格、域和状态之前，只依赖维数及粗形状、准一致界；无细网格尺度或规则性常数，没有要求细算子保持 F。原 d=2,3 的凸多面体由更广的任意正维有界开凸域结论覆盖。域非空、正维、正形状常数是原网格设定；有限体积由有界性保证。未输入逆估计、目标Rayleigh界、H²正则或连续CE。

三模块8声明，定向3544 jobs、全库3932 jobs通过；6989声明递归公理审计PASS。固定 `/tmp/carleman-t135-filter-p1-local-axioms.txt` 为2147555 bytes，SHA256 `690b28457d73c9b0f025ae6c29901636d674ef65961194ac73f2a2c31eb989d3`。

申请独立 PAPER 验收完整 P019 / Proposition7.7。验收与同SHA正式CI完成前仍为14/26；若确认完整原量词及实际对象，可升至15/26，P011/P023及其他未完成项不自动提升。下一步为原 Cartesian 粗网格张量线性插值的12∑Hr⁻²界。
