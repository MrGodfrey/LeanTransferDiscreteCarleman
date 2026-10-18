# T020 — Lemma 4.1 的完整空间误差

本机 main 接续基线 `d9b74c1fee306a7bf33a820d600af09af6319e0e`；此前 main CI39133840999 的三个任务实际通过。原稿未改。新增八模块、36 个显式声明，代码与原假设映射见[逐项核对](../reviews/T020-spatial-complete.md)。

`OriginalForm.spatial_uniform` 是完整原 Lemma 4.1 的入口。由原有界 Lipschitz 域、原闭 V/对称强制形式、正向 A1 椭圆界、内禀闭包光滑 profile 出发，内部调用已证 `OriginalForm.section3`。输出先选择 `Lmin, δt`，对每个固定 L≥Lmin 再选择 `δx≤δnum, ηstar, K>0`，随后才量化离散 Hilbert 空间 X、R/J/A/缺陷、周期网格、时间方向、q、允许指数和 profile 符号、网格尺度与误差参数、载荷和全状态。所有最终常数独立于 T、节点数、qmax 和离散化。

## 原假设与能量证明

`WeightedApproximation` 只有原 N3 的逐时刻 Nm/R₂ₘ 及 L²/R₂ₘ 两个界。`WeightedTest` 只记录原 N4 所需的算子、导数、周期端点、自伴/非负、真实二次型时间导数及超逼近；原正定性足以给非负性，未使用的范数等价不成为额外限制。超逼近仍是 `Csuper*h*qmax`。对任意保持 V 的证明量化只涉及证明无关性，不扩大测试权族。

由此前真实节点提升，`Nσ(u−Qu)≤aE Rσ(u)`、`Nσ(Qu)≤(m+1+aE)Rσ(u)`。安全的 m+1 固定因子来自已证 jet 截断，不是 T 或 qmax 因子。Céa 给能量率和状态稳定性后，原 Euler 图界实际替换 Rσ(u) 为载荷范数。

σ² 的正/逆乘法常数在两个 profile 符号上取 max。形式上界由 Section3.form_bound 提供；质量余量选 `B=18*Ctime+1`，由 Section3.form_coercive 提供。阈值函数实际证明 `ε=Csuper*h*qmax≤1` 和 `Cf*ε+ηA*(ε+CM)≤c/2`；不把吸收条件、形式界或目标估计作为最终新假设。时间阈值同时进入原 Euler 和单元比较范围。

## 完整逆权对偶

`l2_estimate_of_energy` 用 Section3 的存在性构造真实对偶域序列 Y：反向 Euler 方程的载荷是两次 σ 乘法作用于 `u−Rz`。采用逆权后，载荷恰好化为 σ(u−Rz)，不要求 σ² 属于允许权族。

`spatial_duality_bound` 调用此前从两真实方程推导的完整三项恒等式。实际加权配对 Cauchy–Schwarz、N3 逆权 L² 逼近、N3 逆权能量逼近和 N1 缺陷分别给

`‖σe_s‖² ≤ [a0 ‖σD_su‖ + Cf*aE*Nσ(e_s) + ηA*(m+1+aE)*Nσ(Rz)] Rσ逆(Y)`。

接入已证能量/状态稳定性和正、逆 Euler 图界，使用 `aE≤1` 控制 `aE*ηA≤ηA`，零误差范数分支单独处理，得到

`‖σe_s‖ ≤ (Kg+Cf*Ke+Ke*(m+2))*Kg*(a0+aE²+ηA)*‖σf‖`。

能量和 L² 入口取同一个较大 K。两方向均直接使用准确的周期相反伴随；未假设 Q²=Q、G=Id、正交重构、核限制或导数域保持。

## 验证与剩余工作

八模块和根目标已在本机实际构建；完整 3445 build jobs，3080 个 Carleman 声明递归公理检查通过。36 个显式声明逐一输出类型和公理，仅正常基础公理。精确源码 SHA 和 main CI 在实际运行成功后绑定唯一台账。

C008/P009 在核实同 SHA CI 后可登记 BUILT/PAPER；执行者核对不冒充独立语义验收，原文完成计数仍 1/26。Theorem4.2 的空间—时间合成、最终 B4 范数/权族桥及 Theorem2.1 未完成。下一步在真实弱轨迹误差上组合时间两种率、空间误差及两方向单元延拓比较，不能把它们重新作为最终 transfer 假设。
