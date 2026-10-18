# T020 — 真实加权时间下界与空间 Céa 估计

本阶段直接在本机 main 接续，基线 `7f17beb74fbc260084d425126cc719187b0caaac`。
用户已明确授权验证后 commit、push；不新增常规 PR。论文源码保持原版本。

## 证明链

`WeightedTestTime` 从原 N4 的二次型导数界出发。单元内 q 的比较常数为 2，实际 σ 的 L² 乘子比较常数为 3，故 qσ 重构质量范数的比较常数为 6。导数界变成节点质量平方的 36C 倍，精确周期恒等式中的 1/2 给出

`pairing(D± e, T e) ≥ −18C dt ∑ (q_n ‖σ_n R e_n‖)²`。

D+ 使用节点后的单元，D− 使用节点前的单元和未取模右端点。最后单元的 q、σ、测试算子分别通过真实周期端点身份处理。常数不依赖 T、qmax 或节点数；时间阈值仍是既有 cell comparison 的显式条件。

`SpatialCea` 对精确误差方程逐节点测试，并保留质量余量、测试缺陷和刚度缺陷。令 p=Nσ、q=Nσ逆，M=σ²，N4 superapproximation 系数为 ε，乘法常数为 CM，则逆权测试稳定性常数 Ct=ε+CM。由真实有限和的 Cauchy–Schwarz，若

`Cf ε + ηA Ct ≤ c/2`，

则

`Nσ,dt(R e_h) ≤ (2/c) Ct [Cf Nσ,dt(u−Qu) + ηA Nσ,dt(Qu)]`。

证明显式相消 A3 的质量余量与时间负项，零误差范数单独处理后再除以范数。没有将误差估计作为输入，也没有 Q²=Q、G=Id、正交重构或频率限制。

`SquaredWeightTest` 利用原内禀 SmoothOnClosure ρ 和 V 的正/逆权保持，证明真正的
`Nσ逆(σ²v) ≤ CM Nσ(v)`，CM 统一先于 w、τ、t 和 v。两次既有共轭比较给 CM=J²；不扩大允许指数范围，也不假设外邻域光滑延拓。

`Section4.spatial_cea` 将上述结论实例化到原弱 Sobolev 范数、实际 R/J/G、原连续变分 Euler 方程和全离散 Euler 方程。时间负项在定理内部由 N4 导数界证明，误差方程也在内部由两真实方程相减得到。输入的 hform/hcoer 是 Section3 已证的形式结论；hmul 由上面的统一乘法定理供应。`OriginalForm.bilinearForm_apply` 证明这里的线性映射形式与原 scalarForm 完全相同。

`SeminormSum` 和 `NodalApproximation` 将逐节点 N3 界提升为 Section3 的真实 `nodeParameterNorm`，即各弱导数字段的时间 L² 范数之和。Minkowski 不产生节点数或周期因子。低阶 Nm 与高阶 Rn 的比较经原值映射唯一性识别 jets；当前使用安全的固定常数 m+1（m≤n、q≥1），该常数不影响 T 一致性。

## 边界与下一步

C039 是 AUXILIARY，17 个显式声明、6 个模块。本阶段不是完整 Lemma4.1，覆盖表不提升。
尚需把 N3 序列界、原 Euler R 图界和 Céa 估计组合为 `aE+ηA` 的最终误差及状态稳定性；把 ε=Csuper hqmax 和 ηA 的小性统一选成原阈值，不能把 hsmall 当作新的原假设。

随后从 Section3 构造反向、逆权的原对偶解，在已有完整三项恒等式中分别接入 L² 逼近、能量逼近和刚度缺陷，得到 `a0+aE²+ηA`；最后组合时间误差和延拓得到 Theorem4.2/B4，再实例化原 Theorem2.1。hform、hcoer、hmul 的现有独立供应定理需在最终入口实际调用，不得仅将它们列为未清偿前提后提升原文完成状态。
