# T015 真实加权时间分析与剩余交换子

本阶段以已合并 `9f8e351a71cbcd8943db0d9056afdd2bc0a1ffe7` 为基线。T014 的全空间插值及原域扩张检查点保持有效；本阶段不假定或宣称原域扩张完成。

## 已打通的数学链

- `TimeL2Multiplier`：实际空间乘子 σ(t) 在 Bochner 时间 L² 类上的线性作用、代表等式、逆权配对和 σ² 载荷恒等式。全局指数界只用于连续性/有限性，不进入统一误差常数。
- `AffineSeminorm` / `WeightedAffineDefect`：对所有节点状态和两种半开延拓，缺陷恰为一个绝对值不超过 dt 的标量乘真实离散差分延拓。由同一时刻乘子和已有单元比较推出 `‖σ(hat u−bar u)‖ ≤ 3 dt ‖σ_nodes Dεu‖grid`。函数层 MemLp 已证明，不使用总化积分伪造有限性。对应原稿 `eq:timedelta` 的第一段；第二段仍依赖允许权 Euler 图估计。
- `WeightedTemporalDuality`：对任意非负节点 μ 和任意真实节点载荷构造连续解、Euler 解与反向伴随解；伴随载荷为实际两次乘法 σ(σe)，不要求将允许权族扩大到 2τ/2ρ。证明 `‖σe‖²=−ε〈σδ,σ⁻¹Y_t〉` 及带真实网格差分、伴随导数范数的界。对应 `eq:temporal-dual-equation`, `eq:timecancellation`。不假定伴随存在或最终误差。
- `FrozenTemporalPerturbation`：给定任意 η>0，在选择 L₀/δ 后，对所有 T、网格、方向、权、|τ|≤τStar 和时间 L² 状态，实际对数时间导数项 ≤η‖barμ v‖。仅用原 q≥1、m>0、冻结单元下界；从不微分阶梯 barμ。
- `WeightedGraphRemainder` / `WeightedGraphConstruction`：对真实冻结问题，先由 A1/A2 构造加权弱图代表，再吸收上述时间项，得到
  `‖σU_t‖+‖σAU‖+‖barμ σU‖ ≤30(‖σ(εU_t+AU+barμ U)‖+‖A(σU)−σAU‖)`。
  时间方程方向和冻结延拓方向可独立选择。该估计没有假定目标图界；A1 的 Sobolev 正则性只沿 `‖u‖Hⁿ≤Creg‖Au‖` 使用。图代表保留实际 H 弱导数、周期 H 迹及 a.e. D(A) 正规性。
- `WeightedGraphCommutator`：上式差值在 a.e. 代表上恰为 `allowedCommutatorPath`，即原 A2 的 `[A,σ]σ⁻¹` 作用于加权状态；不是一个未经匹配的余项标量。
- `WeightedAdjointRemainder`：构造载荷 W(W e) 的实际反向伴随 Y，取 M=W⁻¹，构造 Z=MY 后，得到 `‖M Y_t‖≤30(‖W e‖+‖AZ−MAY‖)`，并证明余项与原 A2 路径 a.e. 相等。因此时间扰动已清偿，空间交换子仍明确保留。

## 仍未清偿，不能记原文完成

1. 原 bounded Lipschitz Ω 上，同一高阶弱扩张同时 L²/Hⁿ 有界并保持实际弱字段限制；或原域等价局部插值证明。T014 全空间结果不等于此接口。
2. 将原 A2 `C/L · R` 与原域参数图控制结合以吸收真实空间交换子，得到闭合的允许权连续/frozen R 图界。本阶段的“30”估计仍有该项，不能代替 `eq:frozengraph`。
3. 完整允许权 Euler 图估计及其真实节点权时间交换子控制。无权 Euler 结果和加权仿射缺陷不足以代替 `eq:eulerMR`。
4. 上述两项闭合后，才能将实际对偶界闭合为 Theorem 3.5 的 O(dt) 加权 L²。T014 冻结误差能量可复用以得 O(sqrt(dt)) N 误差；空间 Theorem 4.2/B4 仍待。

本阶段保留原论文、最终结论、两方向、全状态和 T 统一性；范围 AUXILIARY，原文完成仍 1/26。几何输入沿既有光滑邻域/内在闭包接口衔接，不将其作为新的原定理限制。

## 工程验证范围

CI 快照新增 workflow-context 的精确 expected-ci-url 核对；仅该地址临时进入展示白名单，checked SHA 仍须一致，台账源数据及 supervisor_checked_at 不变。回归覆盖当前 run/attempt 展示、错 run/外域/路径/查询拒绝、自授权拒绝、输入不变和任务时间不变。该检查只绑定同一运行，不自行宣称 GitHub 实际成功；交付另读运行、日志和产物。
