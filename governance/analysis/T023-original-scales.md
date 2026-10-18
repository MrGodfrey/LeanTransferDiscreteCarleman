# T023 — 原 Corollaries 2.2–2.3 的完整尺度推论

目标为 `paper/main.tex` 的 `cor:general-scales` 与 `cor:scales`。最终入口是 `OriginalForm.scale_uniform` 和 `OriginalForm.heat_scale_uniform`；返回含原载荷与稳定右逆残差两版完整估计的 `Section5.ScaleUniform`。二者内部调用已验收的原 Theorem 2.1，不把 TransferUniform、小量条件或缺陷控制作为最终输入。

原稿保持不变。原近似阶为 aE≤Cap·h^m 和 a0+ηA≤Cap·h^(2m)，Cap 是先于 h、网格、数值空间的统一非负常数。h>0 是原网格参数；h0、Δ0≤1 是所选阈值，不是新增限制。κ、h0、Δ0、Cfinal 先于所有数值空间、时间网格（含 T）、权、方向、载荷和状态。解析与数值假设沿用 T022 同一原始输入。

## 指数与小量

`nuEnergy=max(dStar,max(4m+dStar−c0,0))`、`nuL2=max(bStar,max(4m+bStar−c0,0))` 与原三项最大值相同。`omittedRatio` 在分母为零时返回外层 cap（空间为1、时间为1/2），从已有 cap 的 minimum 中省略这一项。nuEnergy≥0、nuL2>0；后一结论来自原 c0>0 与 bStar≥c0。未以 Lean 的除零值代替省略规则。

`scale_bounds` 证明原四项指数预算及两项 cap。`scale_monomial_le` 对正 x≤1 证明：若 Q≤κ x^(−α) 且 αν≤p，则 x^p Q^ν≤κ^ν。`approximation_rates` 从原近似阶证明

- εE²≤M(h^(2m)+dt)；
- ε0²≤M(h^(4m)+dt²)，

其中 M=8Cap²+2(Cap+Cap²)²+2>0，保留 ηA、aE² 与 sqrt(dt)。`defects_le_budget` 将原两个缺陷都控制于 εE²Q^nuEnergy+ε0²Q^nuL2。

`exists_scale_smallness` 选 ε=min(1,cStar)/(4M)。正指数项由 κ 控制；nuEnergy=0 时，其空间/时间项直接由 h0/Δ0 控制，因此不存在通过 κ^0 变小的错误。再缩小 h0 保证 aE≤1、ηA≤ηstar，取 κ≤δx、κ²≤δt 保证 hQ≤δx、dt Q²≤δt。四个预算单项分别≤ε，最终两个缺陷分别≤1、cStar。没有新增 h/dt 耦合条件。

## 原结论

`scale_uniform_of_transfer` 将上述六项小量逐项代入真实 TransferUniform，保留所有原数值数据、真实空间能量及载荷/观测/残差范数。中间声明接受 TransferUniform 仅作复用；`OriginalForm.scale_uniform` 内部提供已证明的 `a.transfer_uniform`，没有剩余 transfer 前提。

`CarlemanExponents.heat` 正好为 m=1、(c0,c1;o)=(3,1;3)。`heat_scale_exponents` 经 kernel 检查计算 dStar=1、bStar=4、nuEnergy=2、nuL2=5、alphaX=4/5、alphaT=2/5。`OriginalForm.heat_scale_uniform` 用这些等式改写完整 ScaleUniform 结论，不只证明数字恒等式。原允许指数覆盖条件仍由相同 heat 数据明确给出。

## 验收

七个新模块、23 项显式声明，全部由 root 导入并加入实际类型与递归公理审计。最终完成状态必须等待固定提交的真实 main CI 与独立 Agent 原命题验收；本说明不是验收报告。具体声明见任务 T023 的唯一台账。
