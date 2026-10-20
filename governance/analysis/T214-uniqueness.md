# T214 — 同一原数据的连续能量解唯一性

固定基线 `a7ffa08f871d033a1729d80f998b56c5e98d6218`；三模块六定理。原文 `paper/main.tex:2338–2415` 的能量解识别基础；AUXILIARY、17/26。

连续非负 Volterra 引理从 f(t)≤C∫₀ᵗf、C≥0推出整个闭区间 f=0。真实连续夹持延拓仅用于把原积分原函数交给 mathlib 已证 Grönwall；原函数在原区间上的导数与积分均与 f 相同，不要求 f 可微。实际部分时间截断范数严格等于真实代表 q 的局部平方范数积分，仍只使用 a.e. 相等及 Lebesgue 限制测度身份。

`dirichlet_mass_energy_zero` 输入同一原 b、真实 Y∈L²H¹₀、原质量弱时间导数 (MY)'=D(b,Y,0)、真实 H 连续代表 q=EY a.e. 与 q(0)=0。它不要求 q(T)=0，也不假设 Y 具有 V 值强时间导数。T212 的真实逐时能量等式和 T213 的原局部载荷界，内部给 ‖q(t)‖²≤2b.bound∫₀ᵗ‖q(s)‖²。Volterra 引理推出每个时刻 q=0；真实值嵌入注入和 Lp a.e. 身份再给 Y=0。

实际载荷对状态与控制差线性，证明中保留同一 b，不改变势。两个原能量解相减后，由真实 weak derivative 的减法、原 Lp 差的 a.e. 代表及载荷差身份得到零控制方程；相同初迹给零初值。`dirichlet_mass_energy_unique` 因而对同一 b/U 的任意两状态与真实连续代表给 Y=Z、整个闭区间 q=r，无终态或有限测试身份输入。

`FiniteDirichletControlIdentity.identifies_energy_solution` 将已构造的控制极限与任何同一原势/控制/初值的质量弱能量解 Z 比较，内部取得前者的连续初终迹，推出 Y=Z 且后者真实终迹 r(T)=0。比较解不被要求预先具有零终态；这清偿“该能量解到零”中的唯一性，而非仅在零终态解集合内比较。实际 StrongDual 与质量表述的完整互换及最终原定义封装可在后续整合；一般多面体 Carleman 实现仍未完成。
