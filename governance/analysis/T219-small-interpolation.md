# T219 — 真实低阶参数项的任意小常数插值

基线 `b41b6861b988e758d026fed32f5d5802e411b636`。原稿 `paper/main.tex:286` 的固定有界 Lipschitz 域及 `2637–2650` 的 η 插值步骤。1模块9显式声明（8定理、1定义）；AUXILIARY、17/26。

定义 lowerParameterNorm 为全部 k<m 的 q^{m-k}‖D^ku‖ 之和，完整场范数仍是每阶所有无序多重指标的真实 L² 平方和。先证明 R≥1 时 R lower(q)≤parameterNorm(Rq)：每个严格低阶至少给出一个 R 因子。由已验收、已构造的有界 Lipschitz 原域参数插值，选择 R≥C/η 得到任意 η>0 的 lower(q)≤η‖u‖+Cη q^m‖u‖L²。Cη 在 q≥1 和全部原弱射流之前固定。

同时利用 parameterNorm(q)≤parameterNorm(Rq)，得到 R lower(q)parameterNorm(q)≤parameterNorm(Rq)²。再由真实插值、(a+b)²≤2(a²+b²)，选择 R≥2I²/η，得 lower(q)parameterNorm(q)≤η‖u‖²+Cη(q^m‖u‖L²)²。没有把任意小常数插值当作输入。

对原文 r+s<2m 的双和，完整分拆为 r<m 的所有 s≤m，加 r=m、s<m 的剩余项；确切 q^{2m-r-s} 与两个缩放因子相同，故双和≤2 lower(q)parameterNorm(q)。使用 η/2 得原二次估计。最后证明原弱射流积范数≤真实 Sobolev Hilbert 范数（每个场的平方均包含于全部场平方和），将结论提升到实际 H^m 范数；没有错误地把两范数视为相等。原文在 H₀ᵐ 上的使用是其自然子空间限制。

所有阶 m≥0、任意有限维、零状态均覆盖；原 m≥1 是子范围。域的有界 Lipschitz 假设来自全篇设置，未添加扩张算子、目标插值界或光滑状态条件。本批未声称实际系数形式的共轭误差已经由该双和控制；下一阶段仍须证明真实 Leibniz 非主项与共轭形式差界，随后才可与原 coercivity 合并。
