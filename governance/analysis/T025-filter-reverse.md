# T025 — 原 Lemma 7.4：终端子空间的反向范数界

原命题为 `lem:filter-reverse`（2164 行起），证明位于 `sec:filter-reverse-proof`（2962 行起）。最终入口 `Physical.filter_reverse` 在原物理时间真实 Hilbert 伴随方程下证明

`‖p^N‖≤exp(T Λ_F+MT+M²T²/2)‖p^0‖`。

F 是任意终端子空间，只要求 p^N∈F；A 和各步势均不要求保持 F。原正步长、dt M≤1/2、A 非负自伴和 V 自伴范数≤M 输入保留。原子节的其它可观测性/尺度条件未用于该引理，省略它们扩大适用范围。

## 真实单步 Rayleigh 增长

`rayleigh A x=⟨Ax,x⟩/‖x‖²`。先对 ‖z‖=1，定义原 r、b、v、w、ξ、γ，逐项证明正交、‖w‖²≤M²、2γ−dt r≥1 和 ‖x‖²=γ²+dt²‖ξ‖²。用真实非负平方 ‖ξ−γw‖² 配方，直接得到

`r‖x‖²≤⟨Ax,x⟩+dt M²‖x‖²`。

这等价于原证明在 dt M≤1/2 后的最终单步界，无需保留中间更精确分母。归一化由真实非零标量乘法的不变性 `rayleigh_smul` 完成，单步范数下界保证分母非零，从而所有非零 z 都有 `ν(z)≤ν(step z)+dt M²`。没有将此界作为输入。

## 正算子逆界

`positive_form_cauchy` 从 B 的真实非负二次型和对称性，对 t↦⟨B(tx+y),tx+y⟩ 用二次判别式证明 Cauchy–Schwarz。对 B=Id+dt A 和 By=x，结合普通 Hilbert Cauchy–Schwarz得

`‖x‖≤(1+dt ν(x))‖y‖`。

此处等价于原谱下界，但证明无需选特征向量。对扰动步构造实际 S0=(Id+dt A)⁻¹；由 S0 收缩得到 `‖S0x‖≤(1+dt M)‖z‖`，于是

`‖x‖≤(1+dt M)(1+dt ν(x))‖z‖`。

关键使用 incoming x 的 Rayleigh 商，与原证明一致；未使用后向状态的更强假定或全算子范数。

## 真实时间迭代和终端 F

原伴随解非零终值保证所有节点非零。单步商增长证明 `ν(p^n)≤ν(p^N)+(N−n)dt M²`。对真实范数递推用 `1+x≤exp(x)`，累积指数

`F(n)=dt(M+ν(p^N))n+(dt²M²/2)n(2N−n−1)`。

真实 Fin N 步的指数增量与上述 Rayleigh 界完全相符；Fin.induction 得 ‖p^N‖≤exp(F(N))‖p^0‖，而 F(N)≤Tν(p^N)+MT+M²T²/2。零终值单独处理。无需对数中非零因子或对数和的额外假设。

`filterRayleigh A F` 是原非零 F 内 Rayleigh 值集合的真实 sSup，F=⊥ 明确定义为0。真实有界算子的 ν(x)≤‖A‖ 仅用于证明该集合有上界，以合法使用 le_csSup；最终估计常数里没有 ‖A‖。对 p^N∈F 且非零，实际证明 ν(p^N)≤Λ_F。最终方程通过已经验收的原 AdjointEquation 与自伴性的 iff 接入。

四模块19项声明；正式完成须由固定版本真实 CI 和独立 Agent 验收，本文档不代替验收。
