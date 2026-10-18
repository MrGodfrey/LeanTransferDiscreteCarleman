# T021 — Theorem 4.2 的真实空间—时间合成

基线是已核实 main CI39135593975 的 `a315bdc449c58a705a982f0d009f1dde24d6af66`。Section3/Lemma4.1 的独立验收由本机 Agent 同时处理，不以执行者自检替代。

本阶段四模块、13 显式声明，入口 `OriginalForm.combined_uniform` 对应原 `thm:combined`。原稿和原误差尺度不改。`CombinedEstimate` 量化每个实际冻结连续图解 p 和全离散解 z，同一个任意节点载荷 f；中间空间连续 Euler 解 u 由 Section3 存在性在证明内构造。

## 真实范数与误差代表

`reconstructedError` 是 `inclusion(U.domainValue)−R(extension z)` 的 V 值代表。`reconstructedError_value_ae` 证明它在 H 中几乎处处就是原 `U−R bar z`；原 U 仍只需 a.e. D(A)、H 弱导数与周期迹。`reconstructedError_decomposition` 是实际 V 中的

`full error = inclusion(U.domainError u) + extension(inclusion u−Rz)`。

线性 weak jet 映射给实际导数字段的同一分解。第一项的 MemLp 来自 Section3.TemporalEstimate，第二项来自有限序列的真实两方向单元延拓；因此完整误差 jet 的 MemLp 是结论而不是新假设。

`spacetimeWeightedNorm_add_le` 用每阶真正 Bochner L² 三角不等式及有限 Cauchy–Schwarz证明 Nm 时空范数的精确三角不等式，逐字段 MemLp 显式。`spacetimeWeightedNorm_congr_ae` 保证代表无关；没有用总化 L² 范数掩盖无穷值。

`spacetimeWeightedNorm_extension_le` 将各阶弱导数字段的 `q^(m−k)σ` 密度调用既有真实单元比较，平方界常数9，平方根界常数3。积分有限性由真实 jet MemLp 和有界权乘子得到。两个方向直接调用带周期端点的单元延拓。解析阈值使用 `cellThreshold β (τStar+m) ρ.bound` 来覆盖有限的 q 幂；这仅用于解析权函数比较，N1/N3/N4 和 A2/A3 仍只在原 `|τ|≤τStar` 权族取值，没有扩大数值允许权族。

## 原最终率与统一量词

中间 u 同时进入已有 TemporalEstimate 和 Lemma4.1。能量三角给

`Nσ(U−Rbar z) ≤ Kt sqrt(dt) F + 3 Ks (aE+ηA) F`，

真实 H 值分解及 Bochner L² 三角给

`‖σ(U−Rbar z)‖ ≤ Kt dt F + 3 Ks (a0+aE²+ηA) F`，

其中 F 是原节点载荷加权范数。选共同常数 `Kt+3 Ks`，得到原 `εE=sqrt(dt)+aE+ηA` 和 `ε0=dt+a0+aE²+ηA`。

`combined_uniform_of_section3` 在空间阈值、Section3 阈值和新的解析单元阈值之间取 min，Lmin 取 max。`OriginalForm.combined_uniform` 内部调用原 A1 的 `section3`，最终所有常数先于 T/grid/qmax/X/R/J/A/方向/符号/全状态与载荷；固定 L 后允许常数依赖 L。不存在新增最终误差、图界、中间解、可积性或正交性前提。

## 本地检查与范围

四模块和 root 全库实际构建通过：3449 build jobs，3125 个 Carleman 声明递归公理检查 PASS，仅正常基础公理；13 个新增显式声明全部输出类型和依赖。公理报告 SHA256 `9b156ce390cd022093946babb6f0aeb2fec8312682c870375c0753838aeb2c75`。同 SHA main CI 尚待实际绑定，独立 Agent 对原命题的验收将在版本固定后启动。

本阶段完成 Theorem4.2 的候选声明，不宣称原 Theorem2.1 已完成。下一阶段仍需把这些真实空间—时间误差及已证比较、载荷、观测接口构造成最终统一 TransferBridges，实际消去条件性 Section5 的剩余桥接前提。

## 13 项声明的执行者映射

| 声明（Carleman. 前缀） | 作用 |
| --- | --- |
| WeakSobolevJet.parameterTimeField_add | 真正缩放加权弱导数字段的线性。 |
| WeakSobolevJet.spacetimeWeightedNorm_add_le | 显式 MemLp 下真实 Nm 的时空三角。 |
| WeakSobolevJet.spacetimeWeightedNorm_congr_ae | 弱代表无关。 |
| WeakSobolevJet.spacetimeWeightedNorm_extension_le | 两方向、所有弱 jets 的节点到时空能量比较3。 |
| Section4.reconstructedError | 实际 V 值完整误差代表。 |
| Section4.reconstructedError_value_ae | 与原 H 值 U−Rbar z 几乎处处相同。 |
| Section4.reconstructedError_decomposition | 原实际误差分解，无求解条件。 |
| Section4.CombinedEstimate | 原两种误差率、全图解与全离散解、jet MemLp。 |
| Section4.combine_nonnegative_rates | 末步公共常数合并，单列为辅助标量引理。 |
| Section4.combined_estimate_of_spatial_temporal | 构造中间 u 并实际组合已证两个阶段。 |
| Section4.CombinedUniform | 所有原数值数据后置的统一完整结论。 |
| Section4.combined_uniform_of_section3 | 共同阈值、两个方向和两个 profile 符号内部供应。 |
| OriginalForm.combined_uniform | 原 A1–A3/N1/N3/N4 最终入口，不再输入误差估计。 |
