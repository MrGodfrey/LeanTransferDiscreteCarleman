# T092：原允许权族的实际重构与载荷加权稳定性

八模块18声明，AUXILIARY，对应原 Appendix B Step 1 的载荷稳定性及 `eq:fd-local-stability`。在固定原有界开凸域 S 和固定原光滑空间轮廓 ρ 后，存在 C>0，先于所有实际有限 Cartesian/Kuhn 网格、步长上界 h、时间权（因而周期 T）、幂次 τ、时刻 t、符号 |η|=1 和完整离散状态 f，使 hq(t)≤1 时

`Eσ(f) ≤ C ‖σ R_h f‖²`，`‖σ R_h f‖² ≤ C Eσ(f)`，`‖σ L_h f‖² ≤ C Eσ(f)`，

其中 `Eσ(f)=(∏δ_j)∑_a(σ(x_a)f_a)²`，R_h 与 L_h 严格沿用 T091 的实际重构和 T090 已验收的同一 L² 右逆载荷。平方形式与原范数形式等价。最终声明 `allowed_weight_cartesianKuhn_stability` 包含所有网格域等于 S 的原情形，并允许网格域为 S 的子域；所有参数先于 f，C 不依赖网格数、h、时间权、T、τ、符号或状态。长宽比对本阶段不需要。

`WeightedCompactCell` 先证明实际紧单元上连续函数的 L² 与加权平方可积性，再由真正 a.e. 权锚点界得到双向实际积分界。`SimplexWeightedStability` 将真实单元重构质量界和同一载荷精确平方积分界与节点权锚点相连，正锚点消去后给 W⁴(d+2) 的一致常数。这里使用的是实际 Lebesgue 积分，不是将范数稳定性作为前提。

`KuhnAllowedWeightComparison` 把已证开盒直径界延伸到整个闭盒，得到真实单元（包含边界顶点）直径≤dh；原固定光滑轮廓供应 L-Lipschitz 界，hq≤1 内部给实际允许乘子双向比较 W=exp(Ld)。ρ 的空间变化先于全部网格；没有把权比较当成最终定理的输入，也没有把 σ 换成任意抽象系数。

`CartesianKuhnWeightedMass` 用完整内部数据的真实有限指示延拓证明其与任意物理权相乘交换，再把已验收精确质量组装应用于加权节点数据，得到真实单元加权节点质量之和严格等于 Eσ。没有网格基数因子。

`WeightedScalarRepresentative` 证明 L² 类的实际代表替换下，加权平方密度可积且积分等于真正乘子半范数平方。`CartesianKuhnWeightedCell` 将实际闭单元的重构点态公式和同一载荷 a.e. 公式代入单纯形界；共享面只通过已证 a.e. 身份处理。`CartesianKuhnWeightedNorm` 沿同一真实有限分割求和，并用精确加权质量身份和真实 L² 代表，得到原域上的三项加权范数平方界。

`AllowedCartesianKuhnStability` 在原固定 S、ρ 之后一次选择 C=exp(4Ld)(d+2)，逐个实际单元以其零号顶点的真实 σ 值为正锚点，内部清偿全部单元及节点比较假设，最终量词完整覆盖原允许权族和完整内部节点空间。

这只完成原 FD 的加权重构/载荷稳定性阶段。局部 Q_h 稳定性、刚度身份、B.2 与完整 FD 仍待，原文保持13/26。未改动原稿、既有声明、Lean 或 mathlib 固定版本。
