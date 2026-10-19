# T104：原 FD 对角测试的完整弱超逼近

目标为 `paper/main.tex` 的 `eq:testsuper` 及附录 B Step 3，保持原固定物理域、全部内部节点状态、允许权族和常数的先置量词。

`PrescribedNodalWeakResidual` 将已验收的全弱状态乘积残差落实到指定节点数据。实际 `nodalLp` 的代表唯一性保证原残差中存在的节点代表与 `cartesianInteriorData` 产生同一个加权节点插值。结论仍使用真正的 L² 类和弱梯度，没有对一般 L² 类取节点值。

`PrescribedNodalSuperapproximation` 将零阶、梯度平方界组合为原 H¹ 权范数。由 Dq≤1，零阶的 q² 因子被吸收，得到 sqrt(2C) Dq Nσ(u)，再用 q≤qmax。输出取辅助残差的负值，因此明确等于 I(σ²u)−σ²u，符号与论文一致。

`AllowedCartesianTestSuperapproximation` 使用 T103 的实际 Kuhn 内接球和最大直径。固定 S、ρ、κ 后先选 ε=1/(d+1) 和 C，再量化所有网格、h、时间权、τ、t、η 与全部节点状态。网格物理域等于 S 是原固定 Ω 的表达，不是额外限制。紧闭包内部供应有限测度。h q(t)≤ε 推出 Dq(t)≤1；真实重构属于原 conformingSpace，且其节点数据正是原数据。最后得到：

`N_(σ⁻¹)(R_h T_(σ,h) f − σ² R_h f) ≤ C h qmax N_σ(R_h f)`。

σ²T 的身份来自实际节点乘法和实际重构 Lp 身份；没有以任意存在的插值算子替代原对角测试。所有参数依赖都在 Lean 的 ∃/∀ 顺序中固定，两符号完整保留，原 h qmax 小条件自然蕴含使用的 h q(t) 条件。

本阶段三模块、五项声明，定向构建 3526 jobs，全库 3815 jobs，6299 项递归公理审计通过。固定声明产物 `/tmp/carleman-fd-test-super-local-axioms.txt`，1889692 bytes，SHA256 `67c65a22255a76349ad9d77b9438f444bd5994a4224b7582d1309f8d08976989`。

本阶段覆盖原 FD 的空间测试估计，T101/T102 已分别提供真实质量、自伴正定及时间性质。完整 FD/P012 仍需观察接口及全数值接口组装；范围为 AUXILIARY，原文覆盖保持 14/26。固定提交后的独立 Agent 验收和同 SHA CI 另记于唯一台账。
