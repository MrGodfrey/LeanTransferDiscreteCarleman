# T022 — 原 Theorem 2.1：消去完整 transfer 桥接前提

基线为 `9d8230090dad2c5b5a2efa74f5d085728866d139`，main CI39136913051 三项成功，Theorem4.2 已由独立 Agent 验收。原稿及原最终结论未改。新增五模块、18 项显式声明；入口 `OriginalForm.transfer_uniform`，输出 `Section5.TransferUniform`。

## 精确识别原平方量

`SpatialProfile.timeSq_eq_bochnerL2Norm_sq` 在实际 MemLp 下把 θ 密度的 q^b 时间平方积分识别为 q^(b/2)θ 的真实 Bochner L² 范数平方。`nodeMap_l2Norm_sq_powerSq` 给相同节点等式。两者无比较常数。

`WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum` 把原加权 Nm 时空范数平方写为各真实弱导数字段的 q^(2(m−k)+b)θ² 积分和；每阶 MemLp 来自实际 jet 的 MemLp，再逐点使用实幂等式。`sobolevGeometry_graphSq_eq` 将这一结果实例化到既有 Section5 真实 Sobolev geometry。没有用抽象标量替代误差或假定同名范数相等。

## B4 与所有桥接条款

`sobolevGeometry_errorBridge_of_combined` 对 `energyPower(j)/2` 及 c0/2、o/2、2m 分别调用真实 `CombinedEstimate`。所有指数经非负性和原 coverage 界仍在 |τ|≤τStar。逐节点从原辅助方程得到 CombinedEstimate 的方程；同一冻结图解 U 使用同一转移载荷。对真实误差界平方，明确验证右端非负，并把原 `sqrt(dt)+aE+ηA` / `dt+a0+aE²+ηA` 与 `ErrorScales` 重排一致，系数只从 Kc² 放大到共同 K。

L² 分量通过 `reconstructedError_value_ae` 在实际 H 弱代表和 V 域代表间传递真实范数。所有有限性、微分阶数界与冻结移位界调用先前已证明的 `sobolevGeometry_errorBridge` 构造，不再假定它们成立。

`sobolevGeometry_transferBridges` 构造整份 `TransferBridges`。对任意方向、载荷和全状态，实际调用 `existsUnique_variable_periodic` 解非负冻结连续问题，载荷恰为 Lf+μRz；从图方程与 `extensionLp_ae` 得原几乎处处冻结方程。B3 的原数值范数界及 A4 经真实比较/有限性构造填入；B4 来自上述已证误差构造。没有给定解、最终误差或目标离散 Carleman 估计作为本构造之外的假设。

## 原假设入口与统一性

`Section5.NumericalData` 只打包原 N1–N5 中实际使用的内容：真实刚度等式、原允许权族的 N3 逐时逼近、N4 可微测试族、刚度缺陷、θ 节点重构双向界、载荷提升及观测界。共同 Cnum 是这些原正范数常数的平方/最大值，可统一选取。R/J 质量伴随属于 `Reconstruction`；普通 Γ/lift 与 JL=Γ 属于 `LoadInterface`。右逆仍是普通函数，原稳定右逆界用于残差版。数值权范数的 q 幂通过原标量齐次性直接体现于 powerSq，未另要求更大权族。

`TransferUniform` 保留实际 N1–N5 数据和 A4 连续估计；其输入中没有 TransferBridges、CombinedEstimate、图估计、误差估计、插值结论或可积性结论。A4 量化所有原弱周期轨迹，两方向通用；Cce 在网格、数值空间和状态之前固定。省略未使用的原正性、有限维和更强测试范数条件只加强结论，没有增加原论文假设。

`transfer_uniform_of_combined` 先从已证统一 Theorem4.2 选择 L=Lmin，再取得 δx≤δnum、ηstar、Kc。选

`K = 9 + 9 Cnum + Kc² + (2L)^(4m) + differentialFamilyBound(P) + Cce`。

所有这些量先于 X/F/Y、离散化、周期 T、网格、q/qmax、mesh、误差尺度、方向、载荷和状态。时间阈值再与显式 B3 cellThreshold 取 min；空间阈值沿用 Theorem4.2。由真实 NumericalData 在每个原允许权上供应 combined，逆权由 signed_neg/abs_neg 得到，不要求扩大数值权族。

随后调用完整桥接构造和既有已验收吸收证明，取

`cStar = 1/(2 transferConstant(α,K))`，

`Cfinal = 4 transferConstant(α,K) K`。

在原 Λf≤1、Λz≤cStar 条件下输出原 `eq:finalCE` 载荷版；对每个原稳定右逆，输出所有状态的 `eq:rawCE` 残差版。原 εE/ε0、dStar/bStar、两个 max 缺陷幂次均保持不变。Γ 未强加线性，R/J 未强加正交性或 G=Id，未增加频率或状态限制。

最终 `OriginalForm.transfer_uniform` 从原 A1 的 closed-form 实现、原域嵌入和正向椭圆正则界内部调用 `combined_uniform`，然后完成以上组合。A2/A3 留作原 AllowedFamily，A4 留作原连续估计，N1–N5 留作原数值数据，全部 B1–B5 已在证明内清偿。原域/算子与 closed-form 模型的识别沿用已验收 Section3 OriginalForm 接口。

## 本地验证与验收边界

全库实际构建与递归公理检查通过：3454 build jobs、3170 个 Carleman 声明；18 项新显式声明全部输出实际类型和公理依赖，只有 propext/Classical.choice/Quot.sound。公理产物 SHA256 为 `230919fb64b2d861fac74c586ba40f073332eac5581556a0e7d5004dbb27e24e`。本地日志 `/tmp/carleman-original-full.log`。

这只是执行者完成的原 Theorem2.1 候选。待固定提交同 SHA main CI 与独立 Agent 忠实性/依赖验收后才能登记 REVIEWED/PAPER；本记录不替代独立验收。原 Corollaries2.2–2.3 及后续应用、观测、控制等具名结果另行推进。

## 18 项显式声明

- `Carleman.SpatialProfile.timeSq_eq_bochnerL2Norm_sq`
- `Carleman.SpatialProfile.nodeMap_l2Norm_sq_powerSq`
- `Carleman.WeakSobolevJet.spacetimeWeightedNorm_sq_powerSum`
- `Carleman.sobolevGeometry_graphSq_eq`
- `Carleman.sobolevGeometry_errorBridge_of_combined`
- `Carleman.sobolevGeometry_transferBridges`
- `Carleman.Section5.NumericalData`
- `Carleman.Section5.NumericalData.stiffness`
- `Carleman.Section5.NumericalData.approximation`
- `Carleman.Section5.NumericalData.test`
- `Carleman.Section5.NumericalData.defect`
- `Carleman.Section5.NumericalData.reconstruction_upper`
- `Carleman.Section5.NumericalData.reconstruction_lower`
- `Carleman.Section5.NumericalData.lift_bound`
- `Carleman.Section5.NumericalData.observation_bound`
- `Carleman.Section5.TransferUniform`
- `Carleman.Section5.transfer_uniform_of_combined`
- `Carleman.OriginalForm.transfer_uniform`
