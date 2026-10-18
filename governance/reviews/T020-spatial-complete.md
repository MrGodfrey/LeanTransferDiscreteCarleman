# T020 完整空间误差声明核对

这是执行者对新增声明、量词、原假设及依赖的核对；不冒充独立论文验收。精确构建版本和 CI 由唯一任务/claim/coverage 台账绑定。[数学说明](../analysis/T020-spatial-complete.md)记录证明和剩余边界。

| 声明（均前缀 Carleman.） | 核对结论 |
| --- | --- |
| Section4.energyNorm / regularityNorm | 原节点弱 Nm 与各阶字段真实时间 L² 范数之和 R₂ₘ；无抽象替代范数。 |
| Section4.WeightedApproximation / .energy / .l2 | 恰为 N3，全部 t∈[0,T]、原 D(A)；无目标误差字段。 |
| Section4.nodal_energy_le_regularity | 原 D⊆V 截断，固定 m+1 因子；q≥1 来自 TimeWeight。 |
| Section4.WeightedApproximation.nodal_energy / .nodal_Q / .nodal_l2 | 逐时刻 N3 提升到真实节点范数；不引入节点数/T 因子。 |
| Section4.regularityNorm_nonneg / energy_rates_of_cea | 原 e_s=η−Re_h、Rz=Qu+Re_h 恒等式，实际范数三角及两个最终能量率。 |
| Section4.WeightedTest / .op / .derivative / .endpoint / .hasDeriv / .symmetric / .nonneg / .time_bound / .superapprox | N4 必需原数据；只使用原正定性的非负后果，不新增假设。真实时间导数、闭周期端点、原 hqmax 超逼近因子。 |
| Section4.spatial_smallness_thresholds | δx≤δnum、ηstar>0、ηstar≤1；显式给出 ε≤1 和吸收条件。常数先于 hqmax/ηA。 |
| Section4.EnergyEstimate / energy_estimate_of_cea | 对每对实际连续/全离散解给 energy error 与 state stability；载荷来自已证 Euler 图。 |
| Section4.squared_weight_signed_uniform | σ² 两次乘法与逆权的真实 Nm 比较；对两 profile 符号统一，不扩大允许 τ。 |
| Section4.spatial_time_threshold | 正阈值同时进入 Euler 和实际 q/σ 单元范围；无 T/qmax 依赖。 |
| Section4.EnergyUniform / energy_uniform_of_section3 | 统一常数先于全数值数据；内部提供 form、coercivity、σ²、N4 时间下界、小性吸收。 |
| OriginalForm.spatial_energy_uniform | A1–A3 原入口内部调用完整 Section3，无额外 graph/Cea 前提；只是 energy 半部。 |
| Section4.weighted_pairing_bound | 实际正/逆乘子在空间 L² 配对精确相消，再作 dt Cauchy–Schwarz。 |
| Section4.spatial_duality_bound | 完整三项原恒等式、实际反向解方程、原 N3；保留缺陷，左端是真正 σe_s 范数平方。 |
| Section4.L2Estimate / duality_rate_coefficient | L² 原结论及明确仅用于末步的标量率比较，后者不被当作整个误差证明。 |
| Section4.l2_estimate_of_energy | 从存在性构造反向域序列；逆权载荷精确相消；原 energy/stability 和两个 Euler 图合成 a0+aE²+ηA。零范数不除零。 |
| Section4.SpatialUniform / spatial_uniform_of_section3 | 同一 K 覆盖 energy、state、L²；两方向、两符号、全 X/全解/任意载荷，常数在所有变动数值参数前。逆权 N3 是原所有允许权假设的实例。 |
| OriginalForm.spatial_uniform | 完整 Lemma4.1 原假设入口。唯一解析条件是原域/形式、正向椭圆界、原权与 A2/A3；所需 Section3 全部内部调用。 |

八模块、36 显式声明均由 Carleman 根目标导入并逐个加入 CheckAxioms；本机完整构建及全部 3080 声明递归检查 PASS。既有 2973 声明未改写。原稿 SHA256 保持 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

有限维辅助离散存在唯一性沿用此前 `Reconstruction.existsUnique_auxiliaryEuler`；本阶段估计对所有实际解成立，既不把唯一性替换成选定解，也不强加有限维之外的限制。正式覆盖保留 BUILT 而非 REVIEWED，等待独立验收。Theorem4.2 和原最终 Theorem2.1 仍待完成。

实际 main 提交 `a315bdc449c58a705a982f0d009f1dde24d6af66` 的 [CI39135593975](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39135593975/attempts/1) 三项全部成功，下载的公理产物与本机逐字节相同，SHA256 `4cf5509f91b61e80901ab0f86484133c25cf95cd92f58849a473a01189a98278`。C008/P009已按协议绑定BUILT；独立本机Agent另行验收。
