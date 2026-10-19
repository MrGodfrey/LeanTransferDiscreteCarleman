# T164 / C180：完整盒弱周期图上的双方向连续 Carleman 估计

四模块十二声明。BochnerBoxIntegral 在真实时间/空间乘积测度上证明加权密度可积，允许 q 仅在原闭时间区间连续。先用实际 Lp 范数积分及两层 a.e. 平方身份，再用 Fubini 和 Ioo/Icc 测度相等，将原 timeSq 与真正 boxTimeIntegral 对齐；观察项使用真实可测示性函数，内部证明其可积性，没有假设观察示性函数连续。

PeriodicClassicalRepresentatives 从同一 F 的原闭区间迹得到实际 Bochner 值代表；外内两层 Lp smul/add 规则给 ε∂t+A 字段空间 a.e. 等于真实 spaceTimeOrientedHeat，即 ε∂tF−ΔF；实际 cutoff CLM 给观察示性函数代表。DirichletHeatIntegral 结合 T163 的真实弱梯度身份，内部证明经典梯度平方和热残差的连续性，再把原 q³ 值、q 梯度、残差平方、q³ 观察四项逐一转成原柱积分。

最终 box_weak_C2_gaussian_heat_both_signs 内部调用已证原闭区间 C² 光滑状态估计。c、λ、β、qc、C 只由盒和观察集选定，严格在全部 TimeGrid、TimeWeight、两个 ε 和全部原完整 PeriodicGraph 之前。权保留 Icc 上 C²、0/1/2 阶端点匹配、q≥qc、两导数预算；没有要求其区间外连续或光滑。真实 profile 是 interiorSpatialProfile，其值就是原负高斯相位，负值范围全空间成立。仅在固定 q 的密度步骤使用连续性界，最终 C 不依赖 T、qmax、频率或轨道。

在经典 core 上拆出同一 F，使用真实积分身份清偿 T163 的 hCE；由完整周期图密度将同一 C 延拓至所有原弱轨道。最终声明没有给定平滑逼近、经典导数代表、光滑 core CE、全时刻 D(A) 或额外 PDE 前提。值、时间导数、A 和空间梯度均为原实际对象。

这是坐标盒域的完整弱状态 CE，仍不是 P024 所需所有 analytic-realizations 域。权用原框架 TimeWeight（全实轴有界且≥1）承载；其原闭区间 C² 代表尚应另给任意原 q 的内部有界延拓，以及与原 PeriodicWeakTrajectory 的直接接口。一般凸多面体及这些呈现接口继续。保持 AUXILIARY、P024 不提升、覆盖17/26，原稿不改。

定向3582 jobs、根目标4076 jobs通过；7926项递归审计通过。固定 raw 2458281 bytes，SHA256 0e34ed37ddc7d0fa34d57823681e30b39e7e9975f70a1416327bd84a31fc25b2。正式同 SHA CI 与独立验收另行登记。
