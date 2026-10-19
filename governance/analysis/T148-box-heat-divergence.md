# T148：实际坐标盒的面通量与散度积分

接续 T147，完成原 `prop:continuousCE` 的光滑空间通量积分步骤在任意正坐标盒上的真实实例。四模块15声明，AUXILIARY；原完整连续CE/P024不提升，原文17/26不变，原稿未改。

`coordinateBoxFunctional` 是真实坐标基的 Riesz 对偶，上侧取负、下侧取正；逐点等于 −xᵢ 或 xᵢ。真实阈值为 −bᵢ 或 aᵢ，全部严格/弱半空间不等式分别精确等于原 open/closedCoordinateBox。归一化 Riesz 外法向严格为上侧 eᵢ、下侧 −eᵢ。面内部点明确构造为其它坐标取中点、指定坐标取端点；全部其它不等式严格由 aᵢ<bᵢ 推出，不再外给面见证。

`box_face_gaussian_heat_flux` 将这些真实数据代入 T147 的闭面定理，从原 u 在整个 frontier 的逐点零值得到上侧 Vᵢ≤0、下侧 −Vᵢ≤0。同一中心 c∈原开盒、l≥0、q(t)≥0 与实际 L(t,y)=q(t)ρ(y) 保留。结论覆盖各闭面的全部点，包括棱角；这里法向是每个指定坐标面的法向，没有在角点定义唯一法向。

`coordinateDivergence` 定义为实际 Fréchet 导数沿真实 Euclidean 正交基的分量和。`smooth_closed_box_divergence` 调用 pinned mathlib 的真实 Bochner 散度定理。调用前将 Euclidean 空间经实际连续线性等价转换到函数坐标；真实导数由链式法则构造，标准坐标单元向量严格识别为 Euclidean 基向量。连续性给散度在紧闭盒上的可积性，内部满足 mathlib 所有前提，无未证明散度、法向迹或可积性输入。Euclidean 与函数坐标的 Lebesgue 测度由实际保测定理识别，因此没有漏掉体积或面积归一化因子。

最终公式为体散度积分等于各坐标面的上侧积分减下侧积分。每个面用 `Fin.insertNth` 的真实坐标参数化，其余坐标在实际闭区间积上以标准 Lebesgue 测度积分。零维横截面也由同一 mathlib 公式处理，所以覆盖一维盒；高维不受限制。`openCoordinateBox_ae_closed` 从各坐标端点零测和真实保测拉回证明开闭盒几乎处处相等，将公式传到原开盒体积分。

`box_gaussian_heat_flux_integral` 对同一时空 V 的固定时间切片应用该散度定理；切片导数由真实链式法则与 spaceTimeSpatialDirection 精确识别。面参数化的每个点实际属于对应闭面，所以上侧积分非正、下侧积分非负，逐面差非正，得到原开盒上的 ∫divV≤0。L、u、k、p 全时空 C∞ 内部供应切片光滑性。定理仍允许任意光滑 k、p，自然涵盖指定热共轭 k 和 Ψ；没有用不同通量替代原 V。

范围限制：本批建立实际盒域的经典光滑散度积分，不声称一般凸多面体散度公式、原 H²∩H¹₀ 的弱法向迹/Green 或全弱轨道密度。尚未将时间通量通过 Fubini 消去，也尚无 heatcross 系数控制、原 C² 时间权、吸收或时间反射。以上仍属 P024 剩余义务，不能将 ∫divV≤0 当成完整 Carleman 估计。依赖 T147/C163 真实闭面，及其已验收的实际时空通量定义。
