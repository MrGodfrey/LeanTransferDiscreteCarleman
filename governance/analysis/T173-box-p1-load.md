# T173 / C189：完整一致质量 P1 盒实例的物理载荷估计

一个完整定理 `box_p1_physical_load_carleman`，对应原 P1 实现、热尺度与物理载荷 CE。固定正维盒、d+1≤3、非空开控制域 ω⊆盒、原 shape/cmesh/Bmesh/γ 常数及原 grading 阈值。所有相位、β/qc/κ/h0/Δ0/C 常数先于所有网格、时间和权；不是对每张有限网格选择常数。

对每个真实非退化有限单纯形分割及原 face matching、boundary fitted、形状正则和邻接 grading 数据，状态是完整 `M.conformingSpace (dirichletSubspace S)`，内积是实际 L²，刚度是原 Dirichlet 形式的 Galerkin 算子；不替换为质量集中或缩小状态。网格大小精确为真实最大单元直径，由非空域和正维分割证明它严格正。

连续输入全部内部清偿：T166 的全弱轨道原盒连续估计给真实 Gaussian 相位及原 IntervalQClass；T143 的完整盒 H² Dirichlet 域与图范数界供应 A1，原允许权族供应 A2/A3。T126 `full_p1_numericalData` 给全空间原近似/测试数据；取其 approximation/test 构造 GalerkinHeatData，其 consistent-mass 代数、载荷/观察身份由真实 galerkinNumericalData 内部重新供应。观察内集选为 ω，数值观察比较允许等号；没有要求控制域是有限维或附加边界正规性。

调用原 conforming_heat_load_uniform 获得 κ0/h0/Δ0/C，然后统一缩小 κ=min(κ0,ε)，原 h≤h0≤1 与热尺度推出 h*qmax≤ε，完全清偿数值小量而不留下另一额外网格阈值。此缩小在物理参数 S 选择之前完成，不在最终两侧 S 条件之后改变尺度。

结论是真实 PhysicalLoadCarleman：全部周期状态及全部 L² 载荷，负向差分方程，R为实际包含，Γ为真实L²正交投影，观察为实际ambient cutoff控制的Hilbert伴随。其与原区域L²(ω)控制范数的既有身份在后续物理观测/控制使用。原q³状态、载荷权、q³观察及h^(-4/5)/dt^(-2/5)范围保留。

本批不含额外CE、H²域、数值测试或滤波假设；但只完成固定盒上的完整P1实例，一般凸多面体/光滑域仍待，所以AUXILIARY、原文17/26。后续真实物理观测/控制独立接续。

定向3919 jobs成功；根目标4106 jobs成功；全部8138项Carleman声明递归审计PASS。唯一声明已根导入并显式打印类型/公理；固定raw摘要见台账。同SHA正式CI与独立验收另行登记。
