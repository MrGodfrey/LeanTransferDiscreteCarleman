# T174 / C190：完整 P1 盒实例的物理及滤波观测、区域控制

三模块四声明，其中两个显式结论定义仅展开原完整观测/控制命题，两个完整定理内部构造其全部证据。`PhysicalObservationControl` 保留所有非周期伴随解的真实 B* 观测与指数余项、每个初态的实际控制/完整正向方程/原时间成本及完整终态界。`PhysicalFilteredObservationControl` 保留终态∈F的观察结论、每个初态的实际控制、PF终态精确为零及完整指数终态界。这些只是完整命题定义，不将目标放入假设。

`box_p1_physical_observation_control` 在真实固定盒、原维数2/3、形状正则与grading条件下调用 T173 完整 P1 物理载荷CE。原 Gaussian 相位统一负性、consistent-mass Galerkin 算子对称非负、原区域 L²(ω) 控制及真实势投影全部内部供应。任意实际有界空间势 b_i 具有同一 Mbound 上界；势作用为原 L² 投影后的乘法。完整原P1状态、包含重构和真实质量均不变。

最终选择 qc/κ/h0/Δ0/Cb/d0 后才量化任意T>0、Mbound≥0；Cphys(T,Mbound)先于全部单纯形网格/局部尺度/时间/势/状态。原 S=κmin(h^(-4/5),dt^(-2/5))、h=maxDiameter、原两侧物理条件及dtM≤1/2保持。返回实际原L²(ω)控制，而不是ambient空间中的任意向量；其完整ForwardEquation由真实regional HUM供应。

`box_p1_filtered_observation_control` 同样内部供应物理观测，统一取 C0=max(1,max(Cphys,2factor(T,Mbound)²))，先于所有网格、势、θ、F。原TΛ≤θdS与对数条件使用这个同一C0；仅终态F的反向估计给原2C0观察界，真实互补HUM给实际控制、完整正向解、sqrt(2C0)成本、PFyN=0及C0exp(-(1−θ)dS)完整终态界。F任意且无不变性要求，零子空间包含；区域控制Hilbert空间可无限维。

此处没有额外CE、H²域、数值测试/近似或观测前提，参数均按原顺序统一。但仅完整盒P1实例，一般凸多面体仍待；AUXILIARY、覆盖17/26。两个结论定义展开类型与两定理均需独立审核，不能将定义本身计作证明。

定向物理接口3922 jobs、滤波接口3933 jobs通过；根目标与递归审计摘要见台账。同SHA正式CI与独立验收另行记录。
