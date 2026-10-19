# T170 / C186：网格统一的原 Cartesian 物理观测与实际控制

三模块三声明。PhysicalObservationUniformProfiles 将实际物理权构造的 Cb、d0 选在 T/M 之前，将 C(T,M) 选在所有空间类型、测度、相位及离散数据之前。相位仅要求同一个固定 bound=Rbound 和负性阈值；实际常数公式的相位依赖仅经 Rbound。证明直接使用已证原物理权、cutoff、节点势吸收、真实端点余项和初始能量恢复，不对每个网格分别选择存在性常数后擅自断言统一。

BoxCartesianObservation 内部调用 T169 的无额外前提实际载荷 CE；Gaussian 节点相位 bound=2、≤−1，独立于节点数。原状态到计数 L² 的等距映射同时作 R/I，Γ 为其真实逆，质量比较和载荷比较常数严格等于1。任意实节点势 b_i(a) 满足 |b_i(a)|≤M，即为原物理节点乘子；对称性、同 M 算子范数界以及 Γ(b_i R x)=V_i x 均从 T168 内部供应。原差分 Laplacian 的实际对称和非负性已证明。

最终定理选择 qc、κ、h0、Δ0、Cb、d0 后，量化任意 T>0、M≥0，再选择同一 C(T,M)>0，最后才量化空间网格、时间网格、节点势与所有原非周期伴随解。S=κ min(h^(-4/5),dt^(-2/5))，输入准确保留原 16qb≤S≤qb*T/(4dt)、dt*M≤1/2、dt≤min(Δ0,T/12) 及原网格条件。结论使用真实原控制空间中的 B*，由 EBB* 的精确范数身份消去计数表示；余项准确为 exp(-2d0S)‖pN‖²。无额外 CE、矩阵、自伴、正则或数值假设；没有频率过滤。

BoxCartesianControl 从上述完整观测定理和已证真实 HUM 构造给每个原 y0 选择实际节点控制 u 及整个非周期状态序列 y，满足原 ForwardEquation、y0 身份、cost≤sqrt(C)‖y0‖ 和 terminal≤sqrt(C)exp(-d0S)‖y0‖。不是抽象终端向量或未实现的最优性方程。控制使用原 ω 内节点物理空间，实际 B 为零延拓；同一选择次序保持网格统一性。

这是原 physicalO/physicalC 的完整盒 Cartesian 实例；P1 与一般允许几何尚待，仍 AUXILIARY，原文覆盖17/26。没有用实例代替整个一般原文结论。

定向3068、3986、3987 jobs，根目标4097 jobs通过。Axiom audit passed for all 8096 Carleman declarations. 固定raw 2529676 bytes，SHA256 4898f0fd311b42c290e7317371fb9e7d7f3b0b76c0e2864fab66a8f63b8ce174。同SHA CI和独立验收另行登记。
