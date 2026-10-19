# T142：原 Proposition 6.2 的完整 Cartesian 数值实现

目标是原稿 `prop:fd` / Proposition 6.2（`paper/main.tex:1672`），即真实 Cartesian 差分方案的 N1–N5、m=1、aE=Ch、a0=Ch²、ηA=0 和指定节点平方权测试。该命题之后借助连续 CE 推导离散 Carleman 估计的段落是另一个依赖步骤，本阶段不声称证明连续 CE 或一般凸多面体正则性。

`cartesian_numericalData_of_box` 在固定正边长盒上，内部调用 T141 的实际原 Dirichlet 算子域 H² 包含；hD 是输出而不是输入。随后应用 T110 的实际完整数值组装，供应原形式、Kuhn 重构、原对角质量、2d+1 点差分、真实载荷 lift、实际控制零延拓的 Hilbert 伴随、所有状态和允许权的原加权近似/测试/零刚度缺陷。没有给调用者留下 H² 正则性、近似误差、测试超近似或观测界的证明义务。

`Section5.NumericalData` 只保存 transfer 用到的性质，本身不声称涵盖原 N1–N5 中全部较强结论。因此第二个定理 `cartesian_full_weight_interface` 显式联合供应所有允许权的原加权范数比较、载荷 lift 界、指定测试族的真实算子和真实导数等式、测试严格正定性、测试配对的双向范数比较及完整观测界。其 WeightedTest 仍含原周期端点、配对可微、对称性、时间导数界和空间超近似。新增结论是原实际对象的定理，不是补充的假设字段。

两个定理中所有常数和正阈值都在任意网格、步长、时间权、时间网格和状态之前选择；所有允许的符号 η=±1、实指数 |τ|≤τStar 和时间均保留。固定原点和正边长只指定原域；每个离散网格通过精确盒域等式识别，步长满足 h/κ≤δr≤h。取 h=max δr 即原论文设置。维数写 d+1，覆盖每个 d≥1；网格整数未额外限制，故还包含原 Nr≥2 的全部网格及退化零状态空间。两组独立于网格/时间的阈值可取最小值，有限组常数按各个原估计使用；原论文 C 为可变化的统一常数。

原 N1 的 injectivity、无权范数比较、质量伴随、刚度和非负性，N2 的真实 J lift=Γ 与 Γ I=id，不被 NumericalData 的较小接口替换。它们分别由当前固定依赖中的 `cartesianReconstruction_injective`、`cartesianReconstruction_norm_sq_bounds`、`cartesianReconstruction.mass_adjoint`、`cartesianPhysicalLaplacian_stiffness`、实际刚度梯度能量和 `cartesianLoadInterface`/`cartesianLoadInterface_right_inverse` 供给。Γ=I=id，原载荷/状态加权范数相同；全部重量资格和测试正定性来自真实正指数权，不是附加条件。R/J/Q/G 的确切节点与积分公式保留在 `CartesianReconstructionInterface`。原指定测试的每个节点等式见 `cartesianPhysicalTest_values`，其算子范数导数见 `cartesianPhysicalTest_hasDerivWithinAt`。

两模块两新增定理申请完整 P012/PAPER 独立验收，需同时核对上述实际依赖，不能仅凭 Nonempty NumericalData 的类型判定原命题完整。T141 及 T110 原审核范围和固定版本均保留。原稿未修改。固定版本独立验收及实际 CI 完成前不增加原文覆盖数。
