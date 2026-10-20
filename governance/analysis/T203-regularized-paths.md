# T203 — 实际质量正则化连续轨迹

基线 `1b8ccf90c8aeef46bf0f614e537c02a6494caa5a`；原文 `paper/main.tex:2415` 的 H 连续时间迹辅助构造。2 模块 3 声明，AUXILIARY，17/26；不提升 P021。

在完整实 Hilbert 空间 V 上，输入原实际 Y,D∈L²_t V、非负稠密值域有界质量 M，以及原分布等式 (MY)'=D。任意正 ε_n→0，T201 给实际 R_n=(M+ε_n I)⁻¹ 和 Q_n=MR_n。弱 H¹ 连续代表定理应用于质量场 MY，内部构造闭区间 V 连续的 m，与 MY 几乎处处相等。令 u_n=R_n m、du_n=R_n D；有界线性映射的真实积分交换证明 u_n 的弱导数确为 du_n。

实际逆的交换恒等式给 u_n=Q_n Y 几乎处处，Mdu_n=Q_n D 几乎处处。使用真实 toLp/compLpL 代表身份和 T201 的 Bochner 强逼近，得到 u_n→Y、Mdu_n→D 的 L²_t V 强收敛。所有连续性、du_n∈L² 以及弱导数资格都由构造提供。没有假设原 Y 连续，也没有声称 du_n 自身统一有界。

`FiniteDirichletControlIdentity.regularized_time_paths` 直接接到 T199–T200 的原控制极限：M 是真实 dirichletStateValue 的 E*E，D 是同一 Y、U、b 的 dirichletTimeLoad。完整 H¹₀ 能量空间的非负性、稠密质量值域和原弱导数均由已验收证明内部供应。保留原有限空间测度、开集假设和同一 T；所传 TimeGrid 只编码该正周期，不施加周期边界条件。

本批构造实际 V 连续正则化近似和两项图范数分量强收敛。后续用 T202 的质量加权迹估计证明 E u_n 在 C([0,T];H) 一致 Cauchy，并识别 H 连续极限与原 EY。原状态 H 连续迹及初终值仍待，不把此辅助构造标成原论文整命题。

实现中避免在泛型结论中暴露依赖测度等式的证明传输；直接返回实际 MemLp 资格，数学陈述不变，降低 Dirichlet 实例的内核归约成本。原稿与工具链未修改。
