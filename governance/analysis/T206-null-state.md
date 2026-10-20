# T206 — 实际盒 FD 控制的每个弱积聚点给连续零终态解

基线 `bfa6e3a8b9af4367eca74101ad0473c42e8bdfa8`。原文 `paper/main.tex:2347–2415`、`prop:control-convergence` 的实际矩形盒 Cartesian FD 分支。2 模块 3 声明；仍 AUXILIARY、17/26，整个 P021 的一般 P1 分支未完成。

`DirichletNullControlState` 是明确定义的结论谓词，不是假设包或新公理：同一 Y∈L²_t H¹₀、同一原 U/b/y0，存在真实 q∈C([0,T];H)，q=EY a.e.、q(0)=y0、q(T)=0；并对每个内部 C∞ 紧支时间测试，满足实际 StrongDual Bochner 分布等式。原 dirichletPivotDual 是 H 内积嵌入，dirichletDualTimeLoad 是原控制减去梯度形式和原产品势作用的真实 L²_t V′ 载荷，其与所有 V 方向的配对已在 T200 明确证明。

`FiniteDirichletControlIdentity.null_control_state` 由 T200 真正对偶弱导数与 T204–T205 的真实连续迹/端点定理构造这个谓词。没有将结论谓词作为输入，也没有把时间端点赋给任意 Lp 代表。

`Physical.box_cartesian_controls_null_limits` 对同一原盒、嵌套观测区域和可比 Cartesian 网格，保持 T198 的完整量词顺序：κ,d0 先于 T/M；C 先于网格、势、初始数据；任意 h_n→0、dt_n→0 独立细化后存在一个尾段 J 和同一组离散 u_n/y_n。原平均势、初始 E* y0、ForwardEquation、控制费用、指数终值界、真实 K 重构与支撑结论全部原样保留。

相对弱紧性仍对任意抽取序列 a（允许重复）给严格增子列及区域 v；对于每个严格增 a、每个满足实际 K(a_n) 弱收敛的给定 U，使用同一个 T198 提供的 Y 和区域 v，保留其原能量预算、U 的原零延拓身份和 ‖v‖≤√C‖y0‖，并同时返回原 FiniteDirichletControlIdentity 与上述实际连续零终态解。没有将“每个积聚点”换成自行挑选的一个控制极限，也没有重新选择或加强原离散控制族。

本批整合的是实际 FD 分支已证明的强结论：每个弱控制积聚点产生原方程的一个能量解及其真实零终态，未另声称新的能量解唯一性定理。区域 Bochner 控制及其零延拓用原 restrictRegionCLM.adjoint.compLp 实现，与原 L² 产品控制的已建等距重构一致。原成本常数不引入后续迹证明的 T⁻¹；网格与 dt 不增加耦合。

一般 P1 网格控制收敛及整体 P021、其余未覆盖原文结果仍待；不因完成盒 FD 分支提升整个原论文覆盖。原稿保持不变。
