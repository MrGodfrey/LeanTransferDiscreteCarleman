# T211 / C227 独立本机验收

- checked_sha: `a98192d2b1dc2e5f7d7034d4a5be49d41c7b3bec`
- base_commit: `3725f002ad895342683989c46d052625da5f57ba`
- reviewed_at: `2026-10-20T04:34:10+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS — 2/2 定理，无阻断缺陷**
- axiom_check: **PASS**
- scope: **AUXILIARY；盒域、1≤空间维数≤3；17/26 不变，P021 不提升**
- evidence_source: **local**；未查询或声称远端 CI 成功。

直接读取固定 Git 对象中两模块的完整代码、两项 raw 展开类型、T211 分析与 MATH_SPEC，对照原稿 `paper/main.tex:2318–2415` 的重构、实际控制选择、弱紧性、原极限方程及连续端点步骤。原稿 SHA256 仍为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。不使用未来工作树或动态审计替代本批证据。

| 固定声明 | 源模块 | raw 行 | 结论 |
| --- | --- | --- | --- |
| `Carleman.Physical.box_p1_controls_independent_refinement` | `Carleman/Control/P1ControlRefinement.lean` | 39283 | **PASS**。完整尾段上的原区域控制与全 P1 轨道，原投影初值、平均势、费用、指数终态、实际支撑和初终重构极限均内部供应。 |
| `Carleman.Physical.box_p1_controls_null_limits` | `Carleman/Control/BoxP1NullControlLimits.lean` | 39439 | **PASS**。保留同一家族全部结论，任意取样有区域弱子列；任意给定控制弱积点 U 保持原区域代表与费用，并产生同一 Y 的原方程和真实连续零终态。 |

## 常数、完整原对象与独立细化

两项实际类型均先固定正边长盒、盒内非空开控制区以及 shape/cmesh/Bmesh/γ，再选择 κ,d0>0；随后量化任意 T>0、M≥0并选择 C>0，最后才量化整族网格、时间网格、具体势 b 和任意 L² 初值 y₀。C 不依赖网格、具体势或初值，κ、d0 不依赖 T/M。维数写为 d+1≤3，明确包含一至三维；没有以盒域结论冒充一般凸多面体。

Xₙ 是完整 `mesh n.conformingSpace (dirichletSubspace S)`，保留原 H¹₀ 与逐单元仿射 L² 类的全部状态。实际质量是原 L² 包含内积，刚度是原梯度形式的 Galerkin 算子，势算子为 `P_X(b_i·)`，控制算子为原区域零延拓后投影。原 FaceMatching、BoundaryFitted、内球形状规则、ℓ 与单元直径的双侧比较以及共享顶点局部分级 `1≤γ<Γ_(d+1)` 全部明确；没有准一致网格、嵌套或更小状态空间条件。

初值严格为 `Xₙ.orthogonalProjectionOnto y₀`，不是另一个光滑逼近或节点采样。步势严格为同一原产品势 b 的 `fixedTimeCellPotential`，真实 value 是时间胞积分除以 dt，bound 等于 b.bound。实际 T174 控制结论对所有初态返回真实区域 `u : Fin N→L²(ω)` 和完整 `y : Fin(N+1)→X`，同时包含初值、原 ForwardEquation、物理控制费用与终态界；本批取其控制分量，未输入额外 CE、H² 正则性、状态预算或目标控制存在性。

真实 hₙ 是 `maxDiameter`，正性由正维非空盒与实际分割内部取得。读过实际尺度证明：`Sₙ=κ min(hₙ^(-4/5),dtₙ^(-2/5))→∞`，且 `0≤dtₙ Sₙ≤κ dtₙ^(3/5)→0`。它们只使用 hₙ→0、dtₙ→0及正性，不需要单调细化、嵌套或 h/dt 比例。由此在一个共同尾段同时取得 h≤h₀、dt≤Δ₀、`16q_b≤S≤q_b T/(4dt)`、dt·M≤1/2及 dt≤T/12。q_b 是原 `physicalBaseAmplitude`，其正性在内部证明。

`eventually_atTop` 产生 J 后，对**每个** n+J 调用物理控制存在性，再以 `choose` 选择同一 uₙ、yₙ。这不是只在稀疏子列上构造控制。允许 J 位于网格与数据量词之后；基础常数仍在前。全部物理节点和步索引保留，正向方程是 `(y^{i+1}−y^i)/dt+(A+V_i)y^{i+1}=Bu_i`，无周期终点条件。

## 费用、支撑、初终极限

原费用和终端估计准确保留为
`controlNorm(dt,uₙ)≤sqrt(C)‖P_X y₀‖`、
`‖yₙ^N‖≤sqrt(C)exp(−d0 Sₙ)‖P_X y₀‖`。
sqrt(C) 是原存在成本常数的合法命名，仍只依赖固定几何、网格规则及 T/M。正交投影收缩把预算统一到 sqrt(C)‖y₀‖，没有使用有限元逆估计或离散提升范数。

重构 Kₙ 使用真实区域限制 CLM 的 Hilbert 伴随；在 ω 开、故可测的条件下，它就是实际零延拓。`regional_time_control_norm` 给 Kₙ 的 Bochner L² 范数精确等于原区域物理控制范数，而不是投影后较小的状态范数。`regional_time_control_supported` 给几乎每个时间的空间类属于 `supportedRegionSpace ω`，即补集限制算子的核；这是实际 a.e. 支撑，不是任意代表的逐点断言。

原 full P1 正交投影对任意 L² 初值强收敛：实际证明使用紧支光滑测试的 L² 稠密性、真实节点插值误差和正交最佳逼近。本批沿完整尾段搬运该极限，无 y₀ 光滑性或 H¹₀ 前提。指数终端由 Sₙ→∞与 d0>0衰减，投影收缩给统一前因子，因而真实物理终端范数趋零。X⊂H 的原范数精确相同，所以终端包含像亦在固定 H 中强趋零；没有将状态时间迹当作此离散终端极限的前提。

## 每个给定弱积点与同一连续状态

第二项首先保留第一个定理所选的同一 J、u、y。对任意 σ:ℕ→ℕ（允许重复），K_(σn) 的实际统一预算和闭支撑核资格给严格递增 χ 的弱子列，极限等于某个真实区域 Bochner L² 控制 v 的零延拓，且 ‖v‖≤sqrt(C)‖y₀‖。这表达整族重构的序列弱紧性，不要求 σ 本身严格递增。

识别零终态的分支则先量化任意严格递增 σ，再量化**任何给定** U 及 K_(σn) 对全部 Bochner 测试的弱收敛。`regional_control_of_weak_limit` 由同一个 U 的闭核成员身份取区域限制 v，返回真实零延拓 `K v=U`；其范数由零延拓等距及弱下半连续性控制。U 从未被重新选择。所得 v 与状态构造共用这个 U，而非另一个抽取出的控制极限。

调用 T210 时网格、势、控制和轨道统一运输到 σn+J。严格递增性给 `σn+J→∞`，所以 h/dt 的独立极限保留；原方程、初值、dt·M 条件和费用由同一家族 hall 字段给出，终态范数极限由原 hyN 沿 σ 保留。没有把这些条件重新作为本批外部输入。费用在这里从 K 的真实范数等式恢复为原 `controlNorm`。

已直接读取 T210 的实际 `full_p1_weak_control_limit_null_state`：它在 U 固定之后，从原方程内部得到完整 H¹₀ 时间预算，再选择一个 Y 和一个进一步状态子列，之后才量化全部有限测试。因此同一个 Y 满足全部原有限弱身份，U 的弱极限只沿进一步子列保留，并未重选。预算准确为 `stateTimeEnergyBound T M ‖y₀‖ (sqrt(C)‖y₀‖)`，允许依赖固定 T，没有误称 T 独立。

`DirichletNullControlState` 已展开核对：同一 q 在 `[0,T]` 连续、与同一 Y 的原 L² 值 a.e. 相等，且 q(0)=y₀、q(T)=0；同时对全部内部光滑时间测试满足实际 `StrongDual ℝ V` 的分布时间导数身份。其载荷真实配对为 U−Ay−bY，势仍是同一原 b；符号与原弱热方程一致。这些字段由有限弱身份、实际对偶导数及已证连续端点定理内部产生，既不假设 Y 已连续，也不读取任意 Lp 代表的端点。报告不额外声称弱解唯一性；本批也没有提升一般多面体或整条 P021。

## 固定依赖与本地证据

全文读取 T210 冻结报告 `df32e0ea1475520fba053f653a9b5ea06d83cb73:governance/reviews/T210-local-acceptance.md`（4/4 PASS，reviewed_at `2026-10-20T04:23:42+00:00`），读取 T174 报告的数学与量词核查，并直接重读本批使用的 BoxP1PhysicalControl、PhysicalObservationControl、PhysicalRefinement、P1WeakControlLimit、区域支撑/弱极限恢复、P1 初值收敛和真实零终态定义。

两新模块递归 Carleman 源闭包 **874** 文件，其中 **872** 个旧文件与基线 Git blob 全部相同。关键已接受闭包亦未变：BoxP1PhysicalControl 的 692 模块与 T174 `d93e52fc433c99d25a188effa0c451488098a451` 一致；PhysicalRefinement 的 285 模块与 T197 `3998fb3b4353576457a0773e69d587e5cf92e7e8` 一致；P1WeakControlLimit 的 611 模块与 T210 基线一致；RegionalWeakControlLimit 的 336 模块与 `714954acb8b017b09da56c71d4bd91b7d0ccffe2` 一致。不重复重建或审核无关旧闭包。

`/tmp/carleman-t211-local-evidence.json` 实际 checked/source SHA 均等于本报告 proof，source=local、status=PASS、finished_at=`2026-10-20T04:31:29.376250+00:00`；实际全库构建、公理命令均记录 exit 0。审核核查执行记录和固定源码关联，没有声称重新执行全库。

| 证据 | 独立核验 |
| --- | --- |
| `/tmp/carleman-t211-target-build.log` | 两新目标完成，4112 jobs；175 bytes，SHA256 `0b65f477fdfae6bb0bd00e056626c51b71cdcaac7d648c121f34ec7e3391499f`。 |
| `/tmp/carleman-t211-build.log` | 根目标完成，4223 jobs；80 bytes，SHA256 `40f9f8cd3148da07cd1bef8614030083d129ea57135f3235faecc842e4a67eba`。 |
| `/tmp/carleman-t211-axioms.log` | 0 bytes，stderr 为空。 |
| `/tmp/carleman-t211-p1-refinement-local-axioms.txt` | 3,052,508 bytes，SHA256 `9ea6adf39d7ff98ab2fc205c40cb105f55a6171892976358de15568d67f4603d`；末行 **9009** 项递归审计 PASS。 |
| `/tmp/carleman-t211-local-source-manifest.txt` | 107,148 bytes，SHA256 `950dcd719fe60d5f58a6c4a0594325428acfa2f1c4209ff387e6bda1aad426f9`。全部 tracked Lean 与三项构建配置共 **988** 项，独立枚举集合精确无重复，每项摘要与 proof Git blob 匹配。 |

两项展开类型各只依赖 `propext`、`Classical.choice`、`Quot.sound`；raw 的全部 3525 条显式依赖列表及 9 条无公理输出均无白名单外项。根导入、两项 `#check`/`#print axioms` 齐全；审计以 `privateToUserName` 遍历命名空间、递归 `collectAxioms` 覆盖私有和生成声明。Lean 4.35.0/compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`、mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 及治理协议与固定配置一致。

**签发：C227 在上述盒域 AUXILIARY 范围 PASS，无修复项。** 冻结全文及 reviewed_at，只单独提交本报告，不改数学、总台账或原稿，不 push。
