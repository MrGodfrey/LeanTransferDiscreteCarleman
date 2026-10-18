# T031 — 原热尺度推论到物理观测与控制的独立验收

- checked_sha: `4223cdff025d68431b81dc2f3fb620e8bdc9ec6b`
- base_commit: `31d5e165a595849bc1c882523838aad69576b594`
- reviewed_at: `2026-10-18T16:52:30Z`（UTC；固定提交真实 CI 产物核验完成）
- reviewer: 独立数学验收 Agent `/root/accept_section3`，非 T031 执行者。
- target: T031 / C047；四个模块、全部 15 项显式声明。
- scope: **CONDITIONAL**。
- semantic_result: **PASS**。
- axiom_check: **PASS**（同 SHA 真实 main CI 的 3655 项递归审计和全部 15 项实际类型、公理输出逐项核对）。
- result: **PASS**；C047 可升为 REVIEWED/CONDITIONAL，P014/P015 不得提升。
- extra_hypotheses: `["具体P1的原数值条件与连续热Carleman估计仍待供应；本阶段从这些原始条件推出结论"]`。

独立读取固定提交四个新模块全部定义、证明体及实际 elaborated 类型，对照原 `paper/main.tex` 的 A/N 接口、Corollaries 2.2–2.3（599–631 行）、P1 的质量/载荷/控制定义（1485–1493 行）和 Section 7 物理观测与控制结论及证明。固定 MATH_SPEC 和 analysis 文件只用于明确阶段范围与定位，未用执行者说明代替源码核查。

## 结论与原文范围

本阶段正确地从已验收原 `OriginalForm.heat_scale_uniform` 提取真实 q³ 周期载荷 Carleman 估计，再把它供应给实际 L² 子空间的物理观测及 HUM 控制。最终 `conforming_heat_observation_control_uniform` 不再假定周期离散 CE 或物理观测结论；其实际剩余输入是固定原解析形式及正向域正则性，以及对允许 q 的 `ConformingHeatData`。

未发现数学或量词缺陷；正式同 SHA CI 门槛已完成，C047 可升为 **REVIEWED/CONDITIONAL**。**P014 / Theorem 7.2、P015 / Theorem 7.3 不得因此提升。** 具体 P1 网格、原加权近似/测试及统一常数、具体 Dirichlet 实现和连续热 Carleman 尚未供应；FD 的对角质量、重构和载荷是另一个尚未实例化的接口。本报告不把条件定理改称具体 P1/FD 结果。

## 完整热能量到实际周期载荷估计

热指数在已验收代码中准确为 `(m,c0,c1,o)=(1,3,1,3)`。`TransferGeometry.nodeEnergy` 是真实零阶状态项加全部非负导数项。`physical_cube_le_nodeEnergy` 调用 `zeroth_le_nodeEnergy`，只舍弃非负导数项，再以 `Real.rpow_ofNat` 将实指数 3 精确识别为自然数立方，得到

\[
dt\sum_i q_i^3\|\theta_iRz_i\|^2\le\mathcal E_{q,h,dt}(z).
\]

没有把全能量预先改成另一个较弱前提；原完整能量估计实际先由热尺度定理给出，然后取其零阶后果。参数 `hstate` 只是同一真实状态范数的识别，在最终几何里由定义等式供应。

`physical_load_eq_transfer` 精确识别 `dt∑‖θ_i f_i‖²`；`physical_observation_eq_transfer` 精确识别相同 q_i³、dt、观察时刻和观察映射上的有限和。载荷等式本身不依赖 q 幂，所以其实际类型省略未用 `hw`，是正确的参数省略。两条等式没有额外比较常数、少乘或多乘 dt，也没有把权放到错一格的时间节点。

`physical_load_carleman_of_transfer` 的中间前提明确是全方向、全周期状态/载荷的完整 transfer 结论。对每个实际 `D_-z+Az=Γf`，它构造 `Orientation.minus.difference` 的同一个函数等式，取 hce 的 minus 分支后应用上述三项结果。`PhysicalLoadCarleman` 内部仍全称量化所有 N 个周期状态 z 和真实 Lp 载荷 f；没有只证明截断轨迹的特殊情况。最终函数内部清偿这个中间 hce，因此它不构成最终隐藏的离散估计前提。

## 真实符合重构、质量伴随和载荷

`conformingReconstruction` 在真实 `X≤V≤Lp` 上取 `R=X.inclusion hX`、`J=X.orthogonalProjectionOnto`。`mass_adjoint` 使用实际投影内积公式证明 `⟨Jv,z⟩_X=⟨v,Rz⟩_H`，没有假定质量恒等式。`conformingReconstruction_RH` 确认重构到环境 H 后就是 x 的实际 Lp 包含。这里符合质量确实是原 P1 的一致 L² 质量；不将其套用于 FD 对角质量。

`conformingLoad` 的 Γ 为同一实际 J，普通 lift 为环境 Lp 上的恒等函数，JL=Γ 由定义给出。这对应原 P1 的 `F_h=H, Γ_h=J_h, L_h=Id`。真实 I=R 的右逆和所有权下相同元素的稳定性在 T030 已证明，物理组装实际使用；本批不要求加权正交投影收缩。原 transfer 的载荷版不需要另行调用残差版右逆。

`conformingWeightedState` 是真实 θ 乘法 seminorm 与 X 包含的复合。正定性使用已证明指数乘法几乎处处非零及 Lp 正定性，未把正定范数另设成未证假设。load/control 的环境 seminorm 也是实际 θ 乘法 L² 范数。`conformingHeatGeometry` 以同一 q、ρ、真实弱 Sobolev 导数字段和 P 表达式构造 `sobolevGeometry`，不是任意命名的标量能量。源文件中 hX、hD 等不影响几何自身的定义，所以实际 `conformingHeatGeometry` 类型省略这些参数；真正重构及原假设结构仍保留它们，没有丢失 X≤V 或域条件。

中间环境控制 `conformingAmbientControl` 的真实 Hilbert 伴随是 indicator_obs∘R，已有证明直接识别该算子；因此 `p.control(t)(Bstar x)` 是原区域加权观察的环境 Lp 表示。进入周期 CE 的这个观察与连续 A4 的 observation 使用同一个 obs。最终区域控制由真实 restriction/zero-extension 的伴随公式转换，未从某个抽象 Bstar 的名称推断 Hilbert 伴随身份。

## ConformingHeatData 的实际条件

该结构只有三个字段，已逐个展开其实际依赖：

| 字段 | 所保留的原假设及范围 |
|---|---|
| `allowed` | 原 `Section3.AllowedFamily`，对 ±ρ 与全部 `|τ|≤τStar` 提供 V/D(A) 保持、真实交换子、形式上界和强制性，即 A2/A3 所需数据；不包含解、误差或离散 CE。 |
| `numerical` | 已验收 `Section5.NumericalData` 在真实符合重构/载荷/观察上的实例：原刚度—缺陷等式、两符号全允许权的 N3/N4、ηA 的正/逆权缺陷界、重构双向界、提升界及区域观测界。这些是 N1–N5 所用字段，没有空间/时间误差结论或目标离散估计。 |
| `continuous` | 原连续 A4 对每个方向 s 和每个真实 `PeriodicWeakTrajectory` 的完整连续能量估计，右侧是实际 `s.sign*U_t+A U` 与区域观察。它没有 z、A_h、Γ、数值载荷或物理轨迹，绝非离散结论伪装。 |

原 A1 的 V、形式、关联域/算子由固定 `OriginalForm` 提供，hD 和 hell 是原完整 D(A) 的 H² 包含及正向椭圆界；没有反向椭圆界、额外边界条件或更小测试核心。ρ 仍用原内禀 `SmoothOnClosure`，最终另保留原 a.e. 严格负性。现有 `OriginalForm` 与原 V/D/A 的识别沿用已验收依赖，此处没有修改或更换解析算子。

该结构的存在仍必须由调用者证明；它没有为任意 X、A、mesh 自动构造 N3/N4，也没有证明连续热 A4。最终对每个数值实例要求对所有 `PhysicalQClass w g.period β qc` 且 w.max≤Smax 给出同样常数、同样 defect/errors 的数据；不能为每个权重新更换误差率或共同界。这与原对整个允许权族的统一假设一致。原完整 qclass 的值、真实一二阶导数和 0/1/2 阶迹仍保留；只把 `.toRegularity` 交给原时间估计是满足其所需较弱接口，不是删掉最终 qclass 前提。

以全局光滑 `PhysicalQClass` 描述本次实际正弦权不向原实例增加限制：原权假设对 C² 周期权成立时也覆盖这些权，实际物理构造已经证明正弦代表全局光滑。输出对任意原物理轨迹成立；周期性只施于辅助 q 和截断后 z。

## 原尺度与常数量词

`conforming_heat_load_uniform` 实际调用 `a.heat_scale_uniform`，完整供应 r、A、defect、Γ/lift、真实 state/load/control 及正定性、同一个 g/w、`N.allowed`、`N.numerical` 和 `N.continuous`。取返回的载荷结论 `he.1` 后，所有几何识别参数都由 rfl 供应，得到真正的 `PhysicalLoadCarleman`。

原近似阶恰为 `aE≤Cap*h`、`a0+ηA≤Cap*h²`，由 m=1 的代数化简转接；ηA 没有被忽略或强制设零。已验收原尺度证明内部控制误差和缺陷小性、δx≤δnum 等条件，本批不增加新耦合或自行假定这些吸收结果。热尺度严格是

\[
S_{\max}=\kappa\min\{h^{-4/5},dt^{-2/5}\},
\]

实指数未变。`physicalMeshScale_pos` 由正 κ、h、dt 的真实 rpow 正性给 Smax>0。h0≤1、Δ0≤1、正 κ/h0/Δ0/CCE 全部来自同一个已验收尺度输出。

常数的实际顺序是：先固定 Ω、原形式/域、ρ、P、obs、Cap/Creg 和解析数值共同界，再选择 κ、h0、Δ0、CCE；这些常数先于 X、A、defect、T/g、w、h、errors 及所有状态载荷。随后用同一个前置 CCE 选择 Cb、d0，仍先于 T/M。最后对每个 T>0、M≥0 选择 Cphys(T,M)，它先于有限维 X、hX、网格、mesh、A、defect/errors、全权数据、势族 b、伴随轨迹及初值。

最终保留 g.period=T、h≤h0、dt≤Δ0、dt≤T/12、dt*M≤1/2 和原 `16qb≤Smax≤qb*T/(4dt)`。qb 仍是 `Cb(qc+T⁻¹+M^(2/3))`，M=0 有效；Smax 直接代入载荷供应的 w.max 上界，并非另一个自由参数。Cb 可以依赖预先固定的 CCE，却不依赖 T/M 或具体离散数据；未发生常数量词交换。物理 Cphys 按原文允许依赖 T/M，不能被误读成对 T 一致的物理观测常数。

## 真实物理观测与 HUM

最后入口对每个所需完整 PhysicalQClass 权调用 `conforming_heat_load_uniform`，以 `.toRegularity` 和同一个 Smax 供应原尺度条件。它把得到的 CE 交给已验收 `conforming_observation_control_uniform`；该上游已内部证明 R=I 的质量/加权右逆常数 1、Γ 兼容、原乘法势的实际自伴性/范数、q 构造、潜势吸收、端点余项和初值恢复。因此最终不再遗留 T030 的周期离散 CE 前提。

潜势确实是 `Γ(b_i*Rx)` 的正交投影，b_i 是真实 a.e. 有界实乘法场，`b_i.bound≤M` 给其算子范数≤M。没有要求乘法保持 X、各势交换、b_i 非负或额外正则性。A 的非负和自伴在最终显式保留；在具体一致 P1 实例中还需从原刚度定义供应。

最终 B 为 `conformingRegionControl`，控制空间是
`Lp ℝ 2 ((volume.restrict Ω).restrict obs)`，在原 obs⊂Ω 情形正是 L²(obs)。其真实 Hilbert 伴随为区域限制复合包含，观测平方和使用 N 个 `p i.castSucc`，即原 `p^(n−1)`，加权因子准确为 dt。末项为真正的 p^N，并保持 `exp(−2d0 Smax)‖p^N‖²`。不是只对构造解或某个低频子空间断言观测；所有 `Fin(N+1)→X` 满足实际 `.adjoint` 方程的 p 都覆盖。

HUM 对每个 y0 实际给出区域 L² 中的 N 步控制 u 和完整 N+1 节点前向解 y，满足原 `ForwardEquation` 及 y⁰=y0。输出控制预算 `sqrt(Cphys)‖y0‖`、终值预算 `sqrt(Cphys)exp(−d0 Smax)‖y0‖`，控制范数为原 `sqrt(dt∑‖u_i‖²)`。原文通用 C(T,M) 可统一放大为 max(Cphys,sqrt(Cphys))，所以没有常数或指数弱化。有限维只要求状态 X；实际 L² 控制空间不被错误限制为有限维。既有物理解唯一性也保证此 y 是所给控制对应的真实解。

底层 transfer 保留两方向与全周期状态；物理 Section 7 按原证明只取 minus 辅助方向，最终分别给原反向伴随和前向控制方程，不产生额外周期物理解限制。

## 全部 15 项声明

以下每项均已直接阅读固定源码、核对实际展开类型及递归公理。每项仅依赖 `[propext, Classical.choice, Quot.sound]`。

| # | 声明 | 独立结论 |
|---|---|---|
| 1 | `Carleman.Physical.physical_cube_le_nodeEnergy` | PASS：仅舍弃非负导数能量，真实 q³ 与完整零阶项一致。 |
| 2 | `Carleman.Physical.physical_load_eq_transfer` | PASS：相同实际 Lp 载荷和 dt 有限和恒等式。 |
| 3 | `Carleman.Physical.physical_observation_eq_transfer` | PASS：真实观察映射、q³、相同节点和范数恒等式。 |
| 4 | `Carleman.Physical.physical_load_carleman_of_transfer` | PASS：取完整全方向 transfer 的 minus 分支，全状态/载荷。 |
| 5 | `Carleman.Physical.conformingReconstruction` | PASS：真实包含 R、正交 J 和已证明质量伴随。 |
| 6 | `Carleman.Physical.conformingReconstruction_RH` | PASS：环境重构就是同一 Lp 元素。 |
| 7 | `Carleman.Physical.conformingLoad` | PASS：原投影 Γ、普通恒等 lift、JL=Γ。 |
| 8 | `Carleman.Physical.conformingWeightedState` | PASS：真实空间乘法 seminorm 复合包含。 |
| 9 | `Carleman.Physical.conformingWeightedState_definite` | PASS：实际指数非零与 Lp 正定性。 |
| 10 | `Carleman.Physical.conformingHeatGeometry` | PASS：同一权、弱导数、完整热能量和区域观察。 |
| 11 | `Carleman.Physical.ConformingHeatData` | PASS / CONDITIONAL：只有原 A2/A3、N1–N5 所用数据和连续 A4，无离散 CE 或目标观察字段。 |
| 12 | `Carleman.Physical.conforming_heat_load_uniform` | PASS / CONDITIONAL：内部调用原热尺度推论，准确 h/dt 指数和先置常数。 |
| 13 | `Carleman.Physical.physicalMeshScale` | PASS：原 κ min(h^(−4/5),dt^(−2/5))。 |
| 14 | `Carleman.Physical.physicalMeshScale_pos` | PASS：正参数下真实实幂与最小值正性。 |
| 15 | `Carleman.Physical.conforming_heat_observation_control_uniform` | PASS / CONDITIONAL：内部供应周期 CE，输出真实区域观测、HUM 控制及全前向解，剩余原假设明确。 |

模块对应：1–4 为 [PhysicalTransferGeometry](../../Carleman/Control/PhysicalTransferGeometry.lean)，5–11 为 [ConformingTransferData](../../Carleman/Control/ConformingTransferData.lean)，12 为 [ConformingHeatTransfer](../../Carleman/Control/ConformingHeatTransfer.lean)，13–15 为 [ConformingHeatControl](../../Carleman/Control/ConformingHeatControl.lean)。

## 固定版本、依赖与构建

沿用已读且仍有效的根 AGENTS、PROJECT_OPERATIONS 和 state 证据协议，本次读取固定 MATH_SPEC T031 和状态记录。基线至本次提交，原稿和既有数学模块未变；数学新增只有四个模块及 root 导入。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

主要已验收依赖为 [T023 原尺度推论](T023-local-acceptance.md)、[T030 真实区域控制接口](T030-local-acceptance.md) 及其物理观测/HUM 链。本次另直接阅读 `HeatScaleUniform`、`ScaleUniform`、`OriginalData`、`AllowedFamily`、`SobolevGeometry`、`Geometry`、`PhysicalLoadCarleman`、`PhysicalObservationUniform`、`ConformingPhysicalOperators/Observation/Control`、`ConformingRegionControl` 和 `RelaxedControl` 的实际定义与调用，确认本次实参真实满足接口；没有仅凭旧报告或名称通过。

`/tmp/carleman-original-physical-full.log` 记录 `Build completed successfully (3509 jobs).` 和 `Axiom audit passed for all 3655 Carleman declarations.`。固定本机公理副本 `/tmp/carleman-original-physical-local-axioms.txt` 为 1066719 字节，SHA256 `aeba0c8a613abd65d979180577bca0cb57c50b8d8698acaa68ae8492c0731114`。全部 15 项名称、顺序与固定 C047/T031 和 `/tmp/carleman-original-physical-declarations.json` 一致，实际类型和递归公理均齐全。最终声明的公理列表在输出中换行，已按完整列表读取，仍恰为三项标准基础公理。

固定 `tools/CheckAxioms.lean` 对 15 项显式执行 `#check @...` 和 `#print axioms`，再遍历包含私有声明的全部 Carleman 常量递归 `collectAxioms`，仅允许这三项正常基础公理。结构生成字段也在全局检查中；无 sorryAx 或未证明数学公理。根 `Carleman.lean` 导入四模块。

正式证据已核验：实际读取 [main CI 39146586608 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39146586608/attempts/1) 的下载产物 `/tmp/carleman-original-physical-main-ci/result.json`，确认 `status=PASS`，`checked_sha=source_head_sha=4223cdff025d68431b81dc2f3fb620e8bdc9ec6b`，目标 `Carleman`，`finished_at=2026-10-18T16:49:38.198461+00:00`。Lean 为 4.35.0（提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`），mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原始 result 文件 SHA256 为 `ced9f84ef9ba964868fa990391f4f5378a0efa23229fdaaa09c79af0bac5e818`。

同次正式 `/tmp/carleman-original-physical-main-axioms/axioms.txt` 为 1066719 字节，SHA256 `aeba0c8a613abd65d979180577bca0cb57c50b8d8698acaa68ae8492c0731114`。已实际逐字节比较确认它与锁定本机副本相同，并再次核对 15 项类型及全部递归公理输出；每项仍仅三项标准基础公理，全局末行确认 3655 声明审计通过。正式结果绑定同 SHA 的这些远端原始产物，不使用后续工作树或其他运行的结果。

## 当前验收结论

所声明条件蕴含的数学语义、全部 15 项声明、递归公理审计及同 SHA 真实 main CI 均 PASS，没有待修复项。可把 C047 升为 REVIEWED，但必须保留 CONDITIONAL 及上述具体原假设未供应的记录。P014/P015 保持未完成；具体实例及连续热 CE 需要后续独立验收。

本次只新增本报告，未修改数学证明、root、论文、台账或覆盖表，未 commit/push。
