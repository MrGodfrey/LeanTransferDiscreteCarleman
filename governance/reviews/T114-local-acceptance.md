# T114 / C130 独立本机验收

- `checked_sha`: `a5c68e2aaa4da98efe42da31ed0c1da04ba99952`
- `base_commit`: `9e1f7ef800794f6fb560151f827fc7df51f7b10a`
- `reviewed_at`: `2026-10-19T04:43:21+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：原全部弱 H² jet 的实际内部卷积 Hessian 识别、平方可积性、原 field₂ 能量控制，以及同一光滑卷积的局部节点值和完整梯度误差。保留实际反射核支撑条件；不提升 P011 或完整 P1 插值，原文保持 **14/26**。

本 Agent 独立读取固定 git 对象的四个完整模块、11项实际展开类型及关键依赖，核对原稿 Section 6 的 P1 设置与 Step 2（`paper/main.tex:1462–1505,1523–1548`），并读取固定 AGENTS、PROJECT_OPERATIONS、state 协议、MATH_SPEC 和 T114 分析。执行者说明与 CI 未替代语义审查；后续 StrongL2Limit、StrongMollifierLimit、LocalStrongMollification 工作树增量、metadata 提交和变化中的 `.ci` 均未作为本批证明依据。

## 全部11项声明

名称省略公共前缀 `Carleman.`，模块均位于 `Carleman/Spatial/`。名单与固定 C130、T114 及 `/tmp/carleman-weak-hessian-declarations.json` 一致。

| # | 声明 | 固定模块及行 | 独立结论 |
|---|---|---|---|
| 1 | `tensorCoordinateBound` | TensorCoordinateNorm:14 | PASS；真实固定维数张量坐标重构 CLM 的算子范数加一。 |
| 2 | `tensorCoordinateBound_pos` | TensorCoordinateNorm:16 | PASS；对全部 d、k 正，包括空坐标情形。 |
| 3 | `tensor_norm_sq_le_coordinate_sum` | TensorCoordinateNorm:20 | PASS；实际多线性算子范数平方由全部有序坐标平方和控制。 |
| 4 | `SpatialTest.directionalKernel` | LocalHessianConvolution:18 | PASS；值确为 Dκ·e，真实光滑且紧支撑。 |
| 5 | `SpatialTest.directionalKernel_support` | LocalHessianConvolution:25 | PASS；导数核真实拓扑支撑包含于 κ 的拓扑支撑。 |
| 6 | `IsWeakSpatialDerivative.mixed_fderiv_convolution_local` | LocalHessianConvolution:35 | PASS；两条原局部弱链给实际 Dₑ₀(Dₑ₁(u⋆κ))，方向顺序和反射符号正确。 |
| 7 | `IsWeakSpatialDerivative.second_tensor_convolution_local` | LocalHessianConvolution:54 | PASS；实际 iteratedFDeriv 二阶张量在有序向量对上的值等于 z⋆κ。 |
| 8 | `mollified_hessian_energy_le` | MollifiedHessianEnergy:15 | PASS；同时证明真实 Hessian 平方可积及全部有序分量的 L² 能量界。 |
| 9 | `WeakSobolevJet.mollified_hessian_energy_le` | MollifiedHessianEnergy:67 | PASS；原完整弱 H² 自动供应两层链；零延拓等距，d² 项计数正确。 |
| 10 | `WeakSobolevJet.mollified_nodal_value_integral` | MollifiedH2NodalBounds:16 | PASS；同一实际卷积的真实顶点插值给 16 C(d,2)² d² D⁴ 阶平方误差。 |
| 11 | `WeakSobolevJet.mollified_nodal_gradient_integral` | MollifiedH2NodalBounds:33 | PASS；完整 Euclidean 梯度纤维误差给所述形状系数乘 C(d,2)² d² D²。 |

## 实际张量、方向顺序和局部弱身份

`tensorCoordinates` 通过全部标准基有序元组对真实 k 阶连续多线性映射求值。已读取 `IntrinsicSmoothClosure` 中该 CLM 的单射性和 `tensorReconstruction_coordinates`：重构是固定维数线性映射的连续左逆，确实将实际坐标恢复为原张量。第3项先逐坐标以平方和控制有限 Pi 范数，再使用重构算子范数和非负平方；故 C(d,k)=‖tensorReconstruction‖+1 只依赖 d、k，没有网格依赖的范数等价常数，也没有将算子范数错误等同于坐标平方和。

第4–7项的 κ 是真实全空间 `SpatialTest`。第4项使用 κ 的实际 Fréchet 导数构造方向核，其全空间光滑性、紧支撑及第5项支撑包含均有证明。这两项局部导数身份不要求核非负或单位质量；这些条件仅在后续能量界使用。

已展开 `DomainConvolution`：原 `IsWeakSpatialDerivative` 对全部 `SpatialTest S` 成立；`reflectedWithin` 构造实际 κ(x−y)，其支撑资格来自显式 `∀y∈tsupport κ, x−y∈S`。反射导数的负号与弱分部积分的负号相消，所得卷积交换身份为正号。Lp 零延拓仅保持在 **S 上** 的完整弱身份，并未断言跨 ∂S 后仍为全空间弱导数。

第6项先全局识别 Dₑ₁(u⋆κ)=u⋆Dₑ₁κ，再对这个真实光滑卷积取 Dₑ₀。第一条弱链 Dₑ₀u=v 用于方向核 Dₑ₁κ；其支撑包含保证反射测试仍合法。随后第二条弱链 Dₑ₁v=z 用于 κ，得到 Dₑ₀(Dₑ₁(u⋆κ))=z⋆κ。证明没有从仅在单点成立的局部身份直接求导，也没有预设弱状态的点态混合导数。

第7项由卷积的真实 C∞ 正则性取得 D(u⋆κ) 为 C¹，实际调用 `fderiv_clm_apply` 和 `iteratedFDeriv_two_apply`，得到

\[
\operatorname{iteratedFDeriv}_2(u\star\kappa)(x)[e_0,e_1]
=D(D(u\star\kappa))(x)e_0e_1=(z\star\kappa)(x).
\]

因此张量第一个槽位对应外层 e₀，第二个槽位对应内层 e₁，与原两条弱链实际调用一致。不是把自定义候选 Hessian 命名为导数。

## 真正的 Hessian 平方可积与原 field₂

第8项对任意可测 K，显式保留所有 x∈K 的反射核支撑条件。对每个有序 w:Fin 2→Fin d，令 Z_w=z_(w0,w1)⋆κ。已读取 `ConvolutionL2` 和 `MollifiedInterpolation` 的实际卷积积分、加权 Cauchy–Schwarz 及交换性证明：κ≥0、∫κ=1 给 Z_w 的真实 MemLp 和 ‖Z_w‖₂≤‖z_(w0,w1)‖₂，无对称核、径向核或额外衰减假设。

真实二阶张量的各坐标在 K 上逐点等于 Z_w；张量比较给 Hessian 范数平方的有限和可积控制函数。被积函数的可测性来自实际光滑卷积，`Integrable.mono'` 先建立真实可积性，然后才使用积分单调性、有限求和和 L² 收缩。因此结论是

\[
\mathrm{IntegrableOn}_K\|D^2U\|^2,\qquad
\int_K\|D^2U\|^2\le C(d,2)^2\sum_{w:\operatorname{Fin}2\to\operatorname{Fin}d}
\|z_{w(0),w(1)}\|_2^2.
\]

没有使用不可积积分的默认零值；K 无需预先有限体积，所需可积性由控制函数提供。

第9项直接接受原 `WeakSobolevJet d 2 (volume.restrict S) S` 的任意状态。值取真实 value，第一层取 `Sym.cons i nil`，第二层取 `Sym.cons j (Sym.cons i nil)` 的真实 field₂ 分量，随后仅作 L² 零延拓。原 `field_weak_derivative` 在 k=0、k=1 分别供应完整测试族上的弱链；不需要额外光滑代表、点态二阶导数或全空间 H² 延拓。

`zeroExtendLp_norm` 是真实 Lp 等距，`derivativeComponent_norm_le` 是 Euclidean 纤维坐标投影的范数界。每个有序二阶分量均由 ‖field₂u‖ 控制，而 `Fin 2→Fin d` 的基数恰为 d²。证明使用保守但合法的

\[
\int_K\|D^2U\|^2\le C(d,2)^2d^2\|\mathrm{field}_2u\|_{L^2(S)}^2.
\]

对称 jet 中的混合项在有序数组中重复出现是显式计数的一部分；没有漏掉 i≠j，也没有把对称多重指标范数和全有序 Hessian 范数声称为相等。d=0 时有序二阶数组为空，真实二阶张量也为零，不涉及除以 d。

## 同一实际卷积的节点值及完整梯度误差

第10、11项共同使用 U=(zeroExtendLp(value u))⋆κ 和同一 `simplexNodalInterpolant T (fun i => U(T.points i))`。T 是实际 d 维非退化单纯形，积分域为其真实闭凸包 K。所有顶点值均取自真实 C∞ 函数 U，未对原 L² 类直接取节点值。

已独立读取所调用的 `simplexNodal_smooth_h2_value_integral` 和 `simplexNodal_smooth_h2_gradient_integral`：两者以同一光滑函数的实际 Fréchet Hessian 平方积分控制值及全 Euclidean 梯度纤维误差。第10项保留 d≤3、D≥0、K 内所有点对距离≤D；第11项另保留真实内球 ball(a,r)⊆K、r>0 和 D≤γr。以 C=C(d,2)、F=‖derivativeOneFiber(d)‖，本批准确得到

\[
\int_K(U-I_TU)^2\le16C^2d^2D^4\|\mathrm{field}_2u\|_{L^2(S)}^2,
\]
\[
\int_K\|\mathrm{fiber}(DU-DI_TU)\|^2
\le(2^dd+128\gamma^2F^2)C^2d^2D^2\|\mathrm{field}_2u\|_{L^2(S)}^2.
\]

两个误差平方积分均为真实可积函数：U 光滑、插值实际仿射、K 紧。新的组合只以非负显式系数乘第9项的 Hessian 界，再作准确代数整理；没有丢失体积因子或一阶坐标。C、F 固定于 d，形状因子只含 γ，故常数先于 S、单元、状态和核选择，独立于核半径、核各阶导数大小和网格数。新的组合没有除以 D、d、Hessian 能量；合法 d=0、D=0 情形保留。

## 原文对应与尚未清偿的范围

原 P1 Step 2 对任意 v∈D(A)⊆H² 使用其连续代表的全网格节点插值，并进一步结合允许权比较、ℓK≈hK 和全域求和。本批准确清偿的是**内部光滑化的原弱 Hessian 控制**，使 C128/C129 的光滑局部值及梯度估计适用于原全部弱 H² 数据产生的真实卷积。

仍须明确三点：第一，`hinside` 对闭单元的每个点保留，是实质的内部光滑化可容纳条件，不能自动套用到接触 ∂S 的单元；对于支撑含0的常见核和开 S，边界顶点即不满足该条件。第二，右端 ‖field₂u‖ 是 **整个原 S** 上的范数，不是已证明仅取 K 上 Hessian 的局部估计。第三，本批节点数据是 U 的点值，尚未取极限得到原弱状态的连续节点代表、边界零值或全局 conforming 插值。

因此这些显式局部条件与所声称的 AUXILIARY 范围一致，未被隐藏为原完整 P1 的已清偿前提。不能据此宣称原 `eq:p1-interpolation`、`eq:p1-interpolation-energy` 的全部状态、边界及全允许权版本已经完成；N3、P011 和完整 `prop:p1` 仍待后续工作。

## 固定依赖、构建及公理

四个模块的 Carleman 导入闭包共113模块，除本批4个新增模块外，其余109模块与 base 逐字节不变。已进一步比较已验收版本：C128 `SmoothH2NodalError` 的97模块闭包相对 `c8377e5f743689641ab84d5049b4d0fb291d29f5` 不变；C129 `SmoothH2NodalGradient` 的101模块闭包相对本批 base 不变；`DomainConvolution` 的26模块和 `MollifiedInterpolation` 的48模块闭包相对 C089 `c99262c4a0d65a4d23f2efb57748bda490e971d7` 不变；`DirichletPoincare` 的33模块闭包相对 C090 `55dbf36858608cc7ff9300ef61430e18fa0bdadf` 不变。依赖验收记录见 [T112](T112-local-acceptance.md)、[T113](T113-local-acceptance.md)、[T073](T073-local-acceptance.md)、[T074](T074-local-acceptance.md)，本次另核对了它们在实际证明中的使用。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。Lean 固定4.35.0；mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。`Carleman.lean` 显式导入全部四模块。`tools/CheckAxioms.lean` 仅增加11项完整类型与公理输出；递归审计器与 base 不变，对包括私有辅助声明在内的全部 Carleman 常量运行 `collectAxioms`，只允许 propext、Classical.choice、Quot.sound。

独立读取固定 `/tmp/carleman-weak-hessian-target.log`：3287 jobs成功；`-full.log`：3841 jobs成功和6601声明递归审计PASS。固定 `-local-axioms.txt` 为 **1,968,611 bytes**，SHA256 **`685940ff51ac8f8723fd3181bc33f3eede6e7373933c7394bb07f007d26cb16e`**。逐一核对11项展开类型和公理；全文件2243条非空公理记录、8条无公理记录（含重复输出，共2247个不同名字）均仅有上述三项正常基础公理，无 sorryAx 或额外数学公理。递归审计的6601包含生成辅助声明，与显式输出数量是不同统计。

## 实际同 SHA CI 和原始产物

本 Agent 自行查询 [main CI 39200479416 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39200479416/attempts/1)。实际run为 main/push、completed/success，head SHA精确为本报告 checked_sha，最终更新时间 `2026-10-19T04:42:48Z`。三项job均 completed/success：state-check **117892231585**、lean **117892231713**、dashboard / snapshot **117893264067**；最后一项完成时间 `2026-10-19T04:42:47Z`。

同run原始artifact：`lean-ci-result` **12163855763**（归档491 bytes），`lean-declaration-evidence` **12163437525**（归档181,038 bytes），元数据 head_sha 均匹配。本 Agent 自行执行 `gh run download 39200479416`，分别下载至 `/tmp/carleman-weak-hessian-main-ci` 和 `/tmp/carleman-weak-hessian-main-axioms`。

实际 result.json 为537 bytes，SHA256 `084b0ed648be6fb44a644b83d3a13acd0710303d1ca6c33ae7102bd76095defa`；内容PASS，`checked_sha=source_head_sha=a5c68e2aaa4da98efe42da31ed0c1da04ba99952`，target Carleman，`finished_at=2026-10-19T04:41:26.470888+00:00`，ci_url与同run/attempt一致。远端使用 Lean4.35.0、Lean提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 及上述 mathlib pin。

独立逐字节比较 `-main-axioms/axioms.txt` 和固定本机副本：**完全一致，1,968,611 bytes，SHA256 `685940ff51ac8f8723fd3181bc33f3eede6e7373933c7394bb07f007d26cb16e`**。远端实际末行为6601项全声明递归审计PASS。原始文件的PASS与所有job最终成功均已分别核实。

## 验收决定

**C130：PASS，可升级为 REVIEWED，scope保持 AUXILIARY。** 11项声明的真实导数、顺序、支撑、可积性、原弱 field₂、完整梯度和核无关常数均通过独立核对，未发现需要修复的数学缺陷。同SHA三项CI和自行下载的原始证据已验证。

原弱状态连续节点代表、边界适配、局部化及全局允许权插值仍待；P011不提升，原文保持 **14/26**。本次仅新建此报告，未修改实现、台账、原稿或root导入，未commit/push。以上签发UTC固定；通知主Agent后冻结报告，不再改动内容或时间戳。
