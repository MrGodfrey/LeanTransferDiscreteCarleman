# T230 / C246 独立本机验收

- checked_sha: `721b761224ad1b6425466bc956417ddce7f41908`
- mathematical_base: `d1dabe5404212ce3dd399028a79233e3da4e324b`
- reviewed_at: `2026-10-20T06:39:08+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，17/17 显式声明（15 定理、2 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；有限严格半空间交的非空、开凸、紧内含、单调穷竭与真实正则水平集数据。本批不提升 P023 或原文覆盖。**

已完整读取固定 `Carleman/Geometry/HalfspaceSmoothExhaustion.lean`、17 项 raw 完整类型及公理记录、分析/MATH_SPEC/台账、原稿 `paper/main.tex:2659–2665`，并核对实际使用的凸性、指数微分、子水平集和 proper 空间紧性工具。原 Corollary A.2 的结论是一般凸多面体 Dirichlet Laplacian 的完整 A1–A3；本批只提供其凸域正则性证明路线的一项几何准备。没有把几何穷竭等同于内域或全域 H² 正则性，也不对另行验收的 T229/P022 作状态提升。

## 实际对象、量词与数学核对

令 `Ω={x | ∀i, bᵢ<ℓᵢx}`，其中指标类型有限，ℓᵢ 是原实范数空间上的实际连续线性泛函。定义严格使用
`gₙ(x)=Σᵢ exp((n+1)(bᵢ−ℓᵢx))` 和 `Uₙ={gₙ<1/2}`。原偏移 bᵢ 全部保留，不限于过原点的半空间。最终定理仅增加原 Ω 的有界性、一个严格内点 c 和 `ProperSpace E`；后者是原有限维欧氏情形的正常紧性条件。没有输入光滑定义函数、边界非退化、穷竭资格、不可冗余面表示或特定法向量归一化。

1. **实际 C∞ 与凸性。** 仿射表达式、真实 exp 的光滑链式法则及有限求和给全空间 `ContDiff ℝ ∞ gₙ`。凸性对任意非负 a,c 且 a+c=1，逐项应用实指数凸性，并使用 ℓᵢ 的真实线性和偏移项的精确恒等式；不是把 gₙ 的凸性设成字段。连续性给严格子水平集开放，凸函数的严格子水平集给 Uₙ 凸。没有使用严格凸性或 Hessian 正定等较强前提。
2. **整个闭包严格落在 Ω。** 连续性先给 `closure Uₙ⊆{gₙ≤1/2}`。每个指数项非负且不超过总和，所以 `exp((n+1)(bᵢ−ℓᵢx))≤1/2<1`。由 n+1>0 得每个严格不等式 bᵢ<ℓᵢx，故闭包落在原开域 Ω，不仅落在闭半空间交。Ω 有界使该闭包有界；闭集与 proper 空间的真实 Heine–Borel 定理给紧性。没有在一般无限维空间中误用“闭且有界即紧”，也没有宣称所有 n 有同一个边界距离下界。
3. **单调与真实全覆盖。** 对 x∈Uₙ，上一项先证明全部 bᵢ−ℓᵢx<0；m≥n 时乘以更大的 m+1 使指数逐项变小，因此 Uₙ⊆Uₘ。此结论不要求 gₙ 在全空间随 n 递减。对任意 x∈Ω，各项等于 `exp(bᵢ−ℓᵢx)^(n+1)`，其底数严格处于 (0,1)，故逐项趋零；有限求和给 gₙ(x)→0。由阈值 1/2 的正性推出最终进入 Uₙ，两个方向给并集精确等于 Ω。既不扩大为闭包，也不遗漏靠近原边界的内点。
4. **真实 Fréchet 导数及支撑不等式。** 导数由实际 exp 链式法则逐项得到 `Dgₙ(x)=Σᵢ exp((n+1)(bᵢ−ℓᵢx))·(−(n+1)ℓᵢ)`；负号、n+1 和每项权重均正确。支撑不等式 `gₙ(x)+Dgₙ(x)(y−x)≤gₙ(y)` 直接由 `1+t≤exp(t)`、正指数因子及 `exp(a+b)=exp(a)exp(b)` 推出；使用的是同一个 gₙ 的 `fderiv`，不是额外导数字段或仅形式上的梯度。
5. **全部边界点的正则性。** 对 x∈frontier Uₙ，闭包包含给 gₙ(x)≤1/2；开放性使 frontier 与 Uₙ 不交，给 gₙ(x)≥1/2，所以等号成立。若已有 c∈Uₙ 且 Dgₙ(x)=0，支撑不等式取 y=c 会给 `1/2≤gₙ(c)<1/2`，矛盾。因此全部边界点的真实 Fréchet 导数非零。没有假设任意单个 ℓᵢ 非零、法向量独立或边界已经光滑；冗余与重复半空间不影响证明。
6. **同一非空尾段与最终量词。** 最终存在定理先从原严格内点 c 的最终进入性取 N，再固定 `g(n)=g_(N+n)`、`U(n)=U_(N+n)`。单调性使同一个 c 属于全部 U(n)，其余光滑、凸性、紧闭包与内含性质沿同一尾段传递。若任意 x 在原第 k 项中，k≤N+k 保证 x 在尾段第 k 项中，故舍去有限前段不损失覆盖；每个 n 的边界正则性都使用同一个 c。N 由原几何和 c 选取，不涉及载荷、时间、网格或状态；存在量词没有将目标性质假设为真。
7. **边界情形与精确范围。** 初步定义、单调、闭包包含和并集身份允许 Ω 为空；最终非空穷竭定理明确要求一个严格内点，不宣称空域存在非空内域。有限指标不要求非空，空指标时 gₙ=0、Uₙ=全空间，边界正则性为空边界上的真命题；最终紧性仍受原 bounded/proper 假设约束，零维情形没有矛盾。正则水平集的定义函数数据已真实构造，但本批没有构造隐函数定理给出的局部光滑边界坐标，也没有证明内域解 H² 正则性、凸域统一 Hessian/Miranda–Talenti 界或完整 P023。

## 全部声明逐项结论

以下名称统一带前缀 `Carleman.`；源码行均在固定 `HalfspaceSmoothExhaustion.lean`，raw 行在本批固定审计文件。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 15 / 41710 | `halfspaceExpSum` | PASS；真实有限指数和，含原全部偏移。 |
| 18 / 41714 | `halfspaceSmoothInner` | PASS；同一函数的严格 1/2 子水平集。 |
| 21 / 41718 | `halfspaceExpSum_contDiff` | PASS；全空间实际 C∞。 |
| 25 / 41722 | `halfspaceExpSum_convex` | PASS；全空间真实凸性。 |
| 40 / 41726 | `halfspaceSmoothInner_open` | PASS；由实际连续性给开放性。 |
| 44 / 41730 | `halfspaceSmoothInner_convex` | PASS；真实严格子水平集凸性。 |
| 48 / 41734 | `halfspaceExpSum_le_half_mem` | PASS；非严格总和上界推出全部严格半空间资格。 |
| 60 / 41738 | `halfspaceSmoothInner_closure_subset` | PASS；整个闭包位于原开域。 |
| 68 / 41742 | `halfspaceSmoothInner_mono` | PASS；完整 n≤m 的内域包含。 |
| 80 / 41745 | `halfspaceExpSum_tendsto_zero` | PASS；每个原内点的真实数列极限。 |
| 89 / 41749 | `halfspaceSmoothInner_eventually_mem` | PASS；每个内点最终进入。 |
| 94 / 41753 | `halfspaceSmoothInner_exhaustion` | PASS；全部并集精确等于原 Ω。 |
| 105 / 41757 | `halfspaceSmoothInner_compact` | PASS；在明确 proper/有界前提下真实紧闭包。 |
| 111 / 41762 | `halfspaceExpSum_hasFDerivAt` | PASS；完整真实 Fréchet 导数与负号。 |
| 121 / 41766 | `halfspaceExpSum_support` | PASS；同一函数/导数的真实支撑不等式。 |
| 135 / 41771 | `halfspaceSmoothInner_boundary_regular` | PASS；有内点时全部边界点的值与非零导数。 |
| 155 / 41778 | `exists_halfspace_smooth_exhaustion` | PASS；同一明确尾段同时满足全部目标性质。 |

## 固定依赖和本地证据

新模块的 Carleman 导入闭包共 **30 文件**，其中 **29 个旧文件**相对数学 base 的 Git blob 全部不变。已读直接导入 `FiniteHalfspaceFaces`；本批证明本身直接使用 mathlib 的有限和、指数、凸性、微分及拓扑工具，未调用旧的边界几何定理来假定本批结论。检查的 mathlib checkout 无修改，提交与 lock 一致为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；Lean 固定 4.35.0，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。根导入和全部 17 项显式 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t230-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof；finished_at=`2026-10-20T06:37:00.160791+00:00`。`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 的真实执行记录均为 exit 0。
- `/tmp/carleman-t230-local-source-manifest.txt`：**1027 项、111418 bytes**，SHA256 `87aaabbd494a75650f84a0ddc802856fd374138082c9e840e790bcb4c02ad703`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及全部条目的 Git blob 摘要逐项匹配。
- `/tmp/carleman-t230-target-build.log`：**3054 jobs** 成功，115 bytes，SHA256 `03fb13f63eb762feb322c42ff7bd857664656ef57f9bae26f8487bafbd73d1d2`。`/tmp/carleman-t230-build.log`：**4264 jobs** 成功，80 bytes，SHA256 `e35f8bd2730082c7a2d6b916eb910fb09f1c155ecaae3d0ad4f951011e5e8008`。`/tmp/carleman-t230-axioms.log` 为 0 bytes。
- `/tmp/carleman-t230-smooth-exhaustion-local-axioms.txt`：**3209081 bytes**，SHA256 `80f71dea6d886e077281017c10d507494b902f96bbe408c41b131bf5dea13a0a`，与固定证据摘要一致。全部 **3765 个显式公理记录**只含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理；17 项完整类型和公理记录逐项核对。全命名空间 `privateToUserName`/`collectAxioms` 白名单递归循环不变，末行确认 **9554 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿与基线逐字节相同，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。按简化协议读取并核对固定本地执行证据，未重复构建或检查远端 CI/看板，未将执行者说明替代数学审核。

无修复项。接受本批 **AUXILIARY 几何穷竭与正则水平集数据**；内域/全域 PDE 正则性与完整原命题仍须各自证明和验收。本报告正文及 reviewed_at 冻结后只单文件提交，不改实现、台账、原稿或其他报告，不 push。
