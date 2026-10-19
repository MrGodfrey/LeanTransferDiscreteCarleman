# T083 / C099 独立本机验收

- `checked_sha`: `4e697929d6afc9043f0a20caf093a0d62a33963d`
- `base_commit`: `59452751f05398e3446ed5305638a1e20dc89061`
- `semantic_checked_at`: `2026-10-19T00:14:21+00:00`
- `reviewed_at`: `2026-10-19T00:17:06+00:00`
- `result`: **PASS**；固定版本语义与同 SHA 远端证据均通过。
- `axiom_check`: **PASS**；远端原始产物与固定本机副本逐字节一致，5792 项递归审计通过。
- `scope`: **AUXILIARY**；原允许权下、全部原 H²∩H¹₀ 状态的局部边界仿射逼近。原文完成数维持 **13/26**。

直接读取固定提交四模块全部 9 项实际声明、证明、完整展开类型与关键依赖，对照 `paper/main.tex:291–304`、Section 6 Cartesian 定义（1634–1640）、Appendix B 的 B.1（2803–2835）和 B.2 证明（2841–2869），以及 `governance/analysis/T083-weighted-local.md`。数学判断独立于执行者报告和 CI；后续工作树代码不计入本次范围。

## 全部 9 项声明

名称均加前缀 `Carleman.`，位置相对于固定提交的 `Carleman/Spatial/`。

| # | 声明 | 源码位置 | 独立核查结论 |
|---|---|---|---|
| 1 | `BoundedMultiplier.onSubdomain` | `LocalWeightedNorm.lean:14` | PASS；保留同一实际权函数和 bound，以限制测度单调性供应真实可测性和 a.e. 有界性。 |
| 2 | `BoundedMultiplier.onSubdomain_map` | `LocalWeightedNorm.lean:22` | PASS；对任意标量或向量 L² 场，实际乘法与限制在 Lp 类中相等，全部代表身份在较小域共同 a.e. 成立。 |
| 3 | `BoundedMultiplier.onSubdomain_seminorm` | `LocalWeightedNorm.lean:32` | PASS；左侧局部乘权范数恰为原全局乘权场的局部限制范数。 |
| 4 | `BoundedMultiplier.seminorm_le_anchor` | `LocalWeightedNorm.lean:39` | PASS；真实 a.e. 比较推出 ‖wu‖≤Ws‖u‖，适用于一般实赋范空间值字段。 |
| 5 | `BoundedMultiplier.norm_le_seminorm_anchor` | `LocalWeightedNorm.lean:47` | PASS；s>0 及 s≤W|w| 推出 ‖u‖≤(W/s)‖wu‖，除数方向正确。 |
| 6 | `weighted_dirichlet_h2_local_boundary_affine` | `WeightedLocalBoundaryAffine.lean:13` | PASS；同一原弱残差的值、全梯度与局部 Hessian 使用双向权比较，s 精确抵消，C=W²B 先于全部域、盒、权和状态。 |
| 7 | `coordinateBox_diameter_bound` | `BoxAllowedComparison.lean:13` | PASS；任意端点盒改写为正侧长真实物理盒，给实际 Euclidean 距离≤dL，含 d=0。 |
| 8 | `allowedWeight_box_comparison` | `BoxAllowedComparison.lean:21` | PASS；真实允许权在 hq≤1 的盒内双向可比，W=exp(Ldκ)，与 q、τ、η 的两个符号及周期统一。 |
| 9 | `allowed_weight_dirichlet_h2_local_boundary_affine` | `AllowedLocalBoundaryAffine.lean:15` | PASS；内部选固定轮廓 Lipschitz 常数、权比较常数及正锚点，对全部原 H²∩H¹₀ 状态供应真实局部加权误差界。 |

## 原文定位和范围

原 B.2 对每个 v∈H²(Ω)∩H¹₀(Ω)、每个允许 σ 且固定时刻 hq≤1，最终控制实际 `v−Q_hv` 的全域加权 L² 与梯度误差。其证明先在 B_K 取 B.1 的边界仿射 p_K，利用 Q_h 的矩再现和局部稳定性控制 K 上的重构误差，再由每个 B_K 上的权比较及有限重叠求和。

本批严格完成其中的局部加权边界仿射步骤：输出实际 p 和同一原域限制上的弱 H¹ 残差 r，其 a.e. 值是原全局 u−p，且

`‖σr‖L²(B)+h‖σ∇r‖L²(B) ≤ C h² ‖(σD²u)|_B‖L²(B)`。

p 在任意选定的、位于原物理边界上的整个闭面处处为零。右端保留原全局 u 的真实加权 Hessian 的局部范数；没有用全域 Hessian 或完整 H² 范数替代，也没有调用预设的加权逼近估计。

原 FD 域是轴平行 Cartesian 矩形，固定开、凸且闭包紧；原轮廓在闭包 C∞。最后入口的开、凸、紧闭包和 C¹ 条件均由该原场景供应。这里只对该已声明场景验收，不将这个入口声称为任意非凸 Lipschitz 域上的新结论。边长双向比较 `h/κ≤b_i−a_i≤κh` 表达原 B_K 的尺度和有界长宽比；κ 固定在选择任何盒之前。

本批没有定义或证明原实际 Q_h 的矩条件、仿射再现、局部作用稳定性、K 上的重构残差身份、活动节点星或全域有限重叠求和。因此 **C099 可按 AUXILIARY 验收，但完整 B.2/P026 和 FD/P012 不得提升**；已验收 B.1/P025 不受影响，原文仍为 13/26。

## 真实乘权、限制与锚点抵消

`BoundedMultiplier.map` 使用实际函数 `x ↦ w.value x • u x` 的 MemLp 类；`seminorm u=‖w.map u‖`。对实数和导数字段，其平方是实际 `∫|w|²‖u‖²`，相应密度已证明可积。`DerivativeFiber` 的完整 Euclidean 字段用于梯度和 Hessian，没有指定任意能量代替。

`subdomainLp hTS u` 由较小限制测度上的真实 MemLp 构造，a.e. 等于原代表；`onSubdomain` 保留完全相同的权函数。新交换律把全局乘权身份及两个限制身份都拉到同一较小测度，再由 Lp.ext 证明类相等。因此 `onSubdomain_seminorm` 是精确身份，右端确实为 `(σ D²u)|_B`，没有换成独立的局部 Hessian 数据。

两条锚点引理直接调用实际乘权的点态比较定理。上界用 |w|≤Ws 与常数权 1 得 `‖wu‖≤Ws‖u‖`；下界用 s>0 将 s≤W|w| 等价改写为 `1≤(W/s)|w|`，得 `‖u‖≤(W/s)‖wu‖`。没有假定权倒数全局有界，也没有使用状态点值；字段值可以任意变号。

令 B₀=B₀(n,κ)>0 为 T082 对同一 p、r 的真实未加权局部常数。代码先选 `C=W²B₀`，再引入全部物理数据。对 r 的值和全梯度分别使用同一个正向因子 Ws，以 h≥0 相加，得到

`‖wr‖+h‖w∇r‖ ≤ Ws(‖r‖+h‖∇r‖) ≤ Ws B₀h²‖D²u|_B‖`。

对原二阶字段的局部限制应用反向界，再用上述交换律，右端变成

`Ws B₀h² (W/s)‖(wD²u)|_B‖ = W²B₀h²‖(wD²u)|_B‖`。

最后等式使用 s>0 的非零性精确消去 s；未除以任一状态或 Hessian 范数。不存在依赖于局部锚点的剩余常数。估计的是原论文的 `σ∇r`，并未误换为 `∇(σr)`，所以无需额外的权导数项。

## 全部原 H²∩H¹₀ 状态和物理零迹

已直接复核 T082 实现 `SubdomainContinuity`、`CoordinateBoxTraceContinuity`、`DirichletBoxFace`、`DirichletLocalAffine`，以及其实际 `SubdomainRestriction`、`DirichletSpace` 定义。`WeakSobolevJet.restrictSubdomain` 限制全部字段和各分量；任意较小域 SpatialTest 由同一光滑函数和支撑包含提升到原域。测试及其导数在较小域外为零，故真实积分分部身份可限制，不依赖附加延拓或局部弱方程假设。

H¹₀ 的 jet 空间是全部原紧支光滑测试 jet 的线性包在真实完整弱 H¹ 图拓扑中的闭包。`dirichletSubspace` 为其真实 value 像；对开 S，弱导数唯一性保证同一 value 的原一阶截断也属于这个 jet 闭包。因此输入 `value u∈dirichletSubspace S` 恰覆盖原全部 H²∩H¹₀ 状态，未从这个条件另取无关的便利梯度。

局部面迹是已证明的真实 L² 弱迹。限制是图范数连续的，面迹由真实物理迹不等式提升为连续线性映射，二者复合的核闭。原测试的支撑在 S 内，而指定闭面在 `frontier S⊆Sᶜ`；其真实连续代表在该面为零，实际弱迹与该代表面限制一致。闭核因此包含整个 H¹₀ 闭包。这一过程内部推出原 u 限制的一阶零迹，不是新增用户前提或边界点值假设。

限制与截断在全部字段上交换，故 B.1 对原二阶 jet 限制可直接应用。未加权残差已是原限制减实际仿射 jet；T083 保留这同一 p、r，其值等式用同一个限制 a.e. 身份连接到原全局 u。r 的弱 H¹ 类型及弱导数唯一性识别其 field₁ 为该实际差的梯度。原状态无需光滑、连续代表、点值、全空间弱延拓或预给局部零迹。

## 原允许权族、量词和退化情况

`SpatialProfile.scaled` 的实际 multiplier 为 `q(t)^τ exp(ηρ(x)q(t))`。实数 |η|=1 覆盖原 θ 和 θ⁻¹ 两个符号；`q(t)>0` 使乘子在全部点严格为正，任意实数 τ 的实幂均合法。比较依赖中的实际比值恒等式为

`σ(x)/σ(y)=exp(η(ρ(x)−ρ(y))q(t))`，

其中 q^τ 精确抵消，未以依赖 τ 或 q 的上界代替。对 x,y∈B，由真实包含 B⊆S 把点转为 closure S 成员，实际 Euclidean 盒直径界给 `|ρ(x)−ρ(y)|≤Lnκh`。于是 hq(t)≤1 推出双向比较系数 `W=exp(Lnκ)`；倒向通过交换同一对点获得，没有多乘一次 W。

最终入口先对固定开凸 S、紧闭包和实际 C¹ 轮廓，用真实闭包内导数界与凸域均值定理取得 `L≥1`，再选 W 和 `C=W²B₀`。完整类型的量词顺序为固定 n、S、ρ、κ 后 `∃C>0`，随后才是全部 a,b、h、J、TimeWeight、τ、t、η、u。C 可以依赖固定轮廓/域的 Lipschitz 界和 κ，但不依赖盒位置/尺寸、h、权振幅、q/qmax、幂次、符号、时间或原状态。

任意正侧长盒非空，内部选择 y∈B，取真实权值 s=σ(y)>0；同一盒内的点态双向比较经 `ae_restrict_mem` 供应所需两条 a.e. 条件。只对已知实际光滑权函数取值，没有对 u 或其导数字段取点值。用户不必另给锚点、权可比性或加权目标估计。

原 qclass 的时间光滑性、端点匹配、导数约束和 τ 的有界范围不参与这个固定时刻空间证明；TimeWeight 的正性及上下界足够，声明允许所有 τ 和 t。因此这是对原允许族的加强，不是缺少需要的前提；原任意 T 的周期延拓均在其中，C 在整个 TimeWeight 之前选取，确无 T 依赖。hq≤1 正是原 B.2 的固定时刻条件，没有改为更小的数值阈值。

主入口以 n=d+1 覆盖全部原正维 n≥1；几何辅助声明本身也含 d=0。h>0、严格正侧长符合原非退化网格。任意 J 包括空集、单面、全部面和角点；零状态、零 Hessian 和常轮廓不被排除。局部残差无需在人工盒面上零迹，也未被错误要求属于整个局部盒的 H¹₀。

## 固定版本和本机证据

四模块 Carleman 导入闭包共 188 个模块，其中 184 个既有模块相对 base 全部逐字节不变，root 明确导入四个新模块。AGENTS、治理流程、state 协议、原论文、Lean/mathlib pin 和两个 CI workflows 相对 base 均未改。原论文 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

固定 `/tmp/carleman-weighted-local-target.log` 实际显示 `AllowedLocalBoundaryAffine` 定向构建 3370 jobs 成功；`/tmp/carleman-weighted-local-full.log` 实际显示全库 Carleman 3734 jobs 成功，并完成全声明审计。固定 `/tmp/carleman-weighted-local-local-axioms.txt` 为 1,675,964 bytes，SHA256 `e7c65d179f629f08bbc06b031f393f4c58724eb5f7a7f0a168716f0804e329bd`。

九项各有一条完整类型和一条递归公理打印，均已与源码核对。全部 1757 条显式公理打印（1753 个不同声明）只使用 `propext`、`Classical.choice`、`Quot.sound`，无其他公理；末行实际为 `Axiom audit passed for all 5792 Carleman declarations.`。审计程序相对 base 未改，仍递归收集全部 Carleman 声明依赖并拒绝白名单外公理；本批只增显式检查。四模块无 sorry/admit 或新增数学公理。

## 远端证据与签发

已独立查询 [main CI run 39179746249 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39179746249/attempts/1)，确认事件为 `push`、分支为 `main`、head SHA 为固定 `4e697929d6afc9043f0a20caf093a0d62a33963d`。签发时 run 为 `completed/success`，最后更新时间为 `2026-10-19T00:16:35Z`，实际三项 jobs 均最终成功：

| Job | ID | 最终状态 |
|---|---|---|
| `lean` | `117829771145` | `completed/success` |
| `state-check` | `117829771343` | `completed/success` |
| `dashboard / snapshot` | `117830630675` | `completed/success` |

独立读取同次原始 `/tmp/carleman-weighted-local-main-ci/result.json`：`status=PASS`，`checked_sha=source_head_sha` 精确等于本报告固定 SHA，`finished_at=2026-10-19T00:15:27.143281+00:00`，target 为 `Carleman`。Linux Lean 4.35.0 的 commit 为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定源码 pin 一致。

独立查询 artifact 元数据，`lean-ci-result`（ID `12155723104`）和 `lean-declaration-evidence`（ID `12155259730`）均未过期，且各自绑定上述同 run、main 分支和固定 SHA。下载的原始 `/tmp/carleman-weighted-local-main-axioms/axioms.txt` 与固定本机副本逐字节完全一致：1,675,964 bytes，SHA256 `e7c65d179f629f08bbc06b031f393f4c58724eb5f7a7f0a168716f0804e329bd`。远端九项实际类型和公理打印逐项核对，全部 1757 条显式递归公理结果只有三项正常基础公理，末行确认全库 5792 声明审计通过。未使用后续工作树的公理产物。

最终结论为 **AUXILIARY / PASS**，没有发现本批声称范围内的数学缺陷。可将 C099 按 **AUXILIARY / REVIEWED** 记录；完整 B.2、FD 和其它原文覆盖不提升，保持 **13/26**。本 Agent 仅写本报告，未修改实现、台账、root 或原稿，未 commit/push。
