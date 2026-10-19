# T117 / C133 独立本机验收

- `checked_sha`: `d533b7e90f5e8cecf266e09e8faa5afab3772ed7`
- `base_commit`: `fa02c379c6ee0f59172dadc1401b9a535e6d3c9c`
- `reviewed_at`: `2026-10-19T05:07:08+00:00`
- `reviewer`: `/root/accept_spatial_lemma`
- `result`: **PASS**
- `axiom_check`: **PASS**
- `scope`: **AUXILIARY**
- 范围：真实标量仿射拉回的 L² 资格、精确 Jacobian 能量、任意全空间 L² 数据的向内拉回强连续性、实际各阶光滑导数缩放和变动近似的强极限。闭域弱 H² 光滑逼近及边界连续代表尚未组装，P011不提升，原文保持 **14/26**。

本 Agent 直接读取固定 git 对象的五个完整模块、17项实际展开类型和关键依赖，对照原稿 Section 6 P1 设置及 Step 2（`paper/main.tex:1462–1505,1523–1548`），并读取固定 T117 分析、MATH_SPEC、C133。已核实 AGENTS、运行/状态协议、里程碑、覆盖协议及原稿与此前已读版本不变。CI和执行者说明未替代数学核查；后续 InwardMollifierSequence、InwardMollification、WeakH2ClosureSmoothing 工作树增量及变化中的 `.ci` 未纳入。

## 全部17项声明

以下省略公共前缀 `Carleman.`，模块位于 `Carleman/Spatial/`；名单与固定 C133、T117 及 `/tmp/carleman-inward-l2-declarations.json` 完全一致。

| # | 声明 | 固定模块及行 | 独立结论 |
|---|---|---|---|
| 1 | `scalarAffine_memLp` | ScalarAffineL2:15 | PASS；真实可逆标量仿射映射和实际体积推前给 MemLp 保持。 |
| 2 | `integral_scalarAffine_univ` | ScalarAffineL2:24 | PASS；真实满射和 Jacobian 给 r^(−d) 的全空间换元。 |
| 3 | `scalarAffine_L2_sq` | ScalarAffineL2:34 | PASS；输入与拉回均 L²，平方范数精确满足 Jacobian 身份。 |
| 4 | `inwardPullback` | ScalarAffineL2:41 | PASS；实际函数复合 f(rₙx+(1−rₙ)a)，不是逆收缩复合。 |
| 5 | `inwardPullback_memLp` | ScalarAffineL2:44 | PASS；每个实际 rₙ>0，资格由第1项供应。 |
| 6 | `inwardPullback_L2_le` | ScalarAffineL2:49 | PASS；固定维数常数 2^d 对全部 a、n、f 统一。 |
| 7 | `inwardPoint_tendsto` | ScalarAffineL2:62 | PASS；固定 a、x 的真实仿射点趋向 x。 |
| 8 | `l2_square_tendsto_zero_of_ae_of_energy_tendsto` | StrongL2EnergyLimit:13 | PASS；任意测度上 a.e. 收敛与真实能量收敛经 Fatou 给平方误差趋零。 |
| 9 | `l2_error_tendsto_of_ae_of_energy_tendsto` | StrongL2EnergyLimit:59 | PASS；所有误差均 L²，非负平方根转为真实 L² 误差趋零。 |
| 10 | `inwardPullback_L2_error_tendsto_of_continuous` | StrongInwardPullback:15 | PASS；连续 L² 函数的点态拉回与精确能量极限内部供应。 |
| 11 | `inwardPullback_L2_error_tendsto` | StrongInwardPullback:28 | PASS；真实光滑卷积密度推广到任意 MemLp 函数，无其点态拉回收敛前提。 |
| 12 | `scalarAffine_iteratedFDeriv` | InwardSmoothDerivatives:14 | PASS；实际 k 阶张量的平移、标量预复合链式公式，系数 r^k。 |
| 13 | `inwardPullback_contDiff` | InwardSmoothDerivatives:22 | PASS；实际光滑仿射预复合保持给定阶数正则性。 |
| 14 | `coordinateDerivative_inwardPullback` | InwardSmoothDerivatives:27 | PASS；全部有序 k 阶真实坐标导数精确缩放 rₙ^k。 |
| 15 | `inwardPullback_L2_error_tendsto_diagonal` | InwardApproximationLimit:13 | PASS；同指标变化的 Fₙ 与拉回 Pₙ 仍强趋向 f。 |
| 16 | `l2_scaled_error_tendsto` | InwardApproximationLimit:35 | PASS；任意测度和 cₙ→1，实际乘法保持强 L² 极限。 |
| 17 | `inwardPullback_scaled_L2_error_tendsto` | InwardApproximationLimit:55 | PASS；固定 k 下真实 rₙ^k PₙFₙ 强趋向 f。 |

## 实际仿射测度、L²资格和统一常数

已读取 `AffineChangeVolume` 和 `ConvexSegmentIntegral`：`affineChange A b` 是真实连续线性等价后接平移的同胚；体积推前为 |det A|⁻¹ 倍体积。标量 A=r Id 的行列式实际计算为 r^d，使用真实 Euclidean 空间的 finrank=d，并以 r>0 清除绝对值。平移不改变体积，不是把 r^d 当作未经证明的 Jacobian 参数。

第1项通过该推前测度身份、有限标量倍测度的 MemLp 性质及 `comp_of_map` 给出 f(rx+b) 的实际 MemLp。第2项用 r≠0 显式构造逆像 r⁻¹(y−b)，使原限制换元中的像集成为整个空间。因此

\[
\int f(rx+b)\,dx=r^{-d}\int f,
\qquad \|f(r\cdot+b)\|_2^2=r^{-d}\|f\|_2^2.
\]

第2项对任意函数使用 Lean 的全定义积分换元，不单独断言其可积；第3项和后续能量应用先有 MemLp，平方积分均真实可积，不依赖不可积积分的默认值。对原代表的零测修改，仿射推前为有限正倍体积，因而不会通过复合产生正测误差；实际证明也逐次保留了拉回 MemLp 资格。

已读取真实 `inwardRatio n=(1+n)/(2+n)`，其范围为 [1/2,1)，趋于1。当前 Pₙf(x)=f(rₙx+(1−rₙ)a) 使用正向收缩点，与旧 `contractedFunction` 使用逆映射压缩支撑的构造不同；本批没有混用两者的导数尺度。

第6项由 rₙ^(−d)≤2^d 和 2^d≥1 得 rₙ^(−d)≤(2^d)²，再合法开非负平方根，得到 ‖Pₙf‖₂≤2^d‖f‖₂。这是可用的安全常数，并未声称是精确算子范数。常数只依赖 d，对中心 a、指标 n 和全部 L² 数据统一；d=0 也合法，不需要除以维数或状态范数。

## 能量收敛加 a.e. 收敛的 Fatou 证明

第8项在任意测度 ν 上接受 f、每个 Fₙ 的 MemLp、一个共同 a.e. 收敛集合，以及真实平方能量 Eₙ→E。平方和、平方差及原平方均可积，证明先得到精确积分平行四边形身份

\[
\int(F_n+f)^2+\int(F_n-f)^2=2E_n+2E.
\]

若平方误差不趋零，存在 b>0 和趋于无穷的指标子列 φ，使每项误差≥b。能量收敛给最终 Eφ(n)<E+b/4，进而最终 ∫(Fφ(n)+f)²≤4E−b/2。右侧非负性从一个实际非负积分得到，未预设 E>0。

在原共同 a.e. 集合上，Fφ(n)+f→2f。实际调用 `l2_square_bound_of_ae_tendsto` 的最终界版本，得到 4E≤4E−b/2，与 b>0 矛盾。已独立读取该依赖以及 pinned mathlib 的 `exists_seq_forall_of_frequently`、`Lp.eLpNorm_le_of_ae_tendsto`：前者确实给趋向 atTop 的子列，后者从真实 Lp Fatou 下半连续性推出最终界。没有非法把“频繁”当成“最终”，也不需要共同可积控制函数、有限测度或 σ-有限测度。

第9项使用每个真实误差的 MemLp，先将平方积分识别为 bochnerL2Norm 的平方，再用连续平方根和范数非负性得到强 L² 误差趋零。虽然 bochnerL2Norm 定义含 ENNReal.toReal，本批每次实际使用的函数都已证明 MemLp，不会将无限 seminorm 的 toReal 当作零误差。

## 从连续 L² 到任意代表：密度次序正确

第10项仅对连续 f 使用第7项的仿射点收敛，给每点 Pₙf(x)→f(x)；真实 Jacobian 使能量等于 rₙ^(−d)E，并由 rₙ→1 得能量趋于 E。因此第9项的两个极限前提均内部供应。

第11项没有对任意 f 假设 Pₙf→f 点态。它将 hf.toLp f 的实际代表与归一化缩小光滑核卷积，形成 Gₘ；`ConvolutionL2` 证明 Gₘ∈L²，真实卷积正则性证明其连续，已验收 `spatialMollifier_L2_error_tendsto` 给 ‖Gₘ−f‖₂→0。已读取此密度来源：真实 bump 核的 a.e. 卷积极限和 L² 收缩，经 Fatou/平行四边形准则产生全空间强收敛，无紧支撑或原函数 Sobolev 条件。

hf.toLp 的 a.e. 身份仅用于原域误差范数中的代表替换；证明没有把 a.e. 相等不加论证地代入收缩点。它直接对实际函数 f−Gₘ 使用统一拉回估计和真实三角不等式，得到

\[
\|P_nf-f\|_2\le(2^d+1)\|G_m-f\|_2+\|P_nG_m-G_m\|_2.
\]

给定 ε，先选一个固定 m 使第一项小于 ε/2，再对该连续 Gₘ 选最终收缩指标 n，使第二项小于 ε/2。量词次序正确，没有在依赖 n 的逼近项上套用仅对固定函数成立的收敛结论。结论覆盖全部 MemLp 实函数及其任意合法代表，不局限于连续或光滑子空间。

## 真实各阶导数和同时变化的极限

第12项要求全空间 `ContDiff ℝ k f`，先平移 f，再实际调用 mathlib 的 `iteratedFDeriv_comp_const_smul` 和 `iteratedFDeriv_comp_add_right`。已读取 pinned 版本：数乘公式通过真实 Fréchet 链式法则逐阶归纳，给

\[
D^k(f(r\cdot+b))(x)=r^kD^kf(rx+b).
\]

该导数身份本身允许任意实 r，包括0和负数；r>0 仅为前面的 L² Jacobian 定理所需。k=0 的公式由真实零阶张量求值成立。第14项使用 `coordinateDerivative v f=coordinateTensorEval v(iteratedFDeriv k f)` 的实际定义，将同一恒等式线性求值到全部有序坐标，得到 rₙ^k，方向没有颠倒为 rₙ^(−k)。第13项为任意所给光滑阶数保持正则性。这些声明没有假称原弱 L² 字段已有点态经典导数。

第15项对同时变化的 Fₙ 用真实误差分解 PₙFₙ−f=Pₙ(Fₙ−f)+(Pₙf−f)，第一项以 2^d 统一控制，第二项用第11项。第16项在任意测度上分解 cₙFₙ−f=cₙ(Fₙ−f)+(cₙ−1)f，并用精确常数乘法范数及三角不等式；cₙ可以变号，不需额外正性，cₙ→1 足以。第17项取 cₙ=rₙ^k，组合第15项与幂函数极限，全部误差的 MemLp 同时保留。

这里中心 a 和阶数 k 在极限之前固定；统一界对 a、n 独立不意味着对随 n 任意变化的 aₙ 或 kₙ 已证明极限。第11项也是对每个 L² 状态的强收敛，不是算子范数趋于恒等。实际类型没有这些更强断言。

## 原文对应、额外前提与范围边界

原 P1 Step 2 需要 d=2、3 时原全部 H² 状态在 closure Ω 上的连续代表，才能定义所有边界顶点的节点插值并得到全局加权误差。本批是将内部平滑逼近移到闭域所需的全空间 L² 分析工具，各个强收敛声明本身适用于任意固定维数，无不必要的 d≤3、光滑代表或紧支撑限制。

本批尚未选择域内中心、建立收缩闭域与反射核的共同支撑缓冲、选择与收缩协调的核序列，也没有将原全部弱 H² 的各个字段组装成 closure Ω 上同一个强光滑逼近。它没有新的 H² 全空间零延拓定理或边界导数身份；后续若对原字段作零延拓，只能先按真实 L² 数据使用本批结论。闭包连续代表、边界零节点、全局 conforming 插值及允许权组合仍待，不能据此完成 P011 或原 `eq:p1-interpolation`、`eq:p1-interpolation-energy`。

所列 MemLp、a.e./能量极限（仅通用准则）、光滑 Cᵏ（仅经典导数公式）均在实际类型中明确且与本批所声称的辅助范围一致。最终任意 L² 拉回连续性内部清偿了密度及连续逼近所需前提，无尚未证明的收敛、目标估计或连续代表输入。

## 固定依赖、构建与公理

本批 Carleman 导入闭包共109模块，其中5个新增；其余104模块与 base 逐字节一致。进一步核验已验收版本：C131 `StrongMollifierLimit` 的72模块闭包相对 `f134750df6b8ef03c639f50dd5084d4c42d49272` 不变；C132 `TensorCoordinateL2` 的61模块闭包相对 base 不变；`ConvexSegmentIntegral` 的35模块闭包相对 C128 `c8377e5f743689641ab84d5049b4d0fb291d29f5` 不变；`PairwiseL2Limit` 的46模块闭包相对 C089 `c99262c4a0d65a4d23f2efb57748bda490e971d7` 不变。依赖验收见 [T115](T115-local-acceptance.md)、[T116](T116-local-acceptance.md)、[T112](T112-local-acceptance.md)、[T073](T073-local-acceptance.md)，本次另核对上述关键证明和实际调用。

原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，治理协议及原稿相对 T114 已读版本不变。Lean固定4.35.0；mathlib pin及本机实际HEAD均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，本机 mathlib 工作树干净。五个新模块全在固定 root 导入，源码无 sorry、admit、新 axiom 或 native_decide。

`tools/CheckAxioms.lean` 本次仅新增17项类型和公理输出；递归审计器与 base 不变，对全部 Carleman 常量包括私有辅助声明运行 collectAxioms，仅允许 propext、Classical.choice、Quot.sound。固定产物17项均逐名核对，全部2284条非空公理记录、8条无公理记录（含重复输出，共2288个不同名字）均无不允许的公理；真实全环境递归审计为 **6649项 PASS**。

独立读取固定 `/tmp/carleman-inward-l2-target.log` 的 **3286 jobs** 成功，以及 `-full.log` 的 **3855 jobs** 成功和上述递归审计。固定 `-local-axioms.txt` 为 **1,994,655 bytes**，SHA256 **`d402d6bbae277b6e87ff79b09300a4dc7db6532d5917185610de1e884bc0c3ed`**。未读取变化中的 `.ci/axioms.txt` 替代该固定证据。

## 实际同 SHA CI 与原始产物

本 Agent 自行查询 [main CI 39202586094 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39202586094/attempts/1)：实际 main/push，head SHA精确为本报告 checked_sha，最终 completed/success，更新时间 `2026-10-19T05:06:53Z`。三项job分别为 lean **117898518324**、state-check **117898518561**、dashboard / snapshot **117899274361**，均已实际查询为 completed/success；最后一项完成于 `2026-10-19T05:06:52Z`。

同run原始artifact为 `lean-ci-result` **12164576211**（归档491 bytes）、`lean-declaration-evidence` **12164645834**（归档183,413 bytes），元数据中的 head_sha均匹配且未过期。本 Agent 自行执行两次 `gh run download 39202586094`，均exit 0，下载至 `/tmp/carleman-inward-l2-main-ci` 和 `/tmp/carleman-inward-l2-main-axioms`。

实际 result.json 为537 bytes，SHA256 `01712298b9a25a7707e23b579a2157a90113eb21c4a9cb45e06d29d18c3c9e72`。内容PASS，`checked_sha=source_head_sha=d533b7e90f5e8cecf266e09e8faa5afab3772ed7`，target Carleman，`finished_at=2026-10-19T05:05:40.842003+00:00`，ci_url匹配同run/attempt；Lean4.35.0提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，mathlib为上述pin。

自行逐字节比较远端 `-main-axioms/axioms.txt` 与本机固定副本：**完全一致，1,994,655 bytes，SHA256 `d402d6bbae277b6e87ff79b09300a4dc7db6532d5917185610de1e884bc0c3ed`**。原始远端末行确为6649项全声明递归审计PASS。产物PASS与所有job最终成功分别核验，没有将产物提前上传当作run已经完成。

## 验收决定

**C133：PASS，可升级为 REVIEWED，scope保持 AUXILIARY。** 全部17项声明未发现需要修复的数学缺陷；真实 Jacobian、任意 L² 强连续性、Fatou极限、真实各阶导数、变动近似及量词边界均已独立核对。同SHA三项CI与自行下载的原始产物已核实。

闭域弱 H² 光滑逼近、closure Ω 连续代表和完整 P1 加权插值尚待，P011不提升，原文保持 **14/26**。本次仅新建此报告，未修改实现、台账、原稿或root，未commit/push。以上签发UTC固定；通知主Agent后冻结报告，不再改动内容或时间戳。
