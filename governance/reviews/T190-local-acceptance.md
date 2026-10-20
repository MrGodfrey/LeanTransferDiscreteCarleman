# T190 / C206 独立本机验收：真实 Bochner 与产品 L² 映射

- checked_sha: `f0ab18741c799cd2d821174cfce77ffbb454fa20`
- mathematical_base: `b92214e1ee49124122e54ed76dc7bb734792b157`
- reviewer: 独立本机 Agent `/root/accept_spatial_foundations`
- reviewed_at: `2026-10-20T01:13:32+00:00`（UTC；签发后正文与时间冻结）
- 最终状态：**PASS，20/20 显式声明通过独立数学验收；同 SHA 三项 CI 最终成功，独立下载的原始工件逐字节匹配固定本机证据。**
- scope: **AUXILIARY，17/26**；不提升整个 P021 / Corollary 7.9。

## 固定版本、原文与方法

直接读取固定 Git 对象的三个新模块全部证明、固定 raw 中20项完整展开类型、T190 分析/MATH_SPEC 与 T190/C206 台账。AGENTS、PROJECT_OPERATIONS、state/README、MILESTONES、PAPER_COVERAGE 与已读取的 T188 固定版本逐字节相同，沿用其独立语义审查和真实同 SHA 证据要求。未将后续工作树或动态 `.ci/axioms.txt` 作为本批依据。

实际对照 `paper/main.tex:2289–2332` 的原 E_h、K_h、真实时间重构与平均势规则，2335–2400 的控制极限论证，以及附录2890–2930的原势一致性/配对。原稿以 Bochner L²(0,T;H) 描述弱极限，又使用产品域上的实际势积分；本批正是连接这两种真实空间及原 FD 重构的辅助接口。原稿 SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`，没有修改原稿。

已完整读取 [T189 冻结报告](T189-local-acceptance.md)，提交 `c99aad2047e9befa4a82b6aa3e90e2664f35ac3a`，checked SHA 正是本批 mathematical_base，reviewed_at=`2026-10-20T01:03:47+00:00`，13/13 PASS。另外直接重读实际时间重构、固定域运输、真实空间与时空胞元等距、平均势及乘法交换的实现；报告与 CI 均不替代这些数学检查。

## 全部20项实际声明

以下顺序与固定 manifest 完全相同。源码路径相对 `Carleman/Control/`；raw 行指完整展开类型起始行。共 **4 个 def、16 个 theorem**，不是20个原文命题。

| 序号 | 完整声明 | 固定源码 | raw 行 | 结论 |
| --- | --- | --- | --- | --- |
| 1 | `Carleman.simpleL2_uncurry_memLp` | `SimpleL2Product.lean:18` | 36059 | 有限值域给真实 uncurry 的产品 MemLp；PASS。 |
| 2 | `Carleman.simpleL2_product` | `SimpleL2Product.lean:34` | 36064 | 由同一实际代表 toLp 构造；PASS。 |
| 3 | `Carleman.simpleL2_uncurry_add_ae` | `SimpleL2Product.lean:38` | 36074 | 有限例外集合并后的真实 a.e. 加法；PASS。 |
| 4 | `Carleman.simpleL2_uncurry_smul_ae` | `SimpleL2Product.lean:51` | 36079 | 同一代表的真实 a.e. 数乘；PASS。 |
| 5 | `Carleman.simpleL2_productLinear` | `SimpleL2Product.lean:61` | 36084 | 产品 L² 中严格线性，未把代表当逐点线性；PASS。 |
| 6 | `Carleman.simpleL2_bochnerLinear` | `SimpleL2Product.lean:77` | 36094 | 原简单函数进入真实 Bochner L²；PASS。 |
| 7 | `Carleman.memLp_toLp_norm_sq` | `SimpleL2Product.lean:83` | 36104 | 真实 L² 范数平方等于原函数范数平方积分；PASS。 |
| 8 | `Carleman.simpleL2_product_norm` | `SimpleL2Product.lean:91` | 36108 | 可积性清偿后的 Fubini 精确等距；PASS。 |
| 9 | `Carleman.simpleL2_bochnerLinear_dense` | `SimpleL2Product.lean:106` | 36114 | 原简单函数的真实 Lp 稠密性；PASS。 |
| 10 | `Carleman.bochnerL2ProductIsometry` | `BochnerProductL2.lean:18` | 36118 | 稠密像延拓到整个 Bochner L² 的线性等距；PASS。 |
| 11 | `Carleman.bochnerL2ProductIsometry_simple` | `BochnerProductL2.lean:22` | 36128 | 延拓在原简单函数上精确恢复原构造；PASS。 |
| 12 | `Carleman.bochnerL2ProductIsometry_simple_ae` | `BochnerProductL2.lean:26` | 36134 | 恢复真实产品代表；PASS。 |
| 13 | `Carleman.bochnerL2ProductIsometry_indicator_ae` | `BochnerProductL2.lean:32` | 36140 | 指示函数两侧及 Lp 零代表均按 a.e. 核对；PASS。 |
| 14 | `Carleman.bochnerL2ProductIsometry_weak` | `BochnerProductL2.lean:55` | 36147 | 真正 Hilbert 伴随保留全部产品测试弱极限；PASS。 |
| 15 | `Carleman.bochnerL2ProductIsometry_time_ae` | `BochnerProductL2.lean:68` | 36158 | 原后向 Euler 时间胞元的实际有限指示和；PASS。 |
| 16 | `Carleman.bochnerL2ProductIsometry_fixed_time_ae` | `BochnerProductL2.lean:81` | 36164 | 同一固定 T 的精确运输；PASS。 |
| 17 | `Carleman.cartesian_time_product_reconstruction` | `CartesianProductL2.lean:15` | 36171 | 原 E_h 时间重构严格等于原产品胞元重构；PASS。 |
| 18 | `Carleman.cartesian_time_product_potential` | `CartesianProductL2.lean:45` | 36178 | 同一原平均势作用通过同一映射精确交换；PASS。 |
| 19 | `Carleman.cartesian_fixed_time_product_reconstruction` | `CartesianProductL2.lean:68` | 36193 | 固定盒和固定 T 中的同一 E_h 身份；PASS。 |
| 20 | `Carleman.cartesian_time_product_potential_pairing` | `CartesianProductL2.lean:81` | 36202 | 任意两份完整节点序列的真实势配对身份；PASS。 |

## 实际简单函数、a.e. 线性与 Fubini

一般构造的输入为任意可测空间 α、β，有限测度 μ 与 s-finite 测度 ν；简单函数 f 的值域是完整真实 `Lp ℝ 2 ν`。第1项的产品代表确为 `(t,x) ↦ (f t)(x)`，使用的是各空间 L² 类的已有代表，不是把嵌套 Lp 用定义改名为产品 Lp。

证明将这个函数逐点写成 f.range 上的有限和：时间纤维 `f⁻¹{v}` 的指标乘以空间代表 `v(x)`。每个时间纤维可测，`Lp.memLp v` 经 `MemLp.comp_snd μ` 得产品 MemLp，再限制指标集合并有限求和。已读取 mathlib `LpSeminorm/Prod.lean` 的实际证明：第二投影映射测度是 μ(univ)·ν，有限 μ 保证该缩放合法，ν 的 s-finite 资格用于相应测度身份。没有遗漏联合可测性或用未经证明的点值评价连续性。

空间 Lp 代表的加法/数乘仅 a.e. 成立。第3项对 f.range×g.range 的**有限**个身份合并例外集，第4项对 f.range 合并；再通过 `quasiMeasurePreserving_snd.ae` 拉到产品测度。实际读取该 mathlib 引理，其证明用乘积集合测度上界及 ν-零集的逆像仍为零；这两个辅助定理本身无需有限/s-finite 假设。第5项再结合各个 toLp 与加法/数乘的 a.e. 代表身份，用 `Lp.ext` 得线性。这里没有把“每个 t 均有一个空间 a.e. 集合”错误地换成“存在同一集合对不可数 t 成立”。

第7项从 `L2.inner_def`、真实内积自配对和 `hf.coeFn_toLp` 得到 `‖hf.toLp f‖²=∫‖f(t)‖²`。第8项先由第1项的 MemLp 得真实平方范数可积性，再调用 `integral_prod`，将产品积分写成时间—空间迭代积分；对每个简单函数值使用同一 L² 范数身份。已直接读取 mathlib Fubini 的 `Integrable.induction` 证明路径和可积性前提，未对不可积函数使用形式换序。最后两侧范数非负，故平方相等推出范数相等，**没有 μ(univ)、T 或节点数的剩余因子**。

## 从真实稠密像延拓、全测试弱收敛

第6项将实际简单函数通过其有限测度 MemLp 证明送入 Bochner L²。第9项使用 `Lp.simpleFunc.denseRange`，再以 `toSimpleFunc` 与 `toLp_toSimpleFunc` 的身份把真实 Lp 简单函数的像包含到本线性映射的像。已读取 mathlib 的稠密性证明：对任意强可测 Lp 代表，使用其自身可分值域上的 `SimpleFunc.approxOn` 并在 p≠∞ 时 Lp 收敛；不需要整个值域另加可分性前提，也没有假设所有 Bochner 函数本来就是有限值域。

第10项采用 `LinearMap.extendOfIsometry`。实际阅读 `Extend.lean` 的 `compLeftInverse`、`extendOfNorm`、精确恢复与唯一性证明：范数界首先确保简单函数映射在 Bochner Lp 的核上为零，经核商在真实稠密像上良定义，再连续延拓到完备产品 L²。等距由稠密像上的精确范数身份及连续性延拓。即便简单函数到 Lp 的映射不是单射，这个构造也合法；没有直接选择一个任意右逆冒充产品代表。

第11–12项保证此延拓在所有原简单函数上保持原构造和 uncurry 代表。因该像稠密，它唯一确定这个连续映射，因此不是任意 Hilbert 等距。类型为 **`→ₗᵢ[ℝ]`，不是 `≃ₗᵢ[ℝ]`**；本批未证明也未使用满射或逆映射。对一般 Bochner 元素，本批声明的是该实际延拓，而非无条件逐点 uncurry 公式；明确的 a.e. 代表身份已在简单函数、指标和真实有限时间重构上证明。

第13项以实际 piecewise 简单函数表示 `indicatorConstLp`。集合外还显式使用空间 `Lp.coeFn_zero` 并通过第二投影拉回，所以没有把商空间中零元素的任意代表当作处处零。第15项用时间重构的真实有限指标和及映射保和，将各项 a.e. 身份有限相加；第16项只沿 g.period=T 精确运输同一函数。

第14项对每一个**完整产品 L²** 测试 w，将真实 CLM 的 Hilbert 伴随 F* w 放入输入的全部 Bochner 测试，使用 `⟨u,F*w⟩=⟨Fu,w⟩` 得结论。已读 `Adjoint.lean` 真实 Riesz 构造及该身份；两侧实际 L² 都是完备 Hilbert。无需证明 w 在 F 的像中，无需满射，也没有缩小成有限张量测试、选择额外子列或额外有界性前提。

在原物理实例中 μ 是 `volume|(0,T]`，自动有限；ν 是盒内限制 Lebesgue，自动 s-finite，事实上也有限。这些一般构造条件没有给原网格、状态或势添加新的限制。等距常数恰为1，对所有合法周期与空间尺度相同；未使用随网格变化的有限维自动连续性来代替统一范数控制。

## 原 E_h、时空胞元、质量与边界条带

第17项输入任意完整 `Fin g.steps → CartesianPhysicalState δ hδ N` 序列。左侧先用同一原 `cartesianCellIsometry` 重构每个状态，再用原后向 Euler 胞元 `(t_i,t_(i+1)]` 重构时间；右侧为既有 `cartesianSpacetimeCellIsometry`，其胞元是真正的时间胞元与原内部对偶胞元的 Cartesian 乘积。

证明并非仅比较范数：先对有限个时间索引合并真实空间重构的 a.e. 指示和身份，然后拉到产品空间；将两边真实代表展开，利用 `Fintype.sum_prod_type` 逐项比较。分别讨论是否属于该时间胞元及空间胞元，得到 **Lp 元素严格相等**。这同样覆盖全部未覆盖区域；没有假设内部对偶单元覆盖整盒。

已重读 `CartesianSpacetimeCells`、`FiniteCellReconstruction` 与原物理有限空间。真实乘积胞元体积为 **dt·∏δⱼ**，来自乘积测度及实际时间/空间单元体积；不同胞元严格不交。有限指标 Gram 矩阵的积分给内积 **dt·∏δⱼ Σ_(i,a) uᵢ,a vᵢ,a**。`PhysicalFiniteSpace.valuesEquiv.symm` 在此只把同一数组 `u a.1 a.2` 放入具有该真实质量的载体，不重新缩放节点值；时间 Bochner 内积中的 dt 与空间质量 ∏δ 完全匹配，无缺失平方根或重复 dt。

原空间/时空重构均是指标和，单元外为零，包括原稿明确保留的边界条带和内部单元分界面。证明没有将正体积条带当零测集；指标定义直接在未覆盖点给零。对偶单元为开盒、时间单元为左开右闭，与原公式一致。

第19项的 hbox 为 `lo_j+N_jδ_j=hi_j`，hT 为 `g.period=T`；证明以函数外延和等式消去运输同一盒与周期。左侧恰是 T188 使用的固定盒 E_h 的固定时间重构，右侧是原固定产品域的 `fixedSpacetimeCellIsometry`。这些只是原固定物理域的等式，不是新几何限制；没有逐网格任意选择不同同构。

## 同一平均势及完整配对

第18项先用原 `cartesianReconstructedPotential_commute` 把每个时间层的真实空间乘法变成实际节点乘法，再对两侧使用第17项。随后调用原产品胞元 `finiteCellMultiplier_commute`，其逐点证明在胞元内取相同系数，胞元外两边都是零。

已直接读取真实系数定义及公式：`cartesianAveragedPotential` 是原 b 的时间平均再空间胞元平均，等于 **(dt·∏δⱼ)⁻¹∫_(timecell)∫_(D_a)b(t,x)**；原有限柱体可积性及 Fubini 供给该身份。同一系数进入 `cartesianReconstructedPotential` 和 `cartesianSpacetimePotential`，二者都保留 b.bound，均在未覆盖区域为零。输入 b 是原任意 a.e. 有界可测实势，无光滑性、小量或额外一致性假设；不把原 b 本身误认作离散平均 b_h,dt。

第20项对任意两份完整节点序列 u、v，先用第18项重写同一势作用，然后以 F 的真实 `inner_map_map` 得 Bochner 势配对与产品势配对严格相等。不是将这个结论加入前提，也没有只检查 u=v 的能量。该定理针对实际胞元重构；本批未宣称已经证明对任意 Bochner 函数的所有时变乘子交换或完整极限 PDE。任意产品测试的弱极限接口则由第14项单独、完整地提供。

所有最终 Cartesian 身份只要求各 δⱼ>0、原 TimeGrid 和固定域等式（相应定理中）；N_j 允许任意自然数。没有 h→0、dt→0、长宽比、网格嵌套、CFL、状态预算、初末条件或 h–dt 耦合。允许 d=0、空内部节点、空物理盒以及粗网格 N_j≤1；所有操作是有限和、正 dt/正乘积质量及 Lp 身份，没有选择不存在的节点。它们也可对控制零延拓后的状态数组使用，但本批没有另声明完整控制支撑或极限控制方程。

## 依赖闭包、构建与公理

三个入口的实际 Carleman 导入闭包共 **347** 模块，其中 **344** 个旧模块与 mathematical_base 逐字节相同；本批 `Carleman/` 数学改动恰为三个新模块。关键入口完整闭包与已接受版本额外比较，均无变化：

| 入口 | 已接受固定版本 | 闭包模块数 |
| --- | --- | --- |
| Control/TimeWeakTesting | `b92214e1ee49124122e54ed76dc7bb734792b157` | 25 |
| Spatial/FixedSpacetimeCellReconstruction | `8e2e1e1a269c81ea0f9fdd98c6f13477cf8583b8` | 342 |
| Control/CartesianPotentialReconstruction | `ffa5a6f8061e5b13aa96a7f77081aa4f8482e2e5` | 333 |
| Control/TimeCellReconstruction | `d1134c0ccc8f343aef6223f304fe52f86a7aff1d` | 23 |

固定 Carleman 根模块实际导入全部三个入口；20项在固定 CheckAxioms 中均有 `#check @` 和 `#print axioms`。三个新模块无 sorry、admit、native_decide 或新 axiom。实际读全20项展开类型，均仅依赖 **propext、Classical.choice、Quot.sound**。

独立解析固定 raw 全部 **3347** 条显式公理记录（**3343** 个不同名字、**9** 条无公理记录），白名单外依赖为零。并已读取实际递归 auditor：对环境中全部 Carleman 前缀（包括私有名还原）的声明逐项 collectAxioms，拒绝任何白名单外公理；原始末行是 **8569 项 Carleman 声明审计 PASS**。显式打印数与递归环境总数口径不同。

实际读取 `/tmp/carleman-t190-target1.log`，三个新模块最终定向构建 **3538 jobs** 成功；`/tmp/carleman-t190-bochner-product-build.log` 根构建 **4170 jobs** 成功。`-axioms.log` 是零字节 stderr，成功依据为 raw 审计末行，不从空输出推断。开发 probe 日志未作为验收证据，未在变化中的工作树重跑后续版本来替代本批。

固定 `/tmp/carleman-t190-bochner-product-local-axioms.txt` 实测 **2765884 bytes**、SHA256=`672f4f3139d1693a6021980c9f15ca91bcf3fc0c409dac4eea52d139fd2f55d0`。Lean pin 4.35.0；mathlib pin 与本机干净 HEAD 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。工具链、manifest、lean_ci.sh 与两个 workflow 均和数学基线相同。实际读取 mathlib 的简单函数 Lp 稠密性、comp_snd、第二投影准保测、Fubini、extendOfIsometry 及 Hilbert 伴随实现，未仅凭名称接受依赖。

## 正式 CI 与签发

本 Agent 按精确 SHA 独立发现 [main run 39351691345 / attempt 1](https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/actions/runs/39351691345/attempts/1)。实际 `event=push`、`head_branch=main`、`head_sha=f0ab18741c799cd2d821174cfce77ffbb454fa20`；最终 API 为 **completed / success**，updated_at=`2026-10-20T01:11:29Z`。三个作业的 head_sha 均逐项匹配，实际最终状态如下：

| 作业 | job ID | 最终状态 | completed_at（UTC） |
| --- | --- | --- | --- |
| state-check | `118397101867` | completed / success | `2026-10-20T01:07:58Z` |
| lean | `118397102147` | completed / success | `2026-10-20T01:11:19Z` |
| dashboard / snapshot | `118398159620` | completed / success | `2026-10-20T01:11:28Z` |

本次 API 已返回真实最终成功，不需要采用摘要迟滞时的完整日志替代路径。独立原始查询保存在 `/tmp/carleman-t190-bochner-product-review-runs.json`、`-review-run.json`、`-review-jobs.json` 与 `-review-artifacts.json`。

同 run 工件的 workflow_run 均精确绑定上述 SHA/main/run。本 Agent 自行执行两次 `gh run download`，两次实际 exit 0，分别下载到 `/tmp/carleman-t190-bochner-product-main-ci` 与 `-main-axioms`，没有使用 root 副本。

| 工件 | artifact ID | ZIP bytes | GitHub ZIP SHA256 |
| --- | --- | --- | --- |
| lean-ci-result | `12233368510` | 492 | `c59fded758e8e19fd4b8f405aeecc985e2109334407b4bf14816b718797614b7` |
| lean-declaration-evidence | `12233478266` | 255120 | `bfa089a7cd3e54a24e1397835541fb161c23092f1e56ec556cdc49a593489a62` |

实际 `-main-ci/result.json` 为 **537 bytes**，SHA256=`bc17b17d719d9a01b68dde4c74888b31e2979d3d293b5ebf5903bd715d375fb0`。内容 `status=PASS`，`checked_sha=source_head_sha=f0ab18741c799cd2d821174cfce77ffbb454fa20`，`targets=[Carleman]`，ci_url 精确指向本 run/attempt，finished_at=`2026-10-20T01:10:12.579579+00:00`。Lean 4.35.0 编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` 与 mathlib pin 均匹配。

实际 `-main-axioms/axioms.txt` 和固定 `-local-axioms.txt` **逐字节完全一致**，均 **2765884 bytes**、SHA256=`672f4f3139d1693a6021980c9f15ca91bcf3fc0c409dac4eea52d139fd2f55d0`；20项完整类型与公理信息随字节比较一起确认。远端原始末行明确为 **8569 项 Carleman 声明递归公理审计 PASS**。以上原始文件摘要和 GitHub ZIP 摘要分开记录，没有混用。

## 最终判定与冻结

**T190 / C206：PASS，20/20；axiom_check PASS。无阻断或非阻断数学缺陷。** 真实有限值域代表、a.e. 线性、Fubini 精确等距、完整 Bochner 稠密延拓、全产品测试弱极限及原 E_h/平均势配对均忠实。没有隐藏满射、新网格限制、假点值身份或未清偿目标假设。

保留 **AUXILIARY、17/26**；测试强一致性、极限 PDE、时间弱导数与初终值识别等不由本辅助接口自动完成，不提升 P021。此报告是本 Agent 唯一仓库写入，单文件提交；不修改数学、原稿、台账、根导入或公理脚本，不推送。以上签发时间及正文现冻结。
