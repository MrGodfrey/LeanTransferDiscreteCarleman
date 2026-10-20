# T257 / C273 独立本机验收

- checked_sha: `e90a9dc75ebc85da3ccb5dd1bb740fd3d255db1a`
- mathematical_base: `10790206877d2b10b557b56430b8b0c4ec02b117`
- reviewed_at: `2026-10-20T10:37:23+00:00`
- reviewer: independent local Agent `/root/accept_spatial_lemma`
- result: **PASS，17/17 显式声明（15 定理、2 定义）；无阻断缺陷或修复项。**
- axiom_check: **PASS**
- evidence_source: **local**；不查询远端 CI/看板，不重复构建旧闭包。
- scope: **AUXILIARY，18/26；完成原指数和光滑内域上全部 H²∩H¹₀ 状态的完整 H² 零边值强密度，不提升 P023。**

## 原文及实际结论

完整读取固定 `Carleman/Spatial/FiniteStrongH2Density.lean`、17 项完整展开类型/公理、T257 analysis、MATH_SPEC 对应段及 `paper/main.tex:2659–2665`。原 Corollary A.2 要求指定凸多面体/盒的 Dirichlet Laplacian 全部空间假设。本批提供其一般凸域正则性路线中的光滑内域强密度；原弱状态的统一 Hessian 估计、原多面体穷竭和整个 Corollary A.2 仍未完成。

`HasSmoothDirichletH2Approximation u` 的定义确为：存在同一列 `U : ℕ → SpatialTest univ`，每项在原域整个实际 frontier 上处处为零，每项实际 H¹ 截断属于原 `dirichletJetSpace`，且 `allOrderJetOn S 2` 在原完整弱 H² 射流拓扑中趋于同一 u。没有将 H²∩H¹₀ 换成 H²₀，没有要求原 u 有光滑代表、零法向导数或给定逼近序列，也没有只证明标量值收敛。

泛型局部 helper 明确输入模型正则性和紧支状态密度，有限覆盖 helper 明确输入局部结论。最终 `regular_analytic_sublevel_strong_h2_approximation` 及具体 `halfspaceSmoothInner_strong_h2_approximation` 已内部清偿这些输入。具体终点仅保留 d>0、原有限半空间数据及其严格交的有界性、实际指定内域的一点 z、任意原 H²∩H¹₀ 状态。其同一序列先于全部近似索引和边界点；无图域、截断、分割、密度或目标估计作为额外假设。

## 全部声明逐项核对

名称省略共同前缀 `Carleman.`。行号分别是固定新模块源码及固定 raw 的完整类型起点；固定 T257/C273 两份清单与源码、根导入及 audit 条目全部一致。

| 源码 / raw 行 | 声明 | 结论 |
| --- | --- | --- |
| 12 / 44587 | `HasSmoothDirichletH2Approximation` | PASS（定义）；同一列真实全局紧支光滑函数，全部 frontier 零值、原 H¹₀ 成员和完整 H² 强极限三条件同时成立。 |
| 20 / 44590 | `SpatialTest.cutoffH2Transfer_approximation` | PASS；实际光滑乘积精确等于 cutoff CLM 的完整 jet，固定 CLM 连续性及真实边界运输保三条件。 |
| 41 / 44596 | `SpatialTest.cutoffH2Transfer_nested_roundtrip` | PASS；内 η、外 γ 且 γ=1 on tsupport η，返回原自域 η 截断 jet，正确处理两限制测度的 AE 身份。 |
| 77 / 44604 | `SpatialTest.cutoffH2Transfer_off_support` | PASS；真实 η·indicator(S)·u 值公式给 tsupport η 外 AE 零值。 |
| 88 / 44610 | `exists_localized_strong_h2_approximation` | PASS；真实构造外 γ，内部取得两截断各自双向支撑资格，用真实紧支模型密度后精确传回 ηu。 |
| 108 / 44623 | `compact_fullspace_hasSmoothDirichletH2Approximation` | PASS；d>0 下由实际盒/截断构造返回全部三条件，而非仅复用只陈述强极限的简化终点。 |
| 116 / 44632 | `dirichletH2Regular_graphSide` | PASS；Bool 两侧分别调用真实 hypograph/epigraph 弱正则性，保留全局高度及斜率资格。 |
| 125 / 44638 | `exists_interior_local_strong_h2_approximation` | PASS；原内点给包含于 S 的真开球，以全空间为模型，内部供应紧支密度和正则性。 |
| 138 / 44648 | `exists_boundary_local_strong_h2_approximation` | PASS；实际解析水平图及正确子水平侧给模型，全部全局高度/斜率界和模型密度均内部供应；邻域取与单位球的交。 |
| 165 / 44658 | `SpatialTest.sumTest` | PASS（定义）；有限和真实 C∞ 且紧支，定义在全空间。 |
| 175 / 44661 | `SpatialTest.sumTest_allOrderJetOn` | PASS；所有阶 m 的全射流有限和身份由真实 L² 值有限和和弱唯一性证明。 |
| 187 / 44665 | `SpatialTest.cutoffH2Transfer_partition` | PASS；实际分割和为 1 给局部化射流之和精确等于原 u.val。 |
| 206 / 44670 | `hasSmoothDirichletH2Approximation_sum` | PASS；同一索引 n 的有限和保 frontier 零值、H¹₀ 子模与完整 H² 强极限。 |
| 226 / 44675 | `hasSmoothDirichletH2Approximation_of_finite_cover` | PASS；真实 subordinate 光滑分割内部构造，closure S 上的和为 1 供应原状态重构。 |
| 240 / 44684 | `hasSmoothDirichletH2Approximation_of_compact_closure_local` | PASS；真实 compact closure 有限子覆盖，正确转换为有限子类型并使用相应局部结论。 |
| 260 / 44700 | `regular_analytic_sublevel_strong_h2_approximation` | PASS；从实际有界解析正则子水平集内部供应源弱 H² 正则性、所有内/边界模型和有限拼接。 |
| 276 / 44705 | `halfspaceSmoothInner_strong_h2_approximation` | PASS；原指数和实际解析性、紧闭包和真实边界正则性全部内部供应，输出同一原状态的完整三条件。 |

## 关键数学检查

**双截断恢复的是精确局部化状态。** `cutoffH2Transfer_nested_roundtrip` 的两个 cutoff 不被误认相同：γ=1 在 η 的完整拓扑支撑上，故逐点 γη=η。内层恒等式最初仅在 volume|T 下成立；证明使用 T 的可测性，将其改写为全空间 AE 的条件式 `x∈T → ...`，再限制到 S。对 S 中的点，若 x∈T，两层真实 indicator 及 γη=η 得 ηu；若 x∉T，由 S∩tsupport η⊆T 推出 η=0，左右均为零。得到真实 L² 类等式后才调用开放域弱导数唯一性恢复整个 H² jet。没有从支撑包含直接推出恒等，没有假设 η²=η，也未把模型域的 AE 等式无条件搬到 S。

**实际外截断与模型密度。** `exists_localized_strong_h2_approximation` 对紧集 tsupport η⊆开集 V 调用真实 compact smooth cutoff 构造，给 γ=1 on tsupport η 且 tsupport γ⊆V。S/T 在 V 上的精确 membership iff 分别供应 η、γ 的两方向支撑条件。内转 v 是实际 H²∩H¹₀ 状态；其值在 tsupport η 外 AE 为零由真正乘子公式证明。模型密度因此只接收它所要求的紧支状态。传回的光滑函数是 γ 乘模型近似的真实函数，内部使用实际乘积 jet 身份、H¹₀ 保持、完整 H² CLM 连续性和实际 frontier 运输。最后用嵌套 roundtrip 识别极限为原自域 ηu，未混入额外 η 因子。

**局部几何和正则性不存在循环。** 内部点选择实际开球⊆S，以 univ 为模型；全空间正则性和紧支密度的 d>0 假设明确由 hd 供应。边界点从原解析 g、g(c)=a、真实 fderiv 非零，经 `exists_sublevel_graph_near_regular` 得真实全局 C∞ 高度、法向平移不变性、Lipschitz C 与各真实斜率的 Bᵢ，以及原子水平集与正确上/下图域的局部 iff。其实际证明按原法向导数正负调用 coordinate-line 均值论证，未从仅水平集相等猜测侧别。T257 的 true/false 与上/下图域一一对应，W∩ball(c,1) 给有限分割所需的有界开邻域。T256 的真实紧支图域密度在同一 C/B/ψ 上适用，所有额外几何资格已由前述构造提供。

源 `DirichletH2Regular S` 在最终解析子水平定理中，由 T246 的真实弱 Poisson 正则性逐个 v/f 内部构造。已直接核对该旧证明通过内点 H²、边界 cutoff PDE 和有限局部弱导数拼接得到同一 H¹ 状态的 H² lift，再以弱 RHS 唯一性识别负 Laplacian；它不调用本批密度，也不假设给定弱解已有 H²。局部及转移 helper 暴露的 regularity 输入因此未遗留为具体最终定理的额外条件。

**有限和和完整弱射流。** `sumTest` 的值为实际函数有限和，C∞ 和紧支由有限和定理保证。`sumTest_allOrderJetOn` 将各函数与 Lp 代表的 AE 身份在有限个指标上合并，使用 `Lp.coeFn_finsetSum` 得真实值类身份，再用原完整弱 jet 唯一性给任意阶 m 的精确相等。分割身份同样先在单一限制测度下合并有限个 cutoff 公式，S 上 indicator 为 1，实际 Σηᵢ=1 于是给 Σηᵢu=u；完整导数字段由唯一性识别，无需未证明地假设导数项相消。

有限条局部序列选择为 Fᵢ,n 后，使用同一个 n 构造 Uₙ=ΣᵢFᵢ,n。真实 frontier 零值逐项相加、截断的线性及 H¹₀ 子模封闭于有限和、`tendsto_finsetSum` 在完整 H² 拓扑中的连续性分别给三个结论。有限指标不需取稀疏子列、额外一致速率或将无限多个零集交在一起。

**真实有限覆盖与分割。** 对 closure S 中每一点选择已有有界开邻域，`IsCompact.elim_finite_subcover` 取得真实有限指标集 I。代码将其转为有限子类型，对选中邻域复用真实开放性、有界性及局部结论。T246 的 `exists_finite_smooth_partition` 实际调用 mathlib `SmoothPartitionOfUnity.exists_isSubordinate`，其和为 1 在 closure S 上逐点成立。tsupport ηᵢ⊆Vᵢ 与 Vᵢ 有界使每个完整支撑成为有界闭集，欧氏空间 properness 给真正紧支；不是只使用普通 support 或假定分割存在。该构造不要求指标非空，空的泛型子水平域仍合法。具体指数和终点明确保留其真实内点 hz。

**最终原指数和内域。** 实际函数为 Σᵢexp((n+1)(bᵢ−ℓᵢx))，阈值 1/2。原有界严格半空间交给内域闭包紧性，实际解析性内部供应 hg。对真实 frontier，连续性与开放性给 g=1/2；凸支持不等式和同一实际内点的严格 g(z)<1/2 排除 fderiv=0。因而最终没有要求整张水平面上额外边界数据、给定 atlas/覆盖、全局图、密度或目标强收敛。完整 H²∩H¹₀ 输入和 true frontier 零值输出准确保留。

本批只使用固定图和 cutoff 连续性以及有限求和，不宣称这些连续算子范数随内域索引、边界图、partition 或状态统一。没有把密度等同于已经证明弱 Miranda–Talenti 估计或原域穷竭极限。

## 实际依赖与固定版本

实际递归 Carleman 导入闭包为 **298 模块**；其中 **297 个旧模块相对 mathematical_base 全部 Git blob 不变**，唯一新数学模块是 `FiniteStrongH2Density.lean`。已直接读取本批所用的 `CompactGraphDensity` 全部实现、`StrongH2CutoffTransfer` 的实际值/H¹₀/边界/连续性、`FiniteLocalH2Gluing` 的真分割及全局弱正则性、`SublevelGraphRegularity` 的真实两侧图构造、`HalfspaceSmoothExhaustion` 的紧性与边界正则性。上述旧源还分别与其已接受证明版本逐字节相同：T256 `10790206877d2b10b557b56430b8b0c4ec02b117`、T254 `4a84f2b095e71ea776fa79ecf2d568f28270cbe1`、T246 `ebc85ddad04c9b4008fa5b3e89a05696eff19bfb`、T245 `108394721c27094589e1eea0c77c63083625340d`、T230 `721b761224ad1b6425466bc956417ddce7f41908`。

已全文读取 T256 正式冻结报告 `governance/reviews/T256-local-acceptance.md`：报告提交 `d09fd4cf7b7ae62368365520070aa6b8b0fc7e8c`，checked_sha 为本批 base，reviewed_at `2026-10-20T10:31:03+00:00`，14/14 PASS。固定 T257 树中的报告与该提交逐字节相同：12,099 bytes，SHA256 `818c4941f749114be22196e976e819bbbf29fdfca1607caf9b038e4abb00b9eb`。其真实逆图映射覆盖全部弱 H²、保原 H¹₀、保测运输 compact AE 值支撑、真实全局测试及 frontier 身份均已对实际调用再核对，没有只引用执行者说明。

## 本地构建与公理证据

- `/tmp/carleman-t257-local-evidence.json`：source=local、PASS，checked_sha/source_head_sha 均为本报告 proof；根构建/审计实际 exit 0，finished_at=`2026-10-20T10:34:35.011290+00:00`。固定 T257 local_validation 也记录定向/根/审计 exit 0。
- `/tmp/carleman-t257-local-source-manifest.txt`：**1,054 项、114,404 bytes**，SHA256 `5d02cc9040ebf158a900e4721869c0a44fbaba003d0078fca8b7e9b437bf286a`。独立枚举固定树全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及每一个摘要均与固定 Git blob 匹配，未用未来工作树代替。
- `/tmp/carleman-t257-target-build.log`：目标 **3,483 jobs** 成功，110 bytes，SHA256 `3ad7a874548ecfaae7109ce250b10053072adeba8c099864ad6b30ea5e1de67e`。
- `/tmp/carleman-t257-build.log`：根 **4,296 jobs** 成功，80 bytes，SHA256 `b09e4036caad644ac6b92e65392f252b2b2b80d335633cce6938085bf7c77c40`。`/tmp/carleman-t257-axioms.log` 为 0 bytes。
- `/tmp/carleman-t257-finite-strong-h2-density-local-axioms.txt`：**3,443,138 bytes**，SHA256 `f37d2fbee22b5544ba4da395483e1bfe1ef9ad457a5ddfa9d45c6746250b84e4`；真实末行 **10,272 声明递归审计 PASS**。17 项完整类型已逐项读，全部依赖公理仅 `propext`、`Classical.choice`、`Quot.sound`；全 raw 的 4,127 个公理列表和 10 个无公理记录也没有其他公理。无 sorryAx 或新增数学公理，命名空间递归收集/白名单逻辑相对 base 不变。
- 根模块实际导入本模块，各显式声明的 `#check`/`#print axioms` 完整。Lean 4.35.0，编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与干净 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。
- 原稿相对 base 未改，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`；AGENTS/PROJECT_OPERATIONS/state README 摘要与此前已读取协议相同。以上是独立核验的固定本地执行证据，不冒称新 reviewer 全量构建或远端 CI 成功。

**接受 T257/C273 的上述 AUXILIARY 范围，无修复项。** 同一原弱状态的完整强密度已经真实闭合；弱统一 Hessian 估计和原多面体穷竭仍在范围外，覆盖保持 18/26。本报告正文与 reviewed_at 在单文件提交后冻结；不修改数学、台账或其他报告，不 push。
