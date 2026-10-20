# T245 / C261 独立本机验收

- checked_sha: `108394721c27094589e1eea0c77c63083625340d`
- mathematical_base: `31c84b810ce9f75a97bc2fc5a5cae481a9252183`
- reviewed_at: `2026-10-20T08:54:55+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，12/12 显式声明（11 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；原正则子水平域的准确图侧、实际截断，以及原完整 H¹₀ 弱 Poisson 状态在边界球内的同状态 H²。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Geometry/SublevelGraphRegularity.lean`、12 项 raw 类型、公理记录及 analysis/MATH_SPEC/台账，核对原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求整个 Dirichlet 算子域及椭圆估计；本批清偿局部边界 H²，尚未完成全域拼接或凸域统一 Hessian 估计。

## 实际数学、量词及假设

1. **真实坐标直线与导数。** Lₓ(t)=x+(t−x_r)e_r 满足 Lₓ(x_r)=x，实际一维向量导数为 e_r。凸集 U 的原像由真实仿射组合身份证明为凸，使用 α+β=1 正确处理平移项。链式法则给 `(g∘Lₓ)'(t)=Dg(Lₓ(t))(e_r)`，没有引入自由选择的“法向导数”。
2. **均值定理给完整双向严格比较。** 正方向 helper 输入原 g 全空间可微、U 凸以及 U 上实际 D_rg>0。连续性和导数身份满足 mathlib `strictMonoOn_of_deriv_pos` 的全部条件；该引理只在真实原像的内部需要正导数，由原像成员资格内部给出。所得 `StrictMonoOn.lt_iff_lt` 对原像中的任意 a、b 给完整 iff，而非仅 a<b 时的单向估计。负方向对实际 −g 求导，并交换 a、b 调用正方向，得到原 g 比较 ↔ b<a；减号和次序正确。此处没有要求 U 开放或原像非空，以两端点的真实成员资格保证使用合法。
3. **同号球与整个连接线段。** 对 C∞ g，实际 fderiv 连续，因此 D_rg 在 c 的非零符号给一个 ε>0 的同号球。G(x)=x+(Ψ(x)−x_r)e_r 连续且 G(c)=c。实际选择
   `V=N∩ball(c,ε)∩G⁻¹(ball(c,ε))`，
   开放且含 c，并保证 x 与 G(x) 同在该凸球。法向直线连接这两个点的整个线段遂在同号区域中；原图邻域 N 本身不需要凸。以 a=x_r、b=Ψ(x) 调用真实比较，使用 g(Gx)=g(c)，准确得到正 D_rg 时 `g(x)<g(c) ↔ x_r<Ψ(x)`，负 D_rg 时 `g(x)<g(c) ↔ Ψ(x)<x_r`。没有从水平集相等猜测子水平集方向，也没有只检查线段端点的导数符号。
4. **原正则水平数据内部供应全局图资格。** 一般最终几何 theorem 输入全局解析 g、g(c)=a、Dg(c)≠0。T244 从同一 g/c 内部选择 r、全局 C∞ 且法向平移不变的 Ψ、真实高度 Lipschitz 常数 C 和各实际斜率 Lipschitz 常数 B_i；保留非零原 D_rg(c)、Ψ(c)=c_r 及邻域图点身份。按这一原导数的正负分支取得上述完整域侧 iff。解析 g 降为 C∞ 合法，raw 的外层 `⊤`（ω）和 `↑⊤`（C∞）未混淆。r、Ψ、C、B、V 都是存在结论，不是新增几何输入；具体指数和应用内部供应解析性。
5. **截断的整个拓扑支撑合法。** 从 c∈V、V 开放选 ball(c,ε)⊆V；实际 `ContDiffBump c` 的内外半径为 ε/4、ε/2，构成 `SpatialTest univ`。取 δ=ε/4>0。其拓扑支撑是 closedBall(c,ε/2)，严格包含于 ball(c,ε)⊆V；在 ball(c,δ) 上由闭内球恒 1 身份得到 η=1。不是只证明普通 support 或中心点上的资格，也没有要求 η 支撑严格包含在原子水平域内。
6. **两向换域条件都由同一个 iff 给出。** 令 S={g<a}，T 为所选全局上图或下图。对整个 tsupport η 内的点，域侧 iff 分别供应 `S∩tsupport η⊆T` 与 `T∩tsupport η⊆S`。小区域 R=S∩ball(c,δ) 开放；由 ball⊆V 得 R⊆T，另有 R⊆S、η|R=1。两分支把这些条件按正确顺序传给 T242 上图/下图 wrapper，未遗漏逆向支持条件或把两种图侧互换。
7. **应用的是真实完整截断方程。** 已重读实际 T242：对原 u∈H¹₀(S)，v 是合法 H¹ 零延拓再限制到 T；ηv 的 H¹₀(T) 成员资格由原测试闭包及完整 H¹ 图连续性得出。原方程仅在支撑已合法的 ηφ 上使用，内部得到全体目标测试下的载荷
   `ηE(f)−2∑i(D_iη)D_i v−∑i(D_i²η)v`。
   余项负号、系数 2、二阶截断项及真实 L² 资格完整保留。没有假设未截断零延拓 v 满足 T 上原 PDE，没有给原 u 假设 H²，也没有省略边界分布项。
8. **图域 H² 与同一原状态内部恢复。** T242 wrapper 实际调用 T241 对完整 H¹₀ 图域弱 Poisson 解的 H² 定理；T241 内部使用真实 shear、原梯度变换、实际椭圆系数方程与逆 H² 传输。本批的 T244 输出正好供应其全局 Ψ/C/B 条件，斜率条件字面为实际 fderiv 方向求值，没有新输入 hreg 或目标 PDE。得到图域 H² jet 后，真正限制到 R；η=1 与真实 AE 值身份，再由原弱 jet 值唯一性给
   `truncate¹ U = restrictSubdomain inter_subset_left u`。
   这等式包含完整值和全部一阶弱字段，不是只给一个无关的 H² 函数或仅作逐点代表比较。
9. **原内域的最终实例。** 对任意有限半空间数据及 n，实际内点 z 和 frontier 点 c 给指数和 g(c)=1/2 与 Dg(c)≠0；有限指数和全局解析性内部供应。最终 PDE 输入只有原完整 H¹₀ jet u、同域真实 L² f 和原全部 `SpatialTest` 的 `IsWeakNegativeLaplacian u f`。输出的 H² jet 位于原 `halfspaceSmoothInner∩ball(c,δ)`，H¹ 截断仍为同一 u 的限制。没有图、支持、额外边界值或局部目标正则性假设。

图及截断在证明中由几何数据构造后才用于 u/f，但两个 H² 声明的实际量词是任意 u/f 后存在 δ 和 U；本报告不将它擅自改写为已声明的统一 δ 定理。没有穷竭参数、边界点或全部几何数据一致的估计声称，也没有新增有限体积、全域有界或原状态光滑假设。固定 r 的 helper 要求真实 r:Fin d；一般非零 Dg 和具体内点/frontier 条件排除无法选法向的退化情形。局部 H² 成员不等于完整全域 H² 或原统一椭圆估计，后续有限拼接与凸域控制仍需证明。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `SublevelGraphRegularity.lean`，raw 行为固定完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 43374 | `coordinateLine` | PASS；真实法向仿射直线。 |
| 17 / 43376 | `coordinateLine_self` | PASS；原法向参数恢复同一点。 |
| 20 / 43379 | `coordinateLine_hasDerivAt` | PASS；实际导数 e_r。 |
| 26 / 43382 | `coordinateLine_convex_preimage` | PASS；原凸集的真实仿射原像凸性。 |
| 44 / 43385 | `coordinateLine_lt_iff_of_positive` | PASS；实际正导数与均值定理给完整严格 iff。 |
| 63 / 43396 | `coordinateLine_lt_iff_of_negative` | PASS；实际 −g 导数和正确反序 iff。 |
| 75 / 43407 | `exists_sublevel_hypograph_near_of_positive` | PASS；同号凸球内准确下图侧。 |
| 100 / 43419 | `exists_sublevel_epigraph_near_of_negative` | PASS；同号凸球内准确上图侧。 |
| 125 / 43431 | `exists_sublevel_graph_near_regular` | PASS；原正则 g 内部供应所有图与实际导数界，完整域侧二选一。 |
| 146 / 43447 | `exists_spatial_cutoff_one_near` | PASS；真实紧支 C∞ 截断、全拓扑支撑包含及小球恒 1。 |
| 163 / 43452 | `exists_local_dirichlet_H2_of_regular_level` | PASS；原完整 H¹₀ 弱方程内部给同状态局部完整 H²。 |
| 190 / 43467 | `halfspaceSmoothInner_local_boundary_H2` | PASS；原指数和内点/frontier 数据供应全部几何资格。 |

## 固定依赖与本地证据

实际 Carleman 导入闭包 **234 文件**，其中 **233 旧文件**相对 base 逐 Git blob 不变；唯一新增数学模块为本批模块。已直接完整读取本批、`SmoothGraphHeightExtension`、`BoundaryCutoffTransfer`、`GraphDomainRegularity`，核对实际方向导数、全局延拓、原闭包、截断方程和同状态恢复的调用边界。mathlib 均值定理及实际 bump 半径/拓扑支撑/恒 1/紧支接口也已直接读取。

T244 正式报告已全文读取并验证单文件提交 `716031127e9645f4476e104ec26dd92d6c51f4bd`，reviewed_at=`2026-10-20T08:48:04+00:00`，9/9 PASS，proof 为本报告 base；其 **214 文件**实际导入闭包与本 proof 不变。T242 报告 `faecb1d3d0dd83a2ec6ab2b7662181cf9d46ac07` 保持冻结，其已验收 proof `4acd24f5158fda6688403c600ddbd9d2a131c379` 的 **225 文件**闭包也逐 blob 不变。没有用报告代替本批真实调用检查。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和 12 项 `#check`/`#print axioms` 齐全，声明清单精确匹配源码、T245/C261 台账和 raw。AGENTS、PROJECT_OPERATIONS、state/README 摘要与此前已读协议一致。

- `/tmp/carleman-t245-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:51:30.594016+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 记录均 exit 0。
- `/tmp/carleman-t245-local-source-manifest.txt`：**1042 项、113101 bytes**，SHA256 `3f2829809d3e4fcb20765d622d07ccc18e842aaaca6475bb0944c4895b6a9440`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及逐项 SHA256 全部匹配固定 Git blob。
- `/tmp/carleman-t245-target-build.log`：**3419 jobs** 成功，113 bytes，SHA256 `5565a4ae49b60ea68b6f28447df5188f7767b5e3ecc5c69122824c8b098b8bcd`。`/tmp/carleman-t245-build.log`：**4284 jobs** 成功，80 bytes，SHA256 `614a2865b68bd12fa2c5aa879babc645acbf9bb11f8b4b947b2bf8a5ade0d6b4`。`/tmp/carleman-t245-axioms.log` 为 0 bytes。
- `/tmp/carleman-t245-sublevel-graph-local-axioms.txt`：**3340630 bytes**，SHA256 `60640617f835da4f833cfca70ed56359498ebdb1b0c40d2f42f3fd3d19db6bbd`。12 项完整类型及公理逐项核对；全文件 3957 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际尾部确认 **9977 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，没有重跑全库，没有查询远端 CI/看板，也没有将本地成功称为 CI 成功。

无修复项。接受本批 **AUXILIARY 原子水平图侧与同状态局部边界 H²**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
