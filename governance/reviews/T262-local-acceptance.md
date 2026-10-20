# T262 / C278 独立本机数学验收

- checked_sha: `49ca9a4344f0e015567fd8916e61a9a768358ba7`
- base_commit: `708eae70c82d9c0b1d60f6907f0202201d518a16`
- reviewed_at: `2026-10-20T11:17:46+00:00`
- reviewer: `accept_spatial_lemma`（独立于实现者）
- result: **PASS，17 / 17 显式声明**
- axiom_check: **PASS**
- scope: **AUXILIARY**；本批不提升 P024，原文覆盖保持 19 / 26。
- evidence_source: **local**；未查询远端 CI、看板，未重跑全库或不变依赖。

已直接读取固定 Git 对象的三个新增模块、全部实际打印类型、分析文件、MATH_SPEC 对应段落、原稿及下述关键依赖。结论为真实光滑周期状态在真实指数和内域上的积分不等式，未发现阻断缺陷。本报告定稿后冻结正文和签发时间，仅提交本文件。

## 原文对应与实际结论

原稿 `paper/main.tex:2672–2730` 的 `prop:continuousCE` 要求原域、原 C² 时间权、全部弱周期状态、两个时间方向及先于 T 的定量常数。本批对应其中 2696–2704 行的真实热通量与积分步骤：固定内域
\[
S_n=\{x:g_n(x)<1/2\},\qquad
g_n(x)=\sum_i\exp((n+1)(b_i-\ell_i x)),
\]
取实际内点 c、\(\rho(x)=e^{-\lambda|x-c|^2}-2\)、\(L(t,x)=q(t)\rho(x)\)、\(z=e^L u\)。最终使用已有真实 `heatConjugationK` 和 `heatCarlemanBulk`，证明
\[
\int_{[0,T]\times S_n}\mathrm{heatCarlemanBulk}
\le \int_{[0,T]\times S_n}|e^L(\partial_tu-\Delta u)|^2 .
\]
两侧均是限制 Lebesgue 乘积测度下的实际积分；没有新定义一个等同于目标估计的抽象“能量”。

最终定理显式要求 L、辅助函数 p、u 全空间 C∞，三者严格 T 周期，u 对所有时间在真实 frontier 上为零，L 具有上述实际高斯相位公式，λ≥0、T≥0、q 在整个 Icc 上非负，并给定 c∈Sₙ。有限半空间原域有界。几何正则性、紧闭包、支撑方向和通量符号在内部证明。本批没有将这些光滑 core 条件冒充原弱状态结论；p 仍是任意满足上述条件的辅助函数，尚未在最终接口选定原 Ψ 并完成吸收。

这里只得到积分步骤的系数 1；尚未得到原观察项的定量 Carleman 估计，也未处理一般域的弱周期图密度、原 C² 权扩展及反向时间结论。后续 λ、β、q_c、C 必须从固定外域及观察域选择并先于全部内域指标 n，不能从本批薄层宽度或逐域紧性推出这种统一性。

## 逐声明核对

以下名称均位于 `Carleman` 命名空间。三模块实际源码顺序、固定台账 T262/C278 的清单、根导入及公理打印项完全一致：16 theorem、1 def，无遗漏的本批显式声明。

| 模块 / 行 | 声明 | 实际核对与结论 |
|---|---|---|
| LevelHeatBoundary:12 | `pointwiseHeatFlux_unnormalized_eq` | **PASS**。用实际空间方向导数展开完整五项热通量；z=0、∂tz=0、Dᵢz=aNᵢ 时，真实法向配对等于 \(2D_NL\,a^2\|N\|^2\)。没有单位法向、除以 ‖N‖ 或特殊坐标假设。 |
| :34 | `spacetime_level_zero_derivatives` | **PASS**。g 解析且 Dg(x)≠0；真实局部水平图给切片梯度为 Dg 的倍数；所有时间的水平零值令真实时间切片为常零函数，故其真实导数为零。 |
| :51 | `gaussian_level_heat_flux_nonpos` | **PASS**。对同一 \(z=e^Lu\) 供应上述三身份，实际空间链式法则给 \(D_NL=qD_N\rho\)，原高斯支撑方向、λ≥0、q(t)≥0 给非正号。k、p 的边界项因实际 z=0 消去。 |
| :81 | `halfspaceSmoothInner_gaussian_heat_flux_nonpos` | **PASS**。原内点及指数和凸性内部给 Dg≠0、真实 frontier=水平 1/2 和支撑符号；从原 frontier 零值推出辅助引理所需的整水平零值。最终没有额外 whole-level 边值输入。 |
| LevelDivergence:12 | `weighted_level_divergence_identity` | **PASS**。实际紧支 IBP 逐坐标求和，以真实 \(D\eta=-\kappa Dg\) 得 \(\int\eta\,\mathrm{div}F=\int\kappa F\cdot\nabla g\)。全部拆分项可积性内部证明；无 Gauss 公式假设。 |
| :42 | `levelLayer_scalar_upper_bound` | **PASS**。实际正则 frontier 上 \(\delta\|\nabla g\|^2-F>0\)，紧坏集最大值供应薄层；真实 κ≥0 和完整拓扑支撑给全点上界 \(\kappa F\le\delta\kappa\|\nabla g\|^2\)。 |
| :69 | `levelCutoff_divergence_upper_bound` | **PASS**。将真实向量通量代入上一项；κ 通量与 κ 梯度平方均由真实紧支连续性可积；准确给出 \(\int\eta\,\mathrm{div}F\le\delta\int_S|\Delta g|\)。 |
| :98 | `level_divergence_nonpos` | **PASS**。εₙ=1/(n+1) 的真实截断积分先收敛，固定任意 δ>0 得 L≤δM，再以 δ→0 得 L≤0；不要求宽度在 F、δ、时间或 n 上统一。 |
| SublevelHeatIdentity:16 | `domainTimeIntegral` | **PASS**。真实 \((\mathrm{volume}|_{[0,T]})\otimes(\mathrm{volume}|_S)\) 上的积分定义。 |
| :20 | `continuous_domain_time_integrable` | **PASS**。有界 S 的紧闭包与紧 Icc 供给连续函数实际可积性，经乘积限制测度与子集限制到所需域；无额外有限积分输入。 |
| :29 | `domainTimeIntegral_eq_iterated` | **PASS**。在上述真实可积性下使用 Fubini，先空间后时间的积分与定义精确一致。 |
| :34 | `domainTimeIntegral_add` | **PASS**。两个连续函数各自可积后使用真实积分可加性。 |
| :39 | `domainTimeIntegral_mono` | **PASS**。两侧可积，使用实际全点序关系推出真实积分序关系。 |
| :44 | `domainTimeIntegral_nonpos_of_spatial` | **PASS**。Icc 上每个实际空间积分非正，经前述 Fubini 得真实柱积分非正。 |
| :51 | `domainTimeIntegral_periodic_derivative` | **PASS**。实际反序 Fubini、Icc/Ioc 的 Lebesgue a.e. 相等及真实切片 FTC，得到周期端点相消；T=0 也合法，没有除以 T。 |
| :65 | `halfspaceSmoothInner_heat_flux_integral` | **PASS**。实际时空热通量切片为 C∞ 向量场；内部供应指数和紧性、正则性及前述边界符号，再把真实空间 fderiv 精确识别为时空空间方向导数。 |
| :98 | `halfspaceSmoothInner_smooth_heat_carleman_inequality` | **PASS**。使用同一原相位、共轭状态、实际 k 和完整 bulk；积分真实点态不等式，真实时间通量周期项为零、空间通量积分非正，得上述系数 1 结论。 |

完整打印类型由固定 raw 的 44971–45120 附近逐项核对；最后一项跨行公理列表亦已完整检查。辅助函数中的泛型假设没有在最终定理中被偷偷替换为结论。

## 关键证明、量词和依赖

**边界方向。** 对 \(S=\{g<a\}\)，代码使用真实梯度 `graphSlopeVector g x`，其与任意方向的内积等于实际 fderiv。原内点 c 和凸支撑不等式给
\(g(x)+Dg(x)(c-x)\le g(c)<a=g(x)\)，方向是外侧法向。高斯导数为
\(-2\lambda e^{-\lambda|x-c|^2}\langle x-c,N\rangle\)，因此非正。未归一化公式保留 \(\|N\|^2\)，与原单位法向通量完全相容。空间维数与退化情形没有非法除法；实际使用水平图的地方明确有非零微分。

**真实水平集，而非凭图猜测。** 已直接核对 `regular_level_zero_gradient_hessian` 的实际坐标图链式证明，以及 `halfspaceSmoothInner_frontier_of_level` 的原内点—水平点开线段凸性论证。后者把整个水平 1/2 放进真实 frontier，因而最终只需原边界零值。时间导数为零来自固定边界点上的全时间常零函数，不是把空间零值直接当作时间导数条件。

**两次极限。** 已重新读取 `SmoothLevelCutoff` 的真实 transition 定义、闭端点导数、\(D\eta=-\kappa Dg\)、κ≥0、完整 tsupport 层
\(a-2\varepsilon\le g\le a-\varepsilon\)，及 `ClassicalConvexHessian` 的紧坏集、质量界和 DCT。质量恒等式
\(\int\kappa\|\nabla g\|^2=\int\eta\Delta g\)
来自真实紧支 IBP；其上界 M=\(\int_S|\Delta g|\) 可积且与 ε、δ 无关。无需假设 Δg≥0。

DCT 的支配函数为实际 \(1_S|\mathrm{div}F|\)，在有界闭包上连续可积。ηₙ 的全点极限是 \(1_S\)，包括边界处恒为零；没有使用未证明的边界零测结论。对每个 δ 先让 εₙ 最终进入对应薄层，再传积分极限，最后让 δ→0。F 或内域改变时薄层宽度、M 可改变，但其消去不留下误差常数。

**真正的热算子和时间通量。** 已直接复核 `PointwiseHeatIdentity`、`SpacetimeHeatIdentity`、`HeatIdentityRegularity`、`PeriodicHeatFlux` 和所用 `BoxIntegratedHeatIdentity` 规则。原 RHS 是 \(\partial_tu-\Delta u\)，不是其整个负号；bulk 是保留第一平方、矩阵项、真实 p 梯度交叉项和 B 项的既有表达式。点态等式仅舍去非负第二平方。M 是真实
\(\partial_t(kz^2-|\nabla z|^2)\)，V 是真实五项热通量散度。L、p、u 周期内部推出 k、z 及时间通量周期，不额外输入 M 的积分为零。所有 R/M/V/bulk 积分及拆合均有实际连续可积性，空间非正号在时间积分后方向保持正确。

**依赖边界。** 新模块递归 Carleman import 闭包共 251 个模块，其中 248 个旧模块与数学基线逐 Git blob 不变。额外核对本次实际使用的 `LevelBoundaryHessian`、`SmoothLevelCutoff`、`ClassicalConvexHessian` 分别与已验收 T247、T250、T251 固定证明逐字节一致；相关报告已冻结为 `3c514dbd3da93c2821920de26ca27cf04258eb3b`、`748e173a8693b7ad9cf3db536b36ce5c1983ab87`、`3d96393a4d297b3940792ecca761058831d5d28e`。本次直接审查了调用及关键实际证明，没有把历史报告当作新证明的替代。

## 固定本机构建与公理证据

独立读取 `/tmp/carleman-t262-local-evidence.json`：source=`local`、status=`PASS`、checked/source SHA 均等于本报告 proof，`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 记录 exit 0；finished_at=`2026-10-20T11:09:23.817190+00:00`。本次未重新运行构建，以下为对应固定执行产物的独立核验。

| 证据 | 独立核对 |
|---|---|
| `-local-source-manifest.txt` | 1061 条、115159 bytes；枚举固定树全部 tracked `.lean` 与三项工具链配置，逐 Git blob 计算 SHA256，集合和每条摘要全匹配；整体 `8bdc62e84b741e5b981d87702fb5a14b6e1c9b78673e40c51aa84fedf4d3147e`。 |
| `-foundation-build.log` | 两个基础模块成功，3426 jobs；168 bytes；`beba7e3fa6ffe9cdf0fc96576275c8b39b2061028e4dc592ea9297c76523b99f`。 |
| `-target-build.log` | `SublevelHeatIdentity` 成功，3451 jobs；109 bytes；`18163c0ea678cebe9b1c0651928b2895917783890bb4be348d4c2df7c4fc21d1`。 |
| `-build.log` | 根目标成功，4303 jobs；80 bytes；`2568d189d41f094307475f98295eba6539b576a25f35f9a80cd0c0144c2c4a01`。 |
| `-axioms.log` | 空 stderr，0 bytes。 |
| `-sublevel-heat-identity-local-axioms.txt` | 3475075 bytes；`ce72c409e057e545b1f9995c236a310178ab2660a6babc31669b6bbb32be5ac1`；实际末行全命名空间 **10340** 项递归审计 PASS。 |

上述文件前缀均为 `/tmp/carleman-t262`。17 个新增声明都在根目标导入和显式 `#check` / `#print axioms` 中；固定 raw 的全部 4168 个显式公理列表仅含 `propext`、`Classical.choice`、`Quot.sound`，另 10 个列表无需公理。递归审计实现与基线不变，没有 `sorryAx` 或新数学公理。每个本批声明自身只依赖上述标准基础公理。

工具链为 Lean 4.35.0（编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）；固定 lake lock 与实际干净 mathlib checkout 均为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。原稿相对基线逐字节不变，SHA256=`492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。已核对固定 AGENTS、操作协议和状态证据协议。

独立复核记录保存在 `/tmp/carleman-t262-review-verification.json`，逐声明完整类型摘录在 `/tmp/carleman-t262-reviewed-types.txt`。工作树后续 T263 及动态审计文件未作为本报告依据。

## 验收决定

**17 / 17 PASS，无修复项。** C278 可按上述固定版本登记 REVIEWED / AUXILIARY。已完成真实曲面热通量、真实散度积分符号和光滑周期内域的完整 bulk≤残差积分步骤。P024 的原弱状态、原 C² 权、原观察项和外域统一定量常数仍须后续独立清偿；本批不增加原文完成项。
