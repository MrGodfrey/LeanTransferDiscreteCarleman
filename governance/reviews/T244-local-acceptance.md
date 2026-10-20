# T244 / C260 独立本机验收

- checked_sha: `31c84b810ce9f75a97bc2fc5a5cae481a9252183`
- mathematical_base: `e7240abc0fb7acb6a0e456cd916f1845a114b72a`
- reviewed_at: `2026-10-20T08:48:04+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，9/9 显式声明（8 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；真实局部高度的全局光滑法向不变延拓，并内部提供高度及全部斜率的全局 Lipschitz 常数。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Geometry/SmoothGraphHeightExtension.lean`、9 项 raw 完整类型、公理、analysis/MATH_SPEC/台账，核对原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 的完整 Dirichlet 正则性和统一椭圆估计尚未由本阶段完成；本批提供图域路线需要的真实全局高度资格。

## 实际数学核对

1. **真实紧支延拓只使用给定局部光滑性。** 从 c∈V 且 V 开放取得 ε>0、ball(c,ε)⊆V，构造实际 `ContDiffBump c`，内外半径分别 ε/4、ε/2。其拓扑支撑精确为 closedBall(c,ε/2)，严格包含于 V。令 h=βψ：在 V 内用原 `ContDiffOn` 和开放邻域得到真实光滑乘积；在 V 外，由 β 的整个拓扑支撑包含于 V 得 β 在该点附近恒零，故 h 在该邻域也恒零。没有要求 ψ 在 V 外连续、可测或有界。紧支性来自实际 β，局部 h=ψ 来自 β 在 c 附近恒为 1。
2. **Lipschitz 常数由真实导数界内部生成。** 对任意给定实赋范空间间的全局 C∞ 紧支 f，实际 `fderiv ℝ f` 连续，其拓扑支撑包含在 f 的拓扑支撑内，因此有全局有限算子范数界 M。在 0 点的范数非负性保证选出的 M≥0，可包装为 NNReal。均值估计在全空间的凸性上给真正 `LipschitzWith M f`；没有输入目标 Lipschitz 常数、未验证的导数上界或有限维自动连续性。此通用 lemma 的结论不要求有限维；第一步 bump 紧支的具体应用则确在有限维欧氏空间中。
3. **切向重置是准确的仿射映射。** P=`coordinateTangentProjection r` 是实际 CLM `x↦x−x_r e_r`。证明将原 `coordinateLevelMap r (fun _=>a)` 精确识别为 `Px+a e_r`，继而给所有 x 的实际 Fréchet 导数 P 和全局 Lipschitz 常数 ‖P‖。此处不把该重置当作可逆 shear，也没有需要 P 可逆或 ‖P‖>0 的除法。
4. **法向不变延拓及全部实际斜率。** 取 Q(x)=Px+c_r e_r，Ψ=h∘Q。Q 全局光滑，且 Q(x+te_r)=Q(x)，故 Ψ 对所有实 t 全局法向不变。实际链式给
   `D_iΨ(x)=Dh(Qx)(P e_i)`。
   对每个 i，函数 `z↦Dh(z)(P e_i)` 的光滑性来自真实 Dh，其紧支性来自导数支撑包含关系；再用第 2 项取得真实全局 Lipschitz 常数 B′_i。复合 Q 后，输出高度常数 C′‖P‖ 和各斜率常数 B′_i‖P‖。这些常数是存在结论，不是新输入，也没有跳过实际 Ψ 导数的身份验证。
5. **局部相同正确使用中心和原不变性。** Q(c)=c，Q 连续，所以 h=ψ 的 c 邻域身份可拉回为 h(Qx)=ψ(Qx) 的 c 邻域身份。原 ψ 的全局法向不变性在每个 x 处取 t=c_r−x_r，给 ψ(Qx)=ψ(x)。因此 Ψ 与同一原 ψ 在 c 的真实邻域内相等；没有直接对随 x 改变的平移参数求导。原不变性在这个通用 helper 中显式保留，而在后续实际水平图应用中由 T243 内部供应。
6. **不将最终 Ψ 误称紧支。** 紧支结论只给中间 h 和用于取界的 Dh 及其方向求值函数。沿整条法向直线不变的 Ψ 一般不紧支，最终声明没有要求它紧支；斜率 Lipschitz 使用紧支函数与 Q 的复合，而不是声称复合后支撑仍紧。d=1 时 P=0、输出常数可为零，所有论证仍合法。固定 r 版本明确需要 r:Fin d；不伪造零维法向。
7. **真实正则水平图保留全部原身份。** 对原解析 g 和 Dg(c)≠0，T243 的真实基与逆函数图先供应 r、非零 D_rg(c)、局部解析 ψ、V/W 及原图身份。解析资格可降为 C∞，再应用本批延拓。由 V、W 和 Ψ=ψ 的邻域交取得实际开放 N，c∈N；在 N 内用同一高度值逐点替换原图投影，保留
   `g(coordinateLevelMap r Ψ x)=g(c)`、
   `g(x)=g(c) ↔ x_r=Ψ(x)`，
   并保留 Ψ(c)=c_r 和原非零 D_rg(c)。N 的条件既保证原逆图合法，也保证延拓相同，没有只在中心点成立便推广到整个邻域。
8. **原指数和边界应用不新增图或界假设。** 最后 theorem 对任意有限半空间数据、n、实际内点 z 和 frontier 点 c，使用真实 `halfspaceSmoothInner_boundary_regular` 给 g(c)=1/2 与 Dg(c)≠0。已直接核对该依赖：开放性/连续性给准确边界水平值，指数和的实际一阶支撑不等式与内点严格小于 1/2 排除零导数；有限指数和的全局解析性内部供应 g 资格。最终据此输出 r、Ψ、C、B、N，水平恰为 1/2，图点和非零方向导数都对应原 g。空指标、零维或空内域无法同时满足相应真实内点/边界输入，没有从这些退化情形虚构坐标。

这些常数、邻域和所选坐标可依赖原 g、c、局部图与 bump；具体内域应用还可依赖 n 和半空间数据。未声称对整个穷竭或所有边界点统一。最终仅得到水平集对应，未由水平集相等擅自推出子水平域在图的哪一侧；侧身份、实际截断覆盖、有限局部拼接和凸域统一 Hessian 估计仍待。一般 g helper 显式要求解析性，实际指数和应用已内部满足，未要求原 PDE 状态或目标 H² 资格。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`。源码行指固定 `SmoothGraphHeightExtension.lean`，raw 行指本批固定审计文件完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 43300 | `exists_compact_smooth_extension_near` | PASS；真实 bump 与局部零性质给紧支全局 C∞ h，保持原局部值。 |
| 36 / 43306 | `exists_lipschitzWith_of_smooth_compact` | PASS；实际 Fréchet 导数紧支界和均值估计内部给常数。 |
| 48 / 43310 | `coordinateTangentProjection` | PASS；真实删除法向坐标的 CLM。 |
| 51 / 43313 | `coordinateLevelMap_constant_affine` | PASS；准确切向线性项加法向平移。 |
| 57 / 43317 | `coordinateLevelMap_constant_lipschitz` | PASS；真实仿射重置的全局 ‖P‖ 界。 |
| 63 / 43320 | `coordinateLevelMap_constant_hasFDerivAt` | PASS；所有点实际导数为 P。 |
| 71 / 43323 | `exists_smooth_normal_invariant_extension` | PASS；真实 Ψ、全部导数界、全法向不变性和原邻域相等，不假称 Ψ 紧支。 |
| 111 / 43338 | `exists_bounded_smooth_coordinate_level_height` | PASS；原正则解析 g 内部供应图，保持图点、非零原方向导数及全部局部水平身份。 |
| 139 / 43354 | `halfspaceSmoothInner_bounded_coordinate_level_height` | PASS；原指数和/内点/frontier 输入内部给全部资格，精确水平 1/2。 |

## 依赖与固定本地证据

导入闭包 **214 个 Carleman 文件**，其中 **213 个旧文件**相对 base 逐 Git blob 不变，唯一新模块为 `SmoothGraphHeightExtension`。本次完整读取本批模块与实际 `CoordinateLevelGraph`、`AnalyticLevelCharts`，另核对 `HalfspaceSmoothExhaustion` 的真实指数定义、边界正则性及支撑不等式。T243 冻结报告全文读取并核对提交 `a8951af50a513ccfe529b27d1385920ff03c2ee8`；checked_sha 为本报告 base，reviewed_at=`2026-10-20T08:41:49+00:00`，12/12 PASS；报告未代替本次实际构造与调用检查。

实际 mathlib 的 `ContDiffBump` 半径、支撑、邻域恒 1 与内积空间实例、`HasCompactSupport.fderiv/fderiv_apply` 和 `lipschitzWith_of_nnnorm_fderiv_le` 的类型及实现已直接读取。Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入、9 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t244-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:44:52.822417+00:00`；`lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 实际执行记录均 exit 0。
- `/tmp/carleman-t244-local-source-manifest.txt`：**1041 项、112989 bytes**，SHA256 `45b00f27c80bcb9ea6656eb3fbe9acf0b80554ed18738a4e58a1d3babe962c35`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性和逐项摘要均与固定 Git blob 匹配。
- `/tmp/carleman-t244-target-build.log`：**3399 jobs** 成功，116 bytes，SHA256 `04e68599410947f0f2e395dccfb9833ece75632b38216109fbe1eecd3c0d6c14`。`/tmp/carleman-t244-build.log`：**4283 jobs** 成功，80 bytes，SHA256 `e5c2aa56154357d101e9a9fcfb36eb0df218a2af3054d4a3a9dda20085ed9967`。`/tmp/carleman-t244-axioms.log` 为 0 bytes。
- `/tmp/carleman-t244-smooth-height-extension-local-axioms.txt`：**3333490 bytes**，SHA256 `657e48a508f2e054f4588f44cd3c06f0324e48a5a871d7993f85470cbb5d360c`。9 项完整类型逐一核对；全部 **3955 个显式公理记录**仅含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，实际尾部确认 **9963 声明递归审计 PASS**，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地证据，没有重跑全库，没有查询远端 CI/看板，没有把本地成功称作 CI。

无修复项。接受本批 **AUXILIARY 实际全局光滑法向不变高度及内部导数界**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改数学、台账、原稿、根导入、公理工具或其他报告，不 push。
