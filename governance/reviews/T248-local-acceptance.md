# T248 / C264 独立本机验收

- checked_sha: `c8fb6d0a150570c2a62ab9cc761d0f482af5aa6a`
- mathematical_base: `e84f958461360997f4705a75d4eaa6d3c77d2b21`
- reviewed_at: `2026-10-20T09:24:48+00:00`
- reviewer: 独立本机 Agent `accept_spatial_foundations`
- result: **PASS，14/14 声明（12 定理、2 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；原指数和内域上经典光滑零边值函数的真实点态凸边界通量非负性。保持 18/26，不提升 P023。**

已完整读取固定 `Carleman/Geometry/ConvexBoundaryFlux.lean`、14 项 raw 完整类型、公理、analysis/MATH_SPEC 与台账，对照原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求原凸多面体的完整正则性与图范数估计；本批仅完成该证明路线的经典点态通量步骤，不把它当作 Sobolev 估计或完整推论。

## 数学核对

1. **实际欧氏梯度和原 Laplacian。** `graphSlopeVector` 是原 `fderiv` 在全部标准正交基上的分量向量。真实正交基展开给任意 v 的 `inner(gradient f,v)=Df(v)`；因此非零 Dg 确实给非零梯度，整个泛函 Du=qDg 确实给梯度向量比例。前三个转换不输入一个候选梯度。一般 f 版本使用 Lean 的实际 `fderiv` 定义，不在不可微点另声称经典导数存在；最终 u/g 的真实光滑性明确供应。原 `spatialLaplacian` 是逐坐标方向导数之和，实际 `smooth_directional_fderiv_eq` 把每个方向项识别为同一二阶 Fréchet 导数的对角值，故得到完整 trace，未换用假定的 Hessian 或漏掉坐标。
2. **真实切向量且无除法。** 令 N=∇g(c)、p=‖N‖²，定义 `w_i=p e_i−N_i N`。由真实内积的坐标身份得到 `inner(N,w_i)=pN_i−N_ip=0`。继而 Dg(c)w_i=0，准确满足下游全部切向二次型身份的前提。此构造不是一个假设存在的单位切向标架；未除以 p，在 N=0 时也合法。
3. **任意双线性型的完整展开。** 对任意真实连续双线性 H，逐项展开为
   `p²H(e_i,e_i)−pN_iH(e_i,N)−pN_iH(N,e_i)+N_i²H(N,N)`。
   两个混合和分别用 N 的真实基展开计算为 H(N,N)，而不是互相交换 H 的两个变量；同时 `ΣN_i²=p`。因此准确得到
   `ΣH(w_i,w_i)=p(p trace H−H(N,N))`。
   原声明没有对称性前提，证明也没有偷偷用 Hessian 对称性。幂次 p²=‖N‖⁴ 与最后合并的一个 p 均正确。空维度/零向量时等式仍成立。
4. **通量确为原经典表达式。** 定义
   `F(u,g,c)=Δu(c) inner(∇u(c),∇g(c))−D²u(c)[∇u(c),∇g(c)]`，
   第二项是实际 CLM-valued 二阶导数的原有序求值；不是一个另加符号假设的 scalar。它针对子水平域的未归一化水平梯度 N，不把 N 误称为单位法向。对 C∞ u，真实二阶导数与固定基求值给 Δu 的 C∞；对 C∞ u/g，实际导数、内积、CLM 求值及乘减闭性给 F 的 C∞。这两项只给光滑性，不额外声称可积性或 Green 公式。
5. **同一 q 的平方决定符号。** helper 明确输入整个 Du=qDg 和同一 q 对全部切向 v 的 `D²u[v,v]=qD²g[v,v]`。对实际 w_i 求和并用第 3 项与原 Laplacian trace，得到
   `p(pΔu−D²u[N,N])=qΣD²g[w_i,w_i]`。
   将 ∇u=qN 代入原 F 后，两边乘同一个 q，准确得到
   `pF=q²ΣD²g[w_i,w_i]`。
   没有除以 q，也没有遗漏 q=0 情形；不要求 q 正、负或非零。一般 helper 的边界微分数据仍是显式前提，不能将它单独解读成任意 u/g 的无条件通量结论。
6. **非负性消去严格正因子。** 实际 Dg(c)≠0 经第 1 项给 p>0。Hessian 二次型非负适用于每个实际 w_i，故有限和非负；q²≥0 给 pF≥0，再用 p>0 得 F≥0。没有用“u 的切向 Hessian 非负”这一不成立的中间结论，也没有使用 q 的符号。该层输入实际 hreg、hdata、hconv，分别在最终具体应用内部清偿。
7. **最终原几何与边值清偿全部 helper 数据。** 最终声明量化任意 d、有限半空间族 ℓ/b、任意 n、一个真实内点 z、任意全局 C∞ u、原整个 frontier 上的真实零值和任意真实 frontier 点 c。旧 `halfspaceSmoothInner_boundary_regular` 从原指数和、内点与 frontier 证明准确水平 1/2 及 Dg(c)≠0。已重读 T247：实际水平图复合的两次微分给同一 q 的全梯度比例和全部切向二次型比例；真实凸开线段证明整个水平 1/2 属于 frontier，故最终原 frontier 零值足以供应其 whole-level helper。原指数和的实际二阶导数为
   `Σ exp((n+1)(b_i−ℓ_i x))·((n+1)ℓ_i v)²`，
   于是内部给全部 v 的 Hessian 非负性。最终没有额外输入图、切向 Hessian 身份、曲率、通量符号、H² 正则性或 PDE。

实际点态结论不需要域有界；它对原有界穷竭内域当然适用，但不因此证明任何积分或统一常数。d=1 时切向平方和为零仍与通量身份一致；d=0/空指标的代数声明照常成立，无法同时满足内点与真实边界非退化条件的情形不制造虚假法向。u 仍为全空间经典 C∞ 函数，边值为真实 frontier 点值；没有把 T246 的 H² 成员资格误用为光滑性、边界迹或保持边界的强密度。实际通量积分、H²∩H¹₀ 强逼近、随穷竭统一的 Hessian 估计以及原多面体传递仍待。

## 全部声明逐项结论

名称统一带前缀 `Carleman.`；源码行为固定 `ConvexBoundaryFlux.lean`，raw 行为固定审计文件中的完整类型起点。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 12 / 43714 | `euclidean_coordinate_expansion` | PASS；全部标准正交坐标的真实向量展开。 |
| 17 / 43717 | `graphSlopeVector_inner` | PASS；原梯度与实际 Df 对任意方向的配对身份。 |
| 25 / 43720 | `graphSlopeVector_ne_zero` | PASS；非零原导数推出非零原梯度。 |
| 33 / 43723 | `graphSlopeVector_multiple` | PASS；整个原导数比例推出向量比例。 |
| 41 / 43726 | `scaledLevelTangent` | PASS（定义）；p e_i−N_iN，未归一化或除法。 |
| 44 / 43728 | `scaledLevelTangent_inner` | PASS；实际内积切向身份。 |
| 50 / 43731 | `bilinear_scaled_tangent_sum` | PASS；全双线性展开、两个混合和分别计算，无对称性输入。 |
| 76 / 43737 | `spatialLaplacian_eq_hessian_trace` | PASS；原 Laplacian 与实际 Hessian 完整 trace 相等。 |
| 82 / 43742 | `levelBoundaryFlux` | PASS（定义）；实际 Δu、梯度和二阶导数的原通量表达式。 |
| 86 / 43744 | `spatialLaplacian_contDiff` | PASS；原 C∞ u 内部给实际 Laplacian 的 C∞。 |
| 96 / 43747 | `levelBoundaryFlux_contDiff` | PASS；原 C∞ u/g 内部给实际通量的 C∞。 |
| 104 / 43750 | `levelBoundaryFlux_scaled_identity` | PASS；pF=q²ΣD²g[w_i,w_i]，全部因子和方向正确。 |
| 126 / 43761 | `levelBoundaryFlux_nonneg` | PASS；同一 q 的平方与 p>0 给非负，无 q 符号条件。 |
| 141 / 43771 | `halfspaceSmoothInner_boundaryFlux_nonneg` | PASS；原 frontier 零值和原指数和几何内部清偿所有微分/凸性资格。 |

## 固定依赖与本地证据

导入闭包 **222 个 Carleman 文件**；其中 **221 个旧文件**相对 base 逐 Git blob 不变，唯一新增数学模块为本批模块。本次完整读取本批及 `LevelBoundaryHessian`，重读 `GraphEllipticForm` 的实际梯度定义/分量/光滑性、`SmoothLaplacianProduct` 的原 Laplacian 和 `HalfspaceSmoothExhaustion` 的实际指数和/凸性/一阶导数/边界正则性。mathlib 的真实欧氏正交基、`sum_repr`、基向量内积及平方范数有限和实现已直接核对。

T247 冻结报告全文读取，提交 `3c514dbd3da93c2821920de26ca27cf04258eb3b`，checked_sha 为本报告 base，reviewed_at=`2026-10-20T09:17:52+00:00`，11/11 PASS；该提交的报告与当前固定 proof 所含报告逐字节相同。报告未替代上列实际调用审查。新源码、独立声明清单、T248/C264 台账与 raw 的全部 14 项顺序一致；实际 12 theorem、2 def，无遗漏。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入和 14 项 `#check`/`#print axioms` 齐全。

- `/tmp/carleman-t248-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T09:21:07.895836+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 的执行记录均 exit 0。
- `/tmp/carleman-t248-local-source-manifest.txt`：**1045 项、113424 bytes**，SHA256 `2f2d9366cfb89764f1b1e57596239b7b631735458722b243dd6ec46610a472e5`。独立枚举固定提交所有 tracked `.lean` 和三个工具链配置，路径集合、唯一性与每项 SHA256 均匹配固定 Git blob。
- `/tmp/carleman-t248-target-build.log`：**3407 jobs** 成功，108 bytes，SHA256 `f8751fda66f149cbc129f46c4f001ad0072a3b73c72e2dddc693465cc1262088`。`/tmp/carleman-t248-build.log`：**4287 jobs** 成功，80 bytes，SHA256 `687199c21d002fb6d4881952e6dad775f0322282b716b76c42b378079d984e84`。`/tmp/carleman-t248-axioms.log` 为 0 bytes。
- `/tmp/carleman-t248-convex-boundary-flux-local-axioms.txt`：**3362279 bytes**，SHA256 `759134cfcf5bd7fd1a664f4c01b2448f3166403631f39beac76dc685fb1d7102`。14 项完整类型及公理逐项核对；全文件 **4003 个显式公理记录**仅含 `propext`、`Classical.choice`、`Quot.sound` 或无公理。实际尾部为 **10019 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地证据，未重跑全库、未查询远端 CI/看板，未把本地成功称为 CI。

无修复项。接受 **AUXILIARY 经典点态凸边界通量**，保持 18/26，P023 不提升。正文与 reviewed_at 冻结后仅提交本报告，不改数学、原稿、台账、根导入、公理工具或其他报告，不 push。
