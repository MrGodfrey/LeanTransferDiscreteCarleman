# T231 / C247 独立本机验收

- checked_sha: `e61081ad723542df4c8e33ab57a10f10f6db67d0`
- mathematical_base: `721b761224ad1b6425466bc956417ddce7f41908`
- reviewed_at: `2026-10-20T06:49:03+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，6/6 定理，未发现阻断缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；实际指数和内域的解析局部边界坐标、精确半空间对应及图导数互逆。原文覆盖保持 18/26，P023 不提升。**

已全文读取固定 `Carleman/Geometry/AnalyticLevelCharts.lean`、六项 raw 完整类型和公理记录、analysis/MATH_SPEC/声明清单、原稿 `paper/main.tex:2659–2665` 以及实际调用的关键依赖。只使用固定 Git 对象和对应本地证据，没有纳入未来工作树或动态审计输出；按简化协议未重复构建旧闭包，也未查询远端 CI 或看板。

## 原文对应与实际量词

原 Corollary A.2 断言固定有界凸多面体或盒上 Dirichlet Laplacian 满足完整 A1–A3，证明引用凸域 H² 正则性。本批是其正则性证明路线的几何准备：对一般实 Banach 空间中的解析实值函数 g，在任意真实非临界点 c 构造局部图；再对 T230 实际 `gₙ=Σᵢexp((n+1)(bᵢ−ℓᵢx))`、`Uₙ={gₙ<1/2}` 内部供应该资格。没有假设原多面体边界光滑，也未将原多面体直接识别为解析边界域。

一般 helper 的前提是实际 `ContDiff ℝ ω g` 和 `fderiv ℝ g c≠0`。最终内域定理只要求有限指标、原连续线性泛函与偏移、n、一个实际内点 `c∈Uₙ`，以及任意 `x∈frontier Uₙ`；gₙ 解析性与边界非零导数均由证明提供。存在的图随这些几何数据和边界点选择，覆盖该 n 的所有边界点；本批没有宣称统一图半径、统一导数界、有限图册或 Sobolev 变换估计。T230 的同一非空尾段可直接提供每个内域所需的内点，不需再增加边界正规性输入。

## 实际数学核对

1. **非零泛函、真实连续补投影和 IFT。** 取 `L=fderiv ℝ g c`。由非零实线性泛函的代数满射性得到 `L.range=⊤`；有限维的是值域 ℝ 的子空间，不是 E。实际 `ker_closedComplemented_of_finiteDimensional_range` 给 `P:E→L[ℝ]ker L` 且 P 在 ker L 上为恒等。由该真实投影分别推出 P 满射以及 `ker L` 与 `ker P` 互补，没有把补空间或可逆导数列作额外输入。`ImplicitFunctionData` 的左右函数明确为 g 和 `P(x−c)`，左右严格导数是 L、P；全局解析性给前者的实际严格 Fréchet 导数，后者由线性映射和减常数链式法则得到。全部字段在内部构造，公开 `toOpenPartialHomeomorph` 生成 e₀，其实际函数在所有 x 上等于 `(g x,P(x−c))`，源含 c 且 `e₀ c=(g c,0)`。核为闭子空间，所需 Banach 完备资格合法；没有有限维 E 假设。
2. **正向解析与整个目标内逆解析。** 正向就是原解析 g 与真实仿射投影的乘积。由满射与互补核得到实际连续线性等价作为 e₀ 在 c 的导数，调用逆函数解析定理给逆在 `e₀ c` 解析。这里阶数确为 `ω : ℕ∞ω`，raw 打印的 `⊤` 是解析顶元，区别于 C∞ 所用的内层 `∞`。已读 mathlib `contDiffAt_symm` 的 ω 分支以及 `ContDiffAt.eventually` 的 `n≠∞` 条件：ω 确满足，故存在单一开邻域 W，逆在 W 的每点均解析。随后取 `e=(e₀.symm.restrOpen W).symm`，其目标是 `e₀.target∩W`，源是 `e₀.source∩e₀⁻¹W`；c 仍在源中。真实 `restrOpen` 不改变正逆函数本身，所以全空间第一坐标身份、基点像和全局正向解析性均保留，逆在整个新目标解析。没有将 C∞ 逐阶邻域非法合并，也没有只证明逆在基点解析就宣称整个目标解析。
3. **真实导数双向逆。** 通用 `analytic_chart_derivative_inverse` 对任意源点 x，从图源/目标开放及两方向解析性获得实际 `DifferentiableAt`。两方向局部互逆式是邻域上的 EventuallyEq；Fréchet 链式法则及局部函数相等给 `D(e⁻¹)(e x)∘De(x)=id_E` 和 `De(x)∘D(e⁻¹)(e x)=id_F`。由这两个等式构造 `IsInvertible` 并识别 CLM 的实际 inverse，未输入 Jacobian 可逆性，也未用仅单侧逆替代双侧逆。该定理不需要完备性。最终存在图已给正向全局解析和逆在目标解析，因而直接满足此定理全部前提；导数资格没有被留给调用者额外证明。
4. **原严格子水平集的精确像。** `level_chart_image_sublevel` 对任意实 a 证明 `e '' (source∩{g<a})=target∩{y₁<a}`。正向使用 map_source 和全局第一坐标身份；反向从任意目标点取同一个 `e.symm y`，用 map_target、right_inv 恢复原子水平集资格。存在图同时返回 `g(e.symm y)=y₁` 于全部目标点；未漏目标资格或把开半空间写成闭半空间。
5. **全部原局部边界而非截断集的假边界。** 将 `{g<a}` 与 `Iio a×univ` 建成实际 `OpenPartialHomeomorph.IsImage`，再用其 frontier 定理。该工具用开图的邻域映射传递闭包与内部，得到的是源中原全空间集合的 frontier，不是 `frontier(source∩{g<a})`；因此没有额外引入图源边缘。`frontier(Iio a×univ)={a}×univ` 给每个源点 `x∈frontier{g<a} ↔ g x=a`，两方向完整。
6. **同一指数和内域内部实例化。** `halfspaceExpSum_analytic` 直接由原全部仿射函数、真实 exp 与有限求和证明解析阶 ω；不是从旧 C∞ 声明推断解析。最终定理调用 T230 实际边界正则性得到原 `gₙ(x)=1/2` 及 `Dgₙ(x)≠0`，构造上述同一个 e，并返回 `e x=(1/2,0)`、所有源内原 frontier 与水平面对应以及原 Uₙ 的精确半空间像。没有冗余半空间独立性、法向归一化或特殊非零 ℓᵢ 条件。空边界情形仅使按边界点量化的结论真空成立；已有内点前提被如实保留。实际零空间中不存在非零泛函，通用 helper 的前提相应不可满足，没有非法零维补空间论证。

## 全部声明逐项结论

源码行均在固定 `Carleman/Geometry/AnalyticLevelCharts.lean`；raw 行在本批固定审计文件。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 13 / 41795 | `Carleman.exists_analytic_level_chart` | PASS；真实 IFT 构造，源含指定点，完整正逆解析与第一坐标身份。 |
| 76 / 41806 | `Carleman.analytic_chart_derivative_inverse` | PASS；每个源点真实 Fréchet 导数双向可逆并识别逆图导数。 |
| 99 / 41812 | `Carleman.level_chart_image_sublevel` | PASS；严格子水平集与目标半空间精确相等。 |
| 113 / 41816 | `Carleman.level_chart_frontier_iff` | PASS；源内全部原 frontier 与实际水平面双向对应。 |
| 125 / 41820 | `Carleman.halfspaceExpSum_analytic` | PASS；同一实际指数和的解析性，阶数为 ω。 |
| 130 / 41824 | `Carleman.halfspaceSmoothInner_analytic_chart` | PASS；由原几何内部供应全部图资格，无预设图册或边界光滑性。 |

## 依赖与固定本地证据

T230 冻结报告 `6d3f546a94a5ca47a7a1f5aacf5f9d7b15821637` 已全文读取（checked_sha 为本批 base，reviewed_at=`2026-10-20T06:39:08+00:00`，17/17 PASS）。同时直接核对实际指数和/内域定义、真实 Fréchet 导数、凸函数支撑不等式及由内点推出全部边界非临界的证明；没有仅依赖报告结论。新模块 Carleman 导入闭包 **31 文件**，其中 **30 个旧文件**与 base 的 Git blob 逐字节不变。实际 mathlib checkout 无修改、HEAD 与固定 lock 为 `56a005855ea17e0b0958f73ec801ae140b0a1679`；已读实际 IFT 数据结构/公开 API、连续补投影、解析逆函数定理、阶数语义、开图限制和 frontier 传递。透明性选项只影响定义展开，不添加数学公理。

- `/tmp/carleman-t231-local-evidence.json`：source=local、PASS，checked/source 都是本报告 proof，finished_at=`2026-10-20T06:46:42.327048+00:00`。`lake build Carleman` 与 `lake env lean tools/CheckAxioms.lean` 实际执行记录均 exit 0；验收读取正式成功产物，没有用早期失败探针充作成功证据。
- `/tmp/carleman-t231-local-source-manifest.txt`：**1028 项、111526 bytes**，SHA256 `687b682ec2c37ea80d3d80e9177c53c087e0c3372a8c3eeb1c6c9e1d30ee683c`。独立枚举 fixed proof 的全部 tracked `.lean` 与三项工具链配置，核对路径集合完整、无重复，并对全部 Git blob 逐字节摘要验证通过。
- `/tmp/carleman-t231-target-build.log`：**3060 jobs** 成功，109 bytes，SHA256 `629864b7b8821566e8cef294cd5d05ba55ae8ff0005acf229a2638474b122e05`。`/tmp/carleman-t231-build.log`：**4270 jobs** 成功，80 bytes，SHA256 `177c072b53f910626d854f4ff30fb9ab0a76ab548ea127cfaeae2f8845ccf07f`。`/tmp/carleman-t231-axioms.log` 为 0 bytes。
- `/tmp/carleman-t231-level-chart-local-axioms.txt`：**3212447 bytes**，SHA256 `6ee28ebb2b8486c95d65fc6defe879dc4ca65cb7fc9ee1293ffd2d3f10c15546`，与固定证据相同。六项完整类型和各自公理逐项核对；全部显式输出的 **3761 个公理列表及 10 个无公理记录**只含正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或无公理。原 `privateToUserName`/`collectAxioms` 递归白名单循环不变，末行确认 **9560 声明递归审计 PASS**；没有 sorryAx 或额外数学公理。
- 固定根导入、六项 `#check`/`#print axioms` 齐全。Lean 4.35.0，编译器 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`。原稿相对 base 未变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

无修复项。接受本批 **AUXILIARY 解析局部平坦化**；弱 Sobolev 坐标变换、内域边界 H² 正则性、凸域统一二阶估计及完整 P023 仍需各自证明。本报告正文及 reviewed_at 冻结后仅单文件提交，不改数学、台账、原稿或其它报告，不 push。
