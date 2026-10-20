# T243 / C259 独立本机验收

- checked_sha: `e7240abc0fb7acb6a0e456cd916f1845a114b72a`
- mathematical_base: `4acd24f5158fda6688403c600ddbd9d2a131c379`
- reviewed_at: `2026-10-20T08:41:49+00:00`
- reviewer: 独立本机 Agent `accept_spatial_lemma`
- result: **PASS，12/12 显式声明（11 定理、1 定义），未发现缺陷。**
- axiom_check: **PASS**
- accepted_scope: **AUXILIARY；从原正则水平函数构造保持切向坐标的实际解析逆图，以及局部解析、全局法向平移不变的高度函数。保持 18/26，P023 不提升。**

已完整读取固定 `Carleman/Geometry/CoordinateLevelGraph.lean`、12 项 raw 完整类型及公理记录、analysis/MATH_SPEC/台账，并核对原稿 `paper/main.tex:2659–2665`。原 Corollary A.2 要求 Dirichlet 算子域及椭圆估计；本批提供边界正则性路线中的真实局部水平图，不是该原命题本身。

## 实际数学及量词

1. **坐标映射及真实导数。** 定义的 F(x)=x+(g(x)−x_r)e_r 精确保留全部 i≠r 坐标，将第 r 坐标改为 g(x)。前两项恒等式不需要任何正则性。一般 `ContDiff` 阶数的复合及实际 `HasFDerivAt` 给 DF=I+e_r⊗(Dg−e_r*)；这里不是把预定矩阵命名为导数。有限维真实正交基中矩阵为 I+evᵀ，行列式引理给 1+vᵀe=Dg(e_r)。减去的坐标泛函正确消去单位矩阵中的 1，没有误用先前 shear 的 det=1。
2. **非退化坐标由原梯度选择。** 若所有 Dg(e_r) 都为零，基的张成性给整个连续线性泛函为零，故 Dg(c)≠0 内部供应一个实际 r。固定坐标版本只要求该分量非零，不要求正号。d=0 时非零泛函前提不可能成立，证明没有凭空选取 `Fin 0` 元素；d=1 也无需另外假设切向维数为正。
3. **逆图确由实际 IFT 构造。** g 的输入是 `ContDiff ℝ ω g`，即解析性。由真实 DF(c) 的非零行列式，`toContinuousLinearEquivOfDetNeZero` 构造的连续线性等价与原 DF(c) 精确相同；公共 API `ContDiffAt.toOpenPartialHomeomorph` 返回 e₀，正向函数全局等于 F，且 c 真正属于 source。逆函数定理在 e₀(c) 给解析逆，随后使用 `ContDiffAt.eventually` 得一个实际开邻域，在其每一点逆函数解析，再把逆图限制到该开集。最终 e 的整个 target 都有声明中的解析逆，而不是仅在中心点有逆导数。已读取底层 API 的真实类型与实现；raw 中此处打印的外层 `⊤ : WithTop ℕ∞` 是 ω，不能误读成内层无穷阶 C∞；`eventually` 所要求 n≠∞ 正由 ω 满足。
4. **限制没有改变原映射或丢失中心点。** 对 `(e₀.symm.restrOpen O).symm`，target 为 e₀.target∩O，source 为相应原像交集，正逆函数本身不变。c 的成员资格同时含原 source 条件及 e₀(c)∈O。对所有 target 中 y，实际右逆身份 F(e⁻¹y)=y 逐坐标推出 g(e⁻¹y)=y_r 和 (e⁻¹y)_i=y_i。没有把这些坐标身份或逆图存在性列为额外假设。
5. **高度函数的全局不变性与局部正则性分开成立。** 令 a=g(c)，Q(x)=x+(a−x_r)e_r；Q 精确重置法向坐标，故对所有 x、t 有 Q(x+te_r)=Q(x)。ψ(x)=(e⁻¹(Qx))_r 是一个全空间定义的函数，因此上述恒等式无条件给 ψ 的全局法向平移不变性，哪怕 Qx 位于逆图 target 之外。正则性只在 V=Q⁻¹(target e) 上证明：V 实际开放、含 c，Q 在全空间解析，逆图在 target 解析，故 ψ 在 V 解析。ψ(c)=c_r 由实际左逆得出。证明没有在 target 之外使用逆图的连续性、解析性或逆身份。
6. **水平图对应的区域和两个方向准确。** 对 x∈V，真实切向坐标及 ψ 定义给 x+(ψ(x)−x_r)e_r=e⁻¹(Qx)，其 g 值恰为 a。取 W=e.source，对 x∈V∩W，g(x)=a 使 e(x)=Qx，左逆给 x_r=ψ(x)；反向由 x_r=ψ(x) 使该图投影等于 x，再用上一身份。这里使用的是把法向坐标替换为 ψ(x) 的图投影，不能替换为先前 x+ψ(x)e_r 的可逆 shear。source 条件用于合法左逆，V 条件用于合法 target，两者均未遗漏。
7. **原指数和内域供应所有图资格。** 最终结论输入任意有限半空间族、n、一个真实内点 z，以及该内域的实际 frontier 点 c。实际依赖中，连续性和开放性给 g(c)=1/2；指数函数的支撑不等式 g(z)≥g(c)+Dg(c)(z−c) 与 g(z)<1/2 排除 Dg(c)=0。有限指数和内部提供全空间解析性，故最终结论只从原数据选取 r、ψ、V、W，并把水平值精确替换为 1/2；没有另输入正规边界、可逆 Jacobian 或已存在图。空域不能满足内点输入；没有在空指标或零维情形伪造边界点。

全部一般结论的图和邻域可依赖 g、c、所选 r；最终可依赖原半空间数据、n、内点及边界点。本批没有提出统一导数常数或统一图半径，也没有从存在局部解析图推断它们。一般 helper 的全局解析 g 前提比任意光滑函数更强，但实际指数和应用内部清偿了它，不作为原域额外未解决前提。

**范围边界：** 已证明的是水平集等价 g(x)=a ↔ x_r=ψ(x)。本批尚未判定 g(x)<a 对应图的哪一侧；没有构造与 ψ 局部一致的全局 C∞、有界斜率及二阶界延拓，也没有因此直接调用全局图域 H² 定理。有限截断覆盖、局部拼接和凸域统一椭圆估计仍待。最终声明没有 H²、PDE 或目标图资格假设，也没有声称这些后续结论。

## 全部声明

名称统一带前缀 `Carleman.`；源码行为固定 `CoordinateLevelGraph.lean`，raw 行为固定完整类型的位置。

| 源码 / raw 行 | 声明 | 结论 |
|---|---|---|
| 14 / 43208 | `coordinateLevelMap` | PASS；实际法向坐标替换映射。 |
| 17 / 43211 | `coordinateLevelMap_normal` | PASS；法向坐标精确为 g。 |
| 22 / 43214 | `coordinateLevelMap_tangent` | PASS；全部其他坐标保持。 |
| 26 / 43217 | `coordinateLevelMap_contDiff` | PASS；任意所给阶数的真实光滑性。 |
| 30 / 43220 | `coordinateLevelMap_hasFDerivAt` | PASS；实际 Fréchet 导数及坐标减项。 |
| 37 / 43228 | `coordinateLevelMap_det` | PASS；真实矩阵行列式等于 D_rg。 |
| 56 / 43233 | `exists_nonzero_coordinate_derivative` | PASS；从原非零泛函内部选坐标。 |
| 66 / 43237 | `exists_coordinate_level_chart` | PASS；真实 IFT、全 target 解析逆、准确原坐标身份。 |
| 106 / 43248 | `coordinateLevelMap_constant_normal_invariant` | PASS；任意全空间法向平移的重置恒等式。 |
| 117 / 43253 | `exists_local_coordinate_level_height` | PASS；实际开邻域、局部解析高度、全局不变性及双向水平身份。 |
| 166 / 43268 | `exists_local_coordinate_level_height_of_regular` | PASS；非零原梯度内部供应上述固定坐标条件。 |
| 178 / 43283 | `halfspaceSmoothInner_coordinate_level_height` | PASS；原指数和、实际内点/frontier 输入内部供应全部图条件。 |

## 依赖与固定本地证据

实际 Carleman 导入闭包 **213 文件**，其中 **212 旧文件**相对 mathematical_base 的 Git blob 不变；唯一新增数学模块为本批模块。另独立比较 T231 已验收 `e61081ad723542df4c8e33ab57a10f10f6db67d0` 的 31 文件闭包、T237 已验收 `77a0dc79f9a1d256ecae73c15a7e8eebe10ce6c1` 的 206 文件闭包，均与本 proof 逐字节不变。本次重读 `AnalyticLevelCharts`、`HalfspaceSmoothExhaustion` 的实际正则性供应，以及 `NonlinearGraphShear` 的真实定义/导数/行列式，明确新映射与旧 shear 的差别。实际 mathlib IFT、逆解析性、开集限制及行列式转连续线性等价 API 均已直接核对。

T231/T237 冻结报告及单文件提交分别为 `dae4b8b906f87b6192e194d1f827422f3021c92e`、`6e96dffd9f2d128ff3d66d6b6d0e163e8cd0b4d6`；固定 proof 中报告内容未变。已完整读取并核对 T242 报告提交 `faecb1d3d0dd83a2ec6ab2b7662181cf9d46ac07`（reviewed_at=`2026-10-20T08:30:14+00:00`，16/16 PASS）。T242 是接续阶段和后续局部化接口，不把其目标域正则性当作本批图构造的前提。

Lean **4.35.0**，编译器提交 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib lock 与实际无修改 checkout 同为 `56a005855ea17e0b0958f73ec801ae140b0a1679`。根导入及 12 项 `#check`/`#print axioms` 齐全。AGENTS、PROJECT_OPERATIONS、state/README 与此前已读协议摘要一致。

- `/tmp/carleman-t243-local-evidence.json`：source=local、PASS，checked/source 均为本报告 proof，finished_at=`2026-10-20T08:34:01.815622+00:00`；实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 执行记录均 exit 0。
- `/tmp/carleman-t243-local-source-manifest.txt`：**1040 项、112874 bytes**，SHA256 `f6446fbde89e163b62341e674c7a608b59dfd604bb185571b475c131fe9f200d`。独立枚举固定提交全部 tracked `.lean` 及三个工具链配置，路径集合、唯一性及逐项 SHA256 全部匹配固定 Git blob。
- `/tmp/carleman-t243-target-build.log`：**3398 jobs** 成功，110 bytes，SHA256 `b3ecb804ac5a71515807a42a30d45bad02792085c6be50ed89231c967195fd77`。`/tmp/carleman-t243-build.log`：**4282 jobs** 成功，80 bytes，SHA256 `6ec5631ce4a378c93fe458cba286386cee7fee41bab9c1f46753508bf1976da1`。`/tmp/carleman-t243-axioms.log` 为 0 bytes。
- `/tmp/carleman-t243-coordinate-level-graph-local-axioms.txt`：**3328010 bytes**，SHA256 `0d72330679cad359c266c17f4620255bad9680e2f47d4c1c772fdeaa7ad801be`。12 项完整类型及公理全部核对；全文件 3936 个公理列表均仅含 `propext`、`Classical.choice`、`Quot.sound`，另有 10 个无公理记录。实际尾部确认 **9950 声明递归审计 PASS**；全命名空间 `privateToUserName`/`collectAxioms` 白名单逻辑相对 base 不变，无 sorryAx 或额外数学公理。
- 原稿相对 base 不变，SHA256 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。本次核对固定本地执行证据，没有重跑全库，没有查询远端 CI/看板，没有把本地成功称为 CI 成功。

无修复项。接受本批 **AUXILIARY 局部坐标水平图构造**，保持 18/26。正文与 reviewed_at 冻结后仅单文件提交本报告，不修改实现、台账、原稿、根导入、公理工具或其他报告，不 push。
