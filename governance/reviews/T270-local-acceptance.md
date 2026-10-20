# T270 / C286 / P021 与最终 26 项原文结果独立验收

- checked_sha: `99d519544e0eb8d42a955ca6bff3935c322d855f`
- mathematical_base: `b04fcf4526dac2c76c92f4d3155fc4e5763e947b`
- reviewed_at: `2026-10-20T12:41:09+00:00`
- reviewer: 本机独立 Agent `/root/accept_spatial_foundations`
- result / axiom_check: **PASS / PASS；本批 5/5，完整 PAPER Corollary 7.9 / P021。**
- final_scope_result: **原稿 26 个具名结果全部覆盖，既有接受版本在本固定证明树中保持有效；支持最终 26/26。**
- evidence_source: **local**。本报告核验真实本地构建、固定源清单和递归公理产物，不查询或声称远端 CI，不重复整库构建。

未发现阻断数学缺陷。本批两个新模块和两个透明结论定义已完整展开核对，未把返回 Prop 的名字当作证明。已有完整 Cartesian 入口、实际一般 P1 弱极限入口、区域控制、StrongDual 方程及能量解唯一性均直接读取相关源码。最终 26 项复核采用既有独立语义验收加严格源码/配置版本边界；不是在本批重新宣称执行了所有历史审核或所有历史构建。

仅新增本报告，不更改数学、原稿、台账、根入口或审计实现。正文和 reviewed_at 冻结后仅单文件提交，不 push。

## 原 Corollary 7.9 的范围

直接核对固定 `paper/main.tex:2290–2421`，包括原 FE/FD 数据、E/K 重构、Corollary 7.9（`:2344` 起）、六项弱身份、真实 V′ 方程和连续 H 端点。原稿 SHA256 为 `492d3a5ece01681b2440b1481e75937a1daa7214d0e582901566b1a144555cef`。

原结论要求：固定原有界势 b 和初态 y0，沿任意独立的 h→0、dt→0，充分大指标上选择真实物理控制及状态；控制满足统一费用和指数终态界，其重构在原区域内支撑、在固定 L²(0,T;H) 中相对弱紧；每个弱积聚点是一个区域控制的真实零延拓，所对应的原能量解具有初迹 y0 和终迹 0。不是只要求选出某个特殊弱极限，亦不是只证明有限测试恒等式。

新 P1 入口的原域是任意有界有限严格仿射半空间交，维数写成 `d+1≤3`，覆盖原二维、三维凸多面体并额外允许一维。非空由实际非空开控制区包含于域内供给。网格是完整原一致 P1 空间，保留原 FaceMatching、BoundaryFitted、形状正则、尺度两侧可比和 `1≤γ<Γ_d` 的分级条件。常数依赖固定域、区域和网格族的这些固定参数，不依赖具体网格或初态。

既有 `box_cartesian_controls_null_limits` 对任意正维坐标盒、原可比轴向网格、原完整内部节点状态成立。其真实内控制区 `ωsharp` 与 `closure ωsharp⊆ω` 供给充分细网格的单元支撑，正是原稿差分控制的设置。它保留原双单元平均初值和时空平均势、真实 E_h 与 E_h B_h；没有把 P1 的维数限制施加到 FD 分支。

## 本批全部五项声明

下表名称均在 `Carleman.Physical` 命名空间，源码位于固定 `Carleman/Control/`。raw 行号指固定 `/tmp/carleman-t270-control-convergence-local-axioms.txt`。

| 声明 | 固定源码 / raw 起始行 | 独立结论 |
|---|---|---|
| `FiniteHalfspaceP1Refinement` | `FiniteHalfspaceP1Refinement.lean` / 46368 | 透明定义。展开后完整包含原网格/数据量词、共同尾段、真实 u/y、ForwardEquation、费用和指数终态、区域重构范数及支撑、强初终值极限。不是输入性质或新公理。PASS。 |
| `finite_halfspace_p1_controls_independent_refinement` | 同文件 / 46373 | 从已清偿的一般域物理控制内部选取同一个尾段和实际控制；原物理尺度条件由独立细化最终满足，初态投影和终态强收敛均内部证明。PASS。 |
| `FiniteHalfspaceP1NullLimits` | `FiniteHalfspaceP1NullControlLimits.lean` / 46383 | 透明定义。逐项保留前述全部结论，并加入任意取样序列的弱子列存在、任意严格子列的每个给定弱极限 U 的区域表示、费用及同一 Y 的原弱身份和真实零终态解。PASS。 |
| `finite_halfspace_p1_controls_null_limits` | 同文件 / 46388 | 用真实区域闭子空间弱紧性与同一原 P1 方程的状态紧性构造所有见证。U 在抽取状态子列之前固定；Y 在量化全部有限测试之前固定。实际 V′ 方程和 H 连续端点由已证身份内部导出。PASS。 |
| `box_cartesian_controls_null_limits` | `CartesianNullControlLimits.lean:18` / 38456，既有 | 完整原 FD 分支，所有原数据、物理轨迹、区域支撑、独立细化和每个弱积聚点保留；同一有限身份导出真实连续零终态解。重新核对最终完整类型及实际调用，整条旧数学闭包不变。PASS。 |

两个透明定义只拆分巨大依赖类型的书写；对应定理以原几何及网格族参数为输入，证明整个定义。定义中的有限测度实例由原有界域实际供应，既不作为额外前提，也未改变 L² 所用测度。两定义完整源码均已读取，不能以 raw 的 `: Prop` 简写替代本项展开审核。

## 独立细化、实际离散选择及原数据

`finite_halfspace_p1_controls_independent_refinement` 调用固定 T268 的 `finite_halfspace_p1_physical_observation_control`。已重读其实际类型和证明，核对原 Galerkin 刚度、投影乘法势和区域控制，没有留下连续 CE、H² 正则性、目标数值估计或抽象物理控制前提。

先固定原几何、形状/分级参数，得到 κ>0、d0>0；对每个 T>0、M≥0 再选 C>0，然后才量化全部网格序列、时间网格、满足原界的具体势和 y0。所有 n 共用该 C。`sqrt C` 是原 generic 控制常数 C(T,M) 的一个具体正见证，不改变原量词或统一性。

真实尺度为

`S_n = κ min(h_n^(-4/5), dt_n^(-2/5))`。

直接检查 `PhysicalRefinement`：h_n、dt_n 分别正且趋于零即给 S_n→∞；同时 `dt_n S_n ≤ κ dt_n^(3/5)→0`。因此 h≤h0、dt≤Δ0、`16 qb≤S≤qb T/(4dt)`、dt M≤1/2、dt≤T/12 在同一个尾段全部成立。没有输入 h/dt 比值、嵌套网格或时空耦合条件。网格最大直径正性由非空原域和实际分割取得。

P1 数据确为同一固定原 b 的时间单元平均

`fixedTimeCellPotential.value x = dt⁻¹ ∫_(t_i,t_(i+1)] b(t,x) dt`，

其 bound 精确保留原 b.bound≤M。实际势算子为该乘子的原正交投影，未要求一般 b 保持 P1 空间。初值是整个原 L² y0 的 `X.orthogonalProjectionOnto`，不是光滑数据或预选节点子空间。

`choose u y` 对共同尾段各实际离散系统产生控制和 N+1 节点轨迹；结论包含真实

`dt⁻¹(y(i+1)−y(i))+(A_h+V_i)y(i+1)=B_h u_i`，

以及 y(0)=Π_h y0、`controlNorm≤sqrt(C)‖Π_h y0‖`、`‖y(N)‖≤sqrt(C) exp(−d0 S)‖Π_h y0‖`。投影收缩给同一原 y0 的费用界；原 `full_p1_initial_projection_strong_convergence` 给强初值收敛，指数衰减及投影界给终态范数趋零，包含映射下的实际 H 终态也强趋零。既非输入终态结论，亦非只构造一个替代终端向量。

`regional_time_control_norm` 由真实时间单元重构及区域限制算子的实际伴随给精确范数等式

`‖K_h,dt u‖_(L²_t H)=sqrt(dt Σ‖u_i‖²)`。

这里 K 是区域零延拓，未误用投影后的 B。`regional_time_control_supported` 逐单元和 a.e. 代表证明其在 ω 外为零。由于 ω⊆S，可测区域 L² 正是原 L²(ω)；有限区间上的 Bochner 表示经实际产品等距给原时空 L² 控制及同一费用，不需要假设未证明的满射。

## 每个弱积聚点、同一状态与六项身份

最终定理首先保留上述同一 u、y、J 和所有离散结论。对任意取样映射 σ（此存在性分支甚至不要求 σ 严格递增），对有界、实际支撑的 K∘σ 调用真实 Hilbert 弱子列构造，得到 StrictMono χ 和同一真实区域 v 的零延拓弱极限。所用空间是实际可分 Hilbert L²，不是有限维控制空间；原 L² 区域可以无限维。这个对任意取样序列的结论，加实际有界性，给原 Hilbert 弱拓扑下相对弱紧性的标准等价序列表达。

识别分支另行量化 **每个 StrictMono σ 和每个给定的环境弱极限 U**。`regional_control_of_weak_limit` 通过真实区域补集限制的 Bochner 核在弱极限下闭合，构造 v 满足

`(restrictRegionCLM ω).adjoint.compLp v = U`，`‖v‖=‖U‖≤sqrt(C)‖y0‖`。

该步骤不替换 U，也没有只证明新选出的某个弱极限有效。

对索引 `σ n+J`，严格单调性给趋于无穷，故原两项独立细化和物理尾段条件仍成立。随后 `full_p1_weak_control_limit_null_state` 直接使用这个 U、同一个 b、原投影初值、实际 ForwardEquation、已证费用和终态趋零。原方程的能量估计内部给状态预算，`conforming_controlled_states_weak_subsequence` 在完整 `L²_t H¹₀` 中抽取一个 Y，且同一子列上的值和梯度分别是 Y 的实际映射。没有独立选择值/梯度极限，没有逐个测试重复抽状态。

已直接读取 `P1WeakLimitIdentity` 和实际 `TimeAveragedProductPotential`。对原全部有限张量测试，六项极限保留：

- 时间项为 `−(Y,∂tΦ)`，真实前后层差商与离散分部求和一致；
- 刚度项为同一 Y 的真实梯度配对；
- 势项用同一个 b 的真实时间平均、产品 L² 代表及弱强配对得到 `(bY,Φ)`，无 b 光滑性或势收敛外加假设；
- 初值项由真实正交投影强收敛给 `(y0,Φ(0))`；
- 控制项用真实区域零延拓和原弱极限 U 得 `(U,Φ)`；
- 原终端项在离散身份中符号为负，实际终态强零和端点测试收敛使它消失。

因此同一 Y 对全部有限原测试满足

`−(Yv,Φd)+(Yg,Φg)+(bYv,Φ)=(y0,Φ0)+(U,Φ)`。

原有限测试身份同时保留在最终结论中，没有被仅有端点或仅有抽象 PDE 的对象替换。

## 真正的 V′ 方程、连续端点和唯一能量解

已展开 `DirichletNullControlState` 并读取 `DirichletTimeLoad`、`DirichletDualTimeDerivative`、`DirichletTimeEndpoints`、`DirichletDualMassEquivalence`、`DirichletEnergySolution` 和 `DirichletEnergyUniqueness` 的相关实际证明。

令 E 为原 H¹₀→H 值嵌入，G 为实际弱梯度，J 为实际 Bochner→产品 L² 等距。质量为真实 E*E，载荷为

`D = E*U − G*GY − E*J*(b.map(J(EY)))`。

所有伴随均为实际 Hilbert 伴随；不要求 J 满射或 E 有有界逆。对任意 w∈H¹₀ 和任意标量 L² 时间测试，其真实配对是控制减梯度形式减同一 b 的势配对。经实际 `innerSL` 映入 StrongDual 后，pivot 作用为原 H 内积，真实 `dirichletDualTimeLoad` 属于 `L²_t V′`。最终分布身份是

`∫ φ′ pivot(Y) = −∫ φ (U−AY−bY)`，

对所有 `(0,T)` 内紧支光滑时间测试成立，正是原 `∂t y+Ay+by=U`。原 Y 的 pivot 也具有真实 L² 资格，因而是原 V′ 值 H¹ 弱时间状态，而不是只有未解释的符号身份。

连续 H 代表由原弱质量导数的既有实际正则化与迹定理构造；不假设 Y 已有 H 连续代表。完整有限测试身份以不限端点的时间函数取值，经真实标量 Green 公式和 H¹₀ 在 H 中稠密性识别 `q(0)=y0`、`q(T)=0`。没有读取任意 Lp 代表的端点，亦未以连续的 E*E Y 代替所需的 H 连续性。

`DirichletEnergySolution` 的定义只有一般原强对偶方程和初迹，**没有零终态条件**。`DirichletEnergySolution.unique` 先用真实 StrongDual/质量弱方程等价，再以同一 b/U 的差方程、零初态、实际连续能量恒等式和 Volterra 论证给完整 Y=Z。比较解不需要已知零终态或 V 值强 H¹ 时间正则性。`FiniteDirichletControlIdentity.unique_energy_solution` 因而将本批的 Y 识别为原能量解，并把已证明的零终迹传给任意同数据能量解。这清偿原文“the energy solution”的含义，不是只声明某个特殊零终态状态存在。

旧完整 Cartesian 结论采用同一身份→原能量解链；原数据的实际单元平均、未覆盖边界条带零值、K=E_h B_h 的范数/支撑及原弱极限识别链均保持。其最终入口已重新读取，整个 856 模块闭包与已验收 T206 版本一致。

## 本批固定依赖和验收边界

本批两新模块、旧 Cartesian 入口及能量解入口的递归本地数学闭包共 **986** 模块，其中 **984** 个既有模块与 mathematical_base 逐 Git blob 完全相同。额外核对：

| 实际依赖入口 | 已接受数学版本 | 整个闭包逐字节不变 |
|---|---|---:|
| `FiniteHalfspaceP1PhysicalControl` | `5458c11848a69d56199fb5e13d517b58eb38953b` | 746 模块 |
| `P1WeakControlLimit` | `3725f002ad895342683989c46d052625da5f57ba` | 611 模块 |
| `CartesianNullControlLimits` | `7b47cb8efa47015a5e2e62f6e2573204bd5c7418` | 856 模块 |
| `DirichletEnergySolution` | `2bbedbc1881148eb48d0280570a98d0234ef0813` | 443 模块 |

全文读取 T268 冻结报告 `038447d47db3314106c903723fc9415646d96bad`（reviewed_at `2026-10-20T12:26:45+00:00`，4/4 PAPER PASS/P014、P015），16434 bytes，SHA256 `7da213fd2c74f21f5af3e4e8dd4c44c8f63ac7a3ee1e678e9428249c228a004e`。它已在本 proof 树中。并直接复核上述实际物理入口，不只引用报告。

全文读取 T269 冻结报告 `7097e500642997a9718add2322f558f65e45fcbf`（reviewed_at `2026-10-20T12:31:45+00:00`，3/3 PAPER PASS/P017、P018），15535 bytes，SHA256 `d85dc88509bbdb67da2ddda1625cd0431e2a5f13afbb01d1dbd16c19efcf0e34`。**该报告不在 checked_sha 的树中**，本次作为分离固定验收证据核对；其数学版本就是本批基线且未变。固定 coverage 中这两项仍为 BUILT，不将旧状态字段伪写为当时已 REVIEWED。

另外全文读取 T215 冻结报告 `acc193c0a9a79624439b8af36a929bfa3a47367b`，并重新检查实际 StrongDual 等价和一般能量解唯一性。旧辅助报告本身不单独提升 P021；本次新原域选择族、实际全部量词和完整依赖组合构成 PAPER 验收依据。

## 固定本地构建、源码与公理

`/tmp/carleman-t270-local-evidence.json` 的 source=local、status=PASS，checked_sha/source_head_sha 均为本报告 proof。实际 `lake build Carleman` 和 `lake env lean tools/CheckAxioms.lean` 均 exit 0，finished_at 为 `2026-10-20T12:27:10.790056+00:00`。

| 产物 | 独立核验 |
|---|---|
| `/tmp/carleman-t270-local-source-manifest.txt` | 1085 项，117813 bytes；SHA256 `8eefad9a39e0979ca9fccae128ab8b49c23edde850b891dff1e4113cf56e139b`。集合精确等于固定 tracked `.lean` 和三项配置；逐项内容哈希匹配 Git blob，无遗漏或重复。 |
| `/tmp/carleman-t270-target-build.log` | 实际目标 4170 jobs 成功；123 bytes，SHA256 `f2f9ac0a5ffed0f8243307c91f079836fea76c48b40d9163614a9c66e36129ed`。 |
| `/tmp/carleman-t270-root-build.log` | 实际根构建 4327 jobs 成功；80 bytes，SHA256 `3249a83703428bf7d472328036878a5ca1e9020f7bb46c80f205bb905d902c39`。 |
| `/tmp/carleman-t270-control-convergence-local-axioms.txt` | 3577982 bytes；SHA256 `afc286b5b5428afa187e1b30e3b5dff3956af66304d01265ffc1d826bd419bd0`；末行明确全部 **10681** Carleman 声明递归审计 PASS。 |
| 实际公理记录 | 独立检查 4264 条显式公理/无公理记录，仅有正常基础公理 `propext`、`Classical.choice`、`Quot.sound` 或空依赖。五项均有完整类型及各自公理记录。 |
| 配置 | Lean 4.35.0，编译器 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`；mathlib 固定 `56a005855ea17e0b0958f73ec801ae140b0a1679`，与固定配置和 evidence 一致。 |

根模块的真实导入闭包覆盖固定树全部 **1080 个数学模块**。独立剥离字符串及嵌套注释后扫描数学源码，没有代码级 `sorry`、`admit`、自设 `axiom` 或 `native_decide`；递归 `collectAxioms` 实际审计仍是公理结论的依据，静态扫描不取代内核检查。未使用动态 `.ci` 或其它版本的产物。

独立复核的可重查摘要位于 `/tmp/carleman-t270-review-evidence.json`、`review-boundaries.json`、`review-all-version-blobs.json`（后两者同 `carleman-t270-` 前缀），它们只记录本次核对，不替代原始源码和日志。

## 最终 26 个具名结果：范围与版本一一对应

独立解析原稿全部 `theorem/lemma/proposition/corollary` 环境，恰有 **26 个不同原文标签**；与固定 `state/paper_coverage.json` 的 26 个 ID/标签精确一一对应，所有 tex_line 也实际匹配，无漏项、重复计数或把辅助声明另外计入分母。没有把附录重复证明、未命名推广 remark 或实验计为新具名结果。

对下面除 P021 外的 **25 项、18 个不同 declaration_version**，独立枚举各旧版本的全部 `Carleman/` 数学文件，在最终 proof 中逐路径逐 blob 比较，全部原有文件仍在且字节相同；这比只检查入口或只依赖 diff 的修改类别更强。全部三个配置文件、原稿也分别完全相同。旧导入关系不变，故既有声明及其实际源码依赖边界未被后续新增模块改变。加本批共 19 个数学证明版本。

全部覆盖声明的实际类型均出现在最终 raw，且处于最终递归公理审计环境中。部分旧投影/辅助声明有 `#check` 类型而没有单独打印公理行，不能误称每个覆盖名字都有单独 `#print axioms`；它们仍受完整命名空间递归审计覆盖。

下表“旧文件”列是该原接受版本在 `Carleman/` 下被逐 blob 确认不变的文件数；最终判定各行均为 PASS。原声明的具体名字和冻结报告链接保留在固定 coverage 中，不因多个声明共同实现一条命题而增加计数。

| ID / 原结果 | 原标签 | 接受的数学版本 | 旧文件 / 固定独立验收 |
|---|---|---|---|
| P001 Theorem 2.1 | `thm:main` | `5fbbfa1714af4a34facdf933a0f37736a4b7e6cd` | 263；T022 |
| P002 Corollary 2.2 | `cor:general-scales` | `8706e95e3a24b09fe6e2675a0c72c827ba9a93f3` | 270；T023 |
| P003 Corollary 2.3 | `cor:scales` | `8706e95e3a24b09fe6e2675a0c72c827ba9a93f3` | 270；T023 |
| P004 Lemma 3.1 | `lem:graph` | `a315bdc449c58a705a982f0d009f1dde24d6af66` | 254；T019 |
| P005 Lemma 3.2 | `lem:cell` | `3dff0be3a1eaecbbfeb153e55219b9019bd1549b` | 32；历史 PR 7 独立接受记录，见下文 |
| P006 Lemma 3.3 | `lem:eulerMR` | `a315bdc449c58a705a982f0d009f1dde24d6af66` | 254；T019 |
| P007 Lemma 3.4 | `lem:frozen` | `a315bdc449c58a705a982f0d009f1dde24d6af66` | 254；T019 |
| P008 Theorem 3.5 | `thm:timeerror` | `a315bdc449c58a705a982f0d009f1dde24d6af66` | 254；T019 |
| P009 Lemma 4.1 | `lem:spatialEuler` | `a315bdc449c58a705a982f0d009f1dde24d6af66` | 254；T020-lemma |
| P010 Theorem 4.2 | `thm:combined` | `9d8230090dad2c5b5a2efa74f5d085728866d139` | 258；T021 |
| P011 Proposition 6.1 | `prop:p1` | `708eae70c82d9c0b1d60f6907f0202201d518a16` | 1053；T261 |
| P012 Proposition 6.2 | `prop:fd` | `13c8977bd4c50a11d6bed5fdab64b09aeee0203f` | 744；T142 |
| P013 Lemma 7.1 | `lem:physicalduality` | `1aa9b1f253dd759ccc18d92d151aa7c81646f51c` | 276；T024 |
| P014 Theorem 7.2 | `prop:physicalO` | `5458c11848a69d56199fb5e13d517b58eb38953b` | 1077；T268 |
| P015 Theorem 7.3 | `prop:physicalC` | `5458c11848a69d56199fb5e13d517b58eb38953b` | 1077；T268 |
| P016 Lemma 7.4 | `lem:filter-reverse` | `12d18c9c6548cc70165ad9e4c01314f4438dc5f1` | 280；T025 |
| P017 Theorem 7.5 | `thm:filtered-observability` | `b04fcf4526dac2c76c92f4d3155fc4e5763e947b` | 1078；分离冻结 T269 |
| P018 Corollary 7.6 | `cor:filtered-control` | `b04fcf4526dac2c76c92f4d3155fc4e5763e947b` | 1078；分离冻结 T269 |
| P019 Proposition 7.7 | `prop:filter-p1` | `7ad1a9dd94d3abfe384564b1f24f351f5c60fe21` | 709；T135 |
| P020 Proposition 7.8 | `prop:filter-fd` | `ac30cc21022f162809fdd7f88550a3fd58e5ad35` | 718；T137 |
| P021 Corollary 7.9 | `prop:control-convergence` | `99d519544e0eb8d42a955ca6bff3935c322d855f` | 本报告完整新验收 |
| P022 Proposition A.1 | `prop:spatial-operators` | `d1dabe5404212ce3dd399028a79233e3da4e324b` | 1021；T229，含已清偿真实平方根缺项 |
| P023 Corollary A.2 | `prop:analytic-realizations` | `cbd25fdee3e670d39fce5a03cbf172c02a890544` | 1052；T260 |
| P024 Proposition A.3 | `prop:continuousCE` | `0a1808091e23386fc8c06d4e2a3434d1fa9f2a34` | 1075；T267 |
| P025 Lemma B.1 | `lem:fd-boundary-affine` | `e71006a89160b4a22833727048495aff3f9d2016` | 512；T081 |
| P026 Lemma B.2 | `lem:fd-weighted-approximation` | `a9ca6fccf19cc677a4a60b07f373eb533df9d502` | 582；T097 |

已独立读取上述冻结报告的版本和范围记录，并将其提交内报告字节与当前保存副本核对。除本次明确分离的 T269 外，表中版本化旧报告均已在 proof 树中且字节相同；没有以仅 BUILT 的执行者自检替代独立语义接受。T268、T269 及本批关键能量解报告已全文读取；不重复无变化旧闭包的整套历史审核。

P005 的历史独立接受引用仍是 `https://github.com/MrGodfrey/LeanTransferDiscreteCarleman/pull/7`，台账记录时间 `2026-10-17T12:52:31.342266+00:00`。本次没有伪造一个不存在的本机报告或重新访问该 PR；独立核对其固定 32 个数学文件全部不变，另外实际读取 `Weights/CellLemma.lean` 与原 `lem:cell` 全陈述：q/σ 比较、两方向相对差、shift 冻结、真实 L∞ 商及相邻 shift 增量都包含，常数先于 T/网格/权族/方向/L；周期扩展保留跨端点结论。其完整最终类型和正常递归公理证据仍有效。

这一范围复核确认的是原 26 个具名数学结果，而非声称论文中所有未命名 remark、任意额外推广或实验复现均已完成。`governance/MILESTONES.md` 的 M6c 明确要求这 26 项；Section 8 实验是单独可选交付，不在分母内，不能由 Lean 证明替代。

## 历史空 claim 的非数学映射遗漏

独立读取固定 `state/progress.json` 中十条仍 PLANNED、无声明/版本的最早规划记录，并按其实际 `paper_labels` 与原覆盖项对应如下：

| 旧 claim | 同一原文结果 |
|---|---|
| C005 | P004 / `lem:graph` |
| C006 | P006 / `lem:eulerMR` |
| C007 | P008 / `thm:timeerror` |
| C013 | P024 / `prop:continuousCE` |
| C014 | P011 / `prop:p1` |
| C015 | P012 / `prop:fd` |
| C016 | P014 / `prop:physicalO` |
| C017 | P015 / `prop:physicalC` |
| C018 | P017 / `thm:filtered-observability` |
| C019 | P021 / `prop:control-convergence` |

这些记录的原标签均已有上述实际声明和相应接受证据，最后的 C019 由本报告清偿；它们没有指向额外未完成的数学结论。可由唯一台账维护者保留原 ID/依赖，填入同一 P 项的精确声明、数学版本和接受记录，并标明 `resolved_by_paper_result` / `resolved_by_claim_ids`。不得把这些旧规划占位另外计为十个结果，也不得将原无证据记录本身说成此前已经验收。本报告仅指出映射遗漏，不修改台账。

## 最终签发

**T270/C286 的 5 项全部 PASS；原 P021 / Corollary 7.9 完整 PAPER PASS。** 两种原实现的真实数据、完整状态、独立细化、区域控制、每个弱积聚点、原能量解及初终迹均已覆盖，无需新增数学假设或修补实现。

结合上述逐项冻结版本、独立接受和当前完整形式证据，**本固定证明版本支持原 26/26 个具名结果完成**。固定树中 P021 的待验状态、T269 的旧 BUILT 状态及十条旧规划映射可在主执行者正式接纳报告后更新；这些状态维护不影响本报告固定数学判定，也不需要重复宣称历史构建。
